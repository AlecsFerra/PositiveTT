import SPos.Typing.Substitution

theorem DefEq.wfCtx (h : Γ ⊢ t ≡ t' ∶ τ) : ⊢ Γ :=
  match h with
  | .var hΓ _ | .u hΓ => hΓ
  | .symm h | .trans h _ | .conv h _ _ | .pi h _ | .app h _ | .lamη h
  | .id h _ _ | .reflId h _ | .lam _ h _ | .lamβ h _ _ _
  | .j h _ _ _ _ | .jβ h _ _ _ _ => h.wfCtx

theorem WfCtx.lookup_wf (hΓ : ⊢ Γ) (hlook : Γ ∋ x ∶ τ) : ∃ ℓ, Γ ⊢ τ ∶ 𝓤 ℓ :=
  match hΓ, hlook with
  | .nil, hlook => x.elim0
  | .cons hΔ hσ, hlook => by
    rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
    · exact ⟨_, hσ.weaken (hΔ.cons hσ)⟩
    · obtain ⟨ℓ, hτ'⟩ := WfCtx.lookup_wf hΔ hj
      exact ⟨ℓ, hτ'.weaken (hΔ.cons hσ)⟩

-- Inversion targets: whenever a term is syntactically a `Π` (resp. `Id`), its
-- components are well-formed — over a *convertible* domain in the `Π` case, which
-- absorbs the context mismatch that a right-hand congruence or a β-contraction
-- would otherwise force on us.
abbrev PiInv (Γ : Ctx n) (Z : Tm n) : Prop :=
  ∀ (τ : Tm n) (σ : Tm (n + 1)), Z = Π τ σ →
    ∃ (τ' : Tm n) (ℓ₁ ℓ₂ : Nat), (Γ ⊢ τ' ≡ τ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ' ⊢ σ ≡ σ ∶ 𝓤 ℓ₂)

abbrev IdInv (Γ : Ctx n) (Z : Tm n) : Prop :=
  ∀ (τ a b : Tm n), Z = Id τ a b →
    ∃ ℓ, (Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ) ∧ (Γ ⊢ a ≡ a ∶ τ) ∧ (Γ ⊢ b ≡ b ∶ τ)

-- Inversion through conversion, symmetry, transitivity, β and η, for both sides
-- at once.  Bundling the two shapes keeps every recursive call on a bare premise,
-- *before* any case analysis on the subject term (which structural recursion
-- cannot see through).
theorem DefEq.inv_aux (h : Γ ⊢ X ≡ Y ∶ υ) :
    (PiInv Γ X ∧ IdInv Γ X) ∧ (PiInv Γ Y ∧ IdInv Γ Y) :=
  match h with
  | .var _ _ | .u _ | .lam _ _ _ | .app _ _ | .reflId _ _ | .j _ _ _ _ _ =>
      ⟨⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩,
       ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩⟩
  | .symm h =>
      have ih := DefEq.inv_aux h
      ⟨ih.2, ih.1⟩
  | .trans h₁ h₂ => ⟨(DefEq.inv_aux h₁).1, (DefEq.inv_aux h₂).2⟩
  | .conv h _ _ => DefEq.inv_aux h
  | .lamη ht =>
      ⟨(DefEq.inv_aux ht).1, ⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩⟩
  | .jβ _ _ _ _ hd =>
      ⟨⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩, (DefEq.inv_aux hd).1⟩
  | .pi hτeq hυeq =>
      ⟨⟨fun _ _ h => by cases h; exact ⟨_, _, _, hτeq.wf_left, hυeq.wf_left⟩,
        fun _ _ _ h => (nomatch h)⟩,
       ⟨fun _ _ h => by cases h; exact ⟨_, _, _, hτeq, hυeq.wf_right⟩,
        fun _ _ _ h => (nomatch h)⟩⟩
  | .id hτeq haeq hbeq =>
      ⟨⟨fun _ _ h => (nomatch h),
        fun _ _ _ h => by cases h; exact ⟨_, hτeq.wf_left, haeq.wf_left, hbeq.wf_left⟩⟩,
       ⟨fun _ _ h => (nomatch h),
        fun _ _ _ h => by
          cases h
          exact ⟨_, hτeq.wf_right, .conv haeq.wf_right hτeq.wf_right hτeq,
            .conv hbeq.wf_right hτeq.wf_right hτeq⟩⟩⟩
  | .lamβ (t := t) (m := m) _ _ ht hm =>
      -- invert the redex's body and argument up front, then peel the
      -- substitution off the contractum `t [/ m ]`
      have iht := DefEq.inv_aux ht
      have ihm := DefEq.inv_aux hm
      ⟨⟨fun _ _ h => (nomatch h), fun _ _ _ h => (nomatch h)⟩,
       ⟨fun τ σ heq => by
          rcases t with i | ⟨A, B⟩ | _ | _ | _ | _ | _ | _
          · induction i using Fin.cases with
            | zero =>
              simp only [Tm.subst1, Tm.subst, Subst.single, Fin.cases_zero] at heq
              exact ihm.1.1 _ _ heq
            | succ k => simp [Tm.subst1, Tm.subst, Subst.single] at heq
          · simp only [Tm.subst1, Tm.subst] at heq
            cases heq
            obtain ⟨A', ℓ₁, ℓ₂, hA'A, hB⟩ := iht.1.1 A B rfl
            have hΓ := hm.wfCtx
            have h₁ := DefEq.subst1 hA'A hm hΓ
            have hcons : ⊢ Γ ∷ (A'.subst (Subst.single m)) :=
              hΓ.cons (DefEq.subst1 hA'A.wf_left hm hΓ)
            exact ⟨_, _, _, h₁,
              DefEq.subst hB hcons (Subst.WellTyped.lift (Subst.WellTyped.single hΓ hm) hcons)⟩
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq,
        fun τ a b heq => by
          rcases t with i | _ | _ | _ | ⟨A, a₁, b₁⟩ | _ | _ | _
          · induction i using Fin.cases with
            | zero =>
              simp only [Tm.subst1, Tm.subst, Subst.single, Fin.cases_zero] at heq
              exact ihm.1.2 _ _ _ heq
            | succ k => simp [Tm.subst1, Tm.subst, Subst.single] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp only [Tm.subst1, Tm.subst] at heq
            cases heq
            obtain ⟨ℓ, hτd, had, hbd⟩ := iht.1.2 A a₁ b₁ rfl
            have hΓ := hm.wfCtx
            exact ⟨ℓ, DefEq.subst1 hτd hm hΓ, DefEq.subst1 had hm hΓ, DefEq.subst1 hbd hm hΓ⟩
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq
          · simp [Tm.subst1, Tm.subst] at heq⟩⟩

theorem DefEq.pi_inv {X Y υ τ : Tm n} {σ : Tm (n + 1)} (h : Γ ⊢ X ≡ Y ∶ υ)
    (heq : X = Π τ σ ∨ Y = Π τ σ) :
    ∃ (τ' : Tm n) (ℓ₁ ℓ₂ : Nat), (Γ ⊢ τ' ≡ τ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ' ⊢ σ ≡ σ ∶ 𝓤 ℓ₂) :=
  heq.elim (fun h' => h.inv_aux.1.1 _ _ h') (fun h' => h.inv_aux.2.1 _ _ h')

theorem DefEq.id_inv {X Y υ τ a b : Tm n} (h : Γ ⊢ X ≡ Y ∶ υ)
    (heq : X = Id τ a b ∨ Y = Id τ a b) :
    ∃ ℓ, (Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ) ∧ (Γ ⊢ a ≡ a ∶ τ) ∧ (Γ ⊢ b ≡ b ∶ τ) :=
  heq.elim (fun h' => h.inv_aux.1.2 _ _ _ h') (fun h' => h.inv_aux.2.2 _ _ _ h')

theorem DefEq.regular {Γ : Ctx n} {t t' τ : Tm n} (h : Γ ⊢ t ≡ t' ∶ τ) : ∃ ℓ, Γ ⊢ τ ∶ 𝓤 ℓ :=
  match h with
  | .var hΓ hlook => hΓ.lookup_wf hlook
  | .u hΓ => ⟨_, .u hΓ⟩
  | .symm h => h.regular
  | .trans h₁ _ => h₁.regular
  | .conv _ hσ _ => ⟨_, hσ⟩
  | .pi hτeq _ => ⟨_, .u hτeq.wfCtx⟩
  | .lam hσ hτeq _ => ⟨_, .pi hτeq.wf_left hσ⟩
  | .app (m := m) ht hm => by
      obtain ⟨_, hPi⟩ := ht.regular
      obtain ⟨τ', _, ℓ₂, hττ', hσd⟩ := hPi.pi_inv (Or.inl rfl)
      have hm' : Γ ⊢ m ∶ τ' := .conv hm.wf_left hττ'.wf_left hττ'.symm
      exact ⟨ℓ₂, DefEq.subst1 hσd hm' hm.wfCtx⟩
  | .lamβ _ hσwf _ hm => ⟨_, DefEq.subst1 hσwf hm hm.wfCtx⟩
  | .lamη ht => ht.regular
  | .id hτeq _ _ => ⟨_, .u hτeq.wfCtx⟩
  | .reflId hτeq haeq => ⟨_, .id hτeq.wf_left haeq.wf_left haeq.wf_left⟩
  | .j (τ := υ₀) (a := a) (b := b) _ _ hCeq _ hpeq => by
      -- rebuild `Γ ⊢ C [/ ↑p ] [/ b ] ∶ 𝓤 ℓ` by substituting b under the Id
      -- binder (a simultaneous [p, b] split into two steps)
      have hΓ := hpeq.wfCtx
      obtain ⟨_, hIdab⟩ := hpeq.regular
      obtain ⟨_, _, _, hb⟩ := hIdab.id_inv (Or.inl rfl)
      have hIdsub : (Id (↑ υ₀) (↑ a) (# 0) : Tm (n + 1)).subst (Subst.single b) = Id υ₀ a b := by
        simp [Tm.subst, Tm.weaken, Subst.single]
      have hcons : ⊢ Γ ∷ ((Id (↑ υ₀) (↑ a) (# 0) : Tm (n + 1)).subst (Subst.single b)) := by
        rw [hIdsub]; exact hΓ.cons hIdab
      have h1 := DefEq.subst hCeq.wf_left hcons
        (Subst.WellTyped.lift (Subst.WellTyped.single hΓ hb) hcons)
      rw [hIdsub] at h1
      have h2 := DefEq.subst1 h1 hpeq.wf_left hΓ
      exact ⟨_, by rwa [Tm.subst_lift_single] at h2⟩
  | .jβ _ _ _ _ hd => hd.regular
