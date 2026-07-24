import SPos.Typing.Substitution

theorem DefEq.wfCtx (h : Γ ⊢ t ≡ t' ∶ τ) : ⊢ Γ := by
  induction h using DefEq.rec _ _
  case x_0 => exact True
  all_goals grind

theorem WfCtx.lookup_wf (hΓ : ⊢ Γ) (hlook : Γ ∋ x ∶ τ) : ∃ ℓ, Γ ⊢ τ ∶ 𝓤 ℓ :=
  match hΓ, hlook with
  | .nil, hlook => x.elim0
  | .cons hΔ hσ, hlook => by
    rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, _, rfl, rfl, hj⟩
    · exact  ⟨_, hσ.weaken $ hΔ.cons hσ⟩
    · obtain ⟨ℓ, hτ'⟩ := WfCtx.lookup_wf hΔ hj
      exact  ⟨ℓ, hτ'.weaken $ hΔ.cons hσ⟩

abbrev PiInv (Γ : Ctx n) (Z : Tm n) : Prop :=
  ∀ (τ : Tm n) (σ : Tm (n + 1)), Z = Π̶ τ σ →
    ∃ (τ' : Tm n) (ℓ₁ ℓ₂ : Nat), (Γ ⊢ τ' ≡ τ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ' ⊢ σ ≡ σ ∶ 𝓤 ℓ₂)

abbrev SigmaInv (Γ : Ctx n) (Z : Tm n) : Prop :=
  ∀ (τ : Tm n) (σ : Tm (n + 1)), Z = Tm.sigma τ σ →
    ∃ (τ' : Tm n) (ℓ₁ ℓ₂ : Nat), (Γ ⊢ τ' ≡ τ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ' ⊢ σ ≡ σ ∶ 𝓤 ℓ₂)

abbrev IdInv (Γ : Ctx n) (Z : Tm n) : Prop :=
  ∀ (τ a b : Tm n), Z = Id τ a b →
    ∃ ℓ, (Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ) ∧ (Γ ⊢ a ≡ a ∶ τ) ∧ (Γ ⊢ b ≡ b ∶ τ)

-- Inverting a `Π`/`Σ`/`Id` head through a single substitution `t [/ m]`: either the
-- body `t` already had that head (invert it, then substitute `m`), or `t` is the
-- variable being substituted and the head comes from `m`.  Shared by the β-rules.
theorem piInv_subst1 {Γ : Ctx n} {τ m : Tm n} {t : Tm (n + 1)}
    (iht : PiInv (Γ ∷ τ) t) (ihm : PiInv Γ m) (hm : Γ ⊢ m ∶ τ) : PiInv Γ (t [/ m]) := by
  intros _ _ heq
  rcases t with i | _ <;> simp [Tm.subst1, Tm.subst, Subst.single] at heq
  · induction i using Fin.cases <;> grind
  · rcases heq with ⟨rfl, rfl⟩
    obtain ⟨A', ℓ₁, ℓ₂, hA'A, hB⟩ := iht _ _ rfl
    have hΓ := hm.wfCtx
    have hcons := hΓ.cons (DefEq.subst1 hA'A.wf_left hm hΓ)
    exact ⟨_, _, _, DefEq.subst1 hA'A hm hΓ,
      DefEq.subst hB hcons (Subst.WellTyped.lift (Subst.WellTyped.single hΓ hm) hcons)⟩

theorem sigmaInv_subst1 {Γ : Ctx n} {τ m : Tm n} {t : Tm (n + 1)}
    (iht : SigmaInv (Γ ∷ τ) t) (ihm : SigmaInv Γ m) (hm : Γ ⊢ m ∶ τ) : SigmaInv Γ (t [/ m]) := by
  intros _ _ heq
  rcases t with i | _ <;> simp [Tm.subst1, Tm.subst, Subst.single] at heq
  · induction i using Fin.cases <;> grind
  · rcases heq with ⟨rfl, rfl⟩
    obtain ⟨A', ℓ₁, ℓ₂, hA'A, hB⟩ := iht _ _ rfl
    have hΓ := hm.wfCtx
    have hcons := hΓ.cons (DefEq.subst1 hA'A.wf_left hm hΓ)
    exact ⟨_, _, _, DefEq.subst1 hA'A hm hΓ,
      DefEq.subst hB hcons (Subst.WellTyped.lift (Subst.WellTyped.single hΓ hm) hcons)⟩

theorem idInv_subst1 {Γ : Ctx n} {τ m : Tm n} {t : Tm (n + 1)}
    (iht : IdInv (Γ ∷ τ) t) (ihm : IdInv Γ m) (hm : Γ ⊢ m ∶ τ) : IdInv Γ (t [/ m]) := by
  intros _ _ _ heq
  rcases t with i | _ <;> simp [Tm.subst1, Tm.subst, Subst.single] at heq
  · induction i using Fin.cases <;> grind (instances := 3500)
  · rcases heq with ⟨rfl, rfl, rfl⟩
    obtain ⟨ℓ, hτd, had, hbd⟩ := iht _ _ _ rfl
    have hΓ := hm.wfCtx
    exact ⟨ℓ, DefEq.subst1 hτd hm hΓ, DefEq.subst1 had hm hΓ, DefEq.subst1 hbd hm hΓ⟩

theorem DefEq.inv_aux (h : Γ ⊢ t₁ ≡ t₂ ∶ τ)
  : PiInv Γ t₁ ∧ SigmaInv Γ t₁ ∧ IdInv Γ t₁ ∧ PiInv Γ t₂ ∧ SigmaInv Γ t₂ ∧ IdInv Γ t₂ := by
  induction h using DefEq.rec _ _
  case x_0 => exact True
  case lamβ t m _ _ _ hm _ _ iht ihm =>
    exact ⟨by grind, by grind, by grind,
      piInv_subst1 iht.1 ihm.1 hm, sigmaInv_subst1 iht.2.1 ihm.2.1 hm,
      idInv_subst1 iht.2.2.1 ihm.2.2.1 hm⟩
  all_goals grind (instances := 3500)

theorem DefEq.pi_inv {σ : Tm (n + 1)} (h : Γ ⊢ X ≡ Y ∶ υ) (heq : X = Π̶ τ₁ σ ∨ Y = Π̶ τ₁ σ) :
    ∃ (τ₂ : Tm n) (ℓ₁ ℓ₂ : Nat), (Γ ⊢ τ₂ ≡ τ₁ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ₂ ⊢ σ ≡ σ ∶ 𝓤 ℓ₂) :=
  heq.elim (fun h' => h.inv_aux.1 _ _ h') (fun h' => h.inv_aux.2.2.2.1 _ _ h')

theorem DefEq.sigma_inv {σ : Tm (n + 1)} (h : Γ ⊢ X ≡ Y ∶ υ)
    (heq : X = Tm.sigma τ₁ σ ∨ Y = Tm.sigma τ₁ σ) :
    ∃ (τ₂ : Tm n) (ℓ₁ ℓ₂ : Nat), (Γ ⊢ τ₂ ≡ τ₁ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ₂ ⊢ σ ≡ σ ∶ 𝓤 ℓ₂) :=
  heq.elim (fun h' => h.inv_aux.2.1 _ _ h') (fun h' => h.inv_aux.2.2.2.2.1 _ _ h')

theorem DefEq.id_inv (h : Γ ⊢ X ≡ Y ∶ υ) (heq : X = Id τ a b ∨ Y = Id τ a b) :
    ∃ ℓ, (Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ) ∧ (Γ ⊢ a ≡ a ∶ τ) ∧ (Γ ⊢ b ≡ b ∶ τ) :=
  heq.elim (fun h' => h.inv_aux.2.2.1 _ _ _ h') (fun h' => h.inv_aux.2.2.2.2.2 _ _ _ h')

theorem DefEq.regular (h : Γ ⊢ t ≡ t' ∶ τ) : ∃ ℓ, Γ ⊢ τ ∶ 𝓤 ℓ := by
  induction h using DefEq.rec _ _
  case x_0 => exact True
  case u _ _ _ hΓ _ => exact ⟨_, .u hΓ⟩
  case pi _ _ _ _ _ _ _ _ hτeq _ _ _ => exact ⟨_, .u hτeq.wfCtx⟩
  case lam _ _ _ _ _ _ _ _ _ hσ hτeq _ _ _ _ => exact ⟨_, .pi hτeq.wf_left hσ⟩
  case app ht hm iht ihm =>
    obtain ⟨_, hPi⟩ := iht
    obtain ⟨τ', _, ℓ₂, hττ', hσd⟩ := hPi.pi_inv (Or.inl rfl)
    have hm' := DefEq.conv hm.wf_left hττ'.wf_left hττ'.symm
    exact ⟨ℓ₂, DefEq.subst1 hσd hm' hm.wfCtx⟩
  case lamβ _ _ _ _ _ _ _ _ _ hσwf _ hm _ _ _ _ => exact ⟨_, DefEq.subst1 hσwf hm hm.wfCtx⟩
  case id _ _ _ _ _ _ _ _ _ hτeq _ _ _ _ _ => exact ⟨_, .u hτeq.wfCtx⟩
  -- rebuild `Γ ⊢ C [/ ↑p ] [/ b ] ∶ 𝓤 ℓ` by substituting b under the Id
  -- binder (a simultaneous [p, b] split into two steps)
  case j n Γ τ _ _ _ _ _ _ _ _ b a _ _ hCeq _ hpeq _ _ _ _ ihp =>
    have hΓ := hpeq.wfCtx
    obtain ⟨_, hIdab⟩ := ihp
    obtain ⟨_, _, _, hb⟩ := hIdab.id_inv (Or.inl rfl)
    have hIdsub : (Id (↑ τ) (↑ a) (# 0) : Tm (n + 1)).subst (Subst.single b) = Id τ a b := by
      simp [Tm.subst, Tm.weaken, Subst.single]
    have hcons : ⊢ Γ ∷ ((Id (↑ τ) (↑ a) (# 0) : Tm (n + 1)).subst (Subst.single b)) := by
      rw [hIdsub]; exact hΓ.cons hIdab
    have h1 := DefEq.subst hCeq.wf_left hcons
      (Subst.WellTyped.lift (Subst.WellTyped.single hΓ hb) hcons)
    rw [hIdsub] at h1
    have h2 := DefEq.subst1 h1 hpeq.wf_left hΓ
    exact ⟨_, by rwa [Tm.subst_lift_single] at h2⟩
  case sigma _ _ _ _ _ _ _ _ hτ _ _ _ => exact ⟨_, .u hτ.wfCtx⟩
  case pair _ _ _ _ _ _ _ _ _ _ hτ hυ _ _ _ _ _ _ => exact ⟨_, DefEq.sigma hτ hυ⟩
  case fst hp ihp =>
    obtain ⟨_, hSig⟩ := ihp
    obtain ⟨_, ℓ₁, _, hττ', _⟩ := hSig.sigma_inv (Or.inl rfl)
    exact ⟨ℓ₁, hττ'.wf_right⟩
  case snd hp ihp =>
    obtain ⟨_, hSig⟩ := ihp
    obtain ⟨_, _, ℓ₂, hττ', hσd⟩ := hSig.sigma_inv (Or.inl rfl)
    have hfst := DefEq.conv (DefEq.fst hp.wf_left) hττ'.wf_left hττ'.symm
    exact ⟨ℓ₂, DefEq.subst1 hσd hfst hp.wfCtx⟩
  case bool _ _ hΓ _ => exact ⟨_, .u hΓ⟩
  case true _ _ hΓ _ => exact ⟨_, .bool hΓ⟩
  case false _ _ hΓ _ => exact ⟨_, .bool hΓ⟩
  case boolrec _ _ _ _ _ _ _ _ _ _ _ hP _ _ hb _ _ _ _ =>
    exact ⟨_, (DefEq.subst1 hP hb.wf_left hb.wfCtx).wf_left⟩
  case boolβt _ _ _ _ _ _ hP ht _ _ _ _ =>
    exact ⟨_, DefEq.subst1 hP (DefEq.true ht.wfCtx) ht.wfCtx⟩
  case boolβf _ _ _ _ _ _ hP ht _ _ _ _ =>
    exact ⟨_, DefEq.subst1 hP (DefEq.false ht.wfCtx) ht.wfCtx⟩
  all_goals grind (instances := 4000) [DefEq.u, DefEq.pi, DefEq.sigma, DefEq.lam, DefEq.id, DefEq.refl, WfCtx.lookup_wf, DefEq.subst1]
