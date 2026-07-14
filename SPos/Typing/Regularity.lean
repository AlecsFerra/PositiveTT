import SPos.Typing.Substitution

theorem WfTm.wfCtx (ht : Γ ⊢ t ∶ τ) : ⊢ Γ :=
  match ht with
  | .conv ht _ _ | .pi ht _ | .lam ht _ _ | .app ht _
  | .id ht _ _ | .refl ht | .j ht _ _ _ _ => ht.wfCtx
  | .var hΓ _ | .u hΓ => hΓ


theorem WfCtx.lookup_wf (hΓ : ⊢ Γ) (hlook : Γ ∋ x ∶ τ) : ∃ ℓ, Γ ⊢ τ ∶ 𝓤 ℓ :=
  match hΓ, hlook with
  | .nil, hlook => x.elim0
  | .cons hΔ hσ, hlook => by
    rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
    · exact ⟨_, hσ.weaken (hΔ.cons hσ)⟩
    · obtain ⟨ℓ, hτ'⟩ := WfCtx.lookup_wf hΔ hj
      exact ⟨ℓ, hτ'.weaken (hΔ.cons hσ)⟩

theorem WfTm.pi_inv {t : Tm n} (ht : Γ ⊢ t ∶ υ)  (heq : t = Π τ σ)
  : ∃ ℓ₁ ℓ₂, (Γ ⊢ τ ∶ 𝓤 ℓ₁) ∧ (Γ ∷ τ ⊢ σ ∶ 𝓤 ℓ₂) := match ht with
  | .var _ _ | .lam _ _ _ | .app _ _ | .u _
  | .id _ _ _ | .refl _ | .j _ _ _ _ _ => by cases heq
  | .conv ht _ _ => ht.pi_inv heq
  | .pi hτ hσ => by cases heq; exact ⟨_, _, hτ, hσ⟩

theorem WfTm.id_inv {t : Tm n} (ht : Γ ⊢ t ∶ υ) (heq : t = Id τ a b)
  : ∃ ℓ, (Γ ⊢ τ ∶ 𝓤 ℓ) ∧ (Γ ⊢ a ∶ τ) ∧ (Γ ⊢ b ∶ τ) := match ht with
  | .var _ _ | .lam _ _ _ | .app _ _ | .u _
  | .pi _ _ | .refl _ | .j _ _ _ _ _ => by cases heq
  | .conv ht _ _ => ht.id_inv heq
  | .id hτ ha hb => by cases heq; exact ⟨_, hτ, ha, hb⟩

theorem WfTm.regular {Γ : Ctx n} {t τ : Tm n} (ht : Γ ⊢ t ∶ τ) : ∃ ℓ, Γ ⊢ τ ∶ 𝓤 ℓ :=
  match ht with
  | .var hΓ hlook => hΓ.lookup_wf hlook
  | .conv _ hσ _ => ⟨_, hσ⟩
  | .pi hτ _ => ⟨_, .u hτ.wfCtx⟩
  | .lam hτ hσ _ => ⟨_, .pi hτ hσ⟩
  | .app ht hm => by
      obtain ⟨_, hPi⟩ := ht.regular
      obtain ⟨_, ℓ₂, _, hσcod⟩ := hPi.pi_inv rfl
      exact ⟨ℓ₂, hσcod.subst1 hm ht.wfCtx⟩
  | .id hτ _ _ => ⟨_, .u hτ.wfCtx⟩
  | .refl ha => by
      obtain ⟨_, hτ⟩ := ha.regular
      exact ⟨_, .id hτ ha ha⟩
  | .j (τ := υ) (a := a) (b := b) _ _ hC hp _ => by
      -- rebuild `Γ ⊢ C [/ ↑p ] [/ b ] ∶ 𝓤 ℓ` by substituting b under the Id
      -- binder (a simultaneous [p, b] split into two steps)
      have hΓ := hp.wfCtx
      obtain ⟨_, hIdab⟩ := hp.regular
      obtain ⟨_, _, _, hb⟩ := hIdab.id_inv rfl
      have hIdsub : (Id (↑ υ) (↑ a) (# 0) : Tm (n + 1)).subst (Subst.single b) = Id υ a b := by
        simp [Tm.subst, Tm.weaken, Subst.single]
      have hcons : ⊢ Γ ∷ ((Id (↑ υ) (↑ a) (# 0) : Tm (n + 1)).subst (Subst.single b)) := by
        rw [hIdsub]; exact hΓ.cons hIdab
      have h1 := WfTm.subst hC hcons
        (Subst.WellTyped.lift (Subst.WellTyped.single hΓ hb) hcons)
      rw [hIdsub] at h1
      have h2 := WfTm.subst1 h1 hp hΓ
      exact ⟨_, by rwa [Tm.subst_lift_single] at h2⟩
  | .u hΓ => ⟨_, .u hΓ⟩
