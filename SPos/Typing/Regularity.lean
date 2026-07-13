import SPos.Typing.Substitution

theorem WfTm.wfCtx (ht : Γ ⊢ t ∶ τ) : ⊢ Γ :=
  match ht with
  | .conv ht _ _ | .pi ht _ | .lam ht _ _ | .app ht _ => ht.wfCtx
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
  | .var _ _ | .lam _ _ _ | .app _ _ | .u _ => by cases heq
  | .conv ht _ _ => ht.pi_inv heq
  | .pi hτ hσ => by cases heq; exact ⟨_, _, hτ, hσ⟩

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
  | .u hΓ => ⟨_, .u hΓ⟩
