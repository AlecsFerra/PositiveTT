import SPos.Typing.Weakening

def Subst.WellTyped (σ : Subst n m) (Γ : Ctx n) (Δ : Ctx m) : Prop :=
  ∀ {x : Fin n} {τ : Tm n}, (Γ ∋ x ∶ τ) → (Δ ⊢ σ x ∶ τ.subst σ)

theorem Subst.WellTyped.lift {σ : Subst n m} (hσ : Subst.WellTyped σ Γ Δ) {τ : Tm n}
    (hΔτ : ⊢ Δ ∷ τ.subst σ) : Subst.WellTyped (Subst.lift σ) (Γ ∷ τ) (Δ ∷ τ.subst σ) := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · have h0 : Subst.lift σ 0 = Tm.var 0 := by simp [Subst.lift]
    rw [h0, Tm.weaken_subst]
    exact .var hΔτ Lookup.here
  · have hs : Subst.lift σ j.succ = (σ j).weaken := by simp [Subst.lift]
    rw [hs, Tm.weaken_subst]
    exact WfTm.weaken (hσ hj) hΔτ

mutual
theorem WfTm.subst (ht : Γ ⊢ t ∶ τ) (hΔ : ⊢ Δ) (hσ : Subst.WellTyped σ Γ Δ)
  : (Δ ⊢ t.subst σ ∶ τ.subst σ) := match ht with
  | .var hΓ hlook => hσ hlook
  | .conv ht hσwf hτσ =>
      .conv (WfTm.subst ht hΔ hσ) (WfTm.subst hσwf hΔ hσ) (DefEq.subst hτσ hΔ hσ)
  | .pi hτ hυ =>
      let hτ' := WfTm.subst hτ hΔ hσ
      .pi hτ' (WfTm.subst hυ (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
  | .lam hτ hσwf ht =>
      let hτ' := WfTm.subst hτ hΔ hσ
      .lam hτ' (WfTm.subst hσwf (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
        (WfTm.subst ht (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
  | .app (τ := τ) ht hs => by
      simp [-Tm.subst1]
      exact WfTm.app (WfTm.subst ht hΔ hσ) (WfTm.subst hs hΔ hσ)
  | .u hΓ => .u hΔ

theorem DefEq.subst (heq : Γ ⊢ t₁ ≡ t₂ ∶ τ) (hΔ : ⊢ Δ) (hσ : Subst.WellTyped σ Γ Δ)
  : (Δ ⊢ t₁.subst σ ≡ t₂.subst σ ∶ τ.subst σ) := match heq with
  | .refl ht => .refl (WfTm.subst ht hΔ hσ)
  | .symm h => .symm (DefEq.subst h hΔ hσ)
  | .trans h₁ h₂ => .trans (DefEq.subst h₁ hΔ hσ) (DefEq.subst h₂ hΔ hσ)
  | .pi hτwf hυwf hτ hυ =>
      let hτ' := WfTm.subst hτwf hΔ hσ
      .pi hτ' (WfTm.subst hυwf (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
        (DefEq.subst hτ hΔ hσ) (DefEq.subst hυ (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
  | .lam hτ hσwf ht =>
      let hτ' := WfTm.subst hτ hΔ hσ
      .lam hτ' (WfTm.subst hσwf (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
        (DefEq.subst ht (hΔ.cons hτ') (hσ.lift (hΔ.cons hτ')))
  | .app (τ := τ) ht hmwf hm => by
      simp [-Tm.subst1]
      exact DefEq.app (DefEq.subst ht hΔ hσ) (WfTm.subst hmwf hΔ hσ) (DefEq.subst hm hΔ hσ)
  | .β (τ := τ) hlam hm => by
      simp [-Tm.subst1]
      exact DefEq.β (WfTm.subst hlam hΔ hσ) (WfTm.subst hm hΔ hσ)
  | .η ht => by
      have h0 : Subst.lift σ 0 = Tm.var 0 := by simp [Subst.lift]
      simp only [Tm.subst]
      rw [Tm.weaken_subst, h0]
      exact DefEq.η (WfTm.subst ht hΔ hσ)
end

theorem Subst.WellTyped.single (hΓ : ⊢ Γ) (hu : Γ ⊢ u ∶ τ) :
    Subst.WellTyped (Subst.single u) (Γ ∷ τ) Γ := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · show Γ ⊢ Subst.single u 0 ∶ τ.weaken [/ u ]
    rw [Tm.weaken_subst1]
    simpa [Subst.single] using hu
  · show Γ ⊢ Subst.single u j.succ ∶ τ'.weaken [/ u ]
    rw [Tm.weaken_subst1]
    simpa [Subst.single] using WfTm.var hΓ hj

theorem WfTm.subst1 (ht : Γ ∷ τ ⊢ t ∶ σ) (hv : Γ ⊢ v ∶ τ) (hΓ : ⊢ Γ) :
    Γ ⊢ t [/ v ] ∶ σ [/ v ] :=
  WfTm.subst ht hΓ (Subst.WellTyped.single hΓ hv)

theorem DefEq.subst1 (heq : Γ ∷ τ ⊢ t₁ ≡ t₂ ∶ σ) (hv : Γ ⊢ v ∶ τ) (hΓ : ⊢ Γ) :
    Γ ⊢ t₁ [/ v ] ≡ t₂ [/ v ] ∶ σ [/ v ] :=
  DefEq.subst heq hΓ (Subst.WellTyped.single hΓ hv)
