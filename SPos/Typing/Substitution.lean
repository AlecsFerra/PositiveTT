import SPos.Typing.Weakening

def Subst.WellTyped (σ : Subst n m) (Γ : Ctx n) (Δ : Ctx m) : Prop :=
  ∀ {x : Fin n} {τ : Tm n}, (Γ ∋ x ∶ τ) → (Δ ⊢ σ x ∶ τ.subst σ)

theorem Subst.WellTyped.lift {σ : Subst n m} (hσ : Subst.WellTyped σ Γ Δ) {τ : Tm n}
    (hΔτ : ⊢ Δ ∷ τ.subst σ) : Subst.WellTyped (Subst.lift σ) (Γ ∷ τ) (Δ ∷ τ.subst σ) := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · have h0 : Subst.lift σ 0 = Tm.var 0 := by simp [Subst.lift]
    rw [h0, Tm.weaken_subst]
    exact DefEq.var hΔτ Lookup.here
  · have hs : Subst.lift σ j.succ = (σ j).weaken := by simp [Subst.lift]
    rw [hs, Tm.weaken_subst]
    exact WfTm.weaken (hσ hj) hΔτ

theorem Subst.WellTyped.lift2 {σ : Subst n m} (hσ : Subst.WellTyped σ Γ Δ) {τ : Tm n}
    {υ : Tm (n + 1)} (hΔτ : ⊢ Δ ∷ τ.subst σ) (hΔτυ : ⊢ Δ ∷ τ.subst σ ∷ υ.subst σ.lift) :
    Subst.WellTyped (Subst.lift (Subst.lift σ)) (Γ ∷ τ ∷ υ) (Δ ∷ τ.subst σ ∷ υ.subst σ.lift) :=
  Subst.WellTyped.lift (Subst.WellTyped.lift hσ hΔτ) hΔτυ

theorem DefEq.subst (heq : Γ ⊢ t₁ ≡ t₂ ∶ τ) (hΔ : ⊢ Δ) (hσ : Subst.WellTyped σ Γ Δ)
  : (Δ ⊢ t₁.subst σ ≡ t₂.subst σ ∶ τ.subst σ) := match heq with
  | .var _ hlook => hσ hlook
  | .u _ => .u hΔ
  | .symm h => .symm (DefEq.subst h hΔ hσ)
  | .trans h₁ h₂ => .trans (DefEq.subst h₁ hΔ hσ) (DefEq.subst h₂ hΔ hσ)
  | .conv h hσwf hτσ =>
      .conv (DefEq.subst h hΔ hσ) (DefEq.subst hσwf hΔ hσ) (DefEq.subst hτσ hΔ hσ)
  | .pi hτ hυ =>
      let hτ' := DefEq.subst hτ hΔ hσ
      let hΔτ := hΔ.cons hτ'.wf_left
      .pi hτ' (DefEq.subst hυ hΔτ (hσ.lift hΔτ))
  | .lam hσwf hτeq ht =>
      let hτ' := DefEq.subst hτeq hΔ hσ
      let hΔτ := hΔ.cons hτ'.wf_left
      .lam (DefEq.subst hσwf hΔτ (hσ.lift hΔτ)) hτ' (DefEq.subst ht hΔτ (hσ.lift hΔτ))
  | .app ht hm => by
      simp
      exact DefEq.app (DefEq.subst ht hΔ hσ) (DefEq.subst hm hΔ hσ)
  | .lamβ hτ hσwf ht hm => by
      have hτ' := DefEq.subst hτ hΔ hσ
      have hΔτ := hΔ.cons hτ'
      simp
      exact DefEq.lamβ hτ' (DefEq.subst hσwf hΔτ (hσ.lift hΔτ))
        (DefEq.subst ht hΔτ (hσ.lift hΔτ)) (DefEq.subst hm hΔ hσ)
  | .lamη ht => by
      have h0 : Subst.lift σ 0 = Tm.var 0 := by simp [Subst.lift]
      simp [Tm.subst]
      rw [Tm.weaken_subst, h0]
      exact DefEq.lamη (DefEq.subst ht hΔ hσ)
  | .id hτeq haeq hbeq =>
      .id (DefEq.subst hτeq hΔ hσ) (DefEq.subst haeq hΔ hσ) (DefEq.subst hbeq hΔ hσ)
  | .refl hτeq haeq => .refl (DefEq.subst hτeq hΔ hσ) (DefEq.subst haeq hΔ hσ)
  | .j hτ hIdT hCeq hdeq hpeq => by
      have hτ' := DefEq.subst hτ hΔ hσ
      have hΔτ := hΔ.cons hτ'
      have hIdT' := DefEq.subst hIdT hΔτ (hσ.lift hΔτ)
      have hΔτId := hΔτ.cons hIdT'
      have hCeq' := DefEq.subst hCeq hΔτId (hσ.lift2 hΔτ hΔτId)
      have hdeq' := DefEq.subst hdeq hΔ hσ
      simp only [Tm.subst, Tm.subst1_subst, Tm.weaken_subst, Subst.lift, Fin.cases_zero]
        at hIdT' hCeq' hdeq' ⊢
      exact DefEq.j hτ' hIdT' hCeq' hdeq' (DefEq.subst hpeq hΔ hσ)
  | .jβ hτ ha hIdT hC hd => by
      have hτ' := DefEq.subst hτ hΔ hσ
      have hΔτ := hΔ.cons hτ'
      have hIdT' := DefEq.subst hIdT hΔτ (hσ.lift hΔτ)
      have hΔτId := hΔτ.cons hIdT'
      have hC' := DefEq.subst hC hΔτId (hσ.lift2 hΔτ hΔτId)
      have hd' := DefEq.subst hd hΔ hσ
      simp only [Tm.subst, Tm.subst1_subst, Tm.weaken_subst, Subst.lift, Fin.cases_zero]
        at hIdT' hC' hd' ⊢
      exact DefEq.jβ hτ' (DefEq.subst ha hΔ hσ) hIdT' hC' hd'

theorem Subst.WellTyped.single (hΓ : ⊢ Γ) (hu : Γ ⊢ u ∶ τ) :
    Subst.WellTyped (Subst.single u) (Γ ∷ τ) Γ := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · show Γ ⊢ Subst.single u 0 ∶ τ.weaken [/ u ]
    rw [Tm.weaken_subst1]
    simpa [Subst.single] using hu
  · show Γ ⊢ Subst.single u j.succ ∶ τ'.weaken [/ u ]
    rw [Tm.weaken_subst1]
    simpa [Subst.single] using DefEq.var hΓ hj

theorem DefEq.subst1 (heq : Γ ∷ τ ⊢ t₁ ≡ t₂ ∶ σ) (hv : Γ ⊢ v ∶ τ) (hΓ : ⊢ Γ) :
    Γ ⊢ t₁ [/ v ] ≡ t₂ [/ v ] ∶ σ [/ v ] :=
  DefEq.subst heq hΓ (Subst.WellTyped.single hΓ hv)

theorem WfTm.subst1 (ht : Γ ∷ τ ⊢ t ∶ σ) (hv : Γ ⊢ v ∶ τ) (hΓ : ⊢ Γ) :
    Γ ⊢ t [/ v ] ∶ σ [/ v ] :=
  DefEq.subst1 ht hv hΓ
