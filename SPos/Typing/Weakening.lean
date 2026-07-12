import SPos.Typing.Typing
import SPos.Typing.TypingProperties

def Ren.WellTyped (r : Ren n m) (Γ : Ctx n) (Δ : Ctx m) : Prop :=
  ∀ {x : Fin n} {τ : Tm n}, (Γ ∋ x ∶ τ) → (Δ ∋ r x ∶ τ.rename r)

theorem Ren.WellTyped.lift {r : Ren n m} (hr : Ren.WellTyped r Γ Δ) {τ : Tm n} :
    Ren.WellTyped (Ren.lift r) (Γ ∷ τ) (Δ ∷ τ.rename r) := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · have h : Ren.lift r 0 = 0 := by simp
    rw [h, Tm.weaken_rename]
    constructor
  · have h : Ren.lift r j.succ = (r j).succ := by simp
    rw [h, Tm.weaken_rename]
    exact Lookup.there (hr hj)

mutual
-- LEO PLEASE FIX MUTUAL INDUCTION
theorem WfTm.rename (ht : Γ ⊢ t ∶ τ) (hΔ : ⊢ Δ) (hr : Ren.WellTyped r Γ Δ)
  : (Δ ⊢ t.rename r ∶ τ.rename r) := match ht with
  | .var hΓ hlook => .var hΔ (hr hlook)
  | .conv ht hσ hτσ => .conv (WfTm.rename ht hΔ hr) (WfTm.rename hσ hΔ hr) (DefEq.rename hτσ hΔ hr)
  | .pi hτ hυ => .pi (WfTm.rename hτ hΔ hr) (WfTm.rename hυ (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
  | .lam hτ hσ ht => .lam (WfTm.rename hτ hΔ hr)
      (WfTm.rename hσ (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
      (WfTm.rename ht (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
  | .app ht hs => by
      simp [-Tm.subst1]
      exact WfTm.app (WfTm.rename ht hΔ hr) (WfTm.rename hs hΔ hr)
  | .u hΓ => .u hΔ

theorem DefEq.rename (heq : Γ ⊢ t ≡ t' ∶ τ) (hΔ : ⊢ Δ) (hr : Ren.WellTyped r Γ Δ)
  : (Δ ⊢ t.rename r ≡ t'.rename r ∶ τ.rename r) := match heq with
  | .refl ht => .refl (WfTm.rename ht hΔ hr)
  | .symm h => .symm (DefEq.rename h hΔ hr)
  | .trans h₁ h₂ => .trans (DefEq.rename h₁ hΔ hr) (DefEq.rename h₂ hΔ hr)
  | .pi hτwf hυwf hτ hυ => .pi (WfTm.rename hτwf hΔ hr) (WfTm.rename hυwf (hΔ.cons (WfTm.rename hτwf hΔ hr)) hr.lift)
      (DefEq.rename hτ hΔ hr) (DefEq.rename hυ (hΔ.cons (WfTm.rename hτwf hΔ hr)) hr.lift)
  | .lam hτ hσ ht => .lam (WfTm.rename hτ hΔ hr)
      (WfTm.rename hσ (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
      (DefEq.rename ht (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
  | .app ht hmwf hm => by
      simp [-Tm.subst1]
      exact DefEq.app (DefEq.rename ht hΔ hr) (WfTm.rename hmwf hΔ hr) (DefEq.rename hm hΔ hr)
  | .β hlam hm => by
      simp [-Tm.subst1]
      exact DefEq.β (WfTm.rename hlam hΔ hr) (WfTm.rename hm hΔ hr)
  | .η ht => by
      have h0 : Ren.lift r 0 = 0 := by simp
      simp only [Tm.rename]
      rw [Tm.weaken_rename, h0]
      exact DefEq.η (WfTm.rename ht hΔ hr)
end

theorem Ren.succ_wellTyped (Γ : Ctx n) (σ : Tm n) :
    Ren.WellTyped Fin.succ Γ (Γ ∷ σ) :=
  fun hlook => Lookup.there hlook

theorem WfTm.weaken (ht : Γ ⊢ t ∶ τ) (hΓσ : ⊢ Γ ∷ σ) : Γ ∷ σ ⊢ ↑ t ∶ ↑ τ:=
  WfTm.rename ht hΓσ (Ren.succ_wellTyped Γ σ)

theorem DefEq.weaken (heq : Γ ⊢ t₁ ≡ t₂ ∶ τ) (hΓσ : ⊢ Γ ∷ σ) :
    Γ ∷ σ ⊢ t₁.weaken ≡ t₂.weaken ∶ τ.weaken :=
  DefEq.rename heq hΓσ (Ren.succ_wellTyped Γ σ)
