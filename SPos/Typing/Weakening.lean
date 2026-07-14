import SPos.Typing.Typing
import SPos.Typing.TypingProperties

def Ren.WellTyped (r : Ren n m) (Γ : Ctx n) (Δ : Ctx m) : Prop :=
  ∀ {x : Fin n} {τ : Tm n}, (Γ ∋ x ∶ τ) → (Δ ∋ r x ∶ τ.rename r)

theorem Ren.WellTyped.lift {r : Ren n m} (hr : Ren.WellTyped r Γ Δ) {τ : Tm n} :
    Ren.WellTyped (Ren.lift r) (Γ ∷ τ) (Δ ∷ τ.rename r) := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · have h : Ren.lift r 0 = 0 := by simp [Ren.lift]
    rw [h, Tm.weaken_rename]
    constructor
  · have h : Ren.lift r j.succ = (r j).succ := by simp [Ren.lift]
    rw [h, Tm.weaken_rename]
    exact Lookup.there (hr hj)

theorem Ren.WellTyped.lift2 {r : Ren n m} (hr : Ren.WellTyped r Γ Δ) {τ : Tm n} {υ : Tm (n + 1)} :
    Ren.WellTyped (Ren.lift (Ren.lift r)) (Γ ∷ τ ∷ υ)
      (Δ ∷ τ.rename r ∷ υ.rename (Ren.lift r)) :=
  Ren.WellTyped.lift (Ren.WellTyped.lift hr)

mutual
theorem WfTm.rename (ht : Γ ⊢ t ∶ τ) (hΔ : ⊢ Δ) (hr : Ren.WellTyped r Γ Δ)
  : (Δ ⊢ t.rename r ∶ τ.rename r) := match ht with
  | .var hΓ hlook => .var hΔ (hr hlook)
  | .conv ht hσ hτσ => .conv (WfTm.rename ht hΔ hr) (WfTm.rename hσ hΔ hr) (DefEq.rename hτσ hΔ hr)
  | .pi hτ hυ => .pi (WfTm.rename hτ hΔ hr) (WfTm.rename hυ (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
  | .lam hτ hσ ht => .lam (WfTm.rename hτ hΔ hr)
      (WfTm.rename hσ (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
      (WfTm.rename ht (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
  | .app ht hs => by
      simp
      exact WfTm.app (WfTm.rename ht hΔ hr) (WfTm.rename hs hΔ hr)
  | .id hτ ha hb =>
      .id (WfTm.rename hτ hΔ hr) (WfTm.rename ha hΔ hr) (WfTm.rename hb hΔ hr)
  | .refl ha => .refl (WfTm.rename ha hΔ hr)
  | .j hτ hIdT hC hp hd => by
      have hτ' := WfTm.rename hτ hΔ hr
      have hIdT' := WfTm.rename hIdT (hΔ.cons hτ') hr.lift
      have hC' := WfTm.rename hC ((hΔ.cons hτ').cons hIdT') hr.lift2
      have hd' := WfTm.rename hd hΔ hr
      simp only [Tm.rename, Tm.subst1_rename, Tm.weaken_rename, Ren.lift, Fin.cases_zero]
        at hIdT' hC' hd' ⊢
      exact WfTm.j hτ' hIdT' hC' (WfTm.rename hp hΔ hr) hd'
  | .u hΓ => .u hΔ

theorem DefEq.rename (heq : Γ ⊢ t ≡ t' ∶ τ) (hΔ : ⊢ Δ) (hr : Ren.WellTyped r Γ Δ)
  : (Δ ⊢ t.rename r ≡ t'.rename r ∶ τ.rename r) := match heq with
  | .refl ht => .refl (WfTm.rename ht hΔ hr)
  | .symm h => .symm (DefEq.rename h hΔ hr)
  | .trans h₁ h₂ => .trans (DefEq.rename h₁ hΔ hr) (DefEq.rename h₂ hΔ hr)
  | .pi hτwf hτ hυ => .pi (WfTm.rename hτwf hΔ hr)
      (DefEq.rename hτ hΔ hr) (DefEq.rename hυ (hΔ.cons (WfTm.rename hτwf hΔ hr)) hr.lift)
  | .lam hτ hσ ht => .lam (WfTm.rename hτ hΔ hr)
      (WfTm.rename hσ (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
      (DefEq.rename ht (hΔ.cons (WfTm.rename hτ hΔ hr)) hr.lift)
  | .app ht hm => by
      simp
      exact DefEq.app (DefEq.rename ht hΔ hr) (DefEq.rename hm hΔ hr)
  | .lamβ hlam hm => by
      simp
      exact DefEq.lamβ (WfTm.rename hlam hΔ hr) (WfTm.rename hm hΔ hr)
  | .lamη ht => by
      have h0 : Ren.lift r 0 = 0 := by simp [Ren.lift]
      simp [Tm.rename]
      rw [h0]
      exact DefEq.lamη (WfTm.rename ht hΔ hr)
  | .id hτeq haeq hbeq =>
      .id (DefEq.rename hτeq hΔ hr) (DefEq.rename haeq hΔ hr) (DefEq.rename hbeq hΔ hr)
  | .reflId haeq => .reflId (DefEq.rename haeq hΔ hr)
  | .j hτ hIdT hCeq hdeq hpeq => by
      have hτ' := WfTm.rename hτ hΔ hr
      have hIdT' := WfTm.rename hIdT (hΔ.cons hτ') hr.lift
      have hCeq' := DefEq.rename hCeq ((hΔ.cons hτ').cons hIdT') hr.lift2
      have hdeq' := DefEq.rename hdeq hΔ hr
      simp only [Tm.rename, Tm.subst1_rename, Tm.weaken_rename, Ren.lift, Fin.cases_zero]
        at hIdT' hCeq' hdeq' ⊢
      exact DefEq.j hτ' hIdT' hCeq' hdeq' (DefEq.rename hpeq hΔ hr)
  | .jβ hτ ha hIdT hC hd => by
      have hτ' := WfTm.rename hτ hΔ hr
      have hIdT' := WfTm.rename hIdT (hΔ.cons hτ') hr.lift
      have hC' := WfTm.rename hC ((hΔ.cons hτ').cons hIdT') hr.lift2
      have hd' := WfTm.rename hd hΔ hr
      simp only [Tm.rename, Tm.subst1_rename, Tm.weaken_rename, Ren.lift, Fin.cases_zero]
        at hIdT' hC' hd' ⊢
      exact DefEq.jβ hτ' (WfTm.rename ha hΔ hr) hIdT' hC' hd'
end

theorem Ren.succ_wellTyped (Γ : Ctx n) (σ : Tm n) :
    Ren.WellTyped Fin.succ Γ (Γ ∷ σ) :=
  fun hlook => Lookup.there hlook

theorem WfTm.weaken (ht : Γ ⊢ t ∶ τ) (hΓσ : ⊢ Γ ∷ σ) : Γ ∷ σ ⊢ ↑ t ∶ ↑ τ:=
  WfTm.rename ht hΓσ (Ren.succ_wellTyped Γ σ)

theorem DefEq.weaken (heq : Γ ⊢ t₁ ≡ t₂ ∶ τ) (hΓσ : ⊢ Γ ∷ σ) :
    Γ ∷ σ ⊢ t₁.weaken ≡ t₂.weaken ∶ τ.weaken :=
  DefEq.rename heq hΓσ (Ren.succ_wellTyped Γ σ)
