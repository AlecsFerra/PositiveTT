import SPos.Typing.Typing
import SPos.Syntax.SyntaxProperties

inductive Lookup.Inv (Γ : Ctx n) (τ : Tm n) (i : Fin (n + 1)) (σ : Tm (n + 1)) : Prop where
| here (hi : i = 0) (hσ : σ = τ.weaken)
| there (j : Fin n) (τ' : Tm n) (hi : i = j.succ) (hσ : σ = τ'.weaken) (hj : Γ ∋ j ∶ τ')

theorem Lookup.inv (h : Δ ∋ i ∶ σ) (hΔ : Δ = Γ ∷ τ) : Lookup.Inv Γ τ i σ := by
  cases h with
  | here     => obtain ⟨rfl, rfl⟩ := Env.cons_inj hΔ; exact .here rfl rfl
  | there hj => obtain ⟨rfl, rfl⟩ := Env.cons_inj hΔ; exact .there _ _ rfl rfl hj
