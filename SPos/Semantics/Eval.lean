import SPos.Semantics.DomainTheory.Domain
import SPos.Semantics.ValueDomain

import SPos.Syntax.Syntax
import SPos.Syntax.SyntaxProperties

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

variable
  {D : Type u} [ScottDomain D Label]

local notation "DEnv" n => Env (fun _ => D) n

section
set_option hygiene false
notation:max "⟦" t "⟧𝒄 " => Tm.eval t

@[simp]
def Tm.eval : Tm n → (DEnv n) →𝒄 D
| .var i   => ƛ[ by fun_prop ] ρ ↦ ρ.get i
| .pi τ υ  => ƛ[ by fun_prop ] ρ ↦ Π̂ (⟦ τ ⟧𝒄 ρ) (ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ ∷ d))
| .lam _ t => ƛ[ by fun_prop ] ρ ↦ inj→ (ƛ[ by fun_prop ] d ↦ ⟦ t ⟧𝒄 (ρ ∷ d))
| .app t s => ƛ[ by fun_prop ] ρ ↦ ⟦ t ⟧𝒄 ρ •𝒄 ⟦ s ⟧𝒄 ρ
| .id τ a b => ƛ[ by fun_prop ] ρ ↦ Îd (⟦ τ ⟧𝒄 ρ) (⟦ a ⟧𝒄 ρ) (⟦ b ⟧𝒄 ρ)
| .refl _ _ => ƛ[ by fun_prop ] _ ↦ mkRefl
| .j _ d _ => ⟦ d ⟧𝒄
| .u ℓ     => ƛ[ by fun_prop ] ρ ↦ Û ℓ
end

@[simp]
theorem Tm.ap_lam_eval (τ : Tm n) (t : Tm (n + 1)) (ρ : DEnv n) (d : D) :
    ⟦ ƛ τ t ⟧𝒄 ρ •𝒄 d = ⟦ t ⟧𝒄 (ρ ∷ d) := by
  simp [Tm.eval, ScottDomain.lam.ret_inj]
