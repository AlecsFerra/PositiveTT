import SPos.Syntax.Syntax
import SPos.Sem4.Domains.Dinf

abbrev DEnv (n : Nat) := Env (fun _ => D∞) n

@[fun_prop]
theorem Env.cons_scottContinuous [Preorder E] {g : E → DEnv n} {v : E → D∞}
    (hg : ScottContinuous g) (hv : ScottContinuous v) (i : Fin (n + 1)) :
    ScottContinuous fun e => (g e ∷ v e) i := by
  induction i using Fin.lastCases <;>
    simp only [Env.cons, Fin.lastCases_last, Fin.lastCases_castSucc] <;> fun_prop

noncomputable def Tm.eval (t : Tm n) : DEnv n →ₛ D∞ := match t with
| .var i     => ƛₛ ρ ↦ ρ.get i
| .u ℓ       => ƛₛ _ ↦ Dinf.univ ℓ
| .pi τ υ    => ƛₛ ρ ↦ Dinf.pi (τ.eval ρ) (ƛₛ d ↦ υ.eval (ρ ∷ d))
| .sigma τ υ => ƛₛ ρ ↦ Dinf.sigma (τ.eval ρ) (ƛₛ d ↦ υ.eval (ρ ∷ d))
| .lam _ b   => ƛₛ ρ ↦ Dinf.lam (ƛₛ d ↦ b.eval (ρ ∷ d))
| .mu B      => ƛₛ ρ ↦ Dinf.mu (ƛₛ d ↦ B.eval (ρ ∷ d))
| .pair a b  => ƛₛ ρ ↦ Dinf.pair (a.eval ρ) (b.eval ρ)
| .id τ a b  => ƛₛ ρ ↦ Dinf.id (τ.eval ρ) (a.eval ρ) (b.eval ρ)
| .roll t    => ƛₛ ρ ↦ Dinf.roll (t.eval ρ)
| .refl _ _  => ƛₛ _ ↦ Dinf.refl
| .bool      => ƛₛ _ ↦ Dinf.bool
| .true      => ƛₛ _ ↦ Dinf.true
| .false     => ƛₛ _ ↦ Dinf.false
| .boolrec _ t f b => ƛₛ ρ ↦ Dinf.ite (b.eval ρ) (t.eval ρ) (f.eval ρ)
| .j _ d _   => ƛₛ ρ ↦ d.eval ρ
| .fst p     => ƛₛ ρ ↦ Dinf.fst (p.eval ρ)
| .snd p     => ƛₛ ρ ↦ Dinf.snd (p.eval ρ)
| .app t₁ t₂ => ƛₛ ρ ↦ Dinf.app (t₁.eval ρ) (t₂.eval ρ)
