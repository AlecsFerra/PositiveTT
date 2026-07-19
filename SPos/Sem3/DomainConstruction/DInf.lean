import SPos.Sem3.DomainConstruction.Approximation
import SPos.Sem3.DomainConstruction.Projection

structure DInf (φ : Type υ) where
  approx : ∀ n, Dn φ n
  bilimit : ∀ n, approx n = (approx $ n + 1).down

instance : Preorder (DInf φ) where
  le x y := ∀ n, x.approx n ≤ y.approx n
  le_refl := by intro _ _; simp
  le_trans := by
    intro _ _ _ hxy hyz n
    exact le_trans (hxy n) (hyz n)

def DInf.projn (n : Nat) : DInf φ →ₛ Dn φ n := by
  refine ƛₛ[ ?_ ] x ↦ DInf.approx x n
  intro x y hxy f u
  constructor
  · sorry
  · sorry
