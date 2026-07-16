import Mathlib.Order.Lattice
import SPos.Syntax.Syntax

inductive Polarity where
| both | positive | negative | none
deriving DecidableEq, Repr

def Polarity.le : Polarity → Polarity → Prop
| .none,     _         => True
| _,         .both     => True
| .positive, .positive => True
| .negative, .negative => True
| _,         _         => False

instance : DecidableRel Polarity.le := fun a b => by
  cases a <;> cases b
  all_goals simp [Polarity.le]; infer_instance

def Polarity.lub : Polarity → Polarity → Polarity
| .both, _ | _, .both => .both
| .none, x | x, .none => x
| .positive, .positive => .positive
| .negative, .negative => .negative
| .positive, .negative
| .negative, .positive => .both

instance : Max Polarity := ⟨Polarity.lub⟩

def Polarity.flip : Polarity → Polarity
| .both     => .both
| .positive => .negative
| .negative => .positive
| .none     => .none

instance : Neg Polarity := ⟨Polarity.flip⟩

instance : LE Polarity := ⟨Polarity.le⟩
instance : Top Polarity := ⟨.both⟩
instance : Bot Polarity := ⟨.none⟩

def Polarity.inv (p : Polarity) : Polarity := p ⊔ -p

def Tm.polarity (t : Tm n) (x : Fin n) : Polarity := match t with
-- TODO
| _ => .none
