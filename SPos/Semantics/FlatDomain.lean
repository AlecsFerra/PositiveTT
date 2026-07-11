import Mathlib.Order.OmegaCompletePartialOrder

inductive Flat (F : Type v)
| bot : Flat F
| val : F → Flat F
deriving Inhabited, DecidableEq

@[simp]
def Flat.le : Flat F → Flat F → Prop
| .bot,   _      => True
| .val x, .val y => x = y
| _,      _      => False

instance : Preorder (Flat F) where
  le := Flat.le
  le_refl a := by
    cases a
    all_goals simp

  le_trans a b c p q := by
    cases a <;> cases b <;> cases c <;> cases p <;> cases q
    all_goals simp

instance : PartialOrder (Flat F) where
  le_antisymm a b p q := by
    cases a <;> cases b <;> cases p <;> cases q
    all_goals simp

instance : OmegaCompletePartialOrder (Flat F) where
  ωSup s := sorry
  le_ωSup s n := sorry
  ωSup_le s a h := by sorry

instance : Bot (Flat F) where
  bot := .bot
