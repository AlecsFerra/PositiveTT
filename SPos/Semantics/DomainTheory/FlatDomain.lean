import Mathlib.Order.OmegaCompletePartialOrder

open OmegaCompletePartialOrder

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

@[simp]
theorem Flat.bot_le (x : Flat F) : Flat.bot ≤ x := by trivial

@[simp]
theorem Flat.val_le_val : (Flat.val a ≤ Flat.val b) ↔ a = b
  := Iff.rfl

theorem Flat.chain_val_eq (c : Chain (Flat F))
    (hi : c i = .val a) (hj : c j = .val b) : a = b := by
  rcases le_total i j with h | h
  ·       simpa [hi, hj, Flat.val_le_val] using c.monotone h
  · symm; simpa [hi, hj, Flat.val_le_val] using c.monotone h

open Classical

noncomputable def Flat.ωSup (c : Chain (Flat F)) : Flat F :=
  if h : ∃ a, ∃ n, c n = .val a then .val h.choose else .bot

noncomputable instance : OmegaCompletePartialOrder (Flat F) where
  ωSup := Flat.ωSup
  le_ωSup := by
    intro c i
    unfold Flat.ωSup
    split
    · cases _ : c i
      simp
      obtain ⟨_, hn⟩ := ‹∃ a, _›.choose_spec
      simp_all [← Flat.chain_val_eq _ ‹c i = _› hn]
    · cases _ : c i <;> simp_all
  ωSup_le := by
    intros
    unfold Flat.ωSup
    split <;> grind [Flat.bot_le]

theorem Flat.ωSup_eq_bot (c : Chain (Flat F))
    (h : ∀ i, c i = .bot) : Flat.ωSup c = .bot := by
  unfold Flat.ωSup; rw [dif_neg]; rintro ⟨a, n, hn⟩; rw [h n] at hn; simp at hn

theorem Flat.ωSup_eq_val {c : Chain (Flat F)} {v : F} {n : ℕ}
    (hn : c n = .val v) : Flat.ωSup c = .val v := by
  have hex : ∃ a, ∃ k, c k = .val a := ⟨v, n, hn⟩
  unfold Flat.ωSup; rw [dif_pos hex]
  obtain ⟨m, hm⟩ := hex.choose_spec
  exact congrArg Flat.val (Flat.chain_val_eq c hm hn)

instance : Bot (Flat F) where
  bot := .bot
