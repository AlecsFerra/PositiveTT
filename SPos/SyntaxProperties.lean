import Mathlib.Data.Fin.Rev

import SPos.Syntax

variable {α : Nat → Type u} {β : Type u}

/-- Environments with the same lookups are equal. -/
theorem Env.ext {ρ ρ' : Env α n} (h : ∀ i, ρ.get i = ρ'.get i) : ρ = ρ' :=
  funext fun j => by
    rw [← Fin.rev_rev j]
    exact h j.rev

theorem Env.cons_inj {ρ ρ' : Env α n} {v v' : α n} (h : (ρ ∷ v) = (ρ' ∷ v')) :
    ρ = ρ' ∧ v = v' := by
  refine ⟨funext fun i => ?_, ?_⟩
  · simpa [Env.cons] using congrFun h i.castSucc
  · simpa [Env.cons] using congrFun h (Fin.last n)

/-- Entries at equal indices are (heterogeneously) equal. -/
theorem Env.entry_congr (ρ : Env α n) {i j : Fin n} (h : i = j) : HEq (ρ i) (ρ j) := by
  cases h; rfl

/-- The newest entry is variable `0`. -/
@[simp]
theorem Env.get_cons_zero (ρ : Env α n) (v : α n) : (ρ ∷ v).get 0 = v :=
  Fin.lastCases_last

theorem Env.get_cons_succ_heq (ρ : Env α n) (v : α n) (i : Fin n) :
    HEq ((ρ ∷ v).get i.succ) (ρ.get i) :=
  ((ρ ∷ v).entry_congr (Fin.rev_succ i)).trans (heq_of_eq (Fin.lastCases_castSucc ..))

@[simp]
theorem Env.get_cons_succ (ρ : Env (fun _ => β) n) (v : β) (i : Fin n) :
    (ρ ∷ v).get i.succ = ρ.get i :=
  eq_of_heq (ρ.get_cons_succ_heq v i)
