import Mathlib.Data.Fin.Rev

import SPos.Syntax.Syntax

variable {α : Nat → Type u} {β : Type u}

theorem Env.ext {ρ ρ' : Env α n} (h : ∀ i, ρ.get i = ρ'.get i) : ρ = ρ' := by
    funext i; rw [← Fin.rev_rev i]; simp [h]

theorem Env.cons_inj {ρ ρ' : Env α n} {v v' : α n} (h : (ρ ∷ v) = (ρ' ∷ v')) :
    ρ = ρ' ∧ v = v' := by
  constructor
  · funext i; simpa [Env.cons] using congrFun h i.castSucc
  · simpa [Env.cons] using congrFun h (Fin.last n)

theorem Env.entry_congr (ρ : Env α n) {i j : Fin n} (h : i = j) : HEq (ρ i) (ρ j) := by
  cases h; rfl

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

@[simp]
theorem Ren.lift_comp (r₁ : Ren n m) (r₂ : Ren m k) :
    Ren.lift (r₂ ∘ r₁) = Ren.lift r₂ ∘ Ren.lift r₁ := by
  funext i; induction i using Fin.cases <;> simp [Ren.lift]

@[simp]
theorem Tm.rename_rename (t : Tm n) (r₁ : Ren n m) (r₂ : Ren m k) :
    (t.rename r₁).rename r₂ = t.rename (r₂ ∘ r₁) := by
  induction t generalizing m k <;> simp_all [Tm.rename]

@[simp]
theorem Ren.lift_succ (r : Ren n m) : r.lift ∘ Fin.succ = Fin.succ ∘ r := by
  funext i; simp [Ren.lift]

@[simp]
theorem Tm.weaken_rename (t : Tm n) (r : Ren n m) :
    t.weaken.rename r.lift = ↑ (t.rename r) := by simp [Tm.weaken]

@[simp]
theorem Subst.rename_lift (σ : Subst n m) (r : Ren m k) :
    Subst.lift (fun i => (σ i).rename r) = fun i => (σ.lift i).rename r.lift := by
  funext i; induction i using Fin.cases <;> simp [Ren.lift, Tm.weaken, Tm.rename, Subst.lift]

@[simp]
theorem Tm.subst_rename (t : Tm n) (σ : Subst n m) (r : Ren m k) :
    (t.subst σ).rename r = t.subst (fun i => (σ i).rename r) := by
  induction t generalizing m k <;> simp_all [Tm.subst, Tm.rename]

@[simp]
theorem Ren.subst_lift (r : Ren n m) (σ : Subst m k) :
    Subst.lift (fun i => σ (r i)) = fun i => Subst.lift σ (Ren.lift r i) := by
  funext i; induction i using Fin.cases <;> simp [Ren.lift, Subst.lift]

@[simp]
theorem Tm.rename_subst (t : Tm n) (r : Ren n m) (σ : Subst m k) :
    (t.rename r).subst σ = t.subst (fun i => σ (r i)) := by
  induction t generalizing m k <;> simp_all [Tm.rename, Tm.subst]

theorem Subst.lift_succ (σ : Subst n m) :
    (fun i => Subst.lift σ (Fin.succ i)) = fun i => (σ i).rename Fin.succ := by
  funext i; simp [Tm.weaken, Subst.lift]

theorem Tm.weaken_subst (t : Tm n) (σ : Subst n m) :
    t.weaken.subst (Subst.lift σ) = (t.subst σ).weaken := by simp [Tm.weaken, Subst.lift]

@[simp]
theorem Subst.var_lift : Subst.lift (Tm.var : Subst n n) = (Tm.var : Subst (n + 1) (n + 1)) := by
  funext i; induction i using Fin.cases <;> simp [Tm.weaken, Tm.rename, Subst.lift]

@[simp]
theorem Tm.subst_var (t : Tm n) : t.subst Tm.var = t := by
  induction t <;> simp_all [Tm.subst]

@[simp]
theorem Tm.weaken_subst1 (t : Tm n) (v : Tm n) : t.weaken [/ v] = t := by
  simp [Tm.subst1, Tm.weaken, Subst.single]

@[simp]
theorem Subst.lift_subst (σ₁ : Subst n m) (σ₂ : Subst m k) :
    Subst.lift (fun i => (σ₁ i).subst σ₂) = fun i => (σ₁.lift i).subst σ₂.lift := by
  funext i; induction i using Fin.cases <;> simp [Tm.weaken, Tm.subst, Subst.lift]
@[simp]
theorem Tm.subst_subst (t : Tm n) (σ₁ : Subst n m) (σ₂ : Subst m k) :
    (t.subst σ₁).subst σ₂ = t.subst (fun i => (σ₁ i).subst σ₂) := by
  induction t generalizing m k <;> simp_all [Tm.subst]

@[simp]
theorem Tm.subst1_subst (t : Tm (n + 1)) (u : Tm n) (θ : Subst n m) :
    (t [/ u]).subst θ = t.subst θ.lift [/u.subst θ] := by
  simp [Tm.subst1]; congr 1; funext i
  induction i using Fin.cases <;> simp [Subst.single, Tm.subst, Subst.lift, Tm.weaken]

theorem Ren.single_lift (r : Ren n m) (u : Tm n) :
    (fun i => (Subst.single u i).rename r) = fun i => Subst.single (u.rename r) (Ren.lift r i) := by
  funext i; induction i using Fin.cases <;> simp [Subst.single, Ren.lift, Tm.rename]

@[simp]
theorem Tm.subst1_rename (t : Tm (n + 1)) (u : Tm n) (r : Ren n m) :
    (t [/ u]).rename r = t.rename r.lift [/u.rename r] := by
  simp [Tm.subst1, Ren.single_lift]

theorem Tm.subst_lift_single (t : Tm (n + 2)) (b p : Tm n) :
    (t.subst (Subst.lift (Subst.single b))) [/ p ] = t [/ ↑ p ] [/ b ] := by
  simp only [Tm.subst1, Tm.subst_subst]
  congr 1; funext i
  induction i using Fin.cases <;>
    simp only [Subst.lift, Subst.single, Fin.cases_zero, Fin.cases_succ, Tm.subst,
      Tm.weaken, Tm.rename_subst, Tm.subst_var]

theorem Tm.rename_eq_subst (t : Tm n) (r : Ren n m) :
    t.rename r = t.subst (fun i => # (r i)) := by
  induction t generalizing m <;> simp_all [Tm.rename, Tm.subst]
