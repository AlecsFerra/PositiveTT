import SPos.Semantics.Eval
import SPos.SyntaxProperties

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

variable {D : Type u}

local notation "DEnv" n => Env (fun _ => D) n

def Env.rename (r : Ren m n) (ρ : DEnv n) : DEnv m :=
  fun i => ρ.get (r i.rev)

@[simp]
theorem Env.get_rename (r : Ren m n) (ρ : DEnv n) (i : Fin m) :
    (ρ.rename r).get i = ρ.get (r i) := by
  simp [Env.rename, Env.get]; rw [Fin.rev_rev]

@[simp]
theorem Env.rename_lift_cons (r : Ren m n) (ρ : DEnv n) (v : D) :
    (ρ ∷ v).rename r.lift = ρ.rename r ∷ v := by
  apply Env.ext; intro i; induction i using Fin.cases <;> simp

@[simp]
theorem Env.rename_succ_cons (ρ : DEnv n) (v : D) :
    (ρ ∷ v).rename Fin.succ = ρ := by
  apply Env.ext; simp

variable [ScottDomain D Label]

theorem Tm.eval_rename (t : Tm n) (r : Ren n m) (ρ : DEnv m)
  : ⟦ t.rename r ⟧𝒄 ρ = ⟦ t ⟧𝒄 (ρ.rename r) := by
  induction t generalizing m
  all_goals simp_all

/-- Weakening a term makes it ignore the newest variable. -/
@[simp]
theorem Tm.eval_weaken (t : Tm n) (ρ : DEnv n) (d : D) :
    ⟦ t.weaken ⟧𝒄 (ρ ∷ d) = ⟦ t ⟧𝒄 ρ := by
  simp only [Tm.weaken, Tm.eval_rename, Env.rename_succ_cons]

def Subst.eval (σ : Subst n m) (ρ : DEnv m) : DEnv n :=
  fun i => ⟦ σ i.rev ⟧𝒄 ρ

@[simp]
theorem Subst.get_eval (σ : Subst n m) (ρ : DEnv m) (i : Fin n) :
    (σ.eval ρ).get i = ⟦ σ i ⟧𝒄 ρ := by
  simp [Subst.eval, Env.get, Fin.rev_rev]

@[simp]
theorem Subst.eval_lift_cons (σ : Subst n m) (ρ : DEnv m) (d : D) :
    (σ.lift).eval (ρ ∷ d) = σ.eval ρ ∷ d := by
  apply Env.ext; intro i; induction i using Fin.cases with
  | zero   => simp
  | succ j => simp only [Subst.get_eval, Env.get_cons_succ, Subst.lift, Fin.cases_succ, Tm.eval_weaken]

@[simp]
theorem Subst.eval_single (u : Tm n) (ρ : DEnv n) :
    (Subst.single u).eval ρ = ρ ∷ ⟦ u ⟧𝒄 ρ := by
  apply Env.ext; intro i; induction i using Fin.cases <;> simp [Tm.eval]

theorem Tm.eval_subst (t : Tm n) (σ : Subst n m) (ρ : DEnv m)
  : ⟦ t.subst σ ⟧𝒄 ρ = ⟦ t ⟧𝒄 (σ.eval ρ) := by
  induction t generalizing m
  all_goals simp_all

@[simp]
theorem Tm.eval_subst1 (t : Tm (n + 1)) (u : Tm n) (ρ : DEnv n) :
    ⟦ t [/ u ] ⟧𝒄 ρ = ⟦ t ⟧𝒄 (ρ ∷ ⟦ u ⟧𝒄 ρ) := by
  simp only [Tm.subst1, Tm.eval_subst, Subst.eval_single]
