import SPos.Semantics.Eval
import SPos.Syntax.SyntaxProperties

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
  apply Env.ext; intro i; induction i using Fin.cases <;> simp [Ren.lift]

@[simp]
theorem Env.rename_succ_cons (ρ : DEnv n) (v : D) :
    (ρ ∷ v).rename Fin.succ = ρ := by
  apply Env.ext; simp

variable [ScottDomain D Label]

@[simp]
theorem Tm.eval_rename (t : Tm n) (r : Ren n m) (ρ : DEnv m)
  : ⟦ t.rename r ⟧𝒄 ρ = ⟦ t ⟧𝒄 (ρ.rename r) := by
  induction t generalizing m
  all_goals simp_all [Tm.rename]

/-- Weakening a term makes it ignore the newest variable. -/
@[simp]
theorem Tm.eval_weaken (t : Tm n) (ρ : DEnv n) (d : D) :
    ⟦ t.weaken ⟧𝒄 (ρ ∷ d) = ⟦ t ⟧𝒄 ρ := by simp [Tm.weaken]

@[simp]
def Subst.eval (σ : Subst n m) (ρ : DEnv m) : DEnv n :=
  fun i => ⟦ σ i.rev ⟧𝒄 ρ

@[simp]
theorem Subst.get_eval (σ : Subst n m) (ρ : DEnv m) (i : Fin n) :
    (σ.eval ρ).get i = ⟦ σ i ⟧𝒄 ρ := by simp

@[simp]
theorem Subst.eval_lift_cons (σ : Subst n m) (ρ : DEnv m) (d : D) :
    (σ.lift).eval (ρ ∷ d) = σ.eval ρ ∷ d := by
  apply Env.ext; intro i
  induction i using Fin.cases <;> simp [Subst.lift]

@[simp]
theorem Subst.eval_single (u : Tm n) (ρ : DEnv n) :
    (Subst.single u).eval ρ = ρ ∷ ⟦ u ⟧𝒄 ρ := by
  apply Env.ext; intro i
  induction i using Fin.cases <;> simp [Subst.single]

@[simp]
theorem Tm.eval_subst (t : Tm n) (σ : Subst n m) (ρ : DEnv m)
  : ⟦ t.subst σ ⟧𝒄 ρ = ⟦ t ⟧𝒄 (σ.eval ρ) := by
  induction t generalizing m
  all_goals simp_all [Tm.subst]

@[simp]
theorem Tm.eval_subst1 (t : Tm (n + 1)) (u : Tm n) (ρ : DEnv n) :
    ⟦ t [/ u ] ⟧𝒄 ρ = ⟦ t ⟧𝒄 (ρ ∷ ⟦ u ⟧𝒄 ρ) := by simp [Tm.subst1]
