import SPos.Syntax.Syntax
import SPos.Syntax.SyntaxProperties
import SPos.Sem4.Domains.Dinf

abbrev DEnv (n : Nat) := Env (fun _ => D∞) n

@[fun_prop]
theorem Env.cons_scottContinuous [Preorder E] {g : E → DEnv n} {v : E → D∞}
    (hg : ScottContinuous g) (hv : ScottContinuous v) (i : Fin (n + 1)) :
    ScottContinuous fun e => (g e ∷ v e) i := by
  induction i using Fin.lastCases <;> simp [Env.cons] <;>fun_prop

section
set_option hygiene false

notation:max "⟦" t "⟧ᵈ" => Tm.eval t
noncomputable def Tm.eval (t : Tm n) : DEnv n →ₛ D∞ := match t with
| .var i           => ƛₛ ρ ↦ ρ.get i
| .u ℓ             => ƛₛ _ ↦ Dinf.univ ℓ
| .pi τ υ          => ƛₛ ρ ↦ Dinf.pi (⟦ τ ⟧ᵈ ρ) (ƛₛ d ↦ ⟦ υ ⟧ᵈ (ρ ∷ d))
| .sigma τ υ       => ƛₛ ρ ↦ Dinf.sigma (⟦ τ ⟧ᵈ ρ) (ƛₛ d ↦ ⟦ υ ⟧ᵈ (ρ ∷ d))
| .lam _ b         => ƛₛ ρ ↦ Dinf.lam (ƛₛ d ↦ ⟦ b ⟧ᵈ (ρ ∷ d))
| .mu B            => ƛₛ ρ ↦ Dinf.mu (ƛₛ d ↦ ⟦ B ⟧ᵈ (ρ ∷ d))
| .pair a b        => ƛₛ ρ ↦ Dinf.pair (⟦ a ⟧ᵈ ρ) (⟦ b ⟧ᵈ ρ)
| .id τ a b        => ƛₛ ρ ↦ Dinf.id (⟦ τ ⟧ᵈ ρ) (⟦ a ⟧ᵈ ρ) (⟦ b ⟧ᵈ ρ)
| .roll t          => ƛₛ ρ ↦ Dinf.roll (⟦ t ⟧ᵈ ρ)
| .refl _ _        => ƛₛ _ ↦ Dinf.refl
| .bool            => ƛₛ _ ↦ Dinf.bool
| .true            => ƛₛ _ ↦ Dinf.true
| .false           => ƛₛ _ ↦ Dinf.false
| .boolrec _ t f b => ƛₛ ρ ↦ Dinf.ite (⟦ b ⟧ᵈ ρ) (⟦ t ⟧ᵈ ρ) (⟦ f ⟧ᵈ ρ)
| .j _ d _         => ƛₛ ρ ↦ d.eval ρ
| .fst p           => ƛₛ ρ ↦ Dinf.fst (⟦ p ⟧ᵈ ρ)
| .snd p           => ƛₛ ρ ↦ Dinf.snd (⟦ p ⟧ᵈ ρ)
| .app t₁ t₂       => ƛₛ ρ ↦ (⟦ t₁ ⟧ᵈ ρ) (⟦ t₂ ⟧ᵈ ρ)
end

@[simp]
theorem Tm.eval_app_lam (τ : Tm n) (t : Tm (n + 1)) (ρ : DEnv n) (d : D∞) :
    (⟦ ƛ τ t ⟧ᵈ ρ) d = ⟦ t ⟧ᵈ (ρ ∷ d) := by simp [Tm.eval]

def Env.rename (r : Ren m n) (ρ : DEnv n) : DEnv m :=
  fun i => ρ.get (r i.rev)

@[simp]
theorem Env.get_rename (r : Ren m n) (ρ : DEnv n) (i : Fin m) :
    (ρ.rename r).get i = ρ.get (r i) := by
  simp [Env.rename, Env.get]; rw [Fin.rev_rev]

@[simp]
theorem Env.rename_lift_cons (r : Ren m n) (ρ : DEnv n) (v : D∞) :
    (ρ ∷ v).rename r.lift = ρ.rename r ∷ v := by
  apply Env.ext; intro i; induction i using Fin.cases <;> simp [Ren.lift]

@[simp]
theorem Env.rename_succ_cons (ρ : DEnv n) (v : D∞) :
    (ρ ∷ v).rename Fin.succ = ρ := by
  apply Env.ext; simp

@[simp]
theorem Tm.eval_rename (t : Tm n) (r : Ren n m) (ρ : DEnv m) :
    ⟦ t.rename r ⟧ᵈ ρ = ⟦ t ⟧ᵈ (ρ.rename r) := by
  induction t generalizing m
  all_goals simp_all [Tm.rename, Tm.eval]

@[simp]
theorem Tm.eval_weaken (t : Tm n) (ρ : DEnv n) (d : D∞) :
    ⟦ (↑ t : Tm (n + 1)) ⟧ᵈ (ρ ∷ d) = ⟦ t ⟧ᵈ ρ := by simp [Tm.weaken]

@[simp]
noncomputable def Subst.eval (σ : Subst n m) (ρ : DEnv m) : DEnv n :=
  fun i => ⟦ σ i.rev ⟧ᵈ ρ

@[simp]
theorem Subst.get_eval (σ : Subst n m) (ρ : DEnv m) (i : Fin n) :
    (σ.eval ρ).get i = ⟦ σ i ⟧ᵈ ρ := by simp

@[simp]
theorem Subst.eval_lift_cons (σ : Subst n m) (ρ : DEnv m) (d : D∞) :
    (σ.lift).eval (ρ ∷ d) = σ.eval ρ ∷ d := by
  apply Env.ext; intro i
  induction i using Fin.cases <;> simp [Subst.lift, Tm.eval]

@[simp]
theorem Subst.eval_single (u : Tm n) (ρ : DEnv n) :
    (Subst.single u).eval ρ = ρ ∷ ⟦ u ⟧ᵈ ρ := by
  apply Env.ext; intro i
  induction i using Fin.cases <;> simp [Subst.single, Tm.eval]

@[simp]
theorem Tm.eval_subst (t : Tm n) (σ : Subst n m) (ρ : DEnv m) :
    ⟦ t.subst σ ⟧ᵈ ρ = ⟦ t ⟧ᵈ (σ.eval ρ) := by
  induction t generalizing m <;> simp_all [Tm.subst, Tm.eval]

@[simp]
theorem Tm.eval_subst1 (t : Tm (n + 1)) (u : Tm n) (ρ : DEnv n) :
    ⟦ t [/ u ] ⟧ᵈ ρ = ⟦ t ⟧ᵈ (ρ ∷ ⟦ u ⟧ᵈ ρ) := by simp [Tm.subst1]
