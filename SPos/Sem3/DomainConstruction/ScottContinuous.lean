import Mathlib.Order.ScottContinuity

structure ScottContinuousF (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  to_fun : D → E
  scott_continuous : ScottContinuous to_fun

infixr:25 "→ₛ" => ScottContinuousF

instance [Preorder D] [Preorder E] : FunLike (D →ₛ E) D E where
  coe f := f.to_fun
  coe_injective f g h := by cases f; cases g; congr

structure Embedding (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  inj : D →ₛ E
  ret : E →ₛ D
  ret_inj : ∀ e, ret (inj e) = e
  inj_ret : ∀ d, inj (ret d) ≤ d

notation "ƛₛ[" p "]" a "↦" b => ScottContinuousF.mk (fun a ↦ b) p

notation "ƛₒ[" p "]" a "↦" b => OrderHom.mk (fun a ↦ b) p

@[simp]
theorem ScottContinuousF.mk_lam_apply [Preorder α] [Preorder β]
  (f : α → β) (h : ScottContinuous f) (x : α)
  : (ScottContinuousF.mk f h) x = f x := rfl

attribute [fun_prop] ScottContinuous.id
attribute [fun_prop] ScottContinuous.comp
attribute [fun_prop] ScottContinuous.const
attribute [fun_prop] ScottContinuousF.scott_continuous

@[fun_prop]
theorem ScottContinuousF.scottContinuous [Preorder α] [Preorder β]
  (f : α →ₛ β) : ScottContinuous (fun x => f x) := f.scott_continuous

@[fun_prop]
theorem Embedding.inj_scottContinuous [Preorder D] [Preorder E] (e : Embedding D E) :
    ScottContinuous (fun x => e.inj x) := e.inj.scott_continuous

@[fun_prop]
theorem Embedding.ret_scottContinuous [Preorder D] [Preorder E] (e : Embedding D E) :
    ScottContinuous (fun x => e.ret x) := e.ret.scott_continuous
