import Mathlib.Order.OmegaCompletePartialOrder

import SPos.Semantics.Continuous
import SPos.Semantics.FlatDomain

open OmegaCompletePartialOrder

structure Embedding (E : Type v) (D : Type u)
  [OmegaCompletePartialOrder E] [OmegaCompletePartialOrder D] where
  inj : E →𝒄 D
  ret : D →𝒄 E
  ret_inj : ∀ e, ret (inj e) = e
  inj_ret : ∀ d, inj (ret d) ≤ d

class ScottDomain (D : Type u) (F : outParam (Type v))
  extends OmegaCompletePartialOrder D, OrderBot D where
  flat : Embedding (Flat F) D
  pair : Embedding (D × D) D
  lam : Embedding (D →𝒄 D) D
  -- The three kinds of codes are discriminable: retracting a code of a
  -- different kind yields bottom.
  flat_pair : ∀ p, flat.ret (pair.inj p) = ⊥
  pair_flat : ∀ x, pair.ret (flat.inj x) = ⊥
attribute [simp] ScottDomain.flat_pair ScottDomain.pair_flat
open ScottDomain

@[simp]
def ScottDomain.app [ScottDomain D F] : D →𝒄 D →𝒄 D :=
  lam.ret
infixr:60 "•𝒄" => ScottDomain.app

@[simp]
theorem ScottDomain.app_inj [ScottDomain D F] (f : D →𝒄 D) (x : D) :
  (lam.inj f) •𝒄 x = f x := by
  simp [lam.ret_inj]

@[simp]
def ScottDomain.mk_pair [ScottDomain D F] : D × D →𝒄 D :=
  pair.inj
notation  a ",𝒄" b => ScottDomain.mk_pair (a , b)

@[simp]
def ScottDomain.mk_flat [ScottDomain D F] : Flat F →𝒄 D :=
  flat.inj
prefix:(max - 1) "#𝒄" => fun x => ScottDomain.mk_flat (Flat.val x)

@[simp]
def ScottDomain.mk_lam [ScottDomain D F] : (D →𝒄 D) →𝒄 D :=
  lam.inj
notation "inj→" => ScottDomain.mk_lam

@[simp]
theorem ScottDomain.flat_ret_bot [ScottDomain D F] : flat.ret (⊥ : D) = .bot := by
  have h : flat.ret (⊥ : D) ≤ Flat.bot := by
    have := flat.ret.monotone (bot_le : (⊥ : D) ≤ flat.inj .bot)
    rwa [flat.ret_inj] at this
  cases hx : flat.ret (⊥ : D) with
  | bot   => rfl
  | val v => rw [hx] at h; cases h
