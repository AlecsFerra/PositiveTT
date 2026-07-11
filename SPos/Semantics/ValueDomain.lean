import SPos.Semantics.Domain

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

inductive Label where
| U  : Nat → Label
| Pi : Label

variable {D : Type u} [ScottDomain D Label]

def ScottDomain.mkPi : D →𝒄 (D →𝒄 D) →𝒄 D :=
  ƛ[ by fun_prop ] d ↦ ƛ[ by fun_prop ] c ↦ (#𝒄 .Pi ,𝒄 d ,𝒄 lam.inj c)

notation "Π̂" => ScottDomain.mkPi

def ScottDomain.unPi (d : D) : Option (D × (D →𝒄 D)) :=
  let (l, rest) := pair.ret d
  match flat.ret l with
  | .val .Pi =>
    let (a, f) := pair.ret rest
    some (a, lam.ret f)
  | _ => none

@[simp]
theorem ScottDomain.unPi_mkPi (d : D) (c : D →𝒄 D) : unPi (Π̂ d c) = some (d, c) := by
  simp [unPi, mkPi, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj, lam.ret_inj]

def ScottDomain.mkU (n : Nat) : D :=
  #𝒄 (.U n)

prefix:(max - 1) "Û" => ScottDomain.mkU

def ScottDomain.unU (d : D) : Option Nat :=
  match flat.ret d with
  | .val (.U n) => some n
  | _ => none

@[simp]
theorem ScottDomain.unU_mkU (n : Nat) : unU (mkU (D := D) n) = some n := by
  simp [unU, mkU, flat.ret_inj]

-- Disjointess theorems
@[simp]
theorem ScottDomain.unU_mkPi (a : D) (f : D →𝒄 D) : unU (Π̂ a f) = none := by
  simp [unU, mkPi, ωScottContinuous.mk_lam]

@[simp]
theorem ScottDomain.unPi_mkU (n : Nat) : unPi (mkU (D := D) n) = none := by
  simp [unPi, mkU]

theorem ScottDomain.mkU_inj (h : mkU (D := D) ℓ = mkU ℓ') : ℓ = ℓ' := by
  simpa using congrArg unU h

theorem ScottDomain.mkPi_inj {f f' : D →𝒄 D} (h : Π̂ a f = Π̂ a' f') :
    a = a' ∧ f = f' := by
  simpa [Prod.ext_iff] using congrArg unPi h

theorem ScottDomain.mkU_ne_mkPi (ℓ : Nat) (a : D) (f : D →𝒄 D) : mkU ℓ ≠ Π̂ a f := by
  intro h; simpa using congrArg unU h
