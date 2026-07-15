import SPos.Semantics.DomainTheory.Domain

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

inductive Label where
| U  : Nat → Label
| Pi : Label
| Sigma : Label
| Pair : Label
| Bool : Label
| True : Label
| False : Label
| Id : Label
| Refl : Label

variable {D : Type u} [ScottDomain D Label]

noncomputable section

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

def ScottDomain.mkSigma : D →𝒄 (D →𝒄 D) →𝒄 D :=
  ƛ[ by fun_prop ] d ↦ ƛ[ by fun_prop ] c ↦ (#𝒄 .Sigma ,𝒄 d ,𝒄 lam.inj c)

notation "Σ̂" => ScottDomain.mkSigma

def ScottDomain.unSigma (d : D) : Option (D × (D →𝒄 D)) :=
  let (l, rest) := pair.ret d
  match flat.ret l with
  | .val .Sigma =>
    let (a, f) := pair.ret rest
    some (a, lam.ret f)
  | _ => none

def ScottDomain.mkPair : D →𝒄 D →𝒄 D :=
  ƛ[ by fun_prop ] a ↦ ƛ[ by fun_prop ] b ↦ (#𝒄 .Pair ,𝒄 a ,𝒄 b)

def ScottDomain.unPair (d : D) : Option (D × D) :=
  match Prod.map flat.ret pair.ret (pair.ret d) with
  | (.val Label.Pair, (a, b)) => some (a, b)
  | _                         => none

def ScottDomain.proj₁ : D →𝒄 D :=
  ƛ[ by fun_prop ] d ↦ (pair.ret (pair.ret d).2).1

def ScottDomain.proj₂ : D →𝒄 D :=
  ƛ[ by fun_prop ] d ↦ (pair.ret (pair.ret d).2).2


@[simp]
theorem ScottDomain.proj₁_mkPair (a b : D) : proj₁ (mkPair a b) = a := by
  simp [proj₁, mkPair, ωScottContinuous.mk_lam, pair.ret_inj]
@[simp]
theorem ScottDomain.proj₂_mkPair (a b : D) : proj₂ (mkPair a b) = b := by
  simp [proj₂, mkPair, ωScottContinuous.mk_lam, pair.ret_inj]

def ScottDomain.mkU (n : Nat) : D :=
  #𝒄 (.U n)

prefix:(max - 1) "Û" => ScottDomain.mkU

def ScottDomain.unU (d : D) : Option Nat :=
  match flat.ret d with
  | .val (.U n) => some n
  | _           => none

def ScottDomain.mkId : D →𝒄 D →𝒄 D →𝒄 D :=
  ƛ[ by fun_prop ] a ↦ ƛ[ by fun_prop ] x ↦ ƛ[ by fun_prop ] y ↦ (#𝒄 .Id ,𝒄 a ,𝒄 x ,𝒄 y)

notation "Îd" => ScottDomain.mkId

def ScottDomain.unId (d : D) : Option (D × D × D) :=
  let (l, rest) := pair.ret d
  match flat.ret l with
  | .val .Id =>
    let (a, xy) := pair.ret rest
    let (x, y)  := pair.ret xy
    some (a, x, y)
  | _ => none

def ScottDomain.mkRefl : D := #𝒄 .Refl

def ScottDomain.mkBool  : D := #𝒄 .Bool

def ScottDomain.unBool (d : D) : Bool :=
  match flat.ret d with
  | .val .Bool => true
  | _          => false

def ScottDomain.mkTrue  : D := #𝒄 .True
def ScottDomain.mkFalse : D := #𝒄 .False


@[simp]
theorem ScottDomain.flat_ret_mkTrue : flat.ret (mkTrue : D) = .val .True := by
  simp [mkTrue, flat.ret_inj]
@[simp]
theorem ScottDomain.flat_ret_mkFalse : flat.ret (mkFalse : D) = .val .False := by
  simp [mkFalse, flat.ret_inj]

theorem ScottDomain.mkTrue_ne_mkFalse : (mkTrue : D) ≠ mkFalse := by
  intro h; have := congrArg flat.ret h; simp at this

def ScottDomain.boolBrancher (t f : D) : Flat Label → D
| .val .True => t
| .val .False => f
| _ => ⊥

theorem ScottDomain.boolBrancher_mono (t f : D) (hl : l ≤ l') :
    boolBrancher t f l ≤ boolBrancher t f l' := by
    cases l <;> cases l' <;> simp_all [LE.le, boolBrancher]

theorem ScottDomain.boolBrancher_cont (t f : D) : ωScottContinuous (boolBrancher t f) := by
  apply ωScottContinuous.of_monotone_map_ωSup
  refine ⟨fun _ _ h => boolBrancher_mono t f h, fun c => ?_⟩
  by_cases hval : ∃ lbl, ∃ n, c n = Flat.val lbl
  · obtain ⟨lbl, N, hN⟩ := hval
    rw [show ωSup c = Flat.val lbl from Flat.ωSup_eq_val hN]
    apply le_antisymm
    · calc boolBrancher t f (Flat.val lbl)
          = (c.map ⟨boolBrancher t f, fun _ _ h => boolBrancher_mono t f h⟩) N := by simp [hN]
        _ ≤ _ := le_ωSup _ N
    · apply ωSup_le
      intro i
      show boolBrancher t f (c i) ≤ boolBrancher t f (Flat.val lbl)
      cases hi : c i with
      | bot => exact bot_le
      | val lbl' => obtain rfl := Flat.chain_val_eq c hi hN; exact le_refl _
  · push Not at hval
    have hbot : ∀ i, c i = Flat.bot := fun i => by
      cases h : c i with
      | bot => rfl
      | val lbl => exact absurd h (hval lbl i)
    rw [show ωSup c = Flat.bot from Flat.ωSup_eq_bot _ hbot]
    refine le_antisymm bot_le (ωSup_le _ _ (fun i => ?_))
    show boolBrancher t f (c i) ≤ boolBrancher t f Flat.bot
    rw [hbot i]

/-- The boolean recursor's action as a continuous map in the scrutinee. -/
def ScottDomain.boolCase (t f : D) : D →𝒄 D :=
  (ωScottContinuous.mk_lam (boolBrancher t f) (boolBrancher_cont t f)).comp flat.ret

@[simp]
theorem ScottDomain.boolCase_mkTrue (t f : D) : boolCase t f mkTrue = t := by
  simp [boolCase, boolBrancher]
@[simp]
theorem ScottDomain.boolCase_mkFalse (t f : D) : boolCase t f mkFalse = f := by
  simp [boolCase, boolBrancher]

theorem ScottDomain.boolCase_cont_t (f b : D) :
    ωScottContinuous (fun t : D => boolCase t f b) := by
  show ωScottContinuous (fun t => boolBrancher t f (flat.ret b))
  cases flat.ret b with
  | bot => exact ωScottContinuous.const
  | val lbl => cases lbl <;> first | exact ωScottContinuous.id | exact ωScottContinuous.const

theorem ScottDomain.boolCase_cont_f (t b : D) :
    ωScottContinuous (fun f : D => boolCase t f b) := by
  show ωScottContinuous (fun f => boolBrancher t f (flat.ret b))
  cases flat.ret b with
  | bot => exact ωScottContinuous.const
  | val lbl => cases lbl <;> first | exact ωScottContinuous.id | exact ωScottContinuous.const

-- Booleans are all flat, so `flat.ret` discriminates them from the pair-based codes and
-- from `mkU`.
@[simp] theorem ScottDomain.unU_mkBool : unU (mkBool : D) = none := by simp [unU, mkBool, flat.ret_inj]
@[simp] theorem ScottDomain.unBool_mkU (n : Nat) : unBool (mkU (D := D) n) = false := by
  simp [unBool, mkU, flat.ret_inj]
@[simp] theorem ScottDomain.unBool_mkBool : unBool (mkBool : D) = true := by
  simp [unBool, mkBool, flat.ret_inj]
@[simp] theorem ScottDomain.unBool_mkPi (a : D) (f : D →𝒄 D) : unBool (Π̂ a f) = false := by
  simp [unBool, mkPi, ωScottContinuous.mk_lam]
@[simp] theorem ScottDomain.unBool_mkSigma (a : D) (f : D →𝒄 D) : unBool (Σ̂ a f) = false := by
  simp [unBool, mkSigma, ωScottContinuous.mk_lam]
@[simp] theorem ScottDomain.unBool_mkId (a x y : D) : unBool (Îd a x y) = false := by
  simp [unBool, mkId, ωScottContinuous.mk_lam]
@[simp] theorem ScottDomain.unPi_mkBool: unPi (mkBool : D) = none := by
  simp [unPi, mkBool]
@[simp] theorem ScottDomain.unSigma_mkBool : unSigma (mkBool : D) = none := by
  simp [unSigma, mkBool]
@[simp] theorem ScottDomain.unId_mkBool : unId (mkBool : D) = none := by
  simp [unId, mkBool]

@[simp]
theorem ScottDomain.unPi_mkPi (d : D) (c : D →𝒄 D) : unPi (Π̂ d c) = some (d, c) := by
  simp [unPi, mkPi, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj, lam.ret_inj]

@[simp]
theorem ScottDomain.unSigma_mkSigma (d : D) (c : D →𝒄 D) : unSigma (Σ̂ d c) = some (d, c) := by
  simp [unSigma, mkSigma, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj, lam.ret_inj]

@[simp]
theorem ScottDomain.unPair_mkPair (a b : D) : unPair (mkPair a b) = some (a, b) := by
  simp [unPair, mkPair, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]

@[simp]
theorem ScottDomain.unU_mkU (n : Nat) : unU (mkU (D := D) n) = some n := by
  simp [unU, mkU, flat.ret_inj]

@[simp]
theorem ScottDomain.unId_mkId (a x y : D) : unId (Îd a x y) = some (a, x, y) := by
  simp [unId, mkId, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]

@[simp]
theorem ScottDomain.unU_mkSigma (a : D) (f : D →𝒄 D) : unU (Σ̂ a f) = none := by
  simp [unU, mkSigma, ωScottContinuous.mk_lam]
@[simp]
theorem ScottDomain.unSigma_mkU (n : Nat) : unSigma (mkU (D := D) n) = none := by
  simp [unSigma, mkU]
@[simp]
theorem ScottDomain.unPi_mkSigma (a : D) (f : D →𝒄 D) : unPi (Σ̂ a f) = none := by
  simp [unPi, mkSigma, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]
@[simp]
theorem ScottDomain.unSigma_mkPi (a : D) (f : D →𝒄 D) : unSigma (Π̂ a f) = none := by
  simp [unSigma, mkPi, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]
@[simp]
theorem ScottDomain.unSigma_mkId (a x y : D) : unSigma (Îd a x y) = none := by
  simp [unSigma, mkId, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]
@[simp]
theorem ScottDomain.unId_mkSigma (a : D) (f : D →𝒄 D) : unId (Σ̂ a f) = none := by
  simp [unId, mkSigma, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]

@[simp]
theorem ScottDomain.unU_mkPi (a : D) (f : D →𝒄 D) : unU (Π̂ a f) = none := by
  simp [unU, mkPi, ωScottContinuous.mk_lam]
@[simp]
theorem ScottDomain.unPi_mkU (n : Nat) : unPi (mkU (D := D) n) = none := by
  simp [unPi, mkU]
@[simp]
theorem ScottDomain.unU_mkId (a x y : D) : unU (Îd a x y) = none := by
  simp [unU, mkId, ωScottContinuous.mk_lam]
@[simp]
theorem ScottDomain.unId_mkU (n : Nat) : unId (mkU (D := D) n) = none := by
  simp [unId, mkU]
@[simp]
theorem ScottDomain.unPi_mkId (a x y : D) : unPi (Îd a x y) = none := by
  simp [unPi, mkId, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]
@[simp]
theorem ScottDomain.unId_mkPi (a : D) (f : D →𝒄 D) : unId (Π̂ a f) = none := by
  simp [unId, mkPi, ωScottContinuous.mk_lam, pair.ret_inj, flat.ret_inj]

theorem ScottDomain.mkU_inj (h : mkU (D := D) ℓ = mkU ℓ') : ℓ = ℓ' := by
  simpa using congrArg unU h
theorem ScottDomain.mkPi_inj {f f' : D →𝒄 D} (h : Π̂ a f = Π̂ a' f') : a = a' ∧ f = f' := by
  simpa [Prod.ext_iff] using congrArg unPi h
theorem ScottDomain.mkId_inj {a x y a' x' y' : D} (h : Îd a x y = Îd a' x' y') :
    a = a' ∧ x = x' ∧ y = y' := by
  simpa [Prod.ext_iff] using congrArg unId h

theorem ScottDomain.mkSigma_inj {f f' : D →𝒄 D} (h : Σ̂ a f = Σ̂ a' f') : a = a' ∧ f = f' := by
  simpa [Prod.ext_iff] using congrArg unSigma h

theorem ScottDomain.mkPair_inj {a b a' b' : D} (h : mkPair a b = mkPair a' b') :
    a = a' ∧ b = b' := by simpa [Prod.ext_iff] using congrArg unPair h

theorem ScottDomain.boolCase_cont_f_hom (t : D) :
    ωScottContinuous (fun f : D => boolCase t f) :=
  ωScottContinuous.of_apply₃ (fun b => boolCase_cont_f t b)
theorem ScottDomain.boolCase_cont_t_hom (f : D) :
    ωScottContinuous (fun t : D => boolCase t f) :=
  ωScottContinuous.of_apply₃ (fun b => boolCase_cont_t f b)

/-- The boolean recursor as a fully continuous (curried) map. -/
def ScottDomain.boolCaseHom : D →𝒄 D →𝒄 D →𝒄 D :=
  ƛ[ ωScottContinuous.mk_lam_cont boolCase_cont_t_hom ] t ↦
    ƛ[ boolCase_cont_f_hom t ] f ↦ boolCase t f

@[simp]
theorem ScottDomain.boolCaseHom_apply (t f : D) : boolCaseHom t f = boolCase t f := rfl
