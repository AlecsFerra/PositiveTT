import Mathlib.Logic.Relation
import Mathlib.Data.Rel

structure PER (D : Type u) where
  rel : Rel D D
  sym : Std.Symm rel
  tra : IsTrans D rel

variable
  {D : Type u} (R : PER D)
  {S : Type v} (E : PER S)
  {M : D → Type w}

-- notation a "∈ₚ" R => PER.R R a a
notation a "~" b "∈ₚ" R => PER.rel R a b

@[simp]
theorem PER.symm (h : a ~ b ∈ₚ R) : b ~ a ∈ₚ R :=
  R.sym.symm _ _ h

@[simp]
theorem PER.trans (h₁ : a ~ b ∈ₚ R) (h₂ : b ~ c ∈ₚ R) : a ~ c ∈ₚ R :=
  R.tra.trans _ _ _ h₁ h₂

@[simp]
theorem PER.refl_left (h : a ~ b ∈ₚ R) : a ~ a ∈ₚ R :=
  R.trans h (R.symm h)

@[simp]
theorem PER.refl_right (h : a ~ b ∈ₚ R) : b ~ b ∈ₚ R :=
  R.trans (R.symm h) h

def PER.empty (D : Type u) : PER D where
  rel _ _ := False
  sym := ⟨ fun _ _   f   => f ⟩
  tra := ⟨ fun _ _ _ f _ => f ⟩

def PER.diag (D : Type u) : PER D where
  rel a b := a = b
  sym := ⟨ fun _ _   f   => f.symm ⟩
  tra := ⟨ fun _ _ _ f g => f.trans g ⟩

structure PERResp (R : PER D) (E : (x : D) → PER (M x)) where
  toFun : (x : D) → M x
  respCarrier  : ∀ a b, (a ~ b ∈ₚ R) → M a = M b
  respRelation : ∀ a b, (h : a ~ b ∈ₚ R)
    → (toFun a) ~ (respCarrier _ _ h ▸ toFun b) ∈ₚ E a

abbrev PERRespND (R : PER D) (E : PER S) := PERResp R (fun _ => E)

def PERRespND.mk (toFun : D → S) (resp : ∀ a b, (a ~ b ∈ₚ R) → (toFun a) ~ (toFun b) ∈ₚ E) :
  PERRespND R E where
  toFun := toFun
  respCarrier := fun _ _ _ => rfl
  respRelation := resp

instance {R : PER D} {E : (d : D) → PER (M d)}
  : DFunLike (PERResp R E) D (fun d => M d) where
  coe := fun x => x.toFun
  coe_injective f g h := by cases f; cases g; congr

instance {R : PER D} {E : (d : D) → PER (M d)}
  : CoeFun (PERResp R E) fun _ => (x : D) → M x where
  coe f := f.toFun

infixr:25 " →ₚ " => PERRespND

/-- A partial equivalence relation: symmetric and transitive, but not necessarily
reflexive. Its domain is `{a | R a a}`; on the domain it is an equivalence. -/
structure IsPER {D : Type u} (R : D → D → Prop) : Prop where
  symm  : ∀ {a b : D}, R a b → R b a
  trans : ∀ {a b c : D}, R a b → R b c → R a c

namespace IsPER

variable {D : Type u} {R : D → D → Prop}

/-- Anything related is in the domain (self-related), on the left. -/
theorem refl_left (h : IsPER R) {a b : D} (hab : R a b) : R a a :=
  h.trans hab (h.symm hab)

/-- Anything related is in the domain (self-related), on the right. -/
theorem refl_right (h : IsPER R) {a b : D} (hab : R a b) : R b b :=
  h.trans (h.symm hab) hab

end IsPER
