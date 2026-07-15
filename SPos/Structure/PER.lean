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
  sym := by constructor; simp
  tra := by constructor; simp

def PER.diag (D : Type u) : PER D where
  rel a b := a = b
  sym := by constructor; simp
  tra := by constructor; simp

structure PERResp (R : PER D) (E : (x : D) → PER (M x)) where
  toFun : (x : D) → M x
  respCarrier  : ∀ a b, (a ~ b ∈ₚ R) → M a = M b
  respRelation : ∀ a b, (h : a ~ b ∈ₚ R)
    → (toFun a) ~ (respCarrier _ _ h ▸ toFun b) ∈ₚ E a

abbrev PERRespND (R : PER D) (E : PER S) := PERResp R (fun _ => E)

def PERRespND.mk (toFun : D → S) (resp : ∀ a b, (a ~ b ∈ₚ R) → (toFun a) ~ (toFun b) ∈ₚ E) :
  PERRespND R E where
  toFun := toFun
  respCarrier := by intros; simp
  respRelation := resp

instance {R : PER D} {E : (d : D) → PER (M d)}
  : DFunLike (PERResp R E) D (fun d => M d) where
  coe := fun x => x.toFun
  coe_injective f g h := by cases f; cases g; congr

instance {R : PER D} {E : (d : D) → PER (M d)}
  : CoeFun (PERResp R E) fun _ => (x : D) → M x where
  coe f := f.toFun

infixr:25 " →ₚ " => PERRespND

@[simp]
theorem PERRespND.mk_apply (f : D → S)
    (resp : ∀ a b, (a ~ b ∈ₚ R) → (f a) ~ (f b) ∈ₚ E) (a : D) :
    (PERRespND.mk R E f resp) a = f a := rfl

@[ext]
theorem PER.ext {R S : PER D} (h : R.rel = S.rel) : R = S := by
  cases R; cases S; cases h; simp

@[simp]
theorem PERResp.eq_of_rel {A : PER D} (B : A →ₚ PER.diag S)
    {a b : D} (h : a ~ b ∈ₚ A) : B a = B b :=
  B.respRelation a b h
