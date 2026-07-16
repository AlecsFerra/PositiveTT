import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Tactic.DeriveFintype
import SPos.Syntax.Syntax

inductive Polarity where
| both | positive | negative | none
deriving DecidableEq, Repr, Fintype

def Polarity.le : Polarity → Polarity → Prop
| .none,     _         => True
| _,         .both     => True
| .positive, .positive => True
| .negative, .negative => True
| _,         _         => False

instance : DecidableRel Polarity.le := fun a b => by
  cases a <;> cases b
  all_goals simp [Polarity.le]; infer_instance

def Polarity.lub : Polarity → Polarity → Polarity
| .both, _ | _, .both => .both
| .none, x | x, .none => x
| .positive, .positive => .positive
| .negative, .negative => .negative
| .positive, .negative
| .negative, .positive => .both

instance : Max Polarity := ⟨Polarity.lub⟩

def Polarity.glb : Polarity → Polarity → Polarity
| .none, _ | _, .none => .none
| .both, x | x, .both => x
| .positive, .positive => .positive
| .negative, .negative => .negative
| .positive, .negative
| .negative, .positive => .none

instance : Min Polarity := ⟨Polarity.glb⟩

def Polarity.flip : Polarity → Polarity
| .both     => .both
| .positive => .negative
| .negative => .positive
| .none     => .none

instance : Neg Polarity := ⟨Polarity.flip⟩

instance : LE Polarity := ⟨Polarity.le⟩
instance : Top Polarity := ⟨.both⟩
instance : Bot Polarity := ⟨.none⟩

instance : DecidableRel ((· ≤ ·) : Polarity → Polarity → Prop) :=
  fun a b => inferInstanceAs (Decidable (Polarity.le a b))

-- `none < positive, negative < both`: the diamond lattice of occurrence
-- information. All laws are decidable over the finite carrier.
instance : Lattice Polarity where
  le := (· ≤ ·)
  sup := (· ⊔ ·)
  inf := (· ⊓ ·)
  le_refl := by decide
  le_trans := by decide
  le_antisymm := by decide
  le_sup_left := by decide
  le_sup_right := by decide
  sup_le := by decide
  inf_le_left := by decide
  inf_le_right := by decide
  le_inf := by decide

instance : BoundedOrder Polarity where
  top := ⊤
  bot := ⊥
  le_top := by decide
  bot_le := by decide

@[simp] theorem Polarity.top_sup (p : Polarity) : (⊤ : Polarity) ⊔ p = ⊤ := by cases p <;> rfl
@[simp] theorem Polarity.sup_top (p : Polarity) : p ⊔ (⊤ : Polarity) = ⊤ := by cases p <;> rfl
@[simp] theorem Polarity.bot_sup (p : Polarity) : (⊥ : Polarity) ⊔ p = p := by cases p <;> rfl
@[simp] theorem Polarity.sup_bot (p : Polarity) : p ⊔ (⊥ : Polarity) = p := by cases p <;> rfl

@[simp] theorem Polarity.flip_flip (p : Polarity) : - - p = p := by cases p <;> rfl
@[simp] theorem Polarity.flip_bot : -(⊥ : Polarity) = ⊥ := rfl
@[simp] theorem Polarity.flip_top : -(⊤ : Polarity) = ⊤ := rfl

-- Flip swaps `positive`/`negative` and fixes `none`/`both`: an order automorphism.
theorem Polarity.flip_mono {p q : Polarity} (h : p ≤ q) : -p ≤ -q :=
  (by decide : ∀ p q : Polarity, p ≤ q → -p ≤ -q) p q h

@[simp] theorem Polarity.flip_sup (p q : Polarity) : -(p ⊔ q) = -p ⊔ -q := by
  cases p <;> cases q <;> rfl

-- `p.inv`: the polarity of an occurrence whose surrounding position is
-- "term-level" — any actual occurrence is poisoned to `both`, absence stays `none`.
def Polarity.inv (p : Polarity) : Polarity := p ⊔ -p

@[simp] theorem Polarity.inv_bot : (⊥ : Polarity).inv = ⊥ := rfl
@[simp] theorem Polarity.inv_flip (p : Polarity) : (-p).inv = p.inv := by cases p <;> rfl

theorem Polarity.inv_mono {p q : Polarity} (h : p ≤ q) : p.inv ≤ q.inv :=
  (by decide : ∀ p q : Polarity, p ≤ q → p.inv ≤ q.inv) p q h

theorem Polarity.le_inv (p : Polarity) : p ≤ p.inv := by cases p <;> decide

theorem Polarity.inv_eq_bot {p : Polarity} (h : p.inv ≤ .positive) : p = ⊥ :=
  (by decide : ∀ p : Polarity, p.inv ≤ .positive → p = ⊥) p h

theorem Polarity.le_positive_iff {p : Polarity} :
    p ≤ .positive ↔ p = ⊥ ∨ p = .positive :=
  (by decide : ∀ p : Polarity, p ≤ .positive ↔ p = ⊥ ∨ p = .positive) p

theorem Polarity.flip_le_positive {p : Polarity} (h : p ≤ .negative) : -p ≤ .positive :=
  (by decide : ∀ p : Polarity, p ≤ .negative → -p ≤ .positive) p h

-- The polarity of the occurrences of variable `x` in `t`.
--
-- Type formers propagate polarity: `Π` flips its domain, `Σ`/`Π` codomains and
-- `Id`'s carrier are positive positions. Everything term-level (`lam`, `app`,
-- `pair`, projections, `boolrec`, `refl`, `J`, `Id`'s endpoints) poisons
-- occurrences via `.inv`: an occurrence there carries no (anti)monotonicity
-- information, so it becomes `both`.
def Tm.polarity : Tm n → Fin n → Polarity
| .var i, x => if i = x then .positive else ⊥
| .pi τ υ, x => -(τ.polarity x) ⊔ υ.polarity x.succ
| .lam τ t, x => (τ.polarity x).inv ⊔ (t.polarity x.succ).inv
| .app t s, x => (t.polarity x).inv ⊔ (s.polarity x).inv
| .sigma τ υ, x => τ.polarity x ⊔ υ.polarity x.succ
| .pair a b, x => (a.polarity x).inv ⊔ (b.polarity x).inv
| .fst p, x => (p.polarity x).inv
| .snd p, x => (p.polarity x).inv
| .bool, _ => ⊥
| .true, _ => ⊥
| .false, _ => ⊥
| .boolrec P t f b, x =>
    (P.polarity x.succ).inv ⊔ (t.polarity x).inv ⊔ (f.polarity x).inv ⊔ (b.polarity x).inv
| .id τ a b, x => τ.polarity x ⊔ (a.polarity x).inv ⊔ (b.polarity x).inv
| .refl τ a, x => (τ.polarity x).inv ⊔ (a.polarity x).inv
| .j C d p, x => (C.polarity x.succ.succ).inv ⊔ (d.polarity x).inv ⊔ (p.polarity x).inv
-- `mu` is a type former: the least fixed point is monotone in its parameters,
-- so occurrences under the binder keep their polarity. `roll` is term-level.
| .mu B, x => B.polarity x.succ
| .roll t, x => (t.polarity x).inv
| .u _, _ => ⊥

-- A body is a legal inductive definition when its self-variable occurs only
-- positively.
abbrev Tm.Positive (B : Tm (n + 1)) : Prop := B.polarity 0 ≤ .positive

/-! ### Polarity under renaming and substitution

The side condition `Tm.Positive` must survive the renamings and substitutions
performed by Weakening/Substitution. The occurrences of the tracked variable are
in bijection with those of its preimage, so the polarity is preserved exactly.
-/

-- Lifting preserves "the unique preimage of `x'` is `x`".
theorem Ren.liftPres {r : Ren n m} {x : Fin n} {x' : Fin m}
    (h : ∀ i, r i = x' ↔ i = x) : ∀ i, Ren.lift r i = x'.succ ↔ i = x.succ := by
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Ren.lift, Fin.cases_zero]
    exact iff_of_false (fun hh => Fin.succ_ne_zero _ hh.symm)
      (fun hh => Fin.succ_ne_zero _ hh.symm)
  | succ j =>
    simp only [Ren.lift, Fin.cases_succ, Fin.succ_inj]
    exact h j

-- Lifting preserves "`x'` is not in the range".
theorem Ren.liftNotin {r : Ren n m} {x' : Fin m}
    (h : ∀ i, r i ≠ x') : ∀ i, Ren.lift r i ≠ x'.succ := by
  intro i
  induction i using Fin.cases with
  | zero =>
    simp only [Ren.lift, Fin.cases_zero]
    exact fun hh => Fin.succ_ne_zero _ hh.symm
  | succ j =>
    simp only [Ren.lift, Fin.cases_succ]
    exact fun hh => h j (Fin.succ_inj.mp hh)

-- Renaming along `r` where `x'` has the unique preimage `x`.
theorem Tm.polarity_rename : ∀ (t : Tm n) {m : Nat} {r : Ren n m} {x : Fin n} {x' : Fin m},
    (∀ i, r i = x' ↔ i = x) → (t.rename r).polarity x' = t.polarity x
| .var i, _, r, x, x', h => by
    simp only [Tm.rename, Tm.polarity]
    by_cases hi : i = x
    · rw [if_pos ((h i).mpr hi), if_pos hi]
    · rw [if_neg (fun hh => hi ((h i).mp hh)), if_neg hi]
| .pi τ υ, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename h, υ.polarity_rename (Ren.liftPres h)]
| .lam τ t, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename h, t.polarity_rename (Ren.liftPres h)]
| .app t s, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, t.polarity_rename h, s.polarity_rename h]
| .sigma τ υ, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename h, υ.polarity_rename (Ren.liftPres h)]
| .pair a b, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, a.polarity_rename h, b.polarity_rename h]
| .fst p, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, p.polarity_rename h]
| .snd p, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, p.polarity_rename h]
| .bool, _, _, _, _, _ => rfl
| .true, _, _, _, _, _ => rfl
| .false, _, _, _, _, _ => rfl
| .boolrec P t f b, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, P.polarity_rename (Ren.liftPres h),
      t.polarity_rename h, f.polarity_rename h, b.polarity_rename h]
| .id τ a b, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename h,
      a.polarity_rename h, b.polarity_rename h]
| .refl τ a, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename h, a.polarity_rename h]
| .j C d p, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, C.polarity_rename (Ren.liftPres (Ren.liftPres h)),
      d.polarity_rename h, p.polarity_rename h]
| .mu B, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, B.polarity_rename (Ren.liftPres h)]
| .roll t, _, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, t.polarity_rename h]
| .u _, _, _, _, _, _ => rfl

-- Renaming along `r` that never hits `x'`: no occurrences at all.
theorem Tm.polarity_rename_notin : ∀ (t : Tm n) {m : Nat} {r : Ren n m} {x' : Fin m},
    (∀ i, r i ≠ x') → (t.rename r).polarity x' = ⊥
| .var i, _, r, x', h => by
    simp only [Tm.rename, Tm.polarity, if_neg (h i)]
| .pi τ υ, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename_notin h,
      υ.polarity_rename_notin (Ren.liftNotin h), Polarity.flip_bot, Polarity.sup_bot]
| .lam τ t, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename_notin h,
      t.polarity_rename_notin (Ren.liftNotin h), Polarity.inv_bot, Polarity.sup_bot]
| .app t s, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, t.polarity_rename_notin h,
      s.polarity_rename_notin h, Polarity.inv_bot, Polarity.sup_bot]
| .sigma τ υ, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename_notin h,
      υ.polarity_rename_notin (Ren.liftNotin h), Polarity.sup_bot]
| .pair a b, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, a.polarity_rename_notin h,
      b.polarity_rename_notin h, Polarity.inv_bot, Polarity.sup_bot]
| .fst p, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, p.polarity_rename_notin h, Polarity.inv_bot]
| .snd p, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, p.polarity_rename_notin h, Polarity.inv_bot]
| .bool, _, _, _, _ => rfl
| .true, _, _, _, _ => rfl
| .false, _, _, _, _ => rfl
| .boolrec P t f b, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, P.polarity_rename_notin (Ren.liftNotin h),
      t.polarity_rename_notin h, f.polarity_rename_notin h, b.polarity_rename_notin h,
      Polarity.inv_bot, Polarity.sup_bot]
| .id τ a b, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename_notin h,
      a.polarity_rename_notin h, b.polarity_rename_notin h,
      Polarity.inv_bot, Polarity.sup_bot]
| .refl τ a, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, τ.polarity_rename_notin h,
      a.polarity_rename_notin h, Polarity.inv_bot, Polarity.sup_bot]
| .j C d p, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity,
      C.polarity_rename_notin (Ren.liftNotin (Ren.liftNotin h)),
      d.polarity_rename_notin h, p.polarity_rename_notin h,
      Polarity.inv_bot, Polarity.sup_bot]
| .mu B, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, B.polarity_rename_notin (Ren.liftNotin h)]
| .roll t, _, _, _, h => by
    simp only [Tm.rename, Tm.polarity, t.polarity_rename_notin h, Polarity.inv_bot]
| .u _, _, _, _, _ => rfl

@[simp]
theorem Tm.polarity_weaken (t : Tm n) (x : Fin n) :
    (↑ t : Tm (n + 1)).polarity x.succ = t.polarity x :=
  t.polarity_rename (fun _ => Fin.succ_inj)

@[simp]
theorem Tm.polarity_weaken_zero (t : Tm n) : (↑ t : Tm (n + 1)).polarity 0 = ⊥ :=
  t.polarity_rename_notin (fun i => Fin.succ_ne_zero i)

-- Lifting a substitution preserves "`x` is sent to the variable `x'`" …
theorem Subst.liftPresVar {σ : Subst n m} {x : Fin n} {x' : Fin m}
    (hx : σ x = .var x') : Subst.lift σ x.succ = .var x'.succ := by
  simp only [Subst.lift, Fin.cases_succ, hx, Tm.weaken, Tm.rename]

-- … and "every other variable avoids `x'`".
theorem Subst.liftNotin {σ : Subst n m} {x : Fin n} {x' : Fin m}
    (h : ∀ i, i ≠ x → (σ i).polarity x' = ⊥) :
    ∀ i, i ≠ x.succ → ((Subst.lift σ) i).polarity x'.succ = ⊥ := by
  intro i hi
  induction i using Fin.cases with
  | zero =>
    simp only [Subst.lift, Fin.cases_zero, Tm.polarity]
    rw [if_neg (fun hh : (0 : Fin _) = x'.succ => Fin.succ_ne_zero _ hh.symm)]
  | succ j =>
    simp only [Subst.lift, Fin.cases_succ, Tm.polarity_weaken]
    exact h j (fun hj => hi (by rw [hj]))

-- Substitution along `σ` sending `x` to the variable `x'` and everything else to
-- terms avoiding `x'`: the occurrences of `x'` after are exactly those of `x` before.
theorem Tm.polarity_subst : ∀ (t : Tm n) {m : Nat} {σ : Subst n m} {x : Fin n} {x' : Fin m},
    σ x = .var x' → (∀ i, i ≠ x → (σ i).polarity x' = ⊥) →
    (t.subst σ).polarity x' = t.polarity x
| .var i, _, σ, x, x', hx, h => by
    simp only [Tm.subst]
    by_cases hi : i = x
    · subst hi
      rw [hx]
      simp only [Tm.polarity]
    · rw [h i hi]
      simp only [Tm.polarity, if_neg hi]
| .pi τ υ, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, τ.polarity_subst hx h,
      υ.polarity_subst (Subst.liftPresVar hx) (Subst.liftNotin h)]
| .lam τ t, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, τ.polarity_subst hx h,
      t.polarity_subst (Subst.liftPresVar hx) (Subst.liftNotin h)]
| .app t s, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, t.polarity_subst hx h, s.polarity_subst hx h]
| .sigma τ υ, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, τ.polarity_subst hx h,
      υ.polarity_subst (Subst.liftPresVar hx) (Subst.liftNotin h)]
| .pair a b, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, a.polarity_subst hx h, b.polarity_subst hx h]
| .fst p, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, p.polarity_subst hx h]
| .snd p, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, p.polarity_subst hx h]
| .bool, _, _, _, _, _, _ => rfl
| .true, _, _, _, _, _, _ => rfl
| .false, _, _, _, _, _, _ => rfl
| .boolrec P t f b, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity,
      P.polarity_subst (Subst.liftPresVar hx) (Subst.liftNotin h),
      t.polarity_subst hx h, f.polarity_subst hx h, b.polarity_subst hx h]
| .id τ a b, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, τ.polarity_subst hx h,
      a.polarity_subst hx h, b.polarity_subst hx h]
| .refl τ a, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, τ.polarity_subst hx h, a.polarity_subst hx h]
| .j C d p, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity,
      C.polarity_subst (Subst.liftPresVar (Subst.liftPresVar hx))
        (Subst.liftNotin (Subst.liftNotin h)),
      d.polarity_subst hx h, p.polarity_subst hx h]
| .mu B, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity,
      B.polarity_subst (Subst.liftPresVar hx) (Subst.liftNotin h)]
| .roll t, _, _, _, _, hx, h => by
    simp only [Tm.subst, Tm.polarity, t.polarity_subst hx h]
| .u _, _, _, _, _, _, _ => rfl

-- The two instances used by Weakening/Substitution: positivity of a `mu` body
-- survives lifted renamings and lifted substitutions.
@[simp]
theorem Tm.polarity_rename_lift (B : Tm (n + 1)) (r : Ren n m) :
    (B.rename (Ren.lift r)).polarity 0 = B.polarity 0 :=
  B.polarity_rename (fun i => by
    induction i using Fin.cases with
    | zero => simp [Ren.lift]
    | succ j =>
      simp only [Ren.lift, Fin.cases_succ]
      exact iff_of_false (Fin.succ_ne_zero _) (Fin.succ_ne_zero _))

@[simp]
theorem Tm.polarity_subst_lift (B : Tm (n + 1)) (σ : Subst n m) :
    (B.subst (Subst.lift σ)).polarity 0 = B.polarity 0 :=
  B.polarity_subst (by simp [Subst.lift]) (fun i hi => by
    induction i using Fin.cases with
    | zero => exact absurd rfl hi
    | succ j => simp [Subst.lift, Tm.polarity_weaken_zero])
