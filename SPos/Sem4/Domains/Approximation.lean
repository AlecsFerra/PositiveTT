import Mathlib.Order.CompletePartialOrder
import Mathlib.Data.Vector.Basic
import Mathlib.Logic.Lemmas

import SPos.Sem4.Domains.ScottContinuous

inductive ApproxZero : Type υ | bot

instance : CompletePartialOrder ApproxZero where
  le x y      := True
  le_refl     := by intros; trivial
  le_trans    := by intros; trivial
  le_antisymm := by intros; trivial
  bot         := .bot
  bot_le      := by intros; trivial
  sSup s      := .bot
  lubOfDirected := by
    intro c p; constructor
    all_goals intro x y; cases x; simp

inductive Tag : Type where
| univ (ℓ : Nat) | pi    | lam  | sigma
| pair           | bool  | true | false
| id             | refl  | mu   | roll
deriving Repr, DecidableEq

-- First the number of raw self references, then the number continuous functions
@[simp]
def Tag.arity : Tag → Nat × Nat
| univ _ => (0, 0) | pi   => (1, 1) | lam  => (0, 1) | sigma => (1, 1)
| pair   => (2, 0) | bool => (0, 0) | true => (0, 0) | false => (0, 0)
| id     => (3, 0) | refl => (0, 0) | mu   => (0, 1) | roll  => (1, 0)

inductive Approx (ρ : Type υ) [ρo : Preorder ρ] where
| bot : Approx ρ
| op (t : Tag) (_ : List.Vector ρ t.arity.1) (_ : List.Vector (ρ →ₛ ρ) t.arity.2) : Approx ρ

instance [Preorder ρ] : LE (Approx ρ) where
  le x y := match x, y with
  | .bot, _                    => True
  | .op t₁ v₁ w₁, .op t₂ v₂ w₂ => ∃ h : t₁ = t₂,
      (∀ i,   v₁.get i   ≤ v₂.get (h ▸ i))
    ∧ (∀ j x, w₁.get j x ≤ w₂.get (h ▸ j) x)
  | _, _ => False

@[simp]
theorem Approx.bot_le [Preorder ρ] (x : Approx ρ) : .bot ≤ x := by
  cases x <;> simp [LE.le]

instance [Preorder ρ] : OrderBot (Approx ρ) where
  bot := .bot
  bot_le := by simp

instance [Preorder ρ] : Preorder (Approx ρ) where
  le_refl := by
    intro x; cases x <;> simp_all [LE.le]
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z
    all_goals simp_all [LE.le]
    obtain ⟨exy, axy, fxy⟩ := hxy
    obtain ⟨eyz, ayz, fyz⟩ := hyz
    refine ⟨Eq.trans exy eyz, ?_, ?_⟩
    · intro i;   refine le_trans (axy i)   ?_
      subst exy eyz; simp_all
    · intro i x; refine le_trans (fxy i x) ?_
      subst exy eyz; simp_all

instance [PartialOrder ρ] : PartialOrder (Approx ρ) where
  le_antisymm := by
    intro x y hxy hyx
    cases x <;> cases y
    all_goals simp_all [LE.le]
    obtain ⟨exy, axy, fxy⟩ := hxy
    obtain ⟨eyx, ayx, fyx⟩ := hyx
    refine ⟨exy, ?_, ?_⟩
    all_goals cases exy; cases eyx; apply Eq.heq; ext i
    · exact le_antisymm (axy i) (ayx i)
    · exact le_antisymm (fxy i _) (fyx i _)

noncomputable section
open Classical

theorem Approx.op_le_op [Preorder ρ] (ht : t₁ = t₂) {w₁ w₂}
  (hv : ∀ i,   v₁.get i   ≤ v₂.get (ht ▸ i))
  (hw : ∀ j x, w₁.get j x ≤ w₂.get (ht ▸ j) x) :
  (.op t₁ v₁ w₁ : Approx ρ) ≤ .op t₂ v₂ w₂ := by
    cases ht; exact ⟨rfl, hv, hw⟩

theorem Approx.isLUB_op [CompletePartialOrder ρ]
    {V : α → _} {W : α → List.Vector (ρ →ₛ ρ) t.arity.2}
    {v} {w} (hne : s.Nonempty)
    (hv : ∀ i,   IsLUB ((fun a => (V a).get i)   '' s) (v.get i  ))
    (hw : ∀ j y, IsLUB ((fun a => (W a).get j y) '' s) (w.get j y)) :
    IsLUB ((fun a => Approx.op t (V a) (W a)) '' s) (Approx.op t v w) := by
  constructor
  · rintro _ ⟨a, ha, rfl⟩
    apply Approx.op_le_op rfl
    · intro i
      exact (hv i).1 ⟨a, ha, rfl⟩
    · intro j y
      exact (hw j y).1 ⟨a, ha, rfl⟩
  · obtain ⟨a₀, ha₀⟩ := hne
    intro u hu; cases u
    case bot => exact (hu ⟨a₀, ha₀, rfl⟩).elim
    case op t' v' w' =>
      obtain ⟨rfl, _, _⟩ := hu ⟨a₀, ha₀, rfl⟩
      apply Approx.op_le_op rfl
      · intro i;   apply (hv i).2;   rintro _ ⟨a, ha, rfl⟩
        exact (hu ⟨a, ha, rfl⟩).2.1 i
      · intro j y; apply (hw j y).2; rintro _ ⟨a, ha, rfl⟩
        exact (hu ⟨a, ha, rfl⟩).2.2 j y

theorem Approx.tag_eq_of_mem_directed [Preorder ρ] {s : Set (Approx ρ)}
    (hd : DirectedOn (· ≤ ·) s) {w₁ w₂}
    (h₁ : Approx.op t₁ v₁ w₁ ∈ s) (h₂ : Approx.op t₂ v₂ w₂ ∈ s) : t₁ = t₂ := by
  obtain ⟨z, _, le₁, le₂⟩ := hd _ h₁ _ h₂; cases z
  case bot => exact le₁.elim
  exact le₁.1.trans le₂.1.symm

theorem Approx.directedOn_proj_v [Preorder ρ] {s : Set (Approx ρ)}
    (hd : DirectedOn (· ≤ ·) s) (t : Tag) (i : Fin t.arity.1) :
    DirectedOn (· ≤ ·) {x : ρ | ∃ v w, Approx.op t v w ∈ s ∧ x = v.get i} := by
  rintro _ ⟨v₁, w₁, hm₁, rfl⟩ _ ⟨v₂, w₂, hm₂, rfl⟩
  obtain ⟨z, hz, le₁, le₂⟩ := hd _ hm₁ _ hm₂; cases z
  case op t₃ v₃ w₃ =>
    obtain ⟨rfl, hv₁, hw₁⟩ := le₁
    obtain ⟨_,   hv₂, hw₂⟩ := le₂
    refine ⟨v₃.get i, ⟨_, _, hz, rfl⟩, ?_, ?_⟩
    · simp; apply hv₁
    · simp; apply hv₂
  exact le₁.elim

theorem Approx.directedOn_proj_w [Preorder ρ] {s : Set (Approx ρ)}
    (hd : DirectedOn (· ≤ ·) s) (t : Tag) (j : Fin t.arity.2) (x : ρ) :
    DirectedOn (· ≤ ·) {y : ρ | ∃ v w, Approx.op t v w ∈ s ∧ y = (w.get j) x} := by
  rintro _ ⟨v₁, w₁, hm₁, rfl⟩ _ ⟨v₂, w₂, hm₂, rfl⟩
  obtain ⟨z, hz, le₁, le₂⟩ := hd _ hm₁ _ hm₂; cases z
  case op t₃ v₃ w₃ =>
    obtain ⟨rfl, hv₁, hw₁⟩ := le₁
    obtain ⟨_,   hv₂, hw₂⟩ := le₂
    refine ⟨(w₃.get j) x, ⟨_, _, hz, rfl⟩, ?_, ?_⟩
    · simp; apply hw₁
    · simp; apply hw₂
  exact le₁.elim

theorem Approx.scottContinuous_sSup_w [CompletePartialOrder ρ] {s : Set (Approx ρ)}
    (hd : DirectedOn (· ≤ ·) s) (j : Fin t.arity.2) :
    ScottContinuous (fun x => sSup {y : ρ | ∃ v w, Approx.op t v w ∈ s ∧ y = w.get j x}) := by
  intro d hne hdir a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    refine (directedOn_proj_w hd t j x).sSup_le ?_
    rintro _ ⟨v, w, hm, rfl⟩
    exact le_trans ((w.get j).scott_continuous.monotone (ha.1 hx))
                   ((directedOn_proj_w hd t j a).le_sSup ⟨v, w, hm, rfl⟩)
  · intro u hu
    refine (directedOn_proj_w hd t j a).sSup_le ?_
    rintro _ ⟨v, w, hm, rfl⟩
    have hc := (w.get j).scott_continuous hne hdir ha
    refine hc.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_trans ((directedOn_proj_w hd t j x).le_sSup ⟨v, w, hm, rfl⟩)
                   (hu (Set.mem_image_of_mem _ hx))

instance [CompletePartialOrder ρ] : CompletePartialOrder (Approx ρ) where
  sSup s := if hs : DirectedOn (· ≤ ·) s ∧ ∃ t v w, Approx.op t v w ∈ s then by
    let t := hs.2.choose
    refine .op t
      (.ofFn λ i ↦             sSup {x | ∃ v w, .op t v w ∈ s ∧ x = v.get i})
      (.ofFn λ j ↦ ƛₛ[?_] x ↦ sSup {y | ∃ v w, .op t v w ∈ s ∧ y = w.get j x})
    exact Approx.scottContinuous_sSup_w hs.1 j
  else
    ⊥

  lubOfDirected s hs := by
    split_ifs with h
    case neg =>
      constructor
      all_goals intro x hx; cases x <;> simp_all [LE.le]
    case pos =>
      let    t            := h.2.choose
      obtain ⟨v, w, hmem⟩ := h.2.choose_spec
      constructor
      · intro e he; cases e
        case op t' v' w'=>
          obtain rfl := Approx.tag_eq_of_mem_directed hs he hmem
          apply Approx.op_le_op rfl
          all_goals simp [List.Vector.get_ofFn, -exists_and_right]
          · intro i
            apply (Approx.directedOn_proj_v h.1 t i  ).le_sSup ⟨v', w', he, rfl⟩
          · intro i x
            apply (Approx.directedOn_proj_w h.1 t i x).le_sSup ⟨v', w', he, rfl⟩
        case bot => simp
      · intro u hu; cases u
        case op =>
          obtain ⟨rfl, vu, wu⟩ := hu hmem
          apply Approx.op_le_op
          all_goals simp [List.Vector.get_ofFn, -exists_and_right]
          · intro i
            refine (Approx.directedOn_proj_v hs t i).sSup_le ?_
            rintro _ ⟨v, w, hm, rfl⟩
            obtain ⟨eq, hv, hw⟩ := hu hm; exact hv i
          · intro j x
            refine (Approx.directedOn_proj_w hs t j x).sSup_le ?_
            rintro _ ⟨v, w, hm, rfl⟩
            obtain ⟨eq, hv, hw⟩ := hu hm; exact hw j x
        case bot => apply (hu hmem).elim

theorem Approx.exists_op_of_isLUB [Preorder ρ] {d} {w : List.Vector (ρ →ₛ ρ) _}
    (ha : IsLUB d (Approx.op t v w)) : ∃ v' w', Approx.op t v' w' ∈ d := by
  by_contra hno
  refine ha.2 (?_ : ⊥ ∈ upperBounds d)
  intro e he; cases e
  case op =>
    obtain ⟨rfl, _, _⟩ := ha.1 he
    exact absurd ⟨_, _, he⟩ hno
  all_goals simp

theorem Approx.isLUB_proj_v [Preorder ρ] {d} {w}
  (ha : IsLUB d (Approx.op t v w)) (i : Fin t.arity.1) :
  IsLUB {x : ρ | ∃ v' w', Approx.op t v' w' ∈ d ∧ x = v'.get i} (v.get i) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨v', w', hm, rfl⟩
    obtain ⟨eq, hv, hw⟩ := ha.1 hm
    exact hv i
  · intro b hb
    have hub : Approx.op t (v.set i b) w ∈ upperBounds d := by
      intro e he; cases e
      case bot => simp
      case op =>
        obtain ⟨rfl, hv', hw'⟩ := ha.1 he
        apply Approx.op_le_op rfl ?_ hw'
        intro k; simp [List.Vector.get_set_eq_if]
        split_ifs with hik
        · subst hik; exact hb ⟨_, _, he, rfl⟩
        · exact hv' k
    obtain ⟨eq, hv, hw⟩ := ha.2 hub
    simpa [List.Vector.get_set_same] using hv i

theorem Approx.isLUB_proj_w [CompletePartialOrder ρ] {d}
    (hd : DirectedOn (· ≤ ·) d) {v} {w}
    (ha : IsLUB d (Approx.op t v w)) (j : Fin t.arity.2) (y : ρ) :
    IsLUB {z : ρ | ∃ v' w', Approx.op t v' w' ∈ d ∧ z = w'.get j y} ((w.get j) y) := by
  constructor
  · rintro _ ⟨v', w', hm, rfl⟩
    obtain ⟨eq, hv, hw⟩ := ha.1 hm
    exact hw j y
  · intro b hb
    set s : ρ →ₛ ρ := ƛₛ[ Approx.scottContinuous_sSup_w hd j ] x ↦
      sSup {z | ∃ v' w', Approx.op t v' w' ∈ d ∧ z = (w'.get j) x} with hs
    have hub : Approx.op t v (w.set j s) ∈ upperBounds d := by
      intro e he; cases e
      case bot => simp
      case op t' v' w' =>
        obtain ⟨e, hv', hw'⟩ := ha.1 he; subst t'
        apply Approx.op_le_op rfl hv'
        intro k x; simp [List.Vector.get_set_eq_if]
        split_ifs with hjk
        · subst hjk
          exact (Approx.directedOn_proj_w hd t j x).le_sSup ⟨_, _, he, rfl⟩
        · exact hw' k x
    refine le_trans ?_ ((Approx.directedOn_proj_w hd t j y).sSup_le hb)
    have q := (ha.2 hub).2.2 j y
    rwa [List.Vector.get_set_same] at q

@[reducible]
def ApproxChain : Nat → Σ ρ : Type 0, CompletePartialOrder ρ
| 0     => ⟨ApproxZero, inferInstance⟩
| n + 1 => ⟨
    Approx (ApproxChain n).fst (ρo := (ApproxChain n).snd.toPreorder),
    inferInstance
  ⟩
instance : CompletePartialOrder (ApproxChain n).fst := (ApproxChain n).snd
@[reducible]
def D (n : Nat) := (ApproxChain n).fst
instance : CompletePartialOrder (D n) := (ApproxChain n).snd

@[match_pattern]
def D.univ (ℓ : Nat) : D (n + 1) :=
  .op (Tag.univ ℓ) .nil .nil

@[match_pattern]
def D.pi (τ : D n) (σ : D n →ₛ D n) : D (n + 1) :=
  .op Tag.pi ⟨[τ], by simp⟩ ⟨[σ], by simp⟩

@[match_pattern]
def D.lam (b : D n →ₛ D n) : D (n + 1) :=
  .op Tag.lam .nil ⟨[b], by simp⟩

@[match_pattern]
def D.sigma (τ : D n) (σ : D n →ₛ D n) : D (n + 1) :=
  .op Tag.sigma ⟨[τ], by simp⟩ ⟨[σ], by simp⟩

@[match_pattern]
def D.pair (v : D n) (w : D n) : D (n + 1) :=
  .op Tag.pair ⟨[v, w], by simp⟩ .nil

@[match_pattern]
def D.bool : D (n + 1) :=
  .op Tag.bool .nil .nil

@[match_pattern]
def D.true : D (n + 1) :=
  .op Tag.true .nil .nil

@[match_pattern]
def D.false : D (n + 1) :=
  .op Tag.false .nil .nil

@[match_pattern]
def D.id (τ t₁ t₂ : D n) : D (n + 1) :=
  .op Tag.id ⟨[τ, t₁, t₂], by simp⟩ .nil

@[match_pattern]
def D.refl : D (n + 1) :=
  .op Tag.refl .nil .nil

@[match_pattern]
def D.mu (τ : D n →ₛ D n) : D (n + 1) :=
  .op Tag.mu .nil ⟨[τ], by simp⟩

@[match_pattern]
def D.roll (t : D n) : D (n + 1) :=
  .op Tag.roll ⟨[t], by simp⟩ .nil
