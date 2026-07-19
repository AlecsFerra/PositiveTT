import Mathlib.Order.Notation
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.ScottContinuity
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Order

import SPos.Sem3.DomainConstruction.ScottContinuous

inductive DBot : Type υ where
| bot : DBot

instance : CompletePartialOrder DBot where
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

inductive DStep (φ : Type υ) (ρ : Type γ) [po : Preorder ρ]
| bot  : DStep φ ρ
| lam  : (ρ →ₛ ρ) → DStep φ ρ
| pair : ρ → ρ → DStep φ ρ
| flat : φ → DStep φ ρ

instance [Preorder ρ] : LE (DStep φ ρ) where
  le x y := match x, y with
  | .bot,      _           => True
  | .lam b,    .lam b'     => ∀ x, b x ≤ b' x
  | .pair a b, .pair a' b' => a ≤ a' ∧ b ≤ b'
  | .flat x,   .flat y     => x = y
  | _,         _           => False

instance [Preorder ρ] : Preorder (DStep φ ρ) where
  le_refl := by
    intro x; cases x <;> simp_all [LE.le]
  le_trans := by
    intro x y z hxy hyz
    cases x <;> cases y <;> cases z
    all_goals try assumption
    all_goals simp_all [LE.le]
    case lam.lam.lam =>
      intro x;  exact le_trans (hxy x) (hyz x)
    case pair.pair.pair =>
      constructor
      · exact le_trans hxy.1 hyz.1
      · exact le_trans hxy.2 hyz.2

instance [Preorder ρ] : OrderBot (DStep φ ρ) where
  bot := .bot
  bot_le := by intro x; cases x <;> simp_all [LE.le]

instance [PartialOrder ρ] : PartialOrder (DStep φ ρ) where
  le_antisymm := by
    intro x y hxy hyx
    cases x <;> cases y
    all_goals simp_all [LE.le]
    case lam.lam =>
      apply DFunLike.ext; intros
      exact le_antisymm (hxy _) (hyx _)
    case pair.pair =>
      constructor
      · exact le_antisymm hxy.1 hyx.1
      · exact le_antisymm hxy.2 hyx.2

theorem DStep.lam_eval_directed [CompletePartialOrder ρ]
  {s : Set (DStep φ ρ)} (hs : DirectedOn (· ≤ ·) s) (x : ρ) :
  DirectedOn (· ≤ ·) ((· $ x) '' {b | .lam b ∈ s}) := by
  rintro _ ⟨b₁, h₁, rfl⟩ _ ⟨b₂, h₂, rfl⟩
  obtain ⟨z, hz, hz1, hz2⟩ := hs _ h₁ _ h₂
  cases z
  case lam b₃ => exact ⟨b₃ x, ⟨b₃, hz, rfl⟩, hz1 x, hz2 x⟩
  all_goals simp_all [LE.le]

theorem DStep.eval_set_continuous [CompletePartialOrder ρ] {s : Set (DStep φ ρ)}
    (hs : DirectedOn (· ≤ ·) s) :
    ScottContinuous (fun x => sSup ((· $ x) '' {b | .lam b ∈ s})) := by
  have hdir := DStep.lam_eval_directed hs
  intro d hne hddir a ha
  constructor
  · rintro _ ⟨e, hed, rfl⟩
    apply (hdir e).sSup_le
    rintro _ ⟨b, hb, rfl⟩
    exact le_trans (b.scott_continuous.monotone (ha.1 hed))
                   ((hdir _).le_sSup ⟨_, hb, rfl⟩)
  · intro u hu
    apply (hdir a).sSup_le
    rintro _ ⟨b, hb, rfl⟩
    apply (b.scott_continuous hne hddir ha).2
    rintro _ ⟨e, hed, rfl⟩
    exact le_trans ((hdir _).le_sSup ⟨_, hb, rfl⟩)
                   (hu ⟨_, hed, rfl⟩)

theorem DStep.fst_set_directed [CompletePartialOrder ρ] {s : Set (DStep φ ρ)}
    (hs : DirectedOn (· ≤ ·) s) : DirectedOn (· ≤ ·) {a | ∃ b, .pair a b ∈ s} := by
    rintro a ⟨ba, hba⟩ a' ⟨ba', hba'⟩
    obtain ⟨w, hwd, h1, h2⟩ := hs _ hba _ hba'
    cases w
    case pair => exact ⟨_, ⟨_, hwd⟩, h1.1, h2.1⟩
    all_goals simp [LE.le] at h1

theorem DStep.snd_set_directed [CompletePartialOrder ρ] {s : Set (DStep φ ρ)}
    (hs : DirectedOn (· ≤ ·) s) : DirectedOn (· ≤ ·) {b | ∃ a, .pair a b ∈ s} := by
    rintro b ⟨ab, hab⟩ b' ⟨ab', hab'⟩
    obtain ⟨w, hwd, h1, h2⟩ := hs _ hab _ hab'
    cases w
    case pair => exact ⟨_, ⟨_, hwd⟩, h1.2, h2.2⟩
    all_goals simp [LE.le] at h1

noncomputable section
open Classical

instance [CompletePartialOrder ρ] : CompletePartialOrder (DStep φ ρ) where
  sSup s :=
    if hs : DirectedOn (· ≤ ·) s then
      if hf : ∃ v, (DStep.flat v : DStep φ ρ) ∈ s then
        DStep.flat hf.choose
      else if _hl : ∃ b : ρ →ₛ ρ, (DStep.lam b : DStep φ ρ) ∈ s then by
        refine DStep.lam $ ƛₛ[?_] x ↦ sSup $ (· $ x) '' { b | (DStep.lam b) ∈ s}
        exact DStep.eval_set_continuous hs
      else if  ∃ a b, (DStep.pair a b : DStep φ ρ) ∈ s then
        DStep.pair (sSup {a | ∃ b, (DStep.pair a b) ∈ s})
                   (sSup {b | ∃ a, (DStep.pair a b) ∈ s})
      else DStep.bot
    else DStep.bot
  lubOfDirected := by
    intro d hd
    rw [dif_pos hd]
    split_ifs with hf hl hp
    · constructor
      · intro y hy
        obtain ⟨w, hwd, hyw, hvw⟩ := hd y hy _ hf.choose_spec
        cases w <;> simp_all [LE.le]
      · intro u hu; exact hu hf.choose_spec
    · have hdir := DStep.lam_eval_directed hd
      constructor
      · intro y hy
        cases y
        case lam => intro x; exact (hdir x).le_sSup ⟨_, hy, rfl⟩
        case pair =>
          obtain ⟨w, _⟩ := hd _ hy _ (hl.choose_spec)
          cases w <;> simp_all [LE.le]
        all_goals simp_all [LE.le]
      · intro u hu
        cases u
        case lam ub =>
          intro x; apply (hdir x).sSup_le
          rintro _ ⟨b, hb, rfl⟩
          exact (hu hb) x
        all_goals simpa [LE.le] using hu hl.choose_spec
    · constructor
      · intro y hy
        cases y
        case pair a b =>
          constructor
          · exact (DStep.fst_set_directed hd).le_sSup ⟨b, hy⟩
          · exact (DStep.snd_set_directed hd).le_sSup ⟨a, hy⟩
        case lam b =>
          obtain ⟨w, _⟩ := hd _ hy _ hp.choose_spec.choose_spec
          cases w <;> simp_all [LE.le]
        all_goals simp_all [LE.le]
      · intro u hu
        cases u
        case pair ua uc =>
          refine ⟨?_, ?_⟩
          · apply (DStep.fst_set_directed hd).sSup_le
            rintro a ⟨c, hc⟩; exact (hu hc).1
          · apply (DStep.snd_set_directed hd).sSup_le
            rintro c ⟨a, ha⟩; exact (hu ha).2
        all_goals simpa [LE.le] using hu hp.choose_spec.choose_spec
    · constructor
      · intro y hy
        cases y <;> simp_all [LE.le]
      · intro u _; exact bot_le

-- Ugly af but Leo De Moura hates my existance
abbrev DBuild (φ : Type υ) : Nat → Σ ρ : Type _, CompletePartialOrder ρ
| 0     => ⟨DStep φ Empty, inferInstance⟩
| n + 1 => by
  have ⟨ρ, i⟩ := DBuild φ n
  exact ⟨DStep φ ρ, inferInstance⟩
instance : CompletePartialOrder (DBuild φ n).fst := (DBuild φ n).snd

abbrev Dn (φ : Type υ) (n : Nat) : Type _ := (DBuild φ n).fst
instance : CompletePartialOrder (Dn φ n) := (DBuild φ n).snd

theorem DStep.lam_isLUB_eval [CompletePartialOrder α] {d : Set (DStep φ α)}
    (hd : DirectedOn (· ≤ ·) d) {b : α →ₛ α} (hb : IsLUB d (.lam b)) (z : α) :
    IsLUB ((· $ z) '' {b | .lam b ∈ d}) (b z) := by
  have hdir := DStep.lam_eval_directed hd
  have hub : b z ∈ upperBounds ((· $ z) '' {b | .lam b ∈ d}) := by
    rintro _ ⟨b', hb', rfl⟩
    exact (hb.1 hb') z
  have hbz : b z = sSup ((· $ z) '' {b | .lam b ∈ d}) := by
    apply le_antisymm
    · have hgub :
        .lam (ƛₛ[ eval_set_continuous hd ] x ↦ sSup ((· $ x) '' {b | .lam b ∈ d}))
          ∈ upperBounds d := by
        intro y hy
        have := hb.1 hy
        cases y
        case lam b' => intro x; exact (hdir x).le_sSup ⟨b', hy, rfl⟩
        all_goals simp_all [LE.le]
      exact (hb.2 hgub) z
    · exact (hdir z).sSup_le hub
  rw [hbz]
  exact (hdir z).isLUB_sSup

theorem DStep.fst_isLUB [Preorder α] {d : Set (DStep φ α)} {a b : α}
    (ha : IsLUB d (.pair a b)) : IsLUB {x | ∃ y, .pair x y ∈ d} a := by
  refine ⟨fun x ⟨y, hxy⟩ => (ha.1 hxy).1, fun e he => ?_⟩
  have hub : (.pair e b : DStep φ α) ∈ upperBounds d := by
    intro z hz; have := ha.1 hz
    cases z
    case pair x y => exact ⟨he ⟨y, hz⟩, this.2⟩
    all_goals simp_all [LE.le]
  exact (ha.2 hub).1

theorem DStep.snd_isLUB [Preorder α] {d : Set (DStep φ α)} {a b : α}
    (ha : IsLUB d (.pair a b)) : IsLUB {y | ∃ x, .pair x y ∈ d} b := by
  refine ⟨fun y ⟨x, hxy⟩ => (ha.1 hxy).2, fun e he => ?_⟩
  have hub : (.pair a e : DStep φ α) ∈ upperBounds d := by
    intro z hz; have := ha.1 hz
    cases z
    case pair x y => exact ⟨this.1, he ⟨x, hz⟩⟩
    all_goals simp_all [LE.le]
  exact (ha.2 hub).2
