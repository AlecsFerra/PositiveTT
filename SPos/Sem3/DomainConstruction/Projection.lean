import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Order

import SPos.Sem3.DomainConstruction.Approximation

def DStep.map_raw [Preorder α] [Preorder β] (inj : α →ₛ β) (ret : β →ₛ α) : DStep φ α → DStep φ β
  | .bot      => .bot
  | .flat v   => .flat v
  | .pair a b => .pair (inj a) (inj b)
  | .lam b    => .lam (ƛₛ[ by fun_prop ] x ↦ inj (b (ret x)))

set_option linter.unnecessarySimpa false in
noncomputable def DStep.map [CompletePartialOrder α] [CompletePartialOrder β]
    (inj : α →ₛ β) (ret : β →ₛ α) : DStep φ α →ₛ DStep φ β where
  to_fun := DStep.map_raw inj ret
  scott_continuous := by
    intro d hne hddir a ha
    cases a with
    | bot =>
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        cases y <;> simpa [LE.le, DStep.map_raw] using ha.1 hy
      · intro u _; exact bot_le
    | flat v =>
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        cases y <;> simpa [LE.le, DStep.map_raw] using ha.1 hy
      · intro u hu; refine hu ⟨_, ?_, rfl⟩
        obtain ⟨y0, hy0, rfl⟩ : ∃ y ∈ d, y = (.flat v : DStep φ α) := by
          by_contra hcon; push Not at hcon
          have hbot : (.bot : DStep φ α) ∈ upperBounds d := by
            intro y hy; have := ha.1 hy
            cases y
            case flat w => simpa [LE.le] using absurd rfl (hcon _ (this ▸ hy))
            all_goals simpa [LE.le] using ha.1 hy
          exact absurd (ha.2 hbot) (by simp [LE.le])
        exact hy0
    | pair a1 a2 =>
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        cases y
        case pair x c =>
          constructor
          · exact inj.scott_continuous.monotone (ha.1 hy).1
          · exact inj.scott_continuous.monotone (ha.1 hy).2
        all_goals simpa [LE.le, DStep.map_raw] using ha.1 hy
      · intro u hu
        obtain ⟨x0, y0, hp0⟩ : ∃ x0 y0, (.pair x0 y0 : DStep φ α) ∈ d := by
          by_contra hcon; push Not at hcon
          have hbot : (.bot : DStep φ α) ∈ upperBounds d := by
            intro y hy; cases y
            case pair x c => exact absurd hy (hcon x c)
            all_goals simpa [LE.le] using ha.1 hy
          exact absurd (ha.2 hbot) (by simp [LE.le])
        cases u
        case pair ua uc =>
          constructor
          refine (inj.scott_continuous ?_ (DStep.fst_set_directed hddir) ?_).2 ?_
          · exact ⟨x0, y0, hp0⟩
          · exact DStep.fst_isLUB ha
          · rintro _ ⟨x, ⟨y, hxy⟩, rfl⟩
            exact (hu ⟨_, hxy, rfl⟩).1
          refine (inj.scott_continuous ?_ (DStep.snd_set_directed hddir) ?_).2 ?_
          · exact ⟨y0, x0, hp0⟩
          · exact DStep.snd_isLUB ha
          · rintro _ ⟨y, ⟨x, hxy⟩, rfl⟩
            exact (hu ⟨_, hxy, rfl⟩).2
        all_goals simpa [DStep.map_raw, LE.le] using hu ⟨_, hp0, rfl⟩
    | lam b =>
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        cases y
        case lam b' =>
          intro z
          exact inj.scott_continuous.monotone $ ha.1 hy $ ret z
        all_goals simpa [LE.le, DStep.map_raw] using ha.1 hy
      · intro u hu
        obtain ⟨b0, hb0⟩ : ∃ b0, (.lam b0 : DStep φ α) ∈ d := by
          by_contra hcon; push Not at hcon
          have hbot : (.bot : DStep φ α) ∈ upperBounds d := by
            intro y hy; have := ha.1 hy
            cases y
            case lam b' => exact absurd hy (hcon b')
            all_goals simp_all [LE.le]
          exact absurd (ha.2 hbot) (by simp [LE.le])
        cases u
        case lam ub =>
          intro w
          refine (inj.scott_continuous ?_ (DStep.lam_eval_directed hddir (ret w)) ?_).2 ?_
          · exact ⟨_, b0, hb0, rfl⟩
          · exact DStep.lam_isLUB_eval hddir ha (ret w)
          · rintro _ ⟨_, ⟨b'', hb'', rfl⟩, rfl⟩
            exact (hu ⟨_, hb'', rfl⟩) w
        all_goals simpa [DStep.map_raw, LE.le] using hu ⟨_, hb0, rfl⟩

noncomputable section
mutual
  def Dn.up : Dn φ n →ₛ Dn φ (n + 1) := match n with
    | 0     => ƛₛ[ by fun_prop ] _ ↦ .bot
    | _ + 1 => DStep.map Dn.up Dn.down

  def Dn.down : Dn φ (n + 1) →ₛ Dn φ n := match n with
    | 0     => ƛₛ[ by fun_prop ] _ ↦ .bot
    | _ + 1 => DStep.map Dn.down Dn.up
end

@[simp]
theorem DStep.map_apply
    [CompletePartialOrder α]
    [CompletePartialOrder β]
    (inj : α →ₛ β)
    (ret : β →ₛ α)
    (x : DStep φ α) :
    DStep.map inj ret x = DStep.map_raw inj ret x := rfl

def Dn.embedding : Embedding (Dn φ n) (Dn φ (n + 1)) where
  inj := Dn.up
  ret := Dn.down
  ret_inj := by
    intro x; induction n <;> cases x
    all_goals simp_all [Dn.up, Dn.down, DStep.map, DStep.map_raw]
    congr
  inj_ret := by
    intro x; induction n <;> cases x
    all_goals simp_all [Dn.up, Dn.down, DStep.map, DStep.map_raw]
    all_goals try exact bot_le
    case succ.lam ih a =>
      intro x
      exact le_trans (ih _) (a.scott_continuous.monotone (ih x))
    case succ.pair =>
      constructor <;> simp_all

@[fun_prop]
theorem Dn.up_cont : ∀ n, ScottContinuous (Dn.up (φ := φ) (n := n)) := by
  intros; exact Dn.up.scottContinuous
@[fun_prop]
theorem Dn.down_cont : ∀ n, ScottContinuous (Dn.down (φ := φ) (n := n)) := by
  intros; exact Dn.down.scottContinuous

def Dn.up_n : (n : Nat) → Dn φ m →ₛ Dn φ (m + n)
| 0     => ƛₛ[ by fun_prop ] x ↦ x
| n + 1 => ƛₛ[ by fun_prop ] x ↦ Dn.up (Dn.up_n n x)

def Dn.down_n : (n : Nat) → Dn φ (m + n) →ₛ Dn φ m
| 0     => ƛₛ[ by fun_prop ] x ↦ x
| n + 1 => ƛₛ[ by fun_prop ] x ↦ Dn.down_n n (Dn.down x)
