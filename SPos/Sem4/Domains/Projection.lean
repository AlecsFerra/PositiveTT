import Mathlib.Data.Vector.Basic
import Mathlib.Order.CompletePartialOrder

import SPos.Sem4.Domains.ScottContinuous
import SPos.Sem4.Domains.Approximation

set_option linter.unnecessarySimpa false in
def Approx.imap [CompletePartialOrder ρ] [CompletePartialOrder σ]
    (fwd : ρ →ₛ σ) (bwd : σ →ₛ ρ) : Approx ρ →ₛ Approx σ where
  to_fun x := match x with
  | .bot      => .bot
  | .op t v w => .op t (v.map fwd) (w.map fun b => ƛₛ x ↦ fwd $ b $ bwd x)
  scott_continuous := by
    intro d hne hddir a ha
    cases a
    case op t v w =>
      constructor
      rintro _ ⟨y, hy, rfl⟩
      cases y
      case bot => simpa [LE.le] using ha.1 hy
      case op t' v' w' =>
        obtain ⟨rfl, hv, hw⟩ := ha.1 hy
        simp_all [LE.le]
        constructor
        all_goals
          intros; simp [List.Vector.get]
          apply fwd.scott_continuous.monotone
        · apply hv
        · apply hw
      obtain ⟨v₀, w₀, hmem₀⟩ := Approx.exists_op_of_isLUB ha
      intro u hu; cases u
      case right.op t v w =>
        obtain ⟨rfl, hv, hw⟩ := hu (Set.mem_image_of_mem _ hmem₀)
        refine ⟨rfl, fun i => ?_, fun j x => ?_⟩
        all_goals simp [List.Vector.get_map]
        · refine (fwd.scott_continuous ?_ (Approx.directedOn_proj_v hddir t i)
            (Approx.isLUB_proj_v ha i)).2 ?_
          · exact ⟨v₀.get i, v₀, w₀, hmem₀, rfl⟩
          · rintro _ ⟨_, ⟨v', w', hm', rfl⟩, rfl⟩
            have q := (hu (Set.mem_image_of_mem _ hm')).2.1 i
            rwa [List.Vector.get_map] at q
        · refine (fwd.scott_continuous ?_ (Approx.directedOn_proj_w hddir t j (bwd x))
            (Approx.isLUB_proj_w hddir ha j (bwd x))).2 ?_
          · exact ⟨(w₀.get j) (bwd x), v₀, w₀, hmem₀, rfl⟩
          · rintro _ ⟨_, ⟨v', w', hm', rfl⟩, rfl⟩
            have q := (hu (Set.mem_image_of_mem _ hm')).2.2 j x
            rwa [List.Vector.get_map] at q
      case right.bot => exact (hu (Set.mem_image_of_mem _ hmem₀)).elim
    case bot =>
      constructor
      · rintro _ ⟨y, hy, rfl⟩
        cases y <;> simpa [LE.le] using ha.1 hy
      · intro u _; simp

noncomputable section

def D.shift : (n m : Nat) → (D n →ₛ D m)
  | _,     0     => ƛₛ _ ↦ ⊥
  | 0,     _ + 1 => ƛₛ _ ↦ ⊥
  | n + 1, m + 1 => Approx.imap (D.shift n m) (D.shift m n)
termination_by n m => min n m

abbrev D.up : D n →ₛ D (n + 1) := D.shift n (n + 1)

abbrev D.down : D (n + 1) →ₛ D n := D.shift (n + 1) n

@[simp]
theorem D.shift_zero : D.shift n n = ƛₛ x ↦ x := match n with
  | 0     => by simp [D.shift]
  | _ + 1 => by
    ext x; cases x
    all_goals simp [D.shift, Approx.imap]
    congr <;> ext <;> simp [D.shift_zero]

@[simp]
theorem D.shift_bot : D.shift n m ⊥ = ⊥ := match n, m with
  | _,     0     => by simp [D.shift]
  | 0,     _ + 1 => by simp [D.shift]
  | _ + 1, _ + 1 => by simp [D.shift, Approx.imap]; rfl

theorem D.shift_comp (h : min n k ≤ m)
  : D.shift m k (D.shift n m x) = D.shift n k x := match n, m, k, h, x with
  | _,     _,     0,     _, _ => by simp [D.shift]
  | _ + 1, 0,     _ + 1, h, _ => by grind
  | 0,     m,     _ + 1, _, x => by cases x; grind [D.shift_bot]
  | n + 1, m + 1, k + 1, h, x => by
    have hnk : min n k ≤ m := by grind
    have hkn : min k n ≤ m := by grind
    cases x
    case bot =>
      show D.shift _ _ (D.shift _ _ ⊥) = D.shift _ _ ⊥
      grind [D.shift_bot]
    case op t v w =>
      simp [D.shift, Approx.imap]
      congr 1
      all_goals
        ext; simp [List.Vector.get_map]
        try rw [D.shift_comp hnk]
        try rw [D.shift_comp hkn]
termination_by n + m + k

def D.embedding : Embedding (D n) (D (n + 1)) where
  inj := D.up
  ret := D.down
  ret_inj x := by
    show D.shift (n + 1) n (D.shift n (n + 1) x) = x
    rw [D.shift_comp (by grind)]; simp
  inj_ret := by
    induction n with
    | zero => intro x; simp [D.shift]
    | succ n ih =>
      intro x; cases x
      case bot => simp [D.shift, Approx.imap]
      case op t v w =>
        simp [D.shift, Approx.imap]
        apply Approx.op_le_op rfl
        · intro i; simpa using ih (v.get i)
        · intro j x
          simp [List.Vector.get_map]
          exact le_trans (ih _) ((w.get j).scott_continuous.monotone (ih x))

theorem D.shift_up_down_le {n m : Nat} (h : n ≤ m) (y : D m) :
    D.shift n m (D.shift m n y) ≤ y := by
  induction m with
  | zero => obtain rfl : n = 0 := Nat.le_zero.mp h; simp
  | succ m ih =>
    rcases Nat.lt_or_ge n (m + 1) with hn | hn
    · have hnm : n ≤ m := Nat.lt_succ_iff.mp hn
      have e₁ : D.shift (m+1) n y = D.shift m n (D.down y) :=
        (D.shift_comp (n := m+1) (m := m) (k := n) (by grind)).symm
      have e₂ : D.up (D.shift n m (D.shift m n (D.down y)))
              = D.shift n (m+1) (D.shift m n (D.down y)) :=
        D.shift_comp (n := n) (m := m) (k := m+1) (by grind)
      rw [e₁, ← e₂]
      exact le_trans ((D.shift m (m+1)).scott_continuous.monotone (ih hnm _))
                     (D.embedding.inj_ret y)
    · obtain rfl : n = m + 1 := Nat.le_antisymm h hn
      simp

theorem D.shift_shift_le {p q : Nat} (hpq : p ≤ q) (k : Nat) (y : D q) :
    D.shift p k (D.shift q p y) ≤ D.shift q k y := by
  rcases Nat.le_total k p with hk | hk
  · rw [D.shift_comp (n := q) (m := p) (k := k) (by grind)]
  · rcases Nat.le_total k q with hkq | hkq
    · rw [← D.shift_comp (n := q) (m := k) (k := p) (by grind) (x := y)]
      exact D.shift_up_down_le hk _
    · rw [← D.shift_comp (n := p) (m := q) (k := k) (by grind)]
      exact (D.shift q k).scott_continuous.monotone (D.shift_up_down_le hpq _)
