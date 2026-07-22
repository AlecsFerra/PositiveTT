import SPos.Sem4.Domains.Approximation
import SPos.Sem4.Domains.Projection
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.FinCases

structure Dinf where
  approx : ∀ n, D n
  coh : ∀ n, (approx $ n + 1).down = approx n
notation "D∞" => Dinf

@[simp]
theorem D.down_bot : (D.down (⊥ : D (n + 1)) : D n) = ⊥ :=
  D.shift_bot

@[ext]
theorem Dinf.ext {x y : D∞} (h : ∀ n, x.approx n = y.approx n) : x = y := by
  cases x; cases y; simpa using funext h

noncomputable section

instance : PartialOrder D∞ where
  le x y      := ∀ n, x.approx n ≤ y.approx n
  le_refl     := fun _ _ => le_refl _
  le_trans    := fun x y z hxy hyz n => le_trans (hxy n) (hyz n)
  le_antisymm := by intro x y hxy hyx; ext n; exact le_antisymm (hxy n) (hyx n)

instance : OrderBot D∞ where
  bot    := ⟨fun _ => ⊥, fun _ => D.down_bot⟩
  bot_le := fun _ _ => bot_le

theorem Dinf.directedOn_approx {s : Set D∞} (hs : DirectedOn (· ≤ ·) s) (n : Nat) :
    DirectedOn (· ≤ ·) ((·.approx n) '' s) := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hs a ha b hb
  exact ⟨c.approx n, ⟨c, hc, rfl⟩, hac n, hbc n⟩

open Classical

theorem Dinf.pointwiseSup_coh {s : Set D∞} (hs : DirectedOn (· ≤ ·) s) (hne : s.Nonempty) :
  D.down (sSup ((·.approx (n + 1)) '' s)) = sSup ((·.approx n) '' s) := by
  let dapp := Dinf.directedOn_approx hs (n + 1)
  apply ((D.down.scottContinuous) (hne.image _) dapp dapp.isLUB_sSup).unique
  have himg : (·.down) '' (·.approx (n + 1)) '' s = (·.approx n) '' s := by
    simp [Set.image_image]
    apply Set.image_congr
    intro x hx; exact x.coh _
  simpa [himg] using (Dinf.directedOn_approx hs n).isLUB_sSup

def Dinf.pointwiseSup (s : Set D∞) : D∞ :=
  if hs : DirectedOn (· ≤ ·) s ∧ s.Nonempty then
    ⟨fun n => sSup ((·.approx n) '' s), fun _ => Dinf.pointwiseSup_coh hs.1 hs.2⟩
  else ⊥

instance : SupSet D∞ where
  sSup := Dinf.pointwiseSup

theorem sSup_approx {s : Set D∞} (hs : DirectedOn (· ≤ ·) s) (hne : s.Nonempty) :
    (sSup s).approx n = sSup ((·.approx n) '' s) := by
  have hc : DirectedOn (· ≤ ·) s ∧ s.Nonempty := ⟨hs, hne⟩
  show (Dinf.pointwiseSup s).approx n = _
  simp [Dinf.pointwiseSup, dif_pos hc]

instance : CompletePartialOrder D∞ where
  lubOfDirected s hs := by
    rcases s.eq_empty_or_nonempty with rfl | hne
    · refine ⟨fun a ha => ha.elim, fun u _ => ?_⟩
      have hbot : (sSup (∅ : Set D∞)) = ⊥ := dif_neg (by simp)
      simp [hbot]
    · constructor
      · intro x hx n
        simpa [sSup_approx hs hne]
        using (Dinf.directedOn_approx hs n).le_sSup ⟨x, hx, rfl⟩
      · intro u hu n
        simp [sSup_approx hs hne]
        refine (Dinf.directedOn_approx hs n).sSup_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact hu hx n

@[fun_prop]
theorem Dinf.scottContinuous_approx (n : Nat) :
    ScottContinuous (Dinf.approx · n) := by
  apply CompletePartialOrder.scottContinuous.mpr
  intro d hne hdir
  simpa [sSup_approx hdir hne] using (Dinf.directedOn_approx hdir n).isLUB_sSup

def Dinf.emb : D n →ₛ D∞ := by
  refine ƛₛ[?_] x ↦ ⟨fun m => D.shift n m x, ?_⟩
  · intro n; exact D.shift_comp (by grind)
  · intro d hne hdir a ha
    constructor
    · rintro _ ⟨x, hx, rfl⟩ m
      exact (D.shift n m).scott_continuous.monotone (ha.1 hx)
    · intro u hu m
      refine ((D.shift n m).scott_continuous hne hdir ha).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hu (Set.mem_image_of_mem _ hx) m

@[simp]
theorem Dinf.emb_approx {n : Nat} (x : D n) (k : Nat) :
    (Dinf.emb x).approx k = D.shift n k x := rfl

theorem Dinf.emb_up {m : Nat} (x : D m) : Dinf.emb (D.up x) = Dinf.emb x := by
  apply Dinf.ext; intro k
  show D.shift (m + 1) k (D.up x) = D.shift m k x
  exact D.shift_comp (by omega)

def Dinf.op (t : Tag) (v : List.Vector D∞ t.arity.1)
    (w : List.Vector (D∞ →ₛ D∞) t.arity.2) : D∞ where
  approx n := match n with
    | 0     => ⊥
    | n + 1 => .op t (v.map (·.approx n))
                     (w.map fun b => ƛₛ a ↦ (b $ .emb a).approx n)
  coh := by
    intro n; cases n <;> simp [D.down, D.shift, Approx.imap]
    congr 1 <;> ext <;> simp [List.Vector.get_map]
    · exact (v.get _).coh _
    · rw [Dinf.emb_up]
      exact ((w.get _) (Dinf.emb _)).coh _

theorem Dinf.isLUB_of_approx {d : Set D∞} {a : D∞}
    (h : ∀ m, IsLUB ((·.approx m) '' d) (a.approx m)) : IsLUB d a := by
  constructor
  · intro z hz m
    exact (h m).1 ⟨z, hz, rfl⟩
  · intro u hu m
    apply (h m).2
    rintro _ ⟨z, hz, rfl⟩
    exact hu hz m

theorem Dinf.op_scottContinuous [Preorder E] {v : E → List.Vector D∞ t.arity.1}
    {w : E → List.Vector (D∞ →ₛ D∞) t.arity.2}
    (hv : ∀ i, ScottContinuous fun a => (v a).get i)
    (hw : ∀ j x, ScottContinuous fun a => (w a).get j x) :
    ScottContinuous fun a => Dinf.op t (v a) (w a) := by
  intro d hne hd c hc
  apply Dinf.isLUB_of_approx
  intro m; cases m
  · exact ⟨fun _ _ => trivial, fun _ _ => trivial⟩
  · simp [Set.image_image]
    apply Approx.isLUB_op hne
    · intro i
      simpa [Function.comp, List.Vector.get_map]
        using ((hv i).comp (Dinf.scottContinuous_approx _)) hne hd hc
    · intro j y
      simpa [Function.comp, List.Vector.get_map]
        using ((hw j (Dinf.emb y)).comp (Dinf.scottContinuous_approx _)) hne hd hc


@[match_pattern]
abbrev Dinf.univ (ℓ : Nat) : D∞ :=
  Dinf.op (.univ ℓ) .nil .nil

@[match_pattern]
def Dinf.pi : D∞ →ₛ (D∞ →ₛ D∞) →ₛ D∞ := by
  refine ƛₛ[?_] τ ↦ ƛₛ[?_] υ ↦ Dinf.op .pi ⟨[τ], by simp⟩ ⟨[υ], by simp⟩
  · apply Dinf.op_scottContinuous
    · intro i; simp
    · intro j x; simp [Fin.fin_one_eq_zero j, List.Vector.head]; fun_prop
  · apply ScottContinuousF.of_apply₂
    intro υ
    apply Dinf.op_scottContinuous
    · intro i;   simp [Fin.fin_one_eq_zero i, List.Vector.head]
    · intro j x; simp [Fin.fin_one_eq_zero j, List.Vector.head]

@[match_pattern]
def Dinf.sigma : D∞ →ₛ (D∞ →ₛ D∞) →ₛ D∞ := by
  refine ƛₛ[?_] τ ↦ ƛₛ[?_] υ ↦ Dinf.op .sigma ⟨[τ], by simp⟩ ⟨[υ], by simp⟩
  · apply Dinf.op_scottContinuous
    · intro i; simp
    · intro j x; simp [Fin.fin_one_eq_zero j, List.Vector.head]; fun_prop
  · apply ScottContinuousF.of_apply₂
    intro υ
    apply Dinf.op_scottContinuous
    · intro i;   simp [Fin.fin_one_eq_zero i, List.Vector.head]
    · intro j x; simp [Fin.fin_one_eq_zero j, List.Vector.head]

@[match_pattern]
def Dinf.lam : (D∞ →ₛ D∞) →ₛ D∞ := by
  refine ƛₛ[?_] b ↦ Dinf.op .lam .nil ⟨[b], by simp⟩
  · apply Dinf.op_scottContinuous
    · intro i; exact i.elim0
    · intro j x; simp [Fin.fin_one_eq_zero j, List.Vector.head]; fun_prop

@[match_pattern]
def Dinf.mu : (D∞ →ₛ D∞) →ₛ D∞ := by
  refine ƛₛ[?_] B ↦ Dinf.op .mu .nil ⟨[B], by simp⟩
  · apply Dinf.op_scottContinuous
    · intro i; exact i.elim0
    · intro j x; simp [Fin.fin_one_eq_zero j, List.Vector.head]; fun_prop

@[match_pattern]
def Dinf.pair : D∞ →ₛ D∞ →ₛ D∞ := by
  refine ƛₛ[?_] a ↦ ƛₛ[?_] b ↦ Dinf.op .pair ⟨[a, b], by simp⟩ .nil
  · apply Dinf.op_scottContinuous
    · rintro ⟨_ | _ | i, hi⟩ <;> simp only [Tag.arity] at hi <;>
        first | exact absurd hi (by omega) | simp [List.Vector.get]
    · intro j; exact j.elim0
  · apply ScottContinuousF.of_apply₂
    intro b
    apply Dinf.op_scottContinuous
    · rintro ⟨_ | _ | i, hi⟩ <;> simp only [Tag.arity] at hi <;>
        first | exact absurd hi (by omega) | simp [List.Vector.get]
    · intro j; exact j.elim0

@[match_pattern]
def Dinf.id : D∞ →ₛ D∞ →ₛ D∞ →ₛ D∞ := by
  refine ƛₛ[?_] τ ↦ ƛₛ[?_] a ↦ ƛₛ[?_] b ↦ Dinf.op .id ⟨[τ, a, b], by simp⟩ .nil
  · apply Dinf.op_scottContinuous
    · rintro ⟨_ | _ | i, hi⟩ <;> simp only [Tag.arity] at hi <;>
        first | exact absurd hi (by omega) | simp [List.Vector.get]
    · intro j; exact j.elim0
  · apply ScottContinuousF.of_apply₂
    intro b
    apply Dinf.op_scottContinuous
    · rintro ⟨_ | _ | i, hi⟩ <;> simp only [Tag.arity] at hi <;>
        first | exact absurd hi (by omega) | simp [List.Vector.get]
    · intro j; exact j.elim0
  · apply ScottContinuousF.of_apply₂
    intro a
    apply ScottContinuousF.of_apply₂
    intro b
    apply Dinf.op_scottContinuous
    · rintro ⟨_ | _ | i, hi⟩ <;> simp only [Tag.arity] at hi <;>
        first | exact absurd hi (by omega) | simp [List.Vector.get]
    · intro j; exact j.elim0

@[match_pattern]
def Dinf.roll : D∞ →ₛ D∞ := by
  refine ƛₛ[?_] x ↦ Dinf.op .roll ⟨[x], by simp⟩ .nil
  · apply Dinf.op_scottContinuous
    · intro i
      simp [Fin.fin_one_eq_zero i, List.Vector.head]
    · intro j x; exact j.elim0

@[match_pattern] abbrev Dinf.bool  : D∞ := Dinf.op .bool  .nil .nil
@[match_pattern] abbrev Dinf.true  : D∞ := Dinf.op .true  .nil .nil
@[match_pattern] abbrev Dinf.false : D∞ := Dinf.op .false .nil .nil
@[match_pattern] abbrev Dinf.refl  : D∞ := Dinf.op .refl  .nil .nil

def Dinf.tagOf (x : D∞) : Option Tag :=
  match x.approx 1 with
  | .bot      => none
  | .op t _ _ => some t

@[simp]
theorem Dinf.tagOf_op {v : List.Vector D∞ t.arity.1} {w} : (Dinf.op t v w).tagOf = some t := rfl

@[simp]
theorem Dinf.tagOf_bot : (⊥ : D∞).tagOf = none := rfl

theorem Dinf.tagOf_of_approx {x : D∞} (h : ∃ v w, x.approx (n + 1) = .op t v w) :
    x.tagOf = some t := by
  induction n
  case zero =>
    obtain ⟨v, w, hv⟩ := h
    unfold Dinf.tagOf; rw [hv]
  case succ n ih =>
    obtain ⟨v, w, hv⟩ := h
    refine ih ?_
    have hc := x.coh (n + 1)
    rw [hv] at hc
    simp [D.down, D.shift, Approx.imap] at hc
    exact ⟨_, _, hc.symm⟩

theorem Dinf.eq_bot_of_tagOf_none {x : D∞} (h : x.tagOf = none) : x = ⊥ := by
  apply Dinf.ext; intro n
  cases n
  case zero => cases x.approx 0; rfl
  case succ n =>
    rcases e : x.approx (n + 1) with _ | ⟨t, v, w⟩
    · rfl
    · rw [Dinf.tagOf_of_approx ⟨v, w, e⟩] at h; exact absurd h (by simp)

theorem Dinf.tagOf_eq_none_iff {x : D∞} : x.tagOf = none ↔ x = ⊥ :=
  ⟨Dinf.eq_bot_of_tagOf_none, fun h => by subst h; rfl⟩

theorem Dinf.tagOf_mono {x y : D∞} (hxy : x ≤ y) (hx : x.tagOf = some t) :
    y.tagOf = some t := by
  have h := hxy 1
  unfold Dinf.tagOf at hx ⊢
  split at hx
  · exact absurd hx (by simp)
  · next hxe =>
    rw [hxe] at h
    split
    · next hye => rw [hye] at h; exact h.elim
    · next hye => rw [hye] at h; obtain ⟨rfl, _, _⟩ := h; exact hx

theorem Dinf.exists_tagOf_of_isLUB {d : Set D∞} {a : D∞} (hne : d.Nonempty)
    (hdir : DirectedOn (· ≤ ·) d) (ha : IsLUB d a) (ht : a.tagOf = some t) :
    ∃ z ∈ d, z.tagOf = some t := by
  have h1 : IsLUB ((·.approx 1) '' d) (a.approx 1) :=
    Dinf.scottContinuous_approx 1 hne hdir ha
  unfold Dinf.tagOf at ht
  split at ht
  · exact absurd ht (by simp)
  · next hae =>
    obtain rfl := Option.some.inj ht
    rw [hae] at h1
    obtain ⟨v', w', z, hz, hze⟩ := Approx.exists_op_of_isLUB h1
    exact ⟨z, hz, by unfold Dinf.tagOf; simp only [] at hze; rw [hze]⟩

open Classical in
/-- Extract a payload from an `Approx`: `sel` picks the field out of the two
payload vectors, and a tag mismatch (or `bot`) yields `⊥`. `getV`/`getW` are
the two instantiations. -/
def Approx.get' [CompletePartialOrder ρ] (t : Tag)
    (sel : List.Vector ρ t.arity.1 → List.Vector (ρ →ₛ ρ) t.arity.2 → ρ)
    (x : Approx ρ) : ρ :=
  match x with
  | .bot        => ⊥
  | .op t' v w  => if h : t' = t then sel (h ▸ v) (h ▸ w) else ⊥

@[simp]
theorem Approx.get'_bot [CompletePartialOrder ρ] {sel} :
    (Approx.bot : Approx ρ).get' t sel = ⊥ := rfl

@[simp]
theorem Approx.get'_op [CompletePartialOrder ρ] {sel} {v : List.Vector ρ t.arity.1} {w} :
    (Approx.op t v w).get' t sel = sel v w := by simp [Approx.get']

theorem Approx.get'_op_of_ne [CompletePartialOrder ρ] {sel} (h : t' ≠ t)
    {v : List.Vector ρ t'.arity.1} {w} : (Approx.op t' v w).get' t sel = ⊥ := by
  simp [Approx.get', h]

theorem Approx.get'_mono [CompletePartialOrder ρ] {sel} {x y : Approx ρ}
    (hsel : ∀ {v₁ w₁ v₂ w₂}, (∀ i, List.Vector.get v₁ i ≤ List.Vector.get v₂ i) →
      (∀ j a, (List.Vector.get w₁ j) a ≤ (List.Vector.get w₂ j) a) → sel v₁ w₁ ≤ sel v₂ w₂)
    (h : x ≤ y) : x.get' t sel ≤ y.get' t sel := by
  cases x
  case bot => simp
  case op tx vx wx =>
    cases y
    case bot => exact h.elim
    case op ty vy wy =>
      obtain ⟨rfl, hv, hw⟩ := h
      by_cases htx : tx = t
      · subst htx; rw [Approx.get'_op, Approx.get'_op]; exact hsel hv hw
      · rw [Approx.get'_op_of_ne htx, Approx.get'_op_of_ne htx]

/-- The value payload: `x.getV t i` is the `i`-th self-reference under tag `t`. -/
abbrev Approx.getV [CompletePartialOrder ρ] (t : Tag) (i : Fin t.arity.1) (x : Approx ρ) : ρ :=
  x.get' t fun v _ => v.get i

/-- The function payload applied to `a`. -/
abbrev Approx.getW [CompletePartialOrder ρ] (t : Tag) (j : Fin t.arity.2)
    (x : Approx ρ) (a : ρ) : ρ :=
  x.get' t fun _ w => (w.get j) a

theorem Approx.getV_mono [CompletePartialOrder ρ] {x y : Approx ρ} (h : x ≤ y) :
    x.getV t i ≤ y.getV t i :=
  Approx.get'_mono (fun hv _ => hv _) h

theorem Approx.getW_mono [CompletePartialOrder ρ] {x y : Approx ρ} (h : x ≤ y) (a : ρ) :
    x.getW t j a ≤ y.getW t j a :=
  Approx.get'_mono (fun _ hw => hw _ _) h

theorem Approx.getW_mono_arg [CompletePartialOrder ρ] (x : Approx ρ) {a b : ρ} (h : a ≤ b) :
    x.getW t j a ≤ x.getW t j b := by
  cases x
  case bot => simp
  case op t' v w =>
    by_cases ht : t' = t
    · subst ht
      simp only [Approx.getW, Approx.get'_op]
      exact (w.get j).scott_continuous.monotone h
    · simp only [Approx.getW, Approx.get'_op_of_ne ht]; exact le_rfl

theorem Approx.getV_imap [CompletePartialOrder ρ] [CompletePartialOrder σ]
    (fwd : ρ →ₛ σ) (bwd : σ →ₛ ρ) (hb : fwd ⊥ = ⊥) (x : Approx ρ) :
    (Approx.imap fwd bwd x).getV t i = fwd (x.getV t i) := by
  cases x
  case bot => simpa [Approx.imap] using hb.symm
  case op t' v w =>
    by_cases h : t' = t
    · subst h; simp [Approx.imap, List.Vector.get_map]
    · simp [Approx.imap, Approx.get'_op_of_ne h, hb]

theorem Approx.getW_imap [CompletePartialOrder ρ] [CompletePartialOrder σ]
    (fwd : ρ →ₛ σ) (bwd : σ →ₛ ρ) (hb : fwd ⊥ = ⊥) (x : Approx ρ) (a : σ) :
    (Approx.imap fwd bwd x).getW t j a = fwd (x.getW t j (bwd a)) := by
  cases x
  case bot => simpa [Approx.imap] using hb.symm
  case op t' v w =>
    by_cases h : t' = t
    · subst h; simp [Approx.imap, List.Vector.get_map]
    · simp [Approx.imap, Approx.get'_op_of_ne h, hb]

theorem Approx.getV_scottContinuous [CompletePartialOrder ρ] :
    ScottContinuous (Approx.getV t i : Approx ρ → ρ) := by
  intro d hne hdir a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact Approx.getV_mono (ha.1 hx)
  · intro u hu
    rcases hae : a with _ | ⟨t', v, w⟩
    · obtain ⟨x, hx⟩ := hne
      show (⊥ : ρ) ≤ u
      refine le_trans ?_ (hu ⟨x, hx, rfl⟩)
      have : x = Approx.bot := by
        have := ha.1 hx; rw [hae] at this; cases x
        · rfl
        · exact this.elim
      subst this; simp
    · by_cases ht : t' = t
      · subst ht
        subst hae
        simp only [Approx.getV, Approx.get'_op]
        refine (Approx.isLUB_proj_v ha i).2 ?_
        rintro _ ⟨v', w', hm, rfl⟩
        simpa using hu ⟨_, hm, rfl⟩
      · obtain ⟨x, hx⟩ := hne
        simp only [Approx.getV, Approx.get'_op_of_ne ht]
        exact le_trans (OrderBot.bot_le (Approx.getV t i x)) (hu ⟨x, hx, rfl⟩)

/-- Project the `i`-th value payload under tag `t`, level by level. -/
def Dinf.projV (t : Tag) (i : Fin t.arity.1) : D∞ →ₛ D∞ := by
  refine ƛₛ[?_] x ↦ ⟨fun n => (x.approx (n + 1)).getV t i, fun n => ?_⟩
  · rw [← x.coh (n + 1)]
    conv_rhs => rw [D.down, D.shift]
    exact (Approx.getV_imap (D.shift (n + 1) n) (D.shift n (n + 1)) D.shift_bot _).symm
  · intro d hne hdir a ha
    apply Dinf.isLUB_of_approx
    intro n
    simpa [Function.comp, Set.image_image] using
      ((Dinf.scottContinuous_approx (n + 1)).comp
        (Approx.getV_scottContinuous (t := t) (i := i))) hne hdir ha

@[simp]
theorem Dinf.projV_op {v : List.Vector D∞ t.arity.1} {w} :
    Dinf.projV t i (Dinf.op t v w) = v.get i := by
  apply Dinf.ext; intro n
  show Approx.getV t i ((Dinf.op t v w).approx (n + 1)) = _
  simp [Dinf.op, List.Vector.get_map]

@[simp]
theorem Dinf.projV_bot : Dinf.projV t i ⊥ = ⊥ := by
  apply Dinf.ext; intro n
  show Approx.getV t i (⊥ : D (n + 1)) = (⊥ : D n)
  rfl

def Dinf.fst : D∞ →ₛ D∞ := Dinf.projV .pair ⟨0, by simp⟩
def Dinf.snd : D∞ →ₛ D∞ := Dinf.projV .pair ⟨1, by simp⟩
def Dinf.unroll : D∞ →ₛ D∞ := Dinf.projV .roll ⟨0, by simp⟩

/-- `Dinf.ite b t f` selects on the tag of `b`, and is `⊥` unless `b` is a boolean.
Monotone because a tag, once present, never changes (`Dinf.tagOf_mono`). -/
theorem Dinf.monotone_ite {b₁ b₂ t₁ t₂ f₁ f₂ : D∞}
    (hb : b₁ ≤ b₂) (ht : t₁ ≤ t₂) (hf : f₁ ≤ f₂) :
    (if b₁.tagOf = some .true then t₁ else if b₁.tagOf = some .false then f₁ else ⊥)
      ≤ if b₂.tagOf = some .true then t₂ else if b₂.tagOf = some .false then f₂ else ⊥ := by
  by_cases h₁ : b₁.tagOf = some .true
  · rw [if_pos h₁, if_pos (Dinf.tagOf_mono hb h₁)]; exact ht
  · rw [if_neg h₁]
    by_cases h₂ : b₁.tagOf = some .false
    · have h₂' := Dinf.tagOf_mono hb h₂
      rw [if_pos h₂, if_neg (by rw [h₂']; simp), if_pos h₂']; exact hf
    · rw [if_neg h₂]; exact bot_le

@[fun_prop]
theorem Dinf.scottContinuous_ite [Preorder E] {b t f : E → D∞}
    (hb : ScottContinuous b) (ht : ScottContinuous t) (hf : ScottContinuous f) :
    ScottContinuous fun e =>
      if (b e).tagOf = some .true then t e else if (b e).tagOf = some .false then f e else ⊥ := by
  intro d hne hdir a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact Dinf.monotone_ite (hb.monotone (ha.1 hx)) (ht.monotone (ha.1 hx)) (hf.monotone (ha.1 hx))
  · intro u hu
    show (if (b a).tagOf = some .true then t a else
          if (b a).tagOf = some .false then f a else ⊥) ≤ u
    -- Both boolean branches run the same argument: the tag already occurs at some
    -- `z ∈ d`, and above `z` the `ite` has already committed to that branch.
    have branch : ∀ (tg : Tag) (r : E → D∞), ScottContinuous r → (b a).tagOf = some tg →
        (∀ e, (b e).tagOf = some tg →
          r e ≤ if (b e).tagOf = some .true then t e else
                if (b e).tagOf = some .false then f e else ⊥) → r a ≤ u := by
      intro tg r hr htag hcommit
      obtain ⟨_, ⟨z, hz, rfl⟩, hzt⟩ := Dinf.exists_tagOf_of_isLUB (hne.image b)
        (hdir.mono_comp hb.monotone) (hb hne hdir ha) htag
      refine (hr hne hdir ha).2 ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hxy, hzy⟩ := hdir x hx z hz
      exact le_trans (le_trans (hr.monotone hxy)
        (hcommit y (Dinf.tagOf_mono (hb.monotone hzy) hzt))) (hu ⟨y, hy, rfl⟩)
    by_cases h₁ : (b a).tagOf = some .true
    · rw [if_pos h₁]
      exact branch _ t ht h₁ fun e he => by rw [if_pos he]
    · rw [if_neg h₁]
      by_cases h₂ : (b a).tagOf = some .false
      · rw [if_pos h₂]
        exact branch _ f hf h₂ fun e he => by
          rw [if_neg (by rw [he]; simp), if_pos he]
      · rw [if_neg h₂]
        obtain ⟨x, hx⟩ := hne
        exact le_trans bot_le (hu ⟨x, hx, rfl⟩)

def Dinf.ite : D∞ →ₛ D∞ →ₛ D∞ →ₛ D∞ := by
  refine ƛₛ[?_] b ↦ ƛₛ[?_] t ↦ ƛₛ[?_] f ↦
    if b.tagOf = some .true then t else if b.tagOf = some .false then f else ⊥
  · apply Dinf.scottContinuous_ite <;> fun_prop
  · apply ScottContinuousF.of_apply₂; intro f
    apply Dinf.scottContinuous_ite <;> fun_prop
  · apply ScottContinuousF.of_apply₂; intro t
    apply ScottContinuousF.of_apply₂; intro f
    apply Dinf.scottContinuous_ite <;> fun_prop

@[simp] theorem Dinf.ite_true  : Dinf.ite Dinf.true  t f = t := by simp [Dinf.ite]
@[simp] theorem Dinf.ite_false : Dinf.ite Dinf.false t f = f := by simp [Dinf.ite]
@[simp] theorem Dinf.ite_bot   : Dinf.ite ⊥ t f = ⊥ := by simp [Dinf.ite]

theorem Dinf.ite_eq_bot (h₁ : b.tagOf ≠ some .true) (h₂ : b.tagOf ≠ some .false) :
    Dinf.ite b t f = ⊥ := by simp [Dinf.ite, h₁, h₂]

@[simp] theorem Dinf.fst_pair : Dinf.fst (Dinf.pair a b) = a := by
  show Dinf.projV _ _ _ = _
  simp [Dinf.pair, Dinf.projV_op, List.Vector.get]

@[simp] theorem Dinf.snd_pair : Dinf.snd (Dinf.pair a b) = b := by
  show Dinf.projV _ _ _ = _
  simp [Dinf.pair, Dinf.projV_op, List.Vector.get]

@[simp] theorem Dinf.unroll_roll : Dinf.unroll (Dinf.roll a) = a := by
  show Dinf.projV _ _ _ = _
  simp [Dinf.roll, Dinf.projV_op, List.Vector.get]

theorem Dinf.shift_approx_of_le (x : D∞) {m n : Nat} (h : m ≤ n) :
    D.shift n m (x.approx n) = x.approx m := by
  induction n with
  | zero => obtain rfl : m = 0 := Nat.le_zero.mp h; simp
  | succ n ih =>
    rcases Nat.lt_or_ge m (n + 1) with hm | hm
    · have hmn : m ≤ n := Nat.lt_succ_iff.mp hm
      rw [← ih hmn, ← D.shift_comp (k := m) (n := n+1) (m := n) (by grind), x.coh n]
    · obtain rfl : m = n + 1 := Nat.le_antisymm h hm
      simp

theorem Dinf.emb_approx_le (x : D∞) (n : Nat) : Dinf.emb (x.approx n) ≤ x := by
  intro m
  show D.shift n m (x.approx n) ≤ x.approx m
  rcases Nat.le_total m n with h | h
  · rw [Dinf.shift_approx_of_le x h]
  · rw [← Dinf.shift_approx_of_le x h]
    exact D.shift_up_down_le h _

theorem Dinf.isLUB_emb_approx (x : D∞) :
    IsLUB (Set.range fun n => Dinf.emb (x.approx n)) x := by
  constructor
  · rintro _ ⟨n, rfl⟩; exact Dinf.emb_approx_le x n
  · intro u hu m
    have := hu ⟨m, rfl⟩ m
    rwa [Dinf.emb_approx, D.shift_zero] at this

theorem Dinf.up_approx_le (a : D∞) (n : Nat) : D.up (a.approx n) ≤ a.approx (n + 1) := by
  simpa [D.embedding, a.coh n] using (D.embedding (n := n)).inj_ret (a.approx (n + 1))

theorem Dinf.emb_approx_monotone (a : D∞) : Monotone (fun n => Dinf.emb (a.approx n)) := by
  intro p q hpq k
  show D.shift p k (a.approx p) ≤ D.shift q k (a.approx q)
  conv_lhs => rw [← Dinf.shift_approx_of_le a hpq]
  exact D.shift_shift_le hpq k _

theorem Dinf.directedOn_emb_approx (a : D∞) :
    DirectedOn (· ≤ ·) (Set.range fun n => Dinf.emb (a.approx n)) :=
  directedOn_range_of_monotone (Dinf.emb_approx_monotone a)

def Dinf.appAt (t : Tag) (j : Fin t.arity.2) (f a : D∞) (n : Nat) : D∞ :=
  Dinf.emb ((f.approx (n + 1)).getW t j (a.approx n))

theorem Dinf.appAt_succ (t : Tag) (j : Fin t.arity.2) (f a : D∞) (n : Nat) :
    Dinf.appAt t j f a n ≤ Dinf.appAt t j f a (n + 1) := by
  unfold Dinf.appAt
  have key : (f.approx (n + 1)).getW t j (a.approx n)
      = D.down ((f.approx (n + 2)).getW t j (D.up (a.approx n))) := by
    rw [← f.coh (n + 1)]
    conv_lhs => rw [D.down, D.shift]
    exact Approx.getW_imap (D.shift (n+1) n) (D.shift n (n+1)) D.shift_bot _ _
  rw [key]
  refine le_trans ?_ ((Dinf.emb).scott_continuous.monotone
    (Approx.getW_mono_arg _ (Dinf.up_approx_le a n)))
  rw [← Dinf.emb_up (D.down _)]
  exact (Dinf.emb).scott_continuous.monotone (D.embedding.inj_ret _)

theorem Dinf.appAt_monotone (t : Tag) (j : Fin t.arity.2) (f a : D∞) :
    Monotone (Dinf.appAt t j f a) :=
  monotone_nat_of_le_succ (Dinf.appAt_succ t j f a)

/-- Apply the `j`-th function payload of `f` (under tag `t`) to `a`, as the
sup of the finite stages. -/
def Dinf.projW (t : Tag) (j : Fin t.arity.2) (f a : D∞) : D∞ :=
  sSup (Set.range (Dinf.appAt t j f a))

theorem Dinf.projW_lam (b : D∞ →ₛ D∞) (a : D∞) :
    Dinf.projW .lam ⟨0, by simp⟩ (Dinf.lam b) a = b a := by
  have hstage : Set.range (Dinf.appAt .lam ⟨0, by simp⟩ (Dinf.lam b) a)
      = Set.range (fun n => Dinf.emb ((b (Dinf.emb (a.approx n))).approx n)) := rfl
  have hdir := directedOn_range_of_monotone
    (Dinf.appAt_monotone .lam ⟨0, by simp⟩ (Dinf.lam b) a)
  have hb : IsLUB (Set.range fun n => b (Dinf.emb (a.approx n))) (b a) := by
    have := b.scott_continuous (Set.range_nonempty _) (Dinf.directedOn_emb_approx a)
      (Dinf.isLUB_emb_approx a)
    rwa [← Set.range_comp] at this
  unfold Dinf.projW
  apply le_antisymm
  · refine hdir.sSup_le ?_
    rintro _ ⟨n, rfl⟩
    exact le_trans (Dinf.emb_approx_le _ n) (hb.1 ⟨n, rfl⟩)
  · refine hb.2 ?_
    rintro _ ⟨n, rfl⟩
    refine (Dinf.isLUB_emb_approx (b (Dinf.emb (a.approx n)))).2 ?_
    rintro _ ⟨m, rfl⟩
    refine le_trans ?_ (hdir.le_sSup ⟨max n m, rfl⟩)
    show Dinf.emb ((b (Dinf.emb (a.approx n))).approx m)
       ≤ Dinf.emb ((b (Dinf.emb (a.approx (max n m)))).approx (max n m))
    refine le_trans ((Dinf.emb).scott_continuous.monotone ?_)
      (Dinf.emb_approx_monotone (b (Dinf.emb (a.approx (max n m)))) (le_max_right n m))
    exact (b.scott_continuous.monotone
      (Dinf.emb_approx_monotone a (le_max_left n m))) m

theorem Approx.getW_scottContinuous [CompletePartialOrder ρ] (a : ρ) :
    ScottContinuous (fun x : Approx ρ => x.getW t j a) := by
  intro d hne hdir c hc
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact Approx.getW_mono (hc.1 hx) a
  · intro u hu
    rcases hce : c with _ | ⟨t', v, w⟩
    · obtain ⟨x, hx⟩ := hne
      show (⊥ : ρ) ≤ u
      refine le_trans ?_ (hu ⟨x, hx, rfl⟩)
      have : x = Approx.bot := by
        have := hc.1 hx; rw [hce] at this; cases x
        · rfl
        · exact this.elim
      subst this; simp
    · by_cases ht : t' = t
      · subst ht; subst hce
        simp only [Approx.getW, Approx.get'_op]
        refine (Approx.isLUB_proj_w hdir hc j a).2 ?_
        rintro _ ⟨v', w', hm, rfl⟩
        simpa using hu ⟨_, hm, rfl⟩
      · obtain ⟨x, hx⟩ := hne
        simp only [Approx.getW, Approx.get'_op_of_ne ht]
        exact le_trans (OrderBot.bot_le (Approx.getW t j x a)) (hu ⟨x, hx, rfl⟩)

theorem Dinf.appAt_scottContinuous_f [Preorder E] {f : E → D∞} (hf : ScottContinuous f)
    (a : D∞) (n : Nat) : ScottContinuous fun e => Dinf.appAt t j (f e) a n :=
  ((hf.comp (Dinf.scottContinuous_approx (n + 1))).comp
    (Approx.getW_scottContinuous (a.approx n))).comp (Dinf.emb).scott_continuous

theorem Dinf.projW_scottContinuous_f [Preorder E] {f : E → D∞} (hf : ScottContinuous f)
    (a : D∞) : ScottContinuous fun e => Dinf.projW t j (f e) a := by
  apply ScottContinuous.sSup_range (g := fun n e => Dinf.appAt t j (f e) a n)
  · intro n; exact Dinf.appAt_scottContinuous_f hf a n
  · intro e p q hpq; exact Dinf.appAt_monotone t j (f e) a hpq

theorem Approx.getW_scottContinuous_arg [CompletePartialOrder ρ] (x : Approx ρ) :
    ScottContinuous (fun a : ρ => x.getW t j a) := by
  cases x
  case bot => simp [Approx.getW]
  case op t' v w =>
    by_cases ht : t' = t
    · subst ht
      simp only [Approx.getW, Approx.get'_op]
      exact (w.get j).scottContinuous
    · simp only [Approx.getW, Approx.get'_op_of_ne ht]; fun_prop

theorem Dinf.appAt_scottContinuous_a [Preorder E] (f : D∞) {a : E → D∞}
    (ha : ScottContinuous a) (n : Nat) :
    ScottContinuous fun e => Dinf.appAt t j f (a e) n :=
  ((ha.comp (Dinf.scottContinuous_approx n)).comp
    (Approx.getW_scottContinuous_arg (f.approx (n+1)))).comp (Dinf.emb).scott_continuous

theorem Dinf.projW_scottContinuous_a [Preorder E] (f : D∞) {a : E → D∞}
    (ha : ScottContinuous a) : ScottContinuous fun e => Dinf.projW t j f (a e) := by
  apply ScottContinuous.sSup_range (g := fun n e => Dinf.appAt t j f (a e) n)
  · intro n; exact Dinf.appAt_scottContinuous_a f ha n
  · intro e p q hpq; exact Dinf.appAt_monotone t j f (a e) hpq

@[fun_prop]
theorem Dinf.projW_scottContinuous [Preorder E] {f a : E → D∞}
    (hf : ScottContinuous f) (ha : ScottContinuous a) :
    ScottContinuous fun e => Dinf.projW t j (f e) (a e) := by
  apply ScottContinuous.sSup_range (g := fun n e => Dinf.appAt t j (f e) (a e) n)
  · intro n
    unfold Dinf.appAt
    refine ScottContinuous.comp ?_ (Dinf.emb).scott_continuous
    intro d hne hdir c hc
    constructor
    · rintro _ ⟨x, hx, rfl⟩
      exact le_trans (Approx.getW_mono ((hf.monotone (hc.1 hx)) (n+1)) _)
        (Approx.getW_mono_arg _ ((ha.monotone (hc.1 hx)) n))
    · intro u hu
      refine (Approx.getW_scottContinuous_arg (t := t) (j := j) ((f c).approx (n+1))
        (hne.image (fun e => (a e).approx n))
        (hdir.mono_comp (g := fun e => (a e).approx n) (fun _ _ h => (ha.monotone h) n))
        ((ha.comp (Dinf.scottContinuous_approx n)) hne hdir hc)).2 ?_
      rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      refine (Approx.getW_scottContinuous (t := t) (j := j) ((a x).approx n)
        (hne.image (fun e => (f e).approx (n+1)))
        (hdir.mono_comp (g := fun e => (f e).approx (n+1)) (fun _ _ h => (hf.monotone h) (n+1)))
        ((hf.comp (Dinf.scottContinuous_approx (n+1))) hne hdir hc)).2 ?_
      rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      obtain ⟨z, hz, hyz, hxz⟩ := hdir y hy x hx
      exact le_trans (le_trans (Approx.getW_mono ((hf.monotone hyz) (n+1)) _)
        (Approx.getW_mono_arg _ ((ha.monotone hxz) n))) (hu ⟨z, hz, rfl⟩)
  · intro e p q hpq; exact Dinf.appAt_monotone t j (f e) (a e) hpq

def Dinf.app : D∞ →ₛ D∞ →ₛ D∞ := by
  refine ƛₛ[?_] f ↦ ƛₛ[?_] a ↦ Dinf.projW .lam ⟨0, by simp⟩ f a
  · apply Dinf.projW_scottContinuous <;> fun_prop
  · apply ScottContinuousF.of_apply₂; intro a
    apply Dinf.projW_scottContinuous <;> fun_prop

@[simp] theorem Dinf.app_lam (b : D∞ →ₛ D∞) (a : D∞) : Dinf.app (Dinf.lam b) a = b a :=
  Dinf.projW_lam b a
