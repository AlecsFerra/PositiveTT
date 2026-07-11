import SPos.Semantics.ValueDomain
import SPos.Semantics.PER

open OmegaCompletePartialOrder

variable {D : Type u} [ScottDomain D Label]

namespace ScottDomain

/-- One layer of the decoding relation. `DecodeAux k U' c c' X` reads: `c` and `c'`
are equal type-codes denoting the partial equivalence relation `X` on values;
`U'` gives the universes strictly below `k`. Working with pairs of codes is what
makes the denotations extensional: functions are related in a `Pi` type iff they
map related arguments to related results. -/
inductive DecodeAux (k : Nat) (U' : ∀ ℓ, ℓ < k → D → D → Prop) :
    D → D → (D → D → Prop) → Prop where
| univ {ℓ : Nat} (h : ℓ < k) : DecodeAux k U' (mkU ℓ) (mkU ℓ) (U' ℓ h)
| pi {a a' : D} {A : D → D → Prop} {f f' : D →𝒄 D} {B : D → D → D → Prop} :
    DecodeAux k U' a a' A →
    (∀ {d d' : D}, A d d' → DecodeAux k U' (f d) (f' d') (B d)) →
    DecodeAux k U' (Π̂ a f) (Π̂ a' f')
      (fun g g' => ∀ {d d' : D}, A d d' → B d (g •𝒄 d) (g' •𝒄 d'))

/-- Case analysis for `DecodeAux`, with the codes kept as variables so it can be
used against any concrete codes via the discrimination lemmas. -/
theorem DecodeAux.inv {k : Nat} {U' : ∀ ℓ, ℓ < k → D → D → Prop} {c c' : D}
    {X : D → D → Prop} (h : DecodeAux k U' c c' X) :
    (∃ ℓ, ∃ hℓ : ℓ < k, c = mkU ℓ ∧ c' = mkU ℓ ∧ X = U' ℓ hℓ) ∨
    (∃ (a a' : D) (A : D → D → Prop) (f f' : D →𝒄 D) (B : D → D → D → Prop),
      c = Π̂ a f ∧ c' = Π̂ a' f' ∧ DecodeAux k U' a a' A ∧
      (∀ {d d' : D}, A d d' → DecodeAux k U' (f d) (f' d') (B d)) ∧
      X = fun g g' => ∀ {d d' : D}, A d d' → B d (g •𝒄 d) (g' •𝒄 d')) := by
  cases h with
  | univ hℓ => exact .inl ⟨_, hℓ, rfl, rfl, rfl⟩
  | pi hA hB => exact .inr ⟨_, _, _, _, _, _, rfl, rfl, hA, hB, rfl⟩

/-- `Decode k c c' X`: at level `k`, `c` and `c'` are equal type-codes denoting the
PER `X`. Universes below `k` are decoded by recursion on the level. -/
def Decode (k : Nat) : D → D → (D → D → Prop) → Prop :=
  DecodeAux k fun ℓ _ => fun c c' => ∃ X, Decode ℓ c c' X
termination_by k
decreasing_by assumption

/-- The universe at level `ℓ`, itself a PER on codes: two codes are related iff
they decode (at level `ℓ`) to a common PER. -/
def U (ℓ : Nat) : D → D → Prop :=
  fun c c' => ∃ X, Decode ℓ c c' X

@[simp]
theorem mem_U {ℓ : Nat} {c c' : D} : U ℓ c c' ↔ ∃ X, Decode ℓ c c' X := Iff.rfl

theorem decode_iff {k : Nat} {c c' : D} {X : D → D → Prop} :
    Decode k c c' X ↔ DecodeAux k (fun ℓ _ => U ℓ) c c' X := by
  unfold Decode
  exact Iff.rfl

/-- Left determinism: a code decodes to at most one PER, whatever it is paired
with and at whatever level. -/
private theorem DecodeAux.detL {k : Nat} {c c₁ : D} {X : D → D → Prop}
    (h : DecodeAux k (fun ℓ _ => U ℓ) c c₁ X) :
    ∀ {k' : Nat} {c₂ : D} {Y : D → D → Prop},
      DecodeAux k' (fun ℓ _ => U (D := D) ℓ) c c₂ Y → X = Y := by
  induction h with
  | univ hℓ =>
    intro k' c₂ Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, -, rfl⟩ | ⟨a, a', A, f, f', B, hc, -, -, -, -⟩
    · obtain rfl := mkU_inj hc
      rfl
    · exact absurd hc (mkU_ne_mkPi _ _ _)
  | pi hA hB ihA ihB =>
    intro k' c₂ Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, -, -⟩ | ⟨a1, a2, A1, g1, g2, B1, hc, -, hA1, hB1, rfl⟩
    · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
    · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
      obtain rfl := ihA hA1
      funext g g'
      apply propext
      constructor
      · intro hg d d' hdd'
        exact ihB hdd' (hB1 hdd') ▸ hg hdd'
      · intro hg d d' hdd'
        exact (ihB hdd' (hB1 hdd')).symm ▸ hg hdd'

/-- Right determinism. -/
private theorem DecodeAux.detR {k : Nat} {c₁ c : D} {X : D → D → Prop}
    (h : DecodeAux k (fun ℓ _ => U ℓ) c₁ c X) :
    ∀ {k' : Nat} {c₂ : D} {Y : D → D → Prop},
      DecodeAux k' (fun ℓ _ => U (D := D) ℓ) c₂ c Y → X = Y := by
  induction h with
  | univ hℓ =>
    intro k' c₂ Y h'
    rcases h'.inv with ⟨ℓ', hℓ', -, hc, rfl⟩ | ⟨a, a', A, f, f', B, -, hc, -, -, -⟩
    · obtain rfl := mkU_inj hc
      rfl
    · exact absurd hc (mkU_ne_mkPi _ _ _)
  | pi hA hB ihA ihB =>
    intro k' c₂ Y h'
    rcases h'.inv with ⟨ℓ', hℓ', -, hc, -⟩ | ⟨a1, a2, A1, g1, g2, B1, -, hc, hA1, hB1, rfl⟩
    · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
    · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
      obtain rfl := ihA hA1
      funext g g'
      apply propext
      constructor
      · intro hg d d' hdd'
        exact ihB hdd' (hB1 hdd') ▸ hg hdd'
      · intro hg d d' hdd'
        exact (ihB hdd' (hB1 hdd')).symm ▸ hg hdd'

theorem Decode.det {k k' : Nat} {c c₁ c₂ : D} {X Y : D → D → Prop}
    (h : Decode k c c₁ X) (h' : Decode k' c c₂ Y) : X = Y :=
  DecodeAux.detL (decode_iff.mp h) (decode_iff.mp h')

theorem Decode.det_right {k k' : Nat} {c₁ c₂ c : D} {X Y : D → D → Prop}
    (h : Decode k c₁ c X) (h' : Decode k' c₂ c Y) : X = Y :=
  DecodeAux.detR (decode_iff.mp h) (decode_iff.mp h')

/-- The combined metatheory of `Decode`, proved by recursion on the level and
induction on derivations: the judgment is symmetric, composable on the left,
and the denoted relation is a PER. -/
private theorem DecodeAux.package {k : Nat} {c c' : D} {X : D → D → Prop}
    (h : DecodeAux k (fun ℓ _ => U ℓ) c c' X) :
    DecodeAux k (fun ℓ _ => U (D := D) ℓ) c' c X ∧
    (∀ {c'' : D} {Y : D → D → Prop},
      DecodeAux k (fun ℓ _ => U ℓ) c' c'' Y → DecodeAux k (fun ℓ _ => U ℓ) c c'' X) ∧
    IsPER X := by
  induction h with
  | univ hℓ =>
    refine ⟨.univ hℓ, ?_, ?_⟩
    · intro c'' Y h'
      rcases h'.inv with ⟨ℓ', hℓ', hc, rfl, rfl⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩
      · obtain rfl := mkU_inj hc
        exact .univ hℓ
      · exact absurd hc (mkU_ne_mkPi _ _ _)
    · constructor
      · rintro x y ⟨X, hX⟩
        exact ⟨X, decode_iff.mpr (DecodeAux.package (decode_iff.mp hX)).1⟩
      · rintro x y z ⟨X, hX⟩ ⟨Y, hY⟩
        exact ⟨X, decode_iff.mpr
          ((DecodeAux.package (decode_iff.mp hX)).2.1 (decode_iff.mp hY))⟩
  | @pi a a' A f f' B hA hB ihA ihB =>
    obtain ⟨symA, transA, perA⟩ := ihA
    have reflA : ∀ {d d' : D}, A d d' → A d d := fun h => perA.trans h (perA.symm h)
    have coh : ∀ {d d' : D}, A d d' → B d = B d' := fun {d d'} h =>
      DecodeAux.detR (hB (reflA h)) (hB (perA.symm h))
    refine ⟨.pi symA ?_, ?_, ?_⟩
    · intro d d' hdd'
      exact (coh hdd').symm ▸ (ihB (perA.symm hdd')).1
    · intro c'' Y h'
      rcases h'.inv with ⟨ℓ', hℓ', hc, -, -⟩ | ⟨a1, a2, A1, g1, g2, B1, hc, rfl, hA1, hB1, rfl⟩
      · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
      · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
        obtain rfl := DecodeAux.detL hA1 symA
        refine .pi (transA hA1) ?_
        intro d d' hdd'
        exact (ihB (reflA hdd')).2.1 (hB1 hdd')
    · constructor
      · intro g g' hgg' d d' hdd'
        have h1 := hgg' (perA.symm hdd')
        have h2 := ((ihB (perA.symm hdd')).2.2).symm h1
        exact (coh hdd').symm ▸ h2
      · intro g g' g'' h1 h2 d d' hdd'
        have e1 := h1 (reflA hdd')
        have e2 := h2 hdd'
        exact ((ihB hdd').2.2).trans e1 e2
termination_by k
decreasing_by all_goals assumption

theorem Decode.symm {k : Nat} {c c' : D} {X : D → D → Prop}
    (h : Decode k c c' X) : Decode k c' c X :=
  decode_iff.mpr (DecodeAux.package (decode_iff.mp h)).1

theorem Decode.trans {k : Nat} {c c' c'' : D} {X Y : D → D → Prop}
    (h : Decode k c c' X) (h' : Decode k c' c'' Y) : Decode k c c'' X :=
  decode_iff.mpr ((DecodeAux.package (decode_iff.mp h)).2.1 (decode_iff.mp h'))

/-- The relation denoted by a type-code is a partial equivalence relation. -/
theorem Decode.isPER {k : Nat} {c c' : D} {X : D → D → Prop}
    (h : Decode k c c' X) : IsPER X :=
  (DecodeAux.package (decode_iff.mp h)).2.2

theorem Decode.refl_left {k : Nat} {c c' : D} {X : D → D → Prop}
    (h : Decode k c c' X) : Decode k c c X :=
  h.trans h.symm

theorem Decode.univ {ℓ k : Nat} (h : ℓ < k) : Decode k (mkU ℓ : D) (mkU ℓ) (U ℓ) :=
  decode_iff.mpr (.univ h)

theorem Decode.pi {k : Nat} {a a' : D} {A : D → D → Prop} {f f' : D →𝒄 D}
    {B : D → D → D → Prop} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D}, A d d' → Decode k (f d) (f' d') (B d)) :
    Decode k (Π̂ a f) (Π̂ a' f')
      (fun g g' => ∀ {d d' : D}, A d d' → B d (g •𝒄 d) (g' •𝒄 d')) :=
  decode_iff.mpr (.pi (decode_iff.mp hA) fun hdd' => decode_iff.mp (hB hdd'))

/-- Cumulativity: decoding is preserved when going up in the universe hierarchy. -/
theorem Decode.cumul {k k' : Nat} {c c' : D} {X : D → D → Prop}
    (h : Decode k c c' X) (hk : k ≤ k') : Decode k' c c' X := by
  rw [decode_iff] at h ⊢
  induction h with
  | univ hℓ => exact .univ (hℓ.trans_le hk)
  | pi hA hB ihA ihB => exact .pi ihA fun {d d'} hdd' => ihB hdd'

theorem decode_univ_inv {k ℓ : Nat} {c' : D} {X : D → D → Prop}
    (h : Decode k (mkU ℓ : D) c' X) : ℓ < k ∧ c' = mkU ℓ ∧ X = U ℓ := by
  rcases (decode_iff.mp h).inv with ⟨ℓ', hℓ', hc, rfl, rfl⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩
  · obtain rfl := mkU_inj hc
    exact ⟨hℓ', rfl, rfl⟩
  · exact absurd hc (mkU_ne_mkPi _ _ _)

theorem decode_pi_inv {k : Nat} {a : D} {f : D →𝒄 D} {c' : D} {X : D → D → Prop}
    (h : Decode k (Π̂ a f) c' X) :
    ∃ (a' : D) (f' : D →𝒄 D) (A : D → D → Prop) (B : D → D → D → Prop),
      c' = Π̂ a' f' ∧ Decode k a a' A ∧
      (∀ {d d' : D}, A d d' → Decode k (f d) (f' d') (B d)) ∧
      X = fun g g' => ∀ {d d' : D}, A d d' → B d (g •𝒄 d) (g' •𝒄 d') := by
  rcases (decode_iff.mp h).inv with ⟨ℓ, hℓ, hc, -, -⟩ | ⟨a1, a2, A, g1, g2, B, hc, rfl, hA, hB, rfl⟩
  · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
  · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
    exact ⟨a2, g2, A, B, rfl, decode_iff.mpr hA,
      fun {d d'} hdd' => decode_iff.mpr (hB hdd'), rfl⟩

/-- `El ℓ c`: the PER denoted by the code `c` at level `ℓ`
(empty if `c` does not decode). -/
def El (ℓ : Nat) (c : D) : D → D → Prop :=
  fun x y => ∃ X, Decode ℓ c c X ∧ X x y

theorem El_eq_of_decode {ℓ : Nat} {c c' : D} {X : D → D → Prop}
    (h : Decode ℓ c c' X) : El ℓ c = X := by
  funext x y
  apply propext
  exact ⟨fun ⟨X', hX', hx⟩ => hX'.det h.refl_left ▸ hx, fun hx => ⟨X, h.refl_left, hx⟩⟩

/-- Related codes in the universe decode to the `El` of the left one. -/
theorem Decode.el {ℓ : Nat} {c c' : D} (h : U ℓ c c') : Decode ℓ c c' (El ℓ c) := by
  obtain ⟨X, hX⟩ := h
  rw [El_eq_of_decode hX]
  exact hX

end ScottDomain
