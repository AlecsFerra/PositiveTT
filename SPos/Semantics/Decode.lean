import SPos.Semantics.ValueDomain
import SPos.Semantics.PER
import SPos.Semantics.Type

open OmegaCompletePartialOrder

variable {D : Type u} [ScottDomain D Label]

namespace ScottDomain

/-- One layer of the decoding relation. `DecodeAux k U' c c' X` reads: `c` and `c'`
are equal type-codes denoting the partial equivalence relation `X` on values;
`U'` gives the universes strictly below `k`.

The judgment is on *pairs* of codes: this is what lets the fundamental theorem
relate a type's denotations in two different environments, which the `app` case
needs. Codomain families of `Pi` codes are PER-respecting maps
(`A →ₚ PER.diag (PER D)`), so every denoted relation is a PER by construction. -/
inductive DecodeAux (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D) : D → D → PER D → Prop where
| univ {ℓ : Nat} (h : ℓ < k) : DecodeAux k U' (mkU ℓ) (mkU ℓ) (U' ℓ h)
| pi {a a' : D} {A : PER D} {f f' : D →𝒄 D} {B : A →ₚ PER.diag (PER D)} :
    DecodeAux k U' a a' A →
    (∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d)) →
    DecodeAux k U' (Π̂ a f) (Π̂ a' f') (PER.pi A B)

/-- Case analysis for `DecodeAux`, with the codes kept as variables so it can be
used against any concrete codes via the discrimination lemmas. -/
theorem DecodeAux.inv {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D} {c c' : D}
    {X : PER D} (h : DecodeAux k U' c c' X) :
    (∃ ℓ, ∃ hℓ : ℓ < k, c = mkU ℓ ∧ c' = mkU ℓ ∧ X = U' ℓ hℓ) ∨
    (∃ (a a' : D) (A : PER D) (f f' : D →𝒄 D) (B : A →ₚ PER.diag (PER D)),
      c = Π̂ a f ∧ c' = Π̂ a' f' ∧ DecodeAux k U' a a' A ∧
      (∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d)) ∧
      X = PER.pi A B) := by
  cases h with
  | univ hℓ => exact .inl ⟨_, hℓ, rfl, rfl, rfl⟩
  | pi hA hB => exact .inr ⟨_, _, _, _, _, _, rfl, rfl, hA, hB, rfl⟩

/-- Determinism: a (left) code decodes to at most one PER, whatever it is paired
with, at any level, and for any compatible families of lower universes. -/
private theorem DecodeAux.det' {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D} {c c₁ : D}
    {X : PER D} (h : DecodeAux k U' c c₁ X) :
    ∀ {k' : Nat} {U'' : ∀ ℓ, ℓ < k' → PER D}
      (_ : ∀ ℓ (hk : ℓ < k) (hk' : ℓ < k'), U' ℓ hk = U'' ℓ hk')
      {c₂ : D} {Y : PER D}, DecodeAux k' U'' c c₂ Y → X = Y := by
  induction h with
  | univ hℓ =>
    intro k' U'' hU c₂ Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, -, rfl⟩ | ⟨a, a', A, f, f', B, hc, -, -, -, -⟩
    · obtain rfl := mkU_inj hc
      exact hU _ hℓ hℓ'
    · exact absurd hc (mkU_ne_mkPi _ _ _)
  | @pi a a' A f f' B hA hB ihA ihB =>
    intro k' U'' hU c₂ Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, -, -⟩ | ⟨a1, a2, A1, g1, g2, B1, hc, -, hA1, hB1, rfl⟩
    · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
    · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
      obtain rfl := ihA hU hA1
      apply PER.ext
      funext g g'
      apply propext
      constructor
      · intro hg x y hxy
        exact ihB hxy hU (hB1 hxy) ▸ hg x y hxy
      · intro hg x y hxy
        exact (ihB hxy hU (hB1 hxy)).symm ▸ hg x y hxy

/-- Symmetry and left-composition of decoding for a fixed layer, proved
simultaneously. Coherence of the codomain family is its `respRelation` field. -/
private theorem DecodeAux.package {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D} {c c' : D}
    {X : PER D} (h : DecodeAux k U' c c' X) :
    DecodeAux k U' c' c X ∧
    (∀ {c'' : D} {Y : PER D}, DecodeAux k U' c' c'' Y → DecodeAux k U' c c'' X) := by
  induction h with
  | univ hℓ =>
    refine ⟨.univ hℓ, ?_⟩
    intro c'' Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, rfl, rfl⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩
    · obtain rfl := mkU_inj hc
      exact .univ hℓ
    · exact absurd hc (mkU_ne_mkPi _ _ _)
  | @pi a a' A f f' B hA hB ihA ihB =>
    obtain ⟨symA, compA⟩ := ihA
    refine ⟨.pi symA ?_, ?_⟩
    · intro d d' hdd'
      exact (B.eq_of_rel hdd').symm ▸ (ihB (A.symm hdd')).1
    · intro c'' Y h'
      rcases h'.inv with ⟨ℓ', hℓ', hc, -, -⟩ | ⟨a1, a2, A1, g1, g2, B1, hc, rfl, hA1, hB1, rfl⟩
      · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
      · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
        obtain rfl := DecodeAux.det' symA (fun _ _ _ => rfl) hA1
        refine .pi (compA hA1) ?_
        intro d d' hdd'
        exact (ihB (A.refl_left hdd')).2 (hB1 hdd')

/-- The decoding relation together with its symmetry and composition properties,
tied through the universe hierarchy by recursion on the level: the universe below
is a PER *because* decoding below is symmetric and composable. -/
private def DecodePkg : (k : Nat) → { Dec : D → D → PER D → Prop //
    (∀ {c c' : D} {X : PER D}, Dec c c' X → Dec c' c X) ∧
    (∀ {c c' c'' : D} {X Y : PER D}, Dec c c' X → Dec c' c'' Y → Dec c c'' X) }
  | k =>
    ⟨DecodeAux k (fun ℓ _ =>
      { rel := fun c c' => ∃ X : PER D, (DecodePkg ℓ).1 c c' X
        sym := ⟨fun _ _ h => h.elim fun X hX => ⟨X, (DecodePkg ℓ).2.1 hX⟩⟩
        tra := ⟨fun _ _ _ h h' => h.elim fun X hX =>
          h'.elim fun _ hY => ⟨X, (DecodePkg ℓ).2.2 hX hY⟩⟩ }),
     fun {_ _ _} h => (DecodeAux.package h).1,
     fun {_ _ _ _ _} h h' => (DecodeAux.package h).2 h'⟩
termination_by k => k
decreasing_by all_goals assumption

/-- `Decode k c c' X`: at level `k`, `c` and `c'` are equal type-codes denoting the
PER `X`. -/
def Decode (k : Nat) : D → D → PER D → Prop :=
  (DecodePkg k).1

theorem Decode.symm {k : Nat} {c c' : D} {X : PER D}
    (h : Decode k c c' X) : Decode k c' c X :=
  (DecodePkg k).2.1 h

theorem Decode.trans {k : Nat} {c c' c'' : D} {X Y : PER D}
    (h : Decode k c c' X) (h' : Decode k c' c'' Y) : Decode k c c'' X :=
  (DecodePkg k).2.2 h h'

theorem Decode.refl_left {k : Nat} {c c' : D} {X : PER D}
    (h : Decode k c c' X) : Decode k c c X :=
  h.trans h.symm

/-- The universe at level `ℓ`, itself a PER on codes: two codes are related iff
they decode (at level `ℓ`) to a common PER. -/
def U (ℓ : Nat) : PER D where
  rel c c' := ∃ X : PER D, Decode ℓ c c' X
  sym := ⟨fun _ _ ⟨X, hX⟩ => ⟨X, hX.symm⟩⟩
  tra := ⟨fun _ _ _ ⟨X, hX⟩ ⟨_, hY⟩ => ⟨X, hX.trans hY⟩⟩

@[simp]
theorem mem_U {ℓ : Nat} {c c' : D} : (c ~ c' ∈ₚ U ℓ) ↔ ∃ X : PER D, Decode ℓ c c' X :=
  Iff.rfl

theorem decode_iff {k : Nat} {c c' : D} {X : PER D} :
    Decode k c c' X ↔ DecodeAux k (fun ℓ _ => U ℓ) c c' X := by
  unfold Decode
  rw [DecodePkg]
  exact Iff.rfl

theorem Decode.det {k k' : Nat} {c c₁ c₂ : D} {X Y : PER D}
    (h : Decode k c c₁ X) (h' : Decode k' c c₂ Y) : X = Y :=
  DecodeAux.det' (decode_iff.mp h) (fun _ _ _ => rfl) (decode_iff.mp h')

theorem Decode.univ {ℓ k : Nat} (h : ℓ < k) : Decode k (mkU ℓ : D) (mkU ℓ) (U ℓ) :=
  decode_iff.mpr (.univ h)

theorem Decode.pi {k : Nat} {a a' : D} {A : PER D} {f f' : D →𝒄 D}
    {B : A →ₚ PER.diag (PER D)} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) :
    Decode k (Π̂ a f) (Π̂ a' f') (PER.pi A B) :=
  decode_iff.mpr (.pi (decode_iff.mp hA) fun hdd' => decode_iff.mp (hB hdd'))

/-- Cumulativity: decoding is preserved when going up in the universe hierarchy. -/
theorem Decode.cumul {k k' : Nat} {c c' : D} {X : PER D}
    (h : Decode k c c' X) (hk : k ≤ k') : Decode k' c c' X := by
  rw [decode_iff] at h ⊢
  induction h with
  | univ hℓ => exact .univ (hℓ.trans_le hk)
  | pi hA hB ihA ihB => exact .pi ihA fun hdd' => ihB hdd'

theorem decode_univ_inv {k ℓ : Nat} {c' : D} {X : PER D}
    (h : Decode k (mkU ℓ : D) c' X) : ℓ < k ∧ c' = mkU ℓ ∧ X = U ℓ := by
  rcases (decode_iff.mp h).inv with ⟨ℓ', hℓ', hc, rfl, rfl⟩ | ⟨_, _, _, _, _, _, hc, _, _, _, _⟩
  · obtain rfl := mkU_inj hc
    exact ⟨hℓ', rfl, rfl⟩
  · exact absurd hc (mkU_ne_mkPi _ _ _)

theorem decode_pi_inv {k : Nat} {a : D} {f : D →𝒄 D} {c' : D} {X : PER D}
    (h : Decode k (Π̂ a f) c' X) :
    ∃ (a' : D) (f' : D →𝒄 D) (A : PER D) (B : A →ₚ PER.diag (PER D)),
      c' = Π̂ a' f' ∧ Decode k a a' A ∧
      (∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) ∧
      X = PER.pi A B := by
  rcases (decode_iff.mp h).inv with ⟨ℓ, hℓ, hc, -, -⟩ | ⟨a1, a2, A, g1, g2, B, hc, rfl, hA, hB, rfl⟩
  · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
  · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
    exact ⟨a2, g2, A, B, rfl, decode_iff.mpr hA,
      fun hdd' => decode_iff.mpr (hB hdd'), rfl⟩

/-- `El ℓ c`: the PER denoted by the code `c` at level `ℓ`
(empty if `c` does not decode). -/
def El (ℓ : Nat) (c : D) : PER D where
  rel x y := ∃ X : PER D, Decode ℓ c c X ∧ (x ~ y ∈ₚ X)
  sym := ⟨fun _ _ ⟨X, hX, hxy⟩ => ⟨X, hX, X.symm hxy⟩⟩
  tra := ⟨fun _ _ _ ⟨X, hX, h1⟩ ⟨_, hY, h2⟩ => ⟨X, hX, X.trans h1 (Decode.det hY hX ▸ h2)⟩⟩

theorem El_eq_of_decode {ℓ : Nat} {c c' : D} {X : PER D}
    (h : Decode ℓ c c' X) : El ℓ c = X := by
  apply PER.ext
  funext x y
  apply propext
  exact ⟨fun ⟨X', hX', hxy⟩ => hX'.det h.refl_left ▸ hxy, fun hxy => ⟨X, h.refl_left, hxy⟩⟩

/-- Related codes in the universe decode to the `El` of the left one. -/
theorem Decode.el {ℓ : Nat} {c c' : D} (h : c ~ c' ∈ₚ U ℓ) : Decode ℓ c c' (El ℓ c) := by
  obtain ⟨X, hX⟩ := h
  rw [El_eq_of_decode hX]
  exact hX

end ScottDomain
