import SPos.Semantics.ValueDomain

open OmegaCompletePartialOrder

variable {D : Type u} [ScottDomain D Label]

namespace ScottDomain

/-- One layer of the decoding relation: decoding at level `k`, parameterized by the
(decoded) universes `U'` strictly below `k`. `DecodeAux k U' c X` reads: the code `c`
denotes the set of values `X`. -/
inductive DecodeAux (k : Nat) (U' : ∀ ℓ, ℓ < k → Set D) : D → Set D → Prop where
| univ {ℓ : Nat} (h : ℓ < k) : DecodeAux k U' (mkU ℓ) (U' ℓ h)
| pi {a : D} {A : Set D} {f : D →𝒄 D} {B : D → Set D} :
    DecodeAux k U' a A →
    (∀ d ∈ A, DecodeAux k U' (f d) (B d)) →
    DecodeAux k U' (mkPi a f) {g | ∀ d ∈ A, g •𝒄 d ∈ B d}

/-- Case analysis for `DecodeAux`, with the code kept as a variable so it can be
used against any concrete code via the discrimination lemmas. -/
theorem DecodeAux.inv {k : Nat} {U' : ∀ ℓ, ℓ < k → Set D} {c : D} {X : Set D}
    (h : DecodeAux k U' c X) :
    (∃ ℓ, ∃ hℓ : ℓ < k, c = mkU ℓ ∧ X = U' ℓ hℓ) ∨
    (∃ (a : D) (A : Set D) (f : D →𝒄 D) (B : D → Set D), c = mkPi a f ∧
      DecodeAux k U' a A ∧ (∀ d ∈ A, DecodeAux k U' (f d) (B d)) ∧
      X = {g | ∀ d ∈ A, g •𝒄 d ∈ B d}) := by
  cases h with
  | univ hℓ => exact .inl ⟨_, hℓ, rfl, rfl⟩
  | pi hA hB => exact .inr ⟨_, _, _, _, rfl, hA, hB, rfl⟩

/-- `Decode k c X`: at level `k`, the code `c` denotes the set of values `X`.
Universes below `k` are decoded by recursion on the level. -/
def Decode (k : Nat) : D → Set D → Prop :=
  DecodeAux k fun ℓ _ => {d | ∃ X, Decode ℓ d X}
termination_by k
decreasing_by assumption

/-- The universe at level `ℓ`: all codes that decode at level `ℓ`. -/
def U (ℓ : Nat) : Set D :=
  {d | ∃ X, Decode ℓ d X}

@[simp]
theorem mem_U {ℓ : Nat} {d : D} : d ∈ U ℓ ↔ ∃ X, Decode ℓ d X := Iff.rfl

theorem decode_iff {k : Nat} {c : D} {X : Set D} :
    Decode k c X ↔ DecodeAux k (fun ℓ _ => U ℓ) c X := by
  unfold Decode
  exact Iff.rfl

/-- Codes decode to at most one set — even across levels, since the level only
gates which universes may be formed. -/
private theorem DecodeAux.det {k : Nat} {c : D} {X : Set D}
    (h : DecodeAux k (fun ℓ _ => U ℓ) c X) :
    ∀ {k' : Nat} {Y : Set D}, DecodeAux k' (fun ℓ _ => U (D := D) ℓ) c Y → X = Y := by
  induction h with
  | univ hℓ =>
    intro k' Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, rfl⟩ | ⟨a, A, f, B, hc, -, -, -⟩
    · obtain rfl := mkU_inj hc
      rfl
    · exact absurd hc (mkU_ne_mkPi _ _ _)
  | pi hA hB ihA ihB =>
    intro k' Y h'
    rcases h'.inv with ⟨ℓ', hℓ', hc, rfl⟩ | ⟨a', A', f', B', hc, hA', hB', rfl⟩
    · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
    · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
      obtain rfl := ihA hA'
      ext g
      simp only [Set.mem_setOf_eq]
      exact ⟨fun hg d hd => ihB d hd (hB' d hd) ▸ hg d hd,
             fun hg d hd => (ihB d hd (hB' d hd)).symm ▸ hg d hd⟩

theorem Decode.univ {ℓ k : Nat} (h : ℓ < k) : Decode k (mkU ℓ : D) (U ℓ) :=
  decode_iff.mpr (.univ h)

theorem Decode.pi {k : Nat} {a : D} {A : Set D} {f : D →𝒄 D} {B : D → Set D}
    (hA : Decode k a A) (hB : ∀ d ∈ A, Decode k (f d) (B d)) :
    Decode k (Π̂ a f) {g | ∀ d ∈ A, g •𝒄 d ∈ B d} :=
  decode_iff.mpr (.pi (decode_iff.mp hA) fun d hd => decode_iff.mp (hB d hd))

theorem Decode.det {k k' : Nat} {c : D} {X Y : Set D}
    (h : Decode k c X) (h' : Decode k' c Y) : X = Y :=
  DecodeAux.det (decode_iff.mp h) (decode_iff.mp h')

/-- Cumulativity: decoding is preserved when going up in the universe hierarchy. -/
theorem Decode.cumul {k k' : Nat} {c : D} {X : Set D}
    (h : Decode k c X) (hk : k ≤ k') : Decode k' c X := by
  rw [decode_iff] at h ⊢
  induction h with
  | univ hℓ => exact .univ (hℓ.trans_le hk)
  | pi hA hB ihA ihB => exact .pi ihA ihB

theorem decode_univ_inv {k ℓ : Nat} {X : Set D}
    (h : Decode k (mkU ℓ : D) X) : ℓ < k ∧ X = U ℓ := by
  rcases (decode_iff.mp h).inv with ⟨ℓ', hℓ', hc, rfl⟩ | ⟨a, A, f, B, hc, -, -, -⟩
  · obtain rfl := mkU_inj hc
    exact ⟨hℓ', rfl⟩
  · exact absurd hc (mkU_ne_mkPi _ _ _)

theorem decode_pi_inv {k : Nat} {a : D} {f : D →𝒄 D} {X : Set D}
    (h : Decode k (Π̂ a f) X) :
    ∃ (A : Set D) (B : D → Set D), Decode k a A ∧ (∀ d ∈ A, Decode k (f d) (B d)) ∧
      X = {g | ∀ d ∈ A, g •𝒄 d ∈ B d} := by
  rcases (decode_iff.mp h).inv with ⟨ℓ, hℓ, hc, -⟩ | ⟨a', A, f', B, hc, hA, hB, rfl⟩
  · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
  · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
    exact ⟨A, B, decode_iff.mpr hA, fun d hd => decode_iff.mpr (hB d hd), rfl⟩

/-- `El ℓ c`: the set of values denoted by the code `c` at level `ℓ`
(empty if `c` does not decode). -/
def El (ℓ : Nat) (c : D) : Set D :=
  {x | ∃ X, Decode ℓ c X ∧ x ∈ X}

theorem El_eq_of_decode {ℓ : Nat} {c : D} {X : Set D} (h : Decode ℓ c X) :
    El ℓ c = X := by
  ext x
  exact ⟨fun ⟨X', hX', hx⟩ => hX'.det h ▸ hx, fun hx => ⟨X, h, hx⟩⟩

/-- A code in the universe decodes to its `El`. -/
theorem Decode.el {ℓ : Nat} {c : D} (h : c ∈ U ℓ) : Decode ℓ c (El ℓ c) := by
  obtain ⟨X, hX⟩ := h
  rw [El_eq_of_decode hX]
  exact hX

end ScottDomain
