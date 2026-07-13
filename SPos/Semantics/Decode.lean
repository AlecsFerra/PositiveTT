import SPos.Semantics.ValueDomain
import SPos.Structure.PER
import SPos.Semantics.Type

open OmegaCompletePartialOrder ScottDomain

variable {D : Type u} [ScottDomain D Label]

inductive DecodeAux (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D) : D → D → PER D → Prop where
| univ (h : ℓ < k) : DecodeAux k U' (mkU ℓ) (mkU ℓ) (U' ℓ h)
| pi : DecodeAux k U' a a' A →
        (∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d)) →
        DecodeAux k U' (Π̂ a f) (Π̂ a' f') (PER.pi A B)

-- Forded Decode
inductive DecodeAux.Inv (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D) (c c' : D) (X : PER D) : Prop where
| univ (hℓ : ℓ < k) (_ : c = mkU ℓ) (_ : c' = mkU ℓ)
           (_ : X = U' ℓ hℓ)
| pi
    (_ : c = Π̂ a f) (_ : c' = Π̂ a' f')
    (_ : DecodeAux k U' a a' A)
    (_ : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d))
    (_ : X = PER.pi A B)

theorem DecodeAux.inv {X : PER D} (h : DecodeAux k U' c c' X)
  : DecodeAux.Inv k U' c c' X := by cases h with
  | univ hℓ  => apply DecodeAux.Inv.univ <;> (try assumption) <;> simp
  | pi hA hB => apply DecodeAux.Inv.pi   <;> (try assumption) <;> simp

private theorem DecodeAux.det {U₁ : ∀ ℓ, ℓ < ℓ₁ → PER D} {U₂ : ∀ ℓ, ℓ < ℓ₂ → PER D}
  (_ : ∀ ℓ (hk₁ : ℓ < ℓ₁) (hk₂ : ℓ < ℓ₂), U₁ ℓ hk₁ = U₂ ℓ hk₂)
  (h₁ : DecodeAux ℓ₁ U₁ c c₁ X) (h₂ : DecodeAux ℓ₂ U₂ c c₂ Y)
  : X = Y := by induction h₁ generalizing c₂ Y with
  | univ =>
    rcases h₂.inv with ⟨_, hc⟩ | hc
    · obtain rfl := mkU_inj hc; simp_all
    · apply absurd hc; apply mkU_ne_mkPi
  | pi _ _ ihA ihB =>
    rcases h₂.inv with ⟨_, hc⟩ | ⟨hc, -, hA1, hB1, rfl⟩
    · apply absurd hc.symm; apply mkU_ne_mkPi
    · rcases mkPi_inj hc with ⟨rfl, rfl⟩; rcases ihA hA1
      apply PER.ext; funext; apply propext
      constructor
      · intro hg _ _ hxy; rw [← ihB hxy (hB1 hxy)]; apply hg; assumption
      · intro hg _ _ hxy; rw [  ihB hxy (hB1 hxy)]; apply hg; assumption


private theorem DecodeAux.symm {X : PER D}
  (h : DecodeAux k U' c c' X) : DecodeAux k U' c' c X := by
  induction h with
  | univ hℓ => exact .univ hℓ
  | pi _ _ _ ihB =>
    constructor; assumption
    intro _ _ hd
    rw [PERResp.eq_of_rel _ hd]
    exact ihB (PER.symm _ hd)

private theorem DecodeAux.trans {X : PER D} {Y : PER D}
  (h₁ : DecodeAux k U' c c' X) (h₂ : DecodeAux k U' c' c'' Y)
  : DecodeAux k U' c c'' X := by
  induction h₁ generalizing c'' Y with
  | univ hℓ =>
    rcases h₂.inv with ⟨-, hc, rfl, rfl⟩ | ⟨hc, -, -, -, -⟩
    · obtain rfl := mkU_inj hc
      exact .univ hℓ
    · exact absurd hc (mkU_ne_mkPi _ _ _)
  | pi hA hB ihA ihB =>
    rcases h₂.inv with ⟨_, hc, _, _⟩ | ⟨hc, rfl, hA1, hB1, rfl⟩
    · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
    · rcases mkPi_inj hc with ⟨rfl, rfl⟩
      obtain rfl := DecodeAux.det (by simp) hA.symm hA1
      refine .pi (ihA hA1) ?_
      intro _ _ hdd; exact ihB (PER.refl_left _ hdd) (hB1 hdd)


def U (k : Nat) : PER D where
  rel c c' := ∃ X : PER D, DecodeAux k (fun ℓ _ => U ℓ) c c' X
  sym := ⟨ fun _ _ h =>
    h.elim fun X hX => ⟨X, DecodeAux.symm hX⟩
  ⟩
  tra := ⟨ fun _ _ _ h h' =>
    h.elim fun X hX => h'.elim fun _ hY => ⟨X, DecodeAux.trans hX hY⟩
  ⟩

@[simp]
def Decode (k : Nat) (c c' : D) (X : PER D) : Prop :=
  DecodeAux k (fun ℓ _ => U ℓ) c c' X

theorem Decode.symm {X : PER D} (h : Decode k c c' X) : Decode k c' c X :=
  DecodeAux.symm h

theorem Decode.trans  {X Y : PER D} (h : Decode k c c' X) (h' : Decode k c' c'' Y)
  : Decode k c c'' X := DecodeAux.trans h h'

theorem Decode.refl_left {X : PER D} (h : Decode k c c' X) : Decode k c c X :=
  h.trans h.symm

theorem Decode.det {X Y : PER D} (h : Decode ℓ₁ c c₁ X) (h' : Decode ℓ₂ c c₂ Y) : X = Y :=
  DecodeAux.det (by simp) h h'

@[simp]
theorem mem_U : (c ~ c' ∈ₚ U ℓ) ↔ ∃ X : PER D, Decode ℓ c c' X := by
  unfold U Decode; exact Iff.rfl

theorem Decode.univ (h : ℓ < k) : Decode k (mkU ℓ : D) (mkU ℓ) (U ℓ) := by
  simp ; exact (.univ h)

theorem Decode.pi {A : PER D}
    {B : A →ₚ PER.diag (PER D)} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) :
    Decode k (Π̂ a f) (Π̂ a' f') (PER.pi A B) := by
  simp; exact .pi  hA (fun hdd' => hB hdd')

theorem Decode.cumul {X : PER D} (h : Decode k c c' X) (hk : k ≤ k')
  : Decode k' c c' X := by simp; induction h with
  | univ hℓ => exact .univ (hℓ.trans_le hk)
  | pi hA hB ihA ihB => exact .pi ihA fun hdd' => ihB hdd'
inductive Decode.Inv (k : Nat) (c c' : D) (X : PER D) : Prop where
| univ (hℓ : ℓ < k) (hc : c = mkU ℓ) (hc' : c' = mkU ℓ) (hX : X = U ℓ)
| pi (hc : c = Π̂ a f) (hc' : c' = Π̂ a' f')
    (dom : Decode k a a' A)
    (cod : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (hX : X = PER.pi A B)

theorem Decode.inv {k : Nat} {c c' : D} {X : PER D}
    (h : Decode k c c' X) : Decode.Inv k c c' X := by
  simp at *
  rcases h.inv with ⟨hℓ, hc, hc', rfl⟩ | ⟨hc, hc', hA, hB, rfl⟩
  · constructor <;> (try assumption); simp
  · exact .pi hc hc' hA (fun hdd' => hB hdd') rfl

inductive Decode.UnivInv (k ℓ : Nat) (c' : D) (X : PER D) : Prop where
| mk (lt : ℓ < k) (code : c' = mkU ℓ) (per : X = U ℓ)

theorem decode_univ_inv {k ℓ : Nat} {c' : D} {X : PER D}
    (h : Decode k (mkU ℓ : D) c' X) : Decode.UnivInv k ℓ c' X := by
  rcases h.inv with ⟨hℓ, hc, rfl, rfl⟩ | ⟨hc, -, -, -, -⟩
  · obtain rfl := mkU_inj hc; constructor <;> (try assumption); simp
  · exact absurd hc (mkU_ne_mkPi _ _ _)

inductive Decode.PiInv (k : Nat) (a : D) (f : D →𝒄 D) (c' : D) (X : PER D) : Prop where
| mk (a' : D) (f' : D →𝒄 D) (A : PER D) (B : A →ₚ PER.diag (PER D))
    (code : c' = Π̂ a' f')
    (dom  : Decode k a a' A)
    (cod  : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (per  : X = PER.pi A B)

theorem decode_pi_inv {k : Nat} {a : D} {f : D →𝒄 D} {c' : D} {X : PER D}
    (h : Decode k (Π̂ a f) c' X) : Decode.PiInv k a f c' X := by
  rcases h.inv with ⟨-, hc, -, -⟩ | ⟨hc, rfl, hA, hB, rfl⟩
  · exact absurd hc.symm (mkU_ne_mkPi _ _ _)
  · obtain ⟨rfl, rfl⟩ := mkPi_inj hc
    constructor <;> (try assumption); rfl; simp

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
  obtain ⟨X, hX⟩ := mem_U.mp h
  rw [El_eq_of_decode hX]
  exact hX

/-- `El` doesn't depend on which level witnesses a given pair's relatedness. -/
theorem El.det {c x y : D} (h₁ : x ~ y ∈ₚ El ℓ₁ c) (h₂ : x ~ y ∈ₚ El ℓ₂ c) :
    El ℓ₁ c = El ℓ₂ c := by
  obtain ⟨X, hX, _⟩ := h₁
  obtain ⟨Y, hY, _⟩ := h₂
  rw [El_eq_of_decode hX, El_eq_of_decode hY, Decode.det hX hY]
