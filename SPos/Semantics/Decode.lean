import SPos.Semantics.ValueDomain
import SPos.Structure.PER
import SPos.Semantics.Type

open OmegaCompletePartialOrder ScottDomain

variable {D : Type u} [ScottDomain D Label]

abbrev DecodeEnv (D : Type u) (m : Nat) : Type u :=
  Fin m → PER D

def DecodeEnv.empty : DecodeEnv D 0 := Fin.elim0

def DecodeEnv.snoc (ρ : DecodeEnv D m) (X : PER D) : DecodeEnv D (m + 1) :=
  Fin.lastCases X ρ

omit [ScottDomain D Label] in
@[simp]
theorem DecodeEnv.snoc_last (ρ : DecodeEnv D m) (X : PER D) :
    ρ.snoc X (Fin.last m) = X := by
  simp [DecodeEnv.snoc]

omit [ScottDomain D Label] in
@[simp]
theorem DecodeEnv.snoc_castSucc (ρ : DecodeEnv D m) (X : PER D) (i : Fin m) :
    ρ.snoc X i.castSucc = ρ i := by
  simp [DecodeEnv.snoc]

inductive DecodeAux (k : Nat)
    (U' : ∀ ℓ, ℓ < k → ∀ m', DecodeEnv D m' → PER D) :
    {m : Nat} → DecodeEnv D m → D → D → PER D → Prop where
| univ (h : ℓ < k) {ρ : DecodeEnv D m} :
    DecodeAux k U' ρ (mkU ℓ) (mkU ℓ) (U' ℓ h m ρ)
| pi : DecodeAux k U' ρ a a' A
    → (∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' ρ (f d) (f' d') (B d))
    → DecodeAux k U' ρ (Π̂ a f) (Π̂ a' f') (PER.pi A B)
| sigma : DecodeAux k U' ρ a a' A
       → (∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' ρ (f d) (f' d') (B d))
       → DecodeAux k U' ρ (Σ̂ a f) (Σ̂ a' f') (PER.sigma A B)
| bool : DecodeAux k U' ρ mkBool mkBool PER.bool
| id : DecodeAux k U' ρ t t' A → (a ~ a' ∈ₚ A) → (b ~ b' ∈ₚ A) →
        DecodeAux k U' ρ (Îd t a b) (Îd t' a' b') (PER.id A a b)
| muvar (h : i < m) {ρ : DecodeEnv D m} :
    DecodeAux k U' ρ (mkMuVar i) (mkMuVar i) (ρ ⟨i, h⟩)
| mu {ρ : DecodeEnv D m} {F : PER D → PER D} :
      (∀ X : PER D,
        DecodeAux k U' (ρ.snoc X) (f (mkMuVar m)) (f' (mkMuVar m)) (F X))
    → DecodeAux k U' ρ (μ̂ f) (μ̂ f') (PER.muFix F)

-- Forded Decode
inductive DecodeAux.Inv (k : Nat) (U' : ∀ ℓ, ℓ < k → ∀ m', DecodeEnv D m' → PER D)
    {m : Nat} (ρ : DecodeEnv D m) (c c' : D) (X : PER D) : Prop where
| univ
    (hℓ : ℓ < k) (_ : c = mkU ℓ) (_ : c' = mkU ℓ) (_ : X = U' ℓ hℓ m ρ)
| pi
    (_ : c = Π̂ a f) (_ : c' = Π̂ a' f')
    (_ : DecodeAux k U' ρ a a' A)
    (_ : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' ρ (f d) (f' d') (B d))
    (_ : X = PER.pi A B)
| sigma
    (_ : c = Σ̂ a f) (_ : c' = Σ̂ a' f')
    (_ : DecodeAux k U' ρ a a' A)
    (_ : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeAux k U' ρ (f d) (f' d') (B d))
    (_ : X = PER.sigma A B)
| bool
    (_ : c = mkBool) (_ : c' = mkBool)
    (_ : X = PER.bool)
| id
    (_ : c = Îd t a b) (_ : c' = Îd t' a' b')
    (_ : DecodeAux k U' ρ t t' A)
    (_ : a ~ a' ∈ₚ A) (_ : b ~ b' ∈ₚ A)
    (_ : X = PER.id A a b)
| muvar
    (h : i < m) (_ : c = mkMuVar i) (_ : c' = mkMuVar i) (_ : X = ρ ⟨i, h⟩)
| mu
    (_ : c = μ̂ f) (_ : c' = μ̂ f')
    (_ : ∀ Y : PER D,
      DecodeAux k U' (ρ.snoc Y) (f (mkMuVar m)) (f' (mkMuVar m)) (F Y))
    (_ : X = PER.muFix F)

theorem DecodeAux.inv {ρ : DecodeEnv D m} {X : PER D} (h : DecodeAux k U' ρ c c' X)
  : DecodeAux.Inv k U' ρ c c' X := by
  cases h <;> grind [
    DecodeAux.Inv.univ,
    DecodeAux.Inv.pi,
    DecodeAux.Inv.sigma,
    DecodeAux.Inv.bool,
    DecodeAux.Inv.id,
    DecodeAux.Inv.muvar,
    DecodeAux.Inv.mu
  ]

private theorem DecodeAux.det
  {U₁ : ∀ ℓ, ℓ < ℓ₁ → ∀ m', DecodeEnv D m' → PER D}
  {U₂ : ∀ ℓ, ℓ < ℓ₂ → ∀ m', DecodeEnv D m' → PER D}
  {ρ : DecodeEnv D m}
  (_ : ∀ ℓ (hk₁ : ℓ < ℓ₁) (hk₂ : ℓ < ℓ₂) m' (ρ' : DecodeEnv D m'),
    U₁ ℓ hk₁ m' ρ' = U₂ ℓ hk₂ m' ρ')
  (h₁ : DecodeAux ℓ₁ U₁ ρ c c₁ X) (h₂ : DecodeAux ℓ₂ U₂ ρ c c₂ Y)
  : X = Y := by induction h₁ generalizing c₂ Y with
  | univ =>
    rcases h₂.inv
    case univ.univ =>
      simp_all [mkU_inj ‹mkU _ = _›]
    all_goals have f := ‹mkU _ = _›; simpa using congrArg unU f
  | bool =>
    rcases h₂.inv
    case bool.bool => simp [‹_ = PER.bool›]
    all_goals have f := ‹mkBool = _›; simpa using congrArg unBool f
  | pi _ _ ihA ihB =>
    rcases h₂.inv with _ | ⟨_, _, _, hB1⟩
    case pi.pi =>
      simp_all [mkPi_inj ‹mkPi _ _ = _›]
      rcases ihA ‹DecodeAux ℓ₂ _ _ _ _ _›
      apply PER.ext; funext; apply propext
      constructor
      · intro hg _ _ hxy; rw [← ihB hxy (hB1 hxy)]; apply hg; assumption
      · intro hg _ _ hxy; rw [   ihB hxy (hB1 hxy)]; apply hg; assumption
    all_goals have f := ‹mkPi _ _ = _›; simpa using congrArg unPi f
  | sigma _ _ ihA ihB =>
    rcases h₂.inv with _ | _ | ⟨_, _, _, hB1⟩
    case sigma.sigma =>
      simp_all [mkSigma_inj ‹mkSigma _ _ = _›]
      rcases ihA ‹DecodeAux ℓ₂ _ _ _ _ _›
      apply PER.ext; funext p q; apply propext
      constructor
      · rintro ⟨a, b, a', b', rfl, rfl, hd, hcod⟩
        exact ⟨a, b, a', b', rfl, rfl, hd, by rw [← ihB hd (hB1 hd)]; exact hcod⟩
      · rintro ⟨a, b, a', b', rfl, rfl, hd, hcod⟩
        exact ⟨a, b, a', b', rfl, rfl, hd, by rw [ihB hd (hB1 hd)]; exact hcod⟩
    all_goals have f := ‹mkSigma _ _ = _›; simpa using congrArg unSigma f
  | id hsub ha hb ihsub =>
    rcases h₂.inv
    case id.id =>
      simp_all [mkId_inj ‹mkId _ _ _ = _›]
      simp_all [ihsub ‹DecodeAux ℓ₂ _ _ _ _ _›]
    all_goals have f := ‹mkId _ _ _ = _›; simpa using congrArg unId f
  | muvar h =>
    rcases h₂.inv
    case muvar.muvar =>
      obtain rfl := mkMuVar_inj ‹mkMuVar _ = _›
      simp_all
    all_goals have f := ‹mkMuVar _ = _›; simpa using congrArg unMuVar f
  | mu _ ihP =>
    rcases h₂.inv with _ | _ | _ | _ | _ | _ | ⟨hc, rfl, hP₂, rfl⟩
    case mu.mu =>
      obtain rfl := mkMu_inj hc
      exact congrArg PER.muFix (funext fun X' => ihP X' (hP₂ X'))
    all_goals have f := ‹mkMu _ = _›; simpa using congrArg unMu f

private theorem DecodeAux.symm {ρ : DecodeEnv D m} {X : PER D}
  (h : DecodeAux k U' ρ c c' X) : DecodeAux k U' ρ c' c X := by
  induction h
  case id _ ha hb _ =>
    rw [PER.id_congr ha hb]
    constructor
    all_goals grind [PERResp.eq_of_rel _ _, PER.symm]
  case muvar h _ => exact .muvar h
  case mu _ ih => exact .mu ih
  all_goals
    constructor
    all_goals grind [ PER.symm, PERResp.eq_of_rel _ _ ]

private theorem DecodeAux.trans {ρ : DecodeEnv D m} {X : PER D} {Y : PER D}
  (h₁ : DecodeAux k U' ρ c c' X) (h₂ : DecodeAux k U' ρ c' c'' Y)
  : DecodeAux k U' ρ c c'' X := by
  induction h₁ generalizing c'' Y with
  | univ hℓ =>
    rcases h₂.inv
    case univ.univ =>
      simp_all [mkU_inj ‹mkU _ = _›]
    all_goals have f := ‹mkU _ = _›; simpa using congrArg unU f
  | pi hA hB ihA ihB =>
    rcases h₂.inv with _ | ⟨hc, rfl, hA1, hB1, rfl⟩
    case pi.pi =>
      simp_all [mkPi_inj ‹mkPi _ _ = _›]
      obtain rfl := DecodeAux.det (by simp) hA.symm hA1
      refine .pi (ihA hA1) ?_
      intro _ _ hdd; exact ihB (PER.refl_left _ hdd) (hB1 hdd)
    all_goals have f := ‹mkPi _ _ = _›; simpa using congrArg unPi f
  | sigma hA hB ihA ihB =>
    rcases h₂.inv with ⟨_, hc, _, _⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, rfl, hA1, hB1, rfl⟩
      | ⟨hc, -, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨-, hc, -, -⟩ | ⟨hc, -, -, -⟩
    case sigma.sigma =>
      simp_all [mkSigma_inj ‹mkSigma _ _ = _›]
      obtain rfl := DecodeAux.det (by simp) hA.symm hA1
      refine .sigma (ihA hA1) ?_
      intro _ _ hdd; exact ihB (PER.refl_left _ hdd) (hB1 hdd)
    all_goals have f := ‹mkSigma _ _ = _›; simpa using congrArg unSigma f
  | bool =>
    rcases h₂.inv with ⟨_, hc, _, _⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
      | ⟨-, rfl, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨-, hc, -, -⟩ | ⟨hc, -, -, -⟩
    case bool.bool => exact .bool
    all_goals have f := ‹mkBool = _›; simpa using congrArg unBool f
  | id hsub ha hb ihsub =>
    rcases h₂.inv with ⟨_, hc, _, _⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
      | ⟨hc, -, -⟩ | ⟨hc, rfl, hsub2, ha2, hb2, rfl⟩ | ⟨-, hc, -, -⟩ | ⟨hc, -, -, -⟩
    case id.id =>
      rcases mkId_inj hc with ⟨rfl, rfl, rfl⟩
      obtain rfl := DecodeAux.det (by simp) hsub.symm hsub2
      exact DecodeAux.id (ihsub hsub2) (PER.trans _ ha ha2) (PER.trans _ hb hb2)
    all_goals have f := ‹mkId _ _ _ = _›; simpa using congrArg unId f
  | muvar h =>
    rcases h₂.inv with ⟨_, hc, _, _⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
      | ⟨hc, -, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨h', hc, rfl, -⟩ | ⟨hc, -, -, -⟩
    case muvar.muvar =>
      obtain rfl := mkMuVar_inj hc
      exact .muvar h
    all_goals have f := ‹mkMuVar _ = _›; simpa using congrArg unMuVar f
  | mu hP ihP =>
    rcases h₂.inv with ⟨_, hc, _, _⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
      | ⟨hc, -, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨-, hc, -, -⟩ | ⟨hc, rfl, hP₂, rfl⟩
    case mu.mu =>
      obtain rfl := mkMu_inj hc
      exact .mu (fun X' => ihP X' (hP₂ X'))
    all_goals have f := ‹mkMu _ = _›; simpa using congrArg unMu f


/-- The universe hierarchy, relative to a μ-variable environment: `μ`-variables
in scope are members of every relativized universe (via `muvar`), which is what
lets the μ-binder inhabit its type `𝓤 ℓ` in the fundamental lemma. -/
def URel (k : Nat) {m : Nat} (ρ : DecodeEnv D m) : PER D where
  rel c c' := ∃ X : PER D, DecodeAux k (fun ℓ _ _ ρ' => URel ℓ ρ') ρ c c' X
  sym := ⟨fun _ _ h => h.elim fun X hX => ⟨X, DecodeAux.symm hX⟩⟩
  tra := ⟨fun _ _ _ h h' => h.elim fun X hX => h'.elim fun _ hY => ⟨X, DecodeAux.trans hX hY⟩⟩

/-- The closed universe hierarchy: `URel` at the empty environment. -/
@[reducible]
def U (k : Nat) : PER D := URel k DecodeEnv.empty

/-- Decode relative to a μ-variable environment, with the universe assumptions
instantiated to the (relativized) hierarchy. -/
@[simp]
def DecodeRel (k : Nat) {m : Nat} (ρ : DecodeEnv D m) (c c' : D) (X : PER D) : Prop :=
  DecodeAux k (fun ℓ _ _ ρ' => URel ℓ ρ') ρ c c' X

@[simp]
def Decode (k : Nat) (c c' : D) (X : PER D) : Prop :=
  DecodeRel k DecodeEnv.empty c c' X

theorem Decode.symm {X : PER D} (h : Decode k c c' X) : Decode k c' c X :=
  DecodeAux.symm h

theorem Decode.trans  {X Y : PER D} (h : Decode k c c' X)
  (h' : Decode k c' c'' Y) : Decode k c c'' X :=
  DecodeAux.trans h h'

theorem Decode.refl_left {X : PER D} (h : Decode k c c' X) : Decode k c c X :=
  h.trans h.symm

theorem Decode.det {X Y : PER D} (h : Decode ℓ₁ c c₁ X) (h' : Decode ℓ₂ c c₂ Y)
  : X = Y := DecodeAux.det (by simp) h h'

@[simp]
theorem mem_U : (c ~ c' ∈ₚ U ℓ) ↔ ∃ X : PER D, Decode ℓ c c' X := by
  unfold U URel Decode DecodeRel; exact Iff.rfl

theorem Decode.univ (h : ℓ < k) : Decode k (mkU ℓ : D) (mkU ℓ) (U ℓ) := by
  simp ; exact (.univ h)

theorem Decode.pi {A : PER D}
    {B : A →ₚ PER.diag (PER D)} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) :
    Decode k (Π̂ a f) (Π̂ a' f') (PER.pi A B) := by
  simp; exact .pi  hA (fun hdd' => hB hdd')

theorem Decode.sigma {A : PER D}
    {B : A →ₚ PER.diag (PER D)} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) :
    Decode k (Σ̂ a f) (Σ̂ a' f') (PER.sigma A B) := by
  simp; exact .sigma hA (fun hdd' => hB hdd')

theorem Decode.bool : Decode k (mkBool : D) mkBool PER.bool := by
  simp; exact .bool

theorem Decode.id {A : PER D} (hA : Decode k t t' A) (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    Decode k (Îd t a b) (Îd t' a' b') (PER.id A a b) := by
  simp; exact .id hA ha hb

theorem Decode.mu {F : PER D → PER D}
    (h : ∀ X : PER D,
      DecodeRel k (DecodeEnv.empty.snoc X)
        (f (mkMuVar 0)) (f' (mkMuVar 0)) (F X)) :
    Decode k (μ̂ f) (μ̂ f') (PER.muFix F) := by
  simp; exact .mu h

private theorem DecodeAux.cumul {ρ : DecodeEnv D m} {X : PER D}
    (h : DecodeAux k (fun ℓ _ _ ρ' => URel ℓ ρ') ρ c c' X) (hk : k ≤ k') :
    DecodeAux k' (fun ℓ _ _ ρ' => URel ℓ ρ') ρ c c' X := by
  induction h
  all_goals
    constructor
    all_goals grind [LT.lt.trans_le]

theorem Decode.cumul {X : PER D} (h : Decode k c c' X) (hk : k ≤ k')
  : Decode k' c c' X := by
  simp at h ⊢
  exact DecodeAux.cumul h hk

inductive Decode.Inv (k : Nat) (c c' : D) (X : PER D) : Prop where
| univ (hℓ : ℓ < k) (hc : c = mkU ℓ) (hc' : c' = mkU ℓ) (hX : X = U ℓ)
| pi (hc : c = Π̂ a f) (hc' : c' = Π̂ a' f')
    (dom : Decode k a a' A)
    (cod : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (hX : X = PER.pi A B)
| sigma (hc : c = Σ̂ a f) (hc' : c' = Σ̂ a' f')
    (dom : Decode k a a' A)
    (cod : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (hX : X = PER.sigma A B)
| bool (hc : c = mkBool) (hc' : c' = mkBool) (hX : X = PER.bool)
| id (hc : c = Îd t a b) (hc' : c' = Îd t' a' b')
    (dom : Decode k t t' A)
    (ea : a ~ a' ∈ₚ A) (eb : b ~ b' ∈ₚ A)
    (hX : X = PER.id A a b)
| mu (hc : c = μ̂ f) (hc' : c' = μ̂ f')
    (body : ∀ Y : PER D,
      DecodeRel k (DecodeEnv.empty.snoc Y)
        (f (mkMuVar 0)) (f' (mkMuVar 0)) (F Y))
    (hX : X = PER.muFix F)

theorem Decode.inv {k : Nat} {c c' : D} {X : PER D}
    (h : Decode k c c' X) : Decode.Inv k c c' X := by
  simp at *
  rcases h.inv with ⟨hℓ, hc, hc', rfl⟩ | ⟨hc, hc', hA, hB, rfl⟩ | ⟨hc, hc', hA, hB, rfl⟩
    | ⟨hc, hc', rfl⟩ | ⟨hc, hc', hsub, ha, hb, rfl⟩ | ⟨h0, -, -, -⟩ | ⟨hc, hc', hP, rfl⟩
  · constructor <;> (try assumption); simp
  · exact .pi hc hc' hA (fun hdd' => hB hdd') rfl
  · exact .sigma hc hc' hA (fun hdd' => hB hdd') rfl
  · exact .bool hc hc' rfl
  · exact .id hc hc' hsub ha hb rfl
  · exact absurd h0 (Nat.not_lt_zero _)
  · exact .mu hc hc' hP rfl

inductive Decode.UnivInv (k ℓ : Nat) (c' : D) (X : PER D) : Prop where
| mk (lt : ℓ < k) (code : c' = mkU ℓ) (per : X = U ℓ)

theorem decode_univ_inv {k ℓ : Nat} {c' : D} {X : PER D}
    (h : Decode k (mkU ℓ : D) c' X) : Decode.UnivInv k ℓ c' X := by
  rcases h.inv
  case univ => constructor <;> grind [mkU_inj ‹mkU _ = _›]
  all_goals have f := ‹mkU _ = _›; simpa using congrArg unU f

inductive Decode.PiInv (k : Nat) (a : D) (f : D →𝒄 D) (c' : D) (X : PER D) : Prop where
| mk (a' : D) (f' : D →𝒄 D) (A : PER D) (B : A →ₚ PER.diag (PER D))
    (code : c' = Π̂ a' f')
    (dom  : Decode k a a' A)
    (cod  : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (per  : X = PER.pi A B)

theorem decode_pi_inv {k : Nat} {a : D} {f : D →𝒄 D} {c' : D} {X : PER D}
    (h : Decode k (Π̂ a f) c' X) : Decode.PiInv k a f c' X := by
  rcases h.inv with ⟨-, hc, -, -⟩ | ⟨hc, rfl, hA, hB, rfl⟩ | ⟨hc, -, -, -, -⟩
    | ⟨hc, -, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨hc, -, -, -⟩
  case pi =>
    simp [mkPi_inj ‹mkPi _ _ = _›]
    constructor <;> (try assumption); rfl; simp
  all_goals let f := ‹mkPi _ _ = _›; simpa using congrArg unPi f

inductive Decode.SigmaInv (k : Nat) (a : D) (f : D →𝒄 D) (c' : D) (X : PER D) : Prop where
| mk (a' : D) (f' : D →𝒄 D) (A : PER D) (B : A →ₚ PER.diag (PER D))
    (code : c' = Σ̂ a' f')
    (dom  : Decode k a a' A)
    (cod  : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (per  : X = PER.sigma A B)

theorem decode_sigma_inv {k : Nat} {a : D} {f : D →𝒄 D} {c' : D} {X : PER D}
    (h : Decode k (Σ̂ a f) c' X) : Decode.SigmaInv k a f c' X := by
  rcases h.inv with ⟨-, hc, -, -⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, rfl, hA, hB, rfl⟩
    | ⟨hc, -, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨hc, -, -, -⟩
  case sigma =>
    simp [mkSigma_inj ‹mkSigma _ _ = _›]
    constructor <;> (try assumption); rfl; simp
  all_goals let f := ‹mkSigma _ _ = _›; simpa using congrArg unSigma f

inductive Decode.BoolInv (k : Nat) (c' : D) (X : PER D) : Prop where
| mk (code : c' = mkBool) (per : X = PER.bool)

theorem decode_bool_inv {k : Nat} {c' : D} {X : PER D}
    (h : Decode k (mkBool : D) c' X) : Decode.BoolInv k c' X := by
  rcases h.inv with ⟨-, hc, -, -⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
    | ⟨-, hc', rfl⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨hc, -, -, -⟩
  case bool => exact ⟨hc', rfl⟩
  all_goals have f := ‹mkBool = _›; simpa using congrArg unBool f

inductive Decode.IdInv (k : Nat) (t a b : D) (c' : D) (X : PER D) : Prop where
| mk (t' a' b' : D) (A : PER D)
    (code : c' = Îd t' a' b')
    (dom : Decode k t t' A)
    (ea : a ~ a' ∈ₚ A) (eb : b ~ b' ∈ₚ A)
    (per : X = PER.id A a b)

theorem decode_id_inv {k : Nat} {t a b : D} {c' : D} {X : PER D}
    (h : Decode k (Îd t a b) c' X) : Decode.IdInv k t a b c' X := by
  rcases h.inv with ⟨-, hc, -, -⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
    | ⟨hc, -, -⟩ | ⟨hc, hc', hsub, ha, hb, rfl⟩ | ⟨hc, -, -, -⟩
  case id =>
    obtain ⟨rfl, rfl, rfl⟩ := mkId_inj hc
    exact ⟨_, _, _, _, hc', hsub, ha, hb, rfl⟩
  all_goals let f := ‹mkId _ _ _ = _›; simpa using congrArg unId f

inductive Decode.MuInv (k : Nat) (f : D →𝒄 D) (c' : D) (X : PER D) : Prop where
| mk (f' : D →𝒄 D) (F : PER D → PER D)
    (code : c' = μ̂ f')
    (body : ∀ Y : PER D,
      DecodeRel k (DecodeEnv.empty.snoc Y)
        (f (mkMuVar 0)) (f' (mkMuVar 0)) (F Y))
    (per : X = PER.muFix F)

theorem decode_mu_inv {k : Nat} {f : D →𝒄 D} {c' : D} {X : PER D}
    (h : Decode k (μ̂ f) c' X) : Decode.MuInv k f c' X := by
  rcases h.inv with ⟨-, hc, -, -⟩ | ⟨hc, -, -, -, -⟩ | ⟨hc, -, -, -, -⟩
    | ⟨hc, -, -⟩ | ⟨hc, -, -, -, -, -⟩ | ⟨hc, rfl, hP, rfl⟩
  case mu =>
    obtain rfl := mkMu_inj hc
    exact ⟨_, _, rfl, hP, rfl⟩
  all_goals let f := ‹mkMu _ = _›; simpa using congrArg unMu f

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

theorem Decode.el {ℓ : Nat} {c c' : D} (h : c ~ c' ∈ₚ U ℓ) : Decode ℓ c c' (El ℓ c) := by
  obtain ⟨X, hX⟩ := mem_U.mp h
  rw [El_eq_of_decode hX]
  exact hX

theorem El.det {c x y : D} (h₁ : x ~ y ∈ₚ El ℓ₁ c) (h₂ : x ~ y ∈ₚ El ℓ₂ c) :
    El ℓ₁ c = El ℓ₂ c := by
  obtain ⟨X, hX, _⟩ := h₁
  obtain ⟨Y, hY, _⟩ := h₂
  rw [El_eq_of_decode hX, El_eq_of_decode hY, Decode.det hX hY]

/-! ### The extension order on μ-variable environments

Decode-environment weakening is *not* a decode-level fact (a larger
environment enlarges the universes, so `pi` premises quantify over more
pairs), so the fundamental lemma is stated Kripke-style over this order. -/

omit [ScottDomain D Label] in
theorem DecodeEnv.castLE_succ (i : Fin m) :
    Fin.castLE (Nat.le_succ m) i = i.castSucc := by
  apply Fin.ext; simp

/-- `ν.Le ν'`: `ν'` extends `ν` (prefix order on μ-variable environments). -/
def DecodeEnv.Le (ν : DecodeEnv D m) (ν' : DecodeEnv D m') : Prop :=
  ∃ h : m ≤ m', ∀ i : Fin m, ν' (i.castLE h) = ν i

omit [ScottDomain D Label] in
theorem DecodeEnv.Le.refl (ν : DecodeEnv D m) : ν.Le ν :=
  ⟨Nat.le_refl m, fun i => by simp⟩

omit [ScottDomain D Label] in
theorem DecodeEnv.Le.trans {ν : DecodeEnv D m} {ν' : DecodeEnv D m'}
    {ν'' : DecodeEnv D m''} (h₁ : ν.Le ν') (h₂ : ν'.Le ν'') : ν.Le ν'' := by
  obtain ⟨hm₁, h₁⟩ := h₁
  obtain ⟨hm₂, h₂⟩ := h₂
  exact ⟨hm₁.trans hm₂, fun i => by rw [← h₁ i, ← h₂ (i.castLE hm₁)]; rfl⟩

omit [ScottDomain D Label] in
theorem DecodeEnv.Le.snoc (ν : DecodeEnv D m) (X : PER D) : ν.Le (ν.snoc X) :=
  ⟨Nat.le_succ m, fun i => by rw [DecodeEnv.castLE_succ]; simp⟩

omit [ScottDomain D Label] in
theorem DecodeEnv.Le.length {ν : DecodeEnv D m} {ν' : DecodeEnv D m'}
    (h : ν.Le ν') : m ≤ m' := h.1

/-! ### Relativized decode API (mirrors the empty-environment `Decode` API) -/

theorem DecodeRel.symm {ν : DecodeEnv D m} {X : PER D}
    (h : DecodeRel k ν c c' X) : DecodeRel k ν c' c X := DecodeAux.symm h

theorem DecodeRel.trans {ν : DecodeEnv D m} {X Y : PER D}
    (h : DecodeRel k ν c c' X) (h' : DecodeRel k ν c' c'' Y) :
    DecodeRel k ν c c'' X := DecodeAux.trans h h'

theorem DecodeRel.refl_left {ν : DecodeEnv D m} {X : PER D}
    (h : DecodeRel k ν c c' X) : DecodeRel k ν c c X := h.trans h.symm

theorem DecodeRel.det {ν : DecodeEnv D m} {X Y : PER D}
    (h : DecodeRel ℓ₁ ν c c₁ X) (h' : DecodeRel ℓ₂ ν c c₂ Y) : X = Y :=
  DecodeAux.det (by simp) h h'

theorem DecodeRel.cumul {ν : DecodeEnv D m} {X : PER D}
    (h : DecodeRel k ν c c' X) (hk : k ≤ k') : DecodeRel k' ν c c' X :=
  DecodeAux.cumul h hk

@[simp]
theorem mem_URel {ν : DecodeEnv D m} :
    (c ~ c' ∈ₚ URel ℓ ν) ↔ ∃ X : PER D, DecodeRel ℓ ν c c' X := by
  unfold URel DecodeRel; exact Iff.rfl

theorem DecodeRel.univ {ν : DecodeEnv D m} (h : ℓ < k) :
    DecodeRel k ν (mkU ℓ : D) (mkU ℓ) (URel ℓ ν) := by
  simp; exact (.univ h)

theorem DecodeRel.pi {ν : DecodeEnv D m} {A : PER D}
    {B : A →ₚ PER.diag (PER D)} (hA : DecodeRel k ν a a' A)
    (hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeRel k ν (f d) (f' d') (B d)) :
    DecodeRel k ν (Π̂ a f) (Π̂ a' f') (PER.pi A B) := by
  simp; exact .pi hA (fun hdd' => hB hdd')

theorem DecodeRel.sigma {ν : DecodeEnv D m} {A : PER D}
    {B : A →ₚ PER.diag (PER D)} (hA : DecodeRel k ν a a' A)
    (hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) → DecodeRel k ν (f d) (f' d') (B d)) :
    DecodeRel k ν (Σ̂ a f) (Σ̂ a' f') (PER.sigma A B) := by
  simp; exact .sigma hA (fun hdd' => hB hdd')

theorem DecodeRel.bool {ν : DecodeEnv D m} :
    DecodeRel k ν (mkBool : D) mkBool PER.bool := by
  simp; exact .bool

theorem DecodeRel.id {ν : DecodeEnv D m} {A : PER D} (hA : DecodeRel k ν t t' A)
    (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    DecodeRel k ν (Îd t a b) (Îd t' a' b') (PER.id A a b) := by
  simp; exact .id hA ha hb

theorem DecodeRel.muvar {ν : DecodeEnv D m} (h : i < m) :
    DecodeRel k ν (mkMuVar i : D) (mkMuVar i) (ν ⟨i, h⟩) := by
  simp; exact .muvar h

theorem DecodeRel.mu {ν : DecodeEnv D m} {F : PER D → PER D}
    (h : ∀ X : PER D,
      DecodeRel k (ν.snoc X) (f (mkMuVar m)) (f' (mkMuVar m)) (F X)) :
    DecodeRel k ν (μ̂ f) (μ̂ f') (PER.muFix F) := by
  simp; exact .mu h

/-- μ-variables in scope inhabit every relativized universe. -/
theorem URel.muvar_mem {ν : DecodeEnv D m} (h : i < m) :
    ((mkMuVar i : D) ~ mkMuVar i ∈ₚ URel ℓ ν) :=
  mem_URel.mpr ⟨_, DecodeRel.muvar h⟩

inductive DecodeRel.UnivInv (k ℓ : Nat) {m : Nat} (ν : DecodeEnv D m)
    (c' : D) (X : PER D) : Prop where
| mk (lt : ℓ < k) (code : c' = mkU ℓ) (per : X = URel ℓ ν)

theorem decodeRel_univ_inv {k ℓ : Nat} {ν : DecodeEnv D m} {c' : D} {X : PER D}
    (h : DecodeRel k ν (mkU ℓ : D) c' X) : DecodeRel.UnivInv k ℓ ν c' X := by
  rcases h.inv
  case univ => constructor <;> grind [mkU_inj ‹mkU _ = _›]
  all_goals have f := ‹mkU _ = _›; simpa using congrArg unU f

def ElRel (ℓ : Nat) {m : Nat} (ν : DecodeEnv D m) (c : D) : PER D where
  rel x y := ∃ X : PER D, DecodeRel ℓ ν c c X ∧ (x ~ y ∈ₚ X)
  sym := ⟨fun _ _ ⟨X, hX, hxy⟩ => ⟨X, hX, X.symm hxy⟩⟩
  tra := ⟨fun _ _ _ ⟨X, hX, h1⟩ ⟨_, hY, h2⟩ =>
    ⟨X, hX, X.trans h1 (DecodeRel.det hY hX ▸ h2)⟩⟩

theorem ElRel_eq_of_decode {ν : DecodeEnv D m} {c c' : D} {X : PER D}
    (h : DecodeRel ℓ ν c c' X) : ElRel ℓ ν c = X := by
  apply PER.ext
  funext x y
  apply propext
  exact ⟨fun ⟨X', hX', hxy⟩ => hX'.det h.refl_left ▸ hxy,
    fun hxy => ⟨X, h.refl_left, hxy⟩⟩

theorem DecodeRel.el {ν : DecodeEnv D m} {c c' : D} (h : c ~ c' ∈ₚ URel ℓ ν) :
    DecodeRel ℓ ν c c' (ElRel ℓ ν c) := by
  obtain ⟨X, hX⟩ := mem_URel.mp h
  rw [ElRel_eq_of_decode hX]
  exact hX
