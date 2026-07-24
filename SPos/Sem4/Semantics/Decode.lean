import SPos.Sem4.Domains.Dinf
import SPos.Structure.PER

def PER.pi (dom : PER D∞) (cod : dom →ₚ PER.diag (PER D∞)) : PER D∞ where
  rel f g := ∀ (x y : D∞), (x ~ y ∈ₚ dom) → (f x) ~ (g y) ∈ₚ cod x
  sym := ⟨ fun f g h x y hxy => by
    have hcod : cod x = cod y := cod.respRelation _ _ hxy
    rw [hcod]
    exact PER.symm _ (h _ _ (PER.symm _ hxy))
  ⟩
  tra := ⟨ fun f g h hfg hgh x y hxy => by
    have hyy : y ~ y ∈ₚ dom := PER.refl_right _ hxy
    have hcod : cod x = cod y := cod.respRelation _ _ hxy
    apply PER.trans _ (hfg _ _ hxy)
    rw [hcod]
    exact hgh y y hyy
  ⟩

def PER.sigma (dom : PER D∞) (cod : dom →ₚ PER.diag (PER D∞)) : PER D∞ where
  rel p q := ∃ a b a' b', p = Dinf.pair a b ∧ q = Dinf.pair a' b'
              ∧ (a ~ a' ∈ₚ dom) ∧ (b ~ b' ∈ₚ cod a)
  sym := ⟨ fun p q h => by
    obtain ⟨a, b, a', b', rfl, rfl, h₁, h₂⟩ := h
    have hcod : cod a = cod a' := cod.respRelation _ _ h₁
    exact ⟨a', b', a, b, rfl, rfl, PER.symm _ h₁, hcod ▸ PER.symm _ h₂⟩
  ⟩
  tra := ⟨ fun p q r hpq hqr => by
    obtain ⟨a, b, a', b', rfl, hq, h₁, h₂⟩ := hpq
    obtain ⟨a'', b'', a₃, b₃, hq', rfl, h₃, h₄⟩ := hqr
    have heq := hq.symm.trans hq'
    obtain rfl : a' = a'' := by simpa using congrArg Dinf.fst heq
    obtain rfl : b' = b'' := by simpa using congrArg Dinf.snd heq
    have hcod : cod a = cod a' := cod.respRelation _ _ h₁
    exact ⟨a, b, a₃, b₃, rfl, rfl, PER.trans _ h₁ h₃, PER.trans _ h₂ (hcod ▸ h₄)⟩
  ⟩

def PER.bool : PER D∞ where
  rel u v := (u = Dinf.true ∧ v = Dinf.true) ∨ (u = Dinf.false ∧ v = Dinf.false)
  sym := ⟨ fun u v h => by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp ⟩
  tra := ⟨ fun u v w huv hvw => by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hvw with ⟨_, rfl⟩ | ⟨hv, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd (congrArg Dinf.tagOf hv)
          (by simp [Dinf.true, Dinf.false, Dinf.tagOf_op])
    · rcases hvw with ⟨hv, _⟩ | ⟨_, rfl⟩
      · exact absurd (congrArg Dinf.tagOf hv.symm)
          (by simp [Dinf.true, Dinf.false, Dinf.tagOf_op])
      · exact Or.inr ⟨rfl, rfl⟩
  ⟩

def PER.id (A : PER D∞) (a b : D∞) : PER D∞ where
  rel _ _ := a ~ b ∈ₚ A
  sym := ⟨ fun _ _ h => h ⟩
  tra := ⟨ fun _ _ _ h _ => h ⟩

theorem PER.id_congr {A : PER D∞} (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    PER.id A a b = PER.id A a' b' := by
  apply PER.ext; funext x y; apply propext
  grind [PER.id, PER.diag, PER.symm, PER.trans]

inductive DecodeAux (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D∞) : D∞ → D∞ → PER D∞ → Prop where
| univ (h : ℓ < k) : DecodeAux k U' (Dinf.univ ℓ) (Dinf.univ ℓ) (U' ℓ h)
| pi : DecodeAux k U' a a' A
    → (∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d))
    → DecodeAux k U' (Dinf.pi a f) (Dinf.pi a' f') (PER.pi A B)
| sigma : DecodeAux k U' a a' A
       → (∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d))
       → DecodeAux k U' (Dinf.sigma a f) (Dinf.sigma a' f') (PER.sigma A B)
| bool : DecodeAux k U' Dinf.bool Dinf.bool PER.bool
| id : DecodeAux k U' t t' A → (a ~ a' ∈ₚ A) → (b ~ b' ∈ₚ A)
    → DecodeAux k U' (Dinf.id t a b) (Dinf.id t' a' b') (PER.id A a b)

inductive DecodeAux.Inv (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D∞) (c c' : D∞) (X : PER D∞) : Prop where
| univ (hℓ : ℓ < k) (_ : c = Dinf.univ ℓ) (_ : c' = Dinf.univ ℓ)
           (_ : X = U' ℓ hℓ)
| pi
    (_ : c = Dinf.pi a f) (_ : c' = Dinf.pi a' f')
    (_ : DecodeAux k U' a a' A)
    (_ : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d))
    (_ : X = PER.pi A B)
| sigma
    (_ : c = Dinf.sigma a f) (_ : c' = Dinf.sigma a' f')
    (_ : DecodeAux k U' a a' A)
    (_ : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → DecodeAux k U' (f d) (f' d') (B d))
    (_ : X = PER.sigma A B)
| bool
    (_ : c = Dinf.bool) (_ : c' = Dinf.bool)
    (_ : X = PER.bool)
| id
    (_ : c = Dinf.id t a b) (_ : c' = Dinf.id t' a' b')
    (_ : DecodeAux k U' t t' A)
    (_ : a ~ a' ∈ₚ A) (_ : b ~ b' ∈ₚ A)
    (_ : X = PER.id A a b)

theorem DecodeAux.inv {X : PER D∞} (h : DecodeAux k U' c c' X)
  : DecodeAux.Inv k U' c c' X := by
  cases h <;> grind [
    DecodeAux.Inv.univ,
    DecodeAux.Inv.pi,
    DecodeAux.Inv.sigma,
    DecodeAux.Inv.bool,
    DecodeAux.Inv.id
  ]

private theorem DecodeAux.det {U₁ : ∀ ℓ, ℓ < ℓ₁ → PER D∞} {U₂ : ∀ ℓ, ℓ < ℓ₂ → PER D∞}
  (_ : ∀ ℓ (hk₁ : ℓ < ℓ₁) (hk₂ : ℓ < ℓ₂), U₁ ℓ hk₁ = U₂ ℓ hk₂)
  (h₁ : DecodeAux ℓ₁ U₁ c c₁ X) (h₂ : DecodeAux ℓ₂ U₂ c c₂ Y)
  : X = Y := by induction h₁ generalizing c₂ Y with
  | univ =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
    case univ =>
      obtain rfl := Dinf.univ_inj hc
      simp_all
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | bool =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
    case bool => simp [hX]
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | pi _ _ ihA ihB =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA1, hB1, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
    case pi =>
      obtain ⟨rfl, rfl⟩ := Dinf.pi_inj hc
      subst hX
      rcases ihA hA1
      apply PER.ext; funext; apply propext
      constructor
      · intro hg _ _ hxy; rw [← ihB hxy (hB1 hxy)]; apply hg; assumption
      · intro hg _ _ hxy; rw [   ihB hxy (hB1 hxy)]; apply hg; assumption
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | sigma _ _ ihA ihB =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA1, hB1, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
    case sigma =>
      obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc
      subst hX
      rcases ihA hA1
      apply PER.ext; funext p q; apply propext
      constructor
      · rintro ⟨a, b, a', b', rfl, rfl, hd, hcod⟩
        exact ⟨a, b, a', b', rfl, rfl, hd, by rw [← ihB hd (hB1 hd)]; exact hcod⟩
      · rintro ⟨a, b, a', b', rfl, rfl, hd, hcod⟩
        exact ⟨a, b, a', b', rfl, rfl, hd, by rw [ihB hd (hB1 hd)]; exact hcod⟩
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | id hsub ha hb ihsub =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha2, hb2, hX⟩
    case id =>
      obtain ⟨rfl, rfl, rfl⟩ := Dinf.id_inj hc
      simp_all [ihsub hA]
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

private theorem DecodeAux.symm {X : PER D∞}
  (h : DecodeAux k U' c c' X) : DecodeAux k U' c' c X := by
  induction h
  case id _ ha hb _ =>
    rw [PER.id_congr ha hb]
    constructor
    all_goals grind [PERResp.eq_of_rel _ _, PER.symm]
  all_goals
    constructor
    all_goals grind [ PER.symm, PERResp.eq_of_rel _ _ ]

private theorem DecodeAux.trans {X : PER D∞} {Y : PER D∞}
  (h₁ : DecodeAux k U' c c' X) (h₂ : DecodeAux k U' c' c'' Y)
  : DecodeAux k U' c c'' X := by
  induction h₁ generalizing c'' Y with
  | univ hℓ =>
    rcases h₂.inv with ⟨hℓ2, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
    case univ =>
      obtain rfl := Dinf.univ_inj hc
      simp_all
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | pi hA hB ihA ihB =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, rfl, hA1, hB1, rfl⟩ | ⟨hc, hc', hA', hB', hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA', ha, hb, hX⟩
    case pi =>
      obtain ⟨rfl, rfl⟩ := Dinf.pi_inj hc.symm
      obtain rfl := DecodeAux.det (by simp) hA.symm hA1
      refine .pi (ihA hA1) ?_
      intro _ _ hdd; exact ihB (PER.refl_left _ hdd) (hB1 hdd)
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | sigma hA hB ihA ihB =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA', hB', hX⟩ | ⟨hc, rfl, hA1, hB1, rfl⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA', ha, hb, hX⟩
    case sigma =>
      obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc.symm
      obtain rfl := DecodeAux.det (by simp) hA.symm hA1
      refine .sigma (ihA hA1) ?_
      intro _ _ hdd; exact ihB (PER.refl_left _ hdd) (hB1 hdd)
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | bool =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
    case bool => subst hc'; exact .bool
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f
  | id hsub ha hb ihsub =>
    rcases h₂.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
      | ⟨hc, hc', hX⟩ | ⟨hc, rfl, hsub2, ha2, hb2, rfl⟩
    case id =>
      obtain ⟨rfl, rfl, rfl⟩ := Dinf.id_inj hc.symm
      obtain rfl := DecodeAux.det (by simp) hsub.symm hsub2
      exact DecodeAux.id (ihsub hsub2) (PER.trans _ ha ha2) (PER.trans _ hb hb2)
    all_goals
      have f := congrArg Dinf.tagOf hc
      simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

def U (k : Nat) : PER D∞ where
  rel c c' := ∃ X : PER D∞, DecodeAux k (fun ℓ _ => U ℓ) c c' X
  sym := ⟨ fun _ _ h =>
    h.elim fun X hX => ⟨X, DecodeAux.symm hX⟩
  ⟩
  tra := ⟨ fun _ _ _ h h' =>
    h.elim fun X hX => h'.elim fun _ hY => ⟨X, DecodeAux.trans hX hY⟩
  ⟩

@[simp]
def Decode (k : Nat) (c c' : D∞) (X : PER D∞) : Prop :=
  DecodeAux k (fun ℓ _ => U ℓ) c c' X

theorem Decode.symm {X : PER D∞} (h : Decode k c c' X) : Decode k c' c X :=
  DecodeAux.symm h

theorem Decode.trans  {X Y : PER D∞} (h : Decode k c c' X)
  (h' : Decode k c' c'' Y) : Decode k c c'' X :=
  DecodeAux.trans h h'

theorem Decode.refl_left {X : PER D∞} (h : Decode k c c' X) : Decode k c c X :=
  h.trans h.symm

theorem Decode.det {X Y : PER D∞} (h : Decode ℓ₁ c c₁ X) (h' : Decode ℓ₂ c c₂ Y)
  : X = Y := DecodeAux.det (by simp) h h'

@[simp]
theorem mem_U : (c ~ c' ∈ₚ U ℓ) ↔ ∃ X : PER D∞, Decode ℓ c c' X := by
  unfold U Decode; exact Iff.rfl

theorem Decode.univ (h : ℓ < k) : Decode k (Dinf.univ ℓ) (Dinf.univ ℓ) (U ℓ) := by
  simp ; exact (.univ h)

theorem Decode.pi {A : PER D∞}
    {B : A →ₚ PER.diag (PER D∞)} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) :
    Decode k (Dinf.pi a f) (Dinf.pi a' f') (PER.pi A B) := by
  simp; exact .pi  hA (fun hdd' => hB hdd')

theorem Decode.sigma {A : PER D∞}
    {B : A →ₚ PER.diag (PER D∞)} (hA : Decode k a a' A)
    (hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d)) :
    Decode k (Dinf.sigma a f) (Dinf.sigma a' f') (PER.sigma A B) := by
  simp; exact .sigma hA (fun hdd' => hB hdd')

theorem Decode.bool : Decode k Dinf.bool Dinf.bool PER.bool := by
  simp; exact .bool

theorem Decode.id {A : PER D∞} (hA : Decode k t t' A) (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    Decode k (Dinf.id t a b) (Dinf.id t' a' b') (PER.id A a b) := by
  simp; exact .id hA ha hb

theorem Decode.cumul {X : PER D∞} (h : Decode k c c' X) (hk : k ≤ k')
  : Decode k' c c' X := by
  simp; induction h
  all_goals
    constructor
    all_goals grind [LT.lt.trans_le]

inductive Decode.Inv (k : Nat) (c c' : D∞) (X : PER D∞) : Prop where
| univ (hℓ : ℓ < k) (hc : c = Dinf.univ ℓ) (hc' : c' = Dinf.univ ℓ) (hX : X = U ℓ)
| pi (hc : c = Dinf.pi a f) (hc' : c' = Dinf.pi a' f')
    (dom : Decode k a a' A)
    (cod : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (hX : X = PER.pi A B)
| sigma (hc : c = Dinf.sigma a f) (hc' : c' = Dinf.sigma a' f')
    (dom : Decode k a a' A)
    (cod : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (hX : X = PER.sigma A B)
| bool (hc : c = Dinf.bool) (hc' : c' = Dinf.bool) (hX : X = PER.bool)
| id (hc : c = Dinf.id t a b) (hc' : c' = Dinf.id t' a' b')
    (dom : Decode k t t' A)
    (ea : a ~ a' ∈ₚ A) (eb : b ~ b' ∈ₚ A)
    (hX : X = PER.id A a b)

theorem Decode.inv {k : Nat} {c c' : D∞} {X : PER D∞}
    (h : Decode k c c' X) : Decode.Inv k c c' X := by
  simp at *
  rcases h.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
    | ⟨hc, hc', hX⟩ | ⟨hc, hc', hsub, ha, hb, hX⟩
  · exact .univ hℓ hc hc' hX
  · exact .pi hc hc' hA (fun hdd' => hB hdd') hX
  · exact .sigma hc hc' hA (fun hdd' => hB hdd') hX
  · exact .bool hc hc' hX
  · exact .id hc hc' hsub ha hb hX

inductive Decode.UnivInv (k ℓ : Nat) (c' : D∞) (X : PER D∞) : Prop where
| mk (lt : ℓ < k) (code : c' = Dinf.univ ℓ) (per : X = U ℓ)

theorem decode_univ_inv {k ℓ : Nat} {c' : D∞} {X : PER D∞}
    (h : Decode k (Dinf.univ ℓ) c' X) : Decode.UnivInv k ℓ c' X := by
  rcases h.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
    | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
  case univ =>
    obtain rfl := Dinf.univ_inj hc
    exact ⟨hℓ, hc', hX⟩
  all_goals
    have f := congrArg Dinf.tagOf hc
    simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

inductive Decode.PiInv (k : Nat) (a : D∞) (f : D∞ →ₛ D∞) (c' : D∞) (X : PER D∞) : Prop where
| mk (a' : D∞) (f' : D∞ →ₛ D∞) (A : PER D∞) (B : A →ₚ PER.diag (PER D∞))
    (code : c' = Dinf.pi a' f')
    (dom  : Decode k a a' A)
    (cod  : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (per  : X = PER.pi A B)

theorem decode_pi_inv {k : Nat} {a : D∞} {f : D∞ →ₛ D∞} {c' : D∞} {X : PER D∞}
    (h : Decode k (Dinf.pi a f) c' X) : Decode.PiInv k a f c' X := by
  rcases h.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
    | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
  case pi =>
    obtain ⟨rfl, rfl⟩ := Dinf.pi_inj hc.symm
    exact ⟨_, _, _, _, hc', hA, (fun hdd' => hB hdd'), hX⟩
  all_goals
    have f := congrArg Dinf.tagOf hc
    simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

inductive Decode.SigmaInv (k : Nat) (a : D∞) (f : D∞ →ₛ D∞) (c' : D∞) (X : PER D∞) : Prop where
| mk (a' : D∞) (f' : D∞ →ₛ D∞) (A : PER D∞) (B : A →ₚ PER.diag (PER D∞))
    (code : c' = Dinf.sigma a' f')
    (dom  : Decode k a a' A)
    (cod  : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → Decode k (f d) (f' d') (B d))
    (per  : X = PER.sigma A B)

theorem decode_sigma_inv {k : Nat} {a : D∞} {f : D∞ →ₛ D∞} {c' : D∞} {X : PER D∞}
    (h : Decode k (Dinf.sigma a f) c' X) : Decode.SigmaInv k a f c' X := by
  rcases h.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
    | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
  case sigma =>
    obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc.symm
    exact ⟨_, _, _, _, hc', hA, (fun hdd' => hB hdd'), hX⟩
  all_goals
    have f := congrArg Dinf.tagOf hc
    simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

inductive Decode.BoolInv (k : Nat) (c' : D∞) (X : PER D∞) : Prop where
| mk (code : c' = Dinf.bool) (per : X = PER.bool)

theorem decode_bool_inv {k : Nat} {c' : D∞} {X : PER D∞}
    (h : Decode k Dinf.bool c' X) : Decode.BoolInv k c' X := by
  rcases h.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
    | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
  case bool => exact ⟨hc', hX⟩
  all_goals
    have f := congrArg Dinf.tagOf hc
    simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

inductive Decode.IdInv (k : Nat) (t a b : D∞) (c' : D∞) (X : PER D∞) : Prop where
| mk (t' a' b' : D∞) (A : PER D∞)
    (code : c' = Dinf.id t' a' b')
    (dom : Decode k t t' A)
    (ea : a ~ a' ∈ₚ A) (eb : b ~ b' ∈ₚ A)
    (per : X = PER.id A a b)

theorem decode_id_inv {k : Nat} {t a b : D∞} {c' : D∞} {X : PER D∞}
    (h : Decode k (Dinf.id t a b) c' X) : Decode.IdInv k t a b c' X := by
  rcases h.inv with ⟨hℓ, hc, hc', hX⟩ | ⟨hc, hc', hA, hB, hX⟩ | ⟨hc, hc', hA, hB, hX⟩
    | ⟨hc, hc', hX⟩ | ⟨hc, hc', hA, ha, hb, hX⟩
  case id =>
    obtain ⟨rfl, rfl, rfl⟩ := Dinf.id_inj hc.symm
    exact ⟨_, _, _, _, hc', hA, ha, hb, hX⟩
  all_goals
    have f := congrArg Dinf.tagOf hc
    simp [Dinf.univ, Dinf.pi, Dinf.sigma, Dinf.bool, Dinf.id, Dinf.tagOf_op] at f

def El (ℓ : Nat) (c : D∞) : PER D∞ where
  rel x y := ∃ X : PER D∞, Decode ℓ c c X ∧ (x ~ y ∈ₚ X)
  sym := ⟨fun _ _ ⟨X, hX, hxy⟩ => ⟨X, hX, X.symm hxy⟩⟩
  tra := ⟨fun _ _ _ ⟨X, hX, h1⟩ ⟨_, hY, h2⟩ => ⟨X, hX, X.trans h1 (Decode.det hY hX ▸ h2)⟩⟩

theorem El_eq_of_decode {ℓ : Nat} {c c' : D∞} {X : PER D∞}
    (h : Decode ℓ c c' X) : El ℓ c = X := by
  apply PER.ext
  funext x y
  apply propext
  exact ⟨fun ⟨X', hX', hxy⟩ => hX'.det h.refl_left ▸ hxy, fun hxy => ⟨X, h.refl_left, hxy⟩⟩

theorem Decode.el {ℓ : Nat} {c c' : D∞} (h : c ~ c' ∈ₚ U ℓ) : Decode ℓ c c' (El ℓ c) := by
  obtain ⟨X, hX⟩ := mem_U.mp h
  rw [El_eq_of_decode hX]
  exact hX

theorem El.det {c x y : D∞} (h₁ : x ~ y ∈ₚ El ℓ₁ c) (h₂ : x ~ y ∈ₚ El ℓ₂ c) :
    El ℓ₁ c = El ℓ₂ c := by
  obtain ⟨X, hX, _⟩ := h₁
  obtain ⟨Y, hY, _⟩ := h₂
  rw [El_eq_of_decode hX, El_eq_of_decode hY, Decode.det hX hY]

noncomputable def muBody : D∞ →ₛ D∞ := by
  refine ƛₛ[?_] d ↦ Dinf.sigma Dinf.bool (ƛₛ b ↦ Dinf.ite b
    (Dinf.id Dinf.bool Dinf.true Dinf.true)
    (Dinf.sigma Dinf.bool (ƛₛ _ ↦ d)))
  refine ScottContinuousF.scottContinuous_apply (by fun_prop) ?_
  apply ScottContinuousF.of_apply₂
  intro b
  apply Dinf.scottContinuous_ite (by fun_prop) (by fun_prop)
  exact ScottContinuousF.scottContinuous_apply (by fun_prop)
    (ScottContinuousF.of_apply₂ (fun _ => ScottContinuous.id))

noncomputable def muL : D∞ := ScottContinuous.lfp muBody

theorem muL_unfold : muL = Dinf.sigma Dinf.bool (ƛₛ b ↦ Dinf.ite b
    (Dinf.id Dinf.bool Dinf.true Dinf.true) (Dinf.sigma Dinf.bool (ƛₛ _ ↦ muL))) :=
  (ScottContinuous.lfp_fix muBody).symm

noncomputable def muTail (X : PER D∞) : PER D∞ :=
  PER.sigma PER.bool
    (PERRespND.mk PER.bool (PER.diag (PER D∞)) (fun _ => X)
      (by rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl))

noncomputable def muCod (X : PER D∞) : PER.bool →ₚ PER.diag (PER D∞) :=
  PERRespND.mk PER.bool (PER.diag (PER D∞))
    (fun b => if b.tagOf = some .true then PER.id PER.bool Dinf.true Dinf.true else muTail X)
    (by rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl)

noncomputable def muPer (X : PER D∞) : PER D∞ := PER.sigma PER.bool (muCod X)

theorem muBody_decode {k : Nat} {X : D∞} {Xper : PER D∞} (hX : Decode k X X Xper) :
    Decode k (muBody X) (muBody X) (muPer Xper) := by
  show Decode k (Dinf.sigma _ _) (Dinf.sigma _ _) (PER.sigma _ _)
  refine Decode.sigma Decode.bool ?_
  rintro d d' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact Decode.id Decode.bool (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩)
  · exact Decode.sigma Decode.bool (fun _ => hX)

theorem decode_mu {k : Nat} {X : PER D∞}
    (hc : Decode k (ScottContinuous.lfp muBody) (ScottContinuous.lfp muBody) X) :
    X = muPer X := by
  have key := muBody_decode hc
  rw [ScottContinuous.lfp_fix] at key
  exact Decode.det hc key

theorem lfp_not_decode {k : Nat} : ∀ {a a' : D∞} {Y : PER D∞}, Decode k a a' Y →
    a = ScottContinuous.lfp muBody ∨
    a = Dinf.sigma Dinf.bool (ƛₛ _ ↦ ScottContinuous.lfp muBody) → False := by
  have hL : ScottContinuous.lfp muBody = Dinf.sigma Dinf.bool (ƛₛ b ↦ Dinf.ite b
      (Dinf.id Dinf.bool Dinf.true Dinf.true)
      (Dinf.sigma Dinf.bool (ƛₛ _ ↦ ScottContinuous.lfp muBody))) :=
    (ScottContinuous.lfp_fix muBody).symm
  have htL : (ScottContinuous.lfp muBody).tagOf = some Tag.sigma := by
    rw [hL]; simp [Dinf.sigma, Dinf.tagOf_op]
  have htLσ : (Dinf.sigma Dinf.bool (ƛₛ _ ↦ ScottContinuous.lfp muBody)).tagOf = some Tag.sigma := by
    simp [Dinf.sigma, Dinf.tagOf_op]
  intro a a' Y h
  induction h
  case sigma a₀ a₀' A f f' B hdom hcod ihdom ihcod =>
    intro hP
    rcases hP with hP | hP
    · rw [hL] at hP
      obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hP
      obtain ⟨_, rfl⟩ := decode_bool_inv hdom
      exact ihcod (Or.inr ⟨rfl, rfl⟩) (Or.inr rfl)
    · obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hP
      obtain ⟨_, rfl⟩ := decode_bool_inv hdom
      exact ihcod (Or.inr ⟨rfl, rfl⟩) (Or.inl rfl)
  all_goals
    intro hP
    rcases hP with h | h <;>
    · have ht := congrArg Dinf.tagOf h
      first | rw [htL] at ht | rw [htLσ] at ht
      simp [Dinf.univ, Dinf.pi, Dinf.bool, Dinf.id, Dinf.tagOf_op] at ht

theorem list_not_decodable {k : Nat} :
    ¬ ∃ X, Decode k (ScottContinuous.lfp muBody) (ScottContinuous.lfp muBody) X := by
  rintro ⟨X, hX⟩
  exact lfp_not_decode hX (Or.inl rfl)

inductive DecodeF (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D∞) (R : D∞ → D∞ → PER D∞ → Prop) :
    D∞ → D∞ → PER D∞ → Prop where
  | univ (h : ℓ < k) : DecodeF k U' R (Dinf.univ ℓ) (Dinf.univ ℓ) (U' ℓ h)
  | pi (hA : R a a' A) (hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → R (f d) (f' d') (B d)) :
      DecodeF k U' R (Dinf.pi a f) (Dinf.pi a' f') (PER.pi A B)
  | sigma (hA : R a a' A) (hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → R (f d) (f' d') (B d)) :
      DecodeF k U' R (Dinf.sigma a f) (Dinf.sigma a' f') (PER.sigma A B)
  | bool : DecodeF k U' R Dinf.bool Dinf.bool PER.bool
  | id (hA : R t t' A) (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
      DecodeF k U' R (Dinf.id t a b) (Dinf.id t' a' b') (PER.id A a b)

theorem DecodeF.mono {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} {R S : D∞ → D∞ → PER D∞ → Prop}
    (h : ∀ a a' Y, R a a' Y → S a a' Y) {c c' : D∞} {X : PER D∞}
    (hF : DecodeF k U' R c c' X) : DecodeF k U' S c c' X := by
  cases hF
  case univ hℓ => exact .univ hℓ
  case pi hA hB => exact .pi (h _ _ _ hA) (fun hdd' => h _ _ _ (hB hdd'))
  case sigma hA hB => exact .sigma (h _ _ _ hA) (fun hdd' => h _ _ _ (hB hdd'))
  case bool => exact .bool
  case id hA ha hb => exact .id (h _ _ _ hA) ha hb

def DecodeCo (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D∞) (c c' : D∞) (X : PER D∞) : Prop :=
  ∃ R : D∞ → D∞ → PER D∞ → Prop,
    (∀ a a' Y, R a a' Y → DecodeF k U' R a a' Y) ∧ R c c' X

theorem DecodeCo.coinduct {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞}
    (R : D∞ → D∞ → PER D∞ → Prop)
    (hR : ∀ a a' Y, R a a' Y → DecodeF k U' R a a' Y)
    {c c' : D∞} {X : PER D∞} (h : R c c' X) : DecodeCo k U' c c' X :=
  ⟨R, hR, h⟩

theorem DecodeCo.unfold {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} {c c' : D∞} {X : PER D∞}
    (h : DecodeCo k U' c c' X) : DecodeF k U' (DecodeCo k U') c c' X := by
  obtain ⟨R, hR, hc⟩ := h
  exact DecodeF.mono (fun a a' Y hay => ⟨R, hR, hay⟩) (hR c c' X hc)

theorem DecodeCo.fold {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} {c c' : D∞} {X : PER D∞}
    (hf : DecodeF k U' (DecodeCo k U') c c' X) : DecodeCo k U' c c' X := by
  refine ⟨fun a a' Y => DecodeF k U' (DecodeCo k U') a a' Y, ?_, hf⟩
  intro a a' Y hay
  exact DecodeF.mono (fun b b' Z hb => DecodeCo.unfold hb) hay

theorem DecodeCo.bool {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} :
    DecodeCo k U' Dinf.bool Dinf.bool PER.bool :=
  DecodeCo.fold .bool

theorem DecodeCo.id {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} {A : PER D∞}
    (hA : DecodeCo k U' t t' A) (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    DecodeCo k U' (Dinf.id t a b) (Dinf.id t' a' b') (PER.id A a b) :=
  DecodeCo.fold (.id hA ha hb)

theorem DecodeCo.sigma {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} {A : PER D∞}
    {B : A →ₚ PER.diag (PER D∞)} (hA : DecodeCo k U' a a' A)
    (hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) → DecodeCo k U' (f d) (f' d') (B d)) :
    DecodeCo k U' (Dinf.sigma a f) (Dinf.sigma a' f') (PER.sigma A B) :=
  DecodeCo.fold (.sigma hA (fun hdd' => hB hdd'))

noncomputable def muLσ : D∞ := Dinf.sigma Dinf.bool (ƛₛ _ ↦ muL)

def listR (k : Nat) (U' : ∀ ℓ, ℓ < k → PER D∞) (X : PER D∞) :
    D∞ → D∞ → PER D∞ → Prop :=
  fun a a' Y => DecodeCo k U' a a' Y ∨
    (a = muL ∧ a' = muL ∧ Y = X) ∨
    (a = muLσ ∧ a' = muLσ ∧ Y = muTail X)

theorem decodeCo_list {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} {X : PER D∞}
    (hXfix : X = muPer X) : DecodeCo k U' muL muL X := by
  refine DecodeCo.coinduct (listR k U' X) ?_ (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  intro a a' Y hRa
  unfold listR at hRa
  rcases hRa with hCo | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · exact DecodeF.mono (fun b b' Z hb => Or.inl hb) hCo.unfold
  · rw [muL_unfold]
    nth_rewrite 2 [hXfix]
    refine DecodeF.sigma (Or.inl DecodeCo.bool) ?_
    rintro d d' (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact Or.inl (DecodeCo.id DecodeCo.bool (Or.inl ⟨rfl, rfl⟩) (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)
  · refine DecodeF.sigma (Or.inl DecodeCo.bool) ?_
    intro d d' _
    exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

theorem decodeCo_det_forces_unique {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞}
    (det : ∀ Y Z, DecodeCo k U' muL muL Y → DecodeCo k U' muL muL Z → Y = Z)
    {Y Z : PER D∞} (hY : Y = muPer Y) (hZ : Z = muPer Z) : Y = Z :=
  det Y Z (decodeCo_list hY) (decodeCo_list hZ)

theorem muPer_mono : Monotone muPer := by
  intro X X' hXX' p q hpq
  obtain ⟨a, b, a', b', rfl, rfl, hbool, hcod⟩ := hpq
  refine ⟨a, b, a', b', rfl, rfl, hbool, ?_⟩
  rcases hbool with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hcod
  · obtain ⟨c, e, c', e', rfl, rfl, hb2, hc2⟩ := hcod
    exact ⟨c, e, c', e', rfl, rfl, hb2, hXX' hc2⟩

theorem decodeCo_muFix {k : Nat} {U' : ∀ ℓ, ℓ < k → PER D∞} :
    DecodeCo k U' muL muL (PER.muFix muPer) :=
  decodeCo_list (PER.muFix_fixed muPer_mono).symm
