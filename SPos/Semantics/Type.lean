import SPos.Structure.PER
import SPos.Semantics.DomainTheory.Domain
import SPos.Semantics.ValueDomain

open ScottDomain

variable
  {D : Type u} [ScottDomain D Label]

def PER.pi (dom : PER D) (cod : dom →ₚ PER.diag (PER D)) : PER D where
  rel f g := ∀ (x y : D), (x ~ y ∈ₚ dom) → (f •𝒄 x) ~ (g •𝒄 y) ∈ₚ cod x

  sym := ⟨ fun f g h x y hxy => by
    simp [PER.diag] at *
    have hcod : cod x = cod y := by
      exact cod.respRelation _ _ hxy
    rw [hcod]
    exact PER.symm _ (h _ _ (PER.symm _ hxy))
  ⟩

  tra := ⟨ fun f g h hfg hgh x y hxy => by
    simp [PER.diag] at *
    have hyy : y ~ y ∈ₚ dom := PER.refl_right _ hxy
    have hcod : cod x = cod y := by
      exact cod.respRelation _ _ hxy
    apply PER.trans _ (hfg _ _ hxy)
    rw [hcod]
    exact hgh y y hyy
  ⟩


def PER.sigma (dom : PER D) (cod : dom →ₚ PER.diag (PER D)) : PER D where
  rel p q := ∃ a b a' b', p = mkPair a b ∧ q = mkPair a' b'
              ∧ (a ~ a' ∈ₚ dom) ∧ (b ~ b' ∈ₚ cod a)

  sym := ⟨ fun p q h => by
    obtain ⟨a, b, a', b', rfl, rfl, h₁, h₂⟩ := h
    have hcod : cod a = cod a' := cod.respRelation _ _ h₁
    exact ⟨a', b', a, b, rfl, rfl, PER.symm _ h₁, hcod ▸ PER.symm _ h₂⟩
  ⟩

  tra := ⟨ fun p q r hpq hqr => by
    obtain ⟨a, b, a', b', rfl, hq, h₁, h₂⟩ := hpq
    obtain ⟨a'', b'', a₃, b₃, hq', rfl, h₃, h₄⟩ := hqr
    obtain ⟨rfl, rfl⟩ := mkPair_inj (hq.symm.trans hq')
    have hcod : cod a = cod a' := cod.respRelation _ _ h₁
    exact ⟨a, b, a₃, b₃, rfl, rfl, PER.trans _ h₁ h₃, PER.trans _ h₂ (hcod ▸ h₄)⟩
  ⟩

def PER.bool : PER D where
  rel u v := (u = mkTrue ∧ v = mkTrue) ∨ (u = mkFalse ∧ v = mkFalse)
  sym := ⟨ fun u v h => by rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp ⟩
  tra := ⟨ fun u v w huv hvw => by
    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rcases hvw with ⟨_, rfl⟩ | ⟨hv, _⟩
      · exact Or.inl ⟨rfl, rfl⟩
      · exact absurd hv mkTrue_ne_mkFalse
    · rcases hvw with ⟨hv, _⟩ | ⟨_, rfl⟩
      · exact absurd hv.symm mkTrue_ne_mkFalse
      · exact Or.inr ⟨rfl, rfl⟩
  ⟩

def PER.id (A : PER D) (a b : D) : PER D where
  rel _ _ := a ~ b ∈ₚ A
  sym := ⟨ fun _ _ h => h ⟩
  tra := ⟨ fun _ _ _ h _ => h ⟩

omit [ScottDomain D Label] in
theorem PER.id_congr (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    PER.id A a b = PER.id A a' b' := by
  apply PER.ext; funext x y; apply propext
  grind [PER.id, PER.diag, PER.symm, PER.trans]
  -- exact ⟨fun h => A.trans (A.trans (A.symm ha) h) hb,
  --        fun h => A.trans (A.trans ha h) (A.symm hb)⟩
