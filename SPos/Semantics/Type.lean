import SPos.Structure.PER
import SPos.Semantics.DomainTheory.Domain
import SPos.Semantics.ValueDomain

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

def PER.id (A : PER D) (a b : D) : PER D where
  rel _ _ := a ~ b ∈ₚ A
  sym := ⟨ fun _ _ h => h ⟩
  tra := ⟨ fun _ _ _ h _ => h ⟩

omit [ScottDomain D Label] in
theorem PER.id_congr (ha : a ~ a' ∈ₚ A) (hb : b ~ b' ∈ₚ A) :
    PER.id A a b = PER.id A a' b' := by
  apply PER.ext; funext x y; apply propext
  exact ⟨fun h => A.trans (A.trans (A.symm ha) h) hb,
         fun h => A.trans (A.trans ha h) (A.symm hb)⟩
