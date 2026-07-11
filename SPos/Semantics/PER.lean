/-- A partial equivalence relation: symmetric and transitive, but not necessarily
reflexive. Its domain is `{a | R a a}`; on the domain it is an equivalence. -/
structure IsPER {D : Type u} (R : D → D → Prop) : Prop where
  symm  : ∀ {a b : D}, R a b → R b a
  trans : ∀ {a b c : D}, R a b → R b c → R a c

namespace IsPER

variable {D : Type u} {R : D → D → Prop}

/-- Anything related is in the domain (self-related), on the left. -/
theorem refl_left (h : IsPER R) {a b : D} (hab : R a b) : R a a :=
  h.trans hab (h.symm hab)

/-- Anything related is in the domain (self-related), on the right. -/
theorem refl_right (h : IsPER R) {a b : D} (hab : R a b) : R b b :=
  h.trans (h.symm hab) hab

end IsPER
