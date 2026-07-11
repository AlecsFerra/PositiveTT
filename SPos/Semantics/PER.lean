
structure PER (D : Type u) where
  R     : D → D → Prop
  symm  : Symm R
  trans : Transitive R

namespace IsPER

variable {D : Type u} {R : D → D → Prop}

/-- Anything related is in the domain (self-related), on the left. -/
theorem refl_left (h : IsPER R) {a b : D} (hab : R a b) : R a a :=
  h.trans hab (h.symm hab)

/-- Anything related is in the domain (self-related), on the right. -/
theorem refl_right (h : IsPER R) {a b : D} (hab : R a b) : R b b :=
  h.trans (h.symm hab) hab

end IsPER
