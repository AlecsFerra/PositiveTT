import SPos.Sem3.DomainConstruction.Approximation
import SPos.Sem3.DomainConstruction.Projection
import SPos.Sem3.DomainConstruction.Dinf


inductive Symbol where
-- Universe
| univ (ℓ : Nat)
-- Pi
| pi
-- Sigma
| sigma | pair
-- Bool
| bool | true | false
-- Identity
| id | refl
-- Recursive types
| mu | fold

-- We are forced to use this instead of Dn because pattern matching does not
-- reduce definitions even if they are reducible.
abbrev CDn (n : Nat) := DStep Symbol (DBuild Symbol n).fst

@[match_pattern]
def CDn.univ (ℓ : Nat) : CDn (n + 1)
  := .flat (.univ ℓ)

@[match_pattern]
def CDn.pi (τ : CDn n) (υ : CDn n) : CDn (n + 2)
  := .pair (.flat .pi) (.pair τ υ)

@[match_pattern]
def CDn.sigma (τ υ : CDn n) : CDn (n + 2)
  := .pair (.flat .sigma) (.pair τ υ)

@[match_pattern]
def CDn.par (a b : CDn n) : CDn (n + 2)
  := .pair (.flat .pair) (.pair a b)

@[match_pattern]
def CDn.bool : CDn (n + 1)
  := .flat .bool

@[match_pattern]
def CDn.true : CDn (n + 1)
  := .flat .true

@[match_pattern]
def CDn.false : CDn (n + 1)
  := .flat .false

@[match_pattern]
def CDn.id (τ : CDn (n + 1)) (a b : CDn n) : CDn (n + 3)
  := .pair (.flat .id) (.pair τ (.pair a b))

@[match_pattern]
def CDn.refl : CDn (n + 1)
  := .flat .refl

@[match_pattern]
def CDn.mu (τ : CDn n) : CDn (n + 1)
  := .pair (.flat .mu) τ

@[match_pattern]
def CDn.fold (t : CDn n) : CDn (n + 1)
  := .pair (.flat .fold) t

-- noncomputable def CDn.apply : CDn n × CDn n →ₛ CDn n := by
--   refine ƛₛ[ ?_ ] fg ↦ match n, fg with
--   | _ + 1, (.lam b, x) => b (Dn.down x)
--   | _,     _           => ⊥
--   all_goals sorry
-- infixr:60 "•ₐ" => fun x y => CDn.apply (x, y)
