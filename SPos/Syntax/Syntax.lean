inductive Tm : (n : Nat) → Type where
| var : Fin n → Tm n
-- Pi
| pi  : Tm n → Tm (n + 1) → Tm n
| lam : Tm n → Tm (n + 1) → Tm n
| app : Tm n → Tm n → Tm n
-- Identity
| id   : Tm n → Tm n → Tm n → Tm n
| refl : Tm n → Tm n → Tm n
| j    : Tm (n + 2) → Tm n → Tm n → Tm n
-- Universe
| u  : Nat → Tm n

prefix:(max - 1) "#" => Tm.var

notation "Π" => Tm.pi
notation "ƛ" => Tm.lam
infixr:(max - 1) "•" => Tm.app

prefix:(max - 1) "𝓤" => Tm.u

notation "Id" => Tm.id
notation "refl" => Tm.refl
notation "J" => Tm.j

def Ren (n m : Nat) := Fin n → Fin m

def Ren.lift (ρ : Ren n m) : Ren (n + 1) (m + 1) :=
  Fin.cases 0 (fun i => (ρ i).succ)

def Tm.rename (ρ : Ren n m) : Tm n → Tm m
| .var i     => .var (ρ i)
| .pi τ υ    => .pi (τ.rename ρ) (υ.rename ρ.lift)
| .lam τ t   => .lam (τ.rename ρ) (t.rename ρ.lift)
| .app t₁ t₂ => .app (t₁.rename ρ) (t₂.rename ρ)
| .id τ a b  => .id (τ.rename ρ) (a.rename ρ) (b.rename ρ)
| .refl τ a  => .refl (τ.rename ρ) (a.rename ρ)
| .j c d p   => .j (c.rename ρ.lift.lift) (d.rename ρ) (p.rename ρ)
| .u ℓ       => .u ℓ

def Tm.weaken : Tm n → Tm (n + 1) := Tm.rename Fin.succ
prefix:(max - 1) "↑" => Tm.weaken

@[simp]
def Subst (n m : Nat) := Fin n → Tm m

def Subst.lift (σ : Subst n m) : Subst (n + 1) (m + 1) :=
  Fin.cases (Tm.var 0) (fun i => (σ i).weaken)

def Tm.subst (σ : Subst n m) : Tm n → Tm m
| .var i     => σ i
| .pi τ υ    => .pi (τ.subst σ) (υ.subst σ.lift)
| .lam τ t   => .lam (τ.subst σ) (t.subst σ.lift)
| .app t₁ t₂ => .app (t₁.subst σ) (t₂.subst σ)
| .id τ a b  => .id (τ.subst σ) (a.subst σ) (b.subst σ)
| .refl τ a  => .refl (τ.subst σ) (a.subst σ)
| .j c d p   => .j (c.subst σ.lift.lift) (d.subst σ) (p.subst σ)
| .u ℓ       => .u ℓ

def Subst.single (u : Tm n) : Subst (n + 1) n :=
  Fin.cases u Tm.var

def Tm.subst1 (t : Tm (n + 1)) (u : Tm n) : Tm n :=
  t.subst (Subst.single u)

notation:65 t " [/ " u " ]" => Tm.subst1 t u

abbrev Env (α : Nat → Type υ) (n : Nat) : Type υ :=
  (i : Fin n) → α i.val

abbrev Env.nil : Env α 0 :=
  fun i => i.elim0

abbrev Env.cons (ρ : Env α n) (v : α n) : Env α (n + 1) :=
  Fin.lastCases v ρ

abbrev Env.get (ρ : Env α n) (i : Fin n) : α i.rev := ρ i.rev

notation "∅"  => Env.nil
infixl:67 "∷" => Env.cons
