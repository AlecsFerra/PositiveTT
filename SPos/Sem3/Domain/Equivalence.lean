import SPos.Sem3.Domain.Domain


section
set_option hygiene false

notation:40 t:41 "≡" t':41 "∶[" n:41 "]" τ:41 => Dn.equiv n t t' τ

-- Forcing the type to be at an higher approximation level makes stuff easier to
-- prove, but it is not strictly necessary.
def Dn.equiv (n : Nat) (t₁ t₂ : CDn n) (τ : CDn (n + 1)) : Prop :=
  match n, t₁, t₂, τ with
  | _, _, _, _ => by sorry
