import SPos.Syntax.Syntax
import SPos.Syntax.SyntaxProperties

abbrev Ctx := Env Tm

section
set_option hygiene false
notation:40 "⊢" Γ:40 => WfCtx Γ
notation:40 Γ:41 "⊢" a:41 "∶" A:41 => WfTm Γ a A
notation:40 Γ:41 "∋" x:41 "∶" τ:41 => Lookup Γ x τ
notation:40 Γ:41 "⊢" t:41 "≡" t':41 "∶" τ:41 => DefEq Γ t t' τ

inductive Lookup : Ctx n → Fin n → Tm n → Prop where
| here  : Γ ∷ τ ∋ 0 ∶ ↑ τ
| there : Γ ∋ n ∶ τ → Γ ∷ υ ∋ n.succ ∶ ↑ τ

mutual
inductive WfCtx : Ctx n → Prop where
| nil  : ⊢ ∅
| cons : ⊢ Γ → Γ ⊢ τ ∶ 𝓤 ℓ → ⊢ Γ ∷ τ

inductive WfTm : Ctx n → Tm n → Tm n → Prop where
| var : ⊢ Γ → Γ ∋ x ∶ τ → Γ ⊢ # x ∶ τ
| conv : Γ ⊢ t ∶ τ → Γ ⊢ σ ∶ 𝓤 ℓ → Γ ⊢ τ ≡ σ ∶ 𝓤 ℓ → Γ ⊢ t ∶ σ
-- Pi
| pi  : Γ ⊢ τ ∶ 𝓤 ℓ₁ → Γ ∷ τ ⊢ υ ∶ 𝓤 ℓ₂ → Γ ⊢ Π τ υ ∶ 𝓤 (max ℓ₁ ℓ₂)
| lam : Γ ⊢ τ ∶ 𝓤 ℓ → Γ ∷ τ ⊢ σ ∶ 𝓤 ℓ' → Γ ∷ τ ⊢ t ∶ σ → Γ ⊢ ƛ τ t ∶ (Π τ σ)
| app : Γ ⊢ t ∶ (Π τ σ) → Γ ⊢ m ∶ τ → Γ ⊢ t • m ∶ σ [/ m ]
-- Universe
| u : ⊢ Γ → Γ ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1)

inductive DefEq : Ctx n → Tm n → Tm n → Tm n → Prop where
| refl  : Γ ⊢ t ∶ τ → Γ ⊢ t ≡ t ∶ τ
| symm  : Γ ⊢ t ≡ t' ∶ τ → Γ ⊢ t' ≡ t ∶ τ
| trans : Γ ⊢ t ≡ t' ∶ τ → Γ ⊢ t' ≡ t'' ∶ τ → Γ ⊢ t ≡ t'' ∶ τ
-- Pi
| pi  : Γ ⊢ τ ∶ 𝓤 ℓ₁ → Γ ∷ τ ⊢ υ ∶ 𝓤 ℓ₂ → Γ ⊢ τ ≡ τ' ∶ 𝓤 ℓ₁ → Γ ∷ τ ⊢ υ ≡ υ' ∶ 𝓤 ℓ₂
     → Γ ⊢ Π τ υ ≡ Π τ' υ' ∶ 𝓤 (max ℓ₁ ℓ₂)
| lam : Γ ⊢ τ ∶ 𝓤 ℓ → Γ ∷ τ ⊢ σ ∶ 𝓤 ℓ' → Γ ∷ τ ⊢ t ≡ t' ∶ σ
     → Γ ⊢ ƛ τ t ≡ ƛ τ t' ∶ (Π τ σ)
| app : Γ ⊢ t ≡ t' ∶ (Π τ σ) → Γ ⊢ m ∶ τ → Γ ⊢ m ≡ m' ∶ τ
     → Γ ⊢ t • m ≡ t' • m' ∶ σ [/ m ]
| β : Γ ⊢ ƛ τ t ∶ (Π τ σ) → Γ ⊢ m ∶ τ
     → Γ ⊢ (ƛ τ t) • m ≡ t [/ m ] ∶ σ [/ m ]
| η : Γ ⊢ t ∶ Π τ υ → Γ ⊢ t ≡ ƛ τ (↑ t) • # 0 ∶ Π τ υ
end
end
