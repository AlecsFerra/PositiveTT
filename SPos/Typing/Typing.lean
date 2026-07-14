import SPos.Syntax.Syntax

abbrev Ctx := Env Tm

section
set_option hygiene false
notation:40 "⊢" Γ:40 => WfCtx Γ
notation:40 Γ:41 "∋" x:41 "∶" τ:41 => Lookup Γ x τ
notation:40 Γ:41 "⊢" t:41 "≡" t':41 "∶" τ:41 => DefEq Γ t t' τ

inductive Lookup : Ctx n → Fin n → Tm n → Prop where
| here  : Γ ∷ τ ∋ 0 ∶ ↑ τ
| there : Γ ∋ n ∶ τ → Γ ∷ υ ∋ n.succ ∶ ↑ τ

-- Typed definitional equality is the ONLY term judgment; typing is its
-- diagonal (`WfTm` below is an abbreviation, not an inductive).
mutual
inductive WfCtx : Ctx n → Prop where
| nil  : ⊢ ∅
| cons : ⊢ Γ → Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ → ⊢ Γ ∷ τ

inductive DefEq : Ctx n → Tm n → Tm n → Tm n → Prop where
| var   : ⊢ Γ → Γ ∋ x ∶ τ → Γ ⊢ # x ≡ # x ∶ τ
| u     : ⊢ Γ → Γ ⊢ 𝓤 ℓ ≡ 𝓤 ℓ ∶ 𝓤 (ℓ + 1)
| symm  : Γ ⊢ t ≡ t' ∶ τ → Γ ⊢ t' ≡ t ∶ τ
| trans : Γ ⊢ t ≡ t' ∶ τ → Γ ⊢ t' ≡ t'' ∶ τ → Γ ⊢ t ≡ t'' ∶ τ
| conv  : Γ ⊢ t ≡ t' ∶ τ → Γ ⊢ σ ≡ σ ∶ 𝓤 ℓ → Γ ⊢ τ ≡ σ ∶ 𝓤 ℓ → Γ ⊢ t ≡ t' ∶ σ
-- Pi
| pi  : Γ ⊢ τ ≡ τ' ∶ 𝓤 ℓ₁ → Γ ∷ τ ⊢ υ ≡ υ' ∶ 𝓤 ℓ₂ → Γ ⊢ Π τ υ ≡ Π τ' υ' ∶ 𝓤 (max ℓ₁ ℓ₂)
| lam : Γ ∷ τ ⊢ σ ≡ σ ∶ 𝓤 ℓ' → Γ ⊢ τ ≡ τ' ∶ 𝓤 ℓ → Γ ∷ τ ⊢ t ≡ t' ∶ σ →
        Γ ⊢ ƛ τ t ≡ ƛ τ' t' ∶ (Π τ σ)
| app : Γ ⊢ t ≡ t' ∶ (Π τ σ) → Γ ⊢ m ≡ m' ∶ τ → Γ ⊢ t • m ≡ t' • m' ∶ σ [/ m ]
| lamβ : Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ → Γ ∷ τ ⊢ σ ≡ σ ∶ 𝓤 ℓ' → Γ ∷ τ ⊢ t ≡ t ∶ σ → Γ ⊢ m ≡ m ∶ τ →
         Γ ⊢ (ƛ τ t) • m ≡ t [/ m ] ∶ σ [/ m ]
| lamη : Γ ⊢ t ≡ t ∶ Π τ υ → Γ ⊢ t ≡ ƛ τ (↑ t) • # 0 ∶ Π τ υ
-- Identity
| id : Γ ⊢ τ ≡ τ' ∶ 𝓤 ℓ → Γ ⊢ a ≡ a' ∶ τ → Γ ⊢ b ≡ b' ∶ τ →
       Γ ⊢ Id τ a b ≡ Id τ' a' b' ∶ 𝓤 ℓ
| reflId : Γ ⊢ τ ≡ τ' ∶ 𝓤 ℓ → Γ ⊢ a ≡ a' ∶ τ → Γ ⊢ refl τ a ≡ refl τ' a' ∶ Id τ a a
| j {a : Tm n} :
      Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ₁ →
      Γ ∷ τ ⊢ Id (↑ τ) (↑ a) # 0 ≡ Id (↑ τ) (↑ a) # 0 ∶ 𝓤 ℓ₁ →
      Γ ∷ τ ∷ Id (↑ τ) (↑ a) # 0 ⊢ C ≡ C' ∶ 𝓤 ℓ →
      Γ ⊢ d ≡ d' ∶ C [/ refl (↑ τ) (↑ a) ] [/ a ] →
      Γ ⊢ p ≡ p' ∶ Id τ a b →
      Γ ⊢ J C d p ≡ J C' d' p' ∶ C [/ ↑ p ] [/ b ]
| jβ : Γ ⊢ τ ≡ τ ∶ 𝓤 ℓ₁ → Γ ⊢ a ≡ a ∶ τ →
       Γ ∷ τ ⊢ Id (↑ τ) (↑ a) # 0 ≡ Id (↑ τ) (↑ a) # 0 ∶ 𝓤 ℓ₁ →
       Γ ∷ τ ∷ Id (↑ τ) (↑ a) # 0 ⊢ C ≡ C ∶ 𝓤 ℓ →
       Γ ⊢ d ≡ d ∶ C [/ refl (↑ τ) (↑ a) ] [/ a ] →
       Γ ⊢ J C d (refl τ a) ≡ d ∶ C [/ refl (↑ τ) (↑ a) ] [/ a ]
end
end

-- A term is well-typed iff it is definitionally equal to itself.
abbrev WfTm (Γ : Ctx n) (t τ : Tm n) : Prop := Γ ⊢ t ≡ t ∶ τ

notation:40 Γ:41 "⊢" t:41 "∶" τ:41 => WfTm Γ t τ

-- Diagonalization: both sides of an equation are well-typed.
theorem DefEq.wf_left (h : Γ ⊢ t ≡ t' ∶ τ) : Γ ⊢ t ∶ τ := h.trans h.symm

theorem DefEq.wf_right (h : Γ ⊢ t ≡ t' ∶ τ) : Γ ⊢ t' ∶ τ := h.symm.trans h
