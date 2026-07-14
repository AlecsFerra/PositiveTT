import SPos.Syntax.Syntax

abbrev Ctx := Env Tm

section
set_option hygiene false
notation:40 "⊢" Γ:40 => WfCtx Γ
notation:40 Γ:41 "∋" x:41 "∶" τ:41 => Lookup Γ x τ
notation:40 Γ:41 "⊢" t:41 "≡" t':41 "∶" τ:41 => DefEq Γ t t' τ
notation:40 Γ:41 "⊢" t:41 "∶" τ:41 => DefEq Γ t t τ

inductive Lookup : Ctx n → Fin n → Tm n → Prop where
| here  : Γ ∷ τ ∋ 0 ∶ ↑ τ
| there : Γ ∋ n ∶ τ → Γ ∷ υ ∋ n.succ ∶ ↑ τ

mutual
inductive WfCtx : Ctx n → Prop where
| nil  : ⊢ ∅
| cons : ⊢ Γ → Γ ⊢ τ ∶ 𝓤 ℓ → ⊢ Γ ∷ τ

-- The idea is absuing structural rules to get the standard typing
-- judgjments

inductive DefEq : Ctx n → Tm n → Tm n → Tm n → Prop where
-- Structual rules
| symm  : Γ ⊢ t₁ ≡ t₂ ∶ τ
        -----------------
       → Γ ⊢ t₂ ≡ t₁ ∶ τ
| trans : Γ ⊢ t₁ ≡ t₂ ∶ τ → Γ ⊢ t₂ ≡ t₃ ∶ τ
        ------------------------------------
       → Γ ⊢ t₁ ≡ t₃ ∶ τ
-- Conversion
| conv : Γ ⊢ t₁ ≡ t₂ ∶ τ₁ → Γ ⊢ τ₂ ∶ 𝓤 ℓ → Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ
       --------------------------------------------------------
      → Γ ⊢ t₁ ≡ t₂ ∶ τ₂
-- Variable
| var : ⊢ Γ → Γ ∋ x ∶ τ
      ------------------
     → Γ ⊢ # x ∶ τ
-- Universe
| u : ⊢ Γ
    ----------------------
   → Γ ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1)
-- Pi
| pi  : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ₁ → Γ ∷ τ₁ ⊢ υ₁ ≡ υ₂ ∶ 𝓤 ℓ₂
      ------------------------------------------------
     → Γ ⊢ Π τ₁ υ₁ ≡ Π τ₂ υ₂ ∶ 𝓤 (max ℓ₁ ℓ₂)
-- Alecs(TODO): Figure out how to drop the well formedness of υ
| lam : Γ ∷ τ₁ ⊢ υ ∶ 𝓤 ℓ' → Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ → Γ ∷ τ₁ ⊢ t₁ ≡ t₂ ∶ υ
      ----------------------------------------------------------------
     → Γ ⊢ ƛ τ₁ t₁ ≡ ƛ τ₂ t₂ ∶ (Π τ₁ υ)
| app : Γ ⊢ t₁ ≡ t₂ ∶ (Π τ υ) → Γ ⊢ m₁ ≡ m₂ ∶ τ
      ------------------------------------------
     → Γ ⊢ t₁ • m₁ ≡ t₂ • m₂ ∶ υ [/ m₁ ]
| lamβ : Γ ⊢ τ ∶ 𝓤 ℓ → Γ ∷ τ ⊢ υ ∶ 𝓤 ℓ' → Γ ∷ τ ⊢ t ∶ υ → Γ ⊢ m ∶ τ
       -----------------------------------------------------------------
      → Γ ⊢ (ƛ τ t) • m ≡ t [/ m ] ∶ υ [/ m ]
| lamη : Γ ⊢ t ∶ Π τ υ
       -----------------------------------
      → Γ ⊢ t ≡ ƛ τ (↑ t) • # 0 ∶ Π τ υ
-- Identity
| id : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ → Γ ⊢ a₁ ≡ a₂ ∶ τ₁ → Γ ⊢ b₁ ≡ b₂ ∶ τ₁
     ------------------------------------------------------------
    → Γ ⊢ Id τ₁ a₁ b₁ ≡ Id τ₂ a₂ b₂ ∶ 𝓤 ℓ
| refl : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ → Γ ⊢ a₁ ≡ a₂ ∶ τ₁
       -------------------------------------------
      → Γ ⊢ refl τ₁ a₁ ≡ refl τ₂ a₂ ∶ Id τ₁ a₁ a₁
| j : {a : Tm n} → Γ ⊢ τ ∶ 𝓤 ℓ₁ → Γ ∷ τ ⊢ Id (↑ τ) (↑ a) # 0 ∶ 𝓤 ℓ₁
   → Γ ∷ τ ∷ Id (↑ τ) (↑ a) # 0 ⊢ C₁ ≡ C₂ ∶ 𝓤 ℓ
   → Γ ⊢ d₁ ≡ d₂ ∶ C₁ [/ refl (↑ τ) (↑ a) ] [/ a ] → Γ ⊢ p₁ ≡ p₂ ∶ Id τ a b
    ---------------------------------------------------------------------------
   → Γ ⊢ J C₁ d₁ p₁ ≡ J C₂ d₂ p₂ ∶ C₁ [/ ↑ p₁ ] [/ b ]
| jβ : Γ ⊢ τ ∶ 𝓤 ℓ₁ → Γ ⊢ a ∶ τ
    →  Γ ∷ τ ⊢ Id (↑ τ) (↑ a) # 0 ∶ 𝓤 ℓ₁
    →  Γ ∷ τ ∷ Id (↑ τ) (↑ a) # 0 ⊢ C ∶ 𝓤 ℓ
    →  Γ ⊢ d ∶ C [/ refl (↑ τ) (↑ a) ] [/ a ]
     --------------------------------------------------------------
    →  Γ ⊢ J C d (refl τ a) ≡ d ∶ C [/ refl (↑ τ) (↑ a) ] [/ a ]
end
end

theorem DefEq.wf_left (h : Γ ⊢ t ≡ t' ∶ τ) : Γ ⊢ t ∶ τ :=
  h.trans h.symm

theorem DefEq.wf_right (h : Γ ⊢ t ≡ t' ∶ τ) : Γ ⊢ t' ∶ τ :=
  h.symm.trans h
