import SPos.Typing.WellTyped
import SPos.SyntaxProperties
import SPos.Semantics.EvalProperties
import SPos.Semantics.Decode

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

variable {D : Type u} [ScottDomain D Label]

local notation "DEnv" => Env (fun _ => D)

/-- `ρ ⊨ Γ`: every variable's value inhabits the decoding of its type. -/
def Models (ρ : DEnv n) (Γ : Ctx n) : Prop :=
  ∀ {i : Fin n} {τ : Tm n}, (Γ ∋ i ∶ τ) → ∃ ℓ X, Decode ℓ (⟦ τ ⟧𝒄 ρ) X ∧ ρ.get i ∈ X

local notation:40 ρ:41 " ⊨ " Γ:41 => Models ρ Γ

theorem Models.nil (ρ : DEnv 0) : ρ ⊨ (∅ : Ctx 0) :=
  fun {i} {_} _ => i.elim0

private theorem Lookup.cons_inv {Δ : Ctx (n + 1)} {i : Fin (n + 1)} {σ : Tm (n + 1)}
    (h : Δ ∋ i ∶ σ) {Γ : Ctx n} {τ : Tm n} (hΔ : Δ = Γ ∷ τ) :
    (i = 0 ∧ σ = τ.weaken) ∨ ∃ j τ', i = j.succ ∧ σ = τ'.weaken ∧ (Γ ∋ j ∶ τ') := by
  cases h with
  | here =>
    obtain ⟨rfl, rfl⟩ := Env.cons_inj hΔ
    exact .inl ⟨rfl, rfl⟩
  | there hj =>
    obtain ⟨rfl, rfl⟩ := Env.cons_inj hΔ
    exact .inr ⟨_, _, rfl, rfl, hj⟩

/-- Extending a good environment by an element of the (decoded) pushed type. -/
theorem Models.cons {ρ : DEnv n} {Γ : Ctx n} (hρ : ρ ⊨ Γ) {τ : Tm n} {ℓ : Nat} {A : Set D}
    (hA : Decode ℓ (⟦ τ ⟧𝒄 ρ) A) {d : D} (hd : d ∈ A) : (ρ ∷ d) ⊨ (Γ ∷ τ) := by
  intro i σ hlook
  rcases hlook.cons_inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · exact ⟨ℓ, A, by simpa only [Tm.eval_weaken] using hA, by simpa using hd⟩
  · obtain ⟨k, X, hX, hmem⟩ := hρ hj
    exact ⟨k, X, by simpa only [Tm.eval_weaken] using hX, by simpa using hmem⟩

/-- Fundamental theorem: a well-typed term inhabits the decoding of its type. -/
theorem WfTm.sound : ∀ {n : Nat} {Γ : Ctx n} {t τ : Tm n}, (Γ ⊢ t ∶ τ) →
    ∀ {ρ : DEnv n}, (ρ ⊨ Γ) → ∃ ℓ X, Decode ℓ (⟦ τ ⟧𝒄 ρ) X ∧ ⟦ t ⟧𝒄 ρ ∈ X
  | _, _, _, _, .var _ hlook, _, hρ => hρ hlook
  | _, _, _, _, .u (ℓ := ℓ) _, ρ, _ => by
    refine ⟨ℓ + 2, U (ℓ + 1), ?_, U ℓ, ?_⟩
    · simpa [Tm.eval] using Decode.univ (ℓ := ℓ + 1) (by omega)
    · simpa [Tm.eval] using Decode.univ (ℓ := ℓ) (k := ℓ + 1) (by omega)
  | _, Γ, .pi τ υ, _, .pi (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτ hυ, ρ, hρ => by
    obtain ⟨k, Xτ, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := hmemτ
    have hB : ∀ d ∈ A, Decode ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) (El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) := by
      intro d hd
      obtain ⟨k', Xυ, hk', hmemυ⟩ := WfTm.sound hυ (hρ.cons hA hd)
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    refine ⟨max ℓ₁ ℓ₂ + 1, U (max ℓ₁ ℓ₂), ?_, ?_⟩
    · simpa [Tm.eval] using Decode.univ (ℓ := max ℓ₁ ℓ₂) (by omega)
    · have hpi := Decode.pi (f := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ ∷ d))
          (B := fun d => El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)))
          (hA.cumul (le_max_left ℓ₁ ℓ₂))
          (fun d hd => by simpa using (hB d hd).cumul (le_max_right ℓ₁ ℓ₂))
      exact ⟨_, by simpa [Tm.eval] using hpi⟩
  | _, Γ, .lam τ t, _, .lam (ℓ := ℓ₁) (ℓ' := ℓ₂) (σ := σ) hτ hσ ht, ρ, hρ => by
    obtain ⟨k, Xτ, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := hmemτ
    have hB : ∀ d ∈ A, Decode ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) (El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) := by
      intro d hd
      obtain ⟨k', Xσ, hk', hmemσ⟩ := WfTm.sound hσ (hρ.cons hA hd)
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemσ
    refine ⟨max ℓ₁ ℓ₂, _,
      by simpa [Tm.eval] using
        Decode.pi (f := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ ∷ d))
          (B := fun d => El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)))
          (hA.cumul (le_max_left ℓ₁ ℓ₂))
          (fun d hd => by simpa using (hB d hd).cumul (le_max_right ℓ₁ ℓ₂)), ?_⟩
    intro d hd
    obtain ⟨k'', Xt, hk'', hmemt⟩ := WfTm.sound ht (hρ.cons hA hd)
    obtain rfl := hk''.det (hB d hd)
    simpa [Tm.eval, ScottDomain.lam.ret_inj] using hmemt
  | _, Γ, .app t s, _, .app ht hs, ρ, hρ => by
    obtain ⟨k, X, hk, hmemt⟩ := WfTm.sound ht hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨A, B, hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨k', X', hk', hmems⟩ := WfTm.sound hs hρ
    obtain rfl := hk'.det hA
    refine ⟨k, B (⟦ s ⟧𝒄 ρ), ?_, ?_⟩
    · simpa only [Tm.eval_subst1, mk_lam_apply] using hB _ hmems
    · simpa [Tm.eval] using hmemt _ hmems

/-- Soundness, packaged with `El`: `Γ ⊢ t ∶ τ → ⟦t⟧ρ ∈ El ℓ ⟦τ⟧ρ`. -/
theorem WfTm.sound_el {Γ : Ctx n} {t τ : Tm n} {ℓ : Nat}
    (h : Γ ⊢ t ∶ τ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) {ρ : DEnv n} (hρ : ρ ⊨ Γ) :
    ⟦ t ⟧𝒄 ρ ∈ El ℓ (⟦ τ ⟧𝒄 ρ) := by
  obtain ⟨k, X, hk, hmem⟩ := h.sound hρ
  obtain ⟨k', X', hk', hmem'⟩ := hτ.sound hρ
  simp only [Tm.eval, mk_lam_apply] at hk'
  obtain ⟨-, rfl⟩ := decode_univ_inv hk'
  obtain rfl := hk.det (Decode.el hmem')
  exact hmem
