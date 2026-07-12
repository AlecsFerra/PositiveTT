import SPos.Typing.WellTyped
import SPos.Syntax.SyntaxProperties
import SPos.Semantics.EvalProperties
import SPos.Semantics.Decode

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

variable {D : Type u} [ScottDomain D Label]

local notation "DEnv" => Env (fun _ => D)

/-- `ρ ∼ ρ' ⊨ Γ`: pointwise-related environments — the values of each variable are
related in the common PER decoding its type. -/
def Models (ρ ρ' : DEnv n) (Γ : Ctx n) : Prop :=
  ∀ {i : Fin n} {τ : Tm n}, (Γ ∋ i ∶ τ) →
    ∃ (ℓ : Nat) (X : PER D), Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') X ∧ (ρ.get i ~ ρ'.get i ∈ₚ X)

local notation:40 ρ:41 " ∼ " ρ':41 " ⊨ " Γ:41 => Models ρ ρ' Γ

theorem Models.nil (ρ ρ' : DEnv 0) : ρ ∼ ρ' ⊨ (∅ : Ctx 0) :=
  fun {i} {_} _ => i.elim0

theorem Models.refl_left {ρ ρ' : DEnv n} {Γ : Ctx n} (hρ : ρ ∼ ρ' ⊨ Γ) : ρ ∼ ρ ⊨ Γ := by
  intro i τ hlook
  obtain ⟨ℓ, X, hX, hmem⟩ := hρ hlook
  exact ⟨ℓ, X, hX.refl_left, X.refl_left hmem⟩

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

/-- Extending related environments by values related in the pushed type. -/
theorem Models.cons {ρ ρ' : DEnv n} {Γ : Ctx n} (hρ : ρ ∼ ρ' ⊨ Γ) {τ : Tm n} {ℓ : Nat}
    {A : PER D} (hA : Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') A)
    {d d' : D} (hd : d ~ d' ∈ₚ A) : (ρ ∷ d) ∼ (ρ' ∷ d') ⊨ (Γ ∷ τ) := by
  intro i σ hlook
  rcases hlook.cons_inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · exact ⟨ℓ, A, by simpa only [Tm.eval_weaken] using hA, by simpa using hd⟩
  · obtain ⟨k, X, hX, hmem⟩ := hρ hj
    exact ⟨k, X, by simpa only [Tm.eval_weaken] using hX, by simpa using hmem⟩

/-- Fundamental theorem of the PER model: a well-typed term evaluated in related
environments yields related values in the PER decoding its type. In particular
functions are identified extensionally. -/
theorem WfTm.sound : ∀ {n : Nat} {Γ : Ctx n} {t τ : Tm n}, (Γ ⊢ t ∶ τ) →
    ∀ {ρ ρ' : DEnv n}, (ρ ∼ ρ' ⊨ Γ) →
    ∃ (ℓ : Nat) (X : PER D), Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') X ∧ (⟦ t ⟧𝒄 ρ ~ ⟦ t ⟧𝒄 ρ' ∈ₚ X)
  | _, _, _, _, .var _ hlook, _, _, hρ => hρ hlook
  | _, _, _, _, .u (ℓ := ℓ) _, ρ, ρ', _ => by
    refine ⟨ℓ + 2, U (ℓ + 1), ?_, ?_⟩
    · simpa [Tm.eval] using Decode.univ (D := D) (ℓ := ℓ + 1) (by omega)
    · refine mem_U.mpr ⟨U ℓ, ?_⟩
      simpa [Tm.eval] using Decode.univ (D := D) (ℓ := ℓ) (k := ℓ + 1) (by omega)
  | _, Γ, .pi τ υ, _, .pi (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτ hυ, ρ, ρ', hρ => by
    obtain ⟨k, Xτ, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) (⟦ υ ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨k', Xυ, hk', hmemυ⟩ := WfTm.sound hυ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨k', Xυ, hk', hmemυ⟩ := WfTm.sound hυ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    refine ⟨max ℓ₁ ℓ₂ + 1, U (max ℓ₁ ℓ₂), ?_, ?_⟩
    · simpa [Tm.eval] using Decode.univ (D := D) (ℓ := max ℓ₁ ℓ₂) (by omega)
    · exact mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩
  | _, Γ, .lam τ t, _, .lam (ℓ := ℓ₁) (ℓ' := ℓ₂) (σ := σ) hτ hσ ht, ρ, ρ', hρ => by
    obtain ⟨k, Xτ, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) (⟦ σ ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨k', Xσ, hk', hmemσ⟩ := WfTm.sound hσ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemσ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨k', Xσ, hk', hmemσ⟩ := WfTm.sound hσ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemσ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    refine ⟨max ℓ₁ ℓ₂, _, by simpa [Tm.eval] using hpi, ?_⟩
    intro d d' hdd'
    obtain ⟨k'', Xt, hk'', hmemt⟩ := WfTm.sound ht (hρ.cons hA hdd')
    obtain rfl := hk''.det (hB hdd')
    simpa [Tm.eval, ScottDomain.lam.ret_inj] using hmemt
  | _, Γ, .app t s, _, .app ht hs, ρ, ρ', hρ => by
    obtain ⟨k, X, hk, hmemt⟩ := WfTm.sound ht hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    obtain ⟨k', X', hk', hmems⟩ := WfTm.sound hs hρ
    obtain rfl := hk'.det hA
    refine ⟨k, B (⟦ s ⟧𝒄 ρ), ?_, ?_⟩
    · simpa only [Tm.eval_subst1, mk_lam_apply] using hB hmems
    · simpa [Tm.eval] using hmemt _ _ hmems

/-- Soundness, packaged with `El`: well-typed terms in related environments are
related in the `El` of their type. -/
theorem WfTm.sound_el {Γ : Ctx n} {t τ : Tm n} {ℓ : Nat}
    (h : Γ ⊢ t ∶ τ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) {ρ ρ' : DEnv n} (hρ : ρ ∼ ρ' ⊨ Γ) :
    ⟦ t ⟧𝒄 ρ ~ ⟦ t ⟧𝒄 ρ' ∈ₚ El ℓ (⟦ τ ⟧𝒄 ρ) := by
  obtain ⟨k, X, hk, hmem⟩ := h.sound hρ
  obtain ⟨k', X', hk', hmem'⟩ := hτ.sound hρ
  simp only [Tm.eval, mk_lam_apply] at hk'
  obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
  obtain rfl := hk.det (Decode.el hmem')
  exact hmem
