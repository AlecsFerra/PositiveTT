import SPos.Typing.Typing
import SPos.Typing.TypingProperties
import SPos.Syntax.SyntaxProperties
import SPos.Semantics.EvalProperties
import SPos.Semantics.Decode

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

variable {D : Type u} [ScottDomain D Label]

local notation "DEnv" => Env (fun _ => D)

-- `ρ ∼ ρ' ⊨ Γ`: pointwise-related environments in the PER decoding each type.
def Models (ρ ρ' : DEnv n) (Γ : Ctx n) : Prop :=
  ∀ {i : Fin n} {τ : Tm n}, (Γ ∋ i ∶ τ) →
    ∃ (ℓ : Nat) (X : PER D), Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') X ∧ (ρ.get i ~ ρ'.get i ∈ₚ X)

local notation:40 ρ:41 " ∼ " ρ':41 " ⊨ " Γ:41 => Models ρ ρ' Γ

theorem Models.nil (ρ ρ' : DEnv 0) : ρ ∼ ρ' ⊨ (∅ : Ctx 0) :=
  fun {i} {_} _ => i.elim0

theorem Models.refl_left {ρ ρ' : DEnv n} (hρ : ρ ∼ ρ' ⊨ Γ) : ρ ∼ ρ ⊨ Γ := by
  intro i τ hlook
  obtain ⟨ℓ, X, hX, hmem⟩ := hρ hlook
  exact ⟨ℓ, X, hX.refl_left, X.refl_left hmem⟩

theorem Models.symm {ρ ρ' : DEnv n} (hρ : ρ ∼ ρ' ⊨ Γ) : ρ' ∼ ρ ⊨ Γ := by
  intro i τ hlook
  obtain ⟨ℓ, X, hX, hmem⟩ := hρ hlook
  exact ⟨ℓ, X, hX.symm, X.symm hmem⟩

-- Extending related environments by values related in the pushed type.
theorem Models.cons {ρ ρ' : DEnv n} (hρ : ρ ∼ ρ' ⊨ Γ) (hA : Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') A)
    (hd : d ~ d' ∈ₚ A) : (ρ ∷ d) ∼ (ρ' ∷ d') ⊨ (Γ ∷ τ) := by
  intro i σ hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · exact ⟨ℓ, A, by simpa only [Tm.eval_weaken] using hA, by simpa using hd⟩
  · obtain ⟨k, X, hX, hmem⟩ := hρ hj
    exact ⟨k, X, by simpa only [Tm.eval_weaken] using hX, by simpa using hmem⟩

-- Fundamental theorem: well-typed / definitionally-equal terms evaluated in
-- related environments yield related values in the PER decoding their type.
-- (Term-mode structural recursion: `WfTm`/`DefEq` are mutually inductive with
-- `WfCtx`, which the `induction` tactic does not support.)
mutual
theorem WfTm.sound : ∀ {n : Nat} {Γ : Ctx n} {t τ : Tm n}, (Γ ⊢ t ∶ τ) →
    ∀ {ρ ρ' : DEnv n}, (ρ ∼ ρ' ⊨ Γ) →
    ∃ (ℓ : Nat) (X : PER D), Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') X ∧ (⟦ t ⟧𝒄 ρ ~ ⟦ t ⟧𝒄 ρ' ∈ₚ X)
  | _, _, _, _, .var _ hlook, _, _, hρ => hρ hlook
  | _, _, _, σ, .conv (τ := τ) (ℓ := ℓc) ht _ hτσ, ρ, ρ', hρ => by
    obtain ⟨ℓ', X, hX, hmem⟩ := WfTm.sound ht hρ
    obtain ⟨ℓ₁, Y, hYU, hcross⟩ := DefEq.sound hτσ hρ
    simp only [Tm.eval, mk_lam_apply] at hYU
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hYU
    obtain ⟨Z, hZ⟩ := mem_U.mp hcross
    obtain rfl := hX.det hZ
    obtain ⟨ℓ₂, Y', hYU', hself⟩ := DefEq.sound hτσ hρ.refl_left
    simp only [Tm.eval, mk_lam_apply] at hYU'
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hYU'
    obtain ⟨W, hW⟩ := mem_U.mp hself
    obtain rfl := hX.det hW
    exact ⟨ℓc, X, hW.symm.trans hZ, hmem⟩
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

-- Semantic soundness of typed conversion: interchangeable terms denote
-- related values in the PER decoding their shared type.
theorem DefEq.sound : ∀ {n : Nat} {Γ : Ctx n} {t t' τ : Tm n}, (Γ ⊢ t ≡ t' ∶ τ) →
    ∀ {ρ ρ' : DEnv n}, (ρ ∼ ρ' ⊨ Γ) →
    ∃ (ℓ : Nat) (X : PER D), Decode ℓ (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') X ∧ (⟦ t ⟧𝒄 ρ ~ ⟦ t' ⟧𝒄 ρ' ∈ₚ X)
  | _, _, _, _, _, .refl ht, ρ, ρ', hρ => WfTm.sound ht hρ
  | _, _, _, _, _, .symm h, ρ, ρ', hρ => by
    obtain ⟨ℓ, X, hX, hrel⟩ := DefEq.sound h hρ.symm
    exact ⟨ℓ, X, hX.symm, X.symm hrel⟩
  | _, _, _, _, _, .trans h₁ h₂, ρ, ρ', hρ => by
    obtain ⟨ℓ₁, X₁, hX₁, hrel₁⟩ := DefEq.sound h₁ hρ.refl_left
    obtain ⟨ℓ₂, X₂, hX₂, hrel₂⟩ := DefEq.sound h₂ hρ
    obtain rfl := hX₁.det hX₂
    exact ⟨ℓ₂, X₁, hX₂, X₁.trans hrel₁ hrel₂⟩
  | _, Γ, .pi τ υ, .pi _ υ', _, .pi (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτwf hυwf hτ hυ, ρ, ρ', hρ => by
    obtain ⟨k, Xτ, hk, hmemτ⟩ := WfTm.sound hτwf hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    obtain ⟨k₂, X₂, hk₂, hrelτ⟩ := DefEq.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A', hA'⟩ := mem_U.mp hrelτ
    obtain rfl := hA.det hA'
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) (⟦ υ' ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨k', Xυ, hk', hmemυ⟩ := DefEq.sound hυ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨k', Xυ, hk', hmemυ⟩ := WfTm.sound hυwf (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ υ' ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA'.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    refine ⟨max ℓ₁ ℓ₂ + 1, U (max ℓ₁ ℓ₂), ?_, ?_⟩
    · simpa [Tm.eval] using Decode.univ (D := D) (ℓ := max ℓ₁ ℓ₂) (by omega)
    · exact mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩
  | _, Γ, .lam τ t, .lam _ t', _, .lam (ℓ := ℓ₁) (ℓ' := ℓ₂) (σ := σ) hτ hσ ht, ρ, ρ', hρ => by
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
    obtain ⟨k'', Xt, hk'', hmemt⟩ := DefEq.sound ht (hρ.cons hA hdd')
    obtain rfl := hk''.det (hB hdd')
    simpa [Tm.eval, ScottDomain.lam.ret_inj] using hmemt
  | _, _, .app t m, .app t' m', _, .app ht' hmwf hm', ρ, ρ', hρ => by
    obtain ⟨k, X, hk, hmemt⟩ := DefEq.sound ht' hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    obtain ⟨k', X', hk', hmems⟩ := WfTm.sound hmwf hρ
    obtain rfl := hk'.det hA
    obtain ⟨k'', X'', hk'', hmemm⟩ := DefEq.sound hm' hρ
    obtain rfl := hk''.det hA
    refine ⟨k, B (⟦ m ⟧𝒄 ρ), ?_, ?_⟩
    · simpa only [Tm.eval_subst1, mk_lam_apply] using hB hmems
    · simpa [Tm.eval] using hmemt _ _ hmemm
  | _, _, .app _ m, _, _, .β hlam hm, ρ, ρ', hρ => by
    obtain ⟨k, X, hk, hmemt⟩ := WfTm.sound hlam hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    obtain ⟨k', X', hk', hmems⟩ := WfTm.sound hm hρ
    obtain rfl := hk'.det hA
    refine ⟨k, B (⟦ m ⟧𝒄 ρ), ?_, ?_⟩
    · simpa only [Tm.eval_subst1, mk_lam_apply] using hB hmems
    · simpa [Tm.eval, Tm.eval_subst1, ScottDomain.lam.ret_inj] using hmemt _ _ hmems
  | n, _, t, _, _, .eta ht, ρ, ρ', hρ => by
    obtain ⟨ℓ, X, hX, hf⟩ := WfTm.sound ht hρ
    simp only [Tm.eval, mk_lam_apply] at hX
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hX
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    refine ⟨ℓ, PER.pi A B, by simpa [Tm.eval] using Decode.pi hA hB, ?_⟩
    simp only [Tm.eval, mk_lam_apply]
    intro x y hxy
    have : ⟦ Tm.app t.weaken (Tm.var (0 : Fin (n + 1))) ⟧𝒄 (ρ' ∷ x) = ⟦ t ⟧𝒄 ρ' •𝒄 x := by
      simp [Tm.eval]
    simpa [ScottDomain.lam.ret_inj, this] using hf x y hxy
end

-- Soundness, packaged with `El`: related terms land in the `El` of their type.
theorem WfTm.sound_el {ρ ρ' : DEnv n}
    (h : Γ ⊢ t ∶ τ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hρ : ρ ∼ ρ' ⊨ Γ) :
    ⟦ t ⟧𝒄 ρ ~ ⟦ t ⟧𝒄 ρ' ∈ₚ El ℓ (⟦ τ ⟧𝒄 ρ) := by
  obtain ⟨k, X, hk, hmem⟩ := h.sound hρ
  obtain ⟨k', X', hk', hmem'⟩ := hτ.sound hρ
  simp only [Tm.eval, mk_lam_apply] at hk'
  obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
  obtain rfl := hk.det (Decode.el hmem')
  exact hmem
