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

-- Fundamental theorem: well-typed / definitionally-equal terms evaluated in related
-- environments yield related values in the `El` of their type, whose code is itself
-- related in the universe (`… ∈ₚ U ℓ`).  The `U`-conjunct records that the type
-- denotation is coherent across `ρ` and `ρ'` (`El` alone only sees the left one),
-- which conversion and `symm` need; the residual `∃ ℓ : Nat` is level bookkeeping.
-- (Term-mode structural recursion on the derivation: `WfTm`/`DefEq` are mutually
-- inductive with `WfCtx`, which the `induction` tactic does not support.)
mutual
theorem WfTm.sound {Γ : Ctx n} {t τ : Tm n} (ht : Γ ⊢ t ∶ τ) {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨ Γ) :
    ∃ ℓ, (⟦ τ ⟧𝒄 ρ ~ ⟦ τ ⟧𝒄 ρ' ∈ₚ U ℓ) ∧ (⟦ t ⟧𝒄 ρ ~ ⟦ t ⟧𝒄 ρ' ∈ₚ El ℓ (⟦ τ ⟧𝒄 ρ)) :=
  match ht with
  | .var _ hlook => by
    obtain ⟨ℓ, X, hX, hmem⟩ := hρ hlook
    exact ⟨ℓ, mem_U.mpr ⟨X, hX⟩, X, hX.refl_left, hmem⟩
  | .conv ht _ hτσ => by
    obtain ⟨_, hUτ, hElt⟩ := WfTm.sound ht hρ
    obtain ⟨X, hX⟩ := mem_U.mp hUτ
    rw [El_eq_of_decode hX] at hElt
    obtain ⟨_, _, _, hY, hcross⟩ := DefEq.sound hτσ hρ
    simp only [Tm.eval, mk_lam_apply] at hY
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hY
    obtain ⟨Z, hZ⟩ := mem_U.mp hcross
    obtain rfl := hX.det hZ
    obtain ⟨_, _, _, hY', hself⟩ := DefEq.sound hτσ hρ.refl_left
    simp only [Tm.eval, mk_lam_apply] at hY'
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hY'
    obtain ⟨W, hW⟩ := mem_U.mp hself
    obtain rfl := hX.det hW
    exact ⟨_, mem_U.mpr ⟨_, hW.symm.trans hZ⟩, _, (hW.symm.trans hZ).refl_left, hElt⟩
  | .u (ℓ := ℓ) _ => by
    have hu : Decode (ℓ + 2) (mkU (ℓ + 1) : D) (mkU (ℓ + 1)) (U (ℓ + 1)) := Decode.univ (by omega)
    exact ⟨ℓ + 2, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _, by simpa [Tm.eval] using hu,
      mem_U.mpr ⟨U ℓ, by simpa [Tm.eval] using Decode.univ (D := D) (ℓ := ℓ) (k := ℓ + 1) (by omega)⟩⟩
  | .pi (τ := τ) (υ := υ) (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτ hυ => by
    obtain ⟨_, _, _, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) (⟦ υ ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ := WfTm.sound hυ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ :=
        WfTm.sound hυ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    have hu : Decode (max ℓ₁ ℓ₂ + 1) (mkU (max ℓ₁ ℓ₂) : D) (mkU (max ℓ₁ ℓ₂)) (U (max ℓ₁ ℓ₂)) :=
      Decode.univ (by omega)
    exact ⟨max ℓ₁ ℓ₂ + 1, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _,
      by simpa [Tm.eval] using hu, mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩⟩
  | .lam (σ := σ) (ℓ := ℓ₁) (ℓ' := ℓ₂) hτ hσ ht => by
    obtain ⟨_, _, _, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) (⟦ σ ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemσ⟩ := WfTm.sound hσ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemσ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemσ⟩ :=
        WfTm.sound hσ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemσ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    refine ⟨max ℓ₁ ℓ₂, mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩, _,
      by simpa [Tm.eval] using hpi.refl_left, ?_⟩
    intro d d' hdd'
    obtain ⟨_, _, _, hk'', hmemt⟩ := WfTm.sound ht (hρ.cons hA hdd')
    obtain rfl := hk''.det (hB hdd')
    simpa [Tm.eval, ScottDomain.lam.ret_inj] using hmemt
  | .app (σ := σ) (m := s) ht hs => by
    obtain ⟨k, hU, hElt⟩ := WfTm.sound ht hρ
    obtain ⟨X, hk⟩ := mem_U.mp hU
    rw [El_eq_of_decode hk] at hElt
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    obtain ⟨_, _, _, hk', hmems⟩ := WfTm.sound hs hρ
    obtain rfl := hk'.det hA
    have hd : Decode k (⟦ σ [/ s ] ⟧𝒄 ρ) (⟦ σ [/ s ] ⟧𝒄 ρ') (B (⟦ s ⟧𝒄 ρ)) := by
      simpa only [Tm.eval_subst1, mk_lam_apply] using hB hmems
    exact ⟨_, mem_U.mpr ⟨_, hd⟩, _, hd.refl_left, by simpa [Tm.eval] using hElt _ _ hmems⟩

theorem DefEq.sound {Γ : Ctx n} {t t' τ : Tm n} (ht : Γ ⊢ t ≡ t' ∶ τ) {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨ Γ) :
    ∃ ℓ, (⟦ τ ⟧𝒄 ρ ~ ⟦ τ ⟧𝒄 ρ' ∈ₚ U ℓ) ∧ (⟦ t ⟧𝒄 ρ ~ ⟦ t' ⟧𝒄 ρ' ∈ₚ El ℓ (⟦ τ ⟧𝒄 ρ)) :=
  match ht with
  | .refl ht => WfTm.sound ht hρ
  | .symm h => by
    obtain ⟨_, hU, hEl⟩ := DefEq.sound h hρ.symm
    obtain ⟨X, hX⟩ := mem_U.mp hU
    rw [El_eq_of_decode hX] at hEl
    exact ⟨_, mem_U.mpr ⟨_, hX.symm⟩, _, hX.symm.refl_left, X.symm hEl⟩
  | .trans h₁ h₂ => by
    obtain ⟨_, _, X₁, hX₁, hrel₁⟩ := DefEq.sound h₁ hρ.refl_left
    obtain ⟨_, hU, hEl₂⟩ := DefEq.sound h₂ hρ
    obtain ⟨X₂, hX₂⟩ := mem_U.mp hU
    rw [El_eq_of_decode hX₂] at hEl₂
    have hXeq := hX₁.det hX₂
    exact ⟨_, mem_U.mpr ⟨_, hX₂⟩, _, hX₂.refl_left, X₂.trans (hXeq ▸ hrel₁) hEl₂⟩
  | .pi (τ := τ) (υ := υ) (υ' := υ') (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτwf hυwf hτ hυ => by
    obtain ⟨_, _, _, hk, hmemτ⟩ := WfTm.sound hτwf hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    obtain ⟨_, _, _, hk₂, hrelτ⟩ := DefEq.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A', hA'⟩ := mem_U.mp hrelτ
    obtain rfl := hA.det hA'
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) (⟦ υ' ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ := DefEq.sound hυ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ :=
        WfTm.sound hυwf (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ υ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ υ' ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ υ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA'.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    have hu : Decode (max ℓ₁ ℓ₂ + 1) (mkU (max ℓ₁ ℓ₂) : D) (mkU (max ℓ₁ ℓ₂)) (U (max ℓ₁ ℓ₂)) :=
      Decode.univ (by omega)
    exact ⟨max ℓ₁ ℓ₂ + 1, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _,
      by simpa [Tm.eval] using hu, mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩⟩
  | .lam (σ := σ) (ℓ := ℓ₁) (ℓ' := ℓ₂) hτ hσ ht => by
    obtain ⟨_, _, _, hk, hmemτ⟩ := WfTm.sound hτ hρ
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    have hB : ∀ {d d' : D}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) (⟦ σ ⟧𝒄 (ρ' ∷ d')) (El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemσ⟩ := WfTm.sound hσ (hρ.cons hA hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemσ
    have hcoh : ∀ (d d' : D), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d)) = El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemσ⟩ :=
        WfTm.sound hσ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp only [Tm.eval, mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemσ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ ∷ d)) (f' := ƛ[ by fun_prop ] d ↦ ⟦ σ ⟧𝒄 (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D)) (fun d => El ℓ₂ (⟦ σ ⟧𝒄 (ρ ∷ d))) hcoh)
      (hA.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    refine ⟨max ℓ₁ ℓ₂, mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩, _,
      by simpa [Tm.eval] using hpi.refl_left, ?_⟩
    intro d d' hdd'
    obtain ⟨_, _, _, hk'', hmemt⟩ := DefEq.sound ht (hρ.cons hA hdd')
    obtain rfl := hk''.det (hB hdd')
    simpa [Tm.eval, ScottDomain.lam.ret_inj] using hmemt
  | .app (σ := σ) (m := m) ht' hmwf hm' => by
    obtain ⟨k, hU, hElt⟩ := DefEq.sound ht' hρ
    obtain ⟨X, hk⟩ := mem_U.mp hU
    rw [El_eq_of_decode hk] at hElt
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    obtain ⟨_, _, _, hk', hmems⟩ := WfTm.sound hmwf hρ
    obtain rfl := hk'.det hA
    obtain ⟨_, _, _, hk'', hmemm⟩ := DefEq.sound hm' hρ
    obtain rfl := hk''.det hA
    have hd : Decode k (⟦ σ [/ m ] ⟧𝒄 ρ) (⟦ σ [/ m ] ⟧𝒄 ρ') (B (⟦ m ⟧𝒄 ρ)) := by
      simpa only [Tm.eval_subst1, mk_lam_apply] using hB hmems
    exact ⟨_, mem_U.mpr ⟨_, hd⟩, _, hd.refl_left, by simpa [Tm.eval] using hElt _ _ hmemm⟩
  | .β (σ := σ) (m := m) hlam hm => by
    obtain ⟨k, hU, hElt⟩ := WfTm.sound hlam hρ
    obtain ⟨X, hk⟩ := mem_U.mp hU
    rw [El_eq_of_decode hk] at hElt
    simp only [Tm.eval, mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    obtain ⟨_, _, _, hk', hmems⟩ := WfTm.sound hm hρ
    obtain rfl := hk'.det hA
    have hd : Decode k (⟦ σ [/ m ] ⟧𝒄 ρ) (⟦ σ [/ m ] ⟧𝒄 ρ') (B (⟦ m ⟧𝒄 ρ)) := by
      simpa only [Tm.eval_subst1, mk_lam_apply] using hB hmems
    exact ⟨_, mem_U.mpr ⟨_, hd⟩, _, hd.refl_left,
      by simpa [Tm.eval, Tm.eval_subst1, ScottDomain.lam.ret_inj] using hElt _ _ hmems⟩
  | .η hη => by
    obtain ⟨_, hU, hElt⟩ := WfTm.sound hη hρ
    obtain ⟨X, hX⟩ := mem_U.mp hU
    rw [El_eq_of_decode hX] at hElt
    simp only [Tm.eval, mk_lam_apply] at hX
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hX
    obtain ⟨rfl, rfl⟩ := mkPi_inj hc'
    refine ⟨_, mem_U.mpr ⟨_, by simpa [Tm.eval] using Decode.pi hA hB⟩, _,
      by simpa [Tm.eval] using (Decode.pi hA hB).refl_left, ?_⟩
    simp only [Tm.eval, mk_lam_apply]
    intro x y hxy
    have : ⟦ Tm.app t.weaken (Tm.var (0 : Fin (n + 1))) ⟧𝒄 (ρ' ∷ x) = ⟦ t ⟧𝒄 ρ' •𝒄 x := by
      simp [Tm.eval]
    simpa [ScottDomain.lam.ret_inj, this] using hElt x y hxy
end

-- Soundness in the `El`-form fixed by a chosen typing `Γ ⊢ τ ∶ 𝓤 ℓ`: the level is
-- the hypothesis's, not existentially bundled. (`El` is level-independent, so this
-- pins the bundled `∃ ℓ` to the syntactic witness.)
theorem WfTm.sound_el {ρ ρ' : DEnv n}
    (h : Γ ⊢ t ∶ τ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hρ : ρ ∼ ρ' ⊨ Γ) :
    ⟦ t ⟧𝒄 ρ ~ ⟦ t ⟧𝒄 ρ' ∈ₚ El ℓ (⟦ τ ⟧𝒄 ρ) := by
  obtain ⟨_, hU, hEl⟩ := h.sound hρ
  obtain ⟨X, hk⟩ := mem_U.mp hU
  rw [El_eq_of_decode hk] at hEl
  obtain ⟨_, _, _, hk', hmem'⟩ := hτ.sound hρ
  simp only [Tm.eval, mk_lam_apply] at hk'
  obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
  obtain rfl := hk.det (Decode.el hmem')
  exact hEl
