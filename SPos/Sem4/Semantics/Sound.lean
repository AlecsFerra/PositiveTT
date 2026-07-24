import SPos.Typing.Typing
import SPos.Typing.TypingProperties
import SPos.Syntax.SyntaxProperties
import SPos.Sem4.Semantics.Eval
import SPos.Sem4.Semantics.Decode

theorem Dinf.pair_inj {a b a' b' : D∞} (h : Dinf.pair a b = Dinf.pair a' b') :
    a = a' ∧ b = b' :=
  ⟨by simpa using congrArg Dinf.fst h, by simpa using congrArg Dinf.snd h⟩

theorem Dinf.true_ne_false : (Dinf.true : D∞) ≠ Dinf.false := by
  intro h
  simpa [Dinf.true, Dinf.false, Dinf.tagOf_op] using congrArg Dinf.tagOf h

def Models (ρ ρ' : DEnv n) (Γ : Ctx n) : Prop :=
  ∀ {i : Fin n} {τ : Tm n}, (Γ ∋ i ∶ τ) →
    ∃ (ℓ : Nat) (X : PER D∞), Decode ℓ (⟦ τ ⟧ᵈ ρ) (⟦ τ ⟧ᵈ ρ') X ∧ (ρ.get i ~ ρ'.get i ∈ₚ X)

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

theorem Models.cons {ρ ρ' : DEnv n} (hρ : ρ ∼ ρ' ⊨ Γ) (hA : Decode ℓ (⟦ τ ⟧ᵈ ρ) (⟦ τ ⟧ᵈ ρ') A)
    (hd : d ~ d' ∈ₚ A) : (ρ ∷ d) ∼ (ρ' ∷ d') ⊨ (Γ ∷ τ) := by
  intro i σ hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · exact ⟨ℓ, A, by simpa only [Tm.eval_weaken] using hA, by simpa using hd⟩
  · obtain ⟨k, X, hX, hmem⟩ := hρ hj
    exact ⟨k, X, by simpa only [Tm.eval_weaken] using hX, by simpa using hmem⟩

theorem DefEq.sound {Γ : Ctx n} {t t' τ : Tm n} (ht : Γ ⊢ t ≡ t' ∶ τ) {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨ Γ) :
    ∃ ℓ, (⟦ τ ⟧ᵈ ρ ~ ⟦ τ ⟧ᵈ ρ' ∈ₚ U ℓ) ∧ (⟦ t ⟧ᵈ ρ ~ ⟦ t' ⟧ᵈ ρ' ∈ₚ El ℓ (⟦ τ ⟧ᵈ ρ)) :=
  match ht with
  | .var _ hlook => by
    obtain ⟨ℓ, X, hX, hmem⟩ := hρ hlook
    exact ⟨ℓ, mem_U.mpr ⟨X, hX⟩, X, hX.refl_left, hmem⟩
  | .u (ℓ := ℓ) _ => by
    have hu : Decode (ℓ + 2) (Dinf.univ (ℓ + 1)) (Dinf.univ (ℓ + 1)) (U (ℓ + 1)) := Decode.univ (by omega)
    exact ⟨ℓ + 2, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _, by simpa [Tm.eval] using hu,
      mem_U.mpr ⟨U ℓ, by simpa [Tm.eval] using Decode.univ  (ℓ := ℓ) (k := ℓ + 1) (by omega)⟩⟩
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
  | .conv ht _ hτσ => by
    obtain ⟨_, hUτ, hElt⟩ := DefEq.sound ht hρ
    obtain ⟨X, hX⟩ := mem_U.mp hUτ
    rw [El_eq_of_decode hX] at hElt
    obtain ⟨_, _, _, hY, hcross⟩ := DefEq.sound hτσ hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hY
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hY
    obtain ⟨Z, hZ⟩ := mem_U.mp hcross
    obtain rfl := hX.det hZ
    obtain ⟨_, _, _, hY', hself⟩ := DefEq.sound hτσ hρ.refl_left
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hY'
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hY'
    obtain ⟨W, hW⟩ := mem_U.mp hself
    obtain rfl := hX.det hW
    exact ⟨_, mem_U.mpr ⟨_, hW.symm.trans hZ⟩, _, (hW.symm.trans hZ).refl_left, hElt⟩
  | .pi (τ₁ := τ) (υ₁ := υ) (υ₂ := υ') (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτ hυ => by
    obtain ⟨_, _, _, hk₂, hrelτ⟩ := DefEq.sound hτ hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A, hA'⟩ := mem_U.mp hrelτ
    obtain ⟨_, _, _, hk₃, hrelτ'⟩ := DefEq.sound hτ (Models.refl_left hρ.symm)
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₃
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₃
    obtain ⟨A₂, hA₂⟩ := mem_U.mp hrelτ'
    have hA : Decode ℓ₁ (⟦ τ ⟧ᵈ ρ) (⟦ τ ⟧ᵈ ρ') A := hA'.trans hA₂.symm
    have hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d)) (⟦ υ' ⟧ᵈ (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ := DefEq.sound hυ (hρ.cons hA hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D∞), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ :=
        DefEq.sound hυ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      obtain ⟨_, _, _, hk'', hmemυ'⟩ :=
        DefEq.sound hυ (Models.cons hρ.refl_left hA.refl_left (PER.refl_right A hdd'))
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk''
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk''
      obtain ⟨Z, hZ⟩ := mem_U.mp hmemυ'
      rw [El_eq_of_decode (hY.trans hZ.symm), El_eq_of_decode (hY.trans hZ.symm).symm]
    have hpi := Decode.pi
      (f := ƛₛ d ↦ ⟦ υ ⟧ᵈ (ρ ∷ d)) (f' := ƛₛ d ↦ ⟦ υ' ⟧ᵈ (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D∞)) (fun d => El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d))) hcoh)
      (hA'.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    have hu : Decode (max ℓ₁ ℓ₂ + 1) (Dinf.univ (max ℓ₁ ℓ₂)) (Dinf.univ (max ℓ₁ ℓ₂)) (U (max ℓ₁ ℓ₂)) :=
      Decode.univ (by omega)
    exact ⟨max ℓ₁ ℓ₂ + 1, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _,
      by simpa [Tm.eval] using hu, mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩⟩
  | .lam (τ₁ := τ) (υ := σ) (ℓ := ℓ₁) (ℓ' := ℓ₂) hσ hτeq ht => by
    obtain ⟨_, _, _, hk₂, hrelτ⟩ := DefEq.sound hτeq hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A, hA'⟩ := mem_U.mp hrelτ
    obtain ⟨_, _, _, hk₃, hrelτ'⟩ := DefEq.sound hτeq (Models.refl_left hρ.symm)
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₃
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₃
    obtain ⟨A₂, hA₂⟩ := mem_U.mp hrelτ'
    have hA : Decode ℓ₁ (⟦ τ ⟧ᵈ ρ) (⟦ τ ⟧ᵈ ρ') A := hA'.trans hA₂.symm
    have hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ σ ⟧ᵈ (ρ ∷ d)) (⟦ σ ⟧ᵈ (ρ' ∷ d')) (El ℓ₂ (⟦ σ ⟧ᵈ (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemσ⟩ := DefEq.sound hσ (hρ.cons hA hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemσ
    have hcoh : ∀ (d d' : D∞), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ σ ⟧ᵈ (ρ ∷ d)) = El ℓ₂ (⟦ σ ⟧ᵈ (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemσ⟩ :=
        DefEq.sound hσ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemσ
      rw [El_eq_of_decode hY, El_eq_of_decode hY.symm]
    have hpi := Decode.pi
      (f := ƛₛ d ↦ ⟦ σ ⟧ᵈ (ρ ∷ d)) (f' := ƛₛ d ↦ ⟦ σ ⟧ᵈ (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D∞)) (fun d => El ℓ₂ (⟦ σ ⟧ᵈ (ρ ∷ d))) hcoh)
      (hA.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    refine ⟨max ℓ₁ ℓ₂, mem_U.mpr ⟨_, by simpa [Tm.eval] using hpi⟩, _,
      by simpa [Tm.eval] using hpi.refl_left, ?_⟩
    intro d d' hdd'
    obtain ⟨_, _, _, hk'', hmemt⟩ := DefEq.sound ht (hρ.cons hA hdd')
    obtain rfl := hk''.det (hB hdd')
    simpa [Tm.eval, Dinf.app_lam] using hmemt
  | .app (υ := σ) (m₁ := m) ht' hm' => by
    obtain ⟨k, hU, hElt⟩ := DefEq.sound ht' hρ
    obtain ⟨X, hk⟩ := mem_U.mp hU
    rw [El_eq_of_decode hk] at hElt
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hk
    obtain ⟨rfl, rfl⟩ := Dinf.pi_inj hc'
    obtain ⟨_, _, _, hk'', hmemm⟩ := DefEq.sound hm' hρ
    rw [hk''.det hA] at hmemm
    obtain ⟨_, _, _, hk₂, hmemm'⟩ := DefEq.sound hm' (Models.refl_left hρ.symm)
    rw [hk₂.det hA.symm] at hmemm'
    have hmems : (⟦ m ⟧ᵈ ρ) ~ (⟦ m ⟧ᵈ ρ') ∈ₚ A := A.trans hmemm (A.symm hmemm')
    have hd : Decode k (⟦ σ [/ m ] ⟧ᵈ ρ) (⟦ σ [/ m ] ⟧ᵈ ρ') (B (⟦ m ⟧ᵈ ρ)) := by
      simpa [Tm.eval_subst1, ScottContinuousF.mk_lam_apply] using hB hmems
    exact ⟨_, mem_U.mpr ⟨_, hd⟩, _, hd.refl_left, by simpa [Tm.eval] using hElt _ _ hmemm⟩
  | .lamβ (υ := σ) (m := m) (ℓ' := ℓ') hτ hσ ht hm => by
    obtain ⟨_, _, _, hkτ, hmemτ⟩ := DefEq.sound hτ hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hkτ
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hkτ
    obtain ⟨A, hA⟩ := mem_U.mp hmemτ
    obtain ⟨_, _, _, hkm, hmemm⟩ := DefEq.sound hm hρ
    rw [hkm.det hA] at hmemm
    obtain ⟨_, _, _, hkσ, hmemσ⟩ := DefEq.sound hσ (hρ.cons hA hmemm)
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hkσ
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hkσ
    obtain ⟨S, hS⟩ := mem_U.mp hmemσ
    obtain ⟨_, _, _, hkt, hmemt⟩ := DefEq.sound ht (hρ.cons hA hmemm)
    rw [hkt.det hS] at hmemt
    refine ⟨ℓ', mem_U.mpr ⟨S, by simpa [Tm.eval_subst1] using hS⟩, S,
      by simpa [Tm.eval_subst1] using hS.refl_left, ?_⟩
    simpa [Tm.eval, Tm.eval_subst1, ScottContinuousF.mk_lam_apply, Dinf.app_lam] using hmemt
  | .lamη hη => by
    obtain ⟨_, hU, hElt⟩ := DefEq.sound hη hρ
    obtain ⟨X, hX⟩ := mem_U.mp hU
    rw [El_eq_of_decode hX] at hElt
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hX
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_pi_inv hX
    obtain ⟨rfl, rfl⟩ := Dinf.pi_inj hc'
    refine ⟨_, mem_U.mpr ⟨_, by simpa [Tm.eval] using Decode.pi hA hB⟩, _,
      by simpa [Tm.eval] using (Decode.pi hA hB).refl_left, ?_⟩
    simp [Tm.eval, ScottContinuousF.mk_lam_apply]
    intro x y hxy
    have : ⟦ Tm.app t.weaken (Tm.var (0 : Fin (n + 1))) ⟧ᵈ (ρ' ∷ x) = ⟦ t ⟧ᵈ ρ' x := by
      simp [Tm.eval]
    simpa [Dinf.app_lam, this] using hElt x y hxy
  | .sigma (τ₁ := τ) (υ₁ := υ) (υ₂ := υ') (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂) hτ hυ => by
    obtain ⟨_, _, _, hk₂, hrelτ⟩ := DefEq.sound hτ hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A, hA'⟩ := mem_U.mp hrelτ
    obtain ⟨_, _, _, hk₃, hrelτ'⟩ := DefEq.sound hτ (Models.refl_left hρ.symm)
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₃
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₃
    obtain ⟨A₂, hA₂⟩ := mem_U.mp hrelτ'
    have hA : Decode ℓ₁ (⟦ τ ⟧ᵈ ρ) (⟦ τ ⟧ᵈ ρ') A := hA'.trans hA₂.symm
    have hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d)) (⟦ υ' ⟧ᵈ (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ := DefEq.sound hυ (hρ.cons hA hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D∞), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ :=
        DefEq.sound hυ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      obtain ⟨_, _, _, hk'', hmemυ'⟩ :=
        DefEq.sound hυ (Models.cons hρ.refl_left hA.refl_left (PER.refl_right A hdd'))
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk''
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk''
      obtain ⟨Z, hZ⟩ := mem_U.mp hmemυ'
      rw [El_eq_of_decode (hY.trans hZ.symm), El_eq_of_decode (hY.trans hZ.symm).symm]
    have hsig := Decode.sigma
      (f := ƛₛ d ↦ ⟦ υ ⟧ᵈ (ρ ∷ d)) (f' := ƛₛ d ↦ ⟦ υ' ⟧ᵈ (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D∞)) (fun d => El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d))) hcoh)
      (hA'.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    have hu : Decode (max ℓ₁ ℓ₂ + 1) (Dinf.univ (max ℓ₁ ℓ₂)) (Dinf.univ (max ℓ₁ ℓ₂)) (U (max ℓ₁ ℓ₂)) :=
      Decode.univ (by omega)
    exact ⟨max ℓ₁ ℓ₂ + 1, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _,
      by simpa [Tm.eval] using hu, mem_U.mpr ⟨_, by simpa [Tm.eval] using hsig⟩⟩
  | .pair (τ := τ) (υ := υ) (a₁ := a₁) (b₁ := b₁) (ℓ := ℓ₁) (ℓ' := ℓ₂) hτ hυ ha hb => by
    obtain ⟨_, _, _, hk₂, hrelτ⟩ := DefEq.sound hτ hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A, hA'⟩ := mem_U.mp hrelτ
    obtain ⟨_, _, _, hk₃, hrelτ'⟩ := DefEq.sound hτ (Models.refl_left hρ.symm)
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₃
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₃
    obtain ⟨A₂, hA₂⟩ := mem_U.mp hrelτ'
    have hA : Decode ℓ₁ (⟦ τ ⟧ᵈ ρ) (⟦ τ ⟧ᵈ ρ') A := hA'.trans hA₂.symm
    have hB : ∀ {d d' : D∞}, (d ~ d' ∈ₚ A) →
        Decode ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d)) (⟦ υ ⟧ᵈ (ρ' ∷ d')) (El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d))) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ := DefEq.sound hυ (hρ.cons hA hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      exact Decode.el hmemυ
    have hcoh : ∀ (d d' : D∞), (d ~ d' ∈ₚ A) →
        El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d)) = El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d')) := by
      intro d d' hdd'
      obtain ⟨_, _, _, hk', hmemυ⟩ :=
        DefEq.sound hυ (Models.cons hρ.refl_left hA.refl_left hdd')
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
      obtain ⟨Y, hY⟩ := mem_U.mp hmemυ
      obtain ⟨_, _, _, hk'', hmemυ'⟩ :=
        DefEq.sound hυ (Models.cons hρ.refl_left hA.refl_left (PER.refl_right A hdd'))
      simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk''
      obtain ⟨-, -, rfl⟩ := decode_univ_inv hk''
      obtain ⟨Z, hZ⟩ := mem_U.mp hmemυ'
      rw [El_eq_of_decode (hY.trans hZ.symm), El_eq_of_decode (hY.trans hZ.symm).symm]
    have hsig := Decode.sigma
      (f := ƛₛ d ↦ ⟦ υ ⟧ᵈ (ρ ∷ d)) (f' := ƛₛ d ↦ ⟦ υ ⟧ᵈ (ρ' ∷ d))
      (B := PERRespND.mk A (PER.diag (PER D∞)) (fun d => El ℓ₂ (⟦ υ ⟧ᵈ (ρ ∷ d))) hcoh)
      (hA'.cumul (le_max_left ℓ₁ ℓ₂))
      (fun {d d'} hdd' => by simpa using (hB hdd').cumul (le_max_right ℓ₁ ℓ₂))
    obtain ⟨_, _, _, hka, hmema⟩ := DefEq.sound ha hρ
    rw [hka.det hA] at hmema
    obtain ⟨_, _, _, hkb, hmemb⟩ := DefEq.sound hb hρ
    rw [hkb.det (by simpa [Tm.eval_subst1, ScottContinuousF.mk_lam_apply] using hB hmema)] at hmemb
    refine ⟨max ℓ₁ ℓ₂, mem_U.mpr ⟨_, by simpa [Tm.eval] using hsig⟩, _,
      by simpa [Tm.eval] using hsig.refl_left, ?_⟩
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply]
    exact ⟨⟦ a₁ ⟧ᵈ ρ, ⟦ b₁ ⟧ᵈ ρ, _, _, rfl, rfl, hmema, hmemb⟩
  | .fst (τ := τ) hp => by
    obtain ⟨_, hU, hElp⟩ := DefEq.sound hp hρ
    obtain ⟨X, hk⟩ := mem_U.mp hU
    rw [El_eq_of_decode hk] at hElp
    have hk' := hk
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_sigma_inv hk'
    obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc'
    obtain ⟨a, b, a2, b2, hp1, hp2, hab, _⟩ := hElp
    refine ⟨_, mem_U.mpr ⟨A, hA⟩, _, hA.refl_left, ?_⟩
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply, hp1, hp2, Dinf.fst_pair]
    exact hab
  | .snd (τ := τ) (υ := υ) (p₁ := p₁) (p₂ := p₂) hp => by
    obtain ⟨k, hU, hElp⟩ := DefEq.sound hp hρ
    obtain ⟨X, hk⟩ := mem_U.mp hU
    rw [El_eq_of_decode hk] at hElp
    have hk' := hk
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_sigma_inv hk'
    obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc'
    obtain ⟨a, b, a2, b2, hp1, hp2, hab, hbb⟩ := hElp
    -- diagonal at ρ' relates `proj₁⟦p₁⟧ρ` and `proj₁⟦p₁⟧ρ'` in `A`
    obtain ⟨_, hU2, hElp2⟩ := DefEq.sound hp (Models.refl_left hρ.symm)
    obtain ⟨X2, hk2⟩ := mem_U.mp hU2
    rw [El_eq_of_decode hk2] at hElp2
    have hk2' := hk2
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hk2'
    obtain ⟨a'', f'', A2, B2, hc2', hA2, hB2, rfl⟩ := decode_sigma_inv hk2'
    obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc2'
    obtain ⟨a1', b1', a2', b2', hp1', hp2', hab', hbb'⟩ := hElp2
    obtain rfl := hA.symm.refl_left.det hA2
    obtain ⟨rfl, rfl⟩ := Dinf.pair_inj (hp2.symm.trans hp2')
    have hproj : a ~ a1' ∈ₚ A := A.trans hab (A.symm hab')
    have hd : Decode k (⟦ υ [/ pr₁ p₁ ] ⟧ᵈ ρ) (⟦ υ [/ pr₁ p₁ ] ⟧ᵈ ρ') (B a) := by
      simpa [Tm.eval_subst1, Tm.eval, ScottContinuousF.mk_lam_apply, hp1, hp1', Dinf.fst_pair] using hB hproj
    refine ⟨_, mem_U.mpr ⟨_, hd⟩, _, hd.refl_left, ?_⟩
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply, hp1, hp2, Dinf.snd_pair]
    exact hbb
  | .fstβ hτ hυ ha hb => by
    obtain ⟨ℓ, hU, hEl⟩ := DefEq.sound ha hρ
    exact ⟨ℓ, hU, by simpa [Tm.eval, Dinf.fst_pair] using hEl⟩
  | .sndβ hτ hυ ha hb => by
    obtain ⟨ℓ, hU, hEl⟩ := DefEq.sound hb hρ
    exact ⟨ℓ, hU, by simpa [Tm.eval, Dinf.snd_pair] using hEl⟩
  | .pairη hp => by
    -- `PER.sigma` only relates literal `mkPair`s, so `p` denotes a pair and
    -- `⸨pr₁ p, pr₂ p⸩` re-assembles it on the nose.
    obtain ⟨_, hU, hElp⟩ := DefEq.sound hp hρ
    obtain ⟨X, hX⟩ := mem_U.mp hU
    rw [El_eq_of_decode hX] at hElp
    have hX' := hX
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hX'
    obtain ⟨a', f', A, B, hc', hA, hB, rfl⟩ := decode_sigma_inv hX'
    obtain ⟨rfl, rfl⟩ := Dinf.sigma_inj hc'
    obtain ⟨a, b, a2, b2, hp1, hp2, hab, hbb⟩ := hElp
    refine ⟨_, hU, _, hX.refl_left, ?_⟩
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply, hp1, hp2, Dinf.fst_pair, Dinf.snd_pair]
    exact ⟨a, b, a2, b2, rfl, rfl, hab, hbb⟩
  | .bool _ => by
    have hu : Decode 1 (Dinf.univ 0) (Dinf.univ 0) (U 0) := Decode.univ (by omega)
    exact ⟨1, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _, by simpa [Tm.eval] using hu,
      mem_U.mpr ⟨PER.bool, by simpa [Tm.eval] using Decode.bool  (k := 0)⟩⟩
  | .true _ => by
    have hb : Decode 0 (Dinf.bool) Dinf.bool PER.bool := Decode.bool
    refine ⟨0, mem_U.mpr ⟨_, by simpa [Tm.eval] using hb⟩, _, by simpa [Tm.eval] using hb, ?_⟩
    simp only [Tm.eval]
    exact Or.inl ⟨rfl, rfl⟩
  | .false _ => by
    have hb : Decode 0 (Dinf.bool) Dinf.bool PER.bool := Decode.bool
    refine ⟨0, mem_U.mpr ⟨_, by simpa [Tm.eval] using hb⟩, _, by simpa [Tm.eval] using hb, ?_⟩
    simp only [Tm.eval]
    exact Or.inr ⟨rfl, rfl⟩
  | .boolrec (P₁ := P) (b₁ := b₁) hP ht hf hb => by
    obtain ⟨_, hUb, hbmem⟩ := DefEq.sound hb hρ
    obtain ⟨Xb, hkb⟩ := mem_U.mp hUb
    rw [El_eq_of_decode hkb] at hbmem
    have hkb2 := hkb; simp only [Tm.eval] at hkb2
    obtain ⟨_, rfl⟩ := decode_bool_inv hkb2
    obtain ⟨_, hUb', hbmem'⟩ := DefEq.sound hb (Models.refl_left hρ.symm)
    obtain ⟨Xb', hkb'⟩ := mem_U.mp hUb'
    rw [El_eq_of_decode hkb'] at hbmem'
    have hkb2' := hkb'; simp only [Tm.eval] at hkb2'
    obtain ⟨_, rfl⟩ := decode_bool_inv hkb2'
    rcases hbmem with ⟨hbρ, hbρ'⟩ | ⟨hbρ, hbρ'⟩
    · have hb1ρ' : ⟦ b₁ ⟧ᵈ ρ' = Dinf.true := by
        rcases hbmem' with ⟨h, _⟩ | ⟨_, h⟩
        · exact h
        · exact absurd (hbρ'.symm.trans h) Dinf.true_ne_false
      obtain ⟨ℓ, hUt, hElt⟩ := DefEq.sound ht hρ
      refine ⟨ℓ, ?_, ?_⟩
      · simpa [Tm.eval_subst1, Tm.eval, hbρ, hb1ρ'] using hUt
      · simpa [Tm.eval, hbρ, hbρ', Dinf.ite_true, Tm.eval_subst1] using hElt
    · have hb1ρ' : ⟦ b₁ ⟧ᵈ ρ' = Dinf.false := by
        rcases hbmem' with ⟨_, h⟩ | ⟨h, _⟩
        · exact absurd (h.symm.trans hbρ') Dinf.true_ne_false
        · exact h
      obtain ⟨ℓ, hUf, hElf⟩ := DefEq.sound hf hρ
      refine ⟨ℓ, ?_, ?_⟩
      · simpa [Tm.eval_subst1, Tm.eval, hbρ, hb1ρ'] using hUf
      · simpa [Tm.eval, hbρ, hbρ', Dinf.ite_false, Tm.eval_subst1] using hElf
  | .boolβt hP ht hf => by
    obtain ⟨ℓ, hU, hEl⟩ := DefEq.sound ht hρ
    exact ⟨ℓ, hU, by simpa [Tm.eval, Dinf.ite_true] using hEl⟩
  | .boolβf hP ht hf => by
    obtain ⟨ℓ, hU, hEl⟩ := DefEq.sound hf hρ
    exact ⟨ℓ, hU, by simpa [Tm.eval, Dinf.ite_false] using hEl⟩
  | .id (ℓ := ℓ) hτeq haeq hbeq => by
    obtain ⟨_, _, _, hk₂, hrelτ⟩ := DefEq.sound hτeq hρ
    simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk₂
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hk₂
    obtain ⟨A, hA⟩ := mem_U.mp hrelτ
    obtain ⟨_, _, _, hka, hmema⟩ := DefEq.sound haeq hρ
    rw [hka.det hA] at hmema
    obtain ⟨_, _, _, hkb, hmemb⟩ := DefEq.sound hbeq hρ
    rw [hkb.det hA] at hmemb
    have hu : Decode (ℓ + 1) (Dinf.univ ℓ) (Dinf.univ ℓ) (U ℓ) := Decode.univ (by omega)
    exact ⟨ℓ + 1, mem_U.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _, by simpa [Tm.eval] using hu,
      mem_U.mpr ⟨_, by simpa [Tm.eval] using Decode.id hA hmema hmemb⟩⟩
  | .refl (a₁ := a) _ haeq => by
    obtain ⟨_, hUa, _, hka, hmema⟩ := DefEq.sound haeq hρ
    obtain ⟨A, hA⟩ := mem_U.mp hUa
    rw [hka.det hA] at hmema
    obtain ⟨_, _, _, hka', hmema'⟩ := DefEq.sound haeq (Models.refl_left hρ.symm)
    rw [hka'.det hA.symm] at hmema'
    have hmemaa : (⟦ a ⟧ᵈ ρ) ~ (⟦ a ⟧ᵈ ρ') ∈ₚ A := A.trans hmema (A.symm hmema')
    refine ⟨_, mem_U.mpr ⟨_, by simpa [Tm.eval] using Decode.id hA hmemaa hmemaa⟩, _,
      by simpa [Tm.eval] using (Decode.id hA hmemaa hmemaa).refl_left, ?_⟩
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply]
    exact PER.refl_left A hmemaa
  | .j (τ := τ) (a := a) (b := b) (C₁ := C) (ℓ := ℓ) (p₁ := p) _ _ hCeq hdeq hpeq => by
    obtain ⟨_, hUp, _, hkp, hmemp⟩ := DefEq.sound hpeq hρ
    have hpEl := Decode.el hUp
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hpEl hkp
    obtain ⟨_, _, _, A_p, hcode, hAτ, ea, eb, hElp⟩ := decode_id_inv hpEl
    obtain ⟨rfl, rfl, rfl⟩ := Dinf.id_inj hcode
    rw [(El_eq_of_decode hkp).symm.trans hElp] at hmemp
    have hab : (⟦ a ⟧ᵈ ρ) ~ (⟦ b ⟧ᵈ ρ) ∈ₚ A_p := hmemp
    -- type part: relate ρ and ρ' at the result environment
    have hModρ : (ρ ∷ ⟦ b ⟧ᵈ ρ ∷ ⟦ p ⟧ᵈ ρ) ∼ (ρ' ∷ ⟦ b ⟧ᵈ ρ' ∷ ⟦ p ⟧ᵈ ρ')
        ⊨ (Γ ∷ τ ∷ Id (↑ τ) (↑ a) (# 0)) :=
      Models.cons (Models.cons hρ hAτ eb)
        (by simpa [Tm.eval] using Decode.id hAτ ea eb)
        (show (⟦ p ⟧ᵈ ρ) ~ (⟦ p ⟧ᵈ ρ') ∈ₚ PER.id A_p (⟦ a ⟧ᵈ ρ) (⟦ b ⟧ᵈ ρ) from hab)
    obtain ⟨_, _, _, hkCρ, hmemCρ⟩ := DefEq.sound hCeq hModρ
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hkCρ
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hkCρ
    obtain ⟨_, _, _, hkCρ', hmemCρ'⟩ := DefEq.sound hCeq (Models.refl_left hModρ.symm)
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hkCρ'
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hkCρ'
    have hCC : (⟦ C ⟧ᵈ (ρ ∷ ⟦ b ⟧ᵈ ρ ∷ ⟦ p ⟧ᵈ ρ)) ~ (⟦ C ⟧ᵈ (ρ' ∷ ⟦ b ⟧ᵈ ρ' ∷ ⟦ p ⟧ᵈ ρ'))
        ∈ₚ U ℓ := (U ℓ).trans hmemCρ ((U ℓ).symm hmemCρ')
    have hType : (⟦ C [/ ↑ p ] [/ b ] ⟧ᵈ ρ) ~ (⟦ C [/ ↑ p ] [/ b ] ⟧ᵈ ρ') ∈ₚ U ℓ := by
      simpa [Tm.eval_subst1, Tm.eval_weaken, Tm.eval] using hCC
    obtain ⟨Xres, hXres⟩ := mem_U.mp hType
    have hMod : (ρ ∷ ⟦ a ⟧ᵈ ρ ∷ Dinf.refl) ∼ (ρ ∷ ⟦ b ⟧ᵈ ρ ∷ ⟦ p ⟧ᵈ ρ)
        ⊨ (Γ ∷ τ ∷ Id (↑ τ) (↑ a) (# 0)) :=
      Models.cons (Models.cons hρ.refl_left hAτ.refl_left hab)
        (by simpa [Tm.eval] using Decode.id hAτ.refl_left (PER.refl_left _ ea) hab)
        (show Dinf.refl ~ ⟦ p ⟧ᵈ ρ ∈ₚ PER.id A_p (⟦ a ⟧ᵈ ρ) (⟦ a ⟧ᵈ ρ) from PER.refl_left _ hab)
    obtain ⟨_, _, _, hkC, hmemC⟩ := DefEq.sound hCeq hMod
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hkC
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hkC
    obtain ⟨_, _, _, hkC', hmemC'⟩ := DefEq.sound hCeq (Models.refl_left hMod.symm)
    simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hkC'
    obtain ⟨-, -, rfl⟩ := decode_univ_inv hkC'
    have hCbase : (⟦ C ⟧ᵈ (ρ ∷ ⟦ a ⟧ᵈ ρ ∷ Dinf.refl)) ~ (⟦ C ⟧ᵈ (ρ ∷ ⟦ b ⟧ᵈ ρ ∷ ⟦ p ⟧ᵈ ρ))
        ∈ₚ U ℓ := (U ℓ).trans hmemC ((U ℓ).symm hmemC')
    obtain ⟨W, hW⟩ := mem_U.mp hCbase
    have hW' : Decode ℓ (⟦ C [/ refl (↑ τ) (↑ a) ] [/ a ] ⟧ᵈ ρ) (⟦ C [/ ↑ p ] [/ b ] ⟧ᵈ ρ) W := by
      simpa [Tm.eval_subst1, Tm.eval_weaken, Tm.eval] using hW
    obtain ⟨_, _, _, hkd, hmemd⟩ := DefEq.sound hdeq hρ
    obtain rfl := hkd.det hW'.refl_left
    obtain rfl := hXres.det hW'.symm.refl_left
    exact ⟨_, hType, Xres, hXres.refl_left, by simpa [Tm.eval] using hmemd⟩
  | .jβ _ _ _ _ hd => by simpa [Tm.eval] using DefEq.sound hd hρ

theorem WfTm.sound {Γ : Ctx n} {t τ : Tm n} (ht : Γ ⊢ t ∶ τ) {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨ Γ) :
    ∃ ℓ, (⟦ τ ⟧ᵈ ρ ~ ⟦ τ ⟧ᵈ ρ' ∈ₚ U ℓ) ∧ (⟦ t ⟧ᵈ ρ ~ ⟦ t ⟧ᵈ ρ' ∈ₚ El ℓ (⟦ τ ⟧ᵈ ρ)) :=
  DefEq.sound ht hρ

theorem WfTm.sound_el {ρ ρ' : DEnv n}
    (h : Γ ⊢ t ∶ τ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hρ : ρ ∼ ρ' ⊨ Γ) :
    ⟦ t ⟧ᵈ ρ ~ ⟦ t ⟧ᵈ ρ' ∈ₚ El ℓ (⟦ τ ⟧ᵈ ρ) := by
  obtain ⟨_, hU, hEl⟩ := WfTm.sound h hρ
  obtain ⟨X, hk⟩ := mem_U.mp hU
  rw [El_eq_of_decode hk] at hEl
  obtain ⟨_, _, _, hk', hmem'⟩ := WfTm.sound hτ hρ
  simp [Tm.eval, ScottContinuousF.mk_lam_apply] at hk'
  obtain ⟨-, -, rfl⟩ := decode_univ_inv hk'
  obtain rfl := hk.det (Decode.el hmem')
  exact hEl

theorem Id_true_false_not_inhabited :
    ¬ ∃ t : Tm 0, (∅ : Ctx 0) ⊢ t ∶ Id 𝔹 tt ff := by
  rintro ⟨t, ht⟩
  obtain ⟨ℓ, _, hEl⟩ := DefEq.sound ht (Models.nil ∅ ∅)
  obtain ⟨X, hX, hmem⟩ := hEl
  simp only [Tm.eval, ScottContinuousF.mk_lam_apply] at hX
  obtain ⟨t', a', b', A, hcode, hdom, ea, eb, rfl⟩ := decode_id_inv hX
  obtain ⟨_, rfl⟩ := decode_bool_inv hdom
  rcases hmem with ⟨_, h⟩ | ⟨h, _⟩
  · exact Dinf.true_ne_false h.symm
  · exact Dinf.true_ne_false h
