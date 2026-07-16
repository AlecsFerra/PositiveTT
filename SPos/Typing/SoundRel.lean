import SPos.Typing.Typing
import SPos.Typing.TypingProperties
import SPos.Syntax.SyntaxProperties
import SPos.Semantics.EvalProperties
import SPos.Semantics.Decode

open ScottDomain OmegaCompletePartialOrder ωScottContinuous

variable {D : Type u} [ScottDomain D Label]

local notation "DEnv" => Env (fun _ => D)
local infix:50 " ≼ " => DecodeEnv.Le

def ModelsRel {m : Nat} (ν : DecodeEnv D m) (ρ ρ' : DEnv n) (Γ : Ctx n) : Prop :=
  ∀ {i : Fin n} {τ : Tm n}, (Γ ∋ i ∶ τ) →
    ∃ (ℓ : Nat), ∀ {m' : Nat} {ν' : DecodeEnv D m'}, ν ≼ ν' →
      ∃ X : PER D, DecodeRel ℓ ν' (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') X ∧ (ρ.get i ~ ρ'.get i ∈ₚ X)

local notation:40 ρ:41 " ∼ " ρ':41 " ⊨[" ν:41 "] " Γ:41 => ModelsRel ν ρ ρ' Γ

theorem ModelsRel.nil {ν : DecodeEnv D m} (ρ ρ' : DEnv 0) :
    ρ ∼ ρ' ⊨[ν] (∅ : Ctx 0) :=
  fun {i} {_} _ => i.elim0

theorem ModelsRel.mono {ν : DecodeEnv D m} {ν' : DecodeEnv D m'} {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨[ν] Γ) (hle : ν ≼ ν') : ρ ∼ ρ' ⊨[ν'] Γ := by
  intro i τ hlook
  obtain ⟨ℓ, hent⟩ := hρ hlook
  exact ⟨ℓ, fun hle' => hent (hle.trans hle')⟩

theorem ModelsRel.refl_left {ν : DecodeEnv D m} {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨[ν] Γ) : ρ ∼ ρ ⊨[ν] Γ := by
  intro i τ hlook
  obtain ⟨ℓ, hent⟩ := hρ hlook
  refine ⟨ℓ, fun hle => ?_⟩
  obtain ⟨X, hX, hmem⟩ := hent hle
  exact ⟨X, hX.refl_left, X.refl_left hmem⟩

theorem ModelsRel.symm {ν : DecodeEnv D m} {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨[ν] Γ) : ρ' ∼ ρ ⊨[ν] Γ := by
  intro i τ hlook
  obtain ⟨ℓ, hent⟩ := hρ hlook
  refine ⟨ℓ, fun hle => ?_⟩
  obtain ⟨X, hX, hmem⟩ := hent hle
  exact ⟨X, hX.symm, X.symm hmem⟩

theorem ModelsRel.cons {ν : DecodeEnv D m} {ρ ρ' : DEnv n}
    (hρ : ρ ∼ ρ' ⊨[ν] Γ)
    (hA : ∀ {m' : Nat} {ν' : DecodeEnv D m'}, ν ≼ ν' →
      ∃ A : PER D, DecodeRel ℓ ν' (⟦ τ ⟧𝒄 ρ) (⟦ τ ⟧𝒄 ρ') A ∧ (d ~ d' ∈ₚ A)) :
    (ρ ∷ d) ∼ (ρ' ∷ d') ⊨[ν] (Γ ∷ τ) := by
  intro i σ hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · refine ⟨ℓ, fun hle => ?_⟩
    obtain ⟨A, hA', hd'⟩ := hA hle
    exact ⟨A, by simpa only [Tm.eval_weaken] using hA', by simpa using hd'⟩
  · obtain ⟨k, hent⟩ := hρ hj
    refine ⟨k, fun hle => ?_⟩
    obtain ⟨X, hX, hmem⟩ := hent hle
    exact ⟨X, by simpa only [Tm.eval_weaken] using hX, by simpa using hmem⟩

theorem ModelsRel.consMu {ν : DecodeEnv D m} {ρ ρ' : DEnv n} {X : PER D}
    (hρ : ρ ∼ ρ' ⊨[ν] Γ) (ℓ : Nat) :
    (ρ ∷ (mkMuVar m : D)) ∼ (ρ' ∷ (mkMuVar m : D)) ⊨[ν.snoc X] (Γ ∷ 𝓤 ℓ) := by
  intro i σ hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · refine ⟨ℓ + 1, fun {m'} {ν'} hle => ?_⟩
    have hm : m < m' := Nat.lt_of_lt_of_le (Nat.lt_succ_self m) hle.length
    refine ⟨URel ℓ ν', ?_, ?_⟩
    · simpa only [Tm.eval_weaken, Tm.eval, mk_lam_apply] using
        DecodeRel.univ (ν := ν') (Nat.lt_succ_self ℓ)
    · simpa using URel.muvar_mem (ℓ := ℓ) hm
  · obtain ⟨k, hent⟩ := hρ hj
    refine ⟨k, fun hle => ?_⟩
    obtain ⟨Y, hY, hmem⟩ := hent ((DecodeEnv.Le.snoc ν X).trans hle)
    exact ⟨Y, by simpa only [Tm.eval_weaken] using hY, by simpa using hmem⟩

theorem DefEq.soundRel {Γ : Ctx n} {t t' τ : Tm n} (ht : Γ ⊢ t ≡ t' ∶ τ)
    {m : Nat} {ν : DecodeEnv D m} {ρ ρ' : DEnv n} (hρ : ρ ∼ ρ' ⊨[ν] Γ) :
    ∃ ℓ, ∀ {m' : Nat} {ν' : DecodeEnv D m'}, ν ≼ ν' →
      (⟦ τ ⟧𝒄 ρ ~ ⟦ τ ⟧𝒄 ρ' ∈ₚ URel ℓ ν') ∧
      (⟦ t ⟧𝒄 ρ ~ ⟦ t' ⟧𝒄 ρ' ∈ₚ ElRel ℓ ν' (⟦ τ ⟧𝒄 ρ)) :=
  match ht with
  | .var _ hlook => by
    obtain ⟨ℓ, hent⟩ := hρ hlook
    refine ⟨ℓ, fun hle => ?_⟩
    obtain ⟨X, hX, hmem⟩ := hent hle
    exact ⟨mem_URel.mpr ⟨X, hX⟩, X, hX.refl_left, hmem⟩
  | .u (ℓ := ℓ) _ => by
    refine ⟨ℓ + 2, fun {m'} {ν'} hle => ?_⟩
    have hu : DecodeRel (ℓ + 2) ν' (mkU (ℓ + 1) : D) (mkU (ℓ + 1)) (URel (ℓ + 1) ν') :=
      DecodeRel.univ (by omega)
    exact ⟨mem_URel.mpr ⟨_, by simpa [Tm.eval] using hu⟩, _, by simpa [Tm.eval] using hu,
      mem_URel.mpr ⟨URel ℓ ν',
        by simpa [Tm.eval] using
          DecodeRel.univ (D := D) (ℓ := ℓ) (k := ℓ + 1) (ν := ν') (by omega)⟩⟩
  | .mu (ℓ := ℓ) (B₁ := B₁) (B₂ := B₂) hB _ _ => by
    refine ⟨ℓ + 1, fun {m'} {ν'} hle => ?_⟩
    -- the body decodes at every candidate PER for the fresh variable, to the
    -- relativized `El` of its left eval — this pins the operator `F`
    have hdec : ∀ X : PER D,
        DecodeRel ℓ (ν'.snoc X)
          (⟦ B₁ ⟧𝒄 (ρ ∷ (mkMuVar m' : D))) (⟦ B₂ ⟧𝒄 (ρ' ∷ (mkMuVar m' : D)))
          (ElRel ℓ (ν'.snoc X) (⟦ B₁ ⟧𝒄 (ρ ∷ (mkMuVar m' : D)))) := by
      intro X
      have hMod : (ρ ∷ (mkMuVar m' : D)) ∼ (ρ' ∷ (mkMuVar m' : D)) ⊨[ν'.snoc X] (Γ ∷ 𝓤 ℓ) :=
        ModelsRel.consMu (ModelsRel.mono hρ hle) ℓ
      obtain ⟨ℓB, hcon⟩ := DefEq.soundRel hB hMod
      obtain ⟨-, hElB⟩ := hcon (DecodeEnv.Le.refl _)
      obtain ⟨Z, hZ, hpair⟩ := hElB
      rw [show (⟦ 𝓤 ℓ ⟧𝒄 (ρ ∷ (mkMuVar m' : D))) = (mkU ℓ : D) from by simp [Tm.eval]]
        at hZ
      obtain ⟨-, -, rfl⟩ := decodeRel_univ_inv hZ
      exact DecodeRel.el hpair
    have hmu : DecodeRel ℓ ν' (⟦ μ B₁ ⟧𝒄 ρ) (⟦ μ B₂ ⟧𝒄 ρ')
        (PER.muFix (fun X => ElRel ℓ (ν'.snoc X) (⟦ B₁ ⟧𝒄 (ρ ∷ (mkMuVar m' : D))))) := by
      simp only [Tm.eval]
      exact DecodeRel.mu (fun X => by simpa [mk_lam_apply] using hdec X)
    refine ⟨?_, ?_⟩
    · exact mem_URel.mpr ⟨_,
        by simpa [Tm.eval] using DecodeRel.univ (ν := ν') (Nat.lt_succ_self ℓ)⟩
    · refine ⟨URel ℓ ν', ?_, mem_URel.mpr ⟨_, hmu⟩⟩
      simpa [Tm.eval] using DecodeRel.univ (ν := ν') (Nat.lt_succ_self ℓ)
  | _ => sorry
