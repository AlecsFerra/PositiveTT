import SPos.Typing.Regularity
import SPos.Syntax.SyntaxProperties

def Tm.boolFam (ℓ : Nat) (τ υ : Tm n) : Tm (n + 1) :=
  Tm.boolrec (𝓤 ℓ) (↑ τ) (↑ υ) (# 0)

def Tm.sumT (ℓ : Nat) (τ υ : Tm n) : Tm n :=
  Tm.sigma Tm.bool (Tm.boolFam ℓ τ υ)

def Tm.inl (a : Tm n) : Tm n := Tm.pair Tm.true a
def Tm.inr (b : Tm n) : Tm n := Tm.pair Tm.false b

def Tm.instSum (ρ : Tm (n + 1)) (u : Tm (n + 1)) : Tm (n + 1) :=
  (ρ.rename (Ren.lift Fin.succ)) [/ u ]

def Tm.sumrecMot (ρ : Tm (n + 1)) : Tm (n + 2) :=
  (ρ.rename (Ren.lift (fun i => i.succ.succ))) [/ ⸨ # 1 , # 0 ⸩ ]

def Tm.sumMotiveD (ℓ : Nat) (τ υ : Tm n) (ρ : Tm (n + 1)) : Tm (n + 1) :=
  Tm.pi (Tm.boolFam ℓ τ υ) (Tm.sumrecMot ρ)

def Tm.sumrec (ℓ : Nat) (τ υ : Tm n) (ρ l r : Tm (n + 1)) (s : Tm n) : Tm n :=
  (Tm.boolrec (Tm.sumMotiveD ℓ τ υ ρ) (ƛ τ l) (ƛ υ r) (Tm.fst s)) • (Tm.snd s)

theorem Tm.boolFam_rename (ℓ : Nat) (τ υ : Tm n) (r : Ren n m) :
    (Tm.boolFam ℓ τ υ).rename (Ren.lift r) = Tm.boolFam ℓ (τ.rename r) (υ.rename r) := by
  simp [Tm.boolFam, Tm.rename, Ren.lift]

theorem Tm.sumT_rename (ℓ : Nat) (τ υ : Tm n) (r : Ren n m) :
    (Tm.sumT ℓ τ υ).rename r = Tm.sumT ℓ (τ.rename r) (υ.rename r) := by
  simp [Tm.sumT, Tm.rename, Tm.boolFam_rename]

theorem Tm.sumT_weaken (ℓ : Nat) (τ υ : Tm n) :
    (Tm.sumT ℓ τ υ).weaken = Tm.sumT ℓ τ.weaken υ.weaken :=
  Tm.sumT_rename ℓ τ υ Fin.succ

macro "simp_wall" : tactic => `(tactic| simp [
  Subst.single, Subst.lift, Ren.lift, Fin.cases_succ, Fin.cases_zero, Tm.subst,
  Tm.rename, Tm.weaken, Tm.inl, ←Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one',
  Fin.cases_zero, Fin.cases_succ, Tm.subst1, Tm.weaken, Tm.rename, Tm.inr,
  Tm.subst, Tm.instSum
])

theorem Tm.sumrecMot_true (ρ : Tm (n + 1)) :
    (Tm.sumrecMot ρ).subst (Subst.single Tm.true).lift = Tm.instSum ρ (Tm.inl (# 0)) := by
  simp [Tm.sumrecMot, Tm.instSum, subst1, ←Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']
  congr 1; funext i; induction i using Fin.cases <;> simp_wall

theorem Tm.sumrecMot_false (ρ : Tm (n + 1)) :
    (Tm.sumrecMot ρ).subst (Subst.single Tm.false).lift = Tm.instSum ρ (Tm.inr (# 0)) := by
  simp [Tm.sumrecMot, Tm.instSum, subst1, ←Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']
  congr 1; funext i; induction i using Fin.cases <;> simp_wall

theorem Tm.sumrecMot_app (ρ : Tm (n + 1)) (c₁ c₂ : Tm n) :
    ((Tm.sumrecMot ρ).subst (Subst.single c₁).lift) [/ c₂ ] = ρ [/ ⸨ c₁ , c₂ ⸩ ] := by
  simp [Tm.sumrecMot, subst1, ←Fin.succ_zero_eq_one, -Fin.succ_zero_eq_one']
  congr 1; funext i; induction i using Fin.cases <;> simp_wall

theorem Tm.instSum_subst1 (ρ : Tm (n + 1)) (u : Tm (n + 1)) (a : Tm n) :
    (Tm.instSum ρ u) [/ a ] = ρ [/ u [/ a ] ] := by
  simp_wall; congr 1; funext i; induction i using Fin.cases <;> simp_wall

theorem Tm.inl_subst1 (a : Tm n) : (Tm.inl (# 0) : Tm (n + 1)) [/ a ] = Tm.inl a := by
  simp_wall

theorem Tm.inr_subst1 (b : Tm n) : (Tm.inr (# 0) : Tm (n + 1)) [/ b ] = Tm.inr b := by
  simp_wall

variable {Γ : Ctx n}

theorem DefEq.boolFam_true (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ (Tm.boolFam ℓ τ υ) [/ Tm.true ] ≡ τ ∶ 𝓤 ℓ := by
  have hP : Γ ∷ Tm.bool ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1) := DefEq.u (hΓ.cons (DefEq.bool hΓ))
  have ht : Γ ⊢ τ ∶ (𝓤 ℓ) [/ Tm.true ]  := by show Γ ⊢ τ ∶ 𝓤 ℓ; exact hτ
  have hf : Γ ⊢ υ ∶ (𝓤 ℓ) [/ Tm.false ] := by show Γ ⊢ υ ∶ 𝓤 ℓ; exact hυ
  have hβ := DefEq.boolβt hP ht hf
  simpa [Tm.boolFam, Tm.subst1, Tm.subst, Tm.weaken, Subst.single] using hβ

theorem DefEq.boolFam_false (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ (Tm.boolFam ℓ τ υ) [/ Tm.false ] ≡ υ ∶ 𝓤 ℓ := by
  have hP : Γ ∷ Tm.bool ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1) := DefEq.u (hΓ.cons (DefEq.bool hΓ))
  have ht : Γ ⊢ τ ∶ (𝓤 ℓ) [/ Tm.true ]  := by show Γ ⊢ τ ∶ 𝓤 ℓ; exact hτ
  have hf : Γ ⊢ υ ∶ (𝓤 ℓ) [/ Tm.false ] := by show Γ ⊢ υ ∶ 𝓤 ℓ; exact hυ
  have hβ := DefEq.boolβf hP ht hf
  simpa [Tm.boolFam, Tm.subst1, Tm.subst, Tm.weaken, Subst.single] using hβ

theorem DefEq.boolSubstCong (hΓ : ⊢ Γ) (hM : Γ ∷ Tm.bool ⊢ M ∶ 𝓤 s)
    (hv : Γ ⊢ v₁ ≡ v₂ ∶ Tm.bool) :
    Γ ⊢ M [/ v₁ ] ≡ M [/ v₂ ] ∶ 𝓤 s := by
  have hbool := DefEq.bool hΓ
  have hU : Γ ∷ Tm.bool ⊢ 𝓤 s ∶ 𝓤 (s + 1) := DefEq.u (hΓ.cons hbool)
  have hlam : Γ ⊢ (ƛ Tm.bool M) ≡ (ƛ Tm.bool M) ∶ Tm.pi Tm.bool (𝓤 s) :=
    DefEq.lam hU hbool hM
  have happ := DefEq.app hlam hv
  have hβ1 := DefEq.lamβ hbool hU hM hv.wf_left
  have hβ2 := DefEq.lamβ hbool hU hM hv.wf_right
  exact (hβ1.symm.trans happ).trans hβ2

theorem DefEq.boolFam_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ₁ ≡ υ₂ ∶ 𝓤 ℓ) :
    Γ ∷ Tm.bool ⊢ Tm.boolFam ℓ τ₁ υ₁ ≡ Tm.boolFam ℓ τ₂ υ₂ ∶ 𝓤 ℓ := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hΓbb : ⊢ Γ ∷ Tm.bool ∷ Tm.bool := hΓb.cons (DefEq.bool hΓb)
  have hP : Γ ∷ Tm.bool ∷ Tm.bool ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1) := DefEq.u hΓbb
  have ht : Γ ∷ Tm.bool ⊢ τ₁.weaken ≡ τ₂.weaken ∶ (𝓤 ℓ) [/ Tm.true ] := by
    show Γ ∷ Tm.bool ⊢ _ ≡ _ ∶ 𝓤 ℓ
    exact DefEq.weaken hτ hΓb
  have hf : Γ ∷ Tm.bool ⊢ υ₁.weaken ≡ υ₂.weaken ∶ (𝓤 ℓ) [/ Tm.false ] := by
    show Γ ∷ Tm.bool ⊢ _ ≡ _ ∶ 𝓤 ℓ
    exact DefEq.weaken hυ hΓb
  have hb : Γ ∷ Tm.bool ⊢ (# 0) ∶ Tm.bool := DefEq.var hΓb Lookup.here
  show Γ ∷ Tm.bool ⊢ _ ≡ _ ∶ (𝓤 ℓ) [/ (# 0) ]
  exact DefEq.boolrec hP ht hf hb


theorem DefEq.sum :
   Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ → Γ ⊢ υ₁ ≡ υ₂ ∶ 𝓤 ℓ
   ----------------------------------------
→ Γ ⊢ .sumT ℓ τ₁ υ₁ ≡ .sumT ℓ τ₂ υ₂ ∶ 𝓤 ℓ
:= by
  intros hτ hυ
  have hΓ := hτ.wfCtx
  simpa [Tm.sumT, Nat.zero_max]
  using DefEq.sigma (DefEq.bool hΓ) (DefEq.boolFam_cong hΓ hτ hυ)

theorem DefEq.inl :
   Γ ⊢ τ ∶ 𝓤 ℓ → Γ ⊢ υ ∶ 𝓤 ℓ
→ Γ ⊢ a₁ ≡ a₂ ∶ τ
   ------------------------------------
→ Γ ⊢ .inl a₁ ≡ .inl a₂ ∶ .sumT ℓ τ υ
:= by
  intros hτ hυ ha
  have hΓ := hτ.wfCtx
  have hfam := DefEq.boolFam_true hΓ hτ hυ
  exact DefEq.pair
    (DefEq.bool hΓ)
    (DefEq.boolFam_cong hΓ hτ hυ)
    (DefEq.true hΓ)
    (DefEq.conv ha hfam.wf_left hfam.symm)

private theorem DefEq.inl_wk (hΓB : ⊢ Γ ∷ B) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (ha : Γ ∷ B ⊢ a ∶ ↑ τ) : Γ ∷ B ⊢ Tm.inl a ∶ ↑ (Tm.sumT ℓ τ υ) := by
  rw [Tm.sumT_weaken]
  exact DefEq.inl (WfTm.weaken hτ hΓB) (WfTm.weaken hυ hΓB) ha

theorem DefEq.inr :
   Γ ⊢ τ ∶ 𝓤 ℓ → Γ ⊢ υ ∶ 𝓤 ℓ
→ Γ ⊢ b₁ ≡ b₂ ∶ υ
  -------------------------------------
→ Γ ⊢ .inr b₁ ≡ .inr b₂ ∶ .sumT ℓ τ υ
  := by
    intros hτ hυ hb
    have hΓ := hτ.wfCtx
    have hfam := DefEq.boolFam_false hΓ hτ hυ
    exact DefEq.pair
      (DefEq.bool hΓ)
      (DefEq.boolFam_cong hΓ hτ hυ)
      (DefEq.false hΓ)
      (DefEq.conv hb hfam.wf_left hfam.symm)

private theorem DefEq.inr_wk (hΓB : ⊢ Γ ∷ B) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hb : Γ ∷ B ⊢ b ∶ ↑ υ) : Γ ∷ B ⊢ Tm.inr b ∶ ↑ (Tm.sumT ℓ τ υ) := by
  rw [Tm.sumT_weaken]
  exact DefEq.inr (WfTm.weaken hτ hΓB) (WfTm.weaken hυ hΓB) hb

theorem DefEq.substCong (hΓ : ⊢ Γ) (hA : Γ ⊢ A ∶ 𝓤 k) (hM : Γ ∷ A ⊢ M ∶ 𝓤 s)
    (hv : Γ ⊢ v₁ ≡ v₂ ∶ A) : Γ ⊢ M [/ v₁ ] ≡ M [/ v₂ ] ∶ 𝓤 s := by
  have hU : Γ ∷ A ⊢ 𝓤 s ∶ 𝓤 (s + 1) := DefEq.u (hΓ.cons hA)
  have hlam : Γ ⊢ (ƛ A M) ≡ (ƛ A M) ∶ Tm.pi A (𝓤 s) := DefEq.lam hU hA hM
  have happ := DefEq.app hlam hv
  have hβ1 := DefEq.lamβ hA hU hM hv.wf_left
  have hβ2 := DefEq.lamβ hA hU hM hv.wf_right
  exact (hβ1.symm.trans happ).trans hβ2

theorem DefEq.pair_var10 (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ ⸨ # 1 , # 0 ⸩
      ∶ (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ) := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hfam := DefEq.boolFam_cong hΓ hτ hυ
  have hΔ : ⊢ Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ := hΓb.cons hfam
  have hτ2 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ τ.weaken.weaken ∶ 𝓤 ℓ :=
    WfTm.weaken (WfTm.weaken hτ hΓb) hΔ
  have hυ2 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ υ.weaken.weaken ∶ 𝓤 ℓ :=
    WfTm.weaken (WfTm.weaken hυ hΓb) hΔ
  have h1 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ # 1 ∶ Tm.bool :=
    DefEq.var hΔ (Lookup.there Lookup.here)
  have h0 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ
      ⊢ # 0 ∶ (Tm.boolFam ℓ τ.weaken.weaken υ.weaken.weaken) [/ # 1 ] := by
    have hlook := DefEq.var hΔ Lookup.here
    have e : (Tm.boolFam ℓ τ.weaken.weaken υ.weaken.weaken) [/ (# 1 : Tm (n + 2)) ]
        = (Tm.boolFam ℓ τ υ).weaken := by
      simp [Tm.boolFam, Tm.weaken, Tm.subst1, Tm.subst, Subst.single, Tm.rename_eq_subst]
    rw [e]
    exact hlook
  have hpair := DefEq.pair (DefEq.bool hΔ) (DefEq.boolFam_cong hΔ hτ2 hυ2) h1 h0
  have esum : (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ)
      = Tm.sumT ℓ τ.weaken.weaken υ.weaken.weaken := by
    simp [Tm.sumT_rename, Tm.weaken, Tm.rename_rename, Function.comp_def]
  rw [esum]
  exact hpair


theorem DefEq.sumrecMot_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ') :
    Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ Tm.sumrecMot ρ₁ ≡ Tm.sumrecMot ρ₂ ∶ 𝓤 ℓ' := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hfam := DefEq.boolFam_cong hΓ hτ hυ
  have hΔ : ⊢ Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ := hΓb.cons hfam
  have hτ2 := WfTm.weaken (WfTm.weaken hτ hΓb) hΔ
  have hυ2 := WfTm.weaken (WfTm.weaken hυ hΓb) hΔ
  have hpair := DefEq.pair_var10 hΓ hτ hυ
  have hsumR : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ
      ⊢ (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ) ∶ 𝓤 ℓ := by
    have h := DefEq.sum hτ2 hυ2
    have esum : (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ)
        = Tm.sumT ℓ τ.weaken.weaken υ.weaken.weaken := by
      simp [Tm.sumT_rename, Tm.weaken, Tm.rename_rename, Function.comp_def]
    rw [esum]
    exact h
  have hΔs := hΔ.cons hsumR
  have hr2 : Ren.WellTyped (fun i => i.succ.succ) Γ (Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ) := by
    intro x A hlook
    have h := Lookup.there (υ := Tm.boolFam ℓ τ υ) (Lookup.there (υ := Tm.bool) hlook)
    simpa [Tm.weaken, Tm.rename_rename, Function.comp_def] using h
  have hren := DefEq.rename hρ hΔs hr2.lift
  exact DefEq.subst1 hren hpair hΔ

theorem DefEq.sumMotiveD_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ') :
    Γ ∷ Tm.bool ⊢ Tm.sumMotiveD ℓ τ υ ρ₁ ≡ Tm.sumMotiveD ℓ τ υ ρ₂ ∶ 𝓤 (max ℓ ℓ') :=
  DefEq.pi (DefEq.boolFam_cong hΓ hτ hυ) (DefEq.sumrecMot_cong hΓ hτ hυ hρ)

theorem DefEq.sumMotiveD_wf (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ') :
    Γ ∷ Tm.bool ⊢ Tm.sumMotiveD ℓ τ υ ρ ∶ 𝓤 (max ℓ ℓ') :=
  DefEq.sumMotiveD_cong hΓ hτ hυ hρ

theorem DefEq.instSum_cong (hΓ : ⊢ Γ) (hB : Γ ⊢ B ∶ 𝓤 k) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ)
    (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ')
    (hw : Γ ∷ B ⊢ w ∶ (Tm.sumT ℓ τ υ).weaken) :
    Γ ∷ B ⊢ Tm.instSum ρ₁ w ≡ Tm.instSum ρ₂ w ∶ 𝓤 ℓ' := by
  have hΓB : ⊢ Γ ∷ B := hΓ.cons hB
  have hΓBs : ⊢ Γ ∷ B ∷ (Tm.sumT ℓ τ υ).weaken :=
    hΓB.cons (WfTm.weaken (DefEq.sum hτ hυ) hΓB)
  have hren := DefEq.rename hρ hΓBs (Ren.WellTyped.lift (Ren.succ_wellTyped Γ B))
  exact DefEq.subst1 hren hw hΓB

theorem DefEq.sumMotiveD_true (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ') :
    Γ ⊢ (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.true ]
      ≡ Tm.pi τ (Tm.instSum ρ (Tm.inl (# 0))) ∶ 𝓤 (max ℓ ℓ') := by
  have key : (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.true ]
      = Tm.pi ((Tm.boolFam ℓ τ υ) [/ Tm.true ]) (Tm.instSum ρ (Tm.inl (# 0))) := by
    simp only [Tm.sumMotiveD, Tm.subst1, Tm.subst, Tm.sumrecMot_true]
  rw [key]
  have hfam := DefEq.boolFam_true hΓ hτ hυ
  have hΓf : ⊢ Γ ∷ ((Tm.boolFam ℓ τ υ) [/ Tm.true ]) := hΓ.cons hfam.wf_left
  have h0 : Γ ∷ ((Tm.boolFam ℓ τ υ) [/ Tm.true ]) ⊢ # 0 ∶ τ.weaken := by
    have hv := DefEq.var hΓf Lookup.here
    exact DefEq.conv hv (WfTm.weaken hτ hΓf) (DefEq.weaken hfam hΓf)
  have hcod := DefEq.instSum_cong hΓ hfam.wf_left hτ hυ hρ (DefEq.inl_wk hΓf hτ hυ h0)
  exact DefEq.pi hfam hcod

theorem DefEq.sumMotiveD_false (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ') :
    Γ ⊢ (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.false ]
      ≡ Tm.pi υ (Tm.instSum ρ (Tm.inr (# 0))) ∶ 𝓤 (max ℓ ℓ') := by
  have key : (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.false ]
      = Tm.pi ((Tm.boolFam ℓ τ υ) [/ Tm.false ]) (Tm.instSum ρ (Tm.inr (# 0))) := by
    simp only [Tm.sumMotiveD, Tm.subst1, Tm.subst, Tm.sumrecMot_false]
  rw [key]
  have hfam := DefEq.boolFam_false hΓ hτ hυ
  have hΓf : ⊢ Γ ∷ ((Tm.boolFam ℓ τ υ) [/ Tm.false ]) := hΓ.cons hfam.wf_left
  have h0 : Γ ∷ ((Tm.boolFam ℓ τ υ) [/ Tm.false ]) ⊢ # 0 ∶ υ.weaken := by
    have hv := DefEq.var hΓf Lookup.here
    exact DefEq.conv hv (WfTm.weaken hυ hΓf) (DefEq.weaken hfam hΓf)
  have hcod := DefEq.instSum_cong hΓ hfam.wf_left hτ hυ hρ (DefEq.inr_wk hΓf hτ hυ h0)
  exact DefEq.pi hfam hcod

theorem DefEq.sumrec :
   Γ ⊢ τ ∶ 𝓤 ℓ → Γ ⊢ υ ∶ 𝓤 ℓ → Γ ∷ .sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ'
→ Γ ⊢ s₁ ≡ s₂ ∶ .sumT ℓ τ υ
→ Γ ∷ τ ⊢ l₁ ≡ l₂ ∶ ρ₁.instSum (.inl # 0)
→ Γ ∷ υ ⊢ r₁ ≡ r₂ ∶ ρ₁.instSum (.inr # 0)
   ---------------------------------------------------------------------------
→ Γ ⊢ .sumrec ℓ τ υ ρ₁ l₁ r₁ s₁ ≡ .sumrec ℓ τ υ ρ₂ l₂ r₂ s₂ ∶ ρ₁ [/ s₁ ]
:= by
  intro hτ hυ hρ hs hl hr
  have hΓ := hs.wfCtx
  have hΓτ : ⊢ Γ ∷ τ := hΓ.cons hτ
  have hΓυ : ⊢ Γ ∷ υ := hΓ.cons hυ
  have hM := DefEq.sumMotiveD_cong hΓ hτ hυ hρ
  have hMt := DefEq.sumMotiveD_true hΓ hτ hυ hρ.wf_left
  have hMf := DefEq.sumMotiveD_false hΓ hτ hυ hρ.wf_left
  have hcodl := DefEq.instSum_cong hΓ hτ hτ hυ hρ.wf_left
    (DefEq.inl_wk hΓτ hτ hυ (DefEq.var hΓτ Lookup.here))
  have hLpi : Γ ⊢ (ƛ τ l₁) ≡ (ƛ τ l₂) ∶ Tm.pi τ (Tm.instSum ρ₁ (Tm.inl (# 0))) :=
    DefEq.lam hcodl.wf_left hτ hl
  have hL := DefEq.conv hLpi hMt.wf_left hMt.symm
  have hcodr := DefEq.instSum_cong hΓ hυ hτ hυ hρ.wf_left
    (DefEq.inr_wk hΓυ hτ hυ (DefEq.var hΓυ Lookup.here))
  have hRpi : Γ ⊢ (ƛ υ r₁) ≡ (ƛ υ r₂) ∶ Tm.pi υ (Tm.instSum ρ₁ (Tm.inr (# 0))) :=
    DefEq.lam hcodr.wf_left hυ hr
  have hR := DefEq.conv hRpi hMf.wf_left hMf.symm
  have hRec := DefEq.boolrec hM hL hR (DefEq.fst hs)
  have happ := DefEq.app hRec (DefEq.snd hs)
  rw [Tm.sumrecMot_app] at happ
  have hη := DefEq.pairη hs.wf_left
  have hsub := DefEq.substCong hΓ (DefEq.sum hτ hυ) hρ.wf_left hη.symm
  exact DefEq.conv happ hsub.wf_right hsub

theorem DefEq.sumrecβl :
   Γ ⊢ τ ∶ 𝓤 ℓ → Γ ⊢ υ ∶ 𝓤 ℓ → Γ ∷ .sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ'
→ Γ ∷ τ ⊢ l ∶ ρ.instSum (.inl # 0)
→ Γ ∷ υ ⊢ r ∶ ρ.instSum (.inr # 0)
→ Γ ⊢ a ∶ τ
   -----------------------------------------------------------------
→ Γ ⊢ .sumrec ℓ τ υ ρ l r (.inl a) ≡ l [/ a ] ∶ ρ [/ .inl a ]
:= by
  intro hτ hυ hρ hl hr ha
  have hΓ := hτ.wfCtx
  have hΓτ : ⊢ Γ ∷ τ := hΓ.cons hτ
  have hΓυ : ⊢ Γ ∷ υ := hΓ.cons hυ
  have hbool := DefEq.bool hΓ
  have hfamwf := DefEq.boolFam_cong hΓ hτ hυ
  have hfamt := DefEq.boolFam_true hΓ hτ hυ
  have hM := DefEq.sumMotiveD_wf hΓ hτ hυ hρ
  have hMt := DefEq.sumMotiveD_true hΓ hτ hυ hρ
  have hMf := DefEq.sumMotiveD_false hΓ hτ hυ hρ
  have ha_fam : Γ ⊢ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.true ] :=
    DefEq.conv ha hfamt.wf_left hfamt.symm
  have hcodl := DefEq.instSum_cong hΓ hτ hτ hυ hρ
    (DefEq.inl_wk hΓτ hτ hυ (DefEq.var hΓτ Lookup.here))
  have hLpi : Γ ⊢ (ƛ τ l) ∶ Tm.pi τ (Tm.instSum ρ (Tm.inl (# 0))) :=
    DefEq.lam hcodl hτ hl
  have hL : Γ ⊢ (ƛ τ l) ∶ (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.true ] :=
    DefEq.conv hLpi hMt.wf_left hMt.symm
  have hcodr := DefEq.instSum_cong hΓ hυ hτ hυ hρ
    (DefEq.inr_wk hΓυ hτ hυ (DefEq.var hΓυ Lookup.here))
  have hRpi : Γ ⊢ (ƛ υ r) ∶ Tm.pi υ (Tm.instSum ρ (Tm.inr (# 0))) :=
    DefEq.lam hcodr hυ hr
  have hR : Γ ⊢ (ƛ υ r) ∶ (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.false ] :=
    DefEq.conv hRpi hMf.wf_left hMf.symm
  have hFst : Γ ⊢ Tm.fst (Tm.inl a) ≡ Tm.true ∶ Tm.bool :=
    DefEq.fstβ hbool hfamwf (DefEq.true hΓ) ha_fam
  have hSnd : Γ ⊢ Tm.snd (Tm.inl a) ≡ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.true ] :=
    DefEq.sndβ hbool hfamwf (DefEq.true hΓ) ha_fam
  have hMcong := DefEq.boolSubstCong hΓ hM hFst
  have hRecCong := DefEq.conv (DefEq.boolrec hM hL hR hFst) hMcong.wf_right hMcong
  have hRecL := hRecCong.trans (DefEq.boolβt hM hL hR)
  have hRecLpi := DefEq.conv hRecL hMt.wf_right hMt
  have hSnd_τ : Γ ⊢ Tm.snd (Tm.inl a) ≡ a ∶ τ := DefEq.conv hSnd hτ hfamt
  have happ := DefEq.app hRecLpi hSnd_τ
  rw [Tm.instSum_subst1, Tm.inl_subst1] at happ
  have hinj : Γ ⊢ Tm.inl (Tm.snd (Tm.inl a)) ≡ Tm.inl a ∶ Tm.sumT ℓ τ υ :=
    DefEq.inl hτ hυ hSnd_τ
  have hsub := DefEq.substCong hΓ (DefEq.sum hτ hυ) hρ hinj
  have happ' := DefEq.conv happ hsub.wf_right hsub
  have hlamβ := DefEq.lamβ hτ hcodl hl ha
  rw [Tm.instSum_subst1, Tm.inl_subst1] at hlamβ
  exact happ'.trans hlamβ

theorem DefEq.sumrecβr :
   Γ ⊢ τ ∶ 𝓤 ℓ → Γ ⊢ υ ∶ 𝓤 ℓ → Γ ∷ .sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ'
→ Γ ∷ τ ⊢ l ∶ ρ.instSum (.inl # 0)
→ Γ ∷ υ ⊢ r ∶ ρ.instSum (.inr # 0)
→ Γ ⊢ a ∶ υ
   -------------------------------------------------------------------
→ Γ ⊢ .sumrec ℓ τ υ ρ l r (.inr a) ≡ r [/ a ] ∶ ρ [/ .inr a ]
:= by
  intro hτ hυ hρ hl hr hb
  have hΓ := hτ.wfCtx
  have hΓτ : ⊢ Γ ∷ τ := hΓ.cons hτ
  have hΓυ : ⊢ Γ ∷ υ := hΓ.cons hυ
  have hbool := DefEq.bool hΓ
  have hfamwf := DefEq.boolFam_cong hΓ hτ hυ
  have hfamf := DefEq.boolFam_false hΓ hτ hυ
  have hM := DefEq.sumMotiveD_wf hΓ hτ hυ hρ
  have hMt := DefEq.sumMotiveD_true hΓ hτ hυ hρ
  have hMf := DefEq.sumMotiveD_false hΓ hτ hυ hρ
  have hb_fam : Γ ⊢ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] :=
    DefEq.conv hb hfamf.wf_left hfamf.symm
  have hcodl := DefEq.instSum_cong hΓ hτ hτ hυ hρ
    (DefEq.inl_wk hΓτ hτ hυ (DefEq.var hΓτ Lookup.here))
  have hLpi : Γ ⊢ (ƛ τ l) ∶ Tm.pi τ (Tm.instSum ρ (Tm.inl (# 0))) :=
    DefEq.lam hcodl hτ hl
  have hL : Γ ⊢ (ƛ τ l) ∶ (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.true ] :=
    DefEq.conv hLpi hMt.wf_left hMt.symm
  have hcodr := DefEq.instSum_cong hΓ hυ hτ hυ hρ
    (DefEq.inr_wk hΓυ hτ hυ (DefEq.var hΓυ Lookup.here))
  have hRpi : Γ ⊢ (ƛ υ r) ∶ Tm.pi υ (Tm.instSum ρ (Tm.inr (# 0))) :=
    DefEq.lam hcodr hυ hr
  have hR : Γ ⊢ (ƛ υ r) ∶ (Tm.sumMotiveD ℓ τ υ ρ) [/ Tm.false ] :=
    DefEq.conv hRpi hMf.wf_left hMf.symm
  have hFst : Γ ⊢ Tm.fst (Tm.inr a) ≡ Tm.false ∶ Tm.bool :=
    DefEq.fstβ hbool hfamwf (DefEq.false hΓ) hb_fam
  have hSnd : Γ ⊢ Tm.snd (Tm.inr a) ≡ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] :=
    DefEq.sndβ hbool hfamwf (DefEq.false hΓ) hb_fam
  have hMcong := DefEq.boolSubstCong hΓ hM hFst
  have hRecCong := DefEq.conv (DefEq.boolrec hM hL hR hFst) hMcong.wf_right hMcong
  have hRecR := hRecCong.trans (DefEq.boolβf hM hL hR)
  have hRecRpi := DefEq.conv hRecR hMf.wf_right hMf
  have hSnd_υ : Γ ⊢ Tm.snd (Tm.inr a) ≡ a ∶ υ := DefEq.conv hSnd hυ hfamf
  have happ := DefEq.app hRecRpi hSnd_υ
  rw [Tm.instSum_subst1, Tm.inr_subst1] at happ
  have hinj : Γ ⊢ Tm.inr (Tm.snd (Tm.inr a)) ≡ Tm.inr a ∶ Tm.sumT ℓ τ υ :=
    DefEq.inr hτ hυ hSnd_υ
  have hsub := DefEq.substCong hΓ (DefEq.sum hτ hυ) hρ hinj
  have happ' := DefEq.conv happ hsub.wf_right hsub
  have hlamβ := DefEq.lamβ hυ hcodr hr hb
  rw [Tm.instSum_subst1, Tm.inr_subst1] at hlamβ
  exact happ'.trans hlamβ
