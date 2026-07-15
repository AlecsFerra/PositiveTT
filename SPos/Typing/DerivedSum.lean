import SPos.Typing.Regularity


def Tm.boolFam (ℓ : Nat) (τ υ : Tm n) : Tm (n + 1) :=
  Tm.boolrec (𝓤 ℓ) (↑ τ) (↑ υ) (# 0)

def Tm.sumT (ℓ : Nat) (τ υ : Tm n) : Tm n :=
  Tm.sigma Tm.bool (Tm.boolFam ℓ τ υ)

def Tm.inl (a : Tm n) : Tm n := Tm.pair Tm.true a
def Tm.inr (b : Tm n) : Tm n := Tm.pair Tm.false b

/-- Instantiate a motive `ρ` over `Γ ∷ sumT` at `u` while staying under one ambient binder:
    variable 0 of `ρ` becomes `u`, the remaining variables keep their indices.  This is the
    dimension-preserving substitution the branch types `ρ⟨inl #0⟩` / `ρ⟨inr #0⟩` need. -/
def Tm.instSum (ρ : Tm (n + 1)) (u : Tm (n + 1)) : Tm (n + 1) :=
  (ρ.rename (Ren.lift Fin.succ)) [/ u ]

/-- The motive transported from `Γ ∷ sumT` to `Γ ∷ bool ∷ boolFam`: the sum variable becomes
    the pair `⸨#1, #0⸩` of the tag and payload variables, everything else shifts by one. -/
def Tm.sumrecMot (ρ : Tm (n + 1)) : Tm (n + 2) :=
  (ρ.rename (Ren.lift (fun i => i.succ.succ))) [/ ⸨ # (Fin.succ 0) , # 0 ⸩ ]

/-- The `boolrec` motive for the dependent sum recursor: at tag `b`, a `Π` over the payload
    family landing in the transported motive. -/
def Tm.sumMotiveD (ℓ : Nat) (τ υ : Tm n) (ρ : Tm (n + 1)) : Tm (n + 1) :=
  Tm.pi (Tm.boolFam ℓ τ υ) (Tm.sumrecMot ρ)

/-- Dependent sum recursor: recurse on the tag into the `Π`-motive, apply to the payload. -/
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

/-- Renaming is substitution by variables. -/
theorem Tm.rename_eq_subst (t : Tm n) (r : Ren n m) :
    t.rename r = t.subst (fun i => # (r i)) := by
  induction t generalizing m <;> simp_all [Tm.rename, Tm.subst]

/-- The transported motive sliced at `true` is the motive instantiated at `inl #0`. -/
theorem Tm.sumrecMot_true (ρ : Tm (n + 1)) :
    (Tm.sumrecMot ρ).subst (Subst.single Tm.true).lift = Tm.instSum ρ (Tm.inl (# 0)) := by
  simp only [Tm.sumrecMot, Tm.instSum, Tm.subst1, Tm.rename_subst, Tm.subst_subst]
  congr 1
  funext i
  induction i using Fin.cases <;>
    simp only [Subst.single, Subst.lift, Ren.lift, Fin.cases_succ, Fin.cases_zero, Tm.subst,
      Tm.rename, Tm.weaken, Tm.inl]

/-- The transported motive sliced at `false` is the motive instantiated at `inr #0`. -/
theorem Tm.sumrecMot_false (ρ : Tm (n + 1)) :
    (Tm.sumrecMot ρ).subst (Subst.single Tm.false).lift = Tm.instSum ρ (Tm.inr (# 0)) := by
  simp only [Tm.sumrecMot, Tm.instSum, Tm.subst1, Tm.rename_subst, Tm.subst_subst]
  congr 1
  funext i
  induction i using Fin.cases <;>
    simp only [Subst.single, Subst.lift, Ren.lift, Fin.cases_succ, Fin.cases_zero, Tm.subst,
      Tm.rename, Tm.weaken, Tm.inr]

/-- Slicing the transported motive at a tag and then a payload reassembles the pair. -/
theorem Tm.sumrecMot_app (ρ : Tm (n + 1)) (c₁ c₂ : Tm n) :
    ((Tm.sumrecMot ρ).subst (Subst.single c₁).lift) [/ c₂ ] = ρ [/ ⸨ c₁ , c₂ ⸩ ] := by
  simp only [Tm.sumrecMot, Tm.subst1, Tm.rename_subst, Tm.subst_subst]
  congr 1
  funext i
  induction i using Fin.cases with
  | zero =>
      simp only [Subst.single, Subst.lift, Ren.lift, Fin.cases_succ, Fin.cases_zero, Tm.subst,
        Tm.weaken]
      congr 1
      exact Tm.weaken_subst1 c₁ c₂
  | succ i =>
      simp only [Subst.single, Subst.lift, Ren.lift, Fin.cases_succ, Tm.subst,
        Tm.rename, Tm.weaken]

/-- Instantiating under the ambient binder and then substituting the binder collapses. -/
theorem Tm.instSum_subst1 (ρ : Tm (n + 1)) (u : Tm (n + 1)) (a : Tm n) :
    (Tm.instSum ρ u) [/ a ] = ρ [/ u [/ a ] ] := by
  simp only [Tm.instSum, Tm.subst1, Tm.rename_subst, Tm.subst_subst]
  congr 1
  funext i
  induction i using Fin.cases <;>
    simp only [Subst.single, Ren.lift, Fin.cases_succ, Fin.cases_zero, Tm.subst]

theorem Tm.inl_subst1 (a : Tm n) : (Tm.inl (# 0) : Tm (n + 1)) [/ a ] = Tm.inl a := by
  simp [Tm.inl, Tm.subst1, Tm.subst, Subst.single]

theorem Tm.inr_subst1 (b : Tm n) : (Tm.inr (# 0) : Tm (n + 1)) [/ b ] = Tm.inr b := by
  simp [Tm.inr, Tm.subst1, Tm.subst, Subst.single]

variable {Γ : Ctx n}

theorem DefEq.boolFam_wf (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ∷ Tm.bool ⊢ Tm.boolFam ℓ τ υ ∶ 𝓤 ℓ := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hΓbb : ⊢ Γ ∷ Tm.bool ∷ Tm.bool := hΓb.cons (DefEq.bool hΓb)
  -- boolrec with a constant motive `𝓤 ℓ`; branches `↑τ`, `↑υ`; scrutinee `#0`.
  have hP : Γ ∷ Tm.bool ∷ Tm.bool ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1) := DefEq.u hΓbb
  have ht : Γ ∷ Tm.bool ⊢ ↑ τ ∶ (𝓤 ℓ) [/ Tm.true ] := by
    show Γ ∷ Tm.bool ⊢ ↑ τ ∶ 𝓤 ℓ
    exact WfTm.weaken hτ hΓb
  have hf : Γ ∷ Tm.bool ⊢ ↑ υ ∶ (𝓤 ℓ) [/ Tm.false ] := by
    show Γ ∷ Tm.bool ⊢ ↑ υ ∶ 𝓤 ℓ
    exact WfTm.weaken hυ hΓb
  have hb : Γ ∷ Tm.bool ⊢ (# 0) ∶ Tm.bool := DefEq.var hΓb Lookup.here
  show Γ ∷ Tm.bool ⊢ _ ∶ (𝓤 ℓ) [/ (# 0) ]
  exact DefEq.boolrec hP ht hf hb

theorem DefEq.sumT_wf (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ Tm.sumT ℓ τ υ ∶ 𝓤 ℓ := by
  have h := DefEq.sigma (DefEq.bool hΓ) (DefEq.boolFam_wf hΓ hτ hυ)
  rw [Nat.zero_max] at h
  exact h

theorem DefEq.boolFam_true (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ (Tm.boolFam ℓ τ υ) [/ Tm.true ] ≡ τ ∶ 𝓤 ℓ := by
  have hP : Γ ∷ Tm.bool ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1) := DefEq.u (hΓ.cons (DefEq.bool hΓ))
  have ht : Γ ⊢ τ ∶ (𝓤 ℓ) [/ Tm.true ] := by show Γ ⊢ τ ∶ 𝓤 ℓ; exact hτ
  have hf : Γ ⊢ υ ∶ (𝓤 ℓ) [/ Tm.false ] := by show Γ ⊢ υ ∶ 𝓤 ℓ; exact hυ
  -- `boolrec (𝓤 ℓ) τ υ true ≡ τ`; the LHS is exactly `boolFam[/true]`.
  have hβ := DefEq.boolβt hP ht hf
  simpa [Tm.boolFam, Tm.subst1, Tm.subst, Tm.weaken, Subst.single] using hβ

theorem DefEq.boolFam_false (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ (Tm.boolFam ℓ τ υ) [/ Tm.false ] ≡ υ ∶ 𝓤 ℓ := by
  have hP : Γ ∷ Tm.bool ⊢ 𝓤 ℓ ∶ 𝓤 (ℓ + 1) := DefEq.u (hΓ.cons (DefEq.bool hΓ))
  have ht : Γ ⊢ τ ∶ (𝓤 ℓ) [/ Tm.true ] := by show Γ ⊢ τ ∶ 𝓤 ℓ; exact hτ
  have hf : Γ ⊢ υ ∶ (𝓤 ℓ) [/ Tm.false ] := by show Γ ⊢ υ ∶ 𝓤 ℓ; exact hυ
  have hβ := DefEq.boolβf hP ht hf
  simpa [Tm.boolFam, Tm.subst1, Tm.subst, Tm.weaken, Subst.single] using hβ

theorem DefEq.inl_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (ha : Γ ⊢ a₁ ≡ a₂ ∶ τ) : Γ ⊢ Tm.inl a₁ ≡ Tm.inl a₂ ∶ Tm.sumT ℓ τ υ := by
  have hfam := DefEq.boolFam_true hΓ hτ hυ
  have ha' : Γ ⊢ a₁ ≡ a₂ ∶ (Tm.boolFam ℓ τ υ) [/ Tm.true ] :=
    DefEq.conv ha hfam.wf_left hfam.symm
  exact DefEq.pair (DefEq.bool hΓ) (DefEq.boolFam_wf hΓ hτ hυ) (DefEq.true hΓ) ha'

theorem DefEq.inr_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hb : Γ ⊢ b₁ ≡ b₂ ∶ υ) : Γ ⊢ Tm.inr b₁ ≡ Tm.inr b₂ ∶ Tm.sumT ℓ τ υ := by
  have hfam := DefEq.boolFam_false hΓ hτ hυ
  have hb' : Γ ⊢ b₁ ≡ b₂ ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] :=
    DefEq.conv hb hfam.wf_left hfam.symm
  exact DefEq.pair (DefEq.bool hΓ) (DefEq.boolFam_wf hΓ hτ hυ) (DefEq.false hΓ) hb'

/-- Non-dependent sum eliminator, derived by recursing into a `Π`-type and applying to
    `snd c`: `boolrec (Π (boolFam #0) (↑↑ρ)) (ƛτ l) (ƛυ r) (fst c) • snd c`. -/
def Tm.sumMotive (ℓ : Nat) (ρ τ υ : Tm n) : Tm (n + 1) :=
  Tm.pi (Tm.boolFam ℓ τ υ) (Tm.weaken (↑ ρ))

def Tm.sumElim (ℓ : Nat) (ρ τ υ : Tm n) (l r : Tm (n + 1)) (c : Tm n) : Tm n :=
  (Tm.boolrec (Tm.sumMotive ℓ ρ τ υ) (ƛ τ l) (ƛ υ r) (Tm.fst c)) • (Tm.snd c)

/-- The motive at `true`: `(Π (boolFam) ↑↑ρ)[/true] ≡ Π τ (↑ρ)`. -/
theorem DefEq.sumMotive_true (hΓ : ⊢ Γ) (hρ : Γ ⊢ ρ ∶ 𝓤 ℓρ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ)
    (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.true ] ≡ Tm.pi τ ρ.weaken ∶ 𝓤 (max ℓ ℓρ) := by
  have hcod : (ρ.weaken.weaken).subst (Subst.single Tm.true).lift = ρ.weaken := by
    rw [Tm.weaken_subst]; congr 1; exact Tm.weaken_subst1 ρ Tm.true
  have key : (Tm.sumMotive ℓ ρ τ υ) [/ Tm.true ]
      = Tm.pi ((Tm.boolFam ℓ τ υ) [/ Tm.true ]) ρ.weaken := by
    simp only [Tm.sumMotive, Tm.subst1, Tm.subst, hcod]
  rw [key]
  have hfam := DefEq.boolFam_true hΓ hτ hυ
  exact DefEq.pi hfam (WfTm.weaken hρ (hΓ.cons hfam.wf_left))

/-- The motive at `false`: `(Π (boolFam) ↑↑ρ)[/false] ≡ Π υ (↑ρ)`. -/
theorem DefEq.sumMotive_false (hΓ : ⊢ Γ) (hρ : Γ ⊢ ρ ∶ 𝓤 ℓρ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ)
    (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ⊢ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.false ] ≡ Tm.pi υ ρ.weaken ∶ 𝓤 (max ℓ ℓρ) := by
  have hcod : (ρ.weaken.weaken).subst (Subst.single Tm.false).lift = ρ.weaken := by
    rw [Tm.weaken_subst]; congr 1; exact Tm.weaken_subst1 ρ Tm.false
  have key : (Tm.sumMotive ℓ ρ τ υ) [/ Tm.false ]
      = Tm.pi ((Tm.boolFam ℓ τ υ) [/ Tm.false ]) ρ.weaken := by
    simp only [Tm.sumMotive, Tm.subst1, Tm.subst, hcod]
  rw [key]
  have hfam := DefEq.boolFam_false hΓ hτ hυ
  exact DefEq.pi hfam (WfTm.weaken hρ (hΓ.cons hfam.wf_left))

/-- The motive is well-formed over `Γ ∷ Bool`. -/
theorem DefEq.sumMotive_wf (hΓ : ⊢ Γ) (hρ : Γ ⊢ ρ ∶ 𝓤 ℓρ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ)
    (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ∷ Tm.bool ⊢ Tm.sumMotive ℓ ρ τ υ ∶ 𝓤 (max ℓ ℓρ) := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hfam := DefEq.boolFam_wf hΓ hτ hυ
  have hcod : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ Tm.weaken (↑ ρ) ∶ 𝓤 ℓρ :=
    WfTm.weaken (WfTm.weaken hρ hΓb) (hΓb.cons hfam)
  exact DefEq.pi hfam hcod

/-- Reducing the eliminator's result type: the `Π`-codomain `↑↑ρ` substituted at any pair of
    terms collapses back to `ρ` (two `weaken` cancellations). -/
theorem Tm.sumElim_codomain (ρ v w : Tm n) :
    (Tm.subst (Subst.single v).lift (ρ.weaken.weaken)) [/ w ] = ρ := by
  have e1 : Tm.subst (Subst.single v).lift (ρ.weaken.weaken) = ρ.weaken := by
    rw [Tm.weaken_subst]; congr 1; exact Tm.weaken_subst1 ρ v
  rw [e1]; exact Tm.weaken_subst1 ρ w

/-- Sum eliminator typing / congruence (the "equivalence" rule): `sumElim` respects DefEq in all
    of the two branches and the scrutinee, landing in the (non-dependent) result type `ρ`. -/
theorem DefEq.sumElim_cong (hΓ : ⊢ Γ) (hρ : Γ ⊢ ρ ∶ 𝓤 ℓρ)
    (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hl : Γ ∷ τ ⊢ l₁ ≡ l₂ ∶ ρ.weaken) (hr : Γ ∷ υ ⊢ r₁ ≡ r₂ ∶ ρ.weaken)
    (hc : Γ ⊢ c₁ ≡ c₂ ∶ Tm.sumT ℓ τ υ) :
    Γ ⊢ Tm.sumElim ℓ ρ τ υ l₁ r₁ c₁ ≡ Tm.sumElim ℓ ρ τ υ l₂ r₂ c₂ ∶ ρ := by
  have hM := DefEq.sumMotive_wf hΓ hρ hτ hυ
  have hMt := DefEq.sumMotive_true hΓ hρ hτ hυ
  have hMf := DefEq.sumMotive_false hΓ hρ hτ hυ
  -- the two branches, converted from the clean `Π τ ↑ρ` / `Π υ ↑ρ` to the motive at `true`/`false`.
  have hLpi : Γ ⊢ (ƛ τ l₁) ≡ (ƛ τ l₂) ∶ Tm.pi τ ρ.weaken :=
    DefEq.lam (WfTm.weaken hρ (hΓ.cons hτ)) hτ hl
  have hL : Γ ⊢ (ƛ τ l₁) ≡ (ƛ τ l₂) ∶ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.true ] :=
    DefEq.conv hLpi hMt.wf_left hMt.symm
  have hRpi : Γ ⊢ (ƛ υ r₁) ≡ (ƛ υ r₂) ∶ Tm.pi υ ρ.weaken :=
    DefEq.lam (WfTm.weaken hρ (hΓ.cons hυ)) hυ hr
  have hR : Γ ⊢ (ƛ υ r₁) ≡ (ƛ υ r₂) ∶ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.false ] :=
    DefEq.conv hRpi hMf.wf_left hMf.symm
  -- `fst`/`snd` congruence off the scrutinee (`sumT = Σ̶ bool boolFam`).
  have hFst : Γ ⊢ Tm.fst c₁ ≡ Tm.fst c₂ ∶ Tm.bool := DefEq.fst hc
  have hSnd : Γ ⊢ Tm.snd c₁ ≡ Tm.snd c₂ ∶ (Tm.boolFam ℓ τ υ) [/ Tm.fst c₁ ] := DefEq.snd hc
  -- recurse into the `Π`-motive, then apply to `snd c`.
  have hRec := DefEq.boolrec hM hL hR hFst
  have happ := DefEq.app hRec hSnd
  rw [Tm.sumElim_codomain] at happ
  exact happ

/-- Substitution congruence for a `Bool`-indexed type family, via the λ-trick: `M[/v₁] ≡ M[/v₂]`
    whenever `v₁ ≡ v₂ ∶ Bool`.  `M[/v] = (ƛbool M) • v` up to `lamβ`, and application is a
    congruence. This is what the primitive `Bool.rec` lacks (its scrutinee only ever converts
    against `true`/`false`), so we derive it here to line up the eliminator's β types. -/
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

/-- Sum β for the left injection: `sumElim … (inl a) ≡ l[/a]`. -/
theorem DefEq.sumβl (hΓ : ⊢ Γ) (hρ : Γ ⊢ ρ ∶ 𝓤 ℓρ)
    (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hl : Γ ∷ τ ⊢ l ∶ ρ.weaken) (hr : Γ ∷ υ ⊢ r ∶ ρ.weaken)
    (ha : Γ ⊢ a ∶ τ) :
    Γ ⊢ Tm.sumElim ℓ ρ τ υ l r (Tm.inl a) ≡ l [/ a ] ∶ ρ := by
  have hbool := DefEq.bool hΓ
  have hfamwf := DefEq.boolFam_wf hΓ hτ hυ
  have hfamt := DefEq.boolFam_true hΓ hτ hυ
  have hM := DefEq.sumMotive_wf hΓ hρ hτ hυ
  have hMt := DefEq.sumMotive_true hΓ hρ hτ hυ
  -- `a` at the family's `true` slice.
  have ha_fam : Γ ⊢ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.true ] := DefEq.conv ha hfamt.wf_left hfamt.symm
  -- the two branches at their motive slices.
  have hLpi : Γ ⊢ (ƛ τ l) ∶ Tm.pi τ ρ.weaken := DefEq.lam (WfTm.weaken hρ (hΓ.cons hτ)) hτ hl
  have hL : Γ ⊢ (ƛ τ l) ∶ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.true ] := DefEq.conv hLpi hMt.wf_left hMt.symm
  have hRpi : Γ ⊢ (ƛ υ r) ∶ Tm.pi υ ρ.weaken := DefEq.lam (WfTm.weaken hρ (hΓ.cons hυ)) hυ hr
  have hR : Γ ⊢ (ƛ υ r) ∶ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.false ] :=
    DefEq.conv hRpi (DefEq.sumMotive_false hΓ hρ hτ hυ).wf_left (DefEq.sumMotive_false hΓ hρ hτ hυ).symm
  -- `fst (inl a) ≡ true`, `snd (inl a) ≡ a`.
  have hFst : Γ ⊢ Tm.fst (Tm.inl a) ≡ Tm.true ∶ Tm.bool :=
    DefEq.fstβ hbool hfamwf (DefEq.true hΓ) ha_fam
  have hSnd : Γ ⊢ Tm.snd (Tm.inl a) ≡ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.true ] :=
    DefEq.sndβ hbool hfamwf (DefEq.true hΓ) ha_fam
  -- `boolrec … (fst (inl a)) ≡ boolrec … true`, retyped to `M[/true]`, then β to `ƛτ l`.
  have hMcong := DefEq.boolSubstCong hΓ hM hFst
  have hRecCong := DefEq.conv (DefEq.boolrec hM hL hR hFst) hMcong.wf_right hMcong
  have hRecL := hRecCong.trans (DefEq.boolβt hM hL hR)
  -- retype to `Π τ ↑ρ` and apply to `snd (inl a) ≡ a`.
  have hRecLpi := DefEq.conv hRecL hMt.wf_right hMt
  have hSnd_τ : Γ ⊢ Tm.snd (Tm.inl a) ≡ a ∶ τ := DefEq.conv hSnd hτ hfamt
  have happ := DefEq.app hRecLpi hSnd_τ
  have hlamβ := DefEq.lamβ hτ (WfTm.weaken hρ (hΓ.cons hτ)) hl ha
  rw [Tm.weaken_subst1] at happ hlamβ
  exact happ.trans hlamβ

/-- Sum β for the right injection: `sumElim … (inr b) ≡ r[/b]`. -/
theorem DefEq.sumβr (hΓ : ⊢ Γ) (hρ : Γ ⊢ ρ ∶ 𝓤 ℓρ)
    (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hl : Γ ∷ τ ⊢ l ∶ ρ.weaken) (hr : Γ ∷ υ ⊢ r ∶ ρ.weaken)
    (hb : Γ ⊢ b ∶ υ) :
    Γ ⊢ Tm.sumElim ℓ ρ τ υ l r (Tm.inr b) ≡ r [/ b ] ∶ ρ := by
  have hbool := DefEq.bool hΓ
  have hfamwf := DefEq.boolFam_wf hΓ hτ hυ
  have hfamf := DefEq.boolFam_false hΓ hτ hυ
  have hM := DefEq.sumMotive_wf hΓ hρ hτ hυ
  have hMf := DefEq.sumMotive_false hΓ hρ hτ hυ
  have hb_fam : Γ ⊢ b ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] := DefEq.conv hb hfamf.wf_left hfamf.symm
  have hLpi : Γ ⊢ (ƛ τ l) ∶ Tm.pi τ ρ.weaken := DefEq.lam (WfTm.weaken hρ (hΓ.cons hτ)) hτ hl
  have hL : Γ ⊢ (ƛ τ l) ∶ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.true ] :=
    DefEq.conv hLpi (DefEq.sumMotive_true hΓ hρ hτ hυ).wf_left (DefEq.sumMotive_true hΓ hρ hτ hυ).symm
  have hRpi : Γ ⊢ (ƛ υ r) ∶ Tm.pi υ ρ.weaken := DefEq.lam (WfTm.weaken hρ (hΓ.cons hυ)) hυ hr
  have hR : Γ ⊢ (ƛ υ r) ∶ (Tm.sumMotive ℓ ρ τ υ) [/ Tm.false ] := DefEq.conv hRpi hMf.wf_left hMf.symm
  have hFst : Γ ⊢ Tm.fst (Tm.inr b) ≡ Tm.false ∶ Tm.bool :=
    DefEq.fstβ hbool hfamwf (DefEq.false hΓ) hb_fam
  have hSnd : Γ ⊢ Tm.snd (Tm.inr b) ≡ b ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] :=
    DefEq.sndβ hbool hfamwf (DefEq.false hΓ) hb_fam
  have hMcong := DefEq.boolSubstCong hΓ hM hFst
  have hRecCong := DefEq.conv (DefEq.boolrec hM hL hR hFst) hMcong.wf_right hMcong
  have hRecR := hRecCong.trans (DefEq.boolβf hM hL hR)
  have hRecRpi := DefEq.conv hRecR hMf.wf_right hMf
  have hSnd_υ : Γ ⊢ Tm.snd (Tm.inr b) ≡ b ∶ υ := DefEq.conv hSnd hυ hfamf
  have happ := DefEq.app hRecRpi hSnd_υ
  have hlamβ := DefEq.lamβ hυ (WfTm.weaken hρ (hΓ.cons hυ)) hr hb
  rw [Tm.weaken_subst1] at happ hlamβ
  exact happ.trans hlamβ

/-! ### Dependent sum recursor

The rules requested in `SPos.lean`: formation/introduction congruence for the derived sums,
plus a fully dependent recursor `sumrec` with motive `ρ` over `Γ ∷ sumT`, its congruence rule
(at result type `ρ₁[/s₁]`, via `pairη`) and both β-rules. -/

/-- Formation: `boolFam` respects `DefEq` in both branches. -/
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

/-- Formation congruence for the derived sum type. -/
theorem DefEq.sum_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ₁ ≡ υ₂ ∶ 𝓤 ℓ) :
    Γ ⊢ Tm.sumT ℓ τ₁ υ₁ ≡ Tm.sumT ℓ τ₂ υ₂ ∶ 𝓤 ℓ := by
  have h := DefEq.sigma (DefEq.bool hΓ) (DefEq.boolFam_cong hΓ hτ hυ)
  rw [Nat.zero_max] at h
  exact h

/-- Introduction congruence for `inl`, with the type arguments also up to `DefEq` (the
    injections carry no annotations, so only the payload congruence does real work). -/
theorem DefEq.injl_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ₁ ≡ υ₂ ∶ 𝓤 ℓ)
    (ha : Γ ⊢ a₁ ≡ a₂ ∶ τ₁) : Γ ⊢ Tm.inl a₁ ≡ Tm.inl a₂ ∶ Tm.sumT ℓ τ₁ υ₁ :=
  DefEq.inl_cong hΓ hτ.wf_left hυ.wf_left ha

theorem DefEq.injr_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ₁ ≡ τ₂ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ₁ ≡ υ₂ ∶ 𝓤 ℓ)
    (hb : Γ ⊢ b₁ ≡ b₂ ∶ υ₁) : Γ ⊢ Tm.inr b₁ ≡ Tm.inr b₂ ∶ Tm.sumT ℓ τ₁ υ₁ :=
  DefEq.inr_cong hΓ hτ.wf_left hυ.wf_left hb

/-- λ-trick substitution congruence at an arbitrary type: `M[/v₁] ≡ M[/v₂]` whenever
    `v₁ ≡ v₂ ∶ A`.  Generalizes `boolSubstCong`. -/
theorem DefEq.substCong (hΓ : ⊢ Γ) (hA : Γ ⊢ A ∶ 𝓤 k) (hM : Γ ∷ A ⊢ M ∶ 𝓤 s)
    (hv : Γ ⊢ v₁ ≡ v₂ ∶ A) : Γ ⊢ M [/ v₁ ] ≡ M [/ v₂ ] ∶ 𝓤 s := by
  have hU : Γ ∷ A ⊢ 𝓤 s ∶ 𝓤 (s + 1) := DefEq.u (hΓ.cons hA)
  have hlam : Γ ⊢ (ƛ A M) ≡ (ƛ A M) ∶ Tm.pi A (𝓤 s) := DefEq.lam hU hA hM
  have happ := DefEq.app hlam hv
  have hβ1 := DefEq.lamβ hA hU hM hv.wf_left
  have hβ2 := DefEq.lamβ hA hU hM hv.wf_right
  exact (hβ1.symm.trans happ).trans hβ2

/-- Weakened injections: `inl` lands in the weakened sum over any extended context. -/
theorem DefEq.inl_wk (hΓB : ⊢ Γ ∷ B) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (ha : Γ ∷ B ⊢ a ∶ τ.weaken) : Γ ∷ B ⊢ Tm.inl a ∶ (Tm.sumT ℓ τ υ).weaken := by
  rw [Tm.sumT_weaken]
  exact DefEq.inl_cong hΓB (WfTm.weaken hτ hΓB) (WfTm.weaken hυ hΓB) ha

theorem DefEq.inr_wk (hΓB : ⊢ Γ ∷ B) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hb : Γ ∷ B ⊢ b ∶ υ.weaken) : Γ ∷ B ⊢ Tm.inr b ∶ (Tm.sumT ℓ τ υ).weaken := by
  rw [Tm.sumT_weaken]
  exact DefEq.inr_cong hΓB (WfTm.weaken hτ hΓB) (WfTm.weaken hυ hΓB) hb

/-- The tag/payload pair of variables is a sum in the transported context. -/
theorem DefEq.pair_var10 (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) :
    Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ ⸨ # (Fin.succ 0) , # 0 ⸩
      ∶ (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ) := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hfam := DefEq.boolFam_wf hΓ hτ hυ
  have hΔ : ⊢ Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ := hΓb.cons hfam
  have hτ2 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ τ.weaken.weaken ∶ 𝓤 ℓ :=
    WfTm.weaken (WfTm.weaken hτ hΓb) hΔ
  have hυ2 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ υ.weaken.weaken ∶ 𝓤 ℓ :=
    WfTm.weaken (WfTm.weaken hυ hΓb) hΔ
  have h1 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ # (Fin.succ 0) ∶ Tm.bool :=
    DefEq.var hΔ (Lookup.there Lookup.here)
  have h0 : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ
      ⊢ # 0 ∶ (Tm.boolFam ℓ τ.weaken.weaken υ.weaken.weaken) [/ # (Fin.succ 0) ] := by
    have hlook := DefEq.var hΔ Lookup.here
    have e : (Tm.boolFam ℓ τ.weaken.weaken υ.weaken.weaken) [/ (# (Fin.succ 0) : Tm (n + 2)) ]
        = (Tm.boolFam ℓ τ υ).weaken := by
      simp [Tm.boolFam, Tm.weaken, Tm.subst1, Tm.subst, Subst.single, Tm.rename_eq_subst]
    rw [e]
    exact hlook
  have hpair := DefEq.pair (DefEq.bool hΔ) (DefEq.boolFam_wf hΔ hτ2 hυ2) h1 h0
  have esum : (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ)
      = Tm.sumT ℓ τ.weaken.weaken υ.weaken.weaken := by
    simp [Tm.sumT_rename, Tm.weaken, Tm.rename_rename, Function.comp_def]
  rw [esum]
  exact hpair

/-- Transporting the motive to `Γ ∷ bool ∷ boolFam` preserves `DefEq`. -/
theorem DefEq.sumrecMot_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ') :
    Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ ⊢ Tm.sumrecMot ρ₁ ≡ Tm.sumrecMot ρ₂ ∶ 𝓤 ℓ' := by
  have hΓb : ⊢ Γ ∷ Tm.bool := hΓ.cons (DefEq.bool hΓ)
  have hfam := DefEq.boolFam_wf hΓ hτ hυ
  have hΔ : ⊢ Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ := hΓb.cons hfam
  have hτ2 := WfTm.weaken (WfTm.weaken hτ hΓb) hΔ
  have hυ2 := WfTm.weaken (WfTm.weaken hυ hΓb) hΔ
  have hpair := DefEq.pair_var10 hΓ hτ hυ
  have hsumR : Γ ∷ Tm.bool ∷ Tm.boolFam ℓ τ υ
      ⊢ (Tm.sumT ℓ τ υ).rename (fun i => i.succ.succ) ∶ 𝓤 ℓ := by
    have h := DefEq.sumT_wf hΔ hτ2 hυ2
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
  DefEq.pi (DefEq.boolFam_wf hΓ hτ hυ) (DefEq.sumrecMot_cong hΓ hτ hυ hρ)

theorem DefEq.sumMotiveD_wf (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ') :
    Γ ∷ Tm.bool ⊢ Tm.sumMotiveD ℓ τ υ ρ ∶ 𝓤 (max ℓ ℓ') :=
  DefEq.sumMotiveD_cong hΓ hτ hυ hρ

/-- `instSum` preserves `DefEq` of motives over any context extension `B`, whenever the
    instantiating term is a (weakened) sum. -/
theorem DefEq.instSum_cong (hΓ : ⊢ Γ) (hB : Γ ⊢ B ∶ 𝓤 k) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ)
    (hυ : Γ ⊢ υ ∶ 𝓤 ℓ) (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ')
    (hw : Γ ∷ B ⊢ w ∶ (Tm.sumT ℓ τ υ).weaken) :
    Γ ∷ B ⊢ Tm.instSum ρ₁ w ≡ Tm.instSum ρ₂ w ∶ 𝓤 ℓ' := by
  have hΓB : ⊢ Γ ∷ B := hΓ.cons hB
  have hΓBs : ⊢ Γ ∷ B ∷ (Tm.sumT ℓ τ υ).weaken :=
    hΓB.cons (WfTm.weaken (DefEq.sumT_wf hΓ hτ hυ) hΓB)
  have hren := DefEq.rename hρ hΓBs (Ren.WellTyped.lift (Ren.succ_wellTyped Γ B))
  exact DefEq.subst1 hren hw hΓB

/-- The dependent motive at `true` is `Π τ (ρ⟨inl #0⟩)` up to `DefEq`. -/
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

/-- The dependent motive at `false` is `Π υ (ρ⟨inr #0⟩)` up to `DefEq`. -/
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

/-- Dependent sum recursor congruence, at the dependent result type `ρ₁[/s₁]`.  The final
    conversion `ρ₁[/⸨fst s₁, snd s₁⸩] ≡ ρ₁[/s₁]` is where `pairη` is essential: dependent
    elimination from a negative `Σ` is exactly surjective pairing. -/
theorem DefEq.sumrec_cong (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ₁ ≡ ρ₂ ∶ 𝓤 ℓ')
    (hs : Γ ⊢ s₁ ≡ s₂ ∶ Tm.sumT ℓ τ υ)
    (hl : Γ ∷ τ ⊢ l₁ ≡ l₂ ∶ Tm.instSum ρ₁ (Tm.inl (# 0)))
    (hr : Γ ∷ υ ⊢ r₁ ≡ r₂ ∶ Tm.instSum ρ₁ (Tm.inr (# 0))) :
    Γ ⊢ Tm.sumrec ℓ τ υ ρ₁ l₁ r₁ s₁ ≡ Tm.sumrec ℓ τ υ ρ₂ l₂ r₂ s₂ ∶ ρ₁ [/ s₁ ] := by
  have hΓτ : ⊢ Γ ∷ τ := hΓ.cons hτ
  have hΓυ : ⊢ Γ ∷ υ := hΓ.cons hυ
  have hM := DefEq.sumMotiveD_cong hΓ hτ hυ hρ
  have hMt := DefEq.sumMotiveD_true hΓ hτ hυ hρ.wf_left
  have hMf := DefEq.sumMotiveD_false hΓ hτ hυ hρ.wf_left
  -- branch λs, converted to the motive slices
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
  -- recurse on the tag, apply to the payload
  have hRec := DefEq.boolrec hM hL hR (DefEq.fst hs)
  have happ := DefEq.app hRec (DefEq.snd hs)
  rw [Tm.sumrecMot_app] at happ
  -- Σ-η rebuilds the scrutinee
  have hη := DefEq.pairη hs.wf_left
  have hsub := DefEq.substCong hΓ (DefEq.sumT_wf hΓ hτ hυ) hρ.wf_left hη.symm
  exact DefEq.conv happ hsub.wf_right hsub

/-- Dependent sum β at `inl`: `sumrec ρ l r (inl a) ≡ l[/a] ∶ ρ[/inl a]`. -/
theorem DefEq.sumrecβl (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ')
    (hl : Γ ∷ τ ⊢ l ∶ Tm.instSum ρ (Tm.inl (# 0)))
    (hr : Γ ∷ υ ⊢ r ∶ Tm.instSum ρ (Tm.inr (# 0)))
    (ha : Γ ⊢ a ∶ τ) :
    Γ ⊢ Tm.sumrec ℓ τ υ ρ l r (Tm.inl a) ≡ l [/ a ] ∶ ρ [/ Tm.inl a ] := by
  have hΓτ : ⊢ Γ ∷ τ := hΓ.cons hτ
  have hΓυ : ⊢ Γ ∷ υ := hΓ.cons hυ
  have hbool := DefEq.bool hΓ
  have hfamwf := DefEq.boolFam_wf hΓ hτ hυ
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
  -- projections of `inl a`
  have hFst : Γ ⊢ Tm.fst (Tm.inl a) ≡ Tm.true ∶ Tm.bool :=
    DefEq.fstβ hbool hfamwf (DefEq.true hΓ) ha_fam
  have hSnd : Γ ⊢ Tm.snd (Tm.inl a) ≡ a ∶ (Tm.boolFam ℓ τ υ) [/ Tm.true ] :=
    DefEq.sndβ hbool hfamwf (DefEq.true hΓ) ha_fam
  -- reduce the recursor to the left λ, retyped at the `true` slice
  have hMcong := DefEq.boolSubstCong hΓ hM hFst
  have hRecCong := DefEq.conv (DefEq.boolrec hM hL hR hFst) hMcong.wf_right hMcong
  have hRecL := hRecCong.trans (DefEq.boolβt hM hL hR)
  have hRecLpi := DefEq.conv hRecL hMt.wf_right hMt
  have hSnd_τ : Γ ⊢ Tm.snd (Tm.inl a) ≡ a ∶ τ := DefEq.conv hSnd hτ hfamt
  have happ := DefEq.app hRecLpi hSnd_τ
  rw [Tm.instSum_subst1, Tm.inl_subst1] at happ
  -- retype `ρ[/inl (snd (inl a))]` at `ρ[/inl a]`
  have hinj : Γ ⊢ Tm.inl (Tm.snd (Tm.inl a)) ≡ Tm.inl a ∶ Tm.sumT ℓ τ υ :=
    DefEq.inl_cong hΓ hτ hυ hSnd_τ
  have hsub := DefEq.substCong hΓ (DefEq.sumT_wf hΓ hτ hυ) hρ hinj
  have happ' := DefEq.conv happ hsub.wf_right hsub
  have hlamβ := DefEq.lamβ hτ hcodl hl ha
  rw [Tm.instSum_subst1, Tm.inl_subst1] at hlamβ
  exact happ'.trans hlamβ

/-- Dependent sum β at `inr`: `sumrec ρ l r (inr b) ≡ r[/b] ∶ ρ[/inr b]`. -/
theorem DefEq.sumrecβr (hΓ : ⊢ Γ) (hτ : Γ ⊢ τ ∶ 𝓤 ℓ) (hυ : Γ ⊢ υ ∶ 𝓤 ℓ)
    (hρ : Γ ∷ Tm.sumT ℓ τ υ ⊢ ρ ∶ 𝓤 ℓ')
    (hl : Γ ∷ τ ⊢ l ∶ Tm.instSum ρ (Tm.inl (# 0)))
    (hr : Γ ∷ υ ⊢ r ∶ Tm.instSum ρ (Tm.inr (# 0)))
    (hb : Γ ⊢ b ∶ υ) :
    Γ ⊢ Tm.sumrec ℓ τ υ ρ l r (Tm.inr b) ≡ r [/ b ] ∶ ρ [/ Tm.inr b ] := by
  have hΓτ : ⊢ Γ ∷ τ := hΓ.cons hτ
  have hΓυ : ⊢ Γ ∷ υ := hΓ.cons hυ
  have hbool := DefEq.bool hΓ
  have hfamwf := DefEq.boolFam_wf hΓ hτ hυ
  have hfamf := DefEq.boolFam_false hΓ hτ hυ
  have hM := DefEq.sumMotiveD_wf hΓ hτ hυ hρ
  have hMt := DefEq.sumMotiveD_true hΓ hτ hυ hρ
  have hMf := DefEq.sumMotiveD_false hΓ hτ hυ hρ
  have hb_fam : Γ ⊢ b ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] :=
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
  have hFst : Γ ⊢ Tm.fst (Tm.inr b) ≡ Tm.false ∶ Tm.bool :=
    DefEq.fstβ hbool hfamwf (DefEq.false hΓ) hb_fam
  have hSnd : Γ ⊢ Tm.snd (Tm.inr b) ≡ b ∶ (Tm.boolFam ℓ τ υ) [/ Tm.false ] :=
    DefEq.sndβ hbool hfamwf (DefEq.false hΓ) hb_fam
  have hMcong := DefEq.boolSubstCong hΓ hM hFst
  have hRecCong := DefEq.conv (DefEq.boolrec hM hL hR hFst) hMcong.wf_right hMcong
  have hRecR := hRecCong.trans (DefEq.boolβf hM hL hR)
  have hRecRpi := DefEq.conv hRecR hMf.wf_right hMf
  have hSnd_υ : Γ ⊢ Tm.snd (Tm.inr b) ≡ b ∶ υ := DefEq.conv hSnd hυ hfamf
  have happ := DefEq.app hRecRpi hSnd_υ
  rw [Tm.instSum_subst1, Tm.inr_subst1] at happ
  have hinj : Γ ⊢ Tm.inr (Tm.snd (Tm.inr b)) ≡ Tm.inr b ∶ Tm.sumT ℓ τ υ :=
    DefEq.inr_cong hΓ hτ hυ hSnd_υ
  have hsub := DefEq.substCong hΓ (DefEq.sumT_wf hΓ hτ hυ) hρ hinj
  have happ' := DefEq.conv happ hsub.wf_right hsub
  have hlamβ := DefEq.lamβ hυ hcodr hr hb
  rw [Tm.instSum_subst1, Tm.inr_subst1] at hlamβ
  exact happ'.trans hlamβ
