import SPos.Typing.Typing
import SPos.Typing.TypingProperties

def Ren.WellTyped (r : Ren n m) (Γ : Ctx n) (Δ : Ctx m) : Prop :=
  ∀ {x : Fin n} {τ : Tm n}, (Γ ∋ x ∶ τ) → (Δ ∋ r x ∶ τ.rename r)

theorem Ren.WellTyped.lift {r : Ren n m} (hr : Ren.WellTyped r Γ Δ) {τ : Tm n} :
    Ren.WellTyped (Ren.lift r) (Γ ∷ τ) (Δ ∷ τ.rename r) := by
  intro x A hlook
  rcases hlook.inv rfl with ⟨rfl, rfl⟩ | ⟨j, τ', rfl, rfl, hj⟩
  · have h : Ren.lift r 0 = 0 := by simp [Ren.lift]
    rw [h, Tm.weaken_rename]
    constructor
  · have h : Ren.lift r j.succ = (r j).succ := by simp [Ren.lift]
    rw [h, Tm.weaken_rename]
    exact Lookup.there (hr hj)

theorem Ren.WellTyped.lift2 {r : Ren n m} (hr : Ren.WellTyped r Γ Δ) {τ : Tm n} {υ : Tm (n + 1)} :
    Ren.WellTyped (Ren.lift (Ren.lift r)) (Γ ∷ τ ∷ υ)
      (Δ ∷ τ.rename r ∷ υ.rename (Ren.lift r)) :=
  Ren.WellTyped.lift (Ren.WellTyped.lift hr)

theorem DefEq.rename (heq : Γ ⊢ t ≡ t' ∶ τ) (hΔ : ⊢ Δ) (hr : Ren.WellTyped r Γ Δ)
  : (Δ ⊢ t.rename r ≡ t'.rename r ∶ τ.rename r) := match heq with
  | .var _ hlook => .var hΔ (hr hlook)
  | .u _ => .u hΔ
  | .symm h => .symm (DefEq.rename h hΔ hr)
  | .trans h₁ h₂ => .trans (DefEq.rename h₁ hΔ hr) (DefEq.rename h₂ hΔ hr)
  | .conv h hσ hτσ =>
      .conv (DefEq.rename h hΔ hr) (DefEq.rename hσ hΔ hr) (DefEq.rename hτσ hΔ hr)
  | .pi hτ hυ =>
      have hτ' := DefEq.rename hτ hΔ hr
      .pi hτ' (DefEq.rename hυ (hΔ.cons hτ'.wf_left) hr.lift)
  | .lam hσ hτeq ht =>
      have hτ' := DefEq.rename hτeq hΔ hr
      have hΔτ := hΔ.cons hτ'.wf_left
      .lam (DefEq.rename hσ hΔτ hr.lift) hτ' (DefEq.rename ht hΔτ hr.lift)
  | .app ht hm => by
      simp
      exact DefEq.app (DefEq.rename ht hΔ hr) (DefEq.rename hm hΔ hr)
  | .lamβ hτ hσ ht hm => by
      have hτ' := DefEq.rename hτ hΔ hr
      have hΔτ := hΔ.cons hτ'
      simp
      exact DefEq.lamβ hτ' (DefEq.rename hσ hΔτ hr.lift) (DefEq.rename ht hΔτ hr.lift)
        (DefEq.rename hm hΔ hr)
  | .lamη ht => by
      have h0 : Ren.lift r 0 = 0 := by simp [Ren.lift]
      simp [Tm.rename]
      rw [h0]
      exact DefEq.lamη (DefEq.rename ht hΔ hr)
  | .sigma hτ hυ =>
      have hτ' := DefEq.rename hτ hΔ hr
      .sigma hτ' (DefEq.rename hυ (hΔ.cons hτ'.wf_left) hr.lift)
  | .pair hτ hυ ha hb => by
      have hτ' := DefEq.rename hτ hΔ hr
      have hΔτ := hΔ.cons hτ'
      have hb' := DefEq.rename hb hΔ hr
      simp only [Tm.subst1_rename] at hb'
      exact DefEq.pair hτ' (DefEq.rename hυ hΔτ hr.lift) (DefEq.rename ha hΔ hr) hb'
  | .fst hp => .fst (DefEq.rename hp hΔ hr)
  | .snd hp => by
      have hp' := DefEq.rename hp hΔ hr
      simp only [Tm.subst1_rename]
      exact DefEq.snd hp'
  | .fstβ hτ hυ ha hb => by
      have hτ' := DefEq.rename hτ hΔ hr
      have hΔτ := hΔ.cons hτ'
      have hb' := DefEq.rename hb hΔ hr
      simp only [Tm.subst1_rename] at hb'
      exact DefEq.fstβ hτ' (DefEq.rename hυ hΔτ hr.lift) (DefEq.rename ha hΔ hr) hb'
  | .sndβ hτ hυ ha hb => by
      have hτ' := DefEq.rename hτ hΔ hr
      have hΔτ := hΔ.cons hτ'
      have hb' := DefEq.rename hb hΔ hr
      simp only [Tm.subst1_rename] at hb' ⊢
      exact DefEq.sndβ hτ' (DefEq.rename hυ hΔτ hr.lift) (DefEq.rename ha hΔ hr) hb'
  | .pairη hp => .pairη (DefEq.rename hp hΔ hr)
  | .bool _ => .bool hΔ
  | .true _ => .true hΔ
  | .false _ => .false hΔ
  | .boolrec hP ht hf hb => by
      have hP' := DefEq.rename hP (hΔ.cons (DefEq.bool hΔ)) hr.lift
      have ht' := DefEq.rename ht hΔ hr
      have hf' := DefEq.rename hf hΔ hr
      simp only [Tm.subst1_rename] at ht' hf' ⊢
      exact DefEq.boolrec hP' ht' hf' (DefEq.rename hb hΔ hr)
  | .boolβt hP ht hf => by
      have hP' := DefEq.rename hP (hΔ.cons (DefEq.bool hΔ)) hr.lift
      have ht' := DefEq.rename ht hΔ hr
      have hf' := DefEq.rename hf hΔ hr
      simp only [Tm.subst1_rename] at ht' hf' ⊢
      exact DefEq.boolβt hP' ht' hf'
  | .boolβf hP ht hf => by
      have hP' := DefEq.rename hP (hΔ.cons (DefEq.bool hΔ)) hr.lift
      have ht' := DefEq.rename ht hΔ hr
      have hf' := DefEq.rename hf hΔ hr
      simp only [Tm.subst1_rename] at ht' hf' ⊢
      exact DefEq.boolβf hP' ht' hf'
  | .id hτeq haeq hbeq =>
      .id (DefEq.rename hτeq hΔ hr) (DefEq.rename haeq hΔ hr) (DefEq.rename hbeq hΔ hr)
  | .refl hτeq haeq => .refl (DefEq.rename hτeq hΔ hr) (DefEq.rename haeq hΔ hr)
  | .j hτ hIdT hCeq hdeq hpeq => by
      have hτ' := DefEq.rename hτ hΔ hr
      have hIdT' := DefEq.rename hIdT (hΔ.cons hτ') hr.lift
      have hCeq' := DefEq.rename hCeq ((hΔ.cons hτ').cons hIdT'.wf_left) hr.lift2
      have hdeq' := DefEq.rename hdeq hΔ hr
      simp only [Tm.rename, Tm.subst1_rename, Tm.weaken_rename, Ren.lift, Fin.cases_zero]
        at hIdT' hCeq' hdeq' ⊢
      exact DefEq.j hτ' hIdT' hCeq' hdeq' (DefEq.rename hpeq hΔ hr)
  | .jβ hτ ha hIdT hC hd => by
      have hτ' := DefEq.rename hτ hΔ hr
      have hIdT' := DefEq.rename hIdT (hΔ.cons hτ') hr.lift
      have hC' := DefEq.rename hC ((hΔ.cons hτ').cons hIdT'.wf_left) hr.lift2
      have hd' := DefEq.rename hd hΔ hr
      simp only [Tm.rename, Tm.subst1_rename, Tm.weaken_rename, Ren.lift, Fin.cases_zero]
        at hIdT' hC' hd' ⊢
      exact DefEq.jβ hτ' (DefEq.rename ha hΔ hr) hIdT' hC' hd'

theorem Ren.succ_wellTyped (Γ : Ctx n) (σ : Tm n) :
    Ren.WellTyped Fin.succ Γ (Γ ∷ σ) :=
  fun hlook => Lookup.there hlook

theorem DefEq.weaken (heq : Γ ⊢ t₁ ≡ t₂ ∶ τ) (hΓσ : ⊢ Γ ∷ σ) :
    Γ ∷ σ ⊢ t₁.weaken ≡ t₂.weaken ∶ τ.weaken :=
  DefEq.rename heq hΓσ (Ren.succ_wellTyped Γ σ)

theorem WfTm.weaken (ht : Γ ⊢ t ∶ τ) (hΓσ : ⊢ Γ ∷ σ) : Γ ∷ σ ⊢ ↑ t ∶ ↑ τ :=
  DefEq.weaken ht hΓσ
