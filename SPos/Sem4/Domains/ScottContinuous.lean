import Mathlib.Order.ScottContinuity
import Mathlib.Order.CompletePartialOrder

structure ScottContinuousF (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  to_fun : D → E
  scott_continuous : ScottContinuous to_fun
infixr:25 "→ₛ" => ScottContinuousF

instance [Preorder D] [Preorder E] : FunLike (D →ₛ E) D E where
  coe f := f.to_fun
  coe_injective f g h := by cases f; cases g; congr

@[ext]
theorem ScottContinuousF.ext [Preorder D] [Preorder E]
    {f g : ScottContinuousF D E} (h : ∀ x, f x = g x) : f = g := by
  cases f; cases g; congr; funext; exact h _

notation "ƛₛ[" p "]" a "↦" b => ScottContinuousF.mk (fun a ↦ b) p
notation "ƛₛ" a "↦" b => ScottContinuousF.mk (fun a ↦ b) (by fun_prop)
notation "ƛₒ[" p "]" a "↦" b => OrderHom.mk (fun a ↦ b) p

@[simp]
theorem ScottContinuousF.mk_coe [Preorder D] [Preorder E]
  (f : D → E) (h : ScottContinuous f)
  : (ScottContinuousF.mk f h : D → E) = f := rfl

@[simp]
theorem ScottContinuousF.mk_lam_apply [Preorder α] [Preorder β]
  (f : α → β) (h : ScottContinuous f) (x : α)
  : (ScottContinuousF.mk f h) x = f x := rfl

instance [Preorder D] [Preorder E] : Preorder (D →ₛ E) where
  le f g := ∀ x, f x ≤ g x
  le_refl f x := le_refl (f x)
  le_trans f g h hfg hgh x := le_trans (hfg x) (hgh x)

instance [Preorder D] [PartialOrder E] : PartialOrder (D →ₛ E) where
  le_antisymm f g hfg hgf := by ext x; exact le_antisymm (hfg x) (hgf x)

instance [Preorder D] [Preorder E] [OrderBot E] : OrderBot (D →ₛ E) where
  bot      := ⟨fun _ => ⊥, ScottContinuous.const ⊥⟩
  bot_le _ := fun _ => bot_le

theorem directedOn_image_apply [Preorder D] [Preorder E] {s : Set (D →ₛ E)}
    (hs : DirectedOn (· ≤ ·) s) (x : D) :
    DirectedOn (· ≤ ·) ((fun f : D →ₛ E => f x) '' s) := by
  rintro _ ⟨f, hf, rfl⟩ _ ⟨g, hg, rfl⟩
  obtain ⟨h, hh, hfh, hgh⟩ := hs f hf g hg
  exact ⟨h x, ⟨h, hh, rfl⟩, hfh x, hgh x⟩

theorem ScottContinuous.sSup_image [Preorder D] [CompletePartialOrder E] {s : Set (D →ₛ E)}
    (hs : DirectedOn (· ≤ ·) s) :
    ScottContinuous fun x => sSup ((fun f : D →ₛ E => f x) '' s) := by
  intro d hne hd a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    refine (directedOn_image_apply hs x).sSup_le ?_
    rintro _ ⟨f, hf, rfl⟩
    exact le_trans (f.scott_continuous.monotone (ha.1 hx))
                   ((directedOn_image_apply hs a).le_sSup ⟨f, hf, rfl⟩)
  · intro u hu
    refine (directedOn_image_apply hs a).sSup_le ?_
    rintro _ ⟨f, hf, rfl⟩
    refine (f.scott_continuous hne hd ha).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_trans ((directedOn_image_apply hs x).le_sSup ⟨f, hf, rfl⟩) (hu ⟨x, hx, rfl⟩)

open Classical

noncomputable instance [Preorder D] [CompletePartialOrder E] :
    CompletePartialOrder (D →ₛ E) where
  sSup s := if h : DirectedOn (· ≤ ·) s then
      ⟨fun x => sSup ((fun f : D →ₛ E => f x) '' s), ScottContinuous.sSup_image h⟩
    else ⊥
  lubOfDirected s hs := by
    rw [dif_pos hs]
    constructor
    · intro f hf x
      exact (directedOn_image_apply hs x).le_sSup ⟨f, hf, rfl⟩
    · intro u hu x
      refine (directedOn_image_apply hs x).sSup_le ?_
      rintro _ ⟨f, hf, rfl⟩
      exact hu hf x

structure Embedding (D : Type u) (E : Type v) [Preorder D] [Preorder E] where
  inj : D →ₛ E
  ret : E →ₛ D
  ret_inj : ∀ e, ret (inj e) = e
  inj_ret : ∀ d, inj (ret d) ≤ d

@[fun_prop]
theorem ScottContinuousF.scottContinuous [Preorder α] [Preorder β]
  (f : α →ₛ β) : ScottContinuous (fun x => f x) := f.scott_continuous

@[fun_prop]
theorem ScottContinuousF.mk_apply [Preorder α] [Preorder β] [Preorder E] {g : E → α → β}
    {p : ∀ e, ScottContinuous (g e)} {x : α} (h : ScottContinuous fun e => g e x) :
    ScottContinuous fun e => (ƛₛ[p e] a ↦ g e a) x :=
  h

@[fun_prop]
theorem ScottContinuous.apply {α : ι → Type v} [∀ i, Preorder (α i)] (i : ι) :
    ScottContinuous (fun f : ∀ i, α i => f i) := by
  intro d _ _ a ha
  constructor
  · rintro _ ⟨f, hf, rfl⟩; exact ha.1 hf i
  · intro c hc
    have hub : a ≤ Function.update a i c := by
      refine ha.2 fun f hf j => ?_
      by_cases hj : j = i
      · subst hj; simpa using hc ⟨f, hf, rfl⟩
      · simpa [Function.update_of_ne hj] using ha.1 hf j
    simpa using hub i

@[fun_prop]
lemma ScottContinuous.of_apply₂ {β : α → _} {f : γ → ∀ x, β x}
  [Preorder γ] [∀ x, Preorder <| β x]
  (hf : ∀ a, ScottContinuous (f · a)) : ScottContinuous f := by
  intro d hne hd a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩ i
    exact ((hf i) hne hd ha).1 ⟨x, hx, rfl⟩
  · intro u hu i
    refine ((hf i) hne hd ha).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hu ⟨x, hx, rfl⟩ i

@[fun_prop]
theorem ScottContinuousF.apply [Preorder D] [CompletePartialOrder E] (x : D) :
    ScottContinuous (fun f : D →ₛ E => f x) := by
  intro d hne hdir a ha
  constructor
  · rintro _ ⟨f, hf, rfl⟩
    exact ha.1 hf x
  · intro u hu
    refine le_trans (ha.2 (?_ : (ƛₛ[ScottContinuous.sSup_image hdir] y ↦
      sSup ((fun f : D →ₛ E => f y) '' d)) ∈ upperBounds d) x) ?_
    · intro f hf y
      exact (directedOn_image_apply hdir y).le_sSup ⟨f, hf, rfl⟩
    · refine (directedOn_image_apply hdir x).sSup_le ?_
      rintro _ ⟨f, hf, rfl⟩
      exact hu ⟨f, hf, rfl⟩

@[fun_prop]
lemma ScottContinuousF.of_apply₂ [Preorder γ] [Preorder α] [Preorder β] {f : γ → α →ₛ β}
  (hf : ∀ a, ScottContinuous (f · a)) : ScottContinuous f := by
  intro d hne hd a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩ i
    exact ((hf i) hne hd ha).1 ⟨x, hx, rfl⟩
  · intro u hu i
    refine ((hf i) hne hd ha).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hu ⟨x, hx, rfl⟩ i

theorem ScottContinuous.comp₂ [Preorder α] [Preorder β] [Preorder γ] [Preorder E]
    {g : α → β → γ} {f₁ : E → α} {f₂ : E → β}
    (hm : ∀ {a₁ a₂ b₁ b₂}, a₁ ≤ a₂ → b₁ ≤ b₂ → g a₁ b₁ ≤ g a₂ b₂)
    (hg₁ : ∀ b, ScottContinuous (g · b)) (hg₂ : ∀ a, ScottContinuous (g a))
    (h₁ : ScottContinuous f₁) (h₂ : ScottContinuous f₂) :
    ScottContinuous fun e => g (f₁ e) (f₂ e) := by
  intro d hne hdir c hc
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact hm (h₁.monotone (hc.1 hx)) (h₂.monotone (hc.1 hx))
  · intro u hu
    refine (hg₂ (f₁ c) (hne.image f₂) (hdir.mono_comp h₂.monotone) (h₂ hne hdir hc)).2 ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine (hg₁ (f₂ x) (hne.image f₁) (hdir.mono_comp h₁.monotone) (h₁ hne hdir hc)).2 ?_
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨z, hz, hyz, hxz⟩ := hdir y hy x hx
    exact le_trans (hm (h₁.monotone hyz) (h₂.monotone hxz)) (hu ⟨z, hz, rfl⟩)

@[fun_prop]
lemma ScottContinuousF.scottContinuous_apply [Preorder α] [Preorder β] [CompletePartialOrder γ]
  {f : α → β →ₛ γ} (hf : ScottContinuous f) {g : α → β} (hg : ScottContinuous g) :
  ScottContinuous fun x => f x (g x) := by
  intro d hne hd a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    exact le_trans (hf.monotone (ha.1 hx) (g x))
                   ((f a).scott_continuous.monotone (hg.monotone (ha.1 hx)))
  · intro u hu
    refine ((f a).scott_continuous (hne.image g)
      (hd.mono_comp hg.monotone) (hg hne hd ha)).2 ?_
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ((hf.comp (ScottContinuousF.apply (g x))) hne hd ha).2 ?_
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨z, hz, hyz, hxz⟩ := hd y hy x hx
    exact le_trans (le_trans (hf.monotone hyz (g x))
      ((f z).scott_continuous.monotone (hg.monotone hxz))) (hu ⟨z, hz, rfl⟩)

theorem directedOn_range_of_monotone [Preorder β] {g : Nat → β} (h : Monotone g) :
    DirectedOn (· ≤ ·) (Set.range g) := by
  rintro _ ⟨k₁, rfl⟩ _ ⟨k₂, rfl⟩
  exact ⟨_, ⟨max k₁ k₂, rfl⟩, h (le_max_left _ _), h (le_max_right _ _)⟩

@[fun_prop]
theorem ScottContinuous.sSup_range [Preorder α] [CompletePartialOrder β]
    {g : Nat → α → β} (hg : ∀ k, ScottContinuous (g k)) (hm : ∀ x, Monotone (g · x)) :
    ScottContinuous fun x => sSup (Set.range (g · x)) := by
  intro d hne hd a ha
  constructor
  · rintro _ ⟨x, hx, rfl⟩
    refine (directedOn_range_of_monotone (hm x)).sSup_le ?_
    rintro _ ⟨k, rfl⟩
    exact le_trans ((hg k).monotone (ha.1 hx))
      ((directedOn_range_of_monotone (hm a)).le_sSup ⟨k, rfl⟩)
  · intro u hu
    refine (directedOn_range_of_monotone (hm a)).sSup_le ?_
    rintro _ ⟨k, rfl⟩
    refine ((hg k) hne hd ha).2 ?_
    rintro _ ⟨x, hx, rfl⟩
    exact le_trans ((directedOn_range_of_monotone (hm x)).le_sSup ⟨k, rfl⟩) (hu ⟨x, hx, rfl⟩)
