import Mathlib.Order.OmegaCompletePartialOrder

import SPos.Syntax.Syntax

open OmegaCompletePartialOrder

def ωScottContinuous.mk_lam [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E]
  (f : D → E) (h : ωScottContinuous f) : D →𝒄 E :=
  ⟨⟨f, h.monotone⟩, h.map_ωSup⟩

notation "ƛ[" p "]" a "↦" b => ωScottContinuous.mk_lam (fun a ↦ b) p

@[simp]
theorem ωScottContinuous.mk_lam_apply [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E]
    {f : D → E} (h : ωScottContinuous f) (d : D) :
    ωScottContinuous.mk_lam f h d = f d := rfl

@[fun_prop]
lemma ωScottContinuous.of_apply₃
    [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] [OmegaCompletePartialOrder G]
    {f : D → E →𝒄 G} (hf : ∀ e, ωScottContinuous (f · e)) : ωScottContinuous f :=
  ωScottContinuous.of_monotone_map_ωSup
    ⟨fun _ _ h e ↦ (hf e).monotone h, fun c ↦ by ext e; apply (hf e).map_ωSup c⟩

@[fun_prop]
lemma ωScottContinuous.mk_lam_cont
    [OmegaCompletePartialOrder D] [OmegaCompletePartialOrder E] [OmegaCompletePartialOrder G]
    {g : D → E → G} {hg : ∀ d, ωScottContinuous (g d)}
    (hg' : ∀ e, ωScottContinuous (g · e)) :
    ωScottContinuous fun d => ωScottContinuous.mk_lam (g d) (hg d) :=
  ωScottContinuous.of_apply₃ hg'

@[fun_prop]
lemma Env.cons_cont [OmegaCompletePartialOrder E] [OmegaCompletePartialOrder D]
    {g : E → Env (fun _ => D) n}
    (hg : ωScottContinuous g) (hv : ωScottContinuous v) (i : Fin (n + 1)) :
    ωScottContinuous fun e => (g e ∷ v e) i := by
  induction i using Fin.lastCases with
  | last   => simpa [Env.cons] using hv
  | cast j => simpa [Env.cons] using hg.apply₂ j
