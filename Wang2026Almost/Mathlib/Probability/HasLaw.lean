/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Topology.Order.Compact
public import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# Complements on laws of random variables

* `HasLaw.ae_comp`: an almost sure property of the law holds almost surely for the random
  variable;
* `HasLaw.hasSubgaussianMGF_comp`: `f ∘ X` is sub-Gaussian when `f` is sub-Gaussian under the law
  of `X`;
* `integral_mem_Icc_of_ae_mem`: the mean of a probability measure concentrated on `[a, b]` is in
  `[a, b]`;
* `integrable_of_ae_mem_of_continuous`: a continuous function is integrable for a finite measure
  concentrated on a compact set;
* `Measure.eq_dirac_of_ae_eq`: a probability measure concentrated at a point is the Dirac mass.
-/

@[expose] public section

open MeasureTheory

namespace ProbabilityTheory

variable {Ω 𝓧 : Type*} {mΩ : MeasurableSpace Ω} {m𝓧 : MeasurableSpace 𝓧} {P : Measure Ω}
  {μ : Measure 𝓧} {X : Ω → 𝓧}

/-- An almost sure property of the law of `X` holds almost surely for `X`. -/
lemma HasLaw.ae_comp (hX : HasLaw X μ P) {p : 𝓧 → Prop} (h : ∀ᵐ x ∂μ, p x) :
    ∀ᵐ ω ∂P, p (X ω) := by
  rw [← hX.map_eq] at h
  exact ae_of_ae_map hX.aemeasurable h

/-- A function `f ∘ X` of a random variable `X` with law `μ` is sub-Gaussian if `f` is
sub-Gaussian under `μ`. -/
lemma HasLaw.hasSubgaussianMGF_comp (hX : HasLaw X μ P) {f : 𝓧 → ℝ} {c : NNReal}
    (hf : HasSubgaussianMGF f c μ) : HasSubgaussianMGF (fun ω ↦ f (X ω)) c P :=
  HasSubgaussianMGF.of_map hX.aemeasurable (hX.map_eq ▸ hf)

end ProbabilityTheory

namespace MeasureTheory

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The mean of a probability measure on `ℝ` concentrated on `[a, b]` is in `[a, b]`. -/
lemma integral_mem_Icc_of_ae_mem [IsProbabilityMeasure μ] {a b : ℝ} {f : α → ℝ}
    (hf : AEMeasurable f μ) (h : ∀ᵐ x ∂μ, f x ∈ Set.Icc a b) :
    ∫ x, f x ∂μ ∈ Set.Icc a b := by
  have hint : Integrable f μ := Integrable.of_mem_Icc a b hf h
  constructor
  · calc a = ∫ _, a ∂μ := by simp
      _ ≤ ∫ x, f x ∂μ := integral_mono_ae (integrable_const _) hint (h.mono fun x hx ↦ hx.1)
  · calc ∫ x, f x ∂μ ≤ ∫ _, b ∂μ := integral_mono_ae hint (integrable_const _)
          (h.mono fun x hx ↦ hx.2)
      _ = b := by simp

/-- A continuous function is integrable for a finite measure concentrated on a compact set. -/
lemma integrable_of_ae_mem_of_continuous [TopologicalSpace α] [OpensMeasurableSpace α]
    [IsFiniteMeasure μ] {K : Set α} (hK : IsCompact K) (hμ : ∀ᵐ x ∂μ, x ∈ K) {f : α → ℝ}
    (hf : Continuous f) : Integrable f μ := by
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hf.continuousOn
  exact Integrable.of_bound hf.aestronglyMeasurable C (hμ.mono fun x hx ↦ hC x hx)

/-- A probability measure under which `x = c` almost surely is the Dirac mass at `c`. -/
lemma Measure.eq_dirac_of_ae_eq [IsProbabilityMeasure μ] {c : α} (h : ∀ᵐ x ∂μ, x = c) :
    μ = Measure.dirac c := by
  have h1 : μ.map id = μ.map (fun _ ↦ c) := Measure.map_congr h
  rwa [Measure.map_id, Measure.map_const, measure_univ, one_smul] at h1

end MeasureTheory
