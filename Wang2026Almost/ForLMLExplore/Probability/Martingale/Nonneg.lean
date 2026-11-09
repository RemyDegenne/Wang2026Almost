/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Martingale.Convergence

/-!
# Convergence of nonnegative supermartingales

An almost surely nonnegative supermartingale indexed by `ℕ` is bounded in `L¹`, hence converges
almost surely (martingale convergence theorem) to a finite limit, whose expectation is at most the
expectation of the initial value (Fatou's lemma).

## Main statements

* `MeasureTheory.Supermartingale.exists_ae_tendsto_of_nonneg`: an a.s. nonnegative
  supermartingale `V` converges a.s. to a measurable, a.s. nonnegative limit `L` with
  `∫⁻ ofReal L ≤ ofReal (∫ V 0)`.
-/

@[expose] public section

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Convergence of nonnegative supermartingales.** A supermartingale `V` with `V n ≥ 0` a.s.
converges almost surely to a measurable, a.s. nonnegative limit `L`, and
`∫⁻ ω, ENNReal.ofReal (L ω) ∂μ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ)`. -/
lemma Supermartingale.exists_ae_tendsto_of_nonneg [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {V : ℕ → Ω → ℝ} (hV : Supermartingale V ℱ μ)
    (hV_nonneg : ∀ n, 0 ≤ᵐ[μ] V n) :
    ∃ L : Ω → ℝ, Measurable L ∧ (∀ᵐ ω ∂μ, Tendsto (fun n ↦ V n ω) atTop (𝓝 (L ω))) ∧
      0 ≤ᵐ[μ] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
  have hVm : ∀ n, Measurable (V n) := fun n ↦ (hV.stronglyMeasurable n).measurable.mono
    (ℱ.le n) le_rfl
  have hlint : ∀ n, ∫⁻ ω, ENNReal.ofReal (V n ω) ∂μ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) := by
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hV.integrable n) (hV_nonneg n)]
    exact ENNReal.ofReal_le_ofReal <| by
      simpa using hV.setIntegral_le (Nat.zero_le n) MeasurableSet.univ
  have hbdd : ∀ n, eLpNorm ((-V) n) 1 μ ≤ (∫ ω, V 0 ω ∂μ).toNNReal := by
    intro n
    rw [Pi.neg_apply, eLpNorm_one_eq_lintegral_enorm (hVm n).neg.aestronglyMeasurable]
    simp only [Pi.neg_apply, enorm_neg]
    rw [lintegral_enorm_of_ae_nonneg (hV_nonneg n)]
    exact hlint n
  have hconv := hV.neg.ae_tendsto_limitProcess hbdd
  set L : Ω → ℝ := fun ω ↦ -ℱ.limitProcess (-V) μ ω with hL_def
  have hL : ∀ᵐ ω ∂μ, Tendsto (fun n ↦ V n ω) atTop (𝓝 (L ω)) := by
    filter_upwards [hconv] with ω hω
    simpa [hL_def] using hω.neg
  have hL_nonneg : 0 ≤ᵐ[μ] L := by
    filter_upwards [hL, ae_all_iff.2 hV_nonneg] with ω hω h0
    exact ge_of_tendsto' hω fun n ↦ h0 n
  refine ⟨L, Filtration.stronglyMeasurable_limit_process'.measurable.neg, hL, hL_nonneg, ?_⟩
  calc ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ
      = ∫⁻ ω, liminf (fun n ↦ ENNReal.ofReal (V n ω)) atTop ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hL] with ω hω
        exact ((ENNReal.continuous_ofReal.tendsto _).comp hω).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ ω, ENNReal.ofReal (V n ω) ∂μ) atTop :=
        lintegral_liminf_le fun n ↦ (hVm n).ennreal_ofReal
    _ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ) :=
        liminf_le_of_frequently_le' (Frequently.of_forall hlint)

end MeasureTheory
