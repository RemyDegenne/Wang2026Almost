/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Almost sure rate of sums of independent sub-Gaussian random variables

If `Y n` are independent and `c`-sub-Gaussian, then almost surely
`∑ k < n, Y k = O(√n log n)`. This follows from Hoeffding's inequality, which bounds
`P(|∑ k < n, Y k| ≥ √n log n)` by `2 n⁻²` for large `n`, and the Borel–Cantelli lemma.

## Main statements

* `ProbabilityTheory.ae_isBigO_sum_range_sqrt_mul_log`: the almost sure rate `O(√n log n)`.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics
open scoped ENNReal NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- For `n ≥ 1` with `log n ≥ 4 c`, the Hoeffding bound at level `√n log n` is at most `n⁻²`. -/
private lemma exp_neg_sqrt_mul_log_sq_le {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n)
    (hlog : 4 * c ≤ Real.log n) :
    Real.exp (-(√n * Real.log n) ^ 2 / (2 * n * c)) ≤ ((n : ℝ) ^ 2)⁻¹ := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog0 : 0 ≤ Real.log n := le_trans (by positivity) hlog
  rw [← Real.exp_log (by positivity : (0 : ℝ) < ((n : ℝ) ^ 2)⁻¹), Real.exp_le_exp, Real.log_inv,
    Real.log_pow, mul_pow, Real.sq_sqrt hn'.le]
  have h : -(n * Real.log n ^ 2) / (2 * n * c) = -(Real.log n ^ 2 / (2 * c)) := by
    field_simp
  rw [h, neg_le_neg_iff, le_div_iff₀ (by positivity)]
  push_cast
  nlinarith

/-- **Almost sure rate of sums of independent sub-Gaussian random variables.** If the `Y n` are
independent and `c`-sub-Gaussian, then almost surely `∑ k < n, Y k = O(√n log n)`. -/
lemma ae_isBigO_sum_range_sqrt_mul_log [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℝ≥0} (hindep : iIndepFun Y μ) (hY : ∀ n, HasSubgaussianMGF (Y n) c μ) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ ∑ k ∈ Finset.range n, Y k ω) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n) := by
  -- a positive sub-Gaussian constant
  set c' : ℝ≥0 := c + 1 with hc'_def
  have hc' : (0 : ℝ) < c' := by positivity
  have hY' : ∀ n, HasSubgaussianMGF (Y n) c' μ := fun n ↦
    ⟨(hY n).integrable_exp_mul, fun t ↦ ((hY n).mgf_le t).trans <| Real.exp_le_exp.2 <| by
      gcongr
      simp [hc'_def]⟩
  have hindep_neg : iIndepFun (fun n ↦ -Y n) μ :=
    hindep.comp (fun _ ↦ Neg.neg) (fun _ ↦ measurable_neg)
  set s : ℕ → Set Ω := fun n ↦ {ω | √n * Real.log n ≤ |∑ k ∈ Finset.range n, Y k ω|}
    with hs_def
  -- Hoeffding: the tail probabilities are eventually bounded by `2 n⁻²`
  have h_tail : ∀ᶠ n : ℕ in atTop, μ.real (s n) ≤ 2 * ((n : ℝ) ^ 2)⁻¹ := by
    have h_log : ∀ᶠ n : ℕ in atTop, 4 * (c' : ℝ) ≤ Real.log n :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
    filter_upwards [h_log, eventually_ge_atTop 1] with n hlog hn
    have hε : 0 ≤ √n * Real.log n := mul_nonneg (Real.sqrt_nonneg _) (le_trans (by positivity) hlog)
    have h1 := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := n) hindep
      (fun i _ ↦ hY' i) hε
    have h2 := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (n := n) hindep_neg
      (fun i _ ↦ (hY' i).neg) hε
    have hb := exp_neg_sqrt_mul_log_sq_le hc' hn hlog
    calc μ.real (s n)
        ≤ μ.real ({ω | √n * Real.log n ≤ ∑ k ∈ Finset.range n, Y k ω}
          ∪ {ω | √n * Real.log n ≤ ∑ k ∈ Finset.range n, (-Y k) ω}) := by
          refine measureReal_mono (fun ω hω ↦ ?_)
          simp only [hs_def, Set.mem_ofPred_eq, le_abs] at hω
          simp only [Set.mem_union, Set.mem_ofPred_eq, Pi.neg_apply, Finset.sum_neg_distrib]
          exact hω
      _ ≤ μ.real {ω | √n * Real.log n ≤ ∑ k ∈ Finset.range n, Y k ω}
          + μ.real {ω | √n * Real.log n ≤ ∑ k ∈ Finset.range n, (-Y k) ω} :=
          measureReal_union_le _ _
      _ ≤ 2 * ((n : ℝ) ^ 2)⁻¹ := by linarith
  have h_summable : Summable (fun n ↦ μ.real (s n)) := by
    refine Summable.of_norm_bounded_eventually
      ((Real.summable_nat_pow_inv.2 one_lt_two).mul_left 2) ?_
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [h_tail] with n hn
    rwa [Real.norm_of_nonneg measureReal_nonneg]
  have h_tsum : ∑' n, μ (s n) ≠ ∞ := by
    have h : ∀ n, μ (s n) = ENNReal.ofReal (μ.real (s n)) := fun n ↦ (ofReal_measureReal).symm
    simp_rw [h]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ ↦ measureReal_nonneg) h_summable]
    exact ENNReal.ofReal_ne_top
  filter_upwards [ae_eventually_notMem h_tsum] with ω hω
  refine IsBigO.of_bound 1 ?_
  filter_upwards [hω] with n hn
  simp only [hs_def, Set.mem_ofPred_eq, not_le] at hn
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs]
  exact hn.le.trans (le_abs_self _)

end ProbabilityTheory
