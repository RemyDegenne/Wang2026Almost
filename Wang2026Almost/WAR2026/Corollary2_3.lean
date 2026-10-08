/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Wang2026Almost.WAR2026.Theorem2_2

/-!
# Corollary 2.3: divergence of `∑ S n ^ 2 / n ^ 2` for a random walk

For i.i.d. centered random variables with positive variance and partial sums `S n`,
`∑ S n ^ 2 / n ^ 2 = ∞` almost surely: by the central limit theorem `S n / n = Ω_p(n^{-1/2})`,
so `S n ^ 2 / n ^ 2 = Ω_p(n⁻¹)`, and Theorem 2.2 applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory NNReal

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']

/-- **Corollary 2.3** (Wang, Agrawal, Ramdas 2026): for i.i.d. random variables `Y n` with mean
`0` and variance `σ² > 0`, the series `∑ S n ^ 2 / n ^ 2` of the partial sums
`S n = Y 0 + … + Y (n - 1)` diverges almost surely. -/
theorem ae_not_summable_sum_sq_div_sq {Y : ℕ → Ω → ℝ} (hindep : iIndepFun Y P')
    (hident : ∀ n, IdentDistrib (Y n) (Y 0) P' P') (hL2 : MemLp (Y 0) 2 P')
    (h0 : P'[Y 0] = 0) (hvar : 0 < Var[Y 0; P']) :
    ∀ᵐ ω ∂P', ¬ Summable (fun n ↦ (∑ k ∈ Finset.range (n + 1), Y k ω) ^ 2 / (n + 1) ^ 2) := by
  set v : ℝ≥0 := Var[Y 0; P'].toNNReal with hv_def
  have hv : v ≠ 0 := by simpa [hv_def] using hvar
  -- central limit theorem: `S n / √n → N(0, v)`
  have h_clt := tendstoInDistribution_inv_sqrt_mul_sum_sub
    (HasLaw.id : HasLaw id (gaussianReal 0 v) (gaussianReal 0 v)) hL2 hindep hident
  simp only [h0, mul_zero, sub_zero] at h_clt
  -- hence `S n / n = Ω_p(n^{-1/2})`, as `N(0, v)` has no atom
  have h1 : IsBigOmegaInProb P' (fun n ω ↦ (∑ k ∈ Finset.range n, Y k ω) / n)
      (fun n ↦ (√(n : ℝ))⁻¹) := by
    refine isBigOmegaInProb_of_tendstoInDistribution (μ' := gaussianReal 0 v) (Z := id) ?_ ?_ ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have : (0 : ℝ) < n := by exact_mod_cast hn
      positivity
    · convert h_clt using 3 with n ω
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      have hsq : 0 < √(n : ℝ) := Real.sqrt_pos.2 (by positivity)
      rw [div_inv_eq_mul]
      field_simp
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
    · have := nullSingletonClass_gaussianReal (μ := 0) hv
      simp
  -- squaring and shifting the index: `S (n + 1) ^ 2 / (n + 1) ^ 2 = Ω_p(n⁻¹)`
  have h2 := (h1.sq (Eventually.of_forall fun n ↦ by positivity)).comp_tendsto
    (tendsto_add_atTop_nat 1)
  have h3 : IsBigOmegaInProb P'
      (fun n ω ↦ (∑ k ∈ Finset.range (n + 1), Y k ω) ^ 2 / (n + 1) ^ 2)
      (fun n ↦ (n : ℝ)⁻¹) := by
    refine (h2.mono two_pos ?_).congr_ae ?_
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      rw [inv_pow, Real.sq_sqrt (by positivity), Nat.cast_add_one, ← div_eq_mul_inv,
        inv_le_comm₀ (by positivity) (by positivity), inv_div, div_le_iff₀ two_pos]
      linarith
    · exact fun n ↦ Eventually.of_forall fun ω ↦ by simp [div_pow]
  -- Theorem 2.2
  have hY : ∀ k, AEMeasurable (Y k) P' := fun k ↦ (hident k).aemeasurable_fst
  exact ae_not_summable_of_isBigOmegaInProb (fun n ↦ by fun_prop)
    (fun n ↦ Eventually.of_forall fun ω ↦ by positivity) h3

end Wang2026Almost
