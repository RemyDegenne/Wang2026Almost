/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Moments.SubgaussianRate
public import Wang2026Almost.LeanMachineLearning.Betting.Null
public import Wang2026Almost.Mathlib.Probability.HasLaw

/-!
# Almost sure rates under a null distribution on `[0, 1]`

For i.i.d. observations with a law `P` on `[0, 1]` of mean `m` and variance `σ²`, almost surely
`S_n = ∑_{k < n} (X k - m) = O(√n log n)` and `V_n - n σ² = ∑_{k < n} ((X k - m)² - σ²) =
O(√n log n)`: both are sums of i.i.d. bounded centered variables, sub-Gaussian by Hoeffding's
lemma, to which `ae_isBigO_sum_range_sqrt_mul_log` applies. This is the event of probability one
on which the hindsight log-wealth is analysed (GRAPA Bahadur expansion, `χ²` limit of `KL_inf`).

## Main statements

* `ae_isBigO_sum_sub`: `S_n = O(√n log n)` almost surely;
* `ae_isBigO_sum_sq_sub`: `V_n - n σ² = O(√n log n)` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset Asymptotics
open scoped Topology

namespace Learning.Betting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ} {X : ℕ → Ω → ℝ}

/-- Under a null distribution on `[0, 1]`, almost surely `∑_{k < n} (X k - m) = O(√n log n)`. -/
lemma ae_isBigO_sum_sub (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n) :=
  ae_isBigO_sum_range_sqrt_mul_log (Y := fun k ω ↦ X k ω - m)
    (hindep.comp (fun _ x ↦ x - m) fun _ ↦ by fun_prop)
    fun k ↦ (hlaw k).hasSubgaussianMGF_comp (hasSubgaussianMGF_sub_of_mem_Icc hP hm)

/-- Under a null distribution on `[0, 1]`, almost surely
`∑_{k < n} (X k - m)² - n σ² = O(√n log n)`. -/
lemma ae_isBigO_sum_sq_sub (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * Var[id; P]) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n) := by
  have h := ae_isBigO_sum_range_sqrt_mul_log (Y := fun k ω ↦ (X k ω - m) ^ 2 - Var[id; P])
    (hindep.comp (fun _ x ↦ (x - m) ^ 2 - Var[id; P]) fun _ ↦ by fun_prop)
    fun k ↦ (hlaw k).hasSubgaussianMGF_comp (hasSubgaussianMGF_sq_sub_variance hP hm)
  filter_upwards [h] with ω hω
  refine hω.congr_left fun n ↦ ?_
  simp [sum_sub_distrib]

end Learning.Betting
