/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Moments.SubgaussianRate
public import Wang2026Almost.LeanMachineLearning.Betting.AGrapaLimit

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

omit [IsProbabilityMeasure μ] [IsProbabilityMeasure P] in
/-- Observations with a law on `[0, 1]` are in `[0, 1]` almost surely. -/
lemma ae_mem_Icc_of_hasLaw (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) {Y : Ω → ℝ}
    (hY : HasLaw Y P μ) : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← hY.map_eq] at hP
  exact ae_of_ae_map hY.aemeasurable hP

omit [IsProbabilityMeasure P] in
/-- Under a null distribution on `[0, 1]`, almost surely `∑_{k < n} (X k - m) = O(√n log n)`. -/
lemma ae_isBigO_sum_sub (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n) := by
  have hsub : ∀ k, HasSubgaussianMGF (fun ω ↦ X k ω - m) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro k
    have h := hasSubgaussianMGF_of_mem_Icc (hX k).aemeasurable (ae_mem_Icc_of_hasLaw hP (hlaw k))
    rwa [(hlaw k).integral_eq, hm] at h
  exact ae_isBigO_sum_range_sqrt_mul_log (Y := fun k ω ↦ X k ω - m)
    (hindep.comp (fun _ x ↦ x - m) fun _ ↦ by fun_prop) hsub

/-- Under a null distribution on `[0, 1]`, almost surely
`∑_{k < n} (X k - m)² - n σ² = O(√n log n)`. -/
lemma ae_isBigO_sum_sq_sub (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X μ) (hlaw : ∀ n, HasLaw (X n) P μ) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * Var[id; P]) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n) := by
  have hvar : Var[id; P] = ∫ x, (x - m) ^ 2 ∂P := by
    rw [variance_eq_integral aemeasurable_id]
    simp [hm]
  have hm01 : m ∈ Set.Icc (0 : ℝ) 1 := by
    rw [← hm]
    refine ⟨integral_nonneg_of_ae (hP.mono fun x hx ↦ hx.1), ?_⟩
    calc ∫ x, x ∂P ≤ ∫ _, (1 : ℝ) ∂P :=
          integral_mono_ae (integrable_of_mem_Icc_of_continuous hP continuous_id')
            (integrable_const _) (hP.mono fun x hx ↦ hx.2)
      _ = 1 := by simp
  have hsub : ∀ k, HasSubgaussianMGF (fun ω ↦ (X k ω - m) ^ 2 - Var[id; P])
      ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro k
    have hb : ∀ᵐ ω ∂μ, (X k ω - m) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
      filter_upwards [ae_mem_Icc_of_hasLaw hP (hlaw k)] with ω hω
      refine ⟨sq_nonneg _, ?_⟩
      rw [sq_le_one_iff_abs_le_one, abs_le]
      constructor <;> linarith [hω.1, hω.2, hm01.1, hm01.2]
    have h' := hasSubgaussianMGF_of_mem_Icc (((hX k).sub_const m).pow_const 2).aemeasurable hb
    have hmean : μ[fun ω ↦ (X k ω - m) ^ 2] = Var[id; P] := by
      rw [hvar, ← (hlaw k).integral_comp (f := fun x ↦ (x - m) ^ 2) (by fun_prop)]
      rfl
    rwa [hmean] at h'
  have h := ae_isBigO_sum_range_sqrt_mul_log (Y := fun k ω ↦ (X k ω - m) ^ 2 - Var[id; P])
    (hindep.comp (fun _ x ↦ (x - m) ^ 2 - Var[id; P]) fun _ ↦ by fun_prop) hsub
  filter_upwards [h] with ω hω
  refine hω.congr_left fun n ↦ ?_
  simp [sum_sub_distrib]

end Learning.Betting
