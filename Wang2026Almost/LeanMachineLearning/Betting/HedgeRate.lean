/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Strategies
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The rate of the predictable hedging fractions

If the variance estimates `v n` converge to `σ² > 0`, the predictable hedging fractions
`hedgeFraction C α m (v n) n = √(2 log(2/α) / (v n (n + 1) log (n + 2)))` (clipped to
`[-C/(1-m), C/m]`) are eventually unclipped and at least a constant times `(n log n)^{-1/2}`:
`(n log n)^{-1/2} = O(hedgeFraction C α m (v n) n)`.

## Main statements

* `isBigO_rpow_hedgeFraction`;
* `tendsto_hedgeFraction_zero`: the fractions tend to `0`.
-/

@[expose] public section

open Filter Real Asymptotics
open scoped Topology

namespace Learning.Betting

/-- For `n ≥ 2`, `(n + 1) log (n + 2) ≤ 4 n log n`. -/
lemma add_one_mul_log_add_two_le {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) + 1) * Real.log ((n + 2 : ℕ) : ℝ) ≤ 4 * (n * Real.log n) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : Real.log ((n + 2 : ℕ) : ℝ) ≤ 2 * Real.log n := by
    rw [← Real.log_rpow (by positivity), Real.rpow_two]
    refine Real.log_le_log (by positivity) ?_
    push_cast
    nlinarith
  have hlog0 : 0 ≤ Real.log ((n + 2 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ n)]

/-- **Rate of the predictable hedging fractions**: if `v n → σ² > 0` and `α ∈ (0, 2)` (so that
`log (2 / α) > 0`), then
`(n log n)^{-1/2} = O(hedgeFraction C α m (v n) n)`. -/
lemma isBigO_rpow_hedgeFraction {C α m σ2 : ℝ} (hC : 0 < C) (hm : m ∈ Set.Ioo 0 1)
    (hα : α ∈ Set.Ioo 0 2) (hσ : 0 < σ2) {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 σ2)) :
    (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ)) =O[atTop]
      (fun n ↦ hedgeFraction C α m (v n) n) := by
  set L := Real.log (((2 : ℕ) : ℝ) / α) with hL
  have hL0 : 0 < L := Real.log_pos (by
    rw [Nat.cast_ofNat, lt_div_iff₀ hα.1]; linarith [hα.2])
  set D : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) * Real.log ((n + 2 : ℕ) : ℝ) with hD
  have hDtop : Tendsto D atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (Real.tendsto_log_atTop.comp ?_)
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  -- the unclipped fraction tends to `0`
  set s : ℕ → ℝ := fun n ↦ √(((2 : ℕ) : ℝ) * L / (v n * D n)) with hs
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ v n * D n) atTop atTop := Tendsto.pos_mul_atTop hσ hv hDtop
    have h2 : Tendsto (fun n ↦ ((2 : ℕ) : ℝ) * L / (v n * D n)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop h1
    have h3 := (Real.continuous_sqrt.tendsto 0).comp h2
    rw [Real.sqrt_zero] at h3
    exact h3
  have hCm : 0 < C / m := div_pos hC hm.1
  have hK : 0 < L / (4 * σ2) := by positivity
  refine IsBigO.of_bound (√(L / (4 * σ2)))⁻¹ ?_
  filter_upwards [hs0.eventually (gt_mem_nhds hCm), hv.eventually (gt_mem_nhds (by linarith :
      σ2 < 2 * σ2)), hv.eventually (lt_mem_nhds (by linarith : σ2 / 2 < σ2)),
    eventually_ge_atTop 2] with n hsn hvn hvn' hn
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hv0 : 0 < v n := by linarith
  have hnlog : 0 < (n : ℝ) * Real.log n :=
    mul_pos (by linarith) (Real.log_pos (by linarith))
  have hD0 : 0 < D n := by
    simp only [hD]
    exact mul_pos (by linarith) (Real.log_pos (by norm_cast; omega))
  -- the clipping is inactive
  have hclip : hedgeFraction C α m (v n) n = s n := by
    have he : √(((2 : ℕ) : ℝ) * L / (v n * ((n : ℝ) + 1) * Real.log ((n + 2 : ℕ) : ℝ))) = s n := by
      simp only [hs, hD, mul_assoc]
    rw [hedgeFraction, ← hL, he, min_eq_left hsn.le, max_eq_right]
    exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.2 hm.2).le).trans
      (Real.sqrt_nonneg _)
  rw [hclip, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    Real.norm_of_nonneg (Real.rpow_nonneg hnlog.le _)]
  -- `(n log n)^{-1/2} = 1 / √(n log n)`
  have hrpow : ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ) = (√((n : ℝ) * Real.log n))⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hnlog.le]
    norm_num
  rw [hrpow, le_inv_mul_iff₀ (Real.sqrt_pos.2 hK), ← Real.sqrt_inv, ← Real.sqrt_mul hK.le]
  refine Real.sqrt_le_sqrt ?_
  have hDle := add_one_mul_log_add_two_le hn
  have h1 : v n * D n ≤ 2 * σ2 * (4 * (n * Real.log n)) := by
    calc v n * D n ≤ v n * (4 * (n * Real.log n)) := mul_le_mul_of_nonneg_left hDle hv0.le
      _ ≤ 2 * σ2 * (4 * (n * Real.log n)) := by
        exact mul_le_mul_of_nonneg_right hvn.le (by positivity)
  rw [← div_eq_mul_inv, div_div, Nat.cast_ofNat, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul_of_nonneg_left h1 hL0.le]

/-- If `v n → σ² > 0`, the predictable hedging fractions tend to `0`. -/
lemma tendsto_hedgeFraction_zero {C α m σ2 : ℝ} (hC : 0 < C) (hm : m ∈ Set.Ioo 0 1)
    (hσ : 0 < σ2) {v : ℕ → ℝ} (hv : Tendsto v atTop (𝓝 σ2)) :
    Tendsto (fun n ↦ hedgeFraction C α m (v n) n) atTop (𝓝 0) := by
  set D : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1) * Real.log ((n + 2 : ℕ) : ℝ) with hD
  have hDtop : Tendsto D atTop atTop := by
    refine Tendsto.atTop_mul_atTop₀ (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
      (Real.tendsto_log_atTop.comp ?_)
    exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2)
  set s : ℕ → ℝ := fun n ↦ √(((2 : ℕ) : ℝ) * Real.log (((2 : ℕ) : ℝ) / α) / (v n * D n)) with hs
  have hs0 : Tendsto s atTop (𝓝 0) := by
    have h1 : Tendsto (fun n ↦ v n * D n) atTop atTop := Tendsto.pos_mul_atTop hσ hv hDtop
    have h3 := (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_nhds.div_atTop h1 :
      Tendsto (fun n ↦ ((2 : ℕ) : ℝ) * Real.log (((2 : ℕ) : ℝ) / α) / (v n * D n)) atTop (𝓝 0))
    rw [Real.sqrt_zero] at h3
    exact h3
  refine hs0.congr' ?_
  filter_upwards [hs0.eventually (gt_mem_nhds (div_pos hC hm.1))] with n hsn
  have he : √(((2 : ℕ) : ℝ) * Real.log (((2 : ℕ) : ℝ) / α) /
      (v n * ((n : ℝ) + 1) * Real.log ((n + 2 : ℕ) : ℝ))) = s n := by
    simp only [hs, hD, mul_assoc]
  rw [hedgeFraction, he, min_eq_left hsn.le, max_eq_right]
  exact (div_nonpos_of_nonpos_of_nonneg (by linarith) (sub_pos.2 hm.2).le).trans
    (Real.sqrt_nonneg _)

end Learning.Betting
