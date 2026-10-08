/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Divergence of `∑ 1 / (n log n)`

## Main statements

* `Real.not_summable_inv_mul_log`: `∑ 1 / (n log n) = ∞`, by Cauchy condensation.
-/

@[expose] public section

open Filter

namespace Real

/-- **`∑ 1 / (n log n)` diverges**, by Cauchy condensation: the condensed series is
`∑ 2 ^ k / (2 ^ k k log 2) = ∑ 1 / (k log 2)`. (The terms `n = 0, 1` are `0` in Lean.) -/
lemma not_summable_inv_mul_log : ¬ Summable (fun n : ℕ ↦ ((n : ℝ) * Real.log n)⁻¹) := by
  rw [← summable_condensed_iff_of_eventually_nonneg]
  · have h : (fun k : ℕ ↦ (2 : ℝ) ^ k * ((2 ^ k : ℕ) * log (2 ^ k : ℕ) : ℝ)⁻¹)
        = fun k : ℕ ↦ (log 2)⁻¹ * (k : ℝ)⁻¹ := by
      ext k
      push_cast
      rw [log_pow, mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul,
        mul_comm]
    rw [h, summable_mul_left_iff (inv_ne_zero (log_pos one_lt_two).ne')]
    exact Real.not_summable_natCast_inv
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have := log_nonneg this
    positivity
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog : 0 < log n := log_pos (by linarith)
    have hlog' : 0 < log (n + 1) := log_pos (by linarith)
    push_cast
    rw [inv_le_inv₀ (by positivity) (by positivity)]
    exact mul_le_mul (by linarith) (log_le_log (by linarith) (by linarith)) hlog.le (by linarith)

end Real
