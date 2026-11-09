/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Quadratic bounds on `log (1 + x)`

Elementary inequalities comparing `log (1 + x)` with the polynomials `x - x ^ 2 / 2`, `x - x ^ 2`
and `x - c x ^ 2`, used to compare the log-wealth of a betting strategy with a sum of bets minus
a sum of squared bets.

## Main statements

* `Real.abs_log_one_add_sub_le`: for `|x| ≤ 1 / 2`, `|log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 |x| ^ 3`;
* `Real.sub_sq_le_log_one_add`: for `x ≥ -1 / 2`, `x - x ^ 2 ≤ log (1 + x)`, hence
  `Real.abs_log_one_add_sub_le_sq`: `|log (1 + x) - x| ≤ x ^ 2`;
* `Real.log_one_add_le_sub_mul_sq`: for `M ≥ 0` and `-1 < x ≤ M`,
  `log (1 + x) ≤ x - x ^ 2 / (2 (1 + M))`, and its exponential form
  `Real.one_add_le_exp_sub_mul_sq`.
-/

@[expose] public section

open Finset Set

namespace Real

/-- If `g` has derivative `g' y` at every point `y` between `0` and `x`, with `y * g' y ≥ 0`
(that is, `g'` has the sign of `y`), then `g 0 ≤ g x`. -/
private lemma le_of_hasDerivAt_of_mul_nonneg {g g' : ℝ → ℝ} {x : ℝ}
    (hg : ∀ y ∈ uIcc 0 x, HasDerivAt g (g' y) y) (hg' : ∀ y ∈ uIcc 0 x, 0 ≤ y * g' y) :
    g 0 ≤ g x := by
  have hcont : ContinuousOn g (uIcc 0 x) := fun y hy ↦ (hg y hy).continuousAt.continuousWithinAt
  rcases le_total 0 x with hx | hx
  · rw [uIcc_of_le hx] at hg hg' hcont
    refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := g') (convex_Icc 0 x) hcont
      (fun y hy ↦ ?_) (fun y hy ↦ ?_) (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
    · rw [interior_Icc] at hy
      exact (hg y (Ioo_subset_Icc_self hy)).hasDerivWithinAt
    · rw [interior_Icc] at hy
      exact (mul_nonneg_iff_of_pos_left hy.1).1 (hg' y (Ioo_subset_Icc_self hy))
  · rw [uIcc_of_ge hx] at hg hg' hcont
    refine antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Icc x 0) hcont
      (fun y hy ↦ ?_) (fun y hy ↦ ?_) (left_mem_Icc.2 hx) (right_mem_Icc.2 hx) hx
    · rw [interior_Icc] at hy
      exact (hg y (Ioo_subset_Icc_self hy)).hasDerivWithinAt
    · rw [interior_Icc] at hy
      have := hg' y (Ioo_subset_Icc_self hy)
      nlinarith [hy.2]

/-- The derivative of `y ↦ log (1 + y)` at `y > -1`. -/
private lemma hasDerivAt_log_one_add {y : ℝ} (hy : -1 < y) :
    HasDerivAt (fun y ↦ log (1 + y)) (1 / (1 + y)) y := by
  simpa using ((hasDerivAt_id' y).const_add 1).log (by linarith)

/-- Second-order Taylor bound for `log (1 + x)`: for `|x| ≤ 1 / 2`,
`|log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 |x| ^ 3`. -/
lemma abs_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3 := by
  have h := abs_log_sub_add_sum_range_le (x := -x) (by rw [abs_neg]; linarith) 2
  norm_num [sum_range_succ] at h
  have h1 : |x| ^ 3 / (1 - |x|) ≤ 2 * |x| ^ 3 := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [pow_nonneg (abs_nonneg x) 3]
  calc |log (1 + x) - (x - x ^ 2 / 2)| = |-x + x ^ 2 / 2 + log (1 + x)| := by ring_nf
    _ ≤ |x| ^ 3 / (1 - |x|) := h
    _ ≤ 2 * |x| ^ 3 := h1

/-- For `x ≥ -1 / 2`, `x - x ^ 2 ≤ log (1 + x)`. -/
lemma sub_sq_le_log_one_add {x : ℝ} (hx : -1 / 2 ≤ x) : x - x ^ 2 ≤ log (1 + x) := by
  have hmem : ∀ y ∈ uIcc 0 x, -1 / 2 ≤ y := fun y hy ↦ by
    rcases le_total 0 x with h | h
    · rw [uIcc_of_le h] at hy; linarith [hy.1]
    · rw [uIcc_of_ge h] at hy; linarith [hy.1]
  have key := le_of_hasDerivAt_of_mul_nonneg (x := x) (g := fun y ↦ log (1 + y) - (y - y ^ 2))
    (g' := fun y ↦ 1 / (1 + y) - (1 - 2 * y))
    (fun y hy ↦ by
      have h1 := hasDerivAt_log_one_add (y := y) (by linarith [hmem y hy])
      convert h1.sub ((hasDerivAt_id' y).sub (hasDerivAt_pow 2 y)) using 1
      push_cast
      ring)
    (fun y hy ↦ by
      have hy' := hmem y hy
      have hpos : 0 < 1 + y := by linarith
      have : y * (1 / (1 + y) - (1 - 2 * y)) = y ^ 2 * (1 + 2 * y) / (1 + y) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (mul_nonneg (sq_nonneg y) (by linarith)) hpos.le)
  simpa using key

/-- For `M ≥ 0` and `-1 < x ≤ M`, `log (1 + x) ≤ x - x ^ 2 / (2 (1 + M))`. -/
lemma log_one_add_le_sub_mul_sq {x M : ℝ} (hM : 0 ≤ M) (hx1 : -1 < x) (hxM : x ≤ M) :
    log (1 + x) ≤ x - x ^ 2 / (2 * (1 + M)) := by
  have hmem : ∀ y ∈ uIcc 0 x, -1 < y ∧ y ≤ M := fun y hy ↦ by
    rcases le_total 0 x with h | h
    · rw [uIcc_of_le h] at hy; exact ⟨by linarith [hy.1], hy.2.trans hxM⟩
    · rw [uIcc_of_ge h] at hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have key := le_of_hasDerivAt_of_mul_nonneg (x := x)
    (g := fun y ↦ y - y ^ 2 / (2 * (1 + M)) - log (1 + y))
    (g' := fun y ↦ 1 - y / (1 + M) - 1 / (1 + y))
    (fun y hy ↦ by
      have h1 := hasDerivAt_log_one_add (y := y) (hmem y hy).1
      have h2 := (hasDerivAt_id' y).sub ((hasDerivAt_pow 2 y).div_const (2 * (1 + M)))
      convert h2.sub h1 using 1
      have : 1 + M ≠ 0 := by linarith
      field_simp
      push_cast
      ring)
    (fun y hy ↦ by
      obtain ⟨hy1, hyM⟩ := hmem y hy
      have hpos : 0 < 1 + y := by linarith
      have hpos' : 0 < 1 + M := by linarith
      have : y * (1 - y / (1 + M) - 1 / (1 + y)) = y ^ 2 * (M - y) / ((1 + M) * (1 + y)) := by
        field_simp
        ring
      rw [this]
      exact div_nonneg (mul_nonneg (sq_nonneg y) (by linarith)) (mul_pos hpos' hpos).le)
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, sub_self,
    add_zero, log_one] at key
  linarith

/-- For `x ≥ -1 / 2`, `|log (1 + x) - x| ≤ x ^ 2`. -/
lemma abs_log_one_add_sub_le_sq {x : ℝ} (hx : -1 / 2 ≤ x) : |log (1 + x) - x| ≤ x ^ 2 := by
  have h1 : 0 < 1 + x := by linarith
  have h2 := sub_sq_le_log_one_add hx
  have h3 := log_le_sub_one_of_pos h1
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg x]

/-- For `M ≥ 0` and `-1 ≤ x ≤ M`, `1 + x ≤ exp (x - x ^ 2 / (2 (1 + M)))`. -/
lemma one_add_le_exp_sub_mul_sq {x M : ℝ} (hM : 0 ≤ M) (hx1 : -1 ≤ x) (hxM : x ≤ M) :
    1 + x ≤ exp (x - x ^ 2 / (2 * (1 + M))) := by
  rcases hx1.eq_or_lt with h | h
  · rw [← h]
    norm_num
    positivity
  · calc 1 + x = exp (log (1 + x)) := (exp_log (by linarith)).symm
      _ ≤ _ := exp_le_exp.2 (log_one_add_le_sub_mul_sq hM h hxM)

end Real
