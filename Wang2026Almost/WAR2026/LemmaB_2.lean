/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lemma B.2: the limit of `∫ exp (-x A n) dγ(x)`

For a finite measure `γ` on `[0, ∞)` and a sequence `A n` tending to `∞`,
`∫ exp (-x A n) dγ(x) → γ({0})`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace Wang2026Almost

/-- **Lemma B.2** (Wang, Agrawal, Ramdas 2026): for a finite measure `γ` on `[0, ∞)` and a
sequence `A n` tending to `∞`, `∫ exp (-x A n) dγ(x) → γ({0})`. The paper assumes `A` positive and
increasing; the proof (dominated convergence) does not use it. -/
lemma tendsto_integral_exp_neg_mul (γ : Measure ℝ) [IsFiniteMeasure γ] (hγ : γ (Set.Iio 0) = 0)
    {A : ℕ → ℝ} (hA : Tendsto A atTop atTop) :
    Tendsto (fun n ↦ ∫ x, Real.exp (-x * A n) ∂γ) atTop (𝓝 (γ.real {0})) := by
  have h_nonneg : ∀ᵐ x ∂γ, 0 ≤ x := by
    rw [ae_iff]
    simpa [not_le, Set.Iio] using hγ
  have h_lim : ∀ᵐ x ∂γ, Tendsto (fun n ↦ Real.exp (-x * A n)) atTop
      (𝓝 (Set.indicator {0} 1 x)) := by
    filter_upwards [h_nonneg] with x hx
    rcases hx.eq_or_lt with rfl | hx
    · simp
    · rw [Set.indicator_of_notMem (by simpa using hx.ne')]
      exact Real.tendsto_exp_atBot.comp (hA.const_mul_atTop_of_neg (neg_lt_zero.2 hx))
  have h_bound : ∀ᶠ n in atTop, ∀ᵐ x ∂γ, ‖Real.exp (-x * A n)‖ ≤ 1 := by
    filter_upwards [hA.eventually_ge_atTop 0] with n hn
    filter_upwards [h_nonneg] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_le_one_iff]
    nlinarith
  have h := tendsto_integral_filter_of_dominated_convergence (fun _ ↦ (1 : ℝ))
    (Eventually.of_forall fun n ↦ by fun_prop) h_bound (integrable_const 1) h_lim
  rwa [integral_indicator_one (measurableSet_singleton 0)] at h

end Wang2026Almost
