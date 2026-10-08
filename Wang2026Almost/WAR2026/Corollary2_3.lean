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

/-!
# Corollary 2.3: divergence of `∑ S n ^ 2 / n ^ 2` for a random walk

For i.i.d. centered random variables with positive variance and partial sums `S n`,
`∑ S n ^ 2 / n ^ 2 = ∞` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped ProbabilityTheory

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']

/-- **Corollary 2.3** (Wang, Agrawal, Ramdas 2026): for i.i.d. random variables `Y n` with mean
`0` and variance `σ² > 0`, the series `∑ S n ^ 2 / n ^ 2` of the partial sums
`S n = Y 0 + … + Y (n - 1)` diverges almost surely. -/
theorem ae_not_summable_sum_sq_div_sq {Y : ℕ → Ω → ℝ} (hindep : iIndepFun Y P')
    (hident : ∀ n, IdentDistrib (Y n) (Y 0) P' P') (hL2 : MemLp (Y 0) 2 P')
    (h0 : P'[Y 0] = 0) (hvar : 0 < Var[Y 0; P']) :
    ∀ᵐ ω ∂P', ¬ Summable (fun n ↦ (∑ k ∈ Finset.range (n + 1), Y k ω) ^ 2 / (n + 1) ^ 2) := by
  sorry

end Wang2026Almost
