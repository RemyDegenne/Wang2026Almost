/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def

/-!
# Theorem 2.1: the sum-of-squares criterion for null bankruptcy

Under a non-degenerate null distribution `P` on `[0, 1]` with mean `m`, the wealth process of a
predictable plug-in betting strategy converges almost surely, and it converges to `0` exactly on
the paths where `∑ lam n ^ 2 = ∞` or where an all-in bet loses the whole wealth.

The strategy is a run of an LML algorithm `alg : Algorithm Unit ℝ ℝ` (actions = bet fractions)
in the
i.i.d. environment `Environment.const P`, which makes the bet fractions predictable (possibly
randomized) and the observations i.i.d. with law `P`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Theorem 2.1** (sum-of-squares criterion, Wang, Agrawal, Ramdas 2026). Let `P` be a
non-degenerate distribution on `[0, 1]` with mean `m`, and let `(lam, X)` be a run of a betting
strategy `alg` in the i.i.d. environment of law `P`, with bet fractions in
`[-1 / (1 - m), 1 / m]`. Then the wealth process converges almost surely to a random variable
`W` such that, almost surely, `W = 0` iff `∑ lam n ^ 2 = ∞` or some bet loses the whole wealth
(`lam n (X n - m) = -1`), and consequently `W > 0` iff `∑ lam n ^ 2 < ∞` and no bet loses the
whole wealth. -/
theorem sum_sq_criterion (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) (alg : Algorithm Unit ℝ ℝ) {lam X : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) lam X alg (Environment.const P) P')
    (hlam : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m) :
    ∃ W : Ω → ℝ, (∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 (W ω))) ∧
      (∀ᵐ ω ∂P', W ω = 0 ↔ ¬ Summable (fun n ↦ lam n ω ^ 2) ∨ ∃ n, lam n ω * (X n ω - m) = -1) ∧
      (∀ᵐ ω ∂P', 0 < W ω ↔ Summable (fun n ↦ lam n ω ^ 2) ∧ ∀ n, -1 < lam n ω * (X n ω - m)) := by
  sorry

end Wang2026Almost
