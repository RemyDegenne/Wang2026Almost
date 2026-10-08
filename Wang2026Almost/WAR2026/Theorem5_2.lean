/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Theorem 5.2: the sum-of-squares criterion for sub-Gaussian test processes

Under a `1`-sub-Gaussian null distribution with mean `m`, the plug-in
sub-Gaussian test process of a predictable process `lam` converges almost surely, and it
converges to `0` exactly on the paths where `∑ (lam n - m) ^ 2 = ∞`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Theorem 5.2** (sum-of-squares criterion II, Wang, Agrawal, Ramdas 2026). Let `P` be a
`1`-sub-Gaussian distribution with mean `m`, and let `(lam, X)` be a run of a
strategy `alg` (with real-valued actions) in the i.i.d. environment of law `P`. Then the plug-in
test process `M n = exp (∑_{k < n} ((X k - m)² - (X k - lam k)²) / 2)` converges almost surely
to a random variable `M` such that, almost surely, `M = 0` iff `∑ (lam n - m) ^ 2 = ∞`, and
consequently `M > 0` iff `∑ (lam n - m) ^ 2 < ∞`. The paper assumes `P` non-degenerate; the proof
does not use it. -/
theorem sum_sq_criterion_subgaussian (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    (alg : Algorithm Unit ℝ ℝ) {lam X : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) lam X alg (Environment.const P) P') :
    ∃ M : Ω → ℝ, (∀ᵐ ω ∂P', Tendsto (fun n ↦ subgaussianTest m lam X n ω) atTop (𝓝 (M ω))) ∧
      (∀ᵐ ω ∂P', M ω = 0 ↔ ¬ Summable (fun n ↦ (lam n ω - m) ^ 2)) ∧
      (∀ᵐ ω ∂P', 0 < M ω ↔ Summable (fun n ↦ (lam n ω - m) ^ 2)) := by
  sorry

end Wang2026Almost
