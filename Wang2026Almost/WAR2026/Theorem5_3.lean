/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Theorem 5.3: the no-cash criterion for sub-Gaussian mixture test processes

Under a `1`-sub-Gaussian null distribution with mean `m`, the mixture
sub-Gaussian test process with mixing distribution `π` converges almost surely to `π({m})`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Theorem 5.3** (no-cash criterion II, Wang, Agrawal, Ramdas 2026): for i.i.d. observations
`X` of a `1`-sub-Gaussian law `P` with mean `m`, and a probability measure `π` on `ℝ`, the
mixture test process `∫ exp (∑_{k < n} ((X k - m)² - (X k - l)²) / 2) ∂π(l)` converges almost
surely to `π({m})`. The paper assumes `P` non-degenerate; the proof does not use it. -/
theorem tendsto_subgaussianMixtureTest (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') (π : Measure ℝ) [IsProbabilityMeasure π] :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ subgaussianMixtureTest m π X n ω) atTop (𝓝 (π.real {m})) := by
  sorry

end Wang2026Almost
