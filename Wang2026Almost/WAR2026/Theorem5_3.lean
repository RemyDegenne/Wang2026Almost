/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Mixture
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Theorem 5.3: the no-cash criterion for sub-Gaussian mixture test processes

Under a `1`-sub-Gaussian null distribution with mean `m`, the mixture
sub-Gaussian test process with mixing distribution `π` converges almost surely to `π({m})`.

The proof does not follow the paper (law of the iterated logarithm): it splits the mixture at
`|l - m| = ε` (`Learning.Betting.ae_tendsto_integral_of_ball`). The alternatives `|l - m| ≥ ε` are
dominated by the test processes `M^{m ± ε}_n → 0`
(`Learning.Betting.ae_exists_bound_subgaussianTest_of_le_abs`), and the alternatives
`0 < |l - m| < ε` form a nonnegative supermartingale whose limit has expectation at most
`π(0 < |l - m| < ε)` (`Learning.Betting.exists_ae_tendsto_setIntegral_subgaussianTest`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

-- The statement (frozen by its comparator challenge) includes the section instance
-- `[IsProbabilityMeasure P]`, which the proof does not use: silence the linters.
set_option linter.unusedSectionVars false in
/-- **Theorem 5.3** (no-cash criterion II, Wang, Agrawal, Ramdas 2026): for i.i.d. observations
`X` of a `1`-sub-Gaussian law `P` with mean `m`, and a probability measure `π` on `ℝ`, the
mixture test process `∫ exp (∑_{k < n} ((X k - m)² - (X k - l)²) / 2) ∂π(l)` converges almost
surely to `π({m})`. The paper assumes `P` non-degenerate; the proof does not use it. -/
@[nolint unusedArguments]
theorem tendsto_subgaussianMixtureTest (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') (π : Measure ℝ) [IsProbabilityMeasure π] :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ subgaussianMixtureTest m π X n ω) atTop (𝓝 (π.real {m})) := by
  refine ae_tendsto_integral_of_ball (F := fun l n ω ↦ subgaussianTest m (fun _ _ ↦ l) X n ω)
    (c := m) (fun n ω ↦ by simp [subgaussianTest])
    (ae_of_all _ fun ω n ↦ integrable_subgaussianTest n ω) (fun ε hε ↦ ?_) fun ε hε ↦ ?_
  · filter_upwards [ae_exists_bound_subgaussianTest_of_le_abs hP hX hindep hlaw hε.1]
      with ω ⟨G, hG, hle⟩
    refine ⟨G, hG, hle.mono fun n hn ↦ ae_of_all _ fun l hεl ↦ ?_⟩
    obtain ⟨h0, h1⟩ := hn l hεl
    rwa [abs_of_nonneg h0]
  · obtain ⟨L, hLm, hL0, hLint, hL⟩ := exists_ae_tendsto_setIntegral_subgaussianTest hP hX hindep
      hlaw (π := π) (Metric.ball m ε \ {m})
    exact ⟨L, hLm.aemeasurable, hL0, hLint, hL⟩

end Wang2026Almost
