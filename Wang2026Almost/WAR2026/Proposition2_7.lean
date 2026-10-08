/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Strategies
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.StrongLaw

/-!
# Proposition 2.7: null bankruptcy of the aGRAPA bettor

Under a null distribution on `[0, 1]` with mean `m` and variance `σ² > 0`, the approximate GRAPA
bet fractions satisfy `√n lam n → N(0, σ⁻²)` in distribution, hence `lam n = Ω_p(n^{-1/2})`, and
the aGRAPA wealth process converges to `0` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting Real
open scoped Topology ProbabilityTheory

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Proposition 2.7** (Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X` of law `P` on
`[0, 1]` with mean `m` and variance `σ² > 0`, the aGRAPA bet fractions with clipping constant
`C ∈ (0, 1)` satisfy `√n lam n → N(0, σ⁻²)` in distribution, hence `lam n = Ω_p(n^{-1/2})`, and
the aGRAPA wealth process converges to `0` almost surely. -/
theorem agrapa_bankrupt (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) {C : ℝ} (hC : C ∈ Set.Ioo 0 1) {X : ℕ → Ω → ℝ}
    (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * agrapaFraction C m X n ω) atTop (id : ℝ → ℝ)
        (fun _ ↦ P') (gaussianReal 0 ((Var[id; P])⁻¹).toNNReal) ∧
      IsBigOmegaInProb P' (agrapaFraction C m X) (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m (agrapaFraction C m X) X n ω) atTop (𝓝 0) := by
  sorry

end Wang2026Almost
