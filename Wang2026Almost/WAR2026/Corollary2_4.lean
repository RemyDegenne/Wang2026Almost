/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.SumSquares
public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Wang2026Almost.LeanMachineLearning.SequentialLearning.ConstEnvFiltration
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def

/-!
# Corollary 2.4: the `n^{-1/2}` criterion for null bankruptcy

A predictable plug-in betting strategy whose bet fractions decay no faster than `n^{-1/2}` in
probability, or than `(n log n)^{-1/2}` almost surely, goes bankrupt almost surely under every
non-degenerate null distribution.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Corollary 2.4** (`n^{-1/2}` criterion, Wang, Agrawal, Ramdas 2026). Let `P` be a
non-degenerate distribution on `[0, 1]` with mean `m`, and let `(lam, X)` be a run of a betting
strategy `alg` in the i.i.d. environment of law `P`, with bet fractions in `[-1 / (1 - m), 1 / m]`.
If `lam n = Ω_p(n^{-1/2})` or `lam n = Ω_{a.s.}((n log n)^{-1/2})`, then the wealth process
converges to `0` almost surely. -/
theorem tendsto_wealth_zero_of_isBigOmega (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) (alg : Algorithm Unit ℝ ℝ) {lam X : ℕ → Ω → ℝ}
    (h : IsAlgEnvSeq (fun _ _ ↦ ()) lam X alg (Environment.const P) P')
    (hlam : ∀ n, ∀ᵐ ω ∂P', lam n ω ∈ fractionRange m)
    (hrate : IsBigOmegaInProb P' lam (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) ∨
      IsBigOmegaAE P' lam (fun n ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ))) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0) :=
  tendsto_wealth_zero_of_isBigOmega_of_indep hP hm hnd h.measurable_feedback_filtrationAction_succ
    h.indep_feedback_filtrationAction_const h.hasLaw_feedback_const
    h.adapted_action_filtrationAction hlam hrate

end Wang2026Almost
