/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Wang2026Almost.Mathlib.Probability.Distributions.ChiSquare
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-!
# Theorem 5.1: the `χ²` null limit of the best-in-hindsight log-wealth (`KL_inf`)

Under a non-degenerate null distribution on `[0, 1]`, twice the best-in-hindsight log-wealth
`L*_n = max_{l} log W_n^l = n KL_inf(P_n, m)` converges in distribution to a `χ²` distribution with
one degree of freedom. Consequently, a null-bankrupt strategy has unbounded regret
`sup_n (L*_n - log W_n) = ∞` on almost all paths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Theorem 5.1, `χ²` limit** (Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X` of a
non-degenerate law `P` on `[0, 1]` with mean `m`, twice the best-in-hindsight log-wealth
`2 L*_n = 2 max_{l ∈ [-1/(1-m), 1/m]} log W_n^l` converges in distribution to the `χ²`
distribution with one degree of freedom. -/
theorem tendstoInDistribution_hindsightLogWealth (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ 2 * hindsightLogWealth m X n ω) atTop (id : ℝ → ℝ)
      (fun _ ↦ P') (chiSquareMeasure 1) := by
  sorry

/-- **Theorem 5.1, unbounded regret** (Wang, Agrawal, Ramdas 2026): a null-bankrupt betting
strategy has unbounded regret against the best-in-hindsight wealth on almost all paths:
`sup_n (L*_n - log W_n) = ∞` (the wealth may also vanish after finitely many rounds, in which
case the regret is infinite from that round on). -/
theorem not_bddAbove_logRegret_of_tendsto_wealth_zero (hm : m ∈ Set.Ioo 0 1)
    {lam X : ℕ → Ω → ℝ} (h : ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P', (∃ n, wealth m lam X n ω = 0) ∨
      ¬ BddAbove (Set.range fun n ↦ logRegret m lam X n ω) := by
  sorry

end Wang2026Almost
