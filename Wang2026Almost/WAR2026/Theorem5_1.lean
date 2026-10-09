/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Wang2026Almost.LeanMachineLearning.Betting.WealthLemmas
public import Wang2026Almost.LeanMachineLearning.Betting.ChiSquareLimit
public import Wang2026Almost.LeanMachineLearning.Betting.GoodEvent
public import Wang2026Almost.LeanMachineLearning.Betting.Hindsight
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
  have hvar := variance_pos_of_ne_dirac hP hm hnd
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  -- `S_n² / V_n → χ²₁` and, almost surely, `2 L*_n - S_n² / V_n → 0`
  have h1 := tendstoInDistribution_sq_sum_sub_div hP hm hvar hX hindep hlaw
  have hX01 : ∀ᵐ ω ∂P', ∀ k, X k ω ∈ Set.Icc (0 : ℝ) 1 :=
    ae_all_iff.2 fun k ↦ (hlaw k).ae_comp hP
  have hdiff : ∀ᵐ ω ∂P', Tendsto (fun n : ℕ ↦ 2 * hindsightLogWealth m X n ω -
      (∑ k ∈ Finset.range n, (X k ω - m)) ^ 2 / ∑ k ∈ Finset.range n, (X k ω - m) ^ 2) atTop
      (𝓝 0) := by
    filter_upwards [hX01, ae_isBigO_sum_sub hP hm hindep hlaw,
      ae_isBigO_sum_sq_sub hP hm hindep hlaw] with ω hω hS hV
    exact tendsto_two_mul_hindsightLogWealth_sub hm01 hvar hω hS hV
  have hmeas : ∀ n, Measurable (fun ω ↦ 2 * hindsightLogWealth m X n ω) := fun n ↦
    (measurable_hindsightLogWealth hm01 hX n).const_mul 2
  refine tendstoInDistribution_of_tendstoInMeasure_sub _ _ h1 ?_ fun n ↦ (hmeas n).aemeasurable
  refine tendstoInMeasure_of_tendsto_ae (fun n ↦ ?_) hdiff
  refine (Measurable.aestronglyMeasurable ?_)
  exact (hmeas n).sub (((Finset.measurable_sum _ fun k _ ↦ (hX k).sub_const m).pow_const 2).div
    (Finset.measurable_sum _ fun k _ ↦ ((hX k).sub_const m).pow_const 2))

-- The statement (frozen by its comparator challenge) includes the section instance
-- `[IsProbabilityMeasure P']`, which the pathwise proof does not use: silence the linters.
set_option linter.unusedSectionVars false in
/-- **Theorem 5.1, unbounded regret** (Wang, Agrawal, Ramdas 2026): a null-bankrupt betting
strategy has unbounded regret against the best-in-hindsight wealth on almost all paths:
`sup_n (L*_n - log W_n) = ∞` (the wealth may also vanish after finitely many rounds, in which
case the regret is infinite from that round on). -/
@[nolint unusedArguments]
theorem not_bddAbove_logRegret_of_tendsto_wealth_zero (hm : m ∈ Set.Ioo 0 1)
    {lam X : ℕ → Ω → ℝ} (h : ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂P', (∃ n, wealth m lam X n ω = 0) ∨
      ¬ BddAbove (Set.range fun n ↦ logRegret m lam X n ω) := by
  filter_upwards [h] with ω hω
  exact not_bddAbove_logRegret_of_tendsto_zero (Set.Ioo_subset_Icc_self hm) hω

end Wang2026Almost
