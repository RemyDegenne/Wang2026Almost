/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.KTLimit
public import Wang2026Almost.LeanMachineLearning.Betting.PlugIn
public import Wang2026Almost.LeanMachineLearning.Betting.StrategyBounds
public import Wang2026Almost.LeanMachineLearning.Betting.Strategies
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Proposition 2.5: null bankruptcy of the Krichevsky–Trofimov bettor

Under a null distribution on `[0, 1]` with mean `m` and variance `σ² > 0`, the KT bet fractions
satisfy `√n lam n → N(0, σ² / C²)` in distribution, hence `lam n = Ω_p(n^{-1/2})`, and the KT
wealth process converges to `0` almost surely.

The paper takes `C ≥ m (1 - m)`; the additional condition `C ≥ m / 2` guarantees that the first
bet `1 / (2 C)` lies in `[-1 / (1 - m), 1 / m]` (together, the two conditions guarantee that all
the KT bet fractions do, which the bankruptcy statement relies on through Corollary 2.4).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting Real
open scoped Topology ProbabilityTheory

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Proposition 2.5** (Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X` of law `P` on
`[0, 1]` with mean `m` and variance `σ² > 0`, the Krichevsky–Trofimov bet fractions with constant
`C ≥ max (m (1 - m)) (m / 2)` satisfy `√n lam n → N(0, σ² / C²)` in distribution, hence
`lam n = Ω_p(n^{-1/2})`, and the KT wealth process converges to `0` almost surely. -/
theorem kt_bankrupt (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) {C : ℝ} (hC₁ : m * (1 - m) ≤ C) (hC₂ : m / 2 ≤ C)
    {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P') :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √n * ktFraction C m X n ω) atTop (id : ℝ → ℝ)
        (fun _ ↦ P') (gaussianReal 0 (Var[id; P] / C ^ 2).toNNReal) ∧
      IsBigOmegaInProb P' (ktFraction C m X) (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ wealth m (ktFraction C m X) X n ω) atTop (𝓝 0) := by
  have hm01 := mem_Ioo_of_variance_pos hP hm hvar
  have hC : 0 < C := lt_of_lt_of_le (mul_pos hm01.1 (sub_pos.2 hm01.2)) hC₁
  have hL2 := memLp_two_id_of_mem_Icc hP
  have hΩ := isBigOmegaInProb_ktFraction hC hm hL2 hvar hindep hlaw
  refine ⟨tendstoInDistribution_sqrt_mul_ktFraction hC hm hL2 hindep hlaw, hΩ, ?_⟩
  have hX01 := ae_forall_mem_Icc_of_hasLaw hP hlaw
  refine tendsto_wealth_zero_of_isBigOmega_of_isPlugIn hP hm (ne_dirac_of_variance_pos hvar) hX
    hindep hlaw (isPlugIn_ktFraction C m X) (fun n ↦ ?_) (Or.inl hΩ)
  filter_upwards [hX01] with ω hω
  exact ktFraction_mem_fractionRange hm01 hC₁ hC₂ fun k _ ↦ hω k

end Wang2026Almost
