/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import Wang2026Almost.WAR2026.Mixtures
public import Wang2026Almost.WAR2026.MixturesProb
public import Wang2026Almost.WAR2026.Theorem3_1
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-!
# Proposition 3.2: null bankruptcy of the universal portfolio and Robbins mixtures

The two mixture strategies of Orabona and Jun (2023), the universal portfolio (a Beta mixing
distribution rescaled to `[-1, 1]`, `betaMixture`) and Robbins' iterated-logarithm mixture
(`robbinsMixture`), are atomless at `0` and hence null-bankrupt: both are probability measures
on `[-1, 1]`, a subset of the range of the bet fractions, without atom at `0`, and the no-cash
criterion (Theorem 3.1, `tendsto_mixtureWealth`) applies.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology ENNReal

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Proposition 3.2, universal portfolio** (Wang, Agrawal, Ramdas 2026): under every
non-degenerate null distribution on `[0, 1]`, the wealth of the mixture strategy with a rescaled
Beta mixing distribution converges to `0` almost surely. -/
theorem tendsto_mixtureWealth_betaMixture (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m (betaMixture a b) X n ω) atTop (𝓝 0) := by
  have := isProbabilityMeasure_betaMixture ha hb
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  refine ((tendsto_mixtureWealth hP hm hnd hX hindep hlaw (betaMixture a b) ?_).2).2
    (betaMixture_singleton_zero a b)
  filter_upwards [ae_mem_Icc_betaMixture a b] with l hl using Icc_subset_fractionRange hm01 hl

/-- **Proposition 3.2, Robbins' mixture** (Wang, Agrawal, Ramdas 2026): under every
non-degenerate null distribution on `[0, 1]`, the wealth of the mixture strategy with Robbins'
iterated-logarithm mixing distribution converges to `0` almost surely. -/
theorem tendsto_mixtureWealth_robbinsMixture (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m robbinsMixture X n ω) atTop (𝓝 0) := by
  have := isProbabilityMeasure_robbinsMixture
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  refine ((tendsto_mixtureWealth hP hm hnd hX hindep hlaw robbinsMixture ?_).2).2
    robbinsMixture_singleton_zero
  filter_upwards [ae_mem_Icc_robbinsMixture] with l hl using Icc_subset_fractionRange hm01 hl

end Wang2026Almost
