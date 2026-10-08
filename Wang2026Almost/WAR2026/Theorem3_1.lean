/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Mixture
public import Wang2026Almost.WAR2026.MixturesProb
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Dirac.Def
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic

/-!
# Theorem 3.1: the no-cash criterion for null bankruptcy of mixture strategies

Under a non-degenerate null distribution, the wealth of the mixture strategy with mixing
distribution `π` converges almost surely to `π({0})`, the fraction of the wealth kept as cash:
the mixture strategy goes bankrupt iff `π` has no atom at `0`.

The proof does not follow the paper (law of the iterated logarithm): it splits the mixture at
`|l| = ε` (`Learning.Betting.ae_tendsto_integral_of_ball`). The bets `|l| ≥ ε` are dominated by the
fixed-fraction wealths `W^{±ε}_n → 0` (`Learning.Betting.ae_exists_bound_fixedWealth_of_le_abs`),
and the bets `0 < |l| < ε` form a nonnegative supermartingale whose limit has expectation at most
`π(0 < |l| < ε)` (`Learning.Betting.exists_ae_tendsto_setIntegral_fixedWealth`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Theorem 3.1** (no-cash criterion, Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X`
of a non-degenerate law `P` on `[0, 1]` with mean `m`, and a probability measure `π` on
`[-1 / (1 - m), 1 / m]`, the mixture wealth process converges almost surely to `π({0})`. In
particular it converges to `0` almost surely iff `π` has no atom at `0`. -/
theorem tendsto_mixtureWealth (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) {X : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P')
    (hlaw : ∀ n, HasLaw (X n) P P') (π : Measure ℝ) [IsProbabilityMeasure π]
    (hπ : ∀ᵐ l ∂π, l ∈ fractionRange m) :
    (∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m π X n ω) atTop (𝓝 (π.real {0}))) ∧
      ((∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m π X n ω) atTop (𝓝 0)) ↔ π {0} = 0) := by
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  have hlim : ∀ᵐ ω ∂P', Tendsto (fun n ↦ mixtureWealth m π X n ω) atTop (𝓝 (π.real {0})) := by
    refine ae_tendsto_integral_of_ball (F := fun l n ω ↦ fixedWealth m l X n ω) (c := 0)
      (fun n ω ↦ fixedWealth_zero_fraction m X n ω)
      (ae_of_all _ fun ω n ↦ integrable_fixedWealth hπ n ω) (fun ε hε ↦ ?_) fun ε hε ↦ ?_
    · have h1 : ε ∈ fractionRange m :=
        Icc_subset_fractionRange hm01 ⟨by linarith [hε.1], hε.2⟩
      have h2 : -ε ∈ fractionRange m :=
        Icc_subset_fractionRange hm01 ⟨by linarith [hε.2], by linarith [hε.1]⟩
      filter_upwards [ae_exists_bound_fixedWealth_of_le_abs hP hm hnd hX hindep hlaw hε.1 h1 h2]
        with ω ⟨G, hG, hle⟩
      refine ⟨G, hG, hle.mono fun n hn ↦ ?_⟩
      filter_upwards [hπ] with l hl hεl
      rw [sub_zero] at hεl
      obtain ⟨h0, h1⟩ := hn l hl hεl
      rwa [abs_of_nonneg h0]
    · obtain ⟨L, hLm, hL0, hLint, hL⟩ := exists_ae_tendsto_setIntegral_fixedWealth hP hm hm01 hX
        hindep hlaw hπ (Metric.ball 0 ε \ {0})
      exact ⟨L, hLm.aemeasurable, hL0, hLint, hL⟩
  refine ⟨hlim, fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨ω, h1, h2⟩ := (hlim.and h).exists
    rw [← measureReal_eq_zero_iff]
    exact tendsto_nhds_unique h1 h2
  · have h0 : π.real {0} = 0 := by simp [measureReal_def, h]
    simpa [h0] using hlim

end Wang2026Almost
