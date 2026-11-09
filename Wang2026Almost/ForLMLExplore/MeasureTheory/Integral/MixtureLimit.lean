/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Limits of mixtures concentrating at a point

* `ae_tendsto_of_forall_exists_lintegral_le`: if, for every `j`, random variables `V n` converge
  almost surely to `a + L_j` with `L_j ≥ 0` and `E[L_j] ≤ δ j → 0`, then `V n → a` almost surely;
* `tendsto_integral_of_tendsto_setIntegral_ball`: the mixture `∫ F l n ∂π(l)` of functions with
  `F c n = 1` decomposes as `π({c})`, plus the mixture over a punctured ball around `c`, plus a
  part which tends to `0` when `F l n` is uniformly small away from `c`;
* `ae_tendsto_integral_of_ball`: the random version: if, for every small `ε`, the processes are
  uniformly small away from the ball of radius `ε` and the mixture over the punctured ball has an
  almost sure limit of expectation at most `π(B(c, ε) \ {c})`, then the mixture converges almost
  surely to `π({c})`. This is the abstract form of the no-cash criteria of testing by betting.
-/

@[expose] public section

open Filter
open scoped Topology ENNReal

namespace MeasureTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- If, for every `j`, a sequence of random variables converges almost surely to `a + L_j` with
`L_j ≥ 0` and `∫⁻ L_j ≤ δ j`, where `δ j → 0`, then it converges almost surely to `a`. -/
lemma ae_tendsto_of_forall_exists_lintegral_le {μ : Measure Ω} {V : ℕ → Ω → ℝ} {a : ℝ}
    {δ : ℕ → ℝ≥0∞} (hδ : Tendsto δ atTop (𝓝 0))
    (h : ∀ j, ∃ L : Ω → ℝ, AEMeasurable L μ ∧ 0 ≤ᵐ[μ] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ ≤ δ j ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ V n ω) atTop (𝓝 (a + L ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ V n ω) atTop (𝓝 a) := by
  choose L hLm hL0 hLint hLlim using h
  have hall : ∀ᵐ ω ∂μ, ∀ j, Tendsto (fun n ↦ V n ω) atTop (𝓝 (a + L j ω)) := ae_all_iff.2 hLlim
  have heq : ∀ j, L j =ᵐ[μ] L 0 := fun j ↦ by
    filter_upwards [hall] with ω hω
    have := tendsto_nhds_unique (hω j) (hω 0)
    linarith
  have hint0 : ∫⁻ ω, ENNReal.ofReal (L 0 ω) ∂μ = 0 := by
    refine le_antisymm (ge_of_tendsto' hδ fun j ↦ ?_) bot_le
    calc ∫⁻ ω, ENNReal.ofReal (L 0 ω) ∂μ = ∫⁻ ω, ENNReal.ofReal (L j ω) ∂μ :=
          lintegral_congr_ae (by filter_upwards [heq j] with ω hω; rw [hω])
      _ ≤ δ j := hLint j
  have hzero : ∀ᵐ ω ∂μ, ENNReal.ofReal (L 0 ω) = 0 :=
    (lintegral_eq_zero_iff' (hLm 0).ennreal_ofReal).1 hint0
  filter_upwards [hall, hzero, hL0 0] with ω hω h1 h2
  have : L 0 ω = 0 := le_antisymm (ENNReal.ofReal_eq_zero.1 h1) h2
  simpa [this] using hω 0

/-- **Decomposition of a mixture at distance `ε` of a point `c`**, pathwise. Let `F l n` be
integrable in `l` with `F c n = 1`, dominated on `|l - c| ≥ ε` by `G n → 0` for large `n`, and
such that the mixture over `0 < |l - c| < ε` converges to `L`. Then the mixture converges to
`π({c}) + L`. -/
lemma tendsto_integral_of_tendsto_setIntegral_ball {π : Measure ℝ} [IsFiniteMeasure π]
    {c ε : ℝ} (hε : 0 < ε) {F : ℝ → ℕ → ℝ} (hFc : ∀ n, F c n = 1)
    (hint : ∀ n, Integrable (fun l ↦ F l n) π) {G : ℕ → ℝ} (hG : Tendsto G atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, ∀ᵐ l ∂π, ε ≤ |l - c| → |F l n| ≤ G n) {L : ℝ}
    (hsmall : Tendsto (fun n ↦ ∫ l in Metric.ball c ε \ {c}, F l n ∂π) atTop (𝓝 L)) :
    Tendsto (fun n ↦ ∫ l, F l n ∂π) atTop (𝓝 (π.real {c} + L)) := by
  have hcB : {c} ⊆ Metric.ball c ε := Set.singleton_subset_iff.2 (Metric.mem_ball_self hε)
  have hdecomp : ∀ n, ∫ l, F l n ∂π = π.real {c} + ∫ l in Metric.ball c ε \ {c}, F l n ∂π
      + ∫ l in (Metric.ball c ε)ᶜ, F l n ∂π := by
    intro n
    rw [← integral_add_compl Metric.isOpen_ball.measurableSet (hint n)]
    congr 1
    conv_lhs => rw [← Set.union_sdiff_cancel hcB]
    rw [setIntegral_union Set.disjoint_sdiff_right
      (Metric.isOpen_ball.measurableSet.diff (measurableSet_singleton c)) (hint n).integrableOn
      (hint n).integrableOn, integral_singleton, hFc, smul_eq_mul, mul_one]
  have hlarge : Tendsto (fun n ↦ ∫ l in (Metric.ball c ε)ᶜ, F l n ∂π) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ (by simpa using hG.mul_const (π.real (Metric.ball c ε)ᶜ))
    filter_upwards [hle] with n hn
    refine norm_setIntegral_le_of_norm_le_const_ae' (measure_lt_top _ _) ?_
    filter_upwards [hn] with l hl hlB
    rw [Real.norm_eq_abs]
    refine hl ?_
    simpa [Real.dist_eq] using hlB
  simp_rw [hdecomp]
  simpa using (tendsto_const_nhds.add hsmall).add hlarge

/-- **No-cash criterion, abstract form.** Let `F l` be a family of processes indexed by
`l ∈ ℝ`, with `F c = 1`, integrable in `l` for a finite measure `π`. Assume that for every
`ε ∈ (0, 1]`,
* almost surely, `|F l n|` is bounded for `|l - c| ≥ ε` and `n` large by a sequence tending to
  `0` (large bets);
* the mixture over `0 < |l - c| < ε` converges almost surely to a nonnegative limit with
  expectation at most `π(0 < |l - c| < ε)` (small bets).

Then the mixture `∫ F l n ∂π(l)` converges almost surely to `π({c})`. -/
lemma ae_tendsto_integral_of_ball {μ : Measure Ω} {π : Measure ℝ} [IsFiniteMeasure π] {c : ℝ}
    {F : ℝ → ℕ → Ω → ℝ} (hFc : ∀ n ω, F c n ω = 1)
    (hint : ∀ᵐ ω ∂μ, ∀ n, Integrable (fun l ↦ F l n ω) π)
    (hlarge : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ᵐ ω ∂μ, ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧
      ∀ᶠ n in atTop, ∀ᵐ l ∂π, ε ≤ |l - c| → |F l n ω| ≤ G n)
    (hsmall : ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∃ L : Ω → ℝ, AEMeasurable L μ ∧ 0 ≤ᵐ[μ] L ∧
      ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ ≤ π (Metric.ball c ε \ {c}) ∧
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ l in Metric.ball c ε \ {c}, F l n ω ∂π) atTop (𝓝 (L ω))) :
    ∀ᵐ ω ∂μ, Tendsto (fun n ↦ ∫ l, F l n ω ∂π) atTop (𝓝 (π.real {c})) := by
  set s : ℕ → Set ℝ := fun j ↦ Metric.ball c (1 / (j + 1)) \ {c} with hs
  have hεj : ∀ j : ℕ, (1 / (j + 1) : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := fun j ↦
    ⟨by positivity, (div_le_one (by positivity)).2 (by linarith [(j.cast_nonneg : (0 : ℝ) ≤ j)])⟩
  refine ae_tendsto_of_forall_exists_lintegral_le (δ := fun j ↦ π (s j)) ?_ fun j ↦ ?_
  · have hanti : Antitone s := fun i j hij ↦ Set.sdiff_subset_sdiff_left
      (Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) (by gcongr)))
    have hinter : ⋂ j, s j = ∅ := by
      refine Set.eq_empty_of_forall_notMem fun x hx ↦ ?_
      rw [Set.mem_iInter] at hx
      have hxc : x ≠ c := (hx 0).2
      obtain ⟨j, hj⟩ := exists_nat_one_div_lt (dist_pos.2 hxc)
      exact (lt_asymm hj ((hx j).1 : dist x c < 1 / (j + 1)))
    have h := tendsto_measure_iInter_atTop (μ := π) (fun j ↦ (Metric.isOpen_ball.measurableSet.diff
      (measurableSet_singleton c)).nullMeasurableSet) hanti ⟨0, measure_ne_top π _⟩
    rwa [hinter, measure_empty] at h
  · obtain ⟨L, hLm, hL0, hLint, hL⟩ := hsmall _ (hεj j)
    refine ⟨L, hLm, hL0, hLint, ?_⟩
    filter_upwards [hint, hlarge _ (hεj j), hL] with ω hint hlarge hL
    obtain ⟨G, hG, hle⟩ := hlarge
    exact tendsto_integral_of_tendsto_setIntegral_ball (hεj j).1 (fun n ↦ hFc n ω) hint hG hle hL

end MeasureTheory
