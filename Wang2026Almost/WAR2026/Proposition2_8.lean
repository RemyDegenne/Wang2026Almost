/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.HedgeRate
public import Wang2026Almost.LeanMachineLearning.Betting.PlugIn
public import Wang2026Almost.LeanMachineLearning.Betting.StrategyBounds
public import Wang2026Almost.LeanMachineLearning.Betting.Strategies
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Proposition 2.8: null bankruptcy of predictable hedging

Under a null distribution on `[0, 1]` with mean `m` and variance `σ² > 0`, the bet fractions of
the predictable hedging strategy, built from any consistent plug-in variance estimate, are
`Ω_{a.s.}((n log n)^{-1/2})`, and the hedged wealth process converges to `0` almost surely.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Learning Learning.Betting Real
open scoped Topology ProbabilityTheory

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P' : Measure Ω} [IsProbabilityMeasure P']
  {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- **Proposition 2.8** (Wang, Agrawal, Ramdas 2026): for i.i.d. observations `X` of law `P` on
`[0, 1]` with mean `m` and variance `σ² > 0`, and a plug-in variance estimate `v` (a measurable
function of the past observations) which is consistent (`v n → σ²` almost surely), the bet
fractions `hedgeFraction C α m (v n) n` of the predictable hedging strategy (`C, α ∈ (0, 1)`) are
`Ω_{a.s.}((n log n)^{-1/2})`, and the hedged wealth process converges to `0` almost surely. -/
theorem hedged_bankrupt (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) {C α : ℝ} (hC : C ∈ Set.Ioo 0 1) (hα : α ∈ Set.Ioo 0 1)
    {X v : ℕ → Ω → ℝ} (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P')
    (hv : IsPlugIn X v) (hcons : ∀ᵐ ω ∂P', Tendsto (fun n ↦ v n ω) atTop (𝓝 Var[id; P])) :
    IsBigOmegaAE P' (fun n ω ↦ hedgeFraction C α m (v n ω) n)
        (fun n ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ)) ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ hedgedWealth m (fun n ω ↦ hedgeFraction C α m (v n ω) n) X n ω)
        atTop (𝓝 0) := by
  have hm01 := mem_Ioo_of_variance_pos hP hm hvar
  have hnd := ne_dirac_of_variance_pos (m := m) hvar
  set lam : ℕ → Ω → ℝ := fun n ω ↦ hedgeFraction C α m (v n ω) n with hlam
  have hrate : IsBigOmegaAE P' lam (fun n ↦ ((n : ℝ) * Real.log n) ^ (-1 / 2 : ℝ)) := by
    filter_upwards [hcons] with ω hω
    exact isBigO_rpow_hedgeFraction hC.1 hm01 hα hvar hω
  have hmeas : ∀ n, Measurable (fun x : ℝ ↦ hedgeFraction C α m x n) := fun n ↦ by
    unfold hedgeFraction
    fun_prop
  have hplug : IsPlugIn X lam := fun n ↦ by
    obtain ⟨f, hf, hvf⟩ := hv n
    exact ⟨fun x ↦ hedgeFraction C α m (f x) n, (hmeas n).comp hf, fun ω ↦ by simp [hlam, hvf ω]⟩
  have hplug' : IsPlugIn X (fun n ω ↦ -lam n ω) := fun n ↦ by
    obtain ⟨f, hf, hvf⟩ := hv n
    exact ⟨fun x ↦ -hedgeFraction C α m (f x) n, ((hmeas n).comp hf).neg,
      fun ω ↦ by simp [hlam, hvf ω]⟩
  refine ⟨hrate, ?_⟩
  have hW1 := tendsto_wealth_zero_of_isBigOmega_of_isPlugIn hP hm hnd hX hindep hlaw hplug
    (fun n ↦ ae_of_all _ fun ω ↦ hedgeFraction_mem_fractionRange hm01 ⟨hC.1.le, hC.2.le⟩ n)
    (Or.inr hrate)
  have hW2 := tendsto_wealth_zero_of_isBigOmegaAE_of_eventually_mem hP hm hnd hX hindep hlaw
    hplug' ?_ ?_
  · filter_upwards [hW1, hW2] with ω h1 h2
    have h := (h1.add h2).div_const ((2 : ℕ) : ℝ)
    rw [add_zero, zero_div] at h
    exact h
  · filter_upwards [hcons] with ω hω
    have h := (tendsto_hedgeFraction_zero (α := α) hC.1 hm01 hvar hω).neg
    rw [neg_zero] at h
    have hlo : -1 / (1 - m) < 0 := div_neg_of_neg_of_pos (by norm_num) (sub_pos.2 hm01.2)
    have hhi : 0 < 1 / m := div_pos one_pos hm01.1
    filter_upwards [h.eventually (Ioo_mem_nhds hlo hhi)] with n hn
    exact ⟨hn.1.le, hn.2.le⟩
  · filter_upwards [hrate] with ω hω
    exact hω.trans (Asymptotics.isBigO_neg_right.2 (Asymptotics.isBigO_refl _ _))

end Wang2026Almost
