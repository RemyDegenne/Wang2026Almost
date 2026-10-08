/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

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
  sorry

end Wang2026Almost
