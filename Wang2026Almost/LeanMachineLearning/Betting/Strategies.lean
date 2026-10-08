/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth
public import LeanMachineLearning.SequentialLearning.SumRewards
public import Mathlib.Order.Filter.Extr

/-!
# Classical betting strategies

Plug-in betting strategies for testing the mean of observations in `[0, 1]`, as functions of the
past observations.

## Main definitions

* `IsPlugIn X lam`: `lam n` is a measurable function of the first `n` observations
  `X 0, …, X (n - 1)` (a *plug-in* strategy, i.e. a deterministic predictable process);
* `ktFraction C m X n`: the Krichevsky–Trofimov bet fraction
  `(1/2 + ∑_{k < n} (X k - m)) / (C (n + 1))`;
* `IsGrapa m X gr`: `gr` is a GRAPA ("growth rate adaptive to the particular alternative", or
  follow-the-leader) bet fraction process: a plug-in strategy such that `gr n` maximizes the
  hindsight wealth `l ↦ fixedWealth m l X n` over `fractionRange m`;
* `agrapaFraction C m X n`: the approximate GRAPA bet fraction, built from the empirical mean and
  variance `empMean X n`, `empVar X n` of the first `n` observations and clipped to
  `[-C / (1 - m), C / m]` (`empMean X n` is LML's empirical mean `Learning.empMean` of the
  rewards `X` of a constant action, `empMean_eq_empMean_const`);
* `hedgeFraction C α m v n`: the bet fraction `√(2 log(2/α) / (v (n + 1) log (n + 2)))` of the
  predictable hedging strategy, for a variance estimate `v`, clipped to `[-C / (1 - m), C / m]`.
-/

@[expose] public section

open Finset

namespace Learning.Betting

variable {Ω : Type*}

/-- `lam` is a *plug-in* bet fraction process for the observations `X`: each `lam n` is a
measurable function of the first `n` observations `X 0, …, X (n - 1)`. -/
def IsPlugIn (X lam : ℕ → Ω → ℝ) : Prop :=
  ∀ n, ∃ f : (Fin n → ℝ) → ℝ, Measurable f ∧ ∀ ω, lam n ω = f (fun k ↦ X k ω)

lemma isPlugIn_const (X : ℕ → Ω → ℝ) (l : ℝ) : IsPlugIn X fun _ _ ↦ l :=
  fun _ ↦ ⟨fun _ ↦ l, measurable_const, fun _ ↦ rfl⟩

/-- The Krichevsky–Trofimov bet fraction with constant `C`: after `n` observations,
`(1/2 + ∑_{k < n} (X k - m)) / (C (n + 1))`. -/
noncomputable def ktFraction (C m : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (1 / ((2 : ℕ) : ℝ) + ∑ k ∈ range n, (X k ω - m)) / (C * (n + 1))

/-- The Krichevsky–Trofimov strategy is a plug-in strategy. -/
lemma isPlugIn_ktFraction (C m : ℝ) (X : ℕ → Ω → ℝ) : IsPlugIn X (ktFraction C m X) := by
  intro n
  refine ⟨fun x ↦ (1 / ((2 : ℕ) : ℝ) + ∑ k, (x k - m)) / (C * (n + 1)), by fun_prop, fun ω ↦ ?_⟩
  simp [ktFraction, Finset.sum_range]

/-- `gr` is a GRAPA (follow-the-leader) bet fraction process for the observations `X`: a plug-in
strategy such that `gr n` is a maximizer of the hindsight wealth `l ↦ fixedWealth m l X n` over
`fractionRange m` (for `n = 0`, any value in `fractionRange m`). -/
def IsGrapa (m : ℝ) (X gr : ℕ → Ω → ℝ) : Prop :=
  IsPlugIn X gr ∧ ∀ n ω, gr n ω ∈ fractionRange m ∧
    IsMaxOn (fun l ↦ fixedWealth m l X n ω) (fractionRange m) (gr n ω)

/-- The empirical mean of the first `n` observations. -/
noncomputable def empMean (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ := (∑ k ∈ range n, X k ω) / n

/-- The empirical mean of the observations is LML's empirical mean `Learning.empMean` of the
rewards `X` of the constant action. -/
lemma empMean_eq_empMean_const (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    empMean X n ω = Learning.empMean (fun _ _ ↦ ()) X () n ω := by
  simp [empMean, Learning.empMean, Learning.sumRewards, Learning.pullCount]

/-- The empirical variance of the first `n` observations. -/
noncomputable def empVar (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (∑ k ∈ range n, (X k ω - empMean X n ω) ^ 2) / n

/-- The approximate GRAPA (aGRAPA) bet fraction with clipping constant `C`: after `n`
observations, `(μ̂ - m) / (σ̂² + (μ̂ - m)²)` for the empirical mean `μ̂` and variance `σ̂²`,
clipped to `[-C / (1 - m), C / m]`. -/
noncomputable def agrapaFraction (C m : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  max (-C / (1 - m))
    (min ((empMean X n ω - m) / (empVar X n ω + (empMean X n ω - m) ^ 2)) (C / m))

/-- The bet fraction of the predictable hedging strategy at round `n` (after `n` observations),
for the variance estimate `v` and the confidence parameter `α`:
`√(2 log(2/α) / (v (n + 1) log (n + 2)))`, clipped to `[-C / (1 - m), C / m]`. -/
noncomputable def hedgeFraction (C α m v : ℝ) (n : ℕ) : ℝ :=
  max (-C / (1 - m))
    (min (√(((2 : ℕ) : ℝ) * Real.log (((2 : ℕ) : ℝ) / α) /
      (v * ((n : ℝ) + 1) * Real.log ((n + 2 : ℕ) : ℝ)))) (C / m))

end Learning.Betting
