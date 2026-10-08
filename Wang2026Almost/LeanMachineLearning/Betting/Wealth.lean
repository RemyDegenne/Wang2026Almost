/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.SequentialLearning.ObliviousEnv
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Testing by betting: wealth processes

Sequential testing of the null hypothesis `H₀ : mean of P = m` on observations `X 0, X 1, …`
with values in `[0, 1]` by *betting*. The statistician starts with unit wealth; before the
observation `X k` is revealed, they bet the fraction `lam k` of their current wealth on it, which
multiplies their wealth by `1 + lam k * (X k - m)`. The bet fraction must lie in
`fractionRange m = [-1 / (1 - m), 1 / m]` for the wealth to stay nonnegative.

Time is `0`-indexed: after `n` rounds, the bets `lam 0, …, lam (n - 1)` have been placed on
`X 0, …, X (n - 1)`, and `lam k` is chosen from the information available before `X k`
(a *predictable* process; see `Environment.const` for the formalization of predictable strategies as
LML algorithms).

## Main definitions

* `wealth m lam X n`: the wealth `∏_{k < n} (1 + lam k (X k - m))` after `n` rounds of the
  *predictable plug-in* strategy `lam`;
* `fixedWealth m l X n`: the wealth of the fixed-fraction strategy `lam k = l`;
* `mixtureWealth m π X n = ∫ fixedWealth m l X n ∂π(l)`: the wealth of the *mixture* strategy
  with mixing distribution `π` on the bet fractions;
* `hedgedWealth m lam X n`: the wealth of the *hedged* strategy, the equal mixture of the
  strategies `lam` and `-lam`;
* `hindsightLogWealth m X n`: the best-in-hindsight log-wealth
  `max_{l ∈ fractionRange m} log (fixedWealth m l X n)` (equal to `n KL_inf(P_n, m)` for the
  empirical measure `P_n`), and `logRegret m lam X n`, the regret of the strategy `lam` against
  it;
* `subgaussianTest m lam X n`, `subgaussianMixtureTest m π X n`: the analogous plug-in and
  mixture likelihood-ratio test processes `exp (∑_{k < n} ((X k - m)² - (X k - lam k)²) / 2)` for
  the mean of `1`-sub-Gaussian observations.

Under a null distribution, all these processes are nonnegative martingales.

## Main results

* `wealth_zero`, `wealth_succ`, `wealth_nonneg` (for bet fractions in `fractionRange m` and
  observations in `[0, 1]`), `measurable_wealth`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Learning.Betting

variable {Ω : Type*}

/-- The range `[-1 / (1 - m), 1 / m]` of the bet fractions for which the wealth stays
nonnegative when the observations are in `[0, 1]`. -/
def fractionRange (m : ℝ) : Set ℝ := Set.Icc (-1 / (1 - m)) (1 / m)

/-- The wealth after `n` rounds of the predictable plug-in betting strategy `lam` on the
observations `X`, testing the null mean `m`: `∏_{k < n} (1 + lam k (X k - m))`. -/
noncomputable def wealth (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ k ∈ range n, (1 + lam k ω * (X k ω - m))

@[simp]
lemma wealth_zero (m : ℝ) (lam X : ℕ → Ω → ℝ) (ω : Ω) : wealth m lam X 0 ω = 1 := by
  simp [wealth]

lemma wealth_succ (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    wealth m lam X (n + 1) ω = wealth m lam X n ω * (1 + lam n ω * (X n ω - m)) := by
  simp [wealth, prod_range_succ]

/-- For an observation `x ∈ [0, 1]` and a bet fraction `l ∈ fractionRange m`, the wealth factor
`1 + l (x - m)` is nonnegative. -/
lemma one_add_mul_sub_nonneg {m l x : ℝ} (hm : m ∈ Set.Ioo 0 1) (hl : l ∈ fractionRange m)
    (hx : x ∈ Set.Icc 0 1) : 0 ≤ 1 + l * (x - m) := by
  have h1 : l * m ≤ 1 := (le_div_iff₀ hm.1).1 (by simpa using hl.2)
  have h2 : -1 ≤ l * (1 - m) := (div_le_iff₀ (sub_pos.2 hm.2)).1 hl.1
  have h3 : 0 ≤ (1 - x) * (1 - l * m) := mul_nonneg (sub_nonneg.2 hx.2) (sub_nonneg.2 h1)
  have h4 : 0 ≤ x * (1 + l * (1 - m)) := mul_nonneg hx.1 (by linarith)
  nlinarith

/-- The wealth of a strategy betting fractions in `fractionRange m` on observations in `[0, 1]`
is nonnegative. -/
lemma wealth_nonneg {m : ℝ} {lam X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (hm : m ∈ Set.Ioo 0 1)
    (hlam : ∀ k < n, lam k ω ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1) :
    0 ≤ wealth m lam X n ω :=
  prod_nonneg fun k hk ↦ one_add_mul_sub_nonneg hm (hlam k (mem_range.1 hk)) (hX k (mem_range.1 hk))

lemma measurable_wealth [MeasurableSpace Ω] {m : ℝ} {lam X : ℕ → Ω → ℝ}
    (hlam : ∀ k, Measurable (lam k)) (hX : ∀ k, Measurable (X k)) (n : ℕ) :
    Measurable (wealth m lam X n) :=
  Finset.measurable_prod _ fun k _ ↦ measurable_const.add ((hlam k).mul ((hX k).sub_const m))

/-- The wealth of the fixed-fraction strategy betting the fraction `l` at every round. -/
noncomputable def fixedWealth (m l : ℝ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := wealth m (fun _ _ ↦ l) X

/-- The wealth of the mixture strategy with mixing distribution `π` on the bet fractions:
`∫ fixedWealth m l X n ∂π(l)`. -/
noncomputable def mixtureWealth (m : ℝ) (π : Measure ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∫ l, fixedWealth m l X n ω ∂π

/-- The wealth of the hedged strategy based on `lam`: the equal mixture of the strategies `lam`
and `-lam`. -/
noncomputable def hedgedWealth (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  (wealth m lam X n ω + wealth m (fun k ω ↦ -lam k ω) X n ω) / ((2 : ℕ) : ℝ)

/-- The best-in-hindsight log-wealth after `n` rounds:
`log (sup_{l ∈ fractionRange m} fixedWealth m l X n)`. -/
noncomputable def hindsightLogWealth (m : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.log (⨆ l : fractionRange m, fixedWealth m (l : ℝ) X n ω)

/-- The regret of the strategy `lam` after `n` rounds: the best-in-hindsight log-wealth minus its
log-wealth. -/
noncomputable def logRegret (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  hindsightLogWealth m X n ω - Real.log (wealth m lam X n ω)

/-- The plug-in sub-Gaussian test process
`exp (∑_{k < n} ((X k - m)² - (X k - lam k)²) / 2)`: the likelihood ratio of `N(lam k, 1)`
against `N(m, 1)` on the observations. -/
noncomputable def subgaussianTest (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (∑ k ∈ range n, ((X k ω - m) ^ 2 - (X k ω - lam k ω) ^ 2) / ((2 : ℕ) : ℝ))

/-- The mixture sub-Gaussian test process with mixing distribution `π`. -/
noncomputable def subgaussianMixtureTest (m : ℝ) (π : Measure ℝ) (X : ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : ℝ :=
  ∫ l, subgaussianTest m (fun _ _ ↦ l) X n ω ∂π

end Learning.Betting
