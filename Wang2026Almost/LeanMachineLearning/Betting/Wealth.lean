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

* the range of the bet fractions: `zero_mem_fractionRange`, `Icc_neg_one_one_subset_fractionRange`,
  `abs_le_of_mem_fractionRange`, `mem_fractionRange_of_mem_uIcc`, `interior_fractionRange`;
* `wealth_zero`, `wealth_succ`, `wealth_nonneg` (for bet fractions in `fractionRange m` and
  observations in `[0, 1]`, for every `m ∈ [0, 1]`), `measurable_wealth`.
-/

@[expose] public section

open MeasureTheory Finset

namespace Learning.Betting

variable {Ω : Type*}

/-- The range `[-1 / (1 - m), 1 / m]` of the bet fractions for which the wealth stays
nonnegative when the observations are in `[0, 1]`. -/
def fractionRange (m : ℝ) : Set ℝ := Set.Icc (-1 / (1 - m)) (1 / m)

section FractionRange

variable {m l : ℝ}

lemma isCompact_fractionRange (m : ℝ) : IsCompact (fractionRange m) := isCompact_Icc

instance (m : ℝ) : (fractionRange m).OrdConnected := Set.ordConnected_Icc

lemma interior_fractionRange (m : ℝ) :
    interior (fractionRange m) = Set.Ioo (-1 / (1 - m)) (1 / m) := interior_Icc

/-- The null bet `0` is a valid bet fraction. -/
lemma zero_mem_fractionRange (hm : m ∈ Set.Icc 0 1) : 0 ∈ fractionRange m :=
  ⟨div_nonpos_of_nonpos_of_nonneg (by norm_num) (sub_nonneg.2 hm.2), div_nonneg zero_le_one hm.1⟩

/-- For `m ∈ (0, 1)`, the range of the bet fractions has nonempty interior. -/
lemma neg_one_div_one_sub_lt_one_div (hm : m ∈ Set.Ioo 0 1) : -1 / (1 - m) < 1 / m :=
  (div_neg_of_neg_of_pos (by norm_num) (sub_pos.2 hm.2)).trans (one_div_pos.2 hm.1)

/-- The range of the bet fractions contains every fraction between `0` and a valid fraction. -/
lemma mem_fractionRange_of_mem_uIcc (hm : m ∈ Set.Icc 0 1) (hl : l ∈ fractionRange m) {l' : ℝ}
    (hl' : l' ∈ Set.uIcc 0 l) : l' ∈ fractionRange m :=
  Set.OrdConnected.uIcc_subset inferInstance (zero_mem_fractionRange hm) hl hl'

/-- For `m ∈ (0, 1)`, every fraction in `[-1, 1]` is in the interior of the range of the bet
fractions. -/
lemma Icc_neg_one_one_subset_interior_fractionRange (hm : m ∈ Set.Ioo 0 1) :
    Set.Icc (-1) 1 ⊆ interior (fractionRange m) := by
  intro x hx
  rw [interior_fractionRange]
  have h1m : 0 < 1 - m := sub_pos.2 hm.2
  constructor
  · rw [div_lt_iff₀ h1m]
    nlinarith [mul_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x + 1) h1m.le, hm.1]
  · rw [lt_div_iff₀ hm.1]
    nlinarith [mul_nonneg (by linarith [hx.2] : (0 : ℝ) ≤ 1 - x) hm.1.le, hm.2]

/-- For `m ∈ (0, 1)`, every fraction in `[-1, 1]` is a valid bet fraction. -/
lemma Icc_neg_one_one_subset_fractionRange (hm : m ∈ Set.Ioo 0 1) :
    Set.Icc (-1) 1 ⊆ fractionRange m :=
  (Icc_neg_one_one_subset_interior_fractionRange hm).trans interior_subset

/-- The valid bet fractions are bounded by `max (1 / m) (1 / (1 - m))`. -/
lemma abs_le_of_mem_fractionRange (hl : l ∈ fractionRange m) :
    |l| ≤ max (1 / m) (1 / (1 - m)) := by
  rw [abs_le]
  refine ⟨?_, hl.2.trans (le_max_left _ _)⟩
  have := hl.1
  rw [neg_le]
  calc -l ≤ 1 / (1 - m) := by rw [neg_div] at this; linarith
    _ ≤ max (1 / m) (1 / (1 - m)) := le_max_right _ _

end FractionRange

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
lemma one_add_mul_sub_nonneg {m l x : ℝ} (hm : m ∈ Set.Icc 0 1) (hl : l ∈ fractionRange m)
    (hx : x ∈ Set.Icc 0 1) : 0 ≤ 1 + l * (x - m) := by
  have h1 : l * m ≤ 1 := by
    rcases hm.1.eq_or_lt with rfl | h
    · simp
    · exact (le_div_iff₀ h).1 (by simpa using hl.2)
  have h2 : -1 ≤ l * (1 - m) := by
    rcases hm.2.eq_or_lt with rfl | h
    · simp
    · exact (div_le_iff₀ (sub_pos.2 h)).1 hl.1
  have h3 : 0 ≤ (1 - x) * (1 - l * m) := mul_nonneg (sub_nonneg.2 hx.2) (sub_nonneg.2 h1)
  have h4 : 0 ≤ x * (1 + l * (1 - m)) := mul_nonneg hx.1 (by linarith)
  nlinarith

/-- The wealth of a strategy betting fractions in `fractionRange m` on observations in `[0, 1]`
is nonnegative. -/
lemma wealth_nonneg {m : ℝ} {lam X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (hm : m ∈ Set.Icc 0 1)
    (hlam : ∀ k < n, lam k ω ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1) :
    0 ≤ wealth m lam X n ω :=
  prod_nonneg fun k hk ↦ one_add_mul_sub_nonneg hm (hlam k (mem_range.1 hk)) (hX k (mem_range.1 hk))

lemma measurable_wealth [MeasurableSpace Ω] {m : ℝ} {lam X : ℕ → Ω → ℝ}
    (hlam : ∀ k, Measurable (lam k)) (hX : ∀ k, Measurable (X k)) (n : ℕ) :
    Measurable (wealth m lam X n) :=
  Finset.measurable_prod _ fun k _ ↦ measurable_const.add ((hlam k).mul ((hX k).sub_const m))

/-- The wealth of the fixed-fraction strategy betting the fraction `l` at every round. -/
noncomputable def fixedWealth (m l : ℝ) (X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := wealth m (fun _ _ ↦ l) X

/-- The wealth of a fixed fraction in `fractionRange m` on observations in `[0, 1]` is
nonnegative. -/
lemma fixedWealth_nonneg {m l : ℝ} {X : ℕ → Ω → ℝ} {n : ℕ} {ω : Ω} (hm : m ∈ Set.Icc 0 1)
    (hl : l ∈ fractionRange m) (hX : ∀ k < n, X k ω ∈ Set.Icc 0 1) :
    0 ≤ fixedWealth m l X n ω :=
  wealth_nonneg hm (fun _ _ ↦ hl) hX

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
