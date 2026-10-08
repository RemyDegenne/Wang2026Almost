/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Wealth

/-!
# Predictably non-bankrupt paths, leverage and portfolios of betting strategies

Definitions of Wang, Agrawal, Ramdas, "Almost sure null bankruptcy of testing-by-betting
strategies" (COLT 2026) for a betting strategy `lam` on observations `X` testing the mean `m`:

* `nextWealthMin m lam X n`: the minimum possible wealth after round `n` given the information
  available before `X n` is revealed, `min_{x ∈ {0, 1}} wealth n * (1 + lam n (x - m))`;
* `pnbEvent m ρ lam X`: the *`ρ`-predictably non-bankrupt* event `⋂ n {nextWealthMin n > ρ}`;
* `leverageFraction m ρ lam X n`: the bet fraction `wealth n * lam n / (wealth n - ρ)`, which
  amounts to borrowing `ρ / (1 - ρ)` units of cash and leveraging the strategy `lam`;
* `oppLeverage m ρ lam X`: the *`ρ`-opportunistic leverage* of `lam`, which bets
  `leverageFraction` when the next wealth is guaranteed to stay above `ρ` and `lam` otherwise;
* `portfolioFraction m κ lam nu X`: the bet fraction of the portfolio `(1 - κ) W^lam + κ W^nu`
  of two strategies.
-/

@[expose] public section

open Learning.Betting

namespace Wang2026Almost

variable {Ω : Type*}

/-- The minimum possible wealth after round `n`, given the information available before `X n`
is revealed: `min_{x ∈ {0, 1}} wealth m lam X n * (1 + lam n (x - m))`. -/
noncomputable def nextWealthMin (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  min (wealth m lam X n ω * (1 + lam n ω * (0 - m))) (wealth m lam X n ω * (1 + lam n ω * (1 - m)))

/-- The `ρ`-predictably non-bankrupt event of the strategy `lam`: at every round, the next
wealth is guaranteed to stay above `ρ`. -/
def pnbEvent (m ρ : ℝ) (lam X : ℕ → Ω → ℝ) : Set Ω := {ω | ∀ n, ρ < nextWealthMin m lam X n ω}

/-- The bet fraction `wealth n * lam n / (wealth n - ρ)`, equivalent to borrowing `ρ / (1 - ρ)`
units of cash and betting `lam` with the leveraged wealth. -/
noncomputable def leverageFraction (m ρ : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  wealth m lam X n ω * lam n ω / (wealth m lam X n ω - ρ)

/-- The `ρ`-opportunistic leverage of the strategy `lam`: bet `leverageFraction m ρ lam X n` when
the next wealth is guaranteed to stay above `ρ`, and `lam n` otherwise. -/
noncomputable def oppLeverage (m ρ : ℝ) (lam X : ℕ → Ω → ℝ) : ℕ → Ω → ℝ := fun n ω ↦
  if ρ < nextWealthMin m lam X n ω then leverageFraction m ρ lam X n ω else lam n ω

/-- The bet fraction of the portfolio `(1 - κ) W^lam + κ W^nu` of the two strategies `lam` and
`nu`:
`((1 - κ) W^lam_n lam_n + κ W^nu_n nu_n) / ((1 - κ) W^lam_n + κ W^nu_n)`. -/
noncomputable def portfolioFraction (m κ : ℝ) (lam nu X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ((1 - κ) * wealth m lam X n ω * lam n ω + κ * wealth m nu X n ω * nu n ω) /
    ((1 - κ) * wealth m lam X n ω + κ * wealth m nu X n ω)

end Wang2026Almost
