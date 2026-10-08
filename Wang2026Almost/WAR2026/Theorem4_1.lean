/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage
public import Mathlib.Probability.Process.Adapted

/-!
# Theorem 4.1: improvability on predictably non-bankrupt paths

Every betting strategy can be improved on its `ρ`-predictably non-bankrupt event `N^ρ`: there is
another strategy whose wealth is `(W n - ρ) / (1 - ρ)` on `N^ρ`, hence which makes more money
than the original strategy when it makes money and loses more when it loses.

A betting strategy is a process `lam` *predictable* for a filtration `ℱ` to which the
observations are adapted with a lag: `lam n` (the fraction bet on `X n`) is `ℱ n`-measurable and
`X n` is `ℱ (n + 1)`-measurable. This covers the paper's predictable plug-in strategies (`ℱ` the
filtration of the past observations) and the runs of randomized LML algorithms (`ℱ` the
filtration `IsAlgEnvSeq.filtrationAction` of the run). The improved strategy is the
`ρ`-opportunistic leverage `oppLeverage m ρ lam X` of `lam` (Definition B.4), predictable for the
same filtration.
-/

@[expose] public section

open MeasureTheory Filter Learning.Betting
open scoped Topology

namespace Wang2026Almost

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- **Theorem 4.1** (improvability on predictably non-bankrupt paths, Wang, Agrawal, Ramdas
2026). Let `lam` be a betting strategy, predictable for a filtration `ℱ` to which the
observations `X` are adapted with a lag, and let `ρ ∈ (0, 1)`. There is another betting strategy
`gam`, predictable for `ℱ`, whose bet fractions are in `[-1 / (1 - m), 1 / m]` whenever those of
`lam` are, and whose wealth is `(W n - ρ) / (1 - ρ)` on the `ρ`-predictably non-bankrupt event
`N^ρ` of `lam`. Consequently, on `N^ρ`: `W' n > W n` when `W n > 1`, `W' n / W n → 1 / (1 - ρ)`
when `W n → ∞`, `W' n < W n` when `W n < 1`, and `W' n → (w - ρ) / (1 - ρ) < w` when
`W n → w < 1`. -/
theorem exists_improve {ℱ : Filtration ℕ mΩ} {m ρ : ℝ} (hm : m ∈ Set.Ioo 0 1)
    (hρ : ρ ∈ Set.Ioo 0 1) {lam X : ℕ → Ω → ℝ} (hlam : Adapted ℱ lam)
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n)) :
    ∃ gam : ℕ → Ω → ℝ, Adapted ℱ gam ∧
      (∀ n ω, lam n ω ∈ fractionRange m → gam n ω ∈ fractionRange m) ∧
      ∀ ω ∈ pnbEvent m ρ lam X,
        (∀ n, wealth m gam X n ω = (wealth m lam X n ω - ρ) / (1 - ρ)) ∧
        (∀ n, 1 < wealth m lam X n ω → wealth m lam X n ω < wealth m gam X n ω) ∧
        (Tendsto (fun n ↦ wealth m lam X n ω) atTop atTop →
          Tendsto (fun n ↦ wealth m gam X n ω / wealth m lam X n ω) atTop (𝓝 (1 / (1 - ρ)))) ∧
        (∀ n, wealth m lam X n ω < 1 → wealth m gam X n ω < wealth m lam X n ω) ∧
        ∀ w, Tendsto (fun n ↦ wealth m lam X n ω) atTop (𝓝 w) → w < 1 →
          Tendsto (fun n ↦ wealth m gam X n ω) atTop (𝓝 ((w - ρ) / (1 - ρ))) ∧
            (w - ρ) / (1 - ρ) < w := by
  sorry

end Wang2026Almost
