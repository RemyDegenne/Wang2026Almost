/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.WAR2026.Leverage
public import Wang2026Almost.WAR2026.DefinitionB_4
public import Wang2026Almost.WAR2026.LeverageMeasurable
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
  refine ⟨oppLeverage m ρ lam X, adapted_oppLeverage hlam hX,
    fun n ω h ↦ oppLeverage_mem_fractionRange hm h, fun ω hω ↦ ?_⟩
  have hρ1 : 0 < 1 - ρ := sub_pos.2 hρ.2
  have hW : ∀ n, wealth m (oppLeverage m ρ lam X) X n ω = (wealth m lam X n ω - ρ) / (1 - ρ) :=
    fun n ↦ wealth_oppLeverage (Set.Ioo_subset_Icc_self hm) hρ.2.ne fun k _ ↦ hω k
  refine ⟨hW, fun n hn ↦ ?_, fun hlim ↦ ?_, fun n hn ↦ ?_, fun w hw hw1 ↦ ⟨?_, ?_⟩⟩
  · rw [hW, lt_div_iff₀ hρ1]
    nlinarith [hρ.1]
  · have h := ((tendsto_const_nhds (x := ρ)).div_atTop hlim).const_sub 1 |>.div_const (1 - ρ)
    rw [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [hlim.eventually_gt_atTop 0] with n hn
    rw [hW]
    field_simp
  · rw [hW, div_lt_iff₀ hρ1]
    nlinarith [hρ.1]
  · simp_rw [hW]
    exact (hw.sub_const ρ).div_const _
  · rw [div_lt_iff₀ hρ1]
    nlinarith [hρ.1]

end Wang2026Almost
