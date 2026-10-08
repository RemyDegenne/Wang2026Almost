/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cesàro means of a sequence with a summable weighted series

If `a k ∈ [0, 1]` and `∑ a k / k < ∞`, then the Cesàro means `(1 / n) ∑_{k < n} a k` tend to `0`.
This is the special case of Kronecker's lemma used by Wang, Agrawal, Ramdas (2026) in the proof
of their Theorem 2.2.

## Main statements

* `tendsto_cesaro_zero_of_summable_div`.
-/

@[expose] public section

open Filter Finset
open scoped Topology

/-- **Cesàro means of a sequence with summable `a k / k`**: if `a k ∈ [0, 1]` and
`∑ a k / k < ∞`, then `(1 / n) ∑_{k < n} a k → 0`. For `1 ≤ N ≤ n`,
`(1 / n) ∑_{k < n} a k ≤ N / n + ∑_{k ≥ N} a k / k`. -/
lemma tendsto_cesaro_zero_of_summable_div {a : ℕ → ℝ} (h0 : ∀ k, 0 ≤ a k) (h1 : ∀ k, a k ≤ 1)
    (h : Summable (fun k ↦ a k / k)) :
    Tendsto (fun n ↦ (∑ k ∈ Finset.range n, a k) / n) atTop (𝓝 0) := by
  set f : ℕ → ℝ := fun k ↦ a k / k with hf_def
  have hf_nonneg : ∀ k, 0 ≤ f k := fun k ↦ div_nonneg (h0 k) k.cast_nonneg
  -- the tails `∑' f - ∑_{k < N} f k` tend to `0`
  have h_tail : Tendsto (fun N ↦ ∑' k, f k - ∑ k ∈ range N, f k) atTop (𝓝 0) := by
    have := (tendsto_const_nhds (x := ∑' k, f k)).sub h.hasSum.tendsto_sum_nat
    simpa using this
  -- key bound: `(∑_{k<n} a k) / n ≤ N / n + (∑' f - ∑_{k<N} f k)` for `1 ≤ N ≤ n`
  have h_bound : ∀ N n, 1 ≤ N → N ≤ n →
      (∑ k ∈ range n, a k) / n ≤ N / n + (∑' k, f k - ∑ k ∈ range N, f k) := by
    intro N n hN hNn
    have hn : (0 : ℝ) < n := by exact_mod_cast (hN.trans hNn)
    rw [div_le_iff₀ hn, add_mul, div_mul_cancel₀ _ hn.ne', ← sum_range_add_sum_Ico _ hNn]
    gcongr
    · calc ∑ k ∈ range N, a k ≤ ∑ _k ∈ range N, (1 : ℝ) := sum_le_sum fun k _ ↦ h1 k
        _ = N := by simp
    · calc ∑ k ∈ Ico N n, a k ≤ ∑ k ∈ Ico N n, f k * n := by
            refine sum_le_sum fun k hk ↦ ?_
            have hk0 : (0 : ℝ) < k := Nat.cast_pos.2 (by have := (mem_Ico.1 hk).1; omega)
            have hkn : (k : ℝ) ≤ n := by exact_mod_cast (mem_Ico.1 hk).2.le
            rw [hf_def, div_mul_eq_mul_div, le_div_iff₀ hk0]
            exact mul_le_mul_of_nonneg_left hkn (h0 k)
        _ = (∑ k ∈ Ico N n, f k) * n := by rw [sum_mul]
        _ ≤ (∑' k, f k - ∑ k ∈ range N, f k) * n := by
            gcongr
            rw [le_sub_iff_add_le, add_comm, sum_range_add_sum_Ico _ hNn]
            exact h.sum_le_tsum _ fun k _ ↦ hf_nonneg k
  refine tendsto_order.2 ⟨fun b hb ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards with n
    exact hb.trans_le (div_nonneg (sum_nonneg fun k _ ↦ h0 k) n.cast_nonneg)
  · obtain ⟨N, hN, hN1⟩ := ((h_tail.eventually (gt_mem_nhds (half_pos hb))).and
      (eventually_ge_atTop 1)).exists
    have h_lim : Tendsto (fun n : ℕ ↦ (N : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [h_lim.eventually (gt_mem_nhds (half_pos hb)), eventually_ge_atTop N]
      with n hn hNn
    calc (∑ k ∈ range n, a k) / n ≤ N / n + (∑' k, f k - ∑ k ∈ range N, f k) :=
          h_bound N n hN1 hNn
      _ < b / 2 + b / 2 := add_lt_add hn hN
      _ = b := add_halves b
