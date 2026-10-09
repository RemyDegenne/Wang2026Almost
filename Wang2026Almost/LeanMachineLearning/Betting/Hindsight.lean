/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.WealthLemmas
public import Wang2026Almost.LeanMachineLearning.Betting.Domination
public import Wang2026Almost.Mathlib.Analysis.SpecialFunctions.Log.OneAdd
public import Mathlib.Analysis.Calculus.LocalExtr.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Topology.Algebra.Order.Archimedean

/-!
# The best-in-hindsight wealth

Deterministic analysis of the hindsight wealth `F_n(l) = ∏_{k < n} (1 + l y_k)` of the
fixed-fraction betting strategies, for reals `y_k ∈ [-m, 1 - m]` (the centered observations
`y_k = X_k - m`) such that, for some `σ² > 0`, `S_n = ∑_{k < n} y_k = O(√n log n)` and
`V_n - n σ² = O(√n log n)` with `V_n = ∑_{k < n} y_k²` (a property of almost all paths under a
non-degenerate null distribution).

The log-wealth `f_n(l) = ∑_{k < n} log (1 + l y_k)` is close to the quadratic
`l S_n - l² V_n / 2` for small `l`. Consequently, for large `n`, the fixed fractions of size
`|l| ≥ n ^ (-1/3)` lose in hindsight (`F_n(l) < 1`), every maximizer `g` of `F_n` on the fraction
range is within `O(log² n / n)` of `S_n / V_n` (the GRAPA bet fraction), and
`2 log max_l F_n(l) = S_n² / V_n + o(1)`.

## Main statements

* `abs_sum_log_one_add_mul_sub_le`: the quadratic expansion
  `|f_n(l) - (l S_n - l² V_n / 2)| ≤ 2 n |l|³` for `|l| ≤ 1 / 2`;
* `exists_abs_le_mul_eq_of_forall_prod_le`: the first-order condition `g V_n = S_n + g² R`,
  `|R| ≤ 2 n`, at a maximizer `g` of `F_n` near `0`;
* `eventually_prod_one_add_mul_lt_one`: eventually, `F_n(l) < 1` for `|l| ≥ n ^ (-1/3)`;
* `eventually_abs_le_of_isMaxOn`, `eventually_abs_sub_div_le_of_isMaxOn`: location of the
  maximizers `g` of `F_n`: `|g| ≤ K log n / √n` and `|g - S_n / V_n| ≤ K log² n / n`;
* `tendsto_two_mul_log_iSup_sub`: `2 log sup_l F_n(l) - S_n² / V_n → 0`;
* `eventually_fixedWealth_lt_one`, `eventually_abs_le_of_isMaxOn_fixedWealth`,
  `eventually_abs_sub_div_le_of_isMaxOn_fixedWealth`, `tendsto_two_mul_hindsightLogWealth_sub`:
  the same results for the fixed-fraction wealths `fixedWealth m l X n ω` of observations
  `X k ω ∈ [0, 1]` (with `y_k = X k ω - m`);
* `measurable_hindsightLogWealth`: the best-in-hindsight log-wealth is measurable.

## Implementation notes

The asymptotic computations are done in the variables `t = n ^ (1/6) → ∞` and
`b = log n / t → 0`, in which `n = t ^ 6`, `√n = t ^ 3`, `n ^ (-1/3) = t ^ (-2)`, `log n = b t`,
and the assumptions read `|S_n| ≤ C b t ^ 4`, `|V_n - t ^ 6 σ²| ≤ C b t ^ 4`.
-/

@[expose] public section

open Finset Filter Asymptotics
open scoped Topology

namespace Learning.Betting

variable {Ω : Type*}

/-! ### Quadratic expansion of the log-wealth -/

/-- **Quadratic expansion of the log-wealth**: for `|l| ≤ 1 / 2` and `|y k| ≤ 1`,
`|∑_{k < n} log (1 + l y_k) - (l S_n - l² V_n / 2)| ≤ 2 n |l|³`, with `S_n = ∑_{k < n} y_k` and
`V_n = ∑_{k < n} y_k²`. -/
lemma abs_sum_log_one_add_mul_sub_le {y : ℕ → ℝ} {n : ℕ} (hy : ∀ k < n, |y k| ≤ 1) {l : ℝ}
    (hl : |l| ≤ 1 / 2) :
    |∑ k ∈ range n, Real.log (1 + l * y k)
      - (l * ∑ k ∈ range n, y k - l ^ 2 * (∑ k ∈ range n, y k ^ 2) / 2)| ≤ 2 * n * |l| ^ 3 := by
  have h : ∑ k ∈ range n, Real.log (1 + l * y k)
      - (l * ∑ k ∈ range n, y k - l ^ 2 * (∑ k ∈ range n, y k ^ 2) / 2)
      = ∑ k ∈ range n, (Real.log (1 + l * y k) - (l * y k - (l * y k) ^ 2 / 2)) := by
    rw [sum_sub_distrib, mul_sum, mul_sum, sum_div, ← sum_sub_distrib]
    congr 1
    refine sum_congr rfl fun k _ ↦ ?_
    ring
  rw [h]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range n, |Real.log (1 + l * y k) - (l * y k - (l * y k) ^ 2 / 2)|
      ≤ ∑ k ∈ range n, 2 * |l| ^ 3 := by
        refine sum_le_sum fun k hk ↦ ?_
        have hyk := hy k (mem_range.1 hk)
        have hly : |l * y k| ≤ |l| := by
          rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) hyk
        refine (Real.abs_log_one_add_sub_le (hly.trans hl)).trans ?_
        gcongr
    _ = 2 * n * |l| ^ 3 := by rw [sum_const, card_range, nsmul_eq_mul]; ring

/-- For `|l| < 1` and `|y k| ≤ 1`, the product `∏_{k < n} (1 + l y_k)` is positive and its
logarithm is `∑_{k < n} log (1 + l y_k)`. -/
lemma prod_one_add_mul_pos_and_log_eq {y : ℕ → ℝ} {n : ℕ} (hy : ∀ k < n, |y k| ≤ 1) {l : ℝ}
    (hl : |l| < 1) :
    0 < ∏ k ∈ range n, (1 + l * y k) ∧
      Real.log (∏ k ∈ range n, (1 + l * y k)) = ∑ k ∈ range n, Real.log (1 + l * y k) := by
  have hpos : ∀ k ∈ range n, 0 < 1 + l * y k := fun k hk ↦ by
    have h1 : |l * y k| < 1 := by
      rw [abs_mul]
      exact (mul_le_of_le_one_right (abs_nonneg _) (hy k (mem_range.1 hk))).trans_lt hl
    linarith [neg_abs_le (l * y k)]
  exact ⟨prod_pos hpos, Real.log_prod fun k hk ↦ (hpos k hk).ne'⟩

/-! ### Measurability of the hindsight log-wealth -/

/-- The supremum of a continuous function over a nondegenerate closed interval is its supremum
over the rational points of the interval. -/
lemma ciSup_Icc_eq_ciSup_rat {G : ℝ → ℝ} (hG : Continuous G) {a b : ℝ} (hab : a < b) :
    ⨆ l : Set.Icc a b, G l = ⨆ q : {q : ℚ // (q : ℝ) ∈ Set.Icc a b}, G q := by
  have : Nonempty (Set.Icc a b) := ⟨⟨a, Set.left_mem_Icc.2 hab.le⟩⟩
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := a) (b := b)).bddAbove_image hG.continuousOn
  have hbdd : BddAbove (Set.range fun l : Set.Icc a b ↦ G l) :=
    ⟨B, by rintro _ ⟨l, rfl⟩; exact hB ⟨l, l.2, rfl⟩⟩
  have hbddq : BddAbove (Set.range fun q : {q : ℚ // (q : ℝ) ∈ Set.Icc a b} ↦ G q) :=
    ⟨B, by rintro _ ⟨q, rfl⟩; exact hB ⟨q, q.2, rfl⟩⟩
  obtain ⟨q₀, hq₀⟩ := exists_rat_btwn hab
  have : Nonempty {q : ℚ // (q : ℝ) ∈ Set.Icc a b} := ⟨⟨q₀, hq₀.1.le, hq₀.2.le⟩⟩
  refine le_antisymm (ciSup_le fun l ↦ ?_) (ciSup_le fun q ↦ le_ciSup hbdd ⟨q, q.2⟩)
  have hsub : Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)
      ⊆ {x | G x ≤ ⨆ q : {q : ℚ // (q : ℝ) ∈ Set.Icc a b}, G q} := by
    rintro _ ⟨hx, q, rfl⟩
    exact le_ciSup hbddq ⟨q, Set.Ioo_subset_Icc_self hx⟩
  have hl : (l : ℝ) ∈ closure (Set.Ioo a b ∩ Set.range ((↑) : ℚ → ℝ)) := by
    have h1 := Dense.open_subset_closure_inter Rat.denseRange_cast (isOpen_Ioo (a := a) (b := b))
    have h2 : (l : ℝ) ∈ closure (Set.Ioo a b) := by rw [closure_Ioo hab.ne]; exact l.2
    exact closure_minimal h1 isClosed_closure h2
  exact (isClosed_le hG continuous_const).closure_subset_iff.2 hsub hl

/-- The best-in-hindsight log-wealth `log (sup_{l ∈ fractionRange m} W^l_n)` of measurable
observations is measurable: the supremum can be taken over the rational fractions. -/
lemma measurable_hindsightLogWealth [MeasurableSpace Ω] {m : ℝ} (hm : m ∈ Set.Ioo 0 1)
    {X : ℕ → Ω → ℝ} (hX : ∀ k, Measurable (X k)) (n : ℕ) :
    Measurable (hindsightLogWealth m X n) := by
  have h : ∀ ω, (⨆ l : fractionRange m, fixedWealth m l X n ω)
      = ⨆ q : {q : ℚ // (q : ℝ) ∈ fractionRange m}, fixedWealth m q X n ω := fun ω ↦
    ciSup_Icc_eq_ciSup_rat (continuous_fixedWealth m X n ω) (neg_one_div_one_sub_lt_one_div hm)
  unfold hindsightLogWealth
  simp_rw [h]
  exact Real.measurable_log.comp
    (Measurable.iSup fun q ↦ measurable_wealth (fun _ ↦ measurable_const) hX n)

/-! ### First-order condition -/

/-- **First-order condition for the hindsight wealth**: if `|g| < 1 / 2` maximizes
`l ↦ ∏_{k < n} (1 + l y_k)` over `|l| < 1 / 2`, where `|y k| ≤ 1`, then `g V_n = S_n + g² R` for
some `|R| ≤ 2 n`, with `S_n = ∑_{k < n} y_k` and `V_n = ∑_{k < n} y_k²`. -/
lemma exists_abs_le_mul_eq_of_forall_prod_le {y : ℕ → ℝ} {n : ℕ} (hy : ∀ k < n, |y k| ≤ 1)
    {g : ℝ} (hg : |g| < 1 / 2)
    (hmax : ∀ l, |l| < 1 / 2 → ∏ k ∈ range n, (1 + l * y k) ≤ ∏ k ∈ range n, (1 + g * y k)) :
    ∃ R : ℝ, |R| ≤ 2 * n ∧ g * ∑ k ∈ range n, y k ^ 2 = ∑ k ∈ range n, y k + g ^ 2 * R := by
  have hgy : ∀ k ∈ range n, |g * y k| ≤ |g| := fun k hk ↦ by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (hy k (mem_range.1 hk))
  have hpos : ∀ k ∈ range n, 1 / 2 ≤ 1 + g * y k := fun k hk ↦ by
    linarith [neg_abs_le (g * y k), hgy k hk]
  -- the log-wealth has a local maximum at `g`
  have hlocal : IsLocalMax (fun l ↦ ∑ k ∈ range n, Real.log (1 + l * y k)) g := by
    have hU : Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ∈ 𝓝 g := isOpen_Ioo.mem_nhds (abs_lt.1 hg)
    filter_upwards [hU] with l hl
    have hl' : |l| < 1 / 2 := abs_lt.2 hl
    obtain ⟨hFl, hlogl⟩ := prod_one_add_mul_pos_and_log_eq hy (hl'.trans (by norm_num))
    obtain ⟨hFg, hlogg⟩ := prod_one_add_mul_pos_and_log_eq hy (hg.trans (by norm_num))
    rw [← hlogl, ← hlogg]
    exact Real.log_le_log hFl (hmax l hl')
  have hderiv : HasDerivAt (fun l ↦ ∑ k ∈ range n, Real.log (1 + l * y k))
      (∑ k ∈ range n, y k / (1 + g * y k)) g := by
    refine HasDerivAt.fun_sum fun k hk ↦ ?_
    have h := (((hasDerivAt_id' g).mul_const (y k)).const_add 1).log
      (by linarith [hpos k hk] : 0 < 1 + g * y k).ne'
    simpa using h
  have h0 := hlocal.hasDerivAt_eq_zero hderiv
  refine ⟨∑ k ∈ range n, y k ^ 3 / (1 + g * y k), ?_, ?_⟩
  · refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ range n, |y k ^ 3 / (1 + g * y k)| ≤ ∑ k ∈ range n, (2 : ℝ) := by
          refine sum_le_sum fun k hk ↦ ?_
          have h1 := hpos k hk
          rw [abs_div, abs_of_pos (a := 1 + g * y k) (by linarith), div_le_iff₀ (by linarith),
            abs_pow]
          have : |y k| ^ 3 ≤ 1 := pow_le_one₀ (abs_nonneg _) (hy k (mem_range.1 hk))
          linarith
      _ = 2 * n := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  · have h1 : ∑ k ∈ range n, y k / (1 + g * y k) = ∑ k ∈ range n, y k
        - g * ∑ k ∈ range n, y k ^ 2 + g ^ 2 * ∑ k ∈ range n, y k ^ 3 / (1 + g * y k) := by
      rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
      refine sum_congr rfl fun k hk ↦ ?_
      have h1 : 1 + y k * g ≠ 0 := (by linarith [hpos k hk] : 0 < 1 + y k * g).ne'
      field_simp
      ring
    linarith

/-! ### Asymptotic analysis of the hindsight wealth -/

section Asymptotics

variable {m σ2 : ℝ} {y : ℕ → ℝ}

/-- Powers of `x ^ (1 / 6)`. -/
private lemma rpow_one_div_six_pow {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (x ^ ((1 : ℝ) / 6)) ^ k = x ^ ((k : ℝ) / 6) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  ring_nf

/-- With `t = x ^ (1 / 6)`: `t > 0`, `x = t ^ 6`, `√x = t ^ 3` and `x ^ (-1/3) = (t ^ 2)⁻¹`. -/
private lemma rpow_one_div_six_facts {x : ℝ} (hx : 0 < x) :
    0 < x ^ ((1 : ℝ) / 6) ∧ x = (x ^ ((1 : ℝ) / 6)) ^ 6 ∧ √x = (x ^ ((1 : ℝ) / 6)) ^ 3 ∧
      x ^ (-(1 / 3 : ℝ)) = ((x ^ ((1 : ℝ) / 6)) ^ 2)⁻¹ := by
  refine ⟨Real.rpow_pos_of_pos hx _, ?_, ?_, ?_⟩
  · rw [rpow_one_div_six_pow hx.le]; norm_num
  · rw [rpow_one_div_six_pow hx.le, Real.sqrt_eq_rpow]; norm_num
  · rw [rpow_one_div_six_pow hx.le, Real.rpow_neg hx.le]; norm_num

/-- `n ^ (1 / 6) → ∞`. -/
private lemma tendsto_rpow_one_div_six :
    Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ((1 : ℝ) / 6)) atTop atTop :=
  (tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop

/-- `log n / n ^ (1 / 6) → 0`. -/
private lemma tendsto_log_div_rpow_one_div_six :
    Tendsto (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ ((1 : ℝ) / 6)) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 6)).tendsto_div_nhds_zero.comp
    tendsto_natCast_atTop_atTop

/-- A bound `|S n| ≤ C √n log n` with `C ≥ 0` from `S n = O(√n log n)`. -/
private lemma exists_nonneg_bound {S : ℕ → ℝ}
    (hS : S =O[atTop] (fun n : ℕ ↦ √n * Real.log n)) :
    ∃ C, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, |S n| ≤ C * (√n * Real.log n) := by
  obtain ⟨c, hc⟩ := hS.bound
  refine ⟨max c 0, le_max_right _ _, ?_⟩
  filter_upwards [hc, eventually_ge_atTop 1] with n hn hn1
  have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have h0 : 0 ≤ √(n : ℝ) * Real.log n := mul_nonneg (Real.sqrt_nonneg _) hlog
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) h0)

/-- The bounds `|S n| ≤ C₁ √n log n` and `|V n - n σ²| ≤ C₂ √n log n` in the variables
`t = n ^ (1 / 6)` and `b = log n / t`, which tend to `∞` and `0`: then `n = t ^ 6`, `√n = t ^ 3`,
`n ^ (-1/3) = t ^ (-2)`, `log n = b t`, `|S n| ≤ C₁ b t ^ 4` and `|V n - t ^ 6 σ²| ≤ C₂ b t ^ 4`. -/
private lemma eventually_exists_good {S V : ℕ → ℝ} {C1 C2 η : ℝ} (hη : 0 < η) (T : ℝ)
    (hS : ∀ᶠ n : ℕ in atTop, |S n| ≤ C1 * (√n * Real.log n))
    (hV : ∀ᶠ n : ℕ in atTop, |V n - n * σ2| ≤ C2 * (√n * Real.log n)) :
    ∀ᶠ n : ℕ in atTop, ∃ t b : ℝ, 0 < t ∧ T ≤ t ∧ 0 ≤ b ∧ b ≤ η ∧ (n : ℝ) = t ^ 6 ∧
      √(n : ℝ) = t ^ 3 ∧ (n : ℝ) ^ (-(1 / 3 : ℝ)) = (t ^ 2)⁻¹ ∧ Real.log n = b * t ∧
      |S n| ≤ C1 * b * t ^ 4 ∧ |V n - t ^ 6 * σ2| ≤ C2 * b * t ^ 4 := by
  filter_upwards [hS, hV, eventually_ge_atTop 1, tendsto_rpow_one_div_six.eventually_ge_atTop T,
    (tendsto_order.1 tendsto_log_div_rpow_one_div_six).2 η hη] with n hSn hVn hn1 hT hb
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨ht, h6, h3, hδ⟩ := rpow_one_div_six_facts hn0
  set t := (n : ℝ) ^ ((1 : ℝ) / 6)
  have hlog : Real.log n = Real.log n / t * t := (div_mul_cancel₀ _ ht.ne').symm
  have hb0 : 0 ≤ Real.log n / t := div_nonneg (Real.log_nonneg (by exact_mod_cast hn1)) ht.le
  refine ⟨t, Real.log n / t, ht, hT, hb0, hb.le, h6, h3, hδ, hlog, ?_, ?_⟩
  · calc |S n| ≤ C1 * (√n * Real.log n) := hSn
      _ = C1 * (Real.log n / t) * t ^ 4 := by rw [h3]; field_simp
  · rw [← h6]
    calc |V n - n * σ2| ≤ C2 * (√n * Real.log n) := hVn
      _ = C2 * (Real.log n / t) * t ^ 4 := by rw [h3]; field_simp

/-- Algebraic step of `eventually_prod_one_add_mul_lt_one`. -/
private lemma aux_neg {t b S V C1 C2 : ℝ} (hσ : 0 < σ2) (ht : 2 + 8 / σ2 ≤ t)
    (hC1 : C1 * b ≤ σ2 / 4) (hC2 : C2 * b ≤ σ2 / 4) (hS : |S| ≤ C1 * b * t ^ 4)
    (hV : |V - t ^ 6 * σ2| ≤ C2 * b * t ^ 4) :
    (t ^ 2)⁻¹ * |S| - ((t ^ 2)⁻¹) ^ 2 * V / 2 + 2 * t ^ 6 * ((t ^ 2)⁻¹) ^ 3 < 0 := by
  have h8 : 0 < 8 / σ2 := by positivity
  have ht0 : 0 < t := by linarith
  have ht2 : 0 < t ^ 2 := by positivity
  have hVl : t ^ 6 * σ2 - C2 * b * t ^ 4 ≤ V := by linarith [(abs_le.1 hV).1]
  have e1 : (t ^ 2)⁻¹ * |S| ≤ C1 * b * t ^ 2 := by
    rw [inv_mul_le_iff₀ ht2]
    calc |S| ≤ C1 * b * t ^ 4 := hS
      _ = t ^ 2 * (C1 * b * t ^ 2) := by ring
  have e2 : t ^ 2 * σ2 - C2 * b ≤ ((t ^ 2)⁻¹) ^ 2 * V := by
    calc t ^ 2 * σ2 - C2 * b = ((t ^ 2)⁻¹) ^ 2 * (t ^ 6 * σ2 - C2 * b * t ^ 4) := by
          field_simp
      _ ≤ ((t ^ 2)⁻¹) ^ 2 * V := by gcongr
  have e3 : 2 * t ^ 6 * ((t ^ 2)⁻¹) ^ 3 = 2 := by field_simp
  have e4 : t ^ 2 * (C1 * b) ≤ t ^ 2 * (σ2 / 4) := by gcongr
  have e5 : 8 + 2 * σ2 ≤ t * σ2 := by
    have := mul_le_mul_of_nonneg_right ht hσ.le
    rw [add_mul, div_mul_cancel₀ _ hσ.ne'] at this
    linarith
  have e6 : t * σ2 ≤ t ^ 2 * σ2 := by gcongr; nlinarith
  nlinarith

/-- A lower bound on `V` in the variable `t`. -/
private lemma aux_V {t b V C2 : ℝ} (hσ : 0 < σ2) (ht : 2 + 8 / σ2 ≤ t)
    (hC2 : C2 * b ≤ σ2 / 4) (hV : |V - t ^ 6 * σ2| ≤ C2 * b * t ^ 4) :
    t ^ 6 * σ2 / 2 + 2 * t ^ 4 ≤ V := by
  have h8 : 0 < 8 / σ2 := by positivity
  have ht0 : 0 < t := by linarith
  have hVl : t ^ 6 * σ2 - C2 * b * t ^ 4 ≤ V := by linarith [(abs_le.1 hV).1]
  have e5 : 8 + 2 * σ2 ≤ t * σ2 := by
    have := mul_le_mul_of_nonneg_right ht hσ.le
    rw [add_mul, div_mul_cancel₀ _ hσ.ne'] at this
    linarith
  have e6 : t * σ2 ≤ t ^ 2 * σ2 := by gcongr; nlinarith
  have e7 : C2 * b * t ^ 4 ≤ σ2 / 4 * t ^ 4 := by gcongr
  have e8 : (8 + 2 * σ2) * t ^ 4 ≤ t ^ 2 * σ2 * t ^ 4 := by gcongr; linarith
  nlinarith

/-- Algebraic step of the location of the maximizers. -/
private lemma aux_location {t b S V R g C1 C2 : ℝ} (hσ : 0 < σ2) (ht : 2 + 8 / σ2 ≤ t)
    (hC2 : C2 * b ≤ σ2 / 4) (hS : |S| ≤ C1 * b * t ^ 4)
    (hV : |V - t ^ 6 * σ2| ≤ C2 * b * t ^ 4) (hR : |R| ≤ 2 * t ^ 6) (hg : |g| < (t ^ 2)⁻¹)
    (heq : g * V = S + g ^ 2 * R) :
    |g| ≤ 2 * C1 / σ2 * (b / t ^ 2) ∧ |g - S / V| ≤ 16 * C1 ^ 2 / σ2 ^ 3 * (b ^ 2 / t ^ 4) := by
  have h8 : 0 < 8 / σ2 := by positivity
  have ht0 : 0 < t := by linarith
  have hV2 := aux_V hσ ht hC2 hV
  have hVpos : 0 < V := by
    have : 0 < t ^ 6 * σ2 / 2 + 2 * t ^ 4 := by positivity
    linarith
  have h1 : |g| * V ≤ |S| + |g| * (2 * t ^ 4) := by
    have h := congrArg abs heq
    rw [abs_mul, abs_of_pos hVpos] at h
    rw [h]
    calc |S + g ^ 2 * R| ≤ |S| + |g ^ 2 * R| := abs_add_le _ _
      _ = |S| + |g| * (|g| * |R|) := by rw [abs_mul, abs_pow]; ring
      _ ≤ |S| + |g| * ((t ^ 2)⁻¹ * (2 * t ^ 6)) := by gcongr
      _ = |S| + |g| * (2 * t ^ 4) := by field_simp
  have h2 : |g| * (t ^ 6 * σ2 / 2) ≤ C1 * b * t ^ 4 := by
    have := mul_le_mul_of_nonneg_left hV2 (abs_nonneg g)
    nlinarith
  have hgb : |g| ≤ 2 * C1 / σ2 * (b / t ^ 2) := by
    rw [show 2 * C1 / σ2 * (b / t ^ 2) = C1 * b * t ^ 4 / (t ^ 6 * σ2 / 2) by field_simp,
      le_div_iff₀ (by positivity)]
    exact h2
  refine ⟨hgb, ?_⟩
  have h3 : g - S / V = g ^ 2 * R / V := by
    field_simp
    linarith
  rw [h3, abs_div, abs_mul, abs_of_pos hVpos, abs_pow]
  have hV3 : t ^ 6 * σ2 / 2 ≤ V := by
    have : 0 ≤ 2 * t ^ 4 := by positivity
    linarith
  calc |g| ^ 2 * |R| / V ≤ |g| ^ 2 * (2 * t ^ 6) / (t ^ 6 * σ2 / 2) := by gcongr
    _ = 4 / σ2 * |g| ^ 2 := by field_simp; ring
    _ ≤ 4 / σ2 * (2 * C1 / σ2 * (b / t ^ 2)) ^ 2 := by gcongr
    _ = 16 * C1 ^ 2 / σ2 ^ 3 * (b ^ 2 / t ^ 4) := by field_simp; ring

/-- `-1 ≤ a x` for `|a| ≤ 1` and `|x| ≤ 1`. -/
private lemma neg_one_le_mul_of_abs_le {a x : ℝ} (ha : |a| ≤ 1) (hx : |x| ≤ 1) : -1 ≤ a * x := by
  have : |a * x| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg a, abs_nonneg x]
  linarith [neg_abs_le (a * x)]

/-- A centered observation `x ∈ [-m, 1 - m]` satisfies `|x| ≤ 1`. -/
private lemma abs_le_one_of_mem_Icc (hm : m ∈ Set.Ioo 0 1) {x : ℝ}
    (hx : x ∈ Set.Icc (-m) (1 - m)) : |x| ≤ 1 :=
  abs_le.2 ⟨by linarith [hx.1, hm.2], by linarith [hx.2, hm.1]⟩

private lemma mem_interior_fractionRange (hm : m ∈ Set.Ioo 0 1) {l : ℝ} (hl : |l| ≤ 1) :
    l ∈ interior (fractionRange m) :=
  Icc_neg_one_one_subset_interior_fractionRange hm (abs_le.1 hl)

private lemma mem_fractionRange_of_abs_le (hm : m ∈ Set.Ioo 0 1) {l : ℝ} (hl : |l| ≤ 1) :
    l ∈ fractionRange m :=
  Icc_neg_one_one_subset_fractionRange hm (abs_le.1 hl)

/-- For `l ∈ fractionRange m` and `x ∈ [-m, 1 - m]`, `1 + l x ≥ 0`. -/
private lemma one_add_mul_nonneg_of_mem (hm : m ∈ Set.Ioo 0 1) {l x : ℝ}
    (hl : l ∈ fractionRange m) (hx : x ∈ Set.Icc (-m) (1 - m)) : 0 ≤ 1 + l * x := by
  have h := one_add_mul_sub_nonneg (Set.Ioo_subset_Icc_self hm) hl (x := x + m)
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rwa [add_sub_cancel_right] at h

/-- `C b ≤ σ² / 4` for `0 ≤ C ≤ D` and `0 ≤ b ≤ σ² / (4 D)`. -/
private lemma mul_le_of_le_div_four_mul {C D b : ℝ} (hσ : 0 < σ2) (hC0 : 0 ≤ C) (hCD : C ≤ D)
    (hb0 : 0 ≤ b) (hb : b ≤ σ2 / (4 * D)) : C * b ≤ σ2 / 4 := by
  rcases hC0.eq_or_lt with rfl | hC
  · rw [zero_mul]; positivity
  calc C * b ≤ D * (σ2 / (4 * D)) := mul_le_mul hCD hb hb0 (hC.le.trans hCD)
    _ = σ2 / 4 := by field_simp [(hC.trans_le hCD).ne']

/-- `(t ^ 2)⁻¹ ≤ 1 / 2` for `t ≥ 2 + 8 / σ²`. -/
private lemma inv_sq_le_half {t : ℝ} (hσ : 0 < σ2) (ht : 2 + 8 / σ2 ≤ t) : (t ^ 2)⁻¹ ≤ 1 / 2 := by
  have h8 : 0 < 8 / σ2 := by positivity
  rw [inv_le_comm₀ (by nlinarith) (by norm_num)]
  nlinarith

/-- `a ε / (a + 1) < ε` for `a ≥ 0` and `ε > 0`. -/
private lemma mul_div_add_one_lt {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) : a * (ε / (a + 1)) < ε := by
  rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
  linarith

/-- **Large bets lose in hindsight**: under the assumptions `y k ∈ [-m, 1 - m]`,
`S_n = O(√n log n)` and `V_n - n σ² = O(√n log n)`, for all large `n`,
`∏_{k < n} (1 + l y_k) < 1` for every `l ∈ fractionRange m` with `|l| ≥ n ^ (-1/3)`. -/
lemma eventually_prod_one_add_mul_lt_one (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hy : ∀ k, y k ∈ Set.Icc (-m) (1 - m))
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, y k) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, y k ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    ∀ᶠ n : ℕ in atTop, ∀ l ∈ fractionRange m, (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |l| →
      ∏ k ∈ range n, (1 + l * y k) < 1 := by
  obtain ⟨C1, hC1, hSb⟩ := exists_nonneg_bound hS
  obtain ⟨C2, hC2, hVb⟩ := exists_nonneg_bound hV
  have hy1 : ∀ k, |y k| ≤ 1 := fun k ↦ abs_le_one_of_mem_Icc hm (hy k)
  have hη : 0 < σ2 / (4 * (C1 + C2 + 1)) := by positivity
  filter_upwards [eventually_exists_good hη (2 + 8 / σ2) hSb hVb] with n
    ⟨t, b, ht, hT, hb0, hbη, hn, _, hδ, _, hSn, hVn⟩ l hl hδl
  rw [hδ] at hδl
  have hδ0 : 0 < (t ^ 2)⁻¹ := by positivity
  have hδ2 := inv_sq_le_half hσ hT
  have hδy : ∀ k, -1 ≤ (t ^ 2)⁻¹ * y k := fun k ↦
    neg_one_le_mul_of_abs_le (by rw [abs_of_pos hδ0]; linarith) (hy1 k)
  -- the wealths of the fractions `± t⁻²` are less than `1`
  have hneg : ∀ l', |l'| = (t ^ 2)⁻¹ → ∏ k ∈ range n, (1 + l' * y k) < 1 := by
    intro l' hl'
    obtain ⟨hpos, hlog⟩ :=
      prod_one_add_mul_pos_and_log_eq (n := n) (fun k _ ↦ hy1 k) (by linarith : |l'| < 1)
    rw [← Real.log_neg_iff hpos, hlog]
    have hq := (abs_le.1 (abs_sum_log_one_add_mul_sub_le (n := n) (fun k _ ↦ hy1 k)
      (hl'.le.trans hδ2))).2
    have h1 : l' * ∑ k ∈ range n, y k ≤ (t ^ 2)⁻¹ * |∑ k ∈ range n, y k| := by
      rw [← hl', ← abs_mul]; exact le_abs_self _
    have h2 : l' ^ 2 = ((t ^ 2)⁻¹) ^ 2 := by rw [← sq_abs, hl']
    rw [h2, hl', hn] at hq
    have := aux_neg hσ hT
      (mul_le_of_le_div_four_mul hσ hC1 (by linarith) hb0 hbη)
      (mul_le_of_le_div_four_mul hσ hC2 (by linarith) hb0 hbη) hSn hVn
    linarith
  -- domination of the larger bets
  rcases le_or_gt 0 l with h0 | h0
  · rw [abs_of_nonneg h0] at hδl
    have hpos := (prod_one_add_mul_pos_and_log_eq (n := n) (fun k _ ↦ hy1 k) (l := (t ^ 2)⁻¹)
      (by rw [abs_of_pos hδ0]; linarith)).1
    calc ∏ k ∈ range n, (1 + l * y k)
        ≤ (∏ k ∈ range n, (1 + (t ^ 2)⁻¹ * y k)) ^ (l / (t ^ 2)⁻¹) :=
          prod_one_add_mul_le_rpow hδ0 hδl (fun k _ ↦ one_add_mul_nonneg_of_mem hm hl (hy k))
            fun k _ ↦ hδy k
      _ < 1 := Real.rpow_lt_one hpos.le (hneg _ (abs_of_pos hδ0))
          (div_pos (hδ0.trans_le hδl) hδ0)
  · rw [abs_of_neg h0] at hδl
    have hpos := (prod_one_add_mul_pos_and_log_eq (n := n) (fun k _ ↦ hy1 k)
      (l := -(t ^ 2)⁻¹) (by rw [abs_neg, abs_of_pos hδ0]; linarith)).1
    have h := prod_one_add_mul_le_rpow (ε := (t ^ 2)⁻¹) (l := -l) (y := fun k ↦ -y k) (n := n)
      hδ0 hδl (fun k _ ↦ by linarith [one_add_mul_nonneg_of_mem hm hl (hy k)])
      fun k _ ↦ neg_one_le_mul_of_abs_le (by rw [abs_of_pos hδ0]; linarith)
        (by rw [abs_neg]; exact hy1 k)
    have e1 : ∏ k ∈ range n, (1 + -l * -y k) = ∏ k ∈ range n, (1 + l * y k) :=
      prod_congr rfl fun k _ ↦ by ring
    have e2 : ∏ k ∈ range n, (1 + (t ^ 2)⁻¹ * -y k) = ∏ k ∈ range n, (1 + -(t ^ 2)⁻¹ * y k) :=
      prod_congr rfl fun k _ ↦ by ring
    rw [e1, e2] at h
    exact h.trans_lt (Real.rpow_lt_one hpos.le (hneg _ (by rw [abs_neg, abs_of_pos hδ0]))
      (div_pos (by linarith) hδ0))

/-- The location of a maximizer, at a fixed large `n`, in the variables `t = n ^ (1 / 6)` and
`b = log n / t`. -/
private lemma location_aux (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hy : ∀ k, y k ∈ Set.Icc (-m) (1 - m)) {n : ℕ} {t b C1 C2 : ℝ}
    (hT : 2 + 8 / σ2 ≤ t) (hC2 : C2 * b ≤ σ2 / 4) (hn : (n : ℝ) = t ^ 6)
    (hSn : |∑ k ∈ range n, y k| ≤ C1 * b * t ^ 4)
    (hVn : |∑ k ∈ range n, y k ^ 2 - t ^ 6 * σ2| ≤ C2 * b * t ^ 4)
    (hneg : ∀ l ∈ fractionRange m, (t ^ 2)⁻¹ ≤ |l| → ∏ k ∈ range n, (1 + l * y k) < 1)
    {g : ℝ} (hg : IsMaxOn (fun l ↦ ∏ k ∈ range n, (1 + l * y k)) (fractionRange m) g)
    (hgmem : g ∈ fractionRange m) :
    |g| < (t ^ 2)⁻¹ ∧ |g| ≤ 2 * C1 / σ2 * (b / t ^ 2) ∧
      |g - (∑ k ∈ range n, y k) / ∑ k ∈ range n, y k ^ 2|
        ≤ 16 * C1 ^ 2 / σ2 ^ 3 * (b ^ 2 / t ^ 4) := by
  have hy1 : ∀ k, |y k| ≤ 1 := fun k ↦ abs_le_one_of_mem_Icc hm (hy k)
  have hδ2 := inv_sq_le_half hσ hT
  have hF : 1 ≤ ∏ k ∈ range n, (1 + g * y k) := by
    simpa using isMaxOn_iff.1 hg 0 (mem_fractionRange_of_abs_le hm (by simp))
  have hgδ : |g| < (t ^ 2)⁻¹ := by
    by_contra h
    exact absurd (hneg g hgmem (not_lt.1 h)) (not_lt.2 hF)
  have hg2 : |g| < 1 / 2 := hgδ.trans_le hδ2
  obtain ⟨R, hR, heq⟩ := exists_abs_le_mul_eq_of_forall_prod_le (fun k _ ↦ hy1 k) hg2
    fun l hl ↦ isMaxOn_iff.1 hg l (mem_fractionRange_of_abs_le hm (by linarith))
  rw [hn] at hR
  exact ⟨hgδ, aux_location hσ hT hC2 hSn hVn hR hgδ heq⟩

/-- **Location of the hindsight maximizers**: under the assumptions `y k ∈ [-m, 1 - m]`,
`S_n = O(√n log n)` and `V_n - n σ² = O(√n log n)`, there is `K` such that for all large `n`,
every maximizer `g` of `F_n(l) = ∏_{k < n} (1 + l y_k)` on `fractionRange m` is in the interior
of the fraction range, with `|g| < n ^ (-1/3)`, `|g| ≤ K log n / √n` and
`|g - S_n / V_n| ≤ K log² n / n`. -/
lemma eventually_abs_le_of_isMaxOn (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hy : ∀ k, y k ∈ Set.Icc (-m) (1 - m))
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, y k) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, y k ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    ∃ K, ∀ᶠ n : ℕ in atTop, ∀ g,
      IsMaxOn (fun l ↦ ∏ k ∈ range n, (1 + l * y k)) (fractionRange m) g →
        g ∈ fractionRange m →
          g ∈ interior (fractionRange m) ∧ |g| < (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
            |g| ≤ K * Real.log n / √n ∧
            |g - (∑ k ∈ range n, y k) / ∑ k ∈ range n, y k ^ 2| ≤ K * Real.log n ^ 2 / n := by
  obtain ⟨C1, hC1, hSb⟩ := exists_nonneg_bound hS
  obtain ⟨C2, hC2, hVb⟩ := exists_nonneg_bound hV
  have hη : 0 < σ2 / (4 * (C1 + C2 + 1)) := by positivity
  refine ⟨2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3, ?_⟩
  filter_upwards [eventually_prod_one_add_mul_lt_one hm hσ hy hS hV,
    eventually_exists_good hη (2 + 8 / σ2) hSb hVb] with n hneg
    ⟨t, b, ht, hT, hb0, hbη, hn, hsqrt, hδ, hlog, hSn, hVn⟩ g hg hgmem
  rw [hδ] at hneg ⊢
  obtain ⟨hgδ, hgb, hgS⟩ := location_aux hm hσ hy hT
    (mul_le_of_le_div_four_mul hσ hC2 (by linarith) hb0 hbη) hn hSn hVn hneg hg hgmem
  have hδ2 := inv_sq_le_half hσ hT
  have hK1 : 2 * C1 / σ2 ≤ 2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3 :=
    le_add_of_nonneg_right (by positivity)
  have hK2 : 16 * C1 ^ 2 / σ2 ^ 3 ≤ 2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3 :=
    le_add_of_nonneg_left (by positivity)
  refine ⟨mem_interior_fractionRange hm (by linarith), hgδ, ?_, ?_⟩
  · rw [hlog, hsqrt, show (2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3) * (b * t) / t ^ 3
      = (2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3) * (b / t ^ 2) by field_simp]
    exact hgb.trans (by gcongr)
  · rw [hlog, hn, show (2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3) * (b * t) ^ 2 / t ^ 6
      = (2 * C1 / σ2 + 16 * C1 ^ 2 / σ2 ^ 3) * (b ^ 2 / t ^ 4) by field_simp]
    exact hgS.trans (by gcongr)

/-- **Location of the hindsight maximizers**: under the assumptions `y k ∈ [-m, 1 - m]`,
`S_n = O(√n log n)` and `V_n - n σ² = O(√n log n)`, there is `K` such that for all large `n`,
every maximizer `g` of `F_n(l) = ∏_{k < n} (1 + l y_k)` on `fractionRange m` satisfies
`|g - S_n / V_n| ≤ K log² n / n`. See `eventually_abs_le_of_isMaxOn` for more bounds. -/
lemma eventually_abs_sub_div_le_of_isMaxOn (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hy : ∀ k, y k ∈ Set.Icc (-m) (1 - m))
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, y k) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, y k ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    ∃ K, ∀ᶠ n : ℕ in atTop, ∀ g,
      IsMaxOn (fun l ↦ ∏ k ∈ range n, (1 + l * y k)) (fractionRange m) g →
        g ∈ fractionRange m →
          |g - (∑ k ∈ range n, y k) / ∑ k ∈ range n, y k ^ 2| ≤ K * Real.log n ^ 2 / n := by
  obtain ⟨K, hK⟩ := eventually_abs_le_of_isMaxOn hm hσ hy hS hV
  exact ⟨K, hK.mono fun n hn g hg hgmem ↦ (hn g hg hgmem).2.2.2⟩

/-- **Value of the hindsight log-wealth**: under the assumptions `y k ∈ [-m, 1 - m]`,
`S_n = O(√n log n)` and `V_n - n σ² = O(√n log n)`,
`2 log sup_{l ∈ fractionRange m} ∏_{k < n} (1 + l y_k) - S_n² / V_n → 0`. -/
lemma tendsto_two_mul_log_iSup_sub (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hy : ∀ k, y k ∈ Set.Icc (-m) (1 - m))
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, y k) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, y k ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    Tendsto (fun n : ℕ ↦ 2 * Real.log (⨆ l : fractionRange m, ∏ k ∈ range n, (1 + l * y k))
      - (∑ k ∈ range n, y k) ^ 2 / ∑ k ∈ range n, y k ^ 2) atTop (𝓝 0) := by
  obtain ⟨C1, hC1, hSb⟩ := exists_nonneg_bound hS
  obtain ⟨C2, hC2, hVb⟩ := exists_nonneg_bound hV
  have hy1 : ∀ k, |y k| ≤ 1 := fun k ↦ abs_le_one_of_mem_Icc hm (hy k)
  have hK0 : 0 ≤ 2 * C1 / σ2 := by positivity
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hη1 : 0 < σ2 / (4 * (C1 + C2 + 1)) := by positivity
  have hη2 : 0 < ε / (8 * (2 * C1 / σ2) ^ 3 + 1) := by positivity
  have hη : 0 < min (σ2 / (4 * (C1 + C2 + 1))) (min 1 (ε / (8 * (2 * C1 / σ2) ^ 3 + 1))) :=
    lt_min hη1 (lt_min one_pos hη2)
  filter_upwards [eventually_prod_one_add_mul_lt_one hm hσ hy hS hV,
    eventually_exists_good hη (2 + 8 / σ2) hSb hVb] with n hneg
    ⟨t, b, ht, hT, hb0, hbη, hn, _, hδ, _, hSn, hVn⟩
  rw [hδ] at hneg
  have hbη1 : b ≤ σ2 / (4 * (C1 + C2 + 1)) := hbη.trans (min_le_left _ _)
  have hb1 : b ≤ 1 := hbη.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbε : b ≤ ε / (8 * (2 * C1 / σ2) ^ 3 + 1) :=
    hbη.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hC1b := mul_le_of_le_div_four_mul hσ hC1 (by linarith) hb0 hbη1
  have hC2b := mul_le_of_le_div_four_mul hσ hC2 (by linarith) hb0 hbη1
  have hδ2 := inv_sq_le_half hσ hT
  have h8 : 0 < 8 / σ2 := by positivity
  have ht1 : 1 ≤ t ^ 2 := by nlinarith
  -- a maximizer `g` of the hindsight wealth: the supremum is its wealth
  have h0mem : (0 : ℝ) ∈ fractionRange m := mem_fractionRange_of_abs_le hm (by simp)
  obtain ⟨g, hgmem, hg⟩ := (isCompact_Icc : IsCompact (fractionRange m)).exists_isMaxOn
    ⟨0, h0mem⟩ (f := fun l ↦ ∏ k ∈ range n, (1 + l * y k)) (by fun_prop)
  obtain ⟨hgδ, hgb, -⟩ := location_aux hm hσ hy hT hC2b hn hSn hVn hneg hg hgmem
  have : Nonempty (fractionRange m) := ⟨⟨0, h0mem⟩⟩
  have hsup : (⨆ l : fractionRange m, ∏ k ∈ range n, (1 + l * y k))
      = ∏ k ∈ range n, (1 + g * y k) :=
    le_antisymm (ciSup_le fun l ↦ isMaxOn_iff.1 hg l l.2)
      (le_ciSup (f := fun l : fractionRange m ↦ ∏ k ∈ range n, (1 + l * y k))
        ⟨_, by rintro _ ⟨l, rfl⟩; exact isMaxOn_iff.1 hg l l.2⟩ ⟨g, hgmem⟩)
  have hg2 : |g| < 1 / 2 := hgδ.trans_le hδ2
  obtain ⟨hFg, hlogg⟩ :=
    prod_one_add_mul_pos_and_log_eq (n := n) (fun k _ ↦ hy1 k) (hg2.trans (by norm_num))
  rw [hsup, Real.dist_eq, sub_zero, hlogg]
  -- the fraction `S_n / V_n`
  set S := ∑ k ∈ range n, y k with hS_def
  set V := ∑ k ∈ range n, y k ^ 2 with hV_def
  have hV2 := aux_V hσ hT hC2b hVn
  have hVpos : 0 < V := by
    have : 0 < t ^ 6 * σ2 / 2 + 2 * t ^ 4 := by positivity
    linarith
  have hlam : |S / V| ≤ 2 * C1 / σ2 * (b / t ^ 2) := by
    rw [abs_div, abs_of_pos hVpos, div_le_iff₀ hVpos]
    calc |S| ≤ C1 * b * t ^ 4 := hSn
      _ = 2 * C1 / σ2 * (b / t ^ 2) * (t ^ 6 * σ2 / 2) := by field_simp
      _ ≤ 2 * C1 / σ2 * (b / t ^ 2) * V := by gcongr; linarith [show 0 ≤ t ^ 4 by positivity]
  have hlam2 : |S / V| ≤ 1 / 2 := by
    refine hlam.trans ?_
    calc 2 * C1 / σ2 * (b / t ^ 2) ≤ 2 * C1 / σ2 * b := by
          gcongr; exact div_le_self hb0 ht1
      _ = 2 * (C1 * b) / σ2 := by ring
      _ ≤ 2 * (σ2 / 4) / σ2 := by gcongr
      _ = 1 / 2 := by field_simp; norm_num
  have hlammem : S / V ∈ fractionRange m := mem_fractionRange_of_abs_le hm (by linarith)
  obtain ⟨hFlam, hloglam⟩ :=
    prod_one_add_mul_pos_and_log_eq (n := n) (fun k _ ↦ hy1 k) (l := S / V) (by linarith)
  have hle : ∑ k ∈ range n, Real.log (1 + S / V * y k)
      ≤ ∑ k ∈ range n, Real.log (1 + g * y k) := by
    rw [← hloglam, ← hlogg]
    exact Real.log_le_log hFlam (isMaxOn_iff.1 hg _ hlammem)
  -- quadratic expansions
  have hqg := abs_le.1 (abs_sum_log_one_add_mul_sub_le (n := n) (fun k _ ↦ hy1 k) hg2.le)
  have hqlam := abs_le.1 (abs_sum_log_one_add_mul_sub_le (n := n) (fun k _ ↦ hy1 k) hlam2)
  have hup : g * S - g ^ 2 * V / 2 ≤ S ^ 2 / V / 2 := by
    rw [div_div, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (S - g * V)]
  have hlamval : S / V * S - (S / V) ^ 2 * V / 2 = S ^ 2 / V / 2 := by field_simp; ring
  -- the cubic remainders
  have hcube : ∀ x, |x| ≤ 2 * C1 / σ2 * (b / t ^ 2) →
      (n : ℝ) * |x| ^ 3 ≤ (2 * C1 / σ2) ^ 3 * b := by
    intro x hx
    rw [hn]
    calc t ^ 6 * |x| ^ 3 ≤ t ^ 6 * (2 * C1 / σ2 * (b / t ^ 2)) ^ 3 := by gcongr
      _ = (2 * C1 / σ2) ^ 3 * b ^ 3 := by field_simp
      _ ≤ (2 * C1 / σ2) ^ 3 * b := by
          gcongr; exact pow_le_of_le_one hb0 hb1 (by norm_num)
  have hcg := hcube g hgb
  have hclam := hcube _ hlam
  have hfin : 8 * ((2 * C1 / σ2) ^ 3 * b) < ε := by
    calc 8 * ((2 * C1 / σ2) ^ 3 * b) ≤ 8 * (2 * C1 / σ2) ^ 3 * (ε / (8 * (2 * C1 / σ2) ^ 3 + 1))
          := by rw [← mul_assoc]; gcongr
      _ < ε := mul_div_add_one_lt (by positivity) hε
  rw [abs_lt]
  constructor <;> linarith

end Asymptotics

/-! ### Betting forms -/

section Betting

variable {m σ2 : ℝ} {X : ℕ → Ω → ℝ} {ω : Ω}

/-- Observations in `[0, 1]`, centered at `m`, are in `[-m, 1 - m]`. -/
private lemma sub_mem_Icc (hX : ∀ k, X k ω ∈ Set.Icc 0 1) (k : ℕ) :
    X k ω - m ∈ Set.Icc (-m) (1 - m) :=
  ⟨by linarith [(hX k).1], by linarith [(hX k).2]⟩

/-- **Large bets lose in hindsight**, betting form: for observations `X k ω ∈ [0, 1]` with
`S_n = ∑_{k < n} (X k ω - m) = O(√n log n)` and `∑_{k < n} (X k ω - m)² - n σ² = O(√n log n)`,
for all large `n` the fixed fractions `l ∈ fractionRange m` with `|l| ≥ n ^ (-1/3)` have wealth
less than `1`. -/
lemma eventually_fixedWealth_lt_one (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hX : ∀ k, X k ω ∈ Set.Icc 0 1)
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    ∀ᶠ n : ℕ in atTop, ∀ l ∈ fractionRange m, (n : ℝ) ^ (-(1 / 3 : ℝ)) ≤ |l| →
      fixedWealth m l X n ω < 1 :=
  eventually_prod_one_add_mul_lt_one (y := fun k ↦ X k ω - m) hm hσ (sub_mem_Icc hX) hS hV

/-- **Location of the hindsight maximizers**, betting form: for observations `X k ω ∈ [0, 1]`
with `S_n = ∑_{k < n} (X k ω - m) = O(√n log n)` and
`V_n - n σ² = O(√n log n)` (`V_n = ∑_{k < n} (X k ω - m)²`), there is `K` such that for all large
`n`, every maximizer `g` of `l ↦ fixedWealth m l X n ω` on `fractionRange m` is in the interior
of the fraction range, with `|g| < n ^ (-1/3)`, `|g| ≤ K log n / √n` and
`|g - S_n / V_n| ≤ K log² n / n`. -/
lemma eventually_abs_le_of_isMaxOn_fixedWealth (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hX : ∀ k, X k ω ∈ Set.Icc 0 1)
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    ∃ K, ∀ᶠ n : ℕ in atTop, ∀ g,
      IsMaxOn (fun l ↦ fixedWealth m l X n ω) (fractionRange m) g → g ∈ fractionRange m →
        g ∈ interior (fractionRange m) ∧ |g| < (n : ℝ) ^ (-(1 / 3 : ℝ)) ∧
          |g| ≤ K * Real.log n / √n ∧
          |g - (∑ k ∈ range n, (X k ω - m)) / ∑ k ∈ range n, (X k ω - m) ^ 2|
            ≤ K * Real.log n ^ 2 / n :=
  eventually_abs_le_of_isMaxOn (y := fun k ↦ X k ω - m) hm hσ (sub_mem_Icc hX) hS hV

/-- **Location of the hindsight maximizers**, betting form: for observations `X k ω ∈ [0, 1]`
with `S_n = ∑_{k < n} (X k ω - m) = O(√n log n)` and
`V_n - n σ² = O(√n log n)` (`V_n = ∑_{k < n} (X k ω - m)²`), there is `K` such that for all large
`n`, every maximizer `g` of `l ↦ fixedWealth m l X n ω` on `fractionRange m` satisfies
`|g - S_n / V_n| ≤ K log² n / n`. -/
lemma eventually_abs_sub_div_le_of_isMaxOn_fixedWealth (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hX : ∀ k, X k ω ∈ Set.Icc 0 1)
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    ∃ K, ∀ᶠ n : ℕ in atTop, ∀ g,
      IsMaxOn (fun l ↦ fixedWealth m l X n ω) (fractionRange m) g → g ∈ fractionRange m →
        |g - (∑ k ∈ range n, (X k ω - m)) / ∑ k ∈ range n, (X k ω - m) ^ 2|
          ≤ K * Real.log n ^ 2 / n :=
  eventually_abs_sub_div_le_of_isMaxOn (y := fun k ↦ X k ω - m) hm hσ (sub_mem_Icc hX) hS hV

/-- **Value of the hindsight log-wealth**, betting form: for observations `X k ω ∈ [0, 1]` with
`S_n = ∑_{k < n} (X k ω - m) = O(√n log n)` and `V_n - n σ² = O(√n log n)`
(`V_n = ∑_{k < n} (X k ω - m)²`), `2 L*_n - S_n² / V_n → 0` for the best-in-hindsight
log-wealth `L*_n = hindsightLogWealth m X n ω`. -/
lemma tendsto_two_mul_hindsightLogWealth_sub (hm : m ∈ Set.Ioo 0 1) (hσ : 0 < σ2)
    (hX : ∀ k, X k ω ∈ Set.Icc 0 1)
    (hS : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m)) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
    (hV : (fun n : ℕ ↦ ∑ k ∈ range n, (X k ω - m) ^ 2 - n * σ2) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)) :
    Tendsto (fun n : ℕ ↦ 2 * hindsightLogWealth m X n ω
      - (∑ k ∈ range n, (X k ω - m)) ^ 2 / ∑ k ∈ range n, (X k ω - m) ^ 2) atTop (𝓝 0) :=
  tendsto_two_mul_log_iSup_sub (y := fun k ↦ X k ω - m) hm hσ (sub_mem_Icc hX) hS hV

end Betting

end Learning.Betting
