/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Martingale.IndepIncrements
public import Wang2026Almost.Mathlib.Probability.Martingale.Nonneg
public import Mathlib.Probability.Moments.SubGaussian

/-!
# Weighted sums of sub-Gaussian increments

Let `ℱ` be a filtration and `Y` a real process with independent increments along `ℱ`: `Y n` is
`ℱ (n + 1)`-measurable and independent of `ℱ n`. Suppose moreover that each `Y n` is
`c`-sub-Gaussian, and let `w` be an adapted process (the weights). We study the weighted sums
`T n = ∑ k < n, w k * Y k`, with quadratic variation `A n = ∑ k < n, w k ^ 2`.

## Main statements

* `ProbabilityTheory.supermartingale_exp_sum_mul`: for every `t`,
  `exp (t * T n - c * t ^ 2 * A n / 2)` is a supermartingale;
* `ProbabilityTheory.ae_exists_tendsto_sum_mul`: almost surely, if `∑ w n ^ 2 < ∞` then `T n`
  converges;
* `ProbabilityTheory.ae_forall_abs_sum_mul_le`: almost surely, for every `ε > 0` there is `C` with
  `|T n| ≤ C + ε * A n` for all `n`.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {Y w : ℕ → Ω → ℝ} {c : ℝ≥0}
  (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
  (hindep : ∀ n, Indep (MeasurableSpace.comap (Y n) inferInstance) (ℱ n) μ)
  (hsubG : ∀ n, HasSubgaussianMGF (Y n) c μ) (hw : Adapted ℱ w)

include hY hindep hsubG hw

/-- **Exponential supermartingale.** If `Y` has independent `c`-sub-Gaussian increments along `ℱ`
and `w` is adapted, then for every `t : ℝ`,
`n ↦ exp (t * ∑ k < n, w k * Y k - c * t ^ 2 * (∑ k < n, w k ^ 2) / 2)` is a supermartingale. -/
lemma supermartingale_exp_sum_mul (t : ℝ) :
    Supermartingale (fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) ℱ μ := by
  set U : ℕ → Ω → ℝ := fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2) with hU_def
  have hYm : ∀ n, Measurable (Y n) := fun n ↦ (hY n).mono (ℱ.le _) le_rfl
  have hU_adapted : Adapted ℱ U := by
    intro n
    have hT : Measurable[ℱ n] (fun ω ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω) := by
      refine Finset.measurable_fun_sum _ fun k hk ↦ ?_
      have hk : k + 1 ≤ n := Finset.mem_range.1 hk
      exact (hw.measurable_le (by omega)).mul ((hY k).mono (ℱ.mono hk) le_rfl)
    have hA : Measurable[ℱ n] (fun ω ↦ ∑ k ∈ Finset.range n, w k ω ^ 2) := by
      refine Finset.measurable_fun_sum _ fun k hk ↦ ?_
      exact (hw.measurable_le (Finset.mem_range.1 hk).le).pow_const 2
    exact ((hT.const_mul t).sub ((hA.const_mul (c * t ^ 2)).div_const 2)).exp
  refine supermartingale_of_lintegral_le (Z := fun n ω ↦ (U n ω, w n ω)) (Y := Y)
    (Φ := fun n p ↦ ENNReal.ofReal
      (p.1.1 * Real.exp (t * p.1.2 * p.2 - c * t ^ 2 * p.1.2 ^ 2 / 2)))
    hU_adapted (fun n ↦ ae_of_all _ fun ω ↦ (Real.exp_pos _).le) ?_
    (fun n ↦ (hU_adapted n).prodMk (hw n)) hYm hindep (fun n ↦ by fun_prop) ?_ ?_
  · simp [hU_def]
  · intro n
    refine ae_of_all _ fun ω ↦ ?_
    congr 1
    simp only [hU_def, Finset.sum_range_succ]
    rw [← Real.exp_add]
    congr 1
    ring
  · intro n
    refine ae_of_all _ fun ω ↦ ?_
    dsimp only
    set u := U n ω
    set z := w n ω
    have hu : 0 < u := Real.exp_pos _
    clear_value u z
    have h_eq : ∀ y, u * Real.exp (t * z * y - c * t ^ 2 * z ^ 2 / 2)
        = u * Real.exp (-(c * (t * z) ^ 2 / 2)) * Real.exp ((t * z) * y) := fun y ↦ by
      rw [mul_assoc u, ← Real.exp_add]
      congr 2
      ring
    have hint : Integrable
        (fun ω' ↦ u * Real.exp (-(c * (t * z) ^ 2 / 2)) * Real.exp ((t * z) * Y n ω')) μ :=
      ((hsubG n).integrable_exp_mul (t * z)).const_mul _
    simp only [h_eq]
    rw [lintegral_map (by fun_prop) (hYm n), ← ofReal_integral_eq_lintegral_ofReal hint
      (ae_of_all _ fun _ ↦ by positivity), integral_const_mul]
    refine ENNReal.ofReal_le_ofReal ?_
    calc u * Real.exp (-(c * (t * z) ^ 2 / 2)) * ∫ ω', Real.exp ((t * z) * Y n ω') ∂μ
        ≤ u * Real.exp (-(c * (t * z) ^ 2 / 2)) * Real.exp (c * (t * z) ^ 2 / 2) := by
          gcongr
          exact (hsubG n).mgf_le (t * z)
      _ = u := by rw [mul_assoc u, ← Real.exp_add]; simp

/-- Almost surely, the exponential supermartingale `exp (t * T n - c * t ^ 2 * A n / 2)` of
`supermartingale_exp_sum_mul` converges to a finite limit. -/
lemma ae_exists_tendsto_exp_sum_mul (t : ℝ) :
    ∀ᵐ ω ∂μ, ∃ L, Tendsto (fun n ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) atTop (𝓝 L) := by
  obtain ⟨L, -, hL, -⟩ :=
    (supermartingale_exp_sum_mul hY hindep hsubG hw t).exists_ae_tendsto_of_nonneg
      fun n ↦ ae_of_all _ fun ω ↦ (Real.exp_pos _).le
  filter_upwards [hL] with ω hω using ⟨L ω, hω⟩

omit hY hindep hsubG hw [IsProbabilityMeasure μ] in
/-- If `exp (t * x n - c * t ^ 2 * a n / 2)` converges for some `t > 0`, then `x n` is bounded
above by `C + c * t * a n / 2` for some constant `C`. -/
private lemma exists_le_add_of_tendsto_exp {x a : ℕ → ℝ} {t L : ℝ} (ht : 0 < t)
    (h : Tendsto (fun n ↦ Real.exp (t * x n - c * t ^ 2 * a n / 2)) atTop (𝓝 L)) :
    ∃ C, ∀ n, x n ≤ C + c * t * a n / 2 := by
  obtain ⟨K, hK⟩ := h.bddAbove_range
  have hK_pos : 0 < K := (Real.exp_pos _).trans_le (hK ⟨0, rfl⟩)
  refine ⟨Real.log K / t, fun n ↦ ?_⟩
  have h1 : t * x n - c * t ^ 2 * a n / 2 ≤ Real.log K :=
    (Real.le_log_iff_exp_le hK_pos).2 (hK ⟨n, rfl⟩)
  rw [div_add' _ _ _ ht.ne', le_div_iff₀ ht]
  nlinarith

/-- **Convergence on finite quadratic variation.** If `Y` has independent `c`-sub-Gaussian
increments along `ℱ` and `w` is adapted, then almost surely, if `∑ n, w n ^ 2 < ∞` then
`∑ k < n, w k * Y k` converges. -/
lemma ae_exists_tendsto_sum_mul :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ w n ω ^ 2) →
      ∃ T, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω) atTop (𝓝 T) := by
  filter_upwards [ae_exists_tendsto_exp_sum_mul hY hindep hsubG hw 1,
    ae_exists_tendsto_exp_sum_mul hY hindep hsubG hw (-1)] with ω ⟨Lp, hLp⟩ ⟨Lm, hLm⟩ hsum
  set T : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω with hT_def
  set A : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, w k ω ^ 2 with hA_def
  set A' : ℝ := ∑' n, w n ω ^ 2 with hA'_def
  have hA : Tendsto A atTop (𝓝 A') := hsum.hasSum.tendsto_sum_nat
  have hA_le : ∀ n, A n ≤ A' := fun n ↦ hsum.sum_le_tsum _ fun k _ ↦ sq_nonneg _
  have h1 : ∀ n, Real.exp (T n)
      = Real.exp (1 * T n - c * 1 ^ 2 * A n / 2) * Real.exp (c * A n / 2) := fun n ↦ by
    rw [← Real.exp_add]; congr 1; ring
  have hm1 : ∀ n, Real.exp (-T n)
      = Real.exp (-1 * T n - c * (-1) ^ 2 * A n / 2) * Real.exp (c * A n / 2) := fun n ↦ by
    rw [← Real.exp_add]; congr 1; ring
  have hexp : Tendsto (fun n ↦ Real.exp (T n)) atTop (𝓝 (Lp * Real.exp (c * A' / 2))) := by
    simp_rw [h1]
    exact hLp.mul ((Real.continuous_exp.tendsto _).comp ((hA.const_mul _).div_const 2))
  obtain ⟨K, hK⟩ := hLm.bddAbove_range
  have hK_pos : 0 < K := (Real.exp_pos _).trans_le (hK ⟨0, rfl⟩)
  have hpos : 0 < K * Real.exp (c * A' / 2) := mul_pos hK_pos (Real.exp_pos _)
  have hlow : ∀ n, (K * Real.exp (c * A' / 2))⁻¹ ≤ Real.exp (T n) := by
    intro n
    have h2 : Real.exp (-T n) ≤ K * Real.exp (c * A' / 2) := by
      rw [hm1]
      gcongr
      · exact hK ⟨n, rfl⟩
      · exact hA_le n
    calc (K * Real.exp (c * A' / 2))⁻¹ ≤ (Real.exp (-T n))⁻¹ := inv_anti₀ (Real.exp_pos _) h2
      _ = Real.exp (T n) := by rw [Real.exp_neg, inv_inv]
  have hL_pos : 0 < Lp * Real.exp (c * A' / 2) :=
    (inv_pos.2 hpos).trans_le (ge_of_tendsto' hexp hlow)
  refine ⟨Real.log (Lp * Real.exp (c * A' / 2)), ?_⟩
  simpa [Real.log_exp] using hexp.log hL_pos.ne'

/-- **Little-`o` on infinite quadratic variation.** If `Y` has independent `c`-sub-Gaussian
increments along `ℱ` and `w` is adapted, then almost surely, for every `ε > 0` there is `C` with
`|∑ k < n, w k * Y k| ≤ C + ε * ∑ k < n, w k ^ 2` for all `n`. -/
lemma ae_forall_abs_sum_mul_le :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ Finset.range n, w k ω * Y k ω|
      ≤ C + ε * ∑ k ∈ Finset.range n, w k ω ^ 2 := by
  have hp := fun j : ℕ ↦ ae_exists_tendsto_exp_sum_mul hY hindep hsubG hw (1 / (j + 1))
  have hm := fun j : ℕ ↦ ae_exists_tendsto_exp_sum_mul hY hindep hsubG hw (-(1 / (j + 1)))
  filter_upwards [ae_all_iff.2 hp, ae_all_iff.2 hm] with ω hp hm ε hε
  set T : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω with hT_def
  set A : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, w k ω ^ 2 with hA_def
  have hA_nonneg : ∀ n, 0 ≤ A n := fun n ↦ Finset.sum_nonneg fun k _ ↦ sq_nonneg _
  obtain ⟨j, hj⟩ := exists_nat_gt (c / (2 * ε))
  set t : ℝ := 1 / (j + 1) with ht_def
  have ht : 0 < t := by positivity
  have hct : c * t / 2 ≤ ε := by
    rw [ht_def, div_le_iff₀ two_pos, mul_one_div, div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hj
    nlinarith
  obtain ⟨Lp, hLp⟩ := hp j
  obtain ⟨Lm, hLm⟩ := hm j
  obtain ⟨C₁, hC₁⟩ := exists_le_add_of_tendsto_exp (x := T) (a := A) ht hLp
  have hLm' : Tendsto (fun n ↦ Real.exp (t * (-T n) - c * t ^ 2 * A n / 2)) atTop (𝓝 Lm) := by
    convert hLm using 3 with n
    ring
  obtain ⟨C₂, hC₂⟩ := exists_le_add_of_tendsto_exp (x := fun n ↦ -T n) (a := A) ht hLm'
  refine ⟨max C₁ C₂, fun n ↦ ?_⟩
  have h3 : c * t * A n / 2 ≤ ε * A n := by
    rw [mul_div_right_comm]
    exact mul_le_mul_of_nonneg_right hct (hA_nonneg n)
  rw [abs_le]
  constructor
  · linarith [hC₂ n, le_max_right C₁ C₂]
  · linarith [hC₁ n, le_max_left C₁ C₂]

end ProbabilityTheory
