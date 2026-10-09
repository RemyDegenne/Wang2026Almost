/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Martingale.IndepIncrements
public import Wang2026Almost.Mathlib.Probability.Martingale.Nonneg
public import Wang2026Almost.Mathlib.Probability.Moments.SubGaussian

/-!
# Weighted sums of conditionally sub-Gaussian increments

Let `ℱ` be a filtration, `Y` a real process with `Y n` `ℱ (n + 1)`-measurable and conditionally
`c`-sub-Gaussian given `ℱ n` (a sub-Gaussian martingale difference sequence), and `w` an adapted
process (the weights). We study the weighted sums `T n = ∑ k < n, w k * Y k`, with quadratic
variation `A n = ∑ k < n, w k ^ 2`: a strong law of large numbers for martingales with
conditionally sub-Gaussian increments.

All the results follow from the moment bound at `ℱ n`-measurable parameters `s`: for every
`ℱ n`-measurable `g ≥ 0`, `∫⁻ g * exp (s * Y n) ≤ ∫⁻ g * exp (c * s ^ 2 / 2)` (the results with
suffix `_of_lintegral_le`). It holds when `Y n` is conditionally sub-Gaussian
(`HasCondSubgaussianMGF`, which needs a standard Borel space), and when `Y n` is sub-Gaussian and
independent of `ℱ n`, on any measurable space (suffix `_of_indep`).

## Main statements

* `ProbabilityTheory.supermartingale_exp_sum_mul`: for every `t`,
  `exp (t * T n - c * t ^ 2 * A n / 2)` is a supermartingale;
* `ProbabilityTheory.ae_exists_tendsto_sum_mul`: almost surely, if `∑ w n ^ 2 < ∞` then `T n`
  converges;
* `ProbabilityTheory.ae_forall_abs_sum_mul_le`: almost surely, for every `ε > 0` there is `C` with
  `|T n| ≤ C + ε * A n` for all `n`;
* `ProbabilityTheory.supermartingale_exp_sum_mul_of_indep`,
  `ProbabilityTheory.ae_exists_tendsto_sum_mul_of_indep`,
  `ProbabilityTheory.ae_forall_abs_sum_mul_le_of_indep`: the same for independent increments.
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ mΩ} {Y w : ℕ → Ω → ℝ} {c : ℝ≥0}

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

section MomentBound

variable (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n)) (hw : Adapted ℱ w)
  (hmgf : ∀ n (s : Ω → ℝ) (g : Ω → ℝ≥0∞), Measurable[ℱ n] s → Measurable[ℱ n] g →
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (s ω * Y n ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (c * s ω ^ 2 / 2)) ∂μ)

include hY hw hmgf

/-- **Exponential supermartingale**, under the moment bound at `ℱ n`-measurable parameters: for
every `t : ℝ`, `n ↦ exp (t * ∑ k < n, w k * Y k - c * t ^ 2 * (∑ k < n, w k ^ 2) / 2)` is a
supermartingale. -/
lemma supermartingale_exp_sum_mul_of_lintegral_le (t : ℝ) :
    Supermartingale (fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) ℱ μ := by
  set U : ℕ → Ω → ℝ := fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2) with hU_def
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
  refine supermartingale_of_setLIntegral_succ_le hU_adapted
    (fun n ↦ ae_of_all _ fun ω ↦ (Real.exp_pos _).le) (by simp [hU_def]) fun n A hA ↦ ?_
  -- the `ℱ n`-measurable factor, with the parameter `s = t * w n`
  set g : Ω → ℝ≥0∞ := A.indicator fun ω ↦
    ENNReal.ofReal (U n ω * Real.exp (-(c * (t * w n ω) ^ 2 / 2))) with hg_def
  have hs : Measurable[ℱ n] (fun ω ↦ t * w n ω) := (hw n).const_mul t
  have hg : Measurable[ℱ n] g :=
    ((hU_adapted n).mul ((((hs.pow_const 2).const_mul c).div_const 2).neg.exp)).ennreal_ofReal
      |>.indicator hA
  have h_succ : ∀ ω, A.indicator (fun ω ↦ ENNReal.ofReal (U (n + 1) ω)) ω
      = g ω * ENNReal.ofReal (Real.exp ((t * w n ω) * Y n ω)) := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg_def, Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
      congr 1
      simp only [hU_def, Finset.sum_range_succ, ← Real.exp_add]
      congr 1
      ring
    · simp [hg_def, hω]
  have h_n : ∀ ω, g ω * ENNReal.ofReal (Real.exp (c * (t * w n ω) ^ 2 / 2))
      = A.indicator (fun ω ↦ ENNReal.ofReal (U n ω)) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · simp only [hg_def, Set.indicator_of_mem hω]
      rw [← ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le), mul_assoc,
        ← Real.exp_add]
      simp [hU_def]
    · simp [hg_def, hω]
  rw [← lintegral_indicator (ℱ.le n _ hA), ← lintegral_indicator (ℱ.le n _ hA)]
  simp_rw [h_succ, ← h_n]
  exact hmgf n (fun ω ↦ t * w n ω) g hs hg

/-- Almost surely, the exponential supermartingale `exp (t * T n - c * t ^ 2 * A n / 2)` of
`supermartingale_exp_sum_mul_of_lintegral_le` converges to a finite limit. -/
lemma ae_exists_tendsto_exp_sum_mul_of_lintegral_le (t : ℝ) :
    ∀ᵐ ω ∂μ, ∃ L, Tendsto (fun n ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) atTop (𝓝 L) := by
  obtain ⟨L, -, hL, -⟩ :=
    (supermartingale_exp_sum_mul_of_lintegral_le hY hw hmgf t).exists_ae_tendsto_of_nonneg
      fun n ↦ ae_of_all _ fun ω ↦ (Real.exp_pos _).le
  filter_upwards [hL] with ω hω using ⟨L ω, hω⟩

/-- **Convergence on finite quadratic variation**, under the moment bound at `ℱ n`-measurable
parameters: almost surely, if `∑ n, w n ^ 2 < ∞` then `∑ k < n, w k * Y k` converges. -/
lemma ae_exists_tendsto_sum_mul_of_lintegral_le :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ w n ω ^ 2) →
      ∃ T, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω) atTop (𝓝 T) := by
  filter_upwards [ae_exists_tendsto_exp_sum_mul_of_lintegral_le hY hw hmgf 1,
    ae_exists_tendsto_exp_sum_mul_of_lintegral_le hY hw hmgf (-1)] with ω ⟨Lp, hLp⟩ ⟨Lm, hLm⟩ hsum
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

/-- **Little-`o` on infinite quadratic variation**, under the moment bound at `ℱ n`-measurable
parameters: almost surely, for every `ε > 0` there is `C` with
`|∑ k < n, w k * Y k| ≤ C + ε * ∑ k < n, w k ^ 2` for all `n`. -/
lemma ae_forall_abs_sum_mul_le_of_lintegral_le :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ Finset.range n, w k ω * Y k ω|
      ≤ C + ε * ∑ k ∈ Finset.range n, w k ω ^ 2 := by
  have hp := fun j : ℕ ↦ ae_exists_tendsto_exp_sum_mul_of_lintegral_le hY hw hmgf (1 / (j + 1))
  have hm := fun j : ℕ ↦ ae_exists_tendsto_exp_sum_mul_of_lintegral_le hY hw hmgf (-(1 / (j + 1)))
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

end MomentBound

section Indep

variable (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
  (hindep : ∀ n, Indep (MeasurableSpace.comap (Y n) inferInstance) (ℱ n) μ)
  (hsubG : ∀ n, HasSubgaussianMGF (Y n) c μ) (hw : Adapted ℱ w)

include hY hindep hsubG hw

omit hw in
/-- The moment bound at `ℱ n`-measurable parameters for independent sub-Gaussian increments. -/
lemma lintegral_mul_exp_le_of_indep (n : ℕ) (s : Ω → ℝ) (g : Ω → ℝ≥0∞)
    (hs : Measurable[ℱ n] s) (hg : Measurable[ℱ n] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (s ω * Y n ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (c * s ω ^ 2 / 2)) ∂μ :=
  (hsubG n).lintegral_mul_exp_le_of_indep (ℱ.le n) ((hY n).mono (ℱ.le _) le_rfl) (hindep n) hs hg

/-- **Exponential supermartingale, independent increments.** If `Y` has independent
`c`-sub-Gaussian increments along `ℱ` and `w` is adapted, then for every `t : ℝ`,
`n ↦ exp (t * ∑ k < n, w k * Y k - c * t ^ 2 * (∑ k < n, w k ^ 2) / 2)` is a supermartingale. -/
lemma supermartingale_exp_sum_mul_of_indep (t : ℝ) :
    Supermartingale (fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) ℱ μ :=
  supermartingale_exp_sum_mul_of_lintegral_le hY hw
    (lintegral_mul_exp_le_of_indep hY hindep hsubG) t

/-- **Convergence on finite quadratic variation, independent increments.** If `Y` has independent
`c`-sub-Gaussian increments along `ℱ` and `w` is adapted, then almost surely, if
`∑ n, w n ^ 2 < ∞` then `∑ k < n, w k * Y k` converges. -/
lemma ae_exists_tendsto_sum_mul_of_indep :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ w n ω ^ 2) →
      ∃ T, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω) atTop (𝓝 T) :=
  ae_exists_tendsto_sum_mul_of_lintegral_le hY hw
    (lintegral_mul_exp_le_of_indep hY hindep hsubG)

/-- **Little-`o` on infinite quadratic variation, independent increments.** If `Y` has
independent `c`-sub-Gaussian increments along `ℱ` and `w` is adapted, then almost surely, for
every `ε > 0` there is `C` with `|∑ k < n, w k * Y k| ≤ C + ε * ∑ k < n, w k ^ 2` for all `n`. -/
lemma ae_forall_abs_sum_mul_le_of_indep :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ Finset.range n, w k ω * Y k ω|
      ≤ C + ε * ∑ k ∈ Finset.range n, w k ω ^ 2 :=
  ae_forall_abs_sum_mul_le_of_lintegral_le hY hw
    (lintegral_mul_exp_le_of_indep hY hindep hsubG)

end Indep

section Conditional

variable [StandardBorelSpace Ω] (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
  (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (Y n) c μ) (hw : Adapted ℱ w)

include hY hsubG hw

omit hw in
/-- The moment bound at `ℱ n`-measurable parameters for conditionally sub-Gaussian increments. -/
lemma lintegral_mul_exp_le_of_hasCondSubgaussianMGF (n : ℕ) (s : Ω → ℝ) (g : Ω → ℝ≥0∞)
    (hs : Measurable[ℱ n] s) (hg : Measurable[ℱ n] g) :
    ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (s ω * Y n ω)) ∂μ
      ≤ ∫⁻ ω, g ω * ENNReal.ofReal (Real.exp (c * s ω ^ 2 / 2)) ∂μ :=
  (hsubG n).lintegral_mul_exp_le ((hY n).mono (ℱ.le _) le_rfl) hs hg

/-- **Exponential supermartingale.** If `Y n` is `ℱ (n + 1)`-measurable and conditionally
`c`-sub-Gaussian given `ℱ n`, and `w` is adapted, then for every `t : ℝ`,
`n ↦ exp (t * ∑ k < n, w k * Y k - c * t ^ 2 * (∑ k < n, w k ^ 2) / 2)` is a supermartingale. -/
lemma supermartingale_exp_sum_mul (t : ℝ) :
    Supermartingale (fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) ℱ μ :=
  supermartingale_exp_sum_mul_of_lintegral_le hY hw
    (lintegral_mul_exp_le_of_hasCondSubgaussianMGF hY hsubG) t

/-- **Convergence on finite quadratic variation.** If `Y n` is `ℱ (n + 1)`-measurable and
conditionally `c`-sub-Gaussian given `ℱ n`, and `w` is adapted, then almost surely, if
`∑ n, w n ^ 2 < ∞` then `∑ k < n, w k * Y k` converges. -/
lemma ae_exists_tendsto_sum_mul :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ w n ω ^ 2) →
      ∃ T, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω) atTop (𝓝 T) :=
  ae_exists_tendsto_sum_mul_of_lintegral_le hY hw
    (lintegral_mul_exp_le_of_hasCondSubgaussianMGF hY hsubG)

/-- **Little-`o` on infinite quadratic variation.** If `Y n` is `ℱ (n + 1)`-measurable and
conditionally `c`-sub-Gaussian given `ℱ n`, and `w` is adapted, then almost surely, for every
`ε > 0` there is `C` with `|∑ k < n, w k * Y k| ≤ C + ε * ∑ k < n, w k ^ 2` for all `n`. -/
lemma ae_forall_abs_sum_mul_le :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ Finset.range n, w k ω * Y k ω|
      ≤ C + ε * ∑ k ∈ Finset.range n, w k ω ^ 2 :=
  ae_forall_abs_sum_mul_le_of_lintegral_le hY hw
    (lintegral_mul_exp_le_of_hasCondSubgaussianMGF hY hsubG)

end Conditional

end ProbabilityTheory
