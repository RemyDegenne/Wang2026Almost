/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Moments.Variance
public import Mathlib.Probability.Moments.SubGaussian
public import Wang2026Almost.Mathlib.Probability.HasLaw

/-!
# Null distributions of the bounded mean testing problem

A *null distribution* for the test of the mean `m` is a probability measure `P` on `[0, 1]` with
mean `m`; it is *non-degenerate* if `P ≠ δ_m`. Non-degeneracy is equivalent to a positive
variance, and it forces `m ∈ (0, 1)`.

## Main statements

* `mem_Icc_of_integral_eq`: the mean of a distribution on `[0, 1]` is in `[0, 1]`;
* `variance_pos_of_ne_dirac`, `ne_dirac_of_variance_pos`: for a null distribution,
  `P ≠ δ_m ↔ 0 < Var[id; P]`;
* `mem_Ioo_of_ne_dirac`, `mem_Ioo_of_variance_pos`: a non-degenerate null distribution has its
  mean in `(0, 1)`;
* `hasSubgaussianMGF_sub_of_mem_Icc`, `hasSubgaussianMGF_sq_sub_variance`: under a null
  distribution, `x - m` and `(x - m)² - σ²` are `1 / 4`-sub-Gaussian (Hoeffding's lemma).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace Learning.Betting

variable {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- The mean of a probability measure on `[0, 1]` is in `[0, 1]`. -/
lemma mem_Icc_of_integral_eq (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m) :
    m ∈ Set.Icc 0 1 :=
  hm ▸ integral_mem_Icc_of_ae_mem aemeasurable_id hP

/-- A distribution on `[0, 1]` has finite moments of all orders. -/
lemma memLp_id_of_mem_Icc (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (p : ℝ≥0∞) : MemLp id p P :=
  memLp_of_bounded hP aestronglyMeasurable_id p

/-- For a non-degenerate null distribution, the variance is positive. -/
lemma variance_pos_of_ne_dirac (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) : 0 < Var[id; P] := by
  refine (variance_nonneg _ _).lt_of_ne fun h ↦ hnd ?_
  have h' := ae_eq_integral_of_variance_eq_zero (memLp_id_of_mem_Icc hP 2) h.symm
  refine Measure.eq_dirac_of_ae_eq ?_
  filter_upwards [h'] with x hx
  simpa [hm] using hx

/-- A null distribution with positive variance is non-degenerate. -/
lemma ne_dirac_of_variance_pos (hvar : 0 < Var[id; P]) : P ≠ Measure.dirac m := by
  rintro rfl
  simp [variance_dirac] at hvar

/-- A non-degenerate distribution on `[0, 1]` has its mean in `(0, 1)`. -/
lemma mem_Ioo_of_ne_dirac (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) : m ∈ Set.Ioo 0 1 := by
  have hint : Integrable (fun x : ℝ ↦ x) P :=
    (memLp_id_of_mem_Icc hP 2).integrable one_le_two
  obtain ⟨h0, h1⟩ := mem_Icc_of_integral_eq hP hm
  refine ⟨h0.lt_of_ne fun h ↦ hnd ?_, h1.lt_of_ne fun h ↦ hnd ?_⟩
  · -- `m = 0`: `x = 0` almost surely
    have hx : (fun x : ℝ ↦ x) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (hP.mono fun x hx ↦ hx.1) hint).1 (h ▸ hm)
    refine Measure.eq_dirac_of_ae_eq ?_
    filter_upwards [hx] with x hx
    simpa [← h] using hx
  · -- `m = 1`: `1 - x = 0` almost surely
    have hint' : Integrable (fun x : ℝ ↦ 1 - x) P := (integrable_const _).sub hint
    have hx : (fun x : ℝ ↦ 1 - x) =ᵐ[P] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae (hP.mono fun x hx ↦ ?_) hint').1 ?_
      · simpa using hx.2
      · rw [integral_sub (integrable_const _) hint, hm, h]
        simp
    refine Measure.eq_dirac_of_ae_eq ?_
    filter_upwards [hx] with x hx
    simp only [Pi.zero_apply, sub_eq_zero] at hx
    rw [h, hx]

/-- A distribution on `[0, 1]` with positive variance has its mean in `(0, 1)`. -/
lemma mem_Ioo_of_variance_pos (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) : m ∈ Set.Ioo 0 1 :=
  mem_Ioo_of_ne_dirac hP hm (ne_dirac_of_variance_pos hvar)

/-- Under a null distribution on `[0, 1]` with mean `m`, `x - m` is `1 / 4`-sub-Gaussian
(Hoeffding's lemma). -/
lemma hasSubgaussianMGF_sub_of_mem_Icc (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) :
    HasSubgaussianMGF (fun x ↦ x - m) (1 / 4) P := by
  have hint : Integrable (fun x : ℝ ↦ x) P := (memLp_id_of_mem_Icc hP 2).integrable one_le_two
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (μ := P) (X := fun x ↦ x - m) (a := -m)
    (b := 1 - m) (by fun_prop) ?_ ?_
  · have hc : (‖(1 - m) - (-m)‖₊ / 2) ^ 2 = 1 / 4 := by norm_num
    rwa [hc] at h
  · filter_upwards [hP] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [integral_sub hint (integrable_const _), hm]
    simp

/-- Under a null distribution on `[0, 1]` with mean `m`, `(x - m)² - Var[id; P]` is
`1 / 4`-sub-Gaussian (Hoeffding's lemma). -/
lemma hasSubgaussianMGF_sq_sub_variance (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) :
    HasSubgaussianMGF (fun x ↦ (x - m) ^ 2 - Var[id; P]) (1 / 4) P := by
  have hm01 := mem_Icc_of_integral_eq hP hm
  have hb : ∀ᵐ x ∂P, (x - m) ^ 2 ∈ Set.Icc (0 : ℝ) 1 := by
    filter_upwards [hP] with x hx
    refine ⟨sq_nonneg _, ?_⟩
    have h : |x - m| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hx.1, hx.2, hm01.1, hm01.2]
    simpa using sq_le_sq.2 (h.trans_eq abs_one.symm)
  have hint : Integrable (fun x : ℝ ↦ (x - m) ^ 2) P := Integrable.of_mem_Icc 0 1 (by fun_prop) hb
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (μ := P) (X := fun x ↦ (x - m) ^ 2 - Var[id; P]) (a := -Var[id; P]) (b := 1 - Var[id; P])
    (by fun_prop) ?_ ?_
  · have hc : (‖(1 - Var[id; P]) - (-Var[id; P])‖₊ / 2) ^ 2 = 1 / 4 := by norm_num
    rwa [hc] at h
  · filter_upwards [hb] with x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  · rw [integral_sub hint (integrable_const _), variance_eq_integral aemeasurable_id]
    simp [hm]

end Learning.Betting
