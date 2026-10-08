/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.Probability.Moments.Variance

/-!
# Null distributions of the bounded mean testing problem

A *null distribution* for the test of the mean `m` is a probability measure `P` on `[0, 1]` with
mean `m`; it is *non-degenerate* if `P ≠ δ_m`. Non-degeneracy is equivalent to a positive
variance, and it forces `m ∈ (0, 1)`.

## Main statements

* `eq_dirac_of_ae_eq`: a probability measure concentrated at a point is the Dirac mass there;
* `variance_pos_of_ne_dirac`, `ne_dirac_of_variance_pos`: for a null distribution,
  `P ≠ δ_m ↔ 0 < Var[id; P]`;
* `mem_Ioo_of_ne_dirac`, `mem_Ioo_of_variance_pos`: a non-degenerate null distribution has its
  mean in `(0, 1)`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning.Betting

variable {P : Measure ℝ} [IsProbabilityMeasure P] {m : ℝ}

/-- A probability measure on `ℝ` under which `x = c` almost surely is the Dirac mass at `c`. -/
lemma eq_dirac_of_ae_eq {c : ℝ} (h : ∀ᵐ x ∂P, x = c) : P = Measure.dirac c := by
  have h1 : P.map id = P.map (fun _ ↦ c) := Measure.map_congr h
  rwa [Measure.map_id, Measure.map_const, measure_univ, one_smul] at h1

/-- A probability measure on `[0, 1]` is square integrable. -/
lemma memLp_two_id_of_mem_Icc (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) : MemLp id 2 P := by
  refine MemLp.of_bound aestronglyMeasurable_id 1 ?_
  filter_upwards [hP] with x hx
  simp only [id_eq, Real.norm_eq_abs]
  exact abs_le.2 ⟨by linarith [hx.1], hx.2⟩

/-- For a non-degenerate null distribution, the variance is positive. -/
lemma variance_pos_of_ne_dirac (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) : 0 < Var[id; P] := by
  refine (variance_nonneg _ _).lt_of_ne fun h ↦ hnd ?_
  have h' := ae_eq_integral_of_variance_eq_zero (memLp_two_id_of_mem_Icc hP) h.symm
  refine eq_dirac_of_ae_eq ?_
  filter_upwards [h'] with x hx
  simpa [hm] using hx

/-- A null distribution with positive variance is non-degenerate. -/
lemma ne_dirac_of_variance_pos (hvar : 0 < Var[id; P]) : P ≠ Measure.dirac m := by
  rintro rfl
  simp [variance_dirac] at hvar

/-- A non-degenerate distribution on `[0, 1]` has its mean in `(0, 1)`. -/
lemma mem_Ioo_of_ne_dirac (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hnd : P ≠ Measure.dirac m) : m ∈ Set.Ioo 0 1 := by
  have hint : Integrable (fun x : ℝ ↦ x) P := (memLp_two_id_of_mem_Icc hP).integrable one_le_two
  have h0 : 0 ≤ m := hm ▸ integral_nonneg_of_ae (hP.mono fun x hx ↦ hx.1)
  have h1 : m ≤ 1 := by
    rw [← hm]
    calc ∫ x, x ∂P ≤ ∫ _, (1 : ℝ) ∂P := integral_mono_ae hint (integrable_const _)
            (hP.mono fun x hx ↦ hx.2)
      _ = 1 := by simp
  refine ⟨h0.lt_of_ne fun h ↦ hnd ?_, h1.lt_of_ne fun h ↦ hnd ?_⟩
  · -- `m = 0`: `x = 0` almost surely
    have hx : (fun x : ℝ ↦ x) =ᵐ[P] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae (hP.mono fun x hx ↦ hx.1) hint).1 (h ▸ hm)
    refine eq_dirac_of_ae_eq ?_
    filter_upwards [hx] with x hx
    simpa [← h] using hx
  · -- `m = 1`: `1 - x = 0` almost surely
    have hint' : Integrable (fun x : ℝ ↦ 1 - x) P := (integrable_const _).sub hint
    have hx : (fun x : ℝ ↦ 1 - x) =ᵐ[P] 0 := by
      refine (integral_eq_zero_iff_of_nonneg_ae (hP.mono fun x hx ↦ ?_) hint').1 ?_
      · simpa using hx.2
      · rw [integral_sub (integrable_const _) hint, hm, h]
        simp
    refine eq_dirac_of_ae_eq ?_
    filter_upwards [hx] with x hx
    simp only [Pi.zero_apply, sub_eq_zero] at hx
    rw [h, hx]

/-- A distribution on `[0, 1]` with positive variance has its mean in `(0, 1)`. -/
lemma mem_Ioo_of_variance_pos (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1) (hm : ∫ x, x ∂P = m)
    (hvar : 0 < Var[id; P]) : m ∈ Set.Ioo 0 1 :=
  mem_Ioo_of_ne_dirac hP hm (ne_dirac_of_variance_pos hvar)

end Learning.Betting
