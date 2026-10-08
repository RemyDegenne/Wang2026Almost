/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Moments.Basic
public import Wang2026Almost.Mathlib.Probability.Distributions.Gamma

/-!
# The chi-squared distribution

The chi-squared distribution with `k` degrees of freedom is the gamma distribution with shape
`k / 2` and rate `1 / 2`, and this is how it is defined here on top of Mathlib's
`ProbabilityTheory.gammaMeasure` (the way `expMeasure` is defined as `gammaMeasure 1 r`).
That it is the law of the squared norm of a standard Gaussian vector in dimension `k` is
`map_norm_sq_stdGaussian_eq_chiSquareMeasure`, in
`ForMathlib/Probability/Distributions/Gaussian/ChiSquare.lean`.

## Main definitions

* `chiSquarePDFReal k`: the function
  `x ↦ x ^ (k / 2 - 1) * exp (-x / 2) / (2 ^ (k / 2) * Gamma (k / 2))` for `0 ≤ x` and `0` else,
  the probability density function of the chi-squared distribution with `k` degrees of freedom;
* `chiSquarePDF k`: its `ℝ≥0∞`-valued version;
* `chiSquareMeasure k`: the chi-squared distribution with `k` degrees of freedom.

## Main statements

* `isProbabilityMeasure_chiSquareMeasure`: it is a probability measure for `k ≠ 0`;
* `mgf_chiSquareMeasure`: its moment generating function is `(1 - 2t) ^ (-k/2)` for `t < 1/2`.
-/

@[expose] public section

open MeasureTheory Real Set
open scoped ENNReal

namespace ProbabilityTheory

section PDF

variable {k : ℕ} {x : ℝ}

/-- The pdf of the chi-squared distribution with `k` degrees of freedom. -/
noncomputable def chiSquarePDFReal (k : ℕ) (x : ℝ) : ℝ := gammaPDFReal (k / 2) (1 / 2) x

/-- The pdf of the chi-squared distribution with `k` degrees of freedom, as a function valued in
`ℝ≥0∞`. -/
noncomputable def chiSquarePDF (k : ℕ) (x : ℝ) : ℝ≥0∞ := gammaPDF (k / 2) (1 / 2) x

/-- `chiSquarePDF` is the `ℝ≥0∞`-valued version of `chiSquarePDFReal`. -/
lemma chiSquarePDF_eq (k : ℕ) (x : ℝ) :
    chiSquarePDF k x = ENNReal.ofReal (chiSquarePDFReal k x) := rfl

lemma chiSquarePDFReal_of_neg (hx : x < 0) : chiSquarePDFReal k x = 0 := by
  simp [chiSquarePDFReal, gammaPDFReal, not_le.2 hx]

lemma chiSquarePDF_of_neg (hx : x < 0) : chiSquarePDF k x = 0 := gammaPDF_of_neg hx

/-- The usual formula for the chi-squared pdf on `[0, ∞)`. -/
lemma chiSquarePDFReal_of_nonneg (hx : 0 ≤ x) :
    chiSquarePDFReal k x
      = x ^ ((k : ℝ) / 2 - 1) * exp (-x / 2) / (2 ^ ((k : ℝ) / 2) * Gamma (k / 2)) := by
  rw [chiSquarePDFReal, gammaPDFReal, ite_eq_left hx, Real.div_rpow zero_le_one (by norm_num),
    Real.one_rpow, show -((1 : ℝ) / 2 * x) = -x / 2 by ring]
  ring

@[fun_prop]
lemma measurable_chiSquarePDFReal (k : ℕ) : Measurable (chiSquarePDFReal k) :=
  measurable_gammaPDFReal _ _

/-- The chi-squared pdf is nonnegative. -/
lemma chiSquarePDFReal_nonneg (hk : k ≠ 0) (x : ℝ) : 0 ≤ chiSquarePDFReal k x :=
  gammaPDFReal_nonneg (by positivity) (by norm_num) x

/-- The chi-squared pdf integrates to `1`. -/
lemma lintegral_chiSquarePDF_eq_one (hk : k ≠ 0) : ∫⁻ x, chiSquarePDF k x = 1 :=
  lintegral_gammaPDF_eq_one (by positivity) (by norm_num)

end PDF

/-- The chi-squared distribution with `k` degrees of freedom: the gamma distribution with shape
`k / 2` and rate `1 / 2`. -/
noncomputable def chiSquareMeasure (k : ℕ) : Measure ℝ := gammaMeasure ((k : ℝ) / 2) (1 / 2)

lemma chiSquareMeasure_def (k : ℕ) : chiSquareMeasure k = gammaMeasure ((k : ℝ) / 2) (1 / 2) :=
  rfl

/-- The chi-squared distribution has density `chiSquarePDF k` with respect to the Lebesgue
measure. -/
lemma chiSquareMeasure_eq_withDensity (k : ℕ) :
    chiSquareMeasure k = volume.withDensity (chiSquarePDF k) := rfl

/-- The chi-squared distribution with `k ≠ 0` degrees of freedom is a probability measure. -/
lemma isProbabilityMeasure_chiSquareMeasure {k : ℕ} (hk : k ≠ 0) :
    IsProbabilityMeasure (chiSquareMeasure k) :=
  isProbabilityMeasure_gammaMeasure (by positivity) (by norm_num)

instance (k : ℕ) [NeZero k] : IsProbabilityMeasure (chiSquareMeasure k) :=
  isProbabilityMeasure_chiSquareMeasure (NeZero.ne k)

section CDF

/-- The cdf of the chi-squared distribution is the integral of its pdf. -/
lemma cdf_chiSquareMeasure_eq_integral {k : ℕ} (hk : k ≠ 0) (x : ℝ) :
    cdf (chiSquareMeasure k) x = ∫ y in Iic x, chiSquarePDFReal k y :=
  cdf_gammaMeasure_eq_integral (by positivity) (by norm_num) x

/-- The cdf of the chi-squared distribution, as the lower integral of its pdf. -/
lemma cdf_chiSquareMeasure_eq_lintegral {k : ℕ} (hk : k ≠ 0) (x : ℝ) :
    cdf (chiSquareMeasure k) x = (∫⁻ y in Iic x, chiSquarePDF k y).toReal :=
  cdf_gammaMeasure_eq_lintegral (by positivity) (by norm_num) x

end CDF

/-- The moment generating function of the chi-squared distribution with `k` degrees of freedom:
`(1 - 2t) ^ (-k/2)` for `t < 1/2`. -/
lemma mgf_chiSquareMeasure {k : ℕ} (hk : k ≠ 0) {t : ℝ} (ht : t < 1 / 2) :
    mgf id (chiSquareMeasure k) t = (1 - 2 * t) ^ (-(k : ℝ) / 2) := by
  have h1 : (0 : ℝ) < 1 - 2 * t := by linarith
  rw [mgf, chiSquareMeasure]
  simp_rw [id]
  rw [integral_exp_mul_gammaMeasure (by positivity) (by norm_num) (by linarith)]
  rw [show (1 : ℝ) / 2 / (1 / 2 - t) = (1 - 2 * t)⁻¹ by field_simp,
    Real.inv_rpow h1.le, ← Real.rpow_neg h1.le]
  congr 1
  ring

end ProbabilityTheory
