/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.Mathlib.Probability.Independence.Freezing
public import Mathlib.Probability.Martingale.Basic

/-!
# Supermartingales driven by independent increments

Let `ℱ` be a filtration and `V` an adapted, almost surely nonnegative process. Suppose that
`V (n + 1) = Φ n (Z n, Y n)`, where `Z n` is `ℱ n`-measurable, `Y n` is independent of `ℱ n`
and `Φ n ≥ 0`, and that integrating out `Y n` with `Z n` frozen gives at most `V n`. Then `V` is
a supermartingale.

## Main statements

* `MeasureTheory.supermartingale_of_setLIntegral_succ_le`: a nonnegative adapted process whose
  set integrals over `s ∈ ℱ n` do not increase from `n` to `n + 1` is a supermartingale;
* `MeasureTheory.supermartingale_of_lintegral_le`: the criterion above.
-/

@[expose] public section

open ProbabilityTheory
open scoped ENNReal

namespace MeasureTheory

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
  {mF : MeasurableSpace F} {μ : Measure Ω}

/-- An adapted, almost surely nonnegative process `V` with `V 0` integrable, such that
`∫⁻ ω in s, V (n + 1) ω ∂μ ≤ ∫⁻ ω in s, V n ω ∂μ` for every `s ∈ ℱ n`, is a supermartingale. -/
lemma supermartingale_of_setLIntegral_succ_le [IsFiniteMeasure μ] {ℱ : Filtration ℕ mΩ}
    {V : ℕ → Ω → ℝ} (hV : Adapted ℱ V) (hV_nonneg : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV0 : Integrable (V 0) μ)
    (hle : ∀ n, ∀ s, MeasurableSet[ℱ n] s →
      ∫⁻ ω in s, ENNReal.ofReal (V (n + 1) ω) ∂μ ≤ ∫⁻ ω in s, ENNReal.ofReal (V n ω) ∂μ) :
    Supermartingale V ℱ μ := by
  have hVm : ∀ n, Measurable (V n) := fun n ↦ (hV n).mono (ℱ.le n) le_rfl
  have hfin : ∀ n, ∫⁻ ω, ENNReal.ofReal (V n ω) ∂μ < ∞ := by
    intro n
    induction n with
    | zero => exact (hasFiniteIntegral_iff_ofReal (hV_nonneg 0)).1 hV0.2
    | succ n ih =>
      refine lt_of_le_of_lt ?_ ih
      simpa using hle n Set.univ MeasurableSet.univ
  have hint : ∀ n, Integrable (V n) μ := fun n ↦
    ⟨(hVm n).aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (hV_nonneg n)).2 (hfin n)⟩
  refine supermartingale_of_setIntegral_succ_le (fun n ↦ (hV n).stronglyMeasurable) hint ?_
  intro n s hs
  rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae (hV_nonneg (n + 1)))
      (hVm (n + 1)).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_ae (hV_nonneg n))
      (hVm n).aestronglyMeasurable]
  exact ENNReal.toReal_mono ((setLIntegral_le_lintegral _ _).trans_lt (hfin n)).ne (hle n s hs)

/-- **Supermartingales with independent increments.** Let `V` be an adapted, a.s. nonnegative
process with `V 0` integrable. Suppose that for each `n`, `V (n + 1) = Φ n (Z n, Y n)` a.s.,
where `Z n` is `ℱ n`-measurable, `Y n` is measurable and independent of `ℱ n`, `Φ n ≥ 0` is
measurable, and `∫⁻ y, Φ n (Z n, y) ∂(μ.map (Y n)) ≤ V n` a.s. Then `V` is a supermartingale. -/
lemma supermartingale_of_lintegral_le [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {V : ℕ → Ω → ℝ} (hV : Adapted ℱ V) (hV_nonneg : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV0 : Integrable (V 0) μ) {Z : ℕ → Ω → E} {Y : ℕ → Ω → F}
    (hZ : ∀ n, Measurable[ℱ n] (Z n)) (hY : ∀ n, Measurable (Y n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (Y n) mF) (ℱ n) μ)
    {Φ : ℕ → E × F → ℝ≥0∞} (hΦ : ∀ n, Measurable (Φ n))
    (hrec : ∀ n, ∀ᵐ ω ∂μ, ENNReal.ofReal (V (n + 1) ω) = Φ n (Z n ω, Y n ω))
    (hle : ∀ n, ∀ᵐ ω ∂μ, ∫⁻ y, Φ n (Z n ω, y) ∂(μ.map (Y n)) ≤ ENNReal.ofReal (V n ω)) :
    Supermartingale V ℱ μ := by
  refine supermartingale_of_setLIntegral_succ_le hV hV_nonneg hV0 fun n s hs ↦ ?_
  calc ∫⁻ ω in s, ENNReal.ofReal (V (n + 1) ω) ∂μ
      = ∫⁻ ω in s, Φ n (Z n ω, Y n ω) ∂μ := lintegral_congr_ae (ae_restrict_of_ae (hrec n))
    _ = ∫⁻ ω in s, ∫⁻ y, Φ n (Z n ω, y) ∂(μ.map (Y n)) ∂μ :=
        setLIntegral_comp_of_indep (ℱ.le n) (hZ n) (hY n) (hindep n) (hΦ n) hs
    _ ≤ ∫⁻ ω in s, ENNReal.ofReal (V n ω) ∂μ := lintegral_mono_ae (ae_restrict_of_ae (hle n))

end MeasureTheory
