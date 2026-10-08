/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Probability.Independence.Basic

/-!
# Freezing lemma

If `Y` is independent of a sub-σ-algebra `m` and `Z` is `m`-measurable, then integrating a
function of `(Z, Y)` over a set of `m` amounts to first integrating out `Y` with `Z` frozen:
`∫⁻ ω in A, Φ (Z ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, Φ (Z ω, y) ∂(μ.map Y) ∂μ`.

## Main statements

* `ProbabilityTheory.setLIntegral_comp_of_indep`: the freezing lemma for nonnegative functions,
  integrated over a set `A` of the sub-σ-algebra.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω E F : Type*} {m mΩ : MeasurableSpace Ω} {mE : MeasurableSpace E}
  {mF : MeasurableSpace F} {μ : Measure Ω}

/-- **Freezing lemma**: if `Y` is independent of a sub-σ-algebra `m` and `Z` is `m`-measurable,
then for every measurable `Φ ≥ 0` and every `A ∈ m`,
`∫⁻ ω in A, Φ (Z ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, Φ (Z ω, y) ∂(μ.map Y) ∂μ`. -/
lemma setLIntegral_comp_of_indep [IsProbabilityMeasure μ] (hm : m ≤ mΩ) {Z : Ω → E} {Y : Ω → F}
    (hZ : Measurable[m] Z) (hY : Measurable Y)
    (hindep : Indep (MeasurableSpace.comap Y mF) m μ) {Φ : E × F → ℝ≥0∞} (hΦ : Measurable Φ)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, Φ (Z ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, Φ (Z ω, y) ∂(μ.map Y) ∂μ := by
  set I : Ω → ℝ≥0∞ := A.indicator 1 with hI_def
  have hI : Measurable[m] I := (measurable_const (a := (1 : ℝ≥0∞))).indicator hA
  have hZI : Measurable[m] (fun ω ↦ (Z ω, I ω)) := hZ.prodMk hI
  have hZI' : Measurable (fun ω ↦ (Z ω, I ω)) := hZI.mono hm le_rfl
  have h_indep : IndepFun (fun ω ↦ (Z ω, I ω)) Y μ := by
    rw [IndepFun_iff_Indep]
    exact (indep_of_indep_of_le_right hindep hZI.comap_le).symm
  have h_map := (indepFun_iff_map_prod_eq_prod_map_map hZI'.aemeasurable hY.aemeasurable).1
    h_indep
  have hG : Measurable (fun p : (E × ℝ≥0∞) × F ↦ p.1.2 * Φ (p.1.1, p.2)) := by fun_prop
  have h_ind (f : Ω → ℝ≥0∞) : ∫⁻ ω in A, f ω ∂μ = ∫⁻ ω, I ω * f ω ∂μ := by
    rw [← lintegral_indicator (hm _ hA)]
    congr with ω
    by_cases hω : ω ∈ A <;> simp [hI_def, hω]
  calc ∫⁻ ω in A, Φ (Z ω, Y ω) ∂μ
      = ∫⁻ ω, I ω * Φ (Z ω, Y ω) ∂μ := h_ind _
    _ = ∫⁻ p, p.1.2 * Φ (p.1.1, p.2) ∂(μ.map (fun ω ↦ ((Z ω, I ω), Y ω))) := by
        rw [lintegral_map hG (hZI'.prodMk hY)]
    _ = ∫⁻ x, ∫⁻ y, x.2 * Φ (x.1, y) ∂(μ.map Y) ∂(μ.map (fun ω ↦ (Z ω, I ω))) := by
        rw [h_map, lintegral_prod _ hG.aemeasurable]
    _ = ∫⁻ ω, I ω * ∫⁻ y, Φ (Z ω, y) ∂(μ.map Y) ∂μ := by
        rw [lintegral_map hG.lintegral_prod_right' hZI']
        congr with ω
        rw [lintegral_const_mul _ (by fun_prop)]
    _ = ∫⁻ ω in A, ∫⁻ y, Φ (Z ω, y) ∂(μ.map Y) ∂μ := (h_ind _).symm

end ProbabilityTheory
