/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Wang2026Almost.Mathlib.Probability.AsymptoticsInProbability

/-!
# Almost sure divergence of series of nonnegative random variables that are `Ω_p` of a divergent
series

If `a n ≥ 0` with `∑ a n = ∞` and the almost surely nonnegative random variables `Z n` satisfy
`Z n = Ω_p(a n)`, then `∑ Z n = ∞` almost surely. For `a n = n⁻¹` this is Theorem 2.2 of Wang,
Agrawal, Ramdas (2026), "Almost sure null bankruptcy of testing-by-betting strategies".

The proof is a weighted version of the paper's (which uses Kronecker's lemma for the weights
`1 / n`): with `A k = {δ a k ≤ Z k}`, on `{∑ Z < ∞}` the series `∑ a k 𝟙_{A k}` converges while
`∑_{k < n} a k → ∞`, so the weighted proportion of failures
`U n = ∑_{k < n} a k 𝟙_{A kᶜ}` eventually exceeds half of `∑_{k < n} a k`; by Markov's inequality
this has probability at most about `2 ε`, and Fatou's lemma for sets concludes.

## Main statements

* `MeasureTheory.measure_liminf_atTop_le_liminf`: Fatou's lemma for sets,
  `μ (liminf s) ≤ liminf μ (s n)`;
* `ProbabilityTheory.ae_not_summable_of_isBigOmegaInProb`: `∑ Z n = ∞` almost surely.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology ENNReal

namespace MeasureTheory

/-- **Fatou's lemma for sets**: `μ (liminf s) ≤ liminf μ (s n)`, for any sets (measurable or
not). -/
lemma measure_liminf_atTop_le_liminf {α : Type*} {mα : MeasurableSpace α} (μ : Measure α)
    (s : ℕ → Set α) :
    μ (liminf s atTop) ≤ liminf (fun n ↦ μ (s n)) atTop := by
  rw [liminf_eq_iSup_iInf_of_nat, liminf_eq_iSup_iInf_of_nat]
  have h_mono : Monotone fun n ↦ ⨅ i ≥ n, s i :=
    fun m n hmn ↦ biInf_mono fun i hi ↦ hmn.trans hi
  simp only [Set.iSup_eq_iUnion] at h_mono ⊢
  rw [h_mono.measure_iUnion]
  exact iSup_mono fun n ↦ le_iInf₂ fun i hi ↦ measure_mono (biInf_le _ hi)

end MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {Z : ℕ → Ω → ℝ} {a : ℕ → ℝ}

/-- Version of `ae_not_summable_of_isBigOmegaInProb` for measurable random variables. -/
lemma ae_not_summable_of_isBigOmegaInProb_of_measurable (hZ : ∀ n, Measurable (Z n))
    (hnn : ∀ n, 0 ≤ᵐ[P] Z n) (ha : ∀ n, 0 ≤ a n) (ha_sum : ¬ Summable a)
    (hΩ : IsBigOmegaInProb P Z a) :
    ∀ᵐ ω ∂P, ¬ Summable (fun n ↦ Z n ω) := by
  rw [ae_iff]
  simp only [not_not]
  -- partial sums of the weights
  set S : ℕ → ℝ := fun n ↦ ∑ k ∈ Finset.range n, a k with hS_def
  have hS_tendsto : Tendsto S atTop atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg ha).1 ha_sum
  -- it suffices to bound `P(∑ Z < ∞)` by an arbitrary `η > 0`
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add fun η hη _ ↦ ?_) zero_le
  rw [zero_add]
  set ε : ℝ := η / 2 with hε_def
  obtain ⟨δ, hδ, hA⟩ := hΩ ε (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hA
  -- the events `A k = {δ a k ≤ |Z k|}` and the weighted count `U n` of their failures
  set A : ℕ → Set Ω := fun k ↦ {ω | δ * a k ≤ |Z k ω|} with hA_def
  have hA_meas : ∀ k, MeasurableSet (A k) := fun k ↦
    measurableSet_le measurable_const (by fun_prop)
  set U : ℕ → Ω → ℝ := fun n ω ↦ ∑ k ∈ Finset.range n, a k * (A k)ᶜ.indicator 1 ω with hU_def
  set B : ℕ → Set Ω := fun n ↦ {ω | S n / 2 ≤ U n ω} with hB_def
  -- on `{∑ Z < ∞}`, `ω ∈ B n` for all large `n`
  have h_sub : {ω | Summable (fun n ↦ Z n ω)} ≤ᵐ[P] liminf B atTop := by
    filter_upwards [ae_all_iff.2 hnn] with ω hω hsum
    change Summable (fun n ↦ Z n ω) at hsum
    rw [mem_liminf_iff_eventually_mem]
    set s : ℕ → ℝ := fun k ↦ a k * (A k).indicator 1 ω with hs_def
    have hs_nonneg : ∀ k, 0 ≤ s k := fun k ↦
      mul_nonneg (ha k) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
    -- `a k 𝟙_{A k} ≤ Z k / δ`, hence `∑ a k 𝟙_{A k} < ∞`
    have hs_sum : Summable s := by
      refine Summable.of_nonneg_of_le hs_nonneg (fun k ↦ ?_) (hsum.div_const δ)
      by_cases hk : ω ∈ A k
      · simp only [hs_def, Set.indicator_of_mem hk, Pi.one_apply, mul_one]
        have hk' : δ * a k ≤ Z k ω := by
          have := hk
          simp only [hA_def, Set.mem_ofPred_eq] at this
          rwa [abs_of_nonneg (hω k)] at this
        rw [le_div_iff₀ hδ]
        linarith
      · simp only [hs_def, Set.indicator_of_notMem hk, mul_zero]
        exact div_nonneg (hω k) hδ.le
    filter_upwards [hS_tendsto.eventually_ge_atTop (2 * ∑' k, s k)] with n hn
    have h_le : ∑ k ∈ Finset.range n, s k ≤ ∑' k, s k :=
      hs_sum.sum_le_tsum _ fun k _ ↦ hs_nonneg k
    have hU : U n ω = S n - ∑ k ∈ Finset.range n, s k := by
      simp only [hU_def, hS_def, hs_def, ← Finset.sum_sub_distrib, Set.indicator_compl]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      simp only [Pi.sub_apply, Pi.one_apply]
      ring
    change S n / 2 ≤ U n ω
    rw [hU]
    linarith
  -- Markov's inequality: `P(B n) ≤ 2 E[U n] / S n ≤ 2 S N / S n + 2 ε`
  have h_int : ∀ k, Integrable (fun ω ↦ a k * (A k)ᶜ.indicator 1 ω) P := fun k ↦
    ((integrable_const (1 : ℝ)).indicator (hA_meas k).compl).const_mul (a k)
  have hU_int : ∀ n, Integrable (U n) P := fun n ↦ integrable_finsetSum _ fun k _ ↦ h_int k
  have hU_nonneg : ∀ n ω, 0 ≤ U n ω := fun n ω ↦ Finset.sum_nonneg fun k _ ↦
    mul_nonneg (ha k) (Set.indicator_nonneg (fun _ _ ↦ zero_le_one) _)
  have hU_integral : ∀ n, N ≤ n → ∫ ω, U n ω ∂P ≤ S N + ε * S n := by
    intro n hn
    simp only [hU_def]
    rw [integral_finsetSum _ fun k _ ↦ h_int k]
    simp_rw [integral_const_mul, integral_indicator_one (hA_meas _).compl,
      probReal_compl_eq_one_sub (hA_meas _)]
    rw [← Finset.sum_range_add_sum_Ico _ hn]
    gcongr
    · refine Finset.sum_le_sum fun k _ ↦ ?_
      have : P.real (A k) ≤ 1 := measureReal_le_one
      nlinarith [ha k, measureReal_nonneg (μ := P) (s := A k)]
    · calc ∑ k ∈ Finset.Ico N n, a k * (1 - P.real (A k))
          ≤ ∑ k ∈ Finset.Ico N n, ε * a k := by
            refine Finset.sum_le_sum fun k hk ↦ ?_
            have := hN k (Finset.mem_Ico.1 hk).1
            nlinarith [ha k]
        _ = ε * ∑ k ∈ Finset.Ico N n, a k := by rw [Finset.mul_sum]
        _ ≤ ε * S n := by
            gcongr
            exact Finset.sum_le_sum_of_subset_of_nonneg
              (fun k hk ↦ Finset.mem_range.2 (Finset.mem_Ico.1 hk).2) fun k _ _ ↦ ha k
  have hB_le : ∀ᶠ n in atTop, P (B n) ≤ ENNReal.ofReal (2 * (S N / S n) + 2 * ε) := by
    filter_upwards [eventually_ge_atTop N, hS_tendsto.eventually_gt_atTop 0] with n hn hSn
    rw [← ofReal_measureReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := (mul_meas_ge_le_integral_of_nonneg (ae_of_all _ (hU_nonneg n)) (hU_int n)
      (S n / 2)).trans (hU_integral n hn)
    calc P.real (B n) ≤ (S N + ε * S n) / (S n / 2) := by
          rw [le_div_iff₀ (by positivity)]
          linarith
      _ = 2 * (S N / S n) + 2 * ε := by field_simp
  have h_lim : Tendsto (fun n ↦ ENNReal.ofReal (2 * (S N / S n) + 2 * ε)) atTop
      (𝓝 (ENNReal.ofReal (2 * 0 + 2 * ε))) :=
    ENNReal.tendsto_ofReal (((tendsto_const_nhds.div_atTop hS_tendsto).const_mul 2).add
      tendsto_const_nhds)
  -- Fatou's lemma for sets
  calc P {ω | Summable (fun n ↦ Z n ω)} ≤ P (liminf B atTop) := measure_mono_ae h_sub
    _ ≤ liminf (fun n ↦ P (B n)) atTop := measure_liminf_atTop_le_liminf P B
    _ ≤ liminf (fun n ↦ ENNReal.ofReal (2 * (S N / S n) + 2 * ε)) atTop :=
        liminf_le_liminf hB_le
    _ = ENNReal.ofReal (2 * 0 + 2 * ε) := h_lim.liminf_eq
    _ = η := by
        rw [hε_def, mul_zero, zero_add, mul_div_cancel₀ _ two_ne_zero, ENNReal.ofReal_coe_nnreal]

/-- **Almost sure divergence of `∑ Ω_p(a n)`** (Wang, Agrawal, Ramdas 2026, Theorem 2.2 for
`a n = n⁻¹`): if `a n ≥ 0` with `∑ a n = ∞`, and the almost surely nonnegative random variables
`Z n` satisfy `Z n = Ω_p(a n)`, then `∑ Z n = ∞` almost surely. -/
lemma ae_not_summable_of_isBigOmegaInProb (hZ : ∀ n, AEMeasurable (Z n) P)
    (hnn : ∀ n, 0 ≤ᵐ[P] Z n) (ha : ∀ n, 0 ≤ a n) (ha_sum : ¬ Summable a)
    (hΩ : IsBigOmegaInProb P Z a) :
    ∀ᵐ ω ∂P, ¬ Summable (fun n ↦ Z n ω) := by
  have h := ae_not_summable_of_isBigOmegaInProb_of_measurable (Z := fun n ↦ (hZ n).mk (Z n))
    (fun n ↦ (hZ n).measurable_mk)
    (fun n ↦ by filter_upwards [hnn n, (hZ n).ae_eq_mk] with ω h1 h2 using h2 ▸ h1) ha ha_sum
    (hΩ.congr_ae fun n ↦ (hZ n).ae_eq_mk)
  filter_upwards [h, ae_all_iff.2 fun n ↦ (hZ n).ae_eq_mk] with ω hω hω'
  simpa [hω'] using hω

end ProbabilityTheory
