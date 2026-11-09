/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Landau notation in probability and almost surely

For a sequence of real random variables `X n` on a measure space `(Ω, P)` and a sequence of
nonrandom numbers `a n` (Mathlib has the deterministic `Asymptotics.IsBigO` and the convergence in
probability `MeasureTheory.TendstoInMeasure`, but no stochastic Landau notation).

## Main definitions

* `IsBigOInProb P X a` (`X n = O_p(a n)`): for every `ε > 0` there is `M > 0` such that
  `P(|X n| ≤ M a n) ≥ 1 - ε` for all but finitely many `n`;
* `IsBigOmegaInProb P X a` (`X n = Ω_p(a n)`): for every `ε > 0` there is `δ > 0` such that
  `P(|X n| ≥ δ a n) ≥ 1 - ε` for all but finitely many `n`;
* `IsBigOAE P X a` (`X n = O_{a.s.}(a n)`) and `IsBigOmegaAE P X a` (`X n = Ω_{a.s.}(a n)`): the
  pathwise events `X n = O(a n)` and `X n = Ω(a n)` (that is, `a n = O(X n)`) happen `P`-almost
  surely.

## Main statements

* `IsBigOmegaInProb.mono`, `IsBigOmegaInProb.sq`, `IsBigOmegaInProb.comp_tendsto`,
  `IsBigOmegaInProb.congr_ae`: `Ω_p` is preserved by decreasing the rate up to a constant,
  squaring, reindexing along a sequence tending to infinity and almost sure equality;
* `isBigOmegaInProb_of_tendstoInDistribution`: if `X n / a n` converges in distribution to a
  limit without atom at `0` (and `a n > 0`), then `X n = Ω_p(a n)`.
-/

@[expose] public section

open Filter MeasureTheory Asymptotics
open scoped Topology

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω)

/-- `X n = O_p(a n)`: for every `ε > 0` there is `M > 0` such that `P(|X n| ≤ M a n) ≥ 1 - ε`
for all but finitely many `n`. -/
def IsBigOInProb (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ M : ℝ, 0 < M ∧ ∀ᶠ n in atTop, 1 - ε ≤ P.real {ω | |X n ω| ≤ M * a n}

/-- `X n = Ω_p(a n)`: for every `ε > 0` there is `δ > 0` such that `P(|X n| ≥ δ a n) ≥ 1 - ε`
for all but finitely many `n`. -/
def IsBigOmegaInProb (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop, 1 - ε ≤ P.real {ω | δ * a n ≤ |X n ω|}

/-- `X n = O_{a.s.}(a n)`: almost surely, the path `n ↦ X n ω` is `O(a n)`. -/
def IsBigOAE (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, (fun n ↦ X n ω) =O[atTop] a

/-- `X n = Ω_{a.s.}(a n)`: almost surely, the path `n ↦ X n ω` is `Ω(a n)`, that is
`a n = O(X n ω)`. -/
def IsBigOmegaAE (X : ℕ → Ω → ℝ) (a : ℕ → ℝ) : Prop :=
  ∀ᵐ ω ∂P, a =O[atTop] (fun n ↦ X n ω)

section Lemmas

variable {P} {X Y : ℕ → Ω → ℝ} {a b : ℕ → ℝ}

/-- `Ω_p` is preserved by a smaller rate: if `X n = Ω_p(a n)` and eventually `b n ≤ K a n` with
`K > 0`, then `X n = Ω_p(b n)`. -/
lemma IsBigOmegaInProb.mono [IsFiniteMeasure P] (h : IsBigOmegaInProb P X a) {K : ℝ}
    (hK : 0 < K) (hab : ∀ᶠ n in atTop, b n ≤ K * a n) : IsBigOmegaInProb P X b := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  refine ⟨δ / K, div_pos hδ hK, ?_⟩
  filter_upwards [h, hab] with n hn hn'
  refine hn.trans (measureReal_mono fun ω hω ↦ ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  calc δ / K * b n ≤ δ / K * (K * a n) := by gcongr
    _ = δ * a n := by field_simp
    _ ≤ |X n ω| := hω

/-- Squaring: if `X n = Ω_p(a n)` with `a n ≥ 0` eventually, then `X n ^ 2 = Ω_p(a n ^ 2)`. -/
lemma IsBigOmegaInProb.sq [IsFiniteMeasure P] (h : IsBigOmegaInProb P X a)
    (ha : ∀ᶠ n in atTop, 0 ≤ a n) :
    IsBigOmegaInProb P (fun n ω ↦ X n ω ^ 2) (fun n ↦ a n ^ 2) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  refine ⟨δ ^ 2, by positivity, ?_⟩
  filter_upwards [h, ha] with n hn hn'
  refine hn.trans (measureReal_mono fun ω hω ↦ ?_)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [abs_of_nonneg (sq_nonneg _), ← mul_pow, ← sq_abs (X n ω)]
  exact pow_le_pow_left₀ (by positivity) hω 2

/-- Reindexing: if `X n = Ω_p(a n)` and `f n → ∞`, then `X (f n) = Ω_p(a (f n))`. -/
lemma IsBigOmegaInProb.comp_tendsto (h : IsBigOmegaInProb P X a) {f : ℕ → ℕ}
    (hf : Tendsto f atTop atTop) :
    IsBigOmegaInProb P (fun n ↦ X (f n)) (fun n ↦ a (f n)) := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  exact ⟨δ, hδ, hf.eventually h⟩

/-- `Ω_p` only depends on the almost sure classes of the random variables. -/
lemma IsBigOmegaInProb.congr_ae (h : IsBigOmegaInProb P X a) (hXY : ∀ n, X n =ᵐ[P] Y n) :
    IsBigOmegaInProb P Y a := by
  intro ε hε
  obtain ⟨δ, hδ, h⟩ := h ε hε
  refine ⟨δ, hδ, h.mono fun n hn ↦ hn.trans_eq (measureReal_congr ?_)⟩
  filter_upwards [hXY n] with ω hω
  simp [hω]

/-- If `a n > 0` eventually and `X n / a n` converges in distribution to a random variable `Z`
with `P(Z = 0) = 0`, then `X n = Ω_p(a n)`: by the portmanteau theorem for the closed sets
`[-δ, δ]`, `limsup P(|X n / a n| ≤ δ) ≤ P(|Z| ≤ δ)`, which is small for small `δ`. -/
lemma isBigOmegaInProb_of_tendstoInDistribution [IsProbabilityMeasure P] {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → ℝ}
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (h : TendstoInDistribution (fun n ω ↦ X n ω / a n) atTop Z (fun _ ↦ P) μ')
    (hZ : μ' (Z ⁻¹' {0}) = 0) : IsBigOmegaInProb P X a := by
  intro ε hε
  -- the law of `Z` gives a small mass to small intervals around `0`
  set ν : Measure ℝ := μ'.map Z with hν
  have hν0 : ν {0} = 0 := by
    rw [hν, Measure.map_apply_of_aemeasurable h.aemeasurable_limit (measurableSet_singleton 0)]
    exact hZ
  have h_tendsto : Tendsto (fun k : ℕ ↦ ν (Set.Icc (-(1 / (k + 1 : ℝ))) (1 / (k + 1))))
      atTop (𝓝 (ν {0})) := by
    have h_inter : ⋂ k : ℕ, Set.Icc (-(1 / (k + 1 : ℝ))) (1 / (k + 1)) = {0} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_Icc, Set.mem_singleton_iff]
      refine ⟨fun hx ↦ le_antisymm ?_ ?_, fun hx k ↦ ?_⟩
      · refine le_of_forall_pos_lt_add fun η hη ↦ ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
        linarith [(hx k).2]
      · refine le_of_forall_pos_lt_add fun η hη ↦ ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hη
        linarith [(hx k).1]
      · subst hx
        exact ⟨by rw [neg_nonpos]; positivity, by positivity⟩
    rw [← h_inter]
    refine tendsto_measure_iInter_atTop (fun k ↦ measurableSet_Icc.nullMeasurableSet)
      (fun k l hkl ↦ Set.Icc_subset_Icc ?_ ?_) ⟨0, measure_ne_top _ _⟩ <;> gcongr
  rw [hν0] at h_tendsto
  obtain ⟨k, hk⟩ := (h_tendsto.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))).exists
  set δ : ℝ := 1 / (k + 1) with hδ_def
  refine ⟨δ, by positivity, ?_⟩
  -- portmanteau theorem for the closed set `[-δ, δ]`
  have h_limsup := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto h.tendsto
    (isClosed_Icc (a := -δ) (b := δ))
  simp only [ProbabilityMeasure.coe_mk] at h_limsup
  have h_ev : ∀ᶠ n in atTop, P.map (fun ω ↦ X n ω / a n) (Set.Icc (-δ) δ) < ENNReal.ofReal ε :=
    eventually_lt_of_limsup_lt (h_limsup.trans_lt hk)
  filter_upwards [h_ev, ha] with n hn han
  rw [Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) measurableSet_Icc] at hn
  have h_union : Set.univ
      ⊆ {ω | δ * a n ≤ |X n ω|} ∪ (fun ω ↦ X n ω / a n) ⁻¹' Set.Icc (-δ) δ := by
    intro ω _
    by_cases hω : δ * a n ≤ |X n ω|
    · exact Or.inl hω
    · refine Or.inr ?_
      simp only [Set.mem_preimage, Set.mem_Icc, ← abs_le]
      rw [abs_div, abs_of_pos han, div_le_iff₀ han]
      exact (not_le.1 hω).le
  have h1 : 1 ≤ P.real {ω | δ * a n ≤ |X n ω|}
      + P.real ((fun ω ↦ X n ω / a n) ⁻¹' Set.Icc (-δ) δ) :=
    calc (1 : ℝ) = P.real Set.univ := by simp
      _ ≤ P.real ({ω | δ * a n ≤ |X n ω|} ∪ (fun ω ↦ X n ω / a n) ⁻¹' Set.Icc (-δ) δ) :=
        measureReal_mono h_union
      _ ≤ _ := measureReal_union_le _ _
  have h2 : P.real ((fun ω ↦ X n ω / a n) ⁻¹' Set.Icc (-δ) δ) < ε :=
    ENNReal.toReal_lt_of_lt_ofReal hn
  linarith

/-- If `√n X n` converges in distribution to a random variable `Z` with `P(Z = 0) = 0`, then
`X n = Ω_p(n^{-1/2})`. -/
lemma isBigOmegaInProb_rpow_of_tendstoInDistribution_sqrt_mul [IsProbabilityMeasure P]
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {Z : Ω' → ℝ} (h : TendstoInDistribution (fun (n : ℕ) ω ↦ √n * X n ω) atTop Z (fun _ ↦ P) μ')
    (hZ : μ' (Z ⁻¹' {0}) = 0) : IsBigOmegaInProb P X (fun n ↦ (n : ℝ) ^ (-1 / 2 : ℝ)) := by
  refine isBigOmegaInProb_of_tendstoInDistribution ?_ ?_ hZ
  · filter_upwards [eventually_gt_atTop 0] with n hn
    exact Real.rpow_pos_of_pos (by exact_mod_cast hn) _
  · refine h.congr (fun n ↦ ae_of_all _ fun ω ↦ ?_) (ae_of_all _ fun _ ↦ rfl)
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    change √(n : ℝ) * X n ω = X n ω / (n : ℝ) ^ (-1 / 2 : ℝ)
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hn'.le, div_inv_eq_mul,
      Real.sqrt_eq_rpow, mul_comm]

end Lemmas

end ProbabilityTheory
