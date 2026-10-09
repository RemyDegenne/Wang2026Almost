/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Wang2026Almost.LeanMachineLearning.Betting.Domination
public import Wang2026Almost.LeanMachineLearning.Betting.SumSquaresSubgaussian
public import Wang2026Almost.Mathlib.Probability.Martingale.Mixture
public import Wang2026Almost.Mathlib.MeasureTheory.Integral.MixtureLimit

/-!
# Mixture strategies: the no-cash criterion

The mixture wealth `∫ F l n ∂π(l)` of a family of test processes `F l` indexed by a parameter `l`
(the bet fraction for testing by betting, the alternative mean for sub-Gaussian tests), such that
the parameter `c` (bet `0`, alternative `m`) gives the constant process `1`, converges almost
surely to `π({c})` as soon as

* the processes with `|l - c| ≥ ε` are uniformly dominated by a process tending to `0` (large
  bets: for testing by betting, `W^l_n ≤ max (W^ε_n, W^{-ε}_n)` once both are `≤ 1`, and the
  fixed-fraction wealths `W^{±ε}_n` tend to `0`);
* the mixture over `0 < |l - c| < ε` converges almost surely to a limit of expectation at most
  `π(0 < |l - c| < ε)` (small bets: a mixture of nonnegative supermartingales is a nonnegative
  supermartingale).

Indeed, with `ε_j = 1 / (j + 1)`, the mixture converges to `π({c}) + L_j` for every `j`, and the
common value `L_j` has expectation at most `π(0 < |l - c| < ε_j) → 0`. This replaces the law of
the iterated logarithm used in the paper (Theorems 3.1 and 5.3 of Wang, Agrawal, Ramdas 2026).

The abstract criterion is `MeasureTheory.ae_tendsto_integral_of_ball`, and the small bets are
handled by `MeasureTheory.exists_ae_tendsto_setIntegral_of_supermartingale`.

## Main statements

* `ae_exists_bound_fixedWealth_of_le_abs`, `exists_ae_tendsto_setIntegral_fixedWealth`: large and
  small bets for testing by betting on i.i.d. observations;
* `ae_exists_bound_subgaussianTest_of_le_abs`, `exists_ae_tendsto_setIntegral_subgaussianTest`:
  the same for sub-Gaussian test processes;
* `ae_tendsto_subgaussianMixtureTest_of_hasCondSubgaussianMGF`: the no-cash criterion for
  sub-Gaussian mixture test processes when `X n - m` is conditionally `1`-sub-Gaussian given
  `ℱ n` (Theorem 5.3 of Wang, Agrawal, Ramdas 2026 without independence).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal

namespace Learning.Betting

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section Measurability

/-- The wealth of the fixed fraction `g l` is jointly measurable in `(l, ω)` for every
`σ`-algebra on `Ω` for which the first `n` observations are measurable. -/
lemma measurable_fixedWealth_prod {Λ : Type*} {mΛ : MeasurableSpace Λ} {m : ℝ}
    {X : ℕ → Ω → ℝ} {n : ℕ} (hX : ∀ k < n, Measurable (X k)) {g : Λ → ℝ} (hg : Measurable g) :
    Measurable (fun p : Λ × Ω ↦ fixedWealth m (g p.1) X n p.2) := by
  unfold fixedWealth wealth
  exact Finset.measurable_prod _ fun k hk ↦ measurable_const.add
    ((hg.comp measurable_fst).mul (((hX k (mem_range.1 hk)).comp measurable_snd).sub_const m))

/-- The sub-Gaussian test process of the constant alternative `l` is jointly measurable in
`(l, ω)` for every `σ`-algebra on `Ω` for which the first `n` observations are measurable. -/
lemma measurable_subgaussianTest_prod {m : ℝ} {X : ℕ → Ω → ℝ} {n : ℕ}
    (hX : ∀ k < n, Measurable (X k)) :
    Measurable (fun p : ℝ × Ω ↦ subgaussianTest m (fun _ _ ↦ p.1) X n p.2) := by
  unfold subgaussianTest
  refine Measurable.exp (Finset.measurable_sum _ fun k hk ↦ ?_)
  have h : Measurable (fun p : ℝ × Ω ↦ X k p.2) := (hX k (mem_range.1 hk)).comp measurable_snd
  exact (((h.sub_const m).pow_const 2).sub ((h.sub measurable_fst).pow_const 2)).div_const _

end Measurability

section Betting

variable {P' : Measure Ω} [IsProbabilityMeasure P'] {P : Measure ℝ} [IsProbabilityMeasure P]
  {m : ℝ} {X : ℕ → Ω → ℝ}

/-- For a finite measure `π` concentrated on `fractionRange m`, the fixed-fraction wealth after
`n` rounds is `π`-integrable in the fraction (it is continuous in the fraction). -/
lemma integrable_fixedWealth {π : Measure ℝ} [IsFiniteMeasure π]
    (hπ : ∀ᵐ l ∂π, l ∈ fractionRange m) (n : ℕ) (ω : Ω) :
    Integrable (fun l ↦ fixedWealth m l X n ω) π := by
  rw [← Measure.restrict_eq_self_of_ae_mem hπ]
  exact (continuous_fixedWealth m X n ω).continuousOn.integrableOn_compact isCompact_Icc

/-- **Large bets are dominated** (`lem:mixture_large`): for i.i.d. observations with a
non-degenerate law `P` on `[0, 1]` with mean `m` and `ε > 0` with `±ε ∈ fractionRange m`, almost
surely the wealths of the fixed fractions `l ∈ fractionRange m` with `|l| ≥ ε` are bounded, for
`n` large, by a sequence tending to `0` (namely `max (W^ε_n, W^{-ε}_n)`). -/
lemma ae_exists_bound_fixedWealth_of_le_abs (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hnd : P ≠ Measure.dirac m) (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P') {ε : ℝ} (hε : 0 < ε)
    (hεm : ε ∈ fractionRange m) (hεm' : -ε ∈ fractionRange m) :
    ∀ᵐ ω ∂P', ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ l ∈ fractionRange m,
      ε ≤ |l| → 0 ≤ fixedWealth m l X n ω ∧ fixedWealth m l X n ω ≤ G n := by
  have hm01 := mem_Ioo_of_ne_dirac hP hm hnd
  have hXI : ∀ k, ∀ᵐ ω ∂P', X k ω ∈ Set.Icc 0 1 := fun k ↦ by
    have h := hP
    rw [← (hlaw k).map_eq] at h
    exact ae_of_ae_map (hlaw k).aemeasurable h
  filter_upwards [ae_tendsto_fixedWealth_zero hP hm hnd hX hindep hlaw hεm hε.ne',
    ae_tendsto_fixedWealth_zero hP hm hnd hX hindep hlaw hεm' (neg_ne_zero.2 hε.ne'),
    ae_all_iff.2 hXI] with ω h1 h2 hXω
  refine ⟨fun n ↦ max (fixedWealth m ε X n ω) (fixedWealth m (-ε) X n ω), by
    simpa using h1.max h2, ?_⟩
  filter_upwards [h1.eventually_le_const zero_lt_one, h2.eventually_le_const zero_lt_one]
    with n hn1 hn2 l hl hεl
  refine ⟨fixedWealth_nonneg (Set.Ioo_subset_Icc_self hm01) hl fun k _ ↦ hXω k, ?_⟩
  rcases le_total 0 l with h0 | h0
  · rw [abs_of_nonneg h0] at hεl
    exact (fixedWealth_le_of_le_one (Set.Ioo_subset_Icc_self hm01) hε hεl hl (fun k _ ↦ hXω k)
      hn1).trans (le_max_left _ _)
  · rw [abs_of_nonpos h0] at hεl
    exact (fixedWealth_le_of_le_one_of_le_neg (Set.Ioo_subset_Icc_self hm01) hε (by linarith) hl
      (fun k _ ↦ hXω k) hn2).trans (le_max_right _ _)

/-- **Small bets have a small limit** (`lem:mixture_small`): for i.i.d. observations with a law
`P` on `[0, 1]` with mean `m`, a finite measure `π` concentrated on `fractionRange m`
and any set `B` of bet fractions, the mixture wealth over `B` converges almost surely to a
nonnegative limit `L` with `∫⁻ L ≤ π B`. -/
lemma exists_ae_tendsto_setIntegral_fixedWealth (hP : ∀ᵐ x ∂P, x ∈ Set.Icc (0 : ℝ) 1)
    (hm : ∫ x, x ∂P = m) (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P') {π : Measure ℝ}
    [IsFiniteMeasure π] (hπ : ∀ᵐ l ∂π, l ∈ fractionRange m) (B : Set ℝ) :
    ∃ L : Ω → ℝ, Measurable L ∧ 0 ≤ᵐ[P'] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂P' ≤ π B ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ ∫ l in B, fixedWealth m l X n ω ∂π) atTop (𝓝 (L ω)) := by
  have hm01 := mem_Icc_of_integral_eq hP hm
  have hab : -1 / (1 - m) ≤ 1 / m := by
    have h0 := zero_mem_fractionRange hm01
    exact h0.1.trans h0.2
  -- project the fractions on `fractionRange m`, and take the positive part of the wealth
  set g : ℝ → ℝ := fun l ↦ max (-1 / (1 - m)) (min (1 / m) l) with hg_def
  have hg : Measurable g := by fun_prop
  have hg_mem : ∀ l, g l ∈ fractionRange m := fun l ↦
    ⟨le_max_left _ _, max_le hab (min_le_left _ _)⟩
  have hg_eq : ∀ l ∈ fractionRange m, g l = l := fun l hl ↦ by
    simp only [hg_def, min_eq_right hl.2, max_eq_right hl.1]
  set ℱ := pastFiltration X hX with hℱ
  set f : ℝ → ℕ → Ω → ℝ := fun l n ω ↦ max 0 (fixedWealth m (g l) X n ω) with hf_def
  have hXI' : ∀ᵐ ω ∂P', ∀ k, X k ω ∈ Set.Icc 0 1 := ae_all_iff.2 fun k ↦ (hlaw k).ae_comp hP
  have hmeas : ∀ n, Measurable[MeasurableSpace.prod inferInstance (ℱ n)]
      (fun p : ℝ × Ω ↦ f p.1 n p.2) := fun n ↦
    measurable_const.max (measurable_fixedWealth_prod (mΩ := ℱ n)
      (fun k hk ↦ measurable_pastFiltration_of_lt X hX hk) hg)
  have hf : ∀ l, Supermartingale (f l) ℱ P' := by
    intro l
    have hW := supermartingale_wealth (ℱ := ℱ) (lam := fun _ _ ↦ g l) hP hm
      (measurable_pastFiltration_succ X hX) (indep_pastFiltration hX hindep) hlaw
      (fun _ ↦ measurable_const) (fun _ ↦ ae_of_all _ fun _ ↦ hg_mem l)
    refine hW.congr (fun n ↦ ?_) fun n ↦ ?_
    · exact ((hmeas n).comp (measurable_prodMk_left (m := inferInstance))).stronglyMeasurable
    · filter_upwards [hXI'] with ω hω
      exact (max_eq_right (fixedWealth_nonneg hm01 (hg_mem l) fun k _ ↦ hω k)).symm
  obtain ⟨L, hLm, hL0, hLint, hL⟩ := exists_ae_tendsto_setIntegral_of_supermartingale (π := π) hf
    (fun _ _ _ ↦ le_max_left _ _) hmeas (fun l ω ↦ by simp [hf_def, fixedWealth]) B
  refine ⟨L, hLm, hL0, hLint, ?_⟩
  filter_upwards [hL, hXI'] with ω hω hXω
  refine hω.congr fun n ↦ integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [hπ] with l hl
  simp only [hf_def, hg_eq l hl]
  exact max_eq_right (fixedWealth_nonneg hm01 hl fun k _ ↦ hXω k)

end Betting

section Subgaussian

variable {P' : Measure Ω} [IsProbabilityMeasure P'] {P : Measure ℝ} {m : ℝ} {X : ℕ → Ω → ℝ}

/-- The sub-Gaussian test process is positive. -/
lemma subgaussianTest_pos (m : ℝ) (lam X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    0 < subgaussianTest m lam X n ω :=
  Real.exp_pos _

/-- The sub-Gaussian test process of a constant alternative is bounded uniformly in the
alternative: `M^l_n ≤ exp ((∑_{k < n} (X k - m))² / 2)`. -/
lemma subgaussianTest_le_exp_sq (m l : ℝ) (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    subgaussianTest m (fun _ _ ↦ l) X n ω
      ≤ Real.exp ((∑ k ∈ range n, (X k ω - m)) ^ 2 / 2) := by
  rw [subgaussianTest_const]
  gcongr
  set S := ∑ k ∈ range n, (X k ω - m)
  rcases n with _ | n
  · simp [S]
  · have h1 : (l - m) ^ 2 / 2 ≤ ((n + 1 : ℕ) : ℝ) * (l - m) ^ 2 / 2 := by
      have : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos n
      have := sq_nonneg (l - m)
      nlinarith
    nlinarith [sq_nonneg (l - m - S)]

/-- The sub-Gaussian test process after `n` rounds is integrable in the alternative for every
finite measure. -/
lemma integrable_subgaussianTest {π : Measure ℝ} [IsFiniteMeasure π] (n : ℕ) (ω : Ω) :
    Integrable (fun l ↦ subgaussianTest m (fun _ _ ↦ l) X n ω) π := by
  refine Integrable.of_bound (C := Real.exp ((∑ k ∈ range n, (X k ω - m)) ^ 2 / 2)) ?_
    (ae_of_all _ fun l ↦ ?_)
  · refine Continuous.aestronglyMeasurable ?_
    unfold subgaussianTest
    fun_prop
  · rw [Real.norm_of_nonneg (subgaussianTest_pos m _ X n ω).le]
    exact subgaussianTest_le_exp_sq m l X n ω

/-- **Large alternatives are dominated**, pathwise: if the test processes of the alternatives
`m + ε` and `m - ε` tend to `0`, then the test processes of the alternatives `l` with
`|l - m| ≥ ε` are bounded, for `n` large, by `max (M^{m+ε}_n, M^{m-ε}_n) → 0`. -/
lemma exists_bound_subgaussianTest_of_le_abs {ε : ℝ} (hε : 0 < ε) {ω : Ω}
    (h1 : Tendsto (fun n ↦ subgaussianTest m (fun _ _ ↦ m + ε) X n ω) atTop (𝓝 0))
    (h2 : Tendsto (fun n ↦ subgaussianTest m (fun _ _ ↦ m - ε) X n ω) atTop (𝓝 0)) :
    ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ l, ε ≤ |l - m| →
      0 ≤ subgaussianTest m (fun _ _ ↦ l) X n ω ∧ subgaussianTest m (fun _ _ ↦ l) X n ω ≤ G n := by
  refine ⟨fun n ↦ max (subgaussianTest m (fun _ _ ↦ m + ε) X n ω)
    (subgaussianTest m (fun _ _ ↦ m - ε) X n ω), by simpa using h1.max h2, ?_⟩
  filter_upwards [h1.eventually_le_const zero_lt_one, h2.eventually_le_const zero_lt_one]
    with n hn1 hn2 l hεl
  refine ⟨(subgaussianTest_pos m _ X n ω).le, ?_⟩
  rcases le_total m l with h0 | h0
  · rw [abs_of_nonneg (sub_nonneg.2 h0)] at hεl
    exact (subgaussianTest_le_of_le_one hε (by linarith) hn1).trans (le_max_left _ _)
  · rw [abs_of_nonpos (sub_nonpos.2 h0)] at hεl
    exact (subgaussianTest_le_of_le_one_of_le_sub hε (by linarith) hn2).trans (le_max_right _ _)

/-- **Large alternatives are dominated**: for i.i.d. observations with a law `P` such that
`x - m` is `1`-sub-Gaussian and `ε > 0`, almost surely the test processes of the alternatives `l`
with `|l - m| ≥ ε` are bounded, for `n` large, by a sequence tending to `0` (namely
`max (M^{m+ε}_n, M^{m-ε}_n)`). -/
lemma ae_exists_bound_subgaussianTest_of_le_abs (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P)
    (hX : ∀ n, Measurable (X n)) (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P', ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ l, ε ≤ |l - m| →
      0 ≤ subgaussianTest m (fun _ _ ↦ l) X n ω ∧ subgaussianTest m (fun _ _ ↦ l) X n ω ≤ G n := by
  filter_upwards [ae_tendsto_subgaussianTest_zero hP hX hindep hlaw (l := m + ε) (by linarith),
    ae_tendsto_subgaussianTest_zero hP hX hindep hlaw (l := m - ε) (by linarith)] with ω h1 h2
    using exists_bound_subgaussianTest_of_le_abs hε h1 h2

/-- **Small alternatives have a small limit**: for i.i.d. observations with a law `P` such that
`x - m` is `1`-sub-Gaussian, a finite measure `π` and any set `B` of alternatives, the mixture
test process over `B` converges almost surely to a nonnegative limit `L` with `∫⁻ L ≤ π B`. -/
lemma exists_ae_tendsto_setIntegral_subgaussianTest
    (hP : HasSubgaussianMGF (fun x ↦ x - m) 1 P) (hX : ∀ n, Measurable (X n))
    (hindep : iIndepFun X P') (hlaw : ∀ n, HasLaw (X n) P P') {π : Measure ℝ}
    [IsFiniteMeasure π] (B : Set ℝ) :
    ∃ L : Ω → ℝ, Measurable L ∧ 0 ≤ᵐ[P'] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂P' ≤ π B ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ ∫ l in B, subgaussianTest m (fun _ _ ↦ l) X n ω ∂π) atTop
        (𝓝 (L ω)) := by
  set ℱ := pastFiltration X hX with hℱ
  have hf : ∀ l : ℝ, Supermartingale (subgaussianTest m (fun _ _ ↦ l) X) ℱ P' := fun l ↦
    supermartingale_subgaussianTest hP (measurable_pastFiltration_succ X hX)
      (indep_pastFiltration hX hindep) hlaw fun _ ↦ measurable_const
  have hmeas : ∀ n, Measurable[MeasurableSpace.prod inferInstance (ℱ n)]
      (fun p : ℝ × Ω ↦ subgaussianTest m (fun _ _ ↦ p.1) X n p.2) := fun n ↦
    measurable_subgaussianTest_prod (mΩ := ℱ n) fun k hk ↦ measurable_pastFiltration_of_lt X hX hk
  exact exists_ae_tendsto_setIntegral_of_supermartingale (π := π) hf
    (fun l n ω ↦ (subgaussianTest_pos m _ X n ω).le) hmeas (fun l ω ↦ by simp [subgaussianTest]) B

section Conditional

/-! ### Conditionally sub-Gaussian observations

The no-cash criterion for sub-Gaussian mixture test processes holds for observations `X n` such
that `X n - m` is conditionally `1`-sub-Gaussian given `ℱ n`, without independence. -/

variable [StandardBorelSpace Ω] {ℱ : Filtration ℕ mΩ}

/-- **Large alternatives are dominated**, conditionally sub-Gaussian observations. -/
lemma ae_exists_bound_subgaussianTest_of_le_abs_of_hasCondSubgaussianMGF
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (fun ω ↦ X n ω - m) 1 P')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ ω ∂P', ∃ G : ℕ → ℝ, Tendsto G atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ l, ε ≤ |l - m| →
      0 ≤ subgaussianTest m (fun _ _ ↦ l) X n ω ∧ subgaussianTest m (fun _ _ ↦ l) X n ω ≤ G n := by
  filter_upwards [ae_tendsto_subgaussianTest_zero_of_hasCondSubgaussianMGF hX hsubG
      (l := m + ε) (by linarith),
    ae_tendsto_subgaussianTest_zero_of_hasCondSubgaussianMGF hX hsubG (l := m - ε) (by linarith)]
    with ω h1 h2 using exists_bound_subgaussianTest_of_le_abs hε h1 h2

/-- **Small alternatives have a small limit**, conditionally sub-Gaussian observations: for a
finite measure `π` and any set `B` of alternatives, the mixture test process over `B` converges
almost surely to a nonnegative limit `L` with `∫⁻ L ≤ π B`. -/
lemma exists_ae_tendsto_setIntegral_subgaussianTest_of_hasCondSubgaussianMGF
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (fun ω ↦ X n ω - m) 1 P')
    {π : Measure ℝ} [IsFiniteMeasure π] (B : Set ℝ) :
    ∃ L : Ω → ℝ, Measurable L ∧ 0 ≤ᵐ[P'] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂P' ≤ π B ∧
      ∀ᵐ ω ∂P', Tendsto (fun n ↦ ∫ l in B, subgaussianTest m (fun _ _ ↦ l) X n ω ∂π) atTop
        (𝓝 (L ω)) := by
  have hf : ∀ l : ℝ, Supermartingale (subgaussianTest m (fun _ _ ↦ l) X) ℱ P' := fun l ↦
    supermartingale_subgaussianTest_of_hasCondSubgaussianMGF hX hsubG fun _ ↦ measurable_const
  have hmeas : ∀ n, Measurable[MeasurableSpace.prod inferInstance (ℱ n)]
      (fun p : ℝ × Ω ↦ subgaussianTest m (fun _ _ ↦ p.1) X n p.2) := fun n ↦
    measurable_subgaussianTest_prod (mΩ := ℱ n) fun k hk ↦
      (hX k).mono (ℱ.mono (Nat.succ_le_of_lt hk)) le_rfl
  exact exists_ae_tendsto_setIntegral_of_supermartingale (π := π) hf
    (fun l n ω ↦ (subgaussianTest_pos m _ X n ω).le) hmeas (fun l ω ↦ by simp [subgaussianTest]) B

/-- **No-cash criterion for sub-Gaussian mixture test processes, conditionally sub-Gaussian
observations.** If `X n` is `ℱ (n + 1)`-measurable and `X n - m` is conditionally
`1`-sub-Gaussian given `ℱ n`, then for every finite measure `π` on `ℝ`, the mixture test process
`∫ exp (∑_{k < n} ((X k - m)² - (X k - l)²) / 2) ∂π(l)` converges almost surely to `π({m})`. -/
lemma ae_tendsto_subgaussianMixtureTest_of_hasCondSubgaussianMGF
    (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
    (hsubG : ∀ n, HasCondSubgaussianMGF (ℱ n) (ℱ.le n) (fun ω ↦ X n ω - m) 1 P')
    (π : Measure ℝ) [IsFiniteMeasure π] :
    ∀ᵐ ω ∂P', Tendsto (fun n ↦ subgaussianMixtureTest m π X n ω) atTop (𝓝 (π.real {m})) := by
  refine ae_tendsto_integral_of_ball (F := fun l n ω ↦ subgaussianTest m (fun _ _ ↦ l) X n ω)
    (c := m) (fun n ω ↦ by simp [subgaussianTest])
    (ae_of_all _ fun ω n ↦ integrable_subgaussianTest n ω) (fun ε hε ↦ ?_) fun ε hε ↦ ?_
  · filter_upwards [ae_exists_bound_subgaussianTest_of_le_abs_of_hasCondSubgaussianMGF hX hsubG
      hε.1] with ω ⟨G, hG, hle⟩
    refine ⟨G, hG, hle.mono fun n hn ↦ ae_of_all _ fun l hεl ↦ ?_⟩
    obtain ⟨h0, h1⟩ := hn l hεl
    rwa [abs_of_nonneg h0]
  · obtain ⟨L, hLm, hL0, hLint, hL⟩ :=
      exists_ae_tendsto_setIntegral_subgaussianTest_of_hasCondSubgaussianMGF hX hsubG (π := π)
        (Metric.ball m ε \ {m})
    exact ⟨L, hLm.aemeasurable, hL0, hLint, hL⟩

end Conditional

end Subgaussian

end Learning.Betting
