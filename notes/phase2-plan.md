# Phase 2 plan: work packages and briefs

Every package proves the lemmas of one blueprint area, in new files, against the interfaces
fixed below (names and statements). Later packages import earlier ones. Waves:

* **Wave 1** (independent, in parallel): A (martingale tools), B (asymptotics, Thm 2.2,
  Cor 2.3), C1 (pathwise paper results: Lemmas B.2, B.3, Def B.4, Facts 1–2, Thm 4.1, regret),
  C2 (log inequalities, Bernoulli domination, deterministic hindsight analysis).
* **Wave 2**: D (wealth supermartingale, filtrations, sum-of-squares criteria, `n^{-1/2}`
  criterion, sub-Gaussian criterion; Thms 2.1, 5.2, Cor 2.4) — needs A, B.
* **Wave 3** (in parallel): E (Props 2.5–2.8, Thm 5.1 χ²) — needs A, B, C2, D;
  F (Thm 3.1, Prop 3.2, Thm 5.3) — needs A, C2, D.

## Rules for every package

* Read `notes/blueprint-outline.md`, the blueprint chapters of the package, and the files you
  build on. Lean conventions: every file `module` + `public import …` + module docstring +
  `@[expose] public section`, copyright header `Rémy Degenne` (as the existing files), every
  declaration with a docstring, `lemma` (never `theorem`, except the paper's headline results
  already stated), Mathlib naming, lines ≤ 100 chars, no `sorry` left at the end.
* **Never change** the statements of the existing headline theorems and lemmas in
  `Wang2026Almost/WAR2026/` nor the definitions in `Wang2026Almost/LeanMachineLearning/Betting/`,
  `Wang2026Almost/WAR2026/Leverage.lean`, `Mixtures.lean`, `AsymptoticsInProbability.lean`,
  `ChiSquare.lean`, `Gamma.lean`, `ObliviousEnv.lean` (they are frozen by the comparator
  challenges). You may add lemmas to those files only when the brief says so; otherwise add new
  files. If a frozen statement looks false or unprovable, stop and report instead of changing it.
* Prove the general statement and derive the specialization; drop hypotheses the proof does not
  use from *new* lemmas (and say so in the docstring when it departs from the paper).
* Only edit the files of your package and the blueprint chapters listed in your brief. After
  adding/removing a Lean file run `lake exe mk_all --lib Wang2026Almost` (it rewrites the root
  file; concurrent runs are harmless). Do not run `leanblueprint` (another package may be
  building) and do not commit.
* Blueprint: add `\lean{Full.Name}` and `\leanok` to each statement the moment its declaration
  compiles, and `\leanok` inside the `proof` environment when the proof is complete; keep labels
  unchanged; add a lemma (with a label and `\uses`) if you need a new intermediate step. Run
  `python3 scripts/check-blueprint.py`.
* Check, in this order, before reporting: `lake build Wang2026Almost --wfail` (no warnings, no
  `sorry` in your files), `lake exe runLinter Wang2026Almost`, `grep -rn sorry` on your files.
  Concurrent `lake build` calls in this checkout are fine.
* Look up APIs by grepping `.lake/packages/mathlib/Mathlib` and
  `.lake/packages/LeanMachineLearning/LeanMachineLearning`; test in scratch files with
  `lake env lean File.lean` in your scratchpad.
* Report: what was proved (names), any deviation from the interface, anything left.

## A. Martingale tools (`chap:pre_martingale`)

Files (namespaces `ProbabilityTheory` / `MeasureTheory`):
`Wang2026Almost/Mathlib/Probability/Independence/Freezing.lean`,
`Wang2026Almost/Mathlib/Probability/Martingale/IndepIncrements.lean`,
`Wang2026Almost/Mathlib/Probability/Martingale/Nonneg.lean`,
`Wang2026Almost/Mathlib/Probability/Martingale/Mixture.lean`,
`Wang2026Almost/Mathlib/Probability/Martingale/SubgaussianSum.lean`,
`Wang2026Almost/Mathlib/Probability/Moments/SubgaussianRate.lean`.

Interfaces (adapt binder details as needed, keep the names and the mathematical content):

```lean
-- lem:lintegral_comp_indep
lemma ProbabilityTheory.setLIntegral_comp_of_indep [IsProbabilityMeasure μ]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {Z : Ω → E} {Y : Ω → F}
    (hZ : Measurable[m] Z) (hY : Measurable Y)
    (hindep : Indep (MeasurableSpace.comap Y mF) m μ) {Φ : E × F → ℝ≥0∞} (hΦ : Measurable Φ)
    {A : Set Ω} (hA : MeasurableSet[m] A) :
    ∫⁻ ω in A, Φ (Z ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, Φ (Z ω, y) ∂(μ.map Y) ∂μ
-- lem:supermartingale_of_markov
lemma MeasureTheory.supermartingale_of_lintegral_le [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {V : ℕ → Ω → ℝ} (hV : Adapted ℱ V) (hV_nonneg : ∀ n, 0 ≤ᵐ[μ] V n)
    (hV0 : Integrable (V 0) μ) {Z : ℕ → Ω → E} {Y : ℕ → Ω → F}
    (hZ : ∀ n, Measurable[ℱ n] (Z n)) (hY : ∀ n, Measurable (Y n))
    (hindep : ∀ n, Indep (MeasurableSpace.comap (Y n) mF) (ℱ n) μ)
    {Φ : ℕ → E × F → ℝ≥0∞} (hΦ : ∀ n, Measurable (Φ n))
    (hrec : ∀ n, ∀ᵐ ω ∂μ, ENNReal.ofReal (V (n + 1) ω) = Φ n (Z n ω, Y n ω))
    (hle : ∀ n, ∀ᵐ ω ∂μ, ∫⁻ y, Φ n (Z n ω, y) ∂(μ.map (Y n)) ≤ ENNReal.ofReal (V n ω)) :
    Supermartingale V ℱ μ
-- lem:supermartingale_tendsto
lemma MeasureTheory.Supermartingale.exists_ae_tendsto_of_nonneg [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ mΩ} {V : ℕ → Ω → ℝ} (hV : Supermartingale V ℱ μ)
    (hV_nonneg : ∀ n, 0 ≤ᵐ[μ] V n) :
    ∃ L : Ω → ℝ, Measurable L ∧ (∀ᵐ ω ∂μ, Tendsto (fun n ↦ V n ω) atTop (𝓝 (L ω))) ∧
      0 ≤ᵐ[μ] L ∧ ∫⁻ ω, ENNReal.ofReal (L ω) ∂μ ≤ ENNReal.ofReal (∫ ω, V 0 ω ∂μ)
-- lem:supermartingale_integral (π finite measure on a measurable space L)
lemma MeasureTheory.supermartingale_integral [IsFiniteMeasure μ] [IsFiniteMeasure π]
    {ℱ : Filtration ℕ mΩ} {f : L → ℕ → Ω → ℝ} (hf : ∀ l, Supermartingale (f l) ℱ μ)
    (hf_nonneg : ∀ l n ω, 0 ≤ f l n ω)
    (hmeas : ∀ n, Measurable[mL.prod (ℱ n)] (fun p : L × Ω ↦ f p.1 n p.2))
    (hbdd : ∃ C, ∀ l, ∫ ω, f l 0 ω ∂μ ≤ C) :
    Supermartingale (fun n ω ↦ ∫ l, f l n ω ∂π) ℱ μ
-- Section variables for the next three: [IsProbabilityMeasure μ] {ℱ : Filtration ℕ mΩ}
-- {Y w : ℕ → Ω → ℝ} {c : ℝ≥0} (hY : ∀ n, Measurable[ℱ (n + 1)] (Y n))
-- (hindep : ∀ n, Indep (MeasurableSpace.comap (Y n) inferInstance) (ℱ n) μ)
-- (hsubG : ∀ n, HasSubgaussianMGF (Y n) c μ) (hw : Adapted ℱ w)
-- lem:exp_subg_supermartingale
lemma ProbabilityTheory.supermartingale_exp_sum_mul (t : ℝ) :
    Supermartingale (fun n ω ↦ Real.exp (t * ∑ k ∈ Finset.range n, w k ω * Y k ω
      - c * t ^ 2 * (∑ k ∈ Finset.range n, w k ω ^ 2) / 2)) ℱ μ
-- lem:subg_sum_tendsto
lemma ProbabilityTheory.ae_exists_tendsto_sum_mul :
    ∀ᵐ ω ∂μ, Summable (fun n ↦ w n ω ^ 2) →
      ∃ T, Tendsto (fun n ↦ ∑ k ∈ Finset.range n, w k ω * Y k ω) atTop (𝓝 T)
-- lem:subg_sum_little_o
lemma ProbabilityTheory.ae_forall_abs_sum_mul_le :
    ∀ᵐ ω ∂μ, ∀ ε > 0, ∃ C, ∀ n, |∑ k ∈ Finset.range n, w k ω * Y k ω|
      ≤ C + ε * ∑ k ∈ Finset.range n, w k ω ^ 2
-- lem:hoeffding_rate
lemma ProbabilityTheory.ae_isBigO_sum_range_sqrt_mul_log [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {c : ℝ≥0} (hindep : iIndepFun Y μ) (hY : ∀ n, HasSubgaussianMGF (Y n) c μ) :
    ∀ᵐ ω ∂μ, (fun n : ℕ ↦ ∑ k ∈ Finset.range n, Y k ω) =O[atTop]
      (fun n : ℕ ↦ √n * Real.log n)
```

Hints: `indepFun_iff_map_prod_eq_prod_map_map`, `lintegral_map`, `lintegral_prod`,
`supermartingale_of_setIntegral_succ_le`, `Submartingale.ae_tendsto_limitProcess`
(apply to `-V`, `eLpNorm` bound from `∫ |V n| = ∫ V n ≤ ∫ V 0`), `lintegral_liminf_le`
(Fatou), `integral_integral_swap`/`lintegral_lintegral_swap`, `HasSubgaussianMGF.mgf_le`,
`measure_sum_range_ge_le_of_iIndepFun`, `measure_limsup_atTop_eq_zero`. Blueprint:
`chapters/prereq_martingale.tex`.

## B. Asymptotics in probability, Theorem 2.2, Corollary 2.3 (`chap:pre_asymptotics`, part of `chap:predictable`)

Files: add to `Wang2026Almost/Mathlib/Probability/AsymptoticsInProbability.lean` (allowed:
new lemmas only), new `Wang2026Almost/Mathlib/Probability/SumBigOmegaInProb.lean`
(Theorem 2.2 in library form), `Wang2026Almost/Mathlib/Order/Cesaro.lean` (or a better Mathlib
path), `Wang2026Almost/Mathlib/Analysis/SpecialFunctions/Log/Summable.lean`,
`Wang2026Almost/Mathlib/Probability/Distributions/Gaussian/Sq.lean`; proofs of
`WAR2026/Theorem2_2.lean` and `WAR2026/Corollary2_3.lean`.

```lean
lemma ProbabilityTheory.IsBigOmegaInProb.mono (h : IsBigOmegaInProb P X a) {K : ℝ} (hK : 0 < K)
    (hab : ∀ᶠ n in atTop, b n ≤ K * a n) : IsBigOmegaInProb P X b
lemma ProbabilityTheory.IsBigOmegaInProb.sq (h : IsBigOmegaInProb P X a)
    (ha : ∀ᶠ n in atTop, 0 ≤ a n) :
    IsBigOmegaInProb P (fun n ω ↦ X n ω ^ 2) (fun n ↦ a n ^ 2)
lemma ProbabilityTheory.isBigOmegaInProb_of_tendstoInDistribution [IsProbabilityMeasure P]
    {μ' : Measure Ω'} [IsProbabilityMeasure μ'] {Z : Ω' → ℝ} {X : ℕ → Ω → ℝ} {a : ℕ → ℝ}
    (ha : ∀ᶠ n in atTop, 0 < a n)
    (h : TendstoInDistribution (fun n ω ↦ X n ω / a n) atTop Z (fun _ ↦ P) μ')
    (hZ : μ' (Z ⁻¹' {0}) = 0) : IsBigOmegaInProb P X a
lemma MeasureTheory.measure_liminf_atTop_le_liminf (μ) (s : ℕ → Set Ω) :
    μ (liminf s atTop) ≤ liminf (fun n ↦ μ (s n)) atTop
lemma tendsto_cesaro_zero_of_summable_div {a : ℕ → ℝ} (h0 : ∀ k, 0 ≤ a k) (h1 : ∀ k, a k ≤ 1)
    (h : Summable (fun k ↦ a k / k)) : Tendsto (fun n ↦ (∑ k ∈ Finset.range n, a k) / n) atTop (𝓝 0)
lemma Real.not_summable_inv_mul_log : ¬ Summable (fun n : ℕ ↦ ((n : ℝ) * Real.log n)⁻¹)
lemma ProbabilityTheory.gaussianReal_map_sq : (gaussianReal 0 1).map (fun x ↦ x ^ 2) = chiSquareMeasure 1
lemma ProbabilityTheory.ae_not_summable_of_isBigOmegaInProb -- the library form of Thm 2.2
```

Corollary 2.3 needs a measurable modification (`AEMeasurable.mk`) only if convenient; Theorem
2.2 is stated with `AEMeasurable`. Blueprint: `chapters/prereq_asymptotics.tex`, and the
statements `thm:sum_of_op`, `cor:div_sample_mean` in `chapters/predictable.tex` (only those two
environments of that file).

## C1. Pathwise paper results (`chap:improve`, `lem:exp_regular`, `thm:unbounded_regret`)

Prove `WAR2026/LemmaB_2.lean`, `LemmaB_3.lean`, `DefinitionB_4.lean`, `Fact1.lean`,
`Fact2.lean`, `Theorem4_1.lean` (with a new lemma `Wang2026Almost.adapted_oppLeverage` in a new
file `WAR2026/LeverageMeasurable.lean`, or in `Theorem4_1.lean`), and the second theorem of
`WAR2026/Theorem5_1.lean` (`not_bddAbove_logRegret_of_tendsto_wealth_zero`; leave the first
theorem `sorry` for package E). Helper lemmas about `wealth` may go in a new file
`Wang2026Almost/LeanMachineLearning/Betting/WealthLemmas.lean` (namespace `Learning.Betting`),
e.g. `wealth_eq_zero_of_...`, `bddAbove_fixedWealth`, `one_le_iSup_fixedWealth`.
Blueprint: `chapters/improve.tex`, `lem:exp_regular` in `chapters/mixture.tex`,
`thm:unbounded_regret` in `chapters/odds.tex`.

## C2. Log inequalities, Bernoulli domination, hindsight analysis (`chap:pre_betting` except `lem:wealth_supermartingale`)

Files: `Wang2026Almost/Mathlib/Analysis/SpecialFunctions/Log/OneAdd.lean` (namespace `Real`),
`Wang2026Almost/LeanMachineLearning/Betting/Domination.lean`,
`Wang2026Almost/LeanMachineLearning/Betting/Hindsight.lean` (namespace `Learning.Betting`).

```lean
lemma Real.abs_log_one_add_sub_le {x : ℝ} (hx : |x| ≤ 1 / 2) :
    |Real.log (1 + x) - (x - x ^ 2 / 2)| ≤ 2 * |x| ^ 3
lemma Real.sub_sq_le_log_one_add {x : ℝ} (hx : |x| ≤ 1 / 2) : x - x ^ 2 ≤ Real.log (1 + x)
lemma Real.log_one_add_le_sub_mul_sq {x M : ℝ} (hM : 0 ≤ M) (hx1 : -1 < x) (hxM : x ≤ M) :
    Real.log (1 + x) ≤ x - x ^ 2 / (2 * (1 + M))
-- Bernoulli domination, general products then betting forms
lemma Learning.Betting.prod_one_add_mul_le_rpow {ε l : ℝ} (hε : 0 < ε) (hεl : ε ≤ l)
    {y : ℕ → ℝ} {n : ℕ} (hl : ∀ k < n, 0 ≤ 1 + l * y k) (hεy : ∀ k < n, -1 ≤ ε * y k) :
    ∏ k ∈ Finset.range n, (1 + l * y k) ≤ (∏ k ∈ Finset.range n, (1 + ε * y k)) ^ (l / ε)
lemma Learning.Betting.fixedWealth_le_of_le_one -- for X in [0,1], l ∈ fractionRange m, ε ≤ l,
    -- ε ∈ fractionRange m, fixedWealth m ε X n ω ≤ 1 → fixedWealth m l X n ω ≤ fixedWealth m ε X n ω
    -- and the symmetric version for l ≤ -ε < 0
lemma Learning.Betting.subgaussianTest_le_of_le_one -- same for subgaussianTest with constant
    -- strategies m + u, u ≥ ε > 0 (and u ≤ -ε)
-- Hindsight analysis (deterministic). Section variables: {m σ2 : ℝ} (hm : m ∈ Ioo 0 1)
-- (hσ : 0 < σ2) {y : ℕ → ℝ} (hy : ∀ k, y k ∈ Icc (-m) (1 - m))
-- (hS : (fun n : ℕ ↦ ∑ k ∈ range n, y k) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
-- (hV : (fun n : ℕ ↦ ∑ k ∈ range n, y k ^ 2 - n * σ2) =O[atTop] (fun n : ℕ ↦ √n * Real.log n))
-- with S n, V n the two sums, F n l = ∏ k ∈ range n, (1 + l * y k):
lemma Learning.Betting.eventually_abs_sub_div_le_of_isMaxOn : ∃ K, ∀ᶠ n in atTop, ∀ g,
    IsMaxOn (F n) (fractionRange m) g → g ∈ fractionRange m →
      |g - S n / V n| ≤ K * Real.log n ^ 2 / n
lemma Learning.Betting.tendsto_two_mul_log_iSup_sub :
    Tendsto (fun n ↦ 2 * Real.log (⨆ l : fractionRange m, F n l) - S n ^ 2 / V n) atTop (𝓝 0)
lemma Learning.Betting.measurable_hindsightLogWealth -- (hm : m ∈ Ioo 0 1) (hX : ∀ k, Measurable (X k)) (n) :
    -- Measurable (hindsightLogWealth m X n)
```

(`fixedWealth m l X n ω = ∏ k ∈ range n, (1 + l * (X k ω - m))` by definition, so the
betting forms of the hindsight lemmas are the deterministic ones with `y k = X k ω - m`; state
the deterministic ones on `y` and add the `fixedWealth`/`hindsightLogWealth` corollaries.)
Blueprint: `chapters/prereq_betting.tex` (all but `lem:wealth_supermartingale`) and
`lem:measurable_hindsightLogWealth` in `chapters/odds.tex`.

## D. Sum-of-squares criteria (wave 2; `chap:predictable` first and third sections, `thm:sos_crit_subg*`, `lem:wealth_supermartingale`, `lem:iid_of_run`, `lem:iid_of_plug_in`, `def:past_filtration`)

Files: `Wang2026Almost/LeanMachineLearning/Betting/PastFiltration.lean`,
`Wang2026Almost/LeanMachineLearning/Betting/IIDRun.lean`,
`Wang2026Almost/LeanMachineLearning/Betting/SumSquares.lean`,
`Wang2026Almost/LeanMachineLearning/Betting/SumSquaresSubgaussian.lean`; proofs of
`WAR2026/Theorem2_1.lean`, `Corollary2_4.lean`, `Theorem5_2.lean`.

```lean
def Learning.Betting.pastFiltration (X : ℕ → Ω → β) (hX : ∀ n, Measurable (X n)) :
    Filtration ℕ mΩ  -- n ↦ σ(X 0, …, X (n - 1))
lemma Learning.Betting.IsPlugIn.adapted_pastFiltration
lemma Learning.Betting.indep_pastFiltration (hindep : iIndepFun X μ) ...
lemma Learning.IsAlgEnvSeq.adapted_action_filtrationAction / measurable_feedback_filtrationAction_succ /
      indep_feedback_filtrationAction_const
-- the i.i.d.-along-ℱ hypotheses, abbreviated (hlam : Adapted ℱ lam)
-- (hX : ∀ n, Measurable[ℱ (n + 1)] (X n))
-- (hindep : ∀ n, Indep (MeasurableSpace.comap (X n) inferInstance) (ℱ n) P')
-- (hlaw : ∀ n, HasLaw (X n) P P')
lemma Learning.Betting.supermartingale_wealth  -- lem:wealth_supermartingale
lemma Learning.Betting.sum_sq_criterion_of_indep  -- thm:sos_crit_filtration (same conclusion as Thm 2.1)
lemma Learning.Betting.tendsto_wealth_zero_of_isBigOmega_of_indep  -- cor:sq_crit_filtration
lemma Learning.Betting.ae_tendsto_fixedWealth_zero  -- constant nonzero fraction in the range
lemma Learning.Betting.sum_sq_criterion_subgaussian_of_indep  -- thm:sos_crit_subg_filtration
lemma Learning.Betting.ae_tendsto_subgaussianTest_zero  -- constant l ≠ m
```

## E. Strategies and the χ² limit (wave 3; `prop:kt` … `prop:hedge`, `thm:chisq_klinf`, `lem:good_event`, `lem:kt_mem`, `lem:empVar_add_sq`)

Proofs of `WAR2026/Proposition2_5.lean` … `Proposition2_8.lean` and the first theorem of
`Theorem5_1.lean`; helper files under `Wang2026Almost/LeanMachineLearning/Betting/`
(`KT.lean`, `GoodEvent.lean`, …).

## F. Mixtures (wave 3; `chap:mixture` except `lem:exp_regular`, `thm:nocash_subg`)

Proofs of `WAR2026/Theorem3_1.lean`, `Proposition3_2.lean`, `Theorem5_3.lean`; helper files
`Wang2026Almost/LeanMachineLearning/Betting/Mixture.lean`, `WAR2026/MixturesProb.lean`
(probability and atomlessness of `betaMixture`, `robbinsMixture`).

## Progress log

* 2026-10-08, during wave 1 (done by the coordinator, not by agents):
  `Betting/PastFiltration.lean` (`pastFiltration`, `measurable_pastFiltration_succ`,
  `measurable_pastFiltration_of_lt`, `IsPlugIn.adapted_pastFiltration`, `indep_pastFiltration`),
  `SequentialLearning/ConstEnvFiltration.lean` (`IsAlgEnvSeq.indep_feedback_filtrationAction_const`,
  `IsAlgEnvSeq.measurable_feedback_filtrationAction_succ`; LML already has
  `adapted_action_filtrationAction`), `Betting/Null.lean` (`mem_Ioo_of_ne_dirac`,
  `variance_pos_of_ne_dirac`, `mem_Ioo_of_variance_pos`, `ne_dirac_of_variance_pos`,
  `eq_dirac_of_ae_eq`, `memLp_two_id_of_mem_Icc`), `Betting/StrategyBounds.lean`
  (`ktFraction_mem_fractionRange`, `empVar_add_sq_empMean_sub`,
  `agrapaFraction_mem_fractionRange`, `hedgeFraction_mem_fractionRange`). Blueprint tags for
  `lem:kt_mem`, `lem:empVar_add_sq` still to add (predictable.tex was being edited by B).
* `WAR2026/MixturesProb.lean` (coordinator): `Icc_subset_fractionRange`,
  `isProbabilityMeasure_betaMixture`, `ae_mem_Icc_betaMixture`, `betaMixture_singleton_zero`,
  `isProbabilityMeasure_robbinsMixture`, `ae_mem_Icc_robbinsMixture`,
  `robbinsMixture_singleton_zero` (Robbins mass via the antiderivative `1 / log log (C / l)` and
  `integral_comp_abs`). Blueprint tags for `lem:betaMixture_prob`, `lem:robbins_prob` still to
  add (mixture.tex was being edited by C1).
* Coordinator, during waves 1–2 (package E material): `Mathlib/Probability/LimitTheorems.lean`
  (`TendstoInDistribution.of_map_eq`, `TendstoInDistribution.mul_add_of_tendsto`,
  `tendstoInDistribution_sum_sub_div_sqrt` (CLT with `HasLaw`), `ae_tendsto_sum_comp_div`
  (SLLN for `f (X k)`)), `Betting/KTLimit.lean` (`gaussianReal_map_inv_mul`,
  `tendstoInDistribution_sqrt_mul_ktFraction`), `Betting/AGrapaLimit.lean`
  (`ae_tendsto_sum_sub_div`, `ae_tendsto_sum_sub_sq_div`, `measurable_agrapaFraction`,
  `tendstoInDistribution_sqrt_mul_agrapaFraction`), `Betting/HedgeRate.lean`
  (`isBigO_rpow_hedgeFraction`: `(n log n)^{-1/2} = O(hedge fraction)` when `v n → σ² > 0`).
* Wave 1 results: A done (all interfaces; extra `supermartingale_integral_of_integrable`,
  `ae_exists_tendsto_exp_sum_mul`); C1 done (+ `Betting/WealthLemmas.lean`,
  `WAR2026/LeverageMeasurable.lean`). Package D launched after A.
* Wave 1 complete: B (Thm 2.2 in library form for any non-summable rate, Cor 2.3, Gaussian
  square law, `IsBigOmegaInProb` API), C2 (log inequalities, Bernoulli domination, hindsight
  analysis; fixed a wrong blueprint step in `lem:log_ge_sub_sq`).
* Wave 2 complete: D (Thms 2.1, 5.2, Cor 2.4 and their filtration forms; pathwise limit route).
* Coordinator: `Betting/GoodEvent.lean`, `Betting/ChiSquareLimit.lean`, `Betting/GrapaLimit.lean`
  (pathwise Bahadur bound `O(log² n / √n)`, a.s. `o(n^{-1/4} log n)`, CLT, `Ω_p`),
  `Betting/PlugIn.lean` (criterion for plug-in strategies; eventually-in-range a.s. variant,
  needed for hedging since `-λ^PrH` may leave the range when `C (1 - m) > m`), proofs of
  Props 2.5–2.8 and of Thm 5.1 (χ²). Package E is thus done by the coordinator.
* Wave 3: F (Thms 3.1, 5.3, Prop 3.2) launched.
