# Paper roadmap: Almost sure null bankruptcy of testing-by-betting strategies

Paper: RemyDegenne/Wang2026Almost · LMLExplore afd365492580 · LMLRoadmaps d01bdd6b89ce · Refreshed 2026-11-09

## Items

| Id | Item | Tag | Link | Status | Files |
|---|---|---|---|---|---|
| R1 | Freezing lemma for the conditional expectation kernel | exists | `LMLExplore.lintegral_comp_condExpKernel` | – | `ForLMLExplore/Probability/Kernel/Condexp.lean` |
| R2 | Conditional sub-Gaussianity of independent variables, and the moment bound at measurable parameters | exists | `ProbabilityTheory.HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep` | – | `ForLMLExplore/Probability/Moments/SubGaussian.lean` |
| R3 | Mixtures of nonnegative supermartingales | exists | `LMLExplore.supermartingale_integral` | – | `ForLMLExplore/Probability/Martingale/Mixture.lean` |
| R4 | Chi-squared laws | exists | `TauCeti.Probability.chiSquaredMeasure` | – | `ForLMLExplore/Probability/Distributions/ChiSquare.lean` |
| R5 | Moment generating function of the gamma laws | exists | `TauCeti.Probability.mgf_id_gammaMeasure` | – | `ForLMLExplore/Probability/Distributions/Gamma.lean` |
| R6 | The square of a standard Gaussian has law χ²₁; laws are determined by their moment generating function | exists | `TauCeti.Probability.gaussianReal_map_sq` | – | `ForLMLExplore/Probability/Distributions/Gaussian/Sq.lean` |
| R7 | Almost sure convergence of nonnegative supermartingales, with the bound on the expectation of the limit | target | ReinforcementLearning 4.1 | proved | `ForLMLExplore/Probability/Martingale/Nonneg.lean` |
| R8 | Betting wealth processes, the range of bet fractions and the betting supermartingale | target | OnlineLearning 16.4 | proved | `ForLMLExplore/OnlineLearning/Betting/Wealth.lean`, `ForLMLExplore/OnlineLearning/Betting/WealthLemmas.lean` |
| R9 | Landau notation in probability: O_p, Ω_p and their almost sure forms | staged | S1 | proved | `ForLMLExplore/Probability/AsymptoticsInProbability.lean` |
| R10 | Almost sure divergence of series whose terms are Ω_p of a non-summable rate; Fatou's lemma for sets | staged | S1 | proved | `ForLMLExplore/Probability/SumBigOmegaInProb.lean` |
| R11 | The central limit theorem and the strong law in `HasLaw` form; Slutsky with deterministic factors | staged | S1 | proved | `ForLMLExplore/Probability/LimitTheorems.lean` |
| R12 | Freezing lemma for an independent variable, and supermartingales with independent increments | staged | S2 | proved | `ForLMLExplore/Probability/Independence/Freezing.lean`, `ForLMLExplore/Probability/Martingale/IndepIncrements.lean` |
| R13 | Martingale strong law for conditionally sub-Gaussian increments | staged | S2 | proved | `ForLMLExplore/Probability/Martingale/SubgaussianSum.lean` |
| R14 | Almost sure Hoeffding rates for sums of independent sub-Gaussian variables | staged | S2 | proved | `ForLMLExplore/Probability/Moments/SubgaussianRate.lean` |
| R15 | Bounds on log (1 + x), and the divergence of the series of 1 / (n log n) | staged | S4 | proved | `ForLMLExplore/Analysis/SpecialFunctions/Log/OneAdd.lean`, `ForLMLExplore/Analysis/SpecialFunctions/Log/Summable.lean` |
| R16 | The i.i.d. environment `Environment.const` and its runs | staged | S5 | proved | `ForLMLExplore/SequentialLearning/ObliviousEnv.lean`, `ForLMLExplore/SequentialLearning/ConstEnvFiltration.lean` |
| R17 | Null laws on [0, 1]: mean, variance and sub-Gaussianity; `HasLaw` transfer lemmas | staged | S3 | proved | `ForLMLExplore/Probability/HasLaw.lean`, `ForLMLExplore/OnlineLearning/Betting/Null.lean` |
| R18 | Predictable plug-in strategies and the past filtration; the KT, GRAPA, aGRAPA and hedging strategies | staged | S3 | proved | `ForLMLExplore/OnlineLearning/Betting/PastFiltration.lean`, `ForLMLExplore/OnlineLearning/Betting/Strategies.lean`, `ForLMLExplore/OnlineLearning/Betting/StrategyBounds.lean` |
| R19 | Sum-of-squares criterion for null bankruptcy along a filtration, and the n^(-1/2) criterion | staged | S3 | proved | `ForLMLExplore/OnlineLearning/Betting/SumSquares.lean`, `ForLMLExplore/OnlineLearning/Betting/PlugIn.lean` |
| R20 | Sub-Gaussian sum-of-squares criterion | staged | S3 | proved | `ForLMLExplore/OnlineLearning/Betting/SumSquaresSubgaussian.lean` |
| R21 | Null asymptotics of the KT, GRAPA, aGRAPA and hedging strategies | staged | S3 | proved | `ForLMLExplore/OnlineLearning/Betting/KTLimit.lean`, `ForLMLExplore/OnlineLearning/Betting/GrapaLimit.lean`, `ForLMLExplore/OnlineLearning/Betting/AGrapaLimit.lean`, `ForLMLExplore/OnlineLearning/Betting/HedgeRate.lean`, `ForLMLExplore/OnlineLearning/Betting/GoodEvent.lean` |
| R22 | Best constant bet in hindsight: deterministic analysis and the χ²₁ null limit | staged | S3 | proved | `ForLMLExplore/OnlineLearning/Betting/Hindsight.lean`, `ForLMLExplore/OnlineLearning/Betting/ChiSquareLimit.lean` |
| R23 | No-cash criterion for mixtures of constant bets and of sub-Gaussian tests | staged | S3 | proved | `ForLMLExplore/OnlineLearning/Betting/Domination.lean`, `ForLMLExplore/OnlineLearning/Betting/Mixture.lean`, `ForLMLExplore/MeasureTheory/Integral/MixtureLimit.lean` |
| R24 | Leverage, opportunistic leverage and portfolios of two strategies | paper | | proved | `WAR2026/Leverage.lean`, `WAR2026/LeverageMeasurable.lean`, `WAR2026/DefinitionB_4.lean`, `WAR2026/LemmaB_3.lean`, `WAR2026/Fact1.lean`, `WAR2026/Fact2.lean` |
| R25 | Beta and Robbins mixing distributions on the bet fractions | paper | | proved | `WAR2026/Mixtures.lean`, `WAR2026/MixturesProb.lean` |

## Notes

- R1: LMLExplore's `Probability/Kernel/Condexp.lean` has the same statement under the same name.
- R2: `HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep` is in LMLExplore's
  `Probability/Moments/SubGaussian/Basic.lean` with the same hypotheses.
  `HasCondSubgaussianMGF.lintegral_mul_exp_le` is the sub-Gaussian case of LMLExplore's
  `LMLExplore.HasCondMGFBound.lintegral_mul_exp_le`, through
  `hasCondMGFBound_iff_hasCondSubgaussianMGF`. `HasSubgaussianMGF.lintegral_mul_exp_le_of_indep`,
  which needs no `StandardBorelSpace`, is additional: it stays, re-proved on top of LMLExplore.
- R3: `supermartingale_integral` and `supermartingale_integral_of_integrable` are in LMLExplore's
  `Probability/Martingale/Mixture.lean` with the same statements.
  `exists_ae_tendsto_setIntegral_of_supermartingale` is additional; it goes with R23, its only
  user.
- R4: Tau Ceti's `chiSquaredMeasure` takes a real degree and is defined by its density; the local
  `chiSquareMeasure (k : ℕ)` is `gammaMeasure (k / 2) (1 / 2)`, which Tau Ceti's
  `chiSquaredMeasure_eq_gammaMeasure` identifies with it. The headline
  `tendstoInDistribution_hindsightLogWealth` names `chiSquareMeasure 1`: moving it to
  `chiSquaredMeasure 1` changes its statement up to that equality, so the bump decides whether to
  keep the local definition, defined as Tau Ceti's.
- R5: Tau Ceti's `mgf_id_gammaMeasure` and `integrableExpSet_id_gammaMeasure` give the local
  `integral_exp_mul_gammaMeasure`, `integrable_exp_mul_gammaMeasure` and
  `not_integrable_exp_mul_gammaMeasure`.
- R6: Tau Ceti's `gaussianReal_map_sq` states `(gaussianReal 0 1).map (· ^ 2) = chiSquaredMeasure 1`,
  and the uniqueness of a law with a moment generating function finite near `0` is
  `TauCeti.Measure.ext_of_mgf`. The Gaussian integrals of `exp (t x²)` in the local file are steps
  of the local proof.
- R7: ReinforcementLearning 4.1 (Robbins–Siegmund) states its processes in `ℝ≥0` with `condLExp`;
  the convergence of nonnegative supermartingales is its case `a = b = c = 0` and the last step
  of its proof. Port it in the form Robbins–Siegmund calls, with Mathlib's `Supermartingale`, a
  measurable limit, and `∫⁻ ofReal (lim) ≤ ofReal (∫ V 0)`. LMLExplore's namespace is
  `LMLExplore`, not the local `MeasureTheory`.
- R8: OnlineLearning 16.4 asks for the betting wealth `∏_{s<t} (1 + β_s (Z_s - μ))` as a
  nonnegative martingale, for `Z_t ∈ [0, 1]` with `E[Z_t | ℱ_t] = μ` and predictable bets in
  `[-1/(1-μ), 1/μ]`: conditional mean only, no independence, no identical laws. The local
  `supermartingale_wealth` (in `SumSquares.lean`, R19) assumes observations i.i.d. along the
  filtration and gives a supermartingale. The port proves the martingale under the conditional
  mean and derives the supermartingale from it. `fractionRange m` is 16.4's range of bets. The
  other wealth processes of `Wealth.lean` (constant bets, mixtures, hedged, best in hindsight,
  regret, sub-Gaussian tests) are the definitions R19–R23 use, and go with this item. The
  nonnegativity lemmas hold for `m ∈ [0, 1]`, with Lean's `1 / 0 = 0`. Namespace
  `LMLExplore.OnlineLearning` (the OnlineLearning roadmap's convention), not the local
  `Learning.Betting`.
- R9: Mathlib has tightness (`IsTightMeasureSet`) but no Landau notation in probability.
- R11: the central limit theorem and the strong law are Mathlib's
  (`tendstoInDistribution_inv_sqrt_mul_sum_sub`, `strong_law_ae`). The item restates them for
  variables given by their laws (`HasLaw`), and adds Slutsky with deterministic factors along any
  countably generated filter, beside Mathlib's `TendstoInDistribution.add_of_tendstoInMeasure_const`.
- R12: `supermartingale_of_setLIntegral_succ_le` of `IndepIncrements.lean` is in LMLExplore's
  `Probability/Martingale/Basic.lean`, same statement and name. The new content is the freezing lemma
  `setLIntegral_comp_of_indep`, `Indep.comap_comp`, and the criterion for Markov-type updates
  `supermartingale_of_lintegral_le`. R1 combined with LMLExplore's
  `ae_trim_map_condExpKernel_eq_of_indep` gives a second proof of the freezing lemma.
- R13: the exponential supermartingales of `SubgaussianSum.lean` are in LMLExplore
  (`supermartingale_exp_sum_mul_of_hasCondSubgaussianMGF`,
  `supermartingale_exp_sum_of_lintegral_mul_exp_le`), and the Identification roadmap's Layer 4.2
  owns them. The new content is the two almost sure statements, `ae_exists_tendsto_sum_mul`
  (convergence on finite quadratic variation) and `ae_forall_abs_sum_mul_le` (`o` of the quadratic
  variation), with their `_of_indep` and `_of_lintegral_le` forms. They use R7.
- R14: Mathlib has Hoeffding's inequality for independent sub-Gaussian sums
  (`measure_sum_range_ge_le_of_iIndepFun`); the item adds the almost sure form through
  Borel–Cantelli.
- R15: LMLExplore's `Analysis/SpecialFunctions/Log/InvMulLogSq.lean` has explicit tail bounds for
  `∑ 1 / (t log² t)`, not the divergence of `∑ 1 / (n log n)`.
- R16: LML's `SequentialLearning/README.md` lists `Environment.const` as missing. The local
  definition is `Environment.bandit (Kernel.const 𝓐 μ)`, and its run lemmas follow LML's naming
  (`IsAlgEnvSeq.<conclusion>_const`). The item may belong to LML rather than LMLExplore.
- R17: Mathlib has Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`), from which the item derives
  the `1/4`-sub-Gaussianity of `x - m` and of `(x - m)² - σ²` under a law on `[0, 1]`.
- R18: `ktFraction C m X n = (1/2 + ∑_{k<n} (X k - m)) / (C (n + 1))` is the Krichevsky–Trofimov
  bettor of OnlineLearning 13.2 (`β_t = ∑_{s<t} c_s / (t + 1)`), with an initial bet and a scale.
  The item and its null asymptotics (R21) are the testing form and do not advance 13.2, which is
  about regret. `ktFraction_mem_fractionRange` carries the correction of erratum E1 (`C ≥ m/2`);
  the correction of erratum E2 (hedging) is the eventually-in-range criterion
  `tendsto_wealth_zero_of_isBigOmegaAE_of_eventually_mem` of R19.
- R19: the criteria are stated for observations i.i.d. along a filtration (`X n` measurable for
  `ℱ (n + 1)`, independent of `ℱ n`, with law `P`), which covers plug-in strategies
  (`pastFiltration`, R18) and runs of LML algorithms in `Environment.const` (R16).
- R23: `MixtureLimit.lean` is the measure-theoretic core: almost sure limits of mixtures
  `∫ F l n ∂π(l)` that concentrate at a point, with no betting in it.

## Proposed targets

### S1. Asymptotics in probability

Suggested home: `LMLExplore/Probability/`.

1. **Landau notation in probability** [vdV98, §2.2]. For random variables `X : ι → Ω → E` in a
   normed space, a rate `a : ι → ℝ` and a filter `l`, define:
   - `X = O_p(a)`: for every `ε > 0` there is `C` with `P(‖X i‖ > C |a i|) ≤ ε` eventually along `l`;
   - `X = o_p(a)`: for every `c > 0`, `P(‖X i‖ > c |a i|) → 0` along `l`;
   - `X = Ω_p(a)`: for every `ε > 0` there is `c > 0` with `P(‖X i‖ < c |a i|) ≤ ε` eventually;
   - the almost sure forms: almost surely `X · ω =O[l] a`, and almost surely `a =O[l] X · ω`.

   Prove their API: monotonicity in the rate, products and powers, invariance under almost sure
   equality, composition with a map tending to `l`, the implications from the almost sure forms,
   `o_p` from convergence in probability to `0`, `O_p` from convergence in distribution of
   `X i / a i`, and `Ω_p` from convergence in distribution of `X i / a i` to a law with no atom at
   `0` (portmanteau).
2. **Series of order Ω_p** [WAR26, Theorem 2.2]. For nonnegative `Z n = Ω_p(a n)` with `a ≥ 0`
   not summable, `∑ Z n = ∞` almost surely. Its prerequisite is Fatou's lemma for sets,
   `μ (liminf s) ≤ liminf (μ ∘ s)`, absent from Mathlib.
3. **Limit theorems for variables given by their laws.** The central limit theorem and the strong
   law (for pairwise independent variables, as Mathlib's `strong_law_ae`) for variables with a
   given law (`HasLaw`); Slutsky with deterministic factors (`a n X n + b n → a Z + b` in
   distribution when `X n → Z`, `a n → a`, `b n → b`) along any countably generated filter; and
   convergence in measure from almost sure convergence to a constant.

References: [vdV98] A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press
(1998); [WAR26] H. Wang, S. Agrawal and A. Ramdas, *Almost sure null bankruptcy of
testing-by-betting strategies*, COLT 2026, arXiv:2602.08888v2.

### S2. Almost sure behaviour of sums with sub-Gaussian increments

Suggested home: `LMLExplore/Probability/Martingale/` and `LMLExplore/Probability/Moments/`.
Consume the exponential supermartingales of the Identification roadmap's Layer 4.2 and the
convergence of nonnegative supermartingales (ReinforcementLearning 4.1).

1. **Freezing lemma and independent increments.** For `Y` independent of a σ-algebra `m`, `W`
   `m`-measurable with values in any measurable space, `F ≥ 0` jointly measurable and `A ∈ m`:
   `∫⁻ ω in A, F (W ω, Y ω) ∂μ = ∫⁻ ω in A, ∫⁻ y, F (W ω, y) ∂(μ.map Y) ∂μ`. Deduce that an adapted
   nonnegative process with `V (n + 1) = Φ n (Z n, Y n)`, `Z n` measurable for `ℱ n`, `Y n`
   independent of `ℱ n` and `∫⁻ y, Φ n (Z n, y) ∂(μ.map (Y n)) ≤ V n` is a supermartingale.
2. **Martingale strong law for conditionally sub-Gaussian increments** [HH80, Chapter 2; Fit05].
   For `Y n` measurable for `ℱ (n + 1)` and conditionally `c`-sub-Gaussian given `ℱ n`, and `w`
   predictable, with `T n = ∑_{k<n} w k * Y k` and `A n = ∑_{k<n} (w k)²`:
   - almost surely on `{A n converges}`, `T n` converges;
   - almost surely, for every `ε > 0` there is `C` with `|T n| ≤ C + ε A n` for all `n`, so that
     `T n = o(A n)` on `{A n → ∞}`.

   Derive both from the exponential supermartingales, and state them also for independent
   sub-Gaussian increments on any measurable space.
3. **Almost sure Hoeffding rates.** For independent `c`-sub-Gaussian `Y k` and levels `b n ≥ 0`
   with `∑_n exp (-(b n)² / (2 n c)) < ∞`, almost surely `|∑_{k<n} Y k| < b n` eventually
   (Hoeffding's inequality and Borel–Cantelli). Deduce `∑_{k<n} Y k = O(√(n log n))` almost
   surely, and the conditionally sub-Gaussian form along a filtration (Azuma–Hoeffding).

References: [HH80] P. Hall and C. C. Heyde, *Martingale Limit Theory and Its Application*,
Academic Press (1980); [Fit05] P. J. Fitzsimmons, *SLLN for martingales*, lecture notes (2005).

### S3. Testing by betting under the null

Suggested home: `LMLExplore/OnlineLearning/Betting/` (namespace `LMLExplore.OnlineLearning`),
beside the betting martingale of OnlineLearning 16.4. Consume S1, S2 and the environment of S5.

1. **Setting.** Observations `X n ∈ [0, 1]` i.i.d. along a filtration `ℱ` (`X n` measurable for
   `ℱ (n + 1)`, independent of `ℱ n`, with law `P` of mean `m`), and `ℱ`-predictable bet fractions
   in `[-1/(1-m), 1/m]`. Predictable plug-in strategies (`σ(X 0, …, X (n - 1))`) and runs of LML
   algorithms in the i.i.d. environment are the two instances. For laws on `[0, 1]` with mean `m`:
   `m ∈ [0, 1]`; the variance is positive iff `P ≠ δ_m`, and then `m ∈ (0, 1)`; `x - m` and
   `(x - m)² - σ²` are `1/4`-sub-Gaussian.
2. **Sum-of-squares criterion** [WAR26, Theorem 2.1, Corollary 2.4, Theorem 5.2]. Under
   `P ≠ δ_m`, almost surely the wealth tends to `0` iff `∑ λ n² = ∞` or some bet loses everything,
   and otherwise it has a positive limit. Fractions of order `Ω_p(n^(-1/2))` or
   `Ω_as((n log n)^(-1/2))` go bankrupt. When `X n - m` is conditionally `1`-sub-Gaussian given
   `ℱ n`, the sub-Gaussian test `exp (∑_{k<n} ((X k - m)² - (X k - λ k)²) / 2)` with predictable
   alternative means `λ` converges almost surely, to `0` iff `∑ (λ n - m)² = ∞`.
3. **Classical strategies** [OP16; WSR24; WAR26, Propositions 2.5–2.8]. The Krichevsky–Trofimov,
   GRAPA, approximate GRAPA and predictable hedging strategies: their ranges, the null limits in
   distribution of `√n λ n`, and their null bankruptcy.
4. **Mixtures** [WAR26, Theorems 3.1, 5.3]. For a prior `π` on the range of fractions, the mixture
   of the constant-bet wealths converges almost surely to `π {0}`, and so tends to `0` iff `π` has
   no atom at `0`. For a `1`-sub-Gaussian null of mean `m` and a prior `π` on the alternative
   means, the mixture of sub-Gaussian tests converges almost surely to `π {m}`. The
   measure-theoretic core
   is an almost sure limit for mixtures `∫ F l n ∂π(l)` that concentrate at a point.
5. **Best constant bet in hindsight** [WAR26, Theorem 5.1]. A deterministic analysis of
   `λ ↦ ∑_{k<n} log (1 + λ y k)` locates its maximizers and its value when
   `∑ y k = O(√n log n)` and `∑ (y k)² - n σ² = O(√n log n)`. Under the null,
   `2 log sup_λ W^λ_n → χ²₁` in distribution, and the log-regret of a strategy whose wealth tends
   to `0` is unbounded.

References: [WAR26]; [OP16] F. Orabona and D. Pál, *Coin betting and parameter-free online
learning*, NeurIPS 2016; [WSR24] I. Waudby-Smith and A. Ramdas, *Estimating means of bounded
random variables by betting*, J. R. Stat. Soc. Ser. B 86 (2024); [RGVS23] A. Ramdas,
P. Grünwald, V. Vovk and G. Shafer, *Game-theoretic statistics and safe anytime-valid inference*,
Statistical Science 38 (2023).

### S4. Elementary bounds on the logarithm

Suggested home: `LMLExplore/Analysis/SpecialFunctions/Log/`.

1. **Bounds on `log (1 + x)`.**
   - `x - x² ≤ log (1 + x) ≤ x` and `|log (1 + x) - x| ≤ x²` for `x ≥ -1/2`;
   - `log (1 + x) ≤ x - x² / (2 (1 + M))` for `-1 < x ≤ M`, and equivalently
     `1 + x ≤ exp (x - x² / (2 (1 + M)))` on `[-1, M]`;
   - `|log (1 + x) - x + x² / 2| ≤ 2 |x|³` for `|x| ≤ 1/2`, from Mathlib's
     `Real.abs_log_sub_add_sum_range_le`.
2. **Bertrand series.** `∑ 1 / (n (log n)^p)` converges iff `p > 1`, by Cauchy condensation
   (Mathlib's `summable_condensed_iff_of_nonneg`). The case `p = 1` is used here; LMLExplore's
   tail bounds for `p = 2` (`InvMulLogSq.lean`) sit beside it.

### S5. Environments with action-independent feedback

Suggested home: `LMLExplore/SequentialLearning/Environments/`, with LML's naming conventions.

1. **The i.i.d. environment.** `Environment.const μ`, the environment with no observation whose
   feedback has law `μ` whatever the action, is `Environment.bandit (Kernel.const 𝓐 μ)`; LML's
   `SequentialLearning/README.md` lists the name as missing. More generally, take
   `Environment.banditSeq` with constant kernels `Kernel.const 𝓐 (μ n)`.
2. **Its runs.** For every run (`IsAlgEnvSeq`) of any algorithm in these environments:
   - the feedbacks are independent with laws `μ n` (`iIndepFun`, `HasLaw`), i.i.d. for
     `Environment.const`;
   - the feedback of round `n` is measurable for `filtrationAction (n + 1)` and independent of
     `filtrationAction n`;
   - the feedback lies almost surely in every set of full `μ n`-measure.
