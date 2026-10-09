# Upstreaming candidates

Library material of this project meant for Mathlib or LML, with its intended destination.
Updated as phase 2 proceeds.

## Mathlib

* `Wang2026Almost/Mathlib/Probability/AsymptoticsInProbability.lean`: `IsBigOInProb`,
  `IsBigOmegaInProb`, `IsBigOAE`, `IsBigOmegaAE` (from LMLPapers); phase 2 adds monotonicity in
  the rate, squaring, and `Ω_p` from convergence in distribution to a law without atom at `0`.
* `Wang2026Almost/Mathlib/Probability/Distributions/{Gamma,ChiSquare}.lean`: gamma MGF,
  chi-squared distribution (from LMLPapers); phase 2 adds the law of the square of a standard
  Gaussian.
* Done in phase 2 (Mathlib-shaped, namespaces `MeasureTheory`/`ProbabilityTheory`/`Real`):
  - `Probability/Independence/Freezing.lean`: `setLIntegral_comp_of_indep`, `Indep.comap_comp`;
  - `Probability/HasLaw.lean`: `HasLaw.ae_comp`, `HasLaw.hasSubgaussianMGF_comp`,
    `integral_mem_Icc_of_ae_mem`, `integrable_of_ae_mem_of_continuous`,
    `Measure.eq_dirac_of_ae_eq` (small API lemmas, each a candidate for the file of its subject);
  - `Probability/Kernel/Condexp.lean`: `lintegral_comp_condExpKernel`, the freezing lemma for
    the conditional expectation kernel;
  - `Probability/Moments/SubGaussian.lean`: the moment bound of a conditionally sub-Gaussian
    variable at a random `m`-measurable parameter (`HasCondSubgaussianMGF.lintegral_mul_exp_le`,
    and `HasSubgaussianMGF.lintegral_mul_exp_le_of_indep` for independent variables), and
    `HasSubgaussianMGF.hasCondSubgaussianMGF_of_indep`;
  - `Probability/Martingale/IndepIncrements.lean`: `supermartingale_of_setLIntegral_succ_le`,
    `supermartingale_of_lintegral_le`;
    `Nonneg.lean`: `Supermartingale.exists_ae_tendsto_of_nonneg`; `Mixture.lean`:
    `supermartingale_integral(_of_integrable)`, `exists_ae_tendsto_setIntegral_of_supermartingale`;
    `SubgaussianSum.lean`: `supermartingale_exp_sum_mul`, `ae_exists_tendsto_sum_mul`,
    `ae_forall_abs_sum_mul_le` (a martingale strong law for conditionally sub-Gaussian
    increments, `HasCondSubgaussianMGF`), with `_of_indep` versions for independent sub-Gaussian
    increments on any measurable space and `_of_lintegral_le` versions from the moment bound at
    predictable parameters;
  - `MeasureTheory/Integral/MixtureLimit.lean`: a.s. limits of mixtures `∫ F l n ∂π(l)` that
    concentrate at a point (`ae_tendsto_integral_of_ball`), the abstract no-cash criterion;
  - `Probability/Moments/SubgaussianRate.lean`: `ae_eventually_abs_sum_range_lt` (Hoeffding +
    Borel–Cantelli for any level `b n` with `Σ exp(-b n² / (2 n c)) < ∞`) and its corollary
    `ae_isBigO_sum_range_sqrt_mul_log`;
  - `Probability/SumBigOmegaInProb.lean`: `ae_not_summable_of_isBigOmegaInProb` (any
    non-summable rate), `measure_liminf_atTop_le_liminf` (Fatou for sets: not in Mathlib);
  - `Probability/LimitTheorems.lean`: CLT in `HasLaw` form, SLLN for pairwise independent
    variables in `HasLaw` form, deterministic Slutsky along any countably generated filter,
    `tendstoInMeasure_const_of_tendsto`, `TendstoInDistribution.of_map_eq`;
  - `Probability/Distributions/Gaussian/Sq.lean`: `gaussianReal_map_sq`, and MGF uniqueness
    `Measure.ext_of_mgf_eq` (copied from LMLPapers; better in a `Moments/` file);
  - `Analysis/SpecialFunctions/Log/OneAdd.lean` (`log (1 + x)` between `x - x²` and `x` for
    `x ≥ -1/2`, `1 + x ≤ exp (x - x² / (2 (1 + M)))` on `[-1, M]`, second-order Taylor bound),
    `Log/Summable.lean` (`Real.not_summable_inv_mul_log`).

## LML

* `Environment.const` and its run lemmas (`SequentialLearning/ObliviousEnv.lean`, from
  LMLPapers; LML's `SequentialLearning/README.md` lists the name as missing).
* `Betting/Wealth.lean`, `Betting/Strategies.lean`: wealth processes, KT, GRAPA, aGRAPA and
  hedging strategies (from LMLPapers).
* `Betting/Wealth.lean` also has the API of `fractionRange` (compact interval, interior, `0` and
  `[-1, 1]` inside, bound on `|l|`); the nonnegativity lemmas hold for `m ∈ [0, 1]` (Lean's
  `1 / 0 = 0`). `Betting/Null.lean`: consequences of a null distribution on `[0, 1]` (mean in
  `[0, 1]`, moments of all orders, `1/4`-sub-Gaussianity of `x - m` and `(x - m)² - σ²`).
* Beyond the paper: the sub-Gaussian criteria (Theorems 5.2 and 5.3) for observations with
  `X n - m` conditionally `1`-sub-Gaussian given `ℱ n`
  (`sum_sq_criterion_subgaussian_of_hasCondSubgaussianMGF`,
  `ae_tendsto_subgaussianMixtureTest_of_hasCondSubgaussianMGF`).
* Done in phase 2: `Betting/PastFiltration.lean` (could become a Mathlib `Filtration` constructor),
  `SequentialLearning/ConstEnvFiltration.lean`, `Betting/Null.lean`, the filtration forms of the
  criteria (`Betting/SumSquares*.lean`, `Betting/PlugIn.lean`), the strategies' asymptotics
  (`Betting/{KT,AGrapa,Grapa,ChiSquare}Limit.lean`, `HedgeRate.lean`, `GoodEvent.lean`,
  `StrategyBounds.lean`), mixtures (`Betting/Mixture.lean`), the hindsight analysis
  (`Betting/Hindsight.lean`, `Domination.lean`) and wealth lemmas (`WealthLemmas.lean`).
* Naming: some generic names in `Learning.Betting` (`fixedWealth_nonneg`, `subgaussianTest_pos`)
  should be checked against LML before upstreaming.
