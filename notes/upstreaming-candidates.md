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
  - `Probability/Independence/Freezing.lean`: `setLIntegral_comp_of_indep`;
  - `Probability/Martingale/IndepIncrements.lean`: `supermartingale_of_lintegral_le`;
    `Nonneg.lean`: `Supermartingale.exists_ae_tendsto_of_nonneg`; `Mixture.lean`:
    `supermartingale_integral(_of_integrable)`; `SubgaussianSum.lean`:
    `supermartingale_exp_sum_mul`, `ae_exists_tendsto_sum_mul`, `ae_forall_abs_sum_mul_le`
    (a martingale strong law for conditionally sub-Gaussian increments);
  - `Probability/Moments/SubgaussianRate.lean`: `ae_isBigO_sum_range_sqrt_mul_log`;
  - `Probability/SumBigOmegaInProb.lean`: `ae_not_summable_of_isBigOmegaInProb` (any
    non-summable rate), `measure_liminf_atTop_le_liminf` (Fatou for sets: not in Mathlib);
  - `Probability/LimitTheorems.lean`: CLT and SLLN in `HasLaw` form, deterministic Slutsky,
    `TendstoInDistribution.of_map_eq`;
  - `Probability/Distributions/Gaussian/Sq.lean`: `gaussianReal_map_sq`, and MGF uniqueness
    `Measure.ext_of_mgf_eq` (copied from LMLPapers; better in a `Moments/` file);
  - `Analysis/SpecialFunctions/Log/OneAdd.lean`, `Log/Summable.lean`
    (`Real.not_summable_inv_mul_log`), `Analysis/Asymptotics/SpecificAsymptotics.lean` (Cesàro,
    unused by the final proofs; could be dropped).

## LML

* `Environment.const` and its run lemmas (`SequentialLearning/ObliviousEnv.lean`, from
  LMLPapers; LML's `SequentialLearning/README.md` lists the name as missing).
* `Betting/Wealth.lean`, `Betting/Strategies.lean`: wealth processes, KT, GRAPA, aGRAPA and
  hedging strategies (from LMLPapers).
* Done in phase 2: `Betting/PastFiltration.lean` (could become a Mathlib `Filtration` constructor),
  `SequentialLearning/ConstEnvFiltration.lean`, `Betting/Null.lean`, the filtration forms of the
  criteria (`Betting/SumSquares*.lean`, `Betting/PlugIn.lean`), the strategies' asymptotics
  (`Betting/{KT,AGrapa,Grapa,ChiSquare}Limit.lean`, `HedgeRate.lean`, `GoodEvent.lean`,
  `StrategyBounds.lean`), mixtures (`Betting/Mixture.lean`), the hindsight analysis
  (`Betting/Hindsight.lean`, `Domination.lean`) and wealth lemmas (`WealthLemmas.lean`).
* Naming: some generic names in `Learning.Betting` (`fixedWealth_nonneg`, `subgaussianTest_pos`,
  `ae_mem_Icc_of_hasLaw`) should be checked against LML before upstreaming.
