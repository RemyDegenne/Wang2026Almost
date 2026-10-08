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
* Planned (phase 2): the freezing lemma for independent variables, supermartingales with
  independent increments, convergence of nonnegative supermartingales, mixtures of
  supermartingales, exponential supermartingales of conditionally sub-Gaussian sums and their
  convergence / little-`o` consequences, a.s. rates `O(√n log n)` from Hoeffding's inequality,
  Fatou's lemma for sets, Cesàro means of `Σ a_k / k`, divergence of `Σ 1/(n log n)`.

## LML

* `Environment.const` and its run lemmas (`SequentialLearning/ObliviousEnv.lean`, from
  LMLPapers; LML's `SequentialLearning/README.md` lists the name as missing).
* `Betting/Wealth.lean`, `Betting/Strategies.lean`: wealth processes, KT, GRAPA, aGRAPA and
  hedging strategies (from LMLPapers).
* Planned (phase 2): the filtration forms of the sum-of-squares criteria and of the `n^{-1/2}`
  criterion, the past filtration of a process and its plug-in strategies.
