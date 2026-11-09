# Errata of Almost sure null bankruptcy of testing-by-betting strategies

Errors found in the paper while formalizing it, with their corrections. Each entry gives where the
error is (the revision of the paper, the result, the page or equation), the error, the correction,
the declarations that state the corrected form, the kind of error and when it was found. Entries
are numbered `E1`, `E2`, … and never renumbered.

## E1. Proposition 2.5: the KT constant also needs `C ≥ m/2`

- **Where:** arXiv:2602.08888v2, the KT bettor (3) in Section 1 ("where `C ≥ m(1-m)` is an
  appropriate constant"), and Proposition 2.5 in Section 2.3, which uses it.
- **Error:** the first KT bet is `λ_1 = 1/(2C)`, and the bets must lie in `[-1/(1-m), 1/m]` for
  the wealth to stay nonnegative. For `m > 1/2` and `C = m(1-m)`, `λ_1 = 1/(2m(1-m)) > 1/m`:
  after `X_1 = 0` the wealth is `1 - λ_1 m = 1 - 1/(2(1-m)) < 0`. So `C ≥ m(1-m)` alone does not
  make KT a betting strategy, and Corollary 2.4, from which Proposition 2.5 derives the
  bankruptcy of KT, does not apply to it.
- **Correction:** assume also `C ≥ m/2`. With `C ≥ max(m(1-m), m/2)` every KT bet lies in
  `[-1/(1-m), 1/m]`, and the proof goes through.
- **Lean:** `Wang2026Almost.kt_bankrupt` assumes `m / 2 ≤ C` besides `m * (1 - m) ≤ C`.
- **Kind:** missing hypothesis.
- **Found:** phase-1 statement check, 2026-10-08 (commit 2844515).

## E2. Proposition 2.8: the clipped hedging fractions can leave the range of bets

- **Where:** arXiv:2602.08888v2, the hedged wealth (7) and the hedging fraction (8) in Section 1,
  and Proposition 2.8 in Section 2.3, with the sentence before it, which derives it from the rate
  of `λ_n^PrH`.
- **Error:** the hedged wealth (7) needs `λ_n ∈ [0, min(1/(1-m), 1/m))`, but the clipping in (8)
  only gives `λ_n^PrH ∈ [0, C/m]`. When `C (1 - m) > m` (possible with `C ∈ (0, 1)` whenever
  `m < 1/2`), `C/m > 1/(1-m)`, so the bet `-λ_n^PrH` of the second half of the hedge can be below
  `-1/(1-m)`, and the factor `1 - λ_n^PrH (X_n - m)` is negative for `X_n` close to `1`. The
  `n^{-1/2}` criterion (Corollary 2.4), which gives the bankruptcy of each half of the hedge, then
  does not apply to that half. The statement of Proposition 2.8 still holds.
- **Correction:** `λ_n^PrH → 0` almost surely (the variance estimate is consistent), so `-λ_n^PrH`
  is eventually in `[-1/(1-m), 1/m]` almost surely. A version of the criterion for strategies that
  are eventually in range almost surely gives the bankruptcy of the second half of the hedge.
- **Lean:** `Wang2026Almost.hedged_bankrupt` states Proposition 2.8 as in the paper; its proof
  uses `Learning.Betting.tendsto_wealth_zero_of_isBigOmegaAE_of_eventually_mem` for `-λ^PrH`.
- **Kind:** gap in the proof.
- **Found:** phase 2, 2026-10-08 (commit 030ab98).
