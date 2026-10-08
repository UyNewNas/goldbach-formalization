# Imbalanced Chen formalization

Work toward a Lean formalization of *Transferring quantitative Chen bounds to imbalanced semiprime representations* (8 October 2026).

## Verification status

At commit `9d3965f8bfa82012172deb837ac09f7d04e8ec3a`, the twenty-five-module checkpoint compiled, bundled `leanchecker` replayed every `ImbalancedChen.*` module and the root, and the transitive axiom audit passed for 608 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. [Successful CI](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37772490738). This verifies the stated lemmas and conditional transfers; the manuscript's main analytic theorem is **not formally verified**.

- `ImbalancedChen/Counting.lean`: prime-indexed finite representation sets, exact good/bad partition, subtraction and a conditional finite transfer lemma. The initial count excludes receiver 1; the separate Multiplicity module supplies the receiver-one correction.
- `ImbalancedChen/Constants.lean`: exact rational endpoint arithmetic and logarithmic inequalities, reusing mathlib's proved logarithm bound. This does not certify the integrals from which the quoted numbers originate.
- `ImbalancedChen/Multiplicity.lean`: exact multiplicity and receiver-one correction.
- `ImbalancedChen/AsymptoticTransfer.lean`: conditional epsilon transfer, with all analytic estimates explicit.
- `ImbalancedChen/RationalPowers.lean`: exact real-exponent equivalence and literal additive representation witnesses.
- `ImbalancedChen/OrderedBad.lean`: unique ordered prime factors and exact identification of the bad count.
- `ImbalancedChen/NumericalTransfer.lean`: numerical applications with explicit analytic lower/upper estimates.
- `ImbalancedChen/NormalizationGrowth.lean`: proved analytic growth of positive multiples of `N / (log N)^2`.
- `ImbalancedChen/SingularSeries.lean`: convergence and strict positivity of the manuscript's actual Euler product (without a leading factor two), finite correction, and normalization growth.
- `ImbalancedChen/ManuscriptTransfer.lean`: concrete-normalization conditional count and representation endpoints, removing the former growth premise while retaining both analytic count estimates.
- `ImbalancedChen/HalfProductGeometry.lean`: actual bad-factor roughness localization and the exact integral coefficient `log(1/b)`.
- `ImbalancedChen/BadSourceLocalization.lean`: exact bad-source reindexing, retained/discarded cutoff partition, and ceiling-correct real cutoff.
- `ImbalancedChen/LogCutoffError.lean`: proved negligible loss from the actual cutoff `N / (log N)^10`, including the full ceiling error, composed with the retained prime-partner source.
- `ImbalancedChen/HalfProductSource.lean`: exact inclusive half-product sieve source, unique ordered-pair counting including squares, and its prime-partner filter.
- `ImbalancedChen/PowerErrorBudget.lean`: fixed sublinear power-logarithm errors and exact floor/ceiling losses are negligible in the genuine normalization.
- `ImbalancedChen/SieveSourceCoprimality.lean`: actual strict-cap sieve product, primitive congruence and rough-source coprimality, with explicit small-prime-partner correction.
- `ImbalancedChen/ActualSieveGate.lean`: the original logarithmic cutoff eventually clears the exact fifth-root sieve cap, discharging rough-source coprimality conditions.
- `ImbalancedChen/FiniteSieveModel.lean`: genuine mathlib `BoundingSieve` on the actual shifted source, exact reciprocal-totient remainder, and finite upper-Möbius/λ² inequalities.
- `ImbalancedChen/TruncatedSieveLevel.lean`: exact level-squared truncation of the actual λ² main/error sums and a divisor-count coefficient bound.
- `ImbalancedChen/FiniteSieveEuler.lean`: exact finite Euler factorization with the explicit prime-two normalization, and actual Selberg terms on allowed squarefree divisors.
- `ImbalancedChen/CenterPrimeTail.lean`: exact center-prime correction tail, at most five omitted primes at the actual fifth-root cap, and uniform error at most `62 / N^(1/5)` for `N ≥ 1024`.
- `ImbalancedChen/EulerNormalizationLimit.lean`: genuine strict-cap product exhaustion, correction-tail ratios tending to one, and actual sieve-density normalization along positive even centers with the ordinary prime Euler product left explicit.
- `ImbalancedChen/SieveDimensionComparison.lean`: exact density quotients on half-open prime intervals and uniform comparison after excluding center divisors; no logarithmic dimension estimate is assumed.
- `ImbalancedChen/CurvedRegionDiscrepancy.lean`: exact finite discrepancy partitions and a full-carrier curved-boundary transfer with reciprocal-totient mass cost. This does not prove rectangle distribution or boundary lattice-point estimates.
- `ImbalancedChen/TotientReciprocalBudget.lean`: unconditional finite reciprocal-totient sum bound with explicit constant four, applied to the actual curved-boundary logarithmic mass cost.
- `ImbalancedChen/BoundaryGridBudget.lean`: four actual integer-pair collar bounds with explicit rounding and product-fibre multiplicities on a full carrier; awaiting CI. Grid containment and rectangle distribution remain open.
- `docs/PROOF_STATUS.md`: outstanding analytic dependencies and the frontier comparison.

Build: `lake exe cache get && lake build`. The workflow also runs `leanchecker` and a transitive axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

No custom analytic axioms or proof placeholders belong in the verified core. A green core build is not a complete proof of the manuscript or a claim of a new frontier record.

## Reproducibility

Lean and mathlib revisions are pinned in `lean-toolchain` and `lakefile.toml`. The attachment reviewed has SHA-256 `e89d35f219acfbc6018db56b99d7a5c6c70eeeba0a98723fbe1046041ca90fbe`. The companion certificate archive and all 249 payload hashes were preserved and verified. Nine numerical replays, including the full 2,000,000-split extended run, reproduce the stored mathematical results. This confirms numerical reproducibility, not the analytic interpretation or a Lean proof of the certificates. The extended run establishes an upper endpoint below 6.81, not below 6.809; the final 6.786 recombination additionally uses all three disjoint quoted gains.
