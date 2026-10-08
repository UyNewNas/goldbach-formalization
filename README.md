# Imbalanced Chen formalization

Work toward a Lean formalization of *Transferring quantitative Chen bounds to imbalanced semiprime representations* (8 October 2026).

## Verification status

At commit `26c128d85f45fd0ddd7719459d56fcb112fc582c`, the thirteen-module checkpoint compiled, bundled `leanchecker` replayed every `ImbalancedChen.*` module and the root, and the transitive axiom audit passed for 238 declarations using only `propext`, `Classical.choice`, and `Quot.sound`. [Successful CI](https://github.com/UyNewNas/goldbach-formalization/actions/runs/37754452855). This verifies the stated lemmas and conditional transfers; the manuscript's main analytic theorem is **not formally verified**.

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
- `ImbalancedChen/HalfProductSource.lean`: exact inclusive half-product sieve source, unique ordered-pair counting including squares, and its prime-partner filter; new module awaiting CI.
- `ImbalancedChen/PowerErrorBudget.lean`: fixed sublinear power-logarithm errors and exact floor/ceiling losses are negligible in the genuine normalization; awaiting CI.
- `ImbalancedChen/SieveSourceCoprimality.lean`: actual strict-cap sieve product, primitive congruence and rough-source coprimality, with explicit small-prime-partner correction; awaiting CI.
- `ImbalancedChen/ActualSieveGate.lean`: the original logarithmic cutoff eventually clears the exact fifth-root sieve cap, discharging rough-source coprimality conditions; awaiting CI.
- `docs/PROOF_STATUS.md`: outstanding analytic dependencies and the frontier comparison.

Build: `lake exe cache get && lake build`. The workflow also runs `leanchecker` and a transitive axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

No custom analytic axioms or proof placeholders belong in the verified core. A green core build is not a complete proof of the manuscript or a claim of a new frontier record.

## Reproducibility

Lean and mathlib revisions are pinned in `lean-toolchain` and `lakefile.toml`. The attachment reviewed has SHA-256 `e89d35f219acfbc6018db56b99d7a5c6c70eeeba0a98723fbe1046041ca90fbe`. The companion certificate archive and all 249 payload hashes were preserved and verified. Nine numerical replays, including the full 2,000,000-split extended run, reproduce the stored mathematical results. This confirms numerical reproducibility, not the analytic interpretation or a Lean proof of the certificates. The extended run establishes an upper endpoint below 6.81, not below 6.809; the final 6.786 recombination additionally uses all three disjoint quoted gains.
