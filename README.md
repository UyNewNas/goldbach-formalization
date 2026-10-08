# Imbalanced Chen formalization

Work toward a Lean formalization of *Transferring quantitative Chen bounds to imbalanced semiprime representations* (8 October 2026).

## Verification status

GitHub CI has compiled all seven initial core modules and their aggregate root. The subsequent kernel recheck exceeded the job time limit; the transitive axiom audit has not yet run. Focused imports and separately observable verification stages are being tested. The manuscript's main analytic theorem is **not formally verified** by this repository.

- `ImbalancedChen/Counting.lean`: prime-indexed finite representation sets, exact good/bad partition, subtraction and a conditional finite transfer lemma. The initial count excludes receiver 1; the separate Multiplicity module supplies the receiver-one correction.
- `ImbalancedChen/Constants.lean`: exact rational endpoint arithmetic and logarithmic inequalities, reusing mathlib's proved logarithm bound. This does not certify the integrals from which the quoted numbers originate.
- `ImbalancedChen/Multiplicity.lean`: exact multiplicity and receiver-one correction.
- `ImbalancedChen/AsymptoticTransfer.lean`: conditional epsilon transfer, with all analytic estimates explicit.
- `ImbalancedChen/RationalPowers.lean`: exact real-exponent equivalence and literal additive representation witnesses.
- `ImbalancedChen/OrderedBad.lean`: unique ordered prime factors and exact identification of the bad count.
- `ImbalancedChen/NumericalTransfer.lean`: numerical applications with explicit analytic lower/upper estimates.
- `ImbalancedChen/NormalizationGrowth.lean`: proved analytic growth of positive multiples of `N / (log N)^2`; source reviewed, awaiting compilation.
- `ImbalancedChen/SingularSeries.lean`: convergence and strict positivity of the manuscript's actual Euler product (without a leading factor two), finite correction, and normalization growth; source reviewed, awaiting compilation.
- `ImbalancedChen/ManuscriptTransfer.lean`: concrete-normalization conditional count and representation endpoints, removing the former growth premise while retaining both analytic count estimates; awaiting compilation.
- `ImbalancedChen/HalfProductGeometry.lean`: actual bad-factor roughness localization and the exact integral coefficient `log(1/b)`; awaiting compilation.
- `docs/PROOF_STATUS.md`: outstanding analytic dependencies and the frontier comparison.

Build: `lake exe cache get && lake build`. The workflow also runs `leanchecker` and a transitive axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

No custom analytic axioms or proof placeholders belong in the verified core. A green core build is not a complete proof of the manuscript or a claim of a new frontier record.

## Reproducibility

Lean and mathlib revisions are pinned in `lean-toolchain` and `lakefile.toml`. The attachment reviewed has SHA-256 `e89d35f219acfbc6018db56b99d7a5c6c70eeeba0a98723fbe1046041ca90fbe`. The companion certificate archive and all 249 payload hashes were preserved and verified. Nine numerical replays, including the full 2,000,000-split extended run, reproduce the stored mathematical results. This confirms numerical reproducibility, not the analytic interpretation or a Lean proof of the certificates. The extended run establishes an upper endpoint below 6.81, not below 6.809; the final 6.786 recombination additionally uses all three disjoint quoted gains.
