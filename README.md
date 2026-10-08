# Imbalanced Chen formalization

Work toward a Lean formalization of *Transferring quantitative Chen bounds to imbalanced semiprime representations* (8 October 2026).

## Verification status

The initial source files are awaiting their first GitHub CI run. The manuscript's main analytic theorem is **not formally verified** by this repository.

- `ImbalancedChen/Counting.lean`: prime-indexed finite representation sets, exact good/bad partition, subtraction and a conditional finite transfer lemma. The initial count excludes receiver 1; equivalence to the manuscript's Omega convention remains explicit work.
- `ImbalancedChen/Constants.lean`: exact rational endpoint arithmetic and logarithmic inequalities, reusing mathlib's proved logarithm bound. This does not certify the integrals from which the quoted numbers originate.
- `docs/PROOF_STATUS.md`: outstanding analytic dependencies and the frontier comparison.

Build: `lake exe cache get && lake build`. The workflow also runs `leanchecker` and a transitive axiom audit allowing only `propext`, `Classical.choice`, and `Quot.sound`.

No custom analytic axioms or proof placeholders belong in the verified core. A green core build is not a complete proof of the manuscript or a claim of a new frontier record.

## Reproducibility

Lean and mathlib revisions are pinned in `lean-toolchain` and `lakefile.toml`. The attachment reviewed has SHA-256 `e89d35f219acfbc6018db56b99d7a5c6c70eeeba0a98723fbe1046041ca90fbe`. A companion certificate archive has been supplied; its inventory, compatibility and replay are under review.
