# P3 continuation from c509267

## Baseline and scope

The baseline is `c509267dc630d91df33033abde1c484ec86b96ae` on
`codex/p3-formalization-20261123`. The user supplied the successful
80-module, 1,774-declaration strict compilation, kernel replay and axiom
audit result. That receipt is not part of the Git tree; this continuation
keeps the baseline proofs and records its own verification separately.

The frozen manuscript is the 2026-11-06 release at
`chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`.
The earlier equation (24) is the stable label `ana:spectral-polynomial`,
equation (96) in that release. The prime-product target is
`eq:current-PP`, Proposition D.3.

## Implementation plan

1. Reuse `Part3OffDiagonalModuli` to pay the signed progression kernel
   after the whole modulus sum. Keep the same complex modulus weights,
   complete product, coprimality predicate and totient denominator. Keep
   the actual product-equals-target diagonal separate from the divisor
   bound for nonzero differences.
2. Apply that finite bound to the existing labelled proper-power
   residual. Prove its zero fibre, its total mass from the existing
   proper-prime-power count, and its diagonal multiplicity. Connect the
   result to the existing exact prime/von Mangoldt identity.
3. Reuse the existing common-interval Fourier completion and archived
   scalar threshold proofs to extend a full-block exceptional spectral
   estimate to the actual clipped interval and arbitrary positive
   physical weight. Retain each spectral exponent at the threshold,
   and use the exponent cap only on the excess-weight ratio.
4. Strictly compile and kernel-replay the new modules with the original
   pinned toolchain. Audit their complete serialized declaration
   inventories and transitive axioms using the existing audit rules.
   Rebuild only missing dependencies; do not erase or revalidate all
   80 baseline proof objects as part of an incremental run.
5. Review the statements against the manuscript, publish the source and
   incremental receipt, and identify exactly which P3 obligations remain.

## Boundaries

The prime-power payment is a theorem about the actual labelled residual,
not a residual-bound assumption. The spectral extension consumes an
explicit full-block classical estimate and a spectral-parameter bound;
it does not assert that these automorphic inputs have already been
formalized. No ordinary Bombieri--Vinogradov theorem is substituted for
the missing spectral estimate. The frozen manuscript's external
Kuznetsov, ABL, Kim--Sarnak and Pascadi inputs remain visible.

Pascadi's full-block exceptional Theorem J allows the weight threshold
`max(V, Z^2 / V)`. Its common-phase clause and the exact integer interval
endpoints must be preserved. The actual `4*pi` normalization cannot be
dropped when the physical weight is substituted.

## Task ledger

| Task | Owner | Status |
| --- | --- | --- |
| Whole-modulus signed kernel payment | `p3_modulus_payment` | Strict compile and kernel replay passed on Cloud; full inventory pending |
| Actual labelled proper-power residual | `p3_proper_power` | Complete source; development harness passed; actual imports pending |
| Actual box budget to square-root saving | `p3_power_saving` | Complete source; compilation pending |
| Exceptional weight, common interval and two level windows | `p3_spectral_extension` | Complete source; latest full modules pending compilation |
| Dependency reuse, verification, review and publication | root | Independent review complete; incremental CI prepared |

## Compilation continuity

Cloud Compile reached its 128-retained-job limit during this continuation.
Its exposed tools have no archive operation. No other task was cancelled,
and the limit was not modified. The single-module strict/kernel receipt is
preserved in `continuation-20261124/cloud-modulus-receipt.json`.

The new GitHub workflow runs the original pinned Lean and dependencies.
It verifies two disjoint groups, `spectral` and `proper-power`, so a missing
heavy arithmetic dependency does not delay diagnostics for the light
spectral modules. Both groups use the original complete inventory rules.
Only a successful receipt for the exact source hashes is a proof-validation
result; static review, source-only checks and the development harness are
not substitutes for that result.

The proper-power box budget now supplies an explicit `x^(1-a/2)` factor
from a coordinate lower bound `c*x^a` and complete box volume `C*x`.
The spectral adapters now include arbitrary common integer intervals,
both classical level windows, the positive-integer endpoint `m=1`, and
a proof of summability before passing from finite spectral sums to `tsum`.
The actual automorphic input instances and the final uniform P3 assembly
are still separate obligations.

This file is a work ledger, not a completion certificate.
