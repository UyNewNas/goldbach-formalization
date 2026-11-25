# Canonical wall payment reuse — independent review

**Result: PASS for corrected source reuse and static dependency checks. No Lean verification credit.**

The reviewed prepared payer is `P2CanonicalWallFullResidualPayment.lean`, SHA256 `5e935c38a45cb38cee5d505585beed3d2f38dda0a6ad63eab0ca7245b1687860`, 14229 bytes. The review did not modify Lean files, the selected-source manifest, or any runner, and did not submit a compilation job.

## Fixed-source identity and exact reconstruction

The original was read directly from Git at commit `c6b89774822580c731a236ac66dcd7466ac8a0e6`, path `ImbalancedChen/P2CanonicalWallFullResidualPayment.lean`, blob `275e8208efc77e070314c4b3096cd32f537ed37a`. Its 14159 bytes have SHA256 `87140bcfd3740129e34a728ba544847513c83acc38da9a998eae549c1da83c57`.

The prepared source differs only by:

- Replacing `P2SourceFormPairRoundedSigmaLevel` with the actual retained-trace supplier `P2LowerCanonicalRetainedTrace`.
- Adding the existing `PrimeHistoryLogCoordinates` supplier explicitly.
- Quoting six code occurrences of the existing identifier `universe` as `«universe»`.

Removing the added import, reversing the import replacement, and removing exactly those six identifier quotes reconstructs the original bytes exactly, including line endings. The quotes occur in code rather than comments. No new proof or mathematical hypothesis was introduced. Since the original candidate was not elaborated in this review, this is an exact source reconstruction claim, not an accepted-elaborated-type equivalence claim.

## Missing supplier found and resolved

The first 83-module proposal had removed the only transitive supplier of `primeHistoryTuple` and `primeHistoryTuple_ofFn`. The definitions are at lines 27 and 37 of the already selected `ImbalancedChen/PrimeHistoryLogCoordinates.lean`, SHA256 `d54b85bd4d970154e936afaeff41b1c20889619ad5cffa664caccaf1a0a3ffa6`. They are used by the payer's `canonicalPrefix` and `prefix_ofFn`; `P2LowerCanonicalRetainedTrace` supplies `canonical_subword_of_universe`, not those two names.

The parent added the existing supplier import and regenerated the preflight. This review independently recomputed the corrected graph and checked the definitions of 17 referenced project APIs in reachable sources. The complete declaration-to-source mapping is in `INDEPENDENT_REVIEW.json`. The checked APIs include the exact canonical-prefix tuple identity, canonical retained subword, actual prime-box reciprocal totient factorization, squarefree residual universe, raw and rounded coefficient bounds, full residual-mass estimate, and actual affine-wall strip estimate.

## Corrected dependency boundary

| Check | Independently observed result |
|---|---|
| Main manifest snapshot | `d8985c91e5ffc71b7af5d4bea3a7c3ad3128733caf591dd0b3bc6357d41e66d2` |
| Main selected sources | 280; every selected source hash matches |
| Corrected payer project closure | 93 modules |
| Project import edges and all source hashes | Match regenerated preflight |
| New selections relative to main | `AffinePrimeWallReserve`, `P2CanonicalWallFullResidualPayment` |
| Additional nodes caused by explicit tuple supplier | 10, all already selected in main |
| New external imports relative to main | None |
| Missing project sources / import cycles | None |
| Removed heavy source-form module reachable | No |
| Main manifest changed during review | No |

The main HEAD remained `4d1b2ed5abfe0772a8b3f1c52931a3f6f954cd27` during the check. The reviewed `REUSE_PREPARATION.json` SHA256 is `1c097872f2b678cf12813804eac6878b30ed27251b40ab1879b643f47cff221c`; the regenerated preflight SHA256 is `153da1c121d79ae451cbf6ec44b8c42bf4bba7646721a01f84ff8453532770d5`.

## Formal status and remaining requirement

This review establishes source provenance, reversible compatibility edits, reachable existing project APIs, and the actual dependency graph. It does not establish successful Lean elaboration, strict compilation, official kernel replay, or a complete axiom audit. The reuse packet remains uncompiled at this review.

The payer still has its original meaning: it pays the entire residual-modulus mass for an actual canonical-prefix wall. A proof that all required warm fibres lie in the relevant finite wall covering remains a separate requirement. This review does not close that coverage obligation or all of P3.6.
