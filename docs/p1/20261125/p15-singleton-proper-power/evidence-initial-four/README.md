# Accepted original singleton inputs: four owners

These four owners passed normal compilation, named kernel checking, and the
complete environment-owned declaration/type/axiom audit at source commit
`d20acdf13882e17d97833064f5e7c54f3192b03c` in P1 task
`job_1ed0e0c8d4ee466f8444aff044abe510`:

| Owner | All owned declarations | Public declarations |
|---|---:|---:|
| `P1OriginalSingletonPointwiseData` | 25 | 25 |
| `P1Full87TrueDPolicyDelta` | 11 | 11 |
| `P1Full87TrueDUnitBound` | 6 | 3 |
| `P1OriginalHistoricalMiddlePointwiseData` | 5 | 5 |
| Total | 47 | 44 |

The axiom union is exactly `Classical.choice`, `Quot.sound`, and `propext`.
There are no owned axiom declarations or `sorryAx`. All four kernel commands
exited with code zero. The unchanged Batch13 audit checks complete canonical
environment ownership, including private declarations; source declaration
counts alone are not used as audit coverage.

The active four-owner closure has 288 project sources; the committed source
manifest still checks all 316 project sources. Existing dependencies passed
stock readiness without compilation or fingerprint changes. The earlier
23-owner actual fourth/fifth mean chain was not rebuilt.

`collect_public_acceptance.py` revalidates the original retained receipts with
the same immutable `audit_valid` API. It checks current source and object
bindings, original normal commands, kernel commands, audit logs, complete
owned inventories, and before/after context equality. P1 task
`job_aeb236a4703943c38eab3c07317c6b5f` ran that read-only collector successfully.
Only aggregate counts, public module identities, and cryptographic receipt
bindings are exported in `PUBLIC_ACCEPTANCE.json`; raw logs and declaration
types stay in the compiler environment.

This acceptance is specific to the four listed source hashes. The two
proper-power comparison owners and the subsequent Atlas owners still require
their own acceptance. Whole P1.5 and whole P1 are not marked complete.
