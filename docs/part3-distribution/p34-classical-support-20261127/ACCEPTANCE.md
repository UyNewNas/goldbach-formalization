# P3.4 original classical common Poisson support — accepted finite scope

The original common Poisson block now has an accepted classical dyadic support
consumer. Its four explicit original declarations comprise **one definition and
three theorems**. The source retains the actual clipped block and completed
weight, arbitrary signed frequency and the exact physical phase denominator.
Two recorded proof-body expression repairs were needed in the consumer; a
separate unit-cast repair was needed in its boundary example.

**Full P3.4 remains open.** This result establishes finite interval and phase
eligibility, with no new external spectral estimate or amplitude normalization.

## Exact accepted source and result

| Item | Verified value |
|---|---|
| Source commit | `6bafadff2427616abaa8159797b87b816af76d63` |
| Source tree | `3c1c5b3d2c83a036643833e2197289e54ddbdf5f` |
| Cloud task | `job_52c313847b3f46a29ffdfe2ce49b6339` |
| Environment | P1 Private Compiler 32GB, used after P3 and default backup sessions returned `Session terminated` |
| Result | `PASSED`, exit 0, **146/146 stages successful** |
| Project closure | **57 modules: 56 authenticated reused provider objects and 1 newly compiled consumer** |
| Selected kernel replays | **2**, both successful |
| Bound inputs | 69 source/configuration/evidence inputs |
| Direct external objects | 68 objects, 202 parts; all 67 inherited R2 bindings retained |
| Runtime / sampled peak | 240.596 seconds / 4,033,740,800 bytes |

The consumer was strictly compiled in this run. The reused P3.1 integration
core's strict compilation came from the fixed R2 source
`4c213f5d6477aa30e1d4636d5c4fb9d01cf8e188`. Both modules were replayed by the
bundled kernel checker in R4. The remaining 55 dependency compilations were also
reused from R2; the final run did not rebuild all 57 modules.

The [machine-readable acceptance](ACCEPTANCE.json), [actual report](verification/report.json),
[cloud task metadata](verification/cloud-task.json) and
[final checkout provenance](provenance/worktree-provenance.json) record these
identities and distinguish fresh work from reuse.

## Mathematical endpoint

Write `V = 2^j` and `M = V - 1/2`. For the actual block

```lean
commonMBlock J j = Finset.Ico (2^j) (min (2^(j+1)) (J+1))
```

the selected consumer proves:

- `1/2 ≤ M` and `V/2 ≤ M ≤ V`;
- every actual block member satisfies `M < m ≤ 2*M`;
- on that same member, the original completed weight remains
  `exp(2 * π * I * (k1 / (64 * 2^j)) * m)` for every `k1 : ℤ`.

The strict left endpoint includes the original first dyadic block: `j = 0`
gives `M = 1/2`, and `m = 1` belongs to `(M, 2*M]`. No nonempty-block premise was
added; the membership theorem retains the original empty-block behavior.

The strict [boundary file](../../../verification/P34ClassicalSupportBoundary.lean)
passed with the scale at zero, actual `J = 1, j = 0, m = 1` support and signed
phase, and the empty block `J = 0`. The completed phase still uses `64 * 2^j`;
the support scale does not replace the physical phase scale.

The frozen 1106 manuscript correspondence and exact donor identities are in
[SOURCE_INTAKE.json](SOURCE_INTAKE.json) and [ENDPOINT_AUDIT.md](ENDPOINT_AUDIT.md).
The donor segment SHA-256 remains the source gate's reference. Reversing only
the two documented proof-body repairs must recover its exact original bytes.

## Declaration accounting

The selected two-module inventory contains **38 unique compiler records**.

| Owner and origin | Records | Definitions | Theorem constants |
|---|---:|---:|---:|
| New consumer: explicit original declarations | 4 | 1 | 3 |
| New consumer: generated auxiliary records | 2 | 0 | 2 |
| Reused P3.1 common Poisson provider | 32 | 6 | 26 |
| **Total** | **38** | **7** | **31** |

The explicit declarations are `classicalMScale`, `classicalMScale_bounds`,
`commonMBlock_classical_support` and `commonPoissonCompleted_classical_support`.
The generated records are `classicalMScale._proof_1` and
`commonMBlock_classical_support._proof_1_1`. Neither generated records nor the
32 reused provider records count as new manuscript declarations.

[declarations.json](verification/declarations.json) contains all 38 records;
[theorem-types.txt](verification/theorem-types.txt) contains the complete types
and transitive axioms of the 31 theorem constants. Their contents agree with
the raw owner audit. [DECLARATION_ACCOUNTING.json](DECLARATION_ACCOUNTING.json)
preserves the origin distinction. No new historical 32-record comparison is
claimed where the earlier P3.1 inventory was not available locally, and no
cumulative P3.4 union count is inferred by adding this inventory to older totals.

The complete transitive axiom union is `propext`, `Classical.choice`,
`Quot.sound`. No new axiom, `sorry`, `admit`, `unsafe`, `native_decide` or kernel
bypass was introduced. The trust mode remains
`NORMAL_IMPORTED_ENVIRONMENT_TRUST`; the two selected target modules were
replayed, while full external-source kernel replay is outside this claim.

## Evidence preservation and reviews

The exact [verification archive](verification-archive.zip) is **110,278 bytes**,
SHA-256:

```text
0f0c4e31dc0ffd80e101662ca2218dcd65100fc772a74f174d664c6e3f860a04
```

Its [manifest](ARCHIVE_MEMBERS.json) contains 165 members. Every member length
and hash, every one of the 146 stage log hashes and command lines, and the final
source/tree/clean-checkout provenance were independently checked. The published
archive contains the complete logs, including the provenance and final package
checks; selected readable logs are also copied alongside the report.

[SOURCE_PRESERVATION.json](SOURCE_PRESERVATION.json) checks that all 69 accepted
inputs remain byte-identical during evidence publication. No repeated Lean
run is needed for these documentation and evidence-only additions.

The three earlier failures remain available in
[verification-attempts/ATTEMPTS.md](verification-attempts/ATTEMPTS.md): the R1
package-integrity failure, R2 proof-expression failure after 56 successful
provider compilations, and R3 boundary cast failure after the target strict
compile and both replays passed. Their original archives are retained.

The updated Python gate suite passed 12 regression cases. Independent source,
incremental-protocol and final-evidence reviews approved the finite scope and
its evidence quality. See [INCREMENTAL_GATE_REVIEW.md](INCREMENTAL_GATE_REVIEW.md)
and [FINAL_REVIEW.md](FINAL_REVIEW.md). The inherited local import fixture's
missing `LEAN_SYSROOT` setup is retained as an unavailable local fixture in
[CONTINUATION_REVIEW.md](CONTINUATION_REVIEW.md), with no local Lean success
claim; actual cloud import-resolution checks passed.

## Remaining P3.4 boundaries

The original physical level-row attachment through
`Part3OriginalMediumPhysicalE3Block` remains separate. So do the original
nonzero Fricke integral and its genuine radial/Whittaker amplitude identification,
classical A/J spectral estimates and their application ranges/completion,
normalized oldform/ABL dilation, and actual continuous-spectrum Plancherel
normalization. The later R22 source-complete lead remains outside this accepted
scope.

Publication continues on draft [PR #8](https://github.com/UyNewNas/goldbach-formalization/pull/8).
No merge, whole-P3.4 acceptance or board-state promotion is claimed.
