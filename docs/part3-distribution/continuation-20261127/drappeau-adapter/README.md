# P3.5 C4 normalization and cubic regular-envelope adapter

**Two components accepted on P1 and GitHub CI at source commit
[`44743fb463011127f66274f197ff38bf4680c192`](https://github.com/UyNewNas/goldbach-formalization/commit/44743fb463011127f66274f197ff38bf4680c192).
Full P3.5 remains OPEN.**

Both environments passed strict compilation, kernel replay of the two owned
modules, actual-import binding, and a complete serialized declaration/type/
transitive-axiom audit. Acceptance covers **28 declarations: 24 theorem records
and 4 definitions**, including two private theorems and four generated helpers.
It does not certify the final P3.5 assembly.

## Mathematical components

| Module | New derivation |
| --- | --- |
| [Part3ActualSpectralTestNormalization](../../../../ImbalancedChen/Part3ActualSpectralTestNormalization.lean) | Positive mode normalization; actual C4 unit tests for all positive scales; actual Fourier summability with degree-28 cost |
| [Part3DrappeauRegularEnvelope](../../../../ImbalancedChen/Part3DrappeauRegularEnvelope.lean) | Cubic test envelope into the existing shell consumer; finite and positive-measure bounds with coefficient `260*E`; proved global L1 before signed exhaustion |

These modules reuse the accepted actual test jets, Fourier budgets, shell
payment and measure exhaustion. They do not prove the outside Bessel theorem
or supply the unresolved native spectral rows. The envelope theorem has its
lower-level transform estimate as an explicit hypothesis; it does not assume
the target bilinear spectral return.

[Exact outside input and manuscript boundary](EXTERNAL_INPUT.md) ·
[Source recovery and existing-work audit](SOURCE_RECOVERY.md) ·
[Completed P2 source inventory](P2_SOURCE_RECOVERY.json)

## Acceptance evidence

| Check | P1 | GitHub CI |
| --- | --- | --- |
| Exact source commit | `44743fb463011127f66274f197ff38bf4680c192` | Same |
| Environment | Pinned prepared environment | Pinned Lake environment; initial project cache miss |
| Formal stages | 35/35 exit 0 | 36/36 exit 0, including Lake build |
| Owned strict compilation / kernel replay | 2/2 each | 2/2 each |
| Complete declaration inventory | 28 | 28, identical |
| Source/configuration hashes checked | 109 | 109 |
| Actual non-owned imported modules bound | 6,695 | 6,695 |
| Observed transitive axioms | `Classical.choice`, `Quot.sound`, `propext` | Same |

P1 task `job_90af6812f8564015839cdb604a4adb2b` succeeded in 378.04 seconds,
with sampled peak memory 4,129,296,384 bytes. It compiled 60 existing project
dependencies before the formal verifier. Those dependencies were not replayed
as owned modules. The local fallback bootstrap stopped after 182 old modules;
it is not counted as an acceptance pass.

[GitHub CI run 45953060136](https://github.com/UyNewNas/goldbach-formalization/actions/runs/45953060136)
succeeded for the same source commit. Root checked both complete downloaded
evidence sets: every stage-log hash and all 109 source/configuration hashes
match, all 28 declaration records and full theorem types agree, and all 6,695
imported module source hashes agree. The reports also record identical owned
object hashes; this comparison does not claim a separate download of object
binaries. A fresh reviewer independently accepted the complete CI artifact
and checked its imported sources against the local pinned source environment.

Readable records:

- [RECEIPT.json](RECEIPT.json): scope, source hashes, environment results and remaining obligations.
- [report.json](report.json) and [CI_REPORT.json](CI_REPORT.json): original verifier reports.
- [declarations.json](declarations.json) and [theorem-types.txt](theorem-types.txt): complete inventory and types.
- [EVIDENCE_CHECK.json](EVIDENCE_CHECK.json), [CI_EVIDENCE_CHECK.json](CI_EVIDENCE_CHECK.json), and [REVIEW.md](REVIEW.md): root comparison and independent review.
- [P1_TASK.json](P1_TASK.json): original task metadata, command and resource observations.

[acceptance-44743fb4.tar.xz](acceptance-44743fb4.tar.xz) preserves every file
member from the original P1 ZIP (119 files) and CI ZIP (44 files), under `p1/`
and `ci/`. It includes all stage logs, actual-import manifests, generated audit
sources, and P1 setup/baseline/source snapshots. The archive is a repack, not a
byte-for-byte copy of either original ZIP container. Every original member's
bytes were checked after repacking; [ARCHIVE_MANIFEST.json](ARCHIVE_MANIFEST.json)
records their hashes and both original ZIP digests.

- Consolidated archive: 1,760,828 bytes; SHA-256 `652acd2ab7c5eb318681a1bf2d024cb9a9d0f39fe116cd776331482758a96d4b`.
- Original P1 ZIP SHA-256: `9959bfa8b1926806957043bf5808ecb1eef18e3bbe33d0f7aed9dde22e4cdf52`.
- Original CI ZIP SHA-256: `ee69e0fc5ba9aad9c563c292d366f7553e82c930ceba4a82972a1462d1430de1`.

## Remaining P3.5 obligations

The six registered native-row sources have not been recovered in the documented
search scope. The actual transforms still need to instantiate the registered
weight-zero C4 estimate, with the printed row factors retained. Actual row
classes must connect to their existing separate cumulative-energy suppliers,
followed by the remaining regular/exceptional/ABL, level/Fourier, six-scale and
physical assembly. These adapters discharge neither the source-recovery
obligation nor those instantiations. This is an availability/interface boundary;
the search and review do not establish a mathematical gap in the manuscript.

P3.5 is not included in the closed-node Draft PR #12. No previously accepted
proof is reclassified by this component receipt.

## Acceptance route

The verifier group is `p35-drappeau-adapter`. The existing GitHub workflow
selects this group on the P3.5 branch. In a prepared pinned checkout:

```bash
python3 verification/verify_part3_continuation.py \
  --group p35-drappeau-adapter \
  --expected-head 44743fb463011127f66274f197ff38bf4680c192 \
  --output-dir .lake/p35-drappeau-verification
```

`--prepared-environment` additionally permits direct use of a prebuilt,
exactly pinned Lean environment without asking Lake to rebuild its imported
objects. Both modes verify every actual imported module's source and object
root, bind the source and object hashes before and after compilation, strictly
compile the owned modules, replay them with the bundled checker, and audit the
complete serialized declaration/type/transitive-axiom inventory.

The only allowed transitive axioms are `propext`, `Classical.choice` and
`Quot.sound`. Imported dependencies retain normal imported-environment trust;
the group is not a replay certificate for the whole dependency graph.

Run the command in a clean checkout of the exact source commit above. The later
evidence-only commit adds these records without changing the accepted Lean,
verifier, workflow or dependency bytes.

The initial import-binding checks, including rejection of a shadowed object
and of a missing owned import, are recorded in
[IMPORT_GUARD_CHECKS.json](IMPORT_GUARD_CHECKS.json). Those scoped checks are not
acceptance evidence for the two Lean modules.
