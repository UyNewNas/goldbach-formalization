# Cell00 transport to the original moment and floor formulas

The two new owners passed normal Lean compilation, independent `leanchecker`,
and complete owned-declaration auditing in P1 job
`job_a76482d837894253ab9d04e0efe63e57`. The successful attempt is
`20261126T033929994898Z-c8ce14a3`.

## Proven scope

`HigherMomentsPrefix` proves the equality between the existing finite prefix
evaluator and the unchanged original `rationalMoment`, for degrees at most six.
`Cell00AllOriginalFloorBridge` applies that theorem to all 56 original cell00
rows and all ten factors. The degrees cover the first-moment identity and every
term of the original degree-six logarithmic-gap evaluator.

The result preserves the five original floor clauses, the explicit lower and
strict upper Q80 bounds, and the saved Q96 expression `max(old,new)`. The final
raw-access theorem uses the original row-to-vertex-ID-to-coordinate lookup and
the already proved bounds. It does not replace the original rational moments,
change the row ordering, assume saved-field correctness, or add a floor table.

These owners concern the concrete decoded cell00 arrays. The separately
verified `Cell00ArchiveBridge` has its own evidence and acceptance scope. The
remaining twelve cells, ownership and null-overlap guards, physical integral
lower bound, and complete P2.6 endpoint are not established by this package.

## Verification record

| Item | Count |
|---|---:|
| New normal compilations | 2 |
| New independent kernel checks | 2 |
| Complete owned audits | 2 |
| Reused successful supplier kernel backfills | 2 |
| Accepted proof steps across both attempts | 8 |
| Owned declarations audited, including generated declarations | 21 |

The owned counts are five for `HigherMomentsPrefix` and sixteen for
`Cell00AllOriginalFloorBridge`. Every owned declaration has its complete type
and transitive axioms recorded. The observed axiom union is exactly
`propext`, `Classical.choice`, and `Quot.sound`.

The two backfilled suppliers are `CharacterCore00` and
`P2Winner9HomogeneousRecurrence`. Their independent kernel checks succeeded in
the earlier attempt `20261126T033233770413Z-82b28550`, P1 job
`job_44f9f0a7371b4b16b477abae24876401`. That entire earlier attempt remains
`FAILED_STOPPED` because the subsequent new normal compilation failed during
import resolution. Only its two successful kernel steps are reused. The new
attempt validates their source/object, command, log and dependency-context
identities and does not execute those checks again.

The corrected driver installs the 480 finite suppliers and 224 analytic
suppliers into one complete `ImbalancedChen` object root. It also pins the
515 required external source modules and snapshots their existing objects.
No accepted supplier normal compilation was repeated.

## Portable evidence

- [`evidence.tar.xz`](evidence.tar.xz): 1,558,804 bytes; SHA256
  `fcabdc4628201b85bae1b8a83d3548798f7114c7db69360f56302a80e2cfed6d`.
- [`EXPORT_MANIFEST.json`](EXPORT_MANIFEST.json): 51,025 bytes; SHA256
  `fe21004a9ca02a367eed8050b4d9343f164049a6c2726639a0181c1c3738bfb2`.

The archive contains 92 individually listed and hashed files plus the manifest
itself. It includes the selected four source/object pairs, complete new audit
sources and logs, the eight successful step chains, exact supplier manifests,
runtime identities, original failed normal evidence, and the prior verifier
revision. It intentionally does not duplicate all 704 supplier objects.

All listed members, the external and embedded manifests, and the two new
mathematical source identities were checked again after retrieval. Source-file
comments retain their frozen pre-compilation wording; the current acceptance
state is recorded here and in the evidence, without changing those source bytes.

Lean commit: `62eed1db4d67327ec8120be05f1a1b0847d74561` (4.33.0-rc1).
Mathlib commit: `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**Complete P2.6 remains open.**
