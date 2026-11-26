# Scalable original geometry pilot

**Status: the six cell05 owners passed normal compilation, independent kernel
replay, and full owned-declaration audit on P1. The seven cell12 candidates
remain source only. No complete cell or P2.6 acceptance is claimed.**

The completed cell05 run, exact source/object bundle, local evidence recheck,
and scope/performance report are under
`docs/verification/20261126-p26/scalable-geometry-cell05/`. The run verified
18 steps and 2,054 owned declarations in 319.436 seconds of summed step time;
its maximum measured Lean process-tree RSS was 2,831,249,408 bytes.
The frozen `SOURCE_MANIFEST.json` records the original source-only generation
event; subsequent acceptance is recorded separately in `LOCAL_EVIDENCE_CHECK.json`.

The pilot preserves the original packed inputs, `SourceJson` parser, rational
decoder, `GeometryRow` schema, field order, vertex order, and source tokens.
It changes the ownership and import structure of candidate certificates.

## The bounded experiment

| Cell | New leaf coverage | Assembly | New owners |
|---|---|---|---:|
| 05 | Rows 0–7 and 8–15 | A binary node joining rows 0–15 | 6 |
| 12 | Rows 0–7, 3296–3303, and 6592–6599 | Three independent stress leaves | 7 |

Each row retains the previously accepted small parser/field-decoder proof
pattern. Eight rows share one parser owner and one typed owner. The typed
owner imports just its matching parser leaf and `ArchiveRationalChars`.
It does not import a complete `SimplicesValue` or a previous typed prefix.
The binary node imports two typed leaves and composes their original parser
transitions, accumulator order, and `List.mapM` decoding equations.

The full source graph has 13 new owners and 10 existing supplier owners. A
single-cell phase needs nine existing suppliers. The two cell-specific raw
owners are `ArchiveGeometryData05` and `ArchiveGeometryData12`; the eight
generic suppliers are shared. Existing suppliers must be reused byte for byte.

The row-shape lemmas use the literal upper bounds 28 (cell05) and 140 (cell12),
as well as the row's explicit nine-vertex and ten-factor sizes. Their statements
are deliberately local: the vertex-count bounds have not yet been transported
through a complete decoded geometry array. They imply no determinant, volume,
coverage, overlap, or integral fact.

## Why this changes the scaling

The earlier typed owners each import the whole parser array and the preceding
typed owner. Extending that structure repeatedly loads a growing collection of
unrelated certificates. Here every typed leaf has a fixed local project import
closure. A complete array can be assembled by binary nodes, with logarithmic
import-chain depth and fixed fan-in. The final node necessarily retains all
leaf dependencies; no dependency is hidden or dropped.

This pilot measures whether grouping eight rows per owner keeps individual
normal and kernel steps within their resource limits. Its cell05 timing does
not establish a speedup over another cell or predict full-project runtime.
The previous small proof granularity is preserved within each owner, so no
large monolithic `decide` replaces the original parser/decoder proof boundary.

These leaves and the composition node passed. The next complete migration
candidate remains cell05: seven row leaves, balanced assembly, independent leaves
for vertices/vertex values/faces/facet indices, and unchanged top-level field
and parser binding. Only after those proofs pass can a complete cell05 decode
or its full shape theorem be asserted. Cell12's three separated locations test
large packed-input offsets and the actual final-array delimiter before a full
large-cell generation is attempted.

## Reproduction and verification

`generate_pilot.py` reads the exact original files from
`/workspace/p26-original-inputs`, checks their bytes and SHA-256 against the
existing `archive-v4/INPUT_PATHS.json`, and emits candidate Lean sources locally.
It reuses the reviewed raw-span planner and parser fragments. The vendored
`row_templates.py` is the prior field-wise row renderer adapted only to take
its quotation context as an explicit argument; `quotation.py` is unchanged.
No host result is a Lean proof.

`SOURCE_MANIFEST.json` freezes the generated sources, source input identities,
direct imports, row intervals and raw spans. `SUPPLIER_PINS.json` freezes the
required existing source/object identities. Eight generic suppliers have
matching historical normal/kernel acceptance. The original v1 package retained
both raw-data object pins from P1's strict ArchiveCore dependency context while
their individual raw-owner kernel receipts were being recovered.

`RAW05_EVIDENCE_COMPLETION.json` records the subsequent recovery of cell05's
normal compilation, independent kernel replay, and full owned audit for exactly
the same source/object bytes. The complete prior evidence, source, object, and
original JSON are in
`docs/verification/20261126-p26/scalable-geometry-cell05/raw05-supplier-evidence.tar.xz`.
All 74 listed members were checked, including the successful kernel command and
the one-declaration owned inventory with an empty axiom set. The v2 supplier
registry pins all nine historical supplier receipts. Independent review then
found that raw05's historical kernel context used different object bytes for
`ArchivePackedLoader` and `PackedChars`, despite identical source bytes. The
historical raw05 receipt alone therefore does not establish compatibility in
the pilot's actual dependency context.

`verify_raw05_context.py` and `RAW05_CONTEXT_CHECK_PLAN.json` provide a separate
single-command raw05 kernel check using the original pilot's exact `cwd`,
`LEAN_PATH`, and checker path. The check freezes the original 111 evidence
members, original archive, nine supplier source/object and sidecar inventories,
and runtime binaries before and after execution. The combined supplier-context
claim must include this addendum; the original run's closed boolean alone is
insufficient. `inspect_raw05_context_addendum.py` checks that separate join.
The main-bundle inspector reports its narrower receipt scope explicitly.

Cell12's raw-owner receipt remains pending. The original v1 registry is retained
under `history/v1/`; no Lean was executed merely to recover the historical evidence.

`prepare_verifier.py` freezes the verifier and creates all 13 full owned audit
sources locally. Each audit compares the serialized inventory with the entire
environment inventory for its target, prints every owned type and transitive
axiom set, and rejects unsafe, partial, axiom, or truncated declarations.
The permitted inherited axioms are `propext`, `Classical.choice`, and `Quot.sound`.

Install the exact supplier bytes into `STAGE/suppliers/project/ImbalancedChen`
and `STAGE/suppliers/objects/ImbalancedChen`. The driver verifies and links/copies
them into a **single** `STAGE/objects/ImbalancedChen` namespace. It never relies
on partial namespace directories merging across `LEAN_PATH` roots.

Executed P1 first phase (existing supplier installation is required):

```bash
python3 STAGE/tools/p26/scalable/verify_pilot.py \
  --stage STAGE --phase cell05 \
  --toolchain-bin /workspace/toolchains/lean-4.33.0-rc1-linux/bin \
  --mathlib /workspace/blue-member-build/.lake/packages/mathlib \
  --mathlib-packages /workspace/blue-member-build/.lake/packages \
  --rss-gib 6 --wall-seconds 900
```

The default P2 toolchain and Mathlib locations remain in the driver; explicit
flags can select a compatible pinned installation. The Lean commit and complete
Mathlib commit are checked before execution. Every target executes normal,
independent `leanchecker`, then owned audit. Failure stops the phase. Successful
steps are reused only with matching source, object, audit, supplier manifest,
toolchain, and unchanged log bytes. The cell12 stress phase is selected by
`--phase cell12`; it does not require recomputing accepted cell05 targets.

The driver does not author Lean sources, compile suppliers, modify the parser,
or claim that these finite leaves finish P2.6.
