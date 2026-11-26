# Complete cell05: phase1 candidate, workflow v3

This package supplies **15 new source-only owners**: five parser leaves for rows
16–55, five corresponding typed leaves, and five binary assembly nodes. The
already accepted six cell05 pilot owners and their nine suppliers are reused
as **15 exact source/object suppliers**. No old owner is recompiled.

The original JSON is 201042 bytes, with 28 vertices and 56 simplex rows. The
new final node assembles the original `simplices` parser transition, including
its closing array delimiter, and its typed list of 56 rows. Top-level JSON
parsing, complete geometry decoding, complete geometry shape, geometric
meaning and integral claims remain outside phase1.

## Recovery provenance

The local execution environment was cleared before the unpublished v1 package
was uploaded. That lost archive had 299364 bytes and SHA256
`8e583044f314355106423bb4c3d382d905f500896e137868d75aebd90ed1925f`.
Its 15 sources had never run Lean. Earlier review records give their historical
total as 2026333 bytes; the lost files cannot now be compared byte by byte.
The v2 source candidate was reconstructed from the
published scalable generator and original input recovered from the published
raw05 archive. Its 15 new Lean sources total **2026335 bytes**. It is newly
frozen; byte identity with the lost candidate is not claimed. Workflow v3 keeps
those reconstructed 15 sources and their 15 audit sources unchanged.

The 70 published checkpoint files remain unchanged. The recovered capsule has
154 files and retains the 18 accepted pilot steps, 2054 owned declarations,
historical raw05 evidence, and raw05's separate successful kernel check in the
actual pilot dependency context. The original pilot's closure boolean alone
does not establish that context join.

## Package layout and P1 command

The source archive contains `sources/ImbalancedChen/*.lean` and this tools
directory. Extract it to a new, canonical stage directory disjoint from both
supplier roots. The runner installs all accepted suppliers and new sources
into `project/ImbalancedChen`, and accepted objects into a single
`objects/ImbalancedChen` namespace. It writes no Lean source text.

For P1, an intended invocation is:

```sh
python3 /workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-complete/tools/p26/scalable-cell05-complete/verify_phase1.py \
  --stage /workspace/p26-continuation-59264dd64286/scalable-geometry-cell05-complete \
  --supplier-project /workspace/p26-continuation-59264dd64286/scalable-geometry/project \
  --supplier-objects /workspace/p26-continuation-59264dd64286/scalable-geometry/objects \
  --toolchain-bin /workspace/toolchains/lean-4.33.0-rc1-linux/bin \
  --mathlib /workspace/blue-member-build/.lake/packages/mathlib \
  --mathlib-packages /workspace/blue-member-build/.lake/packages \
  --rss-gib 6 --wall-seconds 900
```

P3 uses the same script with explicit host paths. Both hosts must supply the
exact pinned Lean and leanchecker binaries, the pinned Mathlib commit, and all
seven required dependency object roots. Use real canonical toolchain/package
paths: symlink ancestors are rejected. Root schedules all cloud proof jobs;
local preparation does not submit them.

## Receipt and resume rules

Each new owner runs normal compilation, independent `leanchecker --verbose`
replay, and the complete owned declaration/type/axiom audit. Every accepted
step binds `RUN.json → mode-command.json → mode-result.json →
mode-accepted.json` by SHA256. A shared validator is used for initial receipt
checking, resume and export. It checks exact module, mode, argv, original
`object_before` semantics, current stage source/object/audit paths, transitive
project dependency objects, cwd, LEAN_PATH, package roots, compiler identities
and frozen workflow inputs.

Resume uses a new attempt name in the same stage and the same frozen context.
Valid previously accepted steps are reused, including steps from an attempt
that stopped later. Successful normal results remain a no-recompile barrier:
if their object is missing or changed, restore the exact accepted object.
A successful result without its acceptance seal requires evidence recovery.
Accepted seals and SUCCESS/STOPPED index references remain barriers even when
the result file has been lost. A missing or broken referenced chain stops both
preflight and prior lookup before any proof step can be restarted.
Invalid receipt chains and unreceipted existing objects cause an error; the
runner does not fall back to recompiling successful work. Changing source,
workflow or execution context requires a separately reviewed continuation
plan that retains accepted owners as suppliers.

All writable paths, existing ancestors, provider/stage isolation and the
project object namespace are checked before the first stage write. Unknown
objects, unexpected sidecars, symlinks and dangling final symlinks are rejected.
The current supplied Lean invocation is expected to produce only `.olean`.

Completion separately records `accepted_steps`, `newly_executed_steps` and
`reused_steps`. Step RSS is sampled aggregate process-tree RSS, not an MCP
whole-task measurement.

## Evidence export

After a complete successful attempt, run:

```sh
python3 STAGE/tools/p26/scalable-cell05-complete/export_phase1.py \
  --stage STAGE --attempt THE_ACCEPTED_ATTEMPT
```

The exporter calls the same strict validator for all 45 chains, binds each
owner's three modes to the same current object, and checks the current pinned
candidate/supplier manifests. It includes only the 15 new object bodies.
The archive is read back member by member against its manifest, and selected
inputs are compared before and after packing. Context and receipts are checked
again before the export report is written.
Each selected member is emitted as regular file bytes, including source/project
pairs that share an inode after installation; tar hardlink aliases are not used.

The archive remains on the cloud host. Standard output contains only its path,
SHA256, byte count and validation counts. No full archive or base64 payload is
returned automatically.

## Local preparation and checks

`prepare_baseline.py` and `generate_rows.py` only reconstruct source candidates
from published files. `prepare_phase1.py` records the original v2 preparation;
`prepare_revision.py` freezes the reviewed workflow v3 against that immutable
v2 package. `test_workflow.py` uses explicitly synthetic temporary files
and logs to exercise rejection and resume behavior; it never invokes Lean.
Passing these local checks does not accept any of the 15 new mathematical
owners. Until cloud normal/kernel/owned receipts exist, the count remains
**0 of 45 new proof steps**.
