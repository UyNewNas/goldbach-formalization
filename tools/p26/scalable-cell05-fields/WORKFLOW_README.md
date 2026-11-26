# Strict workflow for the 73 original field owners

This execution package combines the four frozen authored field batches into
exactly **73 new owners and 219 required proof steps**. It reuses the same 15
published supplier source/object pairs and 154-file evidence capsule as the
reviewed row workflow v3. The source bytes and complete owned audit bytes of
all four batches remain unchanged. No row-phase1 candidate is a supplier here.

`FIELD_WORKFLOW_ADAPTATION.json` and `workflow/v3-to-fields.diff` record the
mechanical changes from reviewed v3: isolated tool directory, manifest names,
73/219 target counts and field-array scope descriptions. The strict receipt,
path, recovery and export checks are retained. The structural receipt format
remains v2; its immutable context identifies this new field verifier and scope.

## Run after root assigns a slot

Extract `fields-73-owner-workflow-v1.tar.xz` into a new canonical stage disjoint
from both supplier roots. For P1, use actual canonical Mathlib paths rather
than the blue-member checkout's symlink aliases:

```sh
python3 STAGE/tools/p26/scalable-cell05-fields/verify_fields.py \
  --stage STAGE \
  --supplier-project /workspace/p26-continuation-59264dd64286/scalable-geometry/project \
  --supplier-objects /workspace/p26-continuation-59264dd64286/scalable-geometry/objects \
  --toolchain-bin /workspace/toolchains/lean-4.33.0-rc1-linux/bin \
  --mathlib /workspace/goldbach-formalization/.lake/packages/mathlib \
  --mathlib-packages /workspace/goldbach-formalization/.lake/packages \
  --rss-gib 6 --wall-seconds 900
```

P2 or P3 can use explicit canonical host paths with the same pinned compiler
binaries and Mathlib commit. All accepted suppliers are installed into one
project object namespace. They are never recompiled. Root chooses the MCP
memory request and Lean RSS limit from the host's actual available resources.

Resume uses a fresh attempt name with the same immutable context. A successful
result, accepted seal or SUCCESS/STOPPED acceptance reference prevents replay
when its object or evidence is missing or invalid. Restore the exact bytes;
the runner will not reinterpret missing evidence as an unexecuted proof step.

## Export

```sh
python3 STAGE/tools/p26/scalable-cell05-fields/export_fields.py \
  --stage STAGE --attempt THE_ACCEPTED_ATTEMPT
```

Export revalidates all 219 chains and the current source/object/audit bindings,
emits only the 73 new object bodies, writes every member as regular bytes,
reads the entire tar back against its manifest, and checks input/context drift.
The archive remains on the cloud host; stdout returns only metadata and counts.

Local synthetic regression results and source-package checks do not constitute
Lean acceptance. Full top-level parse/decode/shape connection is a later batch
that must join these real accepted receipts with the real accepted row network.
These field batches do not assert geometric or integral meanings or complete
all of P2.6.
