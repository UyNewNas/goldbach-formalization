# Cell12 bounded stress audit

## Decision

The seven existing cell12 candidates can be reused byte for byte. They need
at most **21 new normal/kernel/full-owned steps**, covering 24 selected rows.
No new Lean source or full-cell generation is needed for this experiment.
The current acceptance gate is the raw12 supplier evidence and its exact
dependency context, followed by a read-only census for any existing cell12
successes. The audit itself executed zero Lean commands.

The three leaves are separated regions. They cannot be composed into a
continuous original parser transition without proving the missing regions.
There is no cell12 binary node among the seven frozen owners. A later node
experiment can add only the adjacent block001, its typed owner and node000To001
after the initial stress experiment; none of those three sources is authored
by this audit.

## Exact bounded target set

All names below have prefix `ImbalancedChen.P2OriginalSaving19Geometry12Scalable`.
Every source and owned audit matches its published frozen manifest. Exact
hashes and complete import closures are in `STRESS_EXECUTION_PLAN.json`.

| Owner suffix | Rows or role | Original character interval | Source bytes |
|---|---|---|---:|
| Input | Packed input and generic remainder interfaces | 14461008-character input | 1790 |
| SimplicesBlock000 | Rows 0–7 | [1454524, 1472110) | 311347 |
| TypedRows000 | Original decoder for rows 0–7 | Same parser leaf | 147174 |
| SimplicesBlock412 | Rows 3296–3303 | [7962639, 7976812) | 277217 |
| TypedRows412 | Original decoder for rows 3296–3303 | Same parser leaf | 133330 |
| SimplicesBlock824 | Rows 6592–6599 | [14446316, 14460388) | 278346 |
| TypedRows824 | Original decoder for rows 6592–6599 | Same parser leaf | 132231 |

Total Lean source size is **1281435 bytes**. The original input SHA-256 is
`08488f0584b424ca33cf7c0d48396aee90e54db78b68a7b86313d267bf1191a9`.
Its bytes are not present in the restored local workspace. This audit checks
the published source pins and proof interfaces; it does not claim a fresh
local comparison against the full raw12 JSON. The original generated sources
retain kernel obligations binding the literal fragments to `geometryPacked12`.

The final parser leaf consumes the original `]` and returns the original
remainder at offset 14460388. The other two leaves return the next original
array state. Typed leaves retain `decodeGeometryRow`, its integer/rational
guards and the original vertex order. Their finite shape bounds use literal
140; a complete decoded 140-vertex array and whole-cell shape remain outside
this experiment.

The original array-fuel offsets are also retained: 7192 at the beginning,
3896 in the middle and 600 at the end. The statements remain valid for their
arbitrary additional `fuel`; no shortened input or alternate parser fuel
definition is substituted.

## Large packed input and offset cost

`Geometry12ScalableInput.sourceRest n` is defined as
`(geometryPacked12.drop n).toList`. `Tree.toList_drop` proves its equality with
the ordinary original-character remainder, without changing the parser.
Each parser owner has one `block_original_prefix` theorem that checks its
entire bounded window using `rfl`; its eight row fragments then compose over
that shared binding. The proof does not invoke the whole JSON parser on the
skipped prefix.

The tree representation does **not** cache a branch's count. `Tree.drop`
chooses a branch by recursively evaluating `left.count`. Thus a 16-level path
does not by itself imply logarithmic proof cost. The structural model below
follows the published `packTreeGo` and `blockLimit = 256`, using the pinned
ASCII character count. It counts recursive source-level operations without
evaluator memoization; it is not a Lean timing or memory measurement.

| Quantity | Cell05 comparison | Cell12 |
|---|---:|---:|
| Packed leaves | 1024 | 65536 |
| Total tree nodes | 2047 | 131071 |
| Tree depth | 10 | 16 |
| Characters per leaf | 196–197 | 220–221 |

For each selected cell12 start offset, the uncached model performs 16 branch
tests and 131054 recursive `Tree.count` node visits, including 65535 count
leaf visits. The `sourcePacked_count` theorem separately traverses the full
tree. No skipped characters need decoding, but these count traversals and
the large raw-object import are real potential costs to measure.

| Selected window | Characters checked | Packed leaves touched |
|---|---:|---:|
| Beginning | 17586 | 81 |
| Middle | 14173 | 66 |
| End | 14072 | 65 |

The proposed order is Input, end parser/typed, beginning parser/typed, then
middle parser/typed. This first tests the count theorem and largest offset
with actual final-array termination, then the largest selected character
window. Successful steps should be retained and reused through the reviewed
strict receipt chain. Cell05 performance is not extrapolated to cell12.

## Nine-supplier map and actual evidence

Eight generic suppliers are already accepted and reusable:

| Supplier suffix | Object bytes |
|---|---:|
| PackedChars | 384392 |
| ArchivePackedLoader | 92800 |
| SourceJson | 741272 |
| CharInputBridge | 64136 |
| SourceJsonCharInput | 24712 |
| ParseFromValue00 | 18952 |
| ArchiveSchema | 929928 |
| ArchiveRationalChars | 157088 |

This audit read their actual source and object members, all 16 normal/kernel
receipts and their logs from the published geometry01 `suppliers.tar.xz`.
It verified their SHA/size, explicit target module, command target, object
identity and exact kernel log. `SUPPLIER_MAP.json` retains those evidence
locations and pins. No old supplier was recompiled or rechecked by Lean.

The ninth supplier is `ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12`:

```text
source: 531 bytes
sha256: 6e8970081e04f50c301178fc256548b21f351ddf27f52eb6d01a44c6eca67749

object: 74733720 bytes
sha256: cbfa066dccf5a3dd5f72de7802b40c653b04f26ef33a90be44291ce9458fd684
```

The object pin was previously observed in the strict Core dependency context.
That use is not raw12's own independent kernel acceptance. The published
raw05 history also contains exact raw12 normal, validation and wrapper-result
locators with SHA/size. Their root is:

```text
/workspace/p1-complete-proof/20261125-p26-archive-v4-inputs-v1/
07826355aedef5a01e76c36ad304bc6b115f3c2b/
ImbalancedChen.P2OriginalSaving19ArchiveGeometryData12/
```

`RAW12_HISTORY_LOCATORS.json` records the complete exact paths. Those raw12
receipt bytes have not been recovered in this audit, so full supplier kernel
closure remains false. Raw05 previously demonstrated why the historical
loader/packed-chars object context must be compared explicitly. A raw12
compatibility addendum is necessary only if its actual historical context
differs; the discovery probe does not assume either outcome.

The existing P1 archive-extra and blue-member object locations are candidates
to fingerprint. The eight current generic objects can come from the existing
scalable-geometry stage. P2's old15 cell05 supplier stage does not establish
that raw12 was staged. A new stage must contain all nine exact objects in
one `objects/ImbalancedChen` namespace. Original objects must be restored
from their existing bytes, never regenerated to fill an evidence gap.

## Reusing the reviewed v3 mechanism

The future runner should retain the v3 shared strict validator for both
resume and export: exact module/mode, source/object/audit paths, full RUN and
command fingerprints, precise argv, before/after objects, dependency objects,
cwd, LEAN_PATH and runtime/package context. It must also retain the accepted
seal/index scan, missing-object refusal, canonical-path and bidirectional
provider isolation checks, namespace inventory, actual executed/reused
counts, regular-member archive writing and archive readback.

The required adaptation is small in target scope but is not a blind copy of
the cell05 baseline: target count becomes 7, maximum new steps 21 and old
supplier count 9. The baseline must validate the eight generic evidence
chains plus raw12's own recovered history and any necessary context addendum.
The raw05-specific baseline function or its closed boolean cannot certify
raw12. Existing seven source/audit bytes need no change.

Before compiling, inventory all surviving target objects, result receipts,
accepted seals and success/stopped indexes. A successful normal step with a
missing object or broken receipt chain requires exact recovery. It must not
fall through to a fresh normal compile. Unreceipted objects also stop the
runner. If a stage contains actual successful cell12 steps, reconcile their
original context instead of creating a duplicate execution elsewhere.

No new runner is frozen yet: supplier recovery and the prior-success census
determine the exact baseline it must enforce. The source-only execution plan
is concrete and topologically ordered, and keeps any future node experiment
separate from the initial seven targets.

## Read-only next action

`probe_raw12.py` reads only the pinned historical files, current object/input
fingerprints and known-stage success markers. It invokes no subprocess,
writes no file and prints at most 20000 bytes of metadata. Upload the exact
locators JSON alongside it, then the parent may run:

```sh
python3 probe_raw12.py --plan RAW12_HISTORY_LOCATORS.json \
  --stage /workspace/p26-continuation-59264dd64286/scalable-geometry
```

Its output is discovery, not acceptance. Complete raw12 evidence should be
retained on the cloud host with only a small summary returned. The 74.7 MB
object and 14.5 MB raw input need not be transferred to the local workspace
to validate the existing seven authored sources.

The old unpublished `Geometry02To12Decoding_FEASIBILITY.json` did not survive
the local reset and is absent from the restored repository. This report
derives its conclusions from current published sources and evidence instead.
All 787 previously handed-off paths remained unchanged.
