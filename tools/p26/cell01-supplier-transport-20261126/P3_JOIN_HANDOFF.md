# P3 Cell01 supplier join and preflight handoff

The three-file transport is complete at commit
`ae6207b88203a05e07b364d9542360d333291d55`. Its exact received files are under
`/workspace/p26-cell01-supplier-transport-557a12f3bcd7/payload`. P3 task
`edf05b0cbd994aceaf67090698d2b400` succeeded with exit 0. No extraction,
provider installation or new proof has occurred.

The following is a source-level handoff for the next adapter. The adapter has
not been implemented or run by this transport task.

## Reuse the existing frozen code and sources

| Artifact | Bytes | SHA256 |
|---|---:|---|
| cell01-family-run-p3-v2.tar.xz | 47624 | d61668ff5e41981b69f3526fd5efe0a83c6e01963b6018386e185d2beb610ef7 |
| p3-v2 CODE_MANIFEST.json | 1800 | 34d65a335862bdc81a2f6df7c2a6c9fb511186e696759cb8b8a745b578bf62e9 |
| p3-v2 family_run.py | 69366 | 52666297d9fac67bcb50416f2f9405c38c5d31603dd8679f97620ca441281601 |
| cell01-original-floor-family-v1.tar.xz | 122656 | 457b87938ea4f363ab9ef8a6049173c5577f922bd5a133213ccfdd026001dce5 |

Do not change the frozen runner or rerun its 31 completed tests. The existing
`prepare_pilot.py` supplies reusable metadata routines (`chain`, `direct_refs`,
the four canonical closure references and external-inventory checks), but its
entry point is pinned to pilot-v1 and P1 paths. It cannot be invoked unchanged
for this P3 release.

## Smallest new adapter

One new `prepare_family_p3.py` can perform the following metadata/installation
operations while calling the frozen validator for all acceptance decisions:

1. Verify the received archive and MANIFEST again, then exclusively extract its
   exact 204 regular members into a fresh capsule-provider directory. Validate
   each name, type, size and hash before treating extraction as complete; keep
   partial state on failure and never overwrite an existing provider. No old
   archive or receipt bodies are among these members.
2. Build a 791-row provider registry from the 602 exact P3 pairs in
   `P3_PRESENT_FINAL.json` plus the 189 capsule objects. The 14 missing source
   bodies come from the capsule; the other sources use their existing exact P3
   paths, including `p3_exact_source` in `P3_MISSING_FINAL.json`. Recheck every
   live pin against the frozen SOURCE_MANIFEST/SUPPLIER_DELTA and original
   capsule identities. All expected sidecar lists are empty. A separate copy of
   all 791 pairs is unnecessary: joins may retain those exact provider paths,
   and the frozen runner hardlinks the required pairs into its own new stage.
3. Adapt the pilot's original-body binding collector and add the actual finite
   RUN/INPUT/SUCCESS or PARTIAL schemas. Preserve each historical JSON body and
   original reference exactly. Supply only current-path relocation mappings.
   Row001 must instead use `same_host_row001`, original P3 paths and the frozen
   dedicated resolver; it must never enter the relocation body map.
4. Construct a P3 complete-tree runtime from stock `/toolchains/bin/lean`,
   `/toolchains/bin/leanchecker`, the actual canonical `/toolchains/lib` and the
   nine `/mathlib/.../lib/lean` search roots reported by compiler_info. Recompute
   tree signatures using the unchanged `GenericFloor_verify_v2.tree_signature`
   algorithm; relocation prevents reusing P1 root paths unchanged. Every actual
   nonproject object and sidecar must match the accepted generic owned
   module-byte-context by bytes. Retain the original context body, rebound by
   its exact pin; do not substitute a compiler version string or new inventory
   for this accepted-byte comparison. Check expected external imports against
   the original owned logs and selected sources/audits.
5. Emit immutable per-owner joins using `F.closure(module, rows) - set(targets)`.
   Reuse `F.validate_runtime` once and call `F.validate_join` for each join to
   obtain a full old-supplier preflight without any Lean command. Record only
   pins/counts/pass for the protected row001 validation, never body copies.

The P1 recovery inspection found no accepted interface object or triple.
Therefore omit `accepted_owner` and prove the interface for the first time on
P3 only after the next execution authorization. No accepted owner needs replay.

## Historical evidence still required

The received capsule deliberately contains only objects, sources and metadata.
Its compact successful summary cannot replace the bodies that frozen
`old_chain` reads.

| Supplier family | Existing authority / body location needed |
|---|---|
| 646 canonical suppliers | Original row000 23rd RUN/INPUT/RESULT, three sealed command/result/log chains, full owned inventory, module context where referenced, and four original closure/addendum bodies |
| Original row000 bridge | The same original three-mode row000 authority, with its exact source/object pins |
| Generic transport | Original generic-v2-r14 CONTEXT, INPUT, RUN, RESULT, three ACCEPTED_STEP chains, audit/owned/module-byte-context and before/after bodies |
| Finite rows002–097,107–143 | Original P3 A/B/C-tail batch paths already inventoried; exact raw result/command/log and input bindings |
| Finite rows098–106 | The original P1 C-prefix 27 chains and controls, mapped unchanged to permitted P3 evidence storage and anchored by the fixed original export |
| Finite row001 | Original P3 stage only: `/workspace/p26-continuation-59264dd64286/cell01-row001-finite`; frozen same-host validation checks the three chains, 399 suppliers and 1596 live installed/provider pins |

Canonical row000's already retained local donor archive is
`docs/verification/20261126-p26/cell01-row000-original-floor/evidence.tar.xz`,
886800 bytes, SHA256
`1b88f393c1ccb1e9cd3c9804e86277ab9089badcd7b68b3f417cf74b6a02cea7`.
Its original INPUT pin is 3816105 bytes /
`67ac94afd5e2c3466b0b728c7cc95a574e8b840d5cc5d92fc3bf6f96f5c40e32`.
This archive is distinct from the prohibited row001 evidence group.
Actual P3 presence of all permitted relocated generic/C-prefix/canonical bodies
has not been established by the object inventory or this transport task.

## Exact owner closures

These counts were derived locally from the unchanged frozen source manifest;
they are source dependency counts, not new proof credits.

| Owner suffix | Old suppliers | Full project closure | Earlier new owners |
|---|---:|---:|---:|
| OriginalFloorInterface | 625 | 626 | 0 |
| OriginalFloorBlock000_015 | 663 | 665 | 1 |
| OriginalFloorBlock016_031 | 642 | 644 | 1 |
| OriginalFloorBlock032_047 | 642 | 644 | 1 |
| OriginalFloorBlock048_063 | 642 | 644 | 1 |
| OriginalFloorBlock064_079 | 642 | 644 | 1 |
| OriginalFloorBlock080_095 | 642 | 644 | 1 |
| OriginalFloorBlock096_111 | 642 | 644 | 1 |
| OriginalFloorBlock112_127 | 642 | 644 | 1 |
| OriginalFloorBlock128_143 | 642 | 644 | 1 |
| AllOriginalFloorBridge | 791 | 802 | 10 |

The old-supplier union is exactly 791. The first interface is exactly 624
canonical suppliers plus generic, with no finite supplier required.

## Concrete first preflight CLI after adapter completion

Use separate new code, source, input, provider and execution directories. One
consistent proposed layout is:

```sh
python3 -B /workspace/p26-continuation-557a12f3bcd7/cell01-family-executor-p3-v2/family_run.py \
  --stage /workspace/p26-cell01-family-p3-stage-557a12f3bcd7 \
  --source-root /workspace/p26-continuation-557a12f3bcd7/cell01-family-package \
  --source-archive /workspace/p26-continuation-557a12f3bcd7/cell01-original-floor-family-v1.tar.xz \
  --runtime /workspace/p26-cell01-family-p3-inputs-557a12f3bcd7/RUNTIME.json \
  --join /workspace/p26-cell01-family-p3-inputs-557a12f3bcd7/joins/P2OriginalSaving19Cell01OriginalFloorInterface.json \
  --attempt p3-interface-preflight-v2 \
  --rss-gib 12 --wall-seconds 1800 --max-new-steps 0 --validate-only
```

P3 advertises a maximum task limit of 13107 MiB; pass `--rss-gib 12` explicitly
instead of the runner's 14-GiB default when later authorizing proof commands.

The frozen CLI's `--validate-only` stops after the first unaccepted owner,
because that owner's owned step is still absent. Supplying eleven `--join`
arguments does not make this CLI validate all eleven before returning. Use the
pure `validate_join` adapter loop above for all 791 old suppliers, then this
unmodified CLI for the first persistent owner context. Later proof execution
must use a fresh attempt name and keep the code, runtime and source pins fixed.

All later execution remains limited to the eleven new owners / 33 steps. Old
suppliers are verified and reused; no old source is compiled by this route.
