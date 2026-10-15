# P2 handoff: lossless certificate-data carrier split

State: WAITING_FOR_P0. Request: REQUESTED. Verification: SOURCE_ONLY.

- Request: automation/parts/p2/requests/20261015T022700Z-data-split.json
- Immutable run: automation/parts/p2/runs/20261015T022700Z-data-split.json
- Baseline: d41a7bc48b7066cd95c2a9e143a13e494d44b284
- Worktree: /workspace/shared/chen-coordination/p2-data-split
- Branch: codex/chen-p2-data-split
- Selected 35-file snapshot SHA-256: 9a8b51a20ca9519b0e6fdcb07619d4e87144f1e7e875061c8dc75fd810a5eb6e
- Frozen patch: automation/parts/p2/runs/20261015T022700Z-data-split.patch
- Patch SHA-256: 952df6bf61213321764984a2af00199e92bb4cb7c7b269ccfa70beaeda211325
- Source dependency fingerprint: 0047dfcfd7c850631a2f8480dfdf4549b925ba83575492c9c48bb2a3b5268fc9

Prior pilot 38669650232 failed twice in the same FullCertificateData dependency
with -M4096 interpreter memory_exception, exit -6. Neither new target was reached.
The artifact identity and both raw receipt/log hashes are recorded in the
candidate's verification/parts/p2/data-split-prior-failure.json.

All 186 original approximations326..511 declarations are moved byte-for-byte to
12 data leaves; every original tuple value and its order remains unchanged.
The full data selector/approximation definitions remain byte-identical in a
4,978-byte compatibility entry. E0=6,091; E1=11,481; total 17,572 exact-once pairs.
The largest data leaf has 2,757 rows. FullMask, FullChecker, FullStripCertificates,
pins, raw JSON, root imports and numeric constants are unchanged.

The generic Rows module imports no data. Each sum block imports only its own
data leaf and retains every old numerical proof body. 186 new per-strip rfl
length facts are connected by a real dependent Fin.cases proof in RowAssembly.
The original row/list bridge bodies and final sum proofs are preserved.
No Python equality is presented as a kernel bridge; all proof gates are unpaid.

Detailed mapping, source hashes, deterministic producer, import closure and
static review are in verification/parts/p2/DATA_SPLIT.md and linked reports.
No Lean/Lake/checker/audit/CI/push ran. Patch reverse-apply check and static
coverage/identity/source checks passed. No commit or accepted object is claimed.
The older candidate generator/manifests remain unchanged as historical inputs.

P0 should check light Rows, Block11 and largest-data Block10 first, then all
remaining blocks, the compatibility entry, RowAssembly and NaturalSums.
Preserve all strict/replay/type/inventory/axiom/import-object gates and fixed
-j2/-M4096. Do not repeat unchanged full-row checks or claim a pilot is global
acceptance. 186-deep elaboration and aggregate import memory remain untested.

Natural totals remain 55,858,378,943,374,979 and 55,858,409,959,907,296 at 10^20.
These belong to existing K/80-normalized adopted fibres, not complete K.
Full integral/cast/Buchstab/common-policy bounds and hLower/hUpper remain open.

Next: await P0 diagnostic/acceptance; no further unverified analytic layer.
