# Exact-byte P3 recovery driver

This is locally prepared recovery code, not a compilation or acceptance result.
No cloud command or Lean executable was run while preparing it. Production Lean
sources and `run_cell00_four_consumers_v7.py` are unchanged.

## Current review pins

| Input | SHA-256 |
| --- | --- |
| `restore_p3_cache.py` | `d6d895b80f07c9bd499501cce3e275a271ccd8ddfc166826942953afa960d542` |
| `RECOVERY_SELECTION.json` | `cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf` |
| External `P3_LOCAL_ONLY_DRIVER_PAYLOAD_MANIFEST.json` | `24cf2b46e8850bf2147ac5e751049a3915466ab6131d12ab07405cb9478f0c5d` |
| External local-only 10-object archive | `b0719bd03bab9be02756e298cfef4bc44fa61cabbff722d00025ae460fe3ea80` |

The external archive is 2,640,212 bytes, holding 15,777,112 bytes of existing
object content. P3 already has 21 other objects in its files/archives; those are
mapped directly. Thus the 41-object set is 21 already on P3, 10 transported from
local exact backups, and a different 10 still missing and eligible for normal
rematerialization. The external archive must not be added to Git. The driver checks both its archive
SHA and each selected member SHA. `--payload-archive` relocates the external
archive without editing its pinned manifest.

`OFFLINE_VALIDATION.json` and `OFFLINE_TESTS.log` record 12 passing storage-boundary
tests, plus one targeted regression for the final P3 completion predicate. The CLI plan test checks that even an explicitly supplied result path is
not created in plan mode. Tests also check no overwrite, symlink rejection,
duplicate/incorrect archive members, strict historical requirement preservation,
and rejection of normal compilation of an already available owner.

## What is ready

- `--plan`, the default, is read-only. It resolves exact byte sources and reports
  missing mappings/conflicts plus current runtime hashes. Exit 2 means unresolved
  requirements, not a proof failure. It writes no receipt or cache; redirecting
  stdout is a separate caller action.
- `--restore` installs only available exact bytes and records a new recovery
  receipt. Existing targets are validated, never overwritten. Missing old
  evidence remains explicitly listed and yields `PARTIAL_RESTORE_ONLY`.
- `--normal-rebuild` additionally reconstructs only actually missing approved
  objects from exact existing source bytes. It will not start Lean until final
  P3 object inventory is complete, every non-object historical/witness mapping
  is resolved, current runtime is exact, and any newly located object is reused.
  A differing new object SHA stops before placing that object in old paths.

The current selection has `p3_object_inventory_complete=true`, bound to final
inventory SHA `0029b670eba2c33aae87cc3cfbea3eaff269d1e22a72688aa128cd1d48b76c89`.
The driver requires its explicit completed flag, actual zero exit code, and P3
file-scan record; an early scan header is insufficient. The final P3 scan found
21 exact objects and verified all 14 witness files. No scan needs repeating.
Verified P3 file/archive locations are already in the selection, and the ten
normal candidates remain unchanged. Normal mode still waits for all historical
non-object byte mappings to resolve, which the actual P3 plan must check.

## Exact plan invocation after publication and payload transport

The publication checkout must contain this directory plus the referenced
`p3-cache-recovery` inventory and witness manifests. The example assumes the
unchanged external payload files have been transported to `/workspace`.

```bash
python -B /workspace/p25-cache-recovery-20261126.py \
  --plan \
  --repository /workspace/p25-q96-20261125 \
  --selection /workspace/p25-q96-20261125/docs/source-only/20261126-p2-5-cache-rematerialization/RECOVERY_SELECTION.json \
  --selection-sha cd0b812eaf659d675406c594f7eae66b4ea550bdd30f874b1a2876ebdef04cbf \
  --payload-manifest /workspace/p25-recovery-P3_LOCAL_ONLY_DRIVER_PAYLOAD_MANIFEST.json \
  --payload-manifest-sha 24cf2b46e8850bf2147ac5e751049a3915466ab6131d12ab07405cb9478f0c5d \
  --payload-archive /workspace/p25-p3-local-only-objects-10.tar.xz
```

Extract the runner's exact published bytes to the external runner path before
calling it. Do not edit sources or generate proofs on P3. The driver does not
fetch or change Git HEAD. For a write mode, the caller must first select the
published commit and then replace `--plan` with the desired mode and append:

```text
--publication <exact 40-hex publication commit>
--runner-sha d6d895b80f07c9bd499501cce3e275a271ccd8ddfc166826942953afa960d542
--result-dir /workspace/p25-q96-20261125/.lake/diagnostic/p25-cache-rematerialization-attempt001
```

Use a new result directory for every write invocation. A partial restore may be
followed by a later invocation in another fresh attempt. Old paths that are now
exact are just validated. `--skip-cas` is allowed only for local read-only mapping
work and is refused in write modes.

The driver binds its own source and selection to `git show <publication>:...`,
requires a clean tracked checkout, preserves the compiler/flags and complete
external file set from actual consumer005, and writes only the frozen
destinations plus its new recovery directory. New normal work is recorded as
new normal work; the old accepted replay/owned records remain historical.

## Current unresolved mappings

`LOCAL_PLAN.json` evaluates P3 paths in the local preparation process, which has
no P3 toolchain or `/mathlib`. Its 15,940 absent runtime paths are therefore not a
P3 runtime-loss report. That local run deliberately skips P3 CAS lookup.

It resolved 349 of 419 unique required byte hashes using existing repository
evidence and the original full 31-object local payload for this local-only plan.
Production transport uses only the smaller local-only 10-object subset shown
above and reuses the 21 P3 objects directly. The remaining local-view work is:

- 10 currently missing project objects, confirmed by the final P3 inventory.
- 14 original witness files, totaling 93,508,187 bytes, to be checked at their
  actual P3 paths or restored from exact original bytes.
- 46 distinct historical non-object hashes. Their full old paths and expected
  hashes are in `LOCAL_PLAN.json:missing_nonobject_payload_mappings`.

Those 46 include private owner audits/receipts, old String/Char binding evidence,
runner copies, Decoded/FieldDecode owned inventories, and the original
`COMPLETE_EXTERNAL_BEFORE.json` files for consumer004/005 and field004/005/006.
The snapshot envelopes contain their original timestamps; the driver cannot
manufacture replacements. The P3 CAS scan must determine which bytes remain
available. A manifest entry with a hash does not itself establish possession of
the corresponding bytes.

If any old byte sequence is unavailable, the original v7 route stays blocked.
The driver records the missing paths rather than weakening v7. A successfully
restored cache means only that the existing dependency chain is again available
for v7's unchanged preflight; it is not a declaration that v7 or P2.5 has passed.
