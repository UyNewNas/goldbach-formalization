# Cell03 Simplex05 / Simplex10 / Simplex18: unchanged-source P2 acceptance

This directory prepares three resource retries. It grants no new formal credit.
All three original normal compilations exited with SIGKILL (`-9`), with an empty Lean
diagnostic log and no output object. All three owners import the same FieldSimp module
and have exactly 16 project dependencies: 9 historical accepted objects and 7
new Cell03 objects with complete normal/replay/owned acceptance.

The original sources are from commit
`68703c066df26624af2f2d45b6e0b0a1fd365b6d`. The existing geometry runtime map and
four-function owner driver were published at
`9ab70bc63b3f6a93449397be67981275fa7c59b9`. The original Cell03 checkpoint,
seven-object archive and Simplex10 failure records are published at
`a0eb3b8f66f47f382b0e551be1d5d7c319f8bdab`, under
`docs/verification/20261127-p2-5-cell03-finite/`.

Simplex18's five original failure files and
`SIMPLEX18_SAME_CLOSURE_SIGKILL.json` are bundled unchanged with this extension.
Its source remains from the same original source publication. Before extending
the plan, the complete 18-file hash record for the 05/10 version was retained in
`versions/05-10-v1/`, together with copies of only the control files that change.
`RETAINED_FILES.json` locates the unchanged shared files without duplicating them.

## Reuse the existing transfers

Use that published directory's `ARTIFACT_PARTS.json` and `restore_artifacts.py`
to restore the original archives. Do not create another archive.

| Existing artifact | Bytes | SHA256 |
|---|---:|---|
| `ACTUAL_EVIDENCE_DICT64.json.xz` | 1,338,732 | `197c79787aac8e6182926799e937e8b093020d627c42e8484398dca38d794760` |
| `SIMPLEX05_NEW_DEPS.tar.xz` | 5,552,060 | `008b437eeb659a3ced1d3f7779d9f965c91ff5fdf605b71e5fb8b37c175c2480` |

The first contains the original 625 captured files. The wrapper validates all
members and specifically rechecks the seven dependency receipts, their original
commands, six contexts per owner, exact auditor programs and complete owned
inventories. The second contains exactly seven standalone `.olean` files.

## Read-only preparation and inventory

The following paths are the planned P2 installation and transfer locations.
Choose actual transfer locations if the parent orchestrator uses another folder.

```bash
python /workspace/cell03-simplex05/run_simplex.py \
  --repo /workspace/p2-saving16-20261125 \
  --evidence-capsule /workspace/cell03-transfer/ACTUAL_EVIDENCE_DICT64.json.xz \
  --only 05 10 18 --plan
```

```bash
python /workspace/cell03-simplex05/run_simplex.py \
  --repo /workspace/p2-saving16-20261125 \
  --evidence-capsule /workspace/cell03-transfer/ACTUAL_EVIDENCE_DICT64.json.xz \
  --only 05 10 18 --inventory
```

Inventory searches `/workspace` with `rg` when available, or Python `os.walk`
when `rg` is absent, and records the actual enumerator in `OBJECT_INVENTORY.json`.
Neither enumerator follows directory symlinks. Both select exact object size/hash
matches without `.private` or `.server` companions. Supply repeated
`--search-root PATH` options to add explicit roots when needed, for example a
symlinked cache directory outside the default search. Inventory invokes no Lean
process and lists all missing objects. Existing target objects are reported for
receipt review; the actual runner will not silently duplicate those attempts.

The nine historical objects must already be available. When any of the seven
new accepted dependencies is missing, the actual runner validates the existing
seven-object archive and extracts only missing members into its fresh work
directory. No dependency or external library can be compiled by this wrapper.

## Formal P2 run

```bash
python /workspace/cell03-simplex05/run_simplex.py \
  --repo /workspace/p2-saving16-20261125 \
  --evidence-capsule /workspace/cell03-transfer/ACTUAL_EVIDENCE_DICT64.json.xz \
  --new-deps-archive /workspace/cell03-transfer/SIMPLEX05_NEW_DEPS.tar.xz \
  --only 05 10 18 \
  --work /workspace/cell03-p2-simplex05-10-18-attempt001 \
  --stage-limit 900
```

Use `--only 05`, `--only 10`, or `--only 18` to run only one owner. The work directory must be
fresh; incomplete attempts are retained. Run a single P2 compiler job with the
larger memory allowance, and allow enough job time for the selected stages. The
Lean arguments remain the original Cell03 arguments:

```text
-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=1000000 -DmaxHeartbeats=80000000
```

Each selected owner must pass ordinary Lean, stock `leanchecker -v`, and the
original complete serialized/environment audit. The four original owner-driver
functions and original full audit are reused verbatim. The original public
expectation list has 11 declarations for each simplex. Neighboring simplexes had
17 total owned declarations; this is recorded as a reference, while the actual
complete inventory is always obtained and saved. Acceptance rejects unsafe,
partial or axiom declarations and any transitive axiom outside `propext`,
`Classical.choice`, `Quot.sound`.

Before and after each process, the runner checks the exact sources and accepted
dependency objects, frozen controls, qualified P2 `ExternalSnapshot`, and finite
runtime supplements. The 15,940 original finite runtime hashes must project
exactly onto the existing P2 compatibility map. The five supplements include the
three `Lake.Util.Casing` files; an absent or changed supplement fails before any
Lean invocation. Their actual import resolution is checked too. The actual
external import inventory must equal the original 5,312-module finite closure.
Owner bytes must remain fixed through replay and audit. Earlier accepted owners
are rechecked while subsequent owners run.

## Export and Cell03 consolidation

Export these unchanged artifacts after the remote run:

- `P2_PROVENANCE.json`, `OBJECT_INVENTORY.json`, `SUMMARY.json`.
- For every selected owner: its output `.olean`, entire `evidence/<name>/`
  directory, and the exact `audits/<name>.lean`.
- The installed `run_simplex.py`, `PLAN.json`, `SIMPLEX05_MINIMAL_TRANSFER.json`
  and `local-failures/` files, preserving their byte hashes. For Simplex18, also
  retain `SIMPLEX18_SAME_CLOSURE_SIGKILL.json`.

Keep the original checkpoint and seven-object transfer by their existing
published references; they need no fresh export.

`RESULT.json` uses `p25-cell03-p2-scoped-acceptance-v1`, carries the original
Cell03 `manifest_sha256`, and contains the common accepted/source/object/log
fields. It binds `P2_PROVENANCE.json` and all owner artifacts. Actual P2 paths,
Lean command arguments, resolved executable and the timeout launch command are
retained. The provenance document maps the original local paths to the P2 paths
and references the original SIGKILL evidence without changing it.

The original reused driver records `started_utc` before its before-snapshot.
The local Cell03 driver records that timestamp after its before-snapshot. The
consolidator must honor the explicit remote schema, instead of imposing local
timestamp ordering or replacing P2 commands with local commands. An independent
audited bridge may bind the remote object/receipt for later local consumers; the
remote receipt itself must remain unchanged.

These resource retries prove only the selected decoder owners. They make no
claim that physical geometry, Q96, or P2.5 is complete.

## Preparation actually performed

`PREPARATION_CHECKS.json` records Python syntax validation, successful source and
captured-evidence plans for all three owners, a read-only local inventory matching all
16 accepted dependency objects, and verification of every member in the
existing seven-object archive. No Lean process or remote job was launched while
preparing this directory. The Cell03 agent independently reviewed the wrapper
and its remote merge schema read-only. After confirming that P2 has no `rg`, the
fallback branch was exercised read-only against the same local accepted-object
directory and compared with the `rg` result. Both found the same 16 exact inputs
and no target objects. Source import parsing also preserves nested module names.
