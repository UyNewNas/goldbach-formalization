# Existing P2.5 geometry owners: execution preparation

This directory prepares acceptance of three existing Lean sources. It has not
compiled any geometry theorem, submitted a remote job, edited public Lean source,
or modified the shared Git index. Every result must retain `P2_5_proved: false`:
the three local physical-geometry owners do not supply the complete P2.5 endpoint.

## Immediate Cell00 scope

`run_geometry.py` defaults to `--only Cell00TypedGeometry`. Its exact selected
project closure is 277 modules: 9 accepted finite-cache modules, 267 accepted
analytic modules ending at `P4AOriginalAscendingCell0Literal96`, and one new
geometry owner. The Cell01 state does not block this scope.

The 9 module names, their source paths and SHA-256 values, exact object sizes and
SHA-256 values are in `MANIFEST.json`, under `finite`, selected by
`planned_closures.ImbalancedChen.P2Saving16Cell00TypedGeometry.finite_modules`.

The runner first looks for each finite object's accepted bytes in the existing
P2 `.lake/p2-private/lib`. Additional already-extracted roots can be supplied
with repeated `--finite-objects ROOT`; a root contains `ImbalancedChen/*.olean`.
Only matching accepted bytes are used. It does not compile a missing dependency.

## Existing cache transfer

The complete, already-created finite-cache archive is:

* `P25_VERIFIED_PROJECT_OBJECTS.tar.xz`, 30,963,752 bytes, 246 accepted modules.
* SHA-256: `05d155b7aaecd03231f9250c2e1f0b51a146548befe7a1d7ff2adc063c6461b6`.
* Persistent file ID: `libfile_fde3_f-7a2e7b86f68081919d41d21a65059fdd_b16923d1bd6881918dcbdee2321d458c`.
* Provider file ID: `file_0000000042a08230a1e79b28fa491fc9`, version 4.
* Existing receipt: `/workspace/scratch/ffd83d72c265/p25-compiler/checkpoints/CACHE_LIBRARY_RECEIPT_V4.json`.
* Local existing archive: `/workspace/scratch/ffd83d72c265/p25-compiler/checkpoints/verified-cache-final-seven-owners/P25_VERIFIED_PROJECT_OBJECTS.tar.xz`.

The outer archive contains `CACHED_OBJECTS.json`, `RESTORE.txt`, and
`objects.ltar`. The already-tested extraction requires a 256 MiB process stack
limit for stock `leantar`; the default 8 MiB produced SIGSEGV in earlier
extractions. Reuse the existing restoration instructions and archive. No new
archive, Mathlib build, or P1 analytic-object transfer is needed.

The previously prepared 12-object `finite-objects.ltar` also suffices for Cell00
and both typed geometry owners. It has 23,518,547 bytes and SHA-256
`e62ef085575cba904582ab239514be81505b9da921adf869a5d27c273d52e17d`.
Cell01OriginalGeometry needs another 113 already-accepted finite objects; reuse
the complete archive for that later scope.

## Required P2 receipt

For the current R17 run, the authoritative files are:

```
/workspace/p2-saving16-20261125/.lake/p25-followup-repairs-attempt017/RUN_RESULT.json
/workspace/p2-saving16-20261125/.lake/p25-followup-repairs-attempt017/SOURCE_CLOSURE.json
```

Use their actual terminal SHA-256 values after retrieving and checking the run.
The runner allows unrelated branch failures, but requires all nine terminal
postflight checks to be true and the selected analytic closure to contain no
failed or pending modules. Every required row owner must have terminal owned
acceptance. It revalidates the actual normal records and source/dependency
signatures, current accepted replay/audit receipt, full artifact hashes, and
complete owned declaration log without rerunning the accepted row owner.

For Cell00, only the Literal96 row owner is required. This does not wait for
Cell0AffineChronology or Cell1Affine.

## Invocation

Copy the following existing prepared files together to a directory on P2:
`run_geometry.py`, `run_new_owners.py`, `MANIFEST.json`, `CACHED_OBJECTS.json`,
and `FINITE_RUNTIME_COMPATIBILITY.json.xz`. `PLANNED_ANALYTIC_SOURCE_CLOSURE.json`
is optional and is only for read-only planning; it cannot substitute for the
actual P2 source closure in a real run.

```
python3 -B run_geometry.py \
  --repo /workspace/p2-saving16-20261125 \
  --only Cell00TypedGeometry \
  --source-closure /workspace/p2-saving16-20261125/.lake/p25-followup-repairs-attempt017/SOURCE_CLOSURE.json \
  --source-closure-sha256 ACTUAL_SOURCE_CLOSURE_SHA256 \
  --run-result /workspace/p2-saving16-20261125/.lake/p25-followup-repairs-attempt017/RUN_RESULT.json \
  --run-result-sha256 ACTUAL_TERMINAL_RESULT_SHA256 \
  --finite-objects EXISTING_EXTRACTED_ACCEPTED_OBJECT_ROOT \
  --work /workspace/p25-geometry-cell00-verified-inputs
```

Omit `--finite-objects` if the inventory shows all nine accepted finite objects
already exist in P2's private lib. Add further roots rather than copying or
overwriting an existing nonmatching object.

The work directory has a single isolated project namespace, symlinking the
exact accepted dependency objects. Existing selected geometry acceptances are
reused only when their full context and artifact hashes still match. A prior
incomplete attempt is preserved and causes refusal; do not remove its logs to
force a restart.

The production flags are the original strict flags:

```
-t0 -j1 -M11264 -DwarningAsError=true -DmaxRecDepth=50000 -DmaxHeartbeats=40000000
```

Each owner runs sequentially: normal Lean, stock `leanchecker`, and complete
owned-declaration audit. The default timeout is 900 seconds per stage and can
be selected explicitly with `--stage-limit`; recursion and heartbeat limits
are not exposed as override options.

## External context and acceptance gates

The existing P2 qualified external snapshot has SHA-256
`ad4386f160e7d59bcaca2820fb9123434d05593595b266ca24fa742e48367d27`.
All 5,311 finite-context modules present in that snapshot have identical object
and companion hashes. `FINITE_RUNTIME_COMPATIBILITY.json.xz` records all 5,312
historical finite modules and 15,940 runtime file hashes. Five supplemental
files are checked before any new Lean command and before/after every stage:

* `/workspace/toolchains/lean-4.33.0-rc1-linux/lib/lean/Lake/Util/Casing.olean`
* The same path with `.private` and `.server` suffixes.
* `/workspace/compile-deps/mathlib/lake-manifest.json`
* `/workspace/compile-deps/mathlib/lean-toolchain`

A missing or different supplemental file fails before compilation. No remote
presence claim has been made by this preparation.

Every stage also verifies the selected full source closure, all dependency
object bytes, pinned controls, accepted prerequisite receipts, and the full
qualified external environment. The newly produced owner object must keep
exactly one hash across normal completion, replay, and audit. Unqualified
project `.olean.private`/`.olean.server` companions are rejected. The original
complete serialized/environment inventory template is reused; the independent
existing parser checks full nontruncated types, private/generated declarations,
and transitive axiom sets. Only `propext`, `Classical.choice`, and `Quot.sound`
are permitted, and the four original public theorem names must be present.

Formal evidence is emitted under `WORK/evidence/OWNER`: stage logs, before/after
contexts, full `declarations.json`, `types.txt`, and the accepted `RESULT.json`.
The aggregate `WORK/SUMMARY.json` does not claim the global P2.5 endpoint.

## Later Cell01 scope

After the actual Cell1Affine owner is accepted, select
`--only Cell01OriginalGeometry` to schedule TypedGeometry first and then its
OriginalGeometry transport, or include all three owners. The combined scope
uses 125 finite modules, 294 analytic modules, and 3 new owners. A later analytic
repair can supply its own exact terminal result and source closure; the runner
does not assume unverified R17 Cell1Affine success or reuse preflight objects.
