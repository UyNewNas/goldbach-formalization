# Cell00 isolated continuation verification

This driver adds the two missing independent kernel checks and verifies the
two new continuation owners. The 480-module cell00/Q96 bundle and the 224
analytic suppliers are imported from frozen stage files. No supplier normal
build is run. An attempt has its own copied input sources, audit files,
new objects, command receipts, and logs. The driver copies existing Lean
files verbatim and never constructs Lean source on the compiler host.

The stage is `/workspace/p26-continuation-59264dd64286/cell00`. Extract the
verified cell00 bundle there, including `MANIFEST.json`, `sources/`, and
`objects/`. Place the verified analytic source/object copies in
`analytic/sources/` and `analytic/objects/`, preserving module paths, and
place `HIGHER_MOMENTS_PINNED_CLOSURE.json` at the stage root. The source and
object SHA256 pins cover all 224 analytic modules; the Q96 checker closure
is already included. Run `prepare_cell00_stage.py` first to produce the
required `ANALYTIC_FREEZE.json`. The driver verifies its manifest bindings,
all 224 recorded source/object hashes, and the exact frozen destination paths.

Put the two new owners, with their `ImbalancedChen/` paths, under
`new-sources/`. Copy the two supplied files from `cell00-owned-audits/` to
the stage's `audits/` directory. Keep `Cell00OriginalFloor_continue.py`,
`Cell00OriginalFloor_VERIFIER.json`, and `Cell00OriginalFloor_EXTERNAL_PINS.json`
beside each other. The verifier manifest
pins the driver, both new source files, both audit files, the cell00 bundle
manifest, and the 224-module analytic pin manifest.

```sh
python3 Cell00OriginalFloor_continue.py \
  --stage /workspace/p26-continuation-59264dd64286/cell00 \
  --lean-bin /workspace/toolchains/lean-4.33.0-rc1-linux/bin \
  --mathlib /workspace/blue-member-build/.lake/packages/mathlib \
  --reuse-backfill-attempt /workspace/p26-continuation-59264dd64286/cell00/attempts/20261126T033233770413Z-82b28550
```

The runtime must report Lean `4.33.0-rc1`, commit
`62eed1db4d67327ec8120be05f1a1b0847d74561`; `git -C <mathlib> rev-parse HEAD`
must report `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Seven built package
roots are required beside mathlib: `LeanSearchClient`, `Qq`, `aesop`,
`batteries`, `importGraph`, `plausible`, and `proofwidgets`. A built `Cli`
root is included when present. The driver's `LEAN_PATH` includes only its
attempt objects, the two frozen project object roots, and these runtime
roots; it does not import project objects from the mutable blue build.
All 704 project suppliers are placed in the same attempt object namespace
as the new owners. Same-filesystem suppliers use hardlinks; only an EXDEV
cross-filesystem failure permits a byte-verified copy. This avoids Lean's
first-root namespace lookup shadowing later supplier directories. Sources
for both new owners remain in one project working directory.

The additional external providers are the same-level `goldbach` package,
fixed at `09b97db5764ade1246bfb77206baa1b124760958`, and `LeanArchitect`,
fixed at `78dd66840d3efe8c824c699fc03381cec817c271`. Their locations may be
set with `--goldbach` and `--leanarchitect`. The driver checks both Git
revisions and the source SHA256 pins of the 506 required goldbach modules
and 9 Architect modules. All 515 required existing objects and any
available `.olean.server`, `.olean.private`, or `.ir` sidecars are hashed
before execution and checked again before and after every validation
command. No external package is compiled. Historical P3 object observations
for 21 modules are retained as comparisons, without representing them as
historical P1 object pins. External providers containing an `ImbalancedChen`
object directory are rejected, preventing a project-cache fallback.

Execution order is fixed:

1. Verify and reuse the successful kernel receipt for `P2OriginalSaving19CharacterCore00`.
2. Verify and reuse the successful kernel receipt for `P2Winner9HomogeneousRecurrence`.
3. `P2OriginalSaving19HigherMomentsPrefix`: normal, kernel, complete owned audit.
4. `P2OriginalSaving19Cell00AllOriginalFloorBridge`: normal, kernel, complete owned audit.

The two kernel receipts are required and are never replayed by v3. Their
accepted-step, command/result/log, and input-fingerprint chain must still
match. Source/object bytes, binaries, pinned package context, and logical
project/external supplier snapshots must match the current attempt. Only
the project search-path binding changes to the equivalent complete namespace.

The owned audits enumerate declarations by owning module, print every
owned type and its transitive axioms, and reject unsafe, partial, or axiom
declarations. The only permitted transitive axioms are `propext`,
`Classical.choice`, and `Quot.sound`. There is no fixed declaration-count
assumption; a nonempty inventory, one record per inventoried name, and the
completion count must agree.

Each command has `command.json`, `result.json`, and a hashed `output.log`.
An accepted step additionally has `ACCEPTED_STEP.json`, which binds the
source, object, log, and audit source when applicable. All frozen project
inputs are rehashed before and after each command. A failure stops the
attempt and writes `RESULT.json` with `FAILED_STOPPED`. A successful final
result claims only these two new owners and two kernel backfills, not all
of P2.6. Reusing an attempt identifier is refused.

Host-only tests run with `python3 -B tools/p26/test_cell00_continue.py`.
They check changed/symlinked files, the seven-package layout without Cli,
failed-command receipts, and incomplete/forbidden-axiom audit output. They
do not execute Lean or assert that the new Lean owners compile.
