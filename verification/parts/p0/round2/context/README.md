# Part 0 round 2: source and runtime context

These files are read-only intake records. Their timestamps and original scope
remain intact; they do not imply additional successful proof gates. The current
component verdicts are the adjacent batch `receipt.json` files and the fixed
integration report in `docs/PART0_ROUND2_VERIFICATION.md`.

## Original source versus current receipt

Fixed handoff files retain the authors' original comments, including historical
“uncompiled candidate” headers. A later successful receipt is tied to the exact
source SHA256 and compiled object. The header is not silently edited after
verification, and an old header does not erase a later recorded check. Conversely,
reading a source type or seeing a successful old root build does not verify a
new module.

The P1 progress records explicitly distinguish dependency compilation from the
four new production targets. Missing remote handoff refs are not evidence that
P1 has produced no work. The separately reported inherited fifth-layer integral
candidate remains source-pending in these intake records.

## Actual local compilation path

The unmodified pinned `lean` executable failed at startup with
`error: failed to locate application`, before compiling any proof. The pinned
original Lake executable and original `leanchecker` could start. P0 therefore
used Lake to call the official `Lean.Elab.runFrontend` with `trustLevel := 0` and
`warningAsError := true`, in P0's own output directory. No metadata shim was on
the proof compilation or checker path.

`runtime/frontend-driver.lean.txt` and `runtime/verify_batch.py.txt` preserve the
actual orchestration as evidence, outside the production proof tree. The driver
contains `unsafe Lean.enableInitializersExecution`, the official frontend
initialization call used before loading executable initializers. This is not a
new mathematical declaration, an analytic axiom, or a disabled kernel check.
The production modules themselves are checked for unsafe declarations and
forbidden axioms by Lean, and additionally by the existing project's source
scanner. This distinction is explicit; no stock-CLI aggregate build is claimed.

The bundled checker is invoked directly with the real `LEAN_SYSROOT` and an
explicit `LEAN_PATH`. Each receipt identifies the command, source and object
before/after, exit status, original log and `replaying MODULE` evidence. Its
scope is the named production module over its imports. It does not assert a
fresh replay of every imported declaration or a completed full-root gate.

## Normal checkout entry point

`verification/parts/p0/check_batch.sh` is the executable entry for a normal
checkout where the locked stock CLI starts. It checks pins and tracked source
identity, explicitly builds every selected new production module, uses strict
Lean compilation, runs the defining-module audit, replays every selected
production module with the bundled checker, and verifies hashes afterward.

The local API-based compilation records do not claim that this stock-CLI shell
entry ran end to end in the current environment. The required full project
build, project root checker, and full root/transitive axiom audit remain
separate requirements. Existing CI pins and gate definitions were preserved.

## Historical Actions observation

`ci/30fdb230-actions-receipt.json` applies only to integration commit
`30fdb230428e91d7eb5deb8deb5cbe3fdc113ceb`. Its jobs had no assigned runner and
no execution steps. It is neither a Lean failure diagnosis nor a successful
verification record for this or any later commit. No workflow rerun was
requested to replace missing local progress.
