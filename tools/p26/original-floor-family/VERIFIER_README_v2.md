# Single generic owner: P1 verifier package v2

This package executes exactly one new owner:
ImbalancedChen.P2OriginalSaving19OriginalFloorTransport.
Its source is fixed at SHA256
9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574.
No row001 or other new finite owner is compiled here.

The source-only package is prepared locally. It contains the authored owner
and complete owned audit, the verifier, two unchanged published Python helpers,
the exact 233-supplier registry, external/runtime pins, and source-closure
metadata. It contains no old supplier object or old evidence archive body.

## Accepted suppliers

The registry is selected from the accepted P1 attempt:

    /workspace/p26-continuation-59264dd64286/cell01-row000-original-floor/attempts/20261126T045413255133Z-03f42f40

Every one of the 233 source SHA/size pairs matches that attempt's 1,111-module
canonical registry. The selected sources total 2,406,698 bytes and objects total
187,526,352 bytes. The runtime, exact stock leanchecker binary, 515 external
module records, and old normal/kernel/owned receipt chain remain pinned to that
accepted context. No old proof command is rerun.

Supplier sources, objects, and recorded sidecars are installed by hardlink into
a single project/ImbalancedChen and objects/ImbalancedChen namespace. A
cross-filesystem link failure stops the driver; it does not copy the old object
body. The small authored source and audit are likewise installed from exact
frozen package bytes. No Lean source is generated or rewritten in the cloud.

## Installation and command

Extract the package to a directory separate from both the stage and all cache
providers, for example:

    /workspace/p26-continuation-59264dd64286/original-floor-family/generic-source-v2

Use the distinct stage:

    /workspace/p26-continuation-59264dd64286/original-floor-family/generic-v2

The coordinating agent may run:

    python -B /workspace/p26-continuation-59264dd64286/original-floor-family/generic-source-v2/GenericFloor_verify.py \
      --stage /workspace/p26-continuation-59264dd64286/original-floor-family/generic-v2 \
      --attempt generic-v2-first \
      --rss-gib 6 \
      --wall-seconds 900

This README and the preparer do not submit that command. A fresh attempt name is
required for each continuation; old attempts and failures remain in place.

## Three required steps and byte freezing

The only new proof commands are normal compilation, exact stock
leanchecker --verbose, and the full owned audit. The audit checks serialized
versus environment ownership inventories, every complete declaration type,
unsafe/partial/new-axiom flags, and the complete transitive axiom set. The
permitted axioms remain propext, Classical.choice, and Quot.sound.

The package code, authored source/audit, origin provenance, installed suppliers,
external sources/objects/sidecars, compiler/checker binaries, and stage input
context are pinned. The verifier also computes deterministic byte summaries of
every file in the fixed runtime object roots and toolchain library root. These
summaries cover relative names, link targets where applicable, byte counts, and
content SHA256; no runtime tree is copied. Every new proof step receives a
separate before and after rehash record. The final audit also records exact
provider objects/sidecars for the entire loaded module inventory.

Path guards run before writes. Stage and input/cache roots must be disjoint in
both ancestor directions. Symlinked parents and dangling destinations are
rejected. No existing different source, object, receipt, or context is overwritten.

## Same-stage continuation

Only complete, valid receipts from this exact stage, source, audit, fixed input
context, and runtime may be reused. Their command arguments, command/result/log
chain, before/after checks, object and sidecars, and owned evidence are rechecked.

A success seal with missing or changed evidence stops. A successful raw result
without its accepted seal also stops. Missing or changed accepted objects must
be restored byte-for-byte; they cannot trigger another normal compile. An
unreceipted object is rejected. Failed or unexecuted steps retain their history
and can run in a new attempt after the preceding accepted steps are validated.
Every accepted-step reference in every RESULT.json and PROOF_RESULT.json is
validated, including failed attempt indexes. Missing indexed evidence cannot
be treated as an empty cache. The mode list must be an ordered, duplicate-free
prefix of normal/kernel/owned.

## Evidence

After all three steps are valid, the driver creates an archive in the cloud
stage's evidence/ directory. It contains only the new owner source/object/
sidecars/audit, frozen verifier package, input/runtime fingerprints, complete
new step evidence and owned/module inventories, and this stage's failed/reused
history. Old supplier object bodies and old completed-evidence archives are
excluded. Standard output returns only status, counts, paths, and hashes.
The driver requests no archive retrieval or outbound transfer.

Version 2 reads the completed tar back and checks the exact unique regular
member inventory, sizes, and payload SHA256 against the captured input pins.
Every selected input is rehashed after packing; the full three-step chains and
all frozen/runtime bytes are checked before and after export. Successful export
metadata is written only after these checks. PROOF_RESULT.json records the
accepted proof chains before export, and the final successful RESULT.json is
written only after export validation; both the external evidence manifest and
final result retain the post-export check and validated archive pin.

The original v1 package, driver, test evidence, and mathematical source are
preserved unchanged. The v2 update changes only Python workflow and metadata.

Local regression tests use isolated synthetic Python fixtures; they do not
execute Lean and do not supply acceptance evidence for the mathematical owner.
