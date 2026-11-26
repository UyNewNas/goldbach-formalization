# Independent minimal supplier capsule review

Status: **changes requested for the C-prefix provenance join; exact transport
scope and archive readback design pass static review**. No cloud task, Lean
command, evidence reconstruction, or original-file mutation was performed by
this review.

Reviewed frozen builder:
`tools/p26/supplier-join-20261126/build_p1_minimal_capsule.py`, 18,565 bytes,
SHA256 `f641496f2a875f36a150ad50903cc6f4e1d790e532f0477e438cd72742b4dc70`.

Reviewed request:
`tools/p26/supplier-join-20261126/P1_CAPSULE_REQUEST.json`, 271,284 bytes,
SHA256 `b6e34dc6d72abcd1969dd31b04cbda7a78c3deca0f0b7d018258cf69416fbf7a`.

The initial upload may have been accepted despite its connection timeout. These
two files and that upload command must remain unchanged. Any builder correction
belongs to a separately named version, after read-only recovery identifies the
remote state.

## Findings requiring action

### C-prefix history is hashed but not joined to its accepted export

`prefix_validation` hashes the fixed `EXPORT_MANIFEST.json` and
`INDEPENDENT_REVIEW.json`, then reads current RUN, PARTIAL, ROW_ACCEPTED and proof
records without comparing those identities to the fixed export's member pins.
The nine initially unknown object identities are filled from the current
ROW_ACCEPTED bodies. The live chains receive substantial validation, but the
fixed historical export is not yet their identity authority.

Use the existing export manifest schema to bind the exact original RUN,
PARTIAL, nine ROW_ACCEPTED records, 27 result references, source/object pins and
their command/log/audit dependencies to the already pinned export identities.
Keep the original paths and bytes. No receipt body needs to enter the new
transport archive. This is a provenance join to existing evidence, not a new
acceptance claim or proof run.

This finding was sent to `p26_supplier_join` for a separate v2 correction.

### Recovery must identify a complete immutable output before reuse

The initial builder refuses an existing output directory and uses exclusive
file creation throughout. It will not overwrite an output, but it is not a
reentrant builder. An interrupted or ambiguous submission requires read-only
inspection; it does not authorize rerunning the same output name.

The unsubmitted recovery candidate initially followed `SUMMARY.archive.path`
without first requiring the fixed expected archive path, and checked only
final-component symlinks. It also needed explicit complete/partial/mismatched
classification with summary status/counts, builder/request pins, manifest pin
and archive pin checked together. These corrections were sent to the supplier
agent for the recovery candidate. A successful summary alone is insufficient.

## Confirmed scope and byte identities

- The request selects exactly 189 distinct modules: 178 canonical suppliers,
  one original row000 floor bridge, nine finite rows098–106, and one generic
  original-floor transport.
- It includes exactly 14 source bodies. Every requested source size/hash equals
  the fixed family SOURCE_MANIFEST entry. Every canonical source provider and
  canonical object size/hash equals SUPPLIER_DELTA.
- The request's SOURCE_MANIFEST and SUPPLIER_DELTA pins match the actual local
  files. The separate machine-readable review records the exact missing-set and
  source-body-set comparisons against P3_MISSING_FINAL.
- Row000 uses the previously recorded object
  `2c5fb7d0119b62728cecdf6fa98d07d890c3ac4fc67d7b7e3d9f5f3f72442d75`
  (72,552 bytes) and the original normal/kernel/owned seal pins. Its source is
  `044746b6376ae5efdac05dd97b77ba9840c91435001acf3e7a402015b272ede8`.
- Generic uses the original accepted object
  `7affb7b9a94589a3463b00f84663c4c5fdc659445cd93769c00fc0a13edc4266`
  (120,672 bytes), source
  `9f4b64321975f8eb567484982abc622ee77ac222c90a6d117b2acc7a0f39b574`,
  fixed CONTEXT, and all three original accepted seal pins. The original
  `GenericFloor_verify_v2.validate_step` is reused for those chains.

## C-prefix scope and proof-chain checks already present

The builder requires the original C invocation to select098–143, its preserved
PARTIAL marker to credit exactly098–106, and its remaining ordinals to be
exactly107–143. It rejects contradictory SUCCESS/STOPPED markers. Its 27
records must be in row-major normal/kernel/owned order. Each row must have
`PASS_NORMAL_KERNEL_FULL_OWNED`, the correct original ordinal, the same runtime
context, and292 owned declarations. Each existing result is checked with the
fixed original finite batch validator; kernel logs identify the exact module;
full owned inventories and permitted axiom sets are checked. The builder
explicitly reports `full_C_batch_claimed: false`.

These are real existing-chain checks, not merely finite-data evaluation. The
remaining provenance finding above concerns their connection to the fixed
historical export, not the row range or command-mode coverage.

## Row001 boundary

No request entry contains `row001`, including the permitted independent object.
The builder's canonical-path check rejects any path containing `row001` before
opening it. The selected original finite/generic validators do not traverse a
row001 receipt group: finite validation reads only selected row bodies and
shared metadata, and the generic source closure contains no finite-row owner.

The tar payload consists only of189 explicitly selected `.olean` files,
14 explicitly selected `.lean` files, and one newly generated MANIFEST. No
archive, receipt, log, ROW_ACCEPTED body, raw RUN/PARTIAL body, or full historical
evidence group is packed. No blocked row001 completed archive was opened by
this review.

## Packing and limits of this review

The builder freezes selected source/object bytes before packing, rejects
unlisted sidecars, requires203 unique payload members, and adds one metadata
manifest. Readback checks all204 regular members, exact names, no duplicates or
path traversal, sizes and SHA256 hashes. It then rehashes watched original
files before writing a success summary. All output writes are exclusive and
old source/evidence files are only read.

The review confirms this source-level behavior and the local request pins. It
does not assert that P1 has executed the builder, that live files still match,
that an archive exists, or that the cloud readback has passed. The transport
archive also does not replace the final executor's original evidence and
runtime validation.
