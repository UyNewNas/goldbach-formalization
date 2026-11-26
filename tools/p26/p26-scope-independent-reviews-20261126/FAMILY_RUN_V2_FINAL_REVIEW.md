# Independent final source review: Cell01 family runner v2

Conclusion: **the identified historical-schema and reuse issues are resolved
in the reviewed source; no additional concrete source-level blocker was found**.
This is a local source checkpoint. It grants **zero new Lean acceptances** and
does not claim that P1/P3 preflight, runtime validation or a new owner has run.

Reviewed `family_run.py`:

```text
bytes: 69366
sha256: 52666297d9fac67bcb50416f2f9405c38c5d31603dd8679f97620ca441281601
```

The machine-readable `FAMILY_RUN_V2_FINAL_REVIEW.json` records the corresponding
final local file/release pins. A later change to this source requires a new
review record; this conclusion does not automatically cover changed bytes.

## Concrete issues reviewed and resolved

1. **Original row001 single-owner SUCCESS schema.** The index dispatcher now
   recognizes only the explicit original row001 target, ordinal 1, successful
   one-target terminal marker, unchanged-input flag and exact three-mode row
   record order. Its three original result hashes remain separately fixed.
   This does not admit an arbitrary `succeeded` document as an acceptance.

2. **Accepted interface pilot prefix schema.** The dispatcher accepts the
   actual family prefix representation in the fixed eleven-owner order and
   checks `accepted_steps`, `accepted_owners` and the non-completion scope.
   Full-family success and export-pending statuses require all 33 records.
   A three-record interface prefix cannot claim all eleven owners.

3. **Original row001 input location.** RUN and SUCCESS use the exact original
   attempt filenames. The input snapshot must stay within the original stage
   and agree with the fixed receipt → command → RUN input pin. The unsupported
   assumption that the input snapshot must itself reside in the attempt
   directory was removed.

4. **Imported pilot prerequisites.** Normal has no self-prerequisite; kernel
   retains its normal receipt; owned retains normal and kernel. Original seal
   and command prerequisite lists must match these exact original references.
   All three lists are no longer incorrectly required to be empty.

5. **Canonical and generic authorities.** Canonical RUN/INPUT/RESULT byte
   identities are tied to the fixed source package's original 23rd
   SUPPLIER_DELTA pins. Generic source/object/context and the three actual
   `generic-v2-r14` seals retain their original accepted identities. The new
   join does not infer acceptance from a source manifest or a module name.

## Evidence supporting actual schema compatibility

The existing original row000 archive is 886,800 bytes, SHA256
`1b88f393c1ccb1e9cd3c9804e86277ab9089badcd7b68b3f417cf74b6a02cea7`.
Its real normal/kernel/owned command bodies use `input_fingerprints`, and its
owned output contains both IMPORTS and INVENTORY markers.

`FAMILY_ROW000_SCHEMA_FIXTURE.json` records a direct call to the candidate
`old_chain` using 17 exact original archive member bodies read in memory. It
passed the real three-mode shape, 647-module project source closure and 1111
canonical-module metadata. That diagnostic ran against its separately
recorded earlier candidate hash; it is retained as a schema fixture, not
relabeled as a final cloud or proof test. No archive extraction, object/source
reconstruction or Lean command occurred.

For row001, the existing generated-source manifest records a 2,710-byte audit
with SHA256
`02535799e4db7ef71082a2655f50dfff3a822f6c4ab4797b6e994ec537cc153a`.
An in-memory substitution of the module name in the existing row002 audit
source produces exactly that size and hash and includes the IMPORTS marker.
No row001 receipt, log or completed archive was read or reconstructed to
establish this source fact.

The existing finite selected-row exporter requires one IMPORTS marker, a
complete owned inventory and the exact 400-module per-row project closure.
The generic historical context/three-seal field shapes were inspected before
the P1 outage. No legacy fallback that drops the import inventory requirement
is needed for these known owners.

## Reuse and original row001 boundaries

Foreign owner import is restricted to the independently accepted interface
pilot. It requires the fixed pilot-v1 code manifest, exact source/audit/object,
three original chains and per-module equality between the original owned byte
inventory and current project/runtime providers. It records an import marker
before installing the object and restores accepted anchors without invoking
Lean. Original new-owner evidence is retained unchanged with an explicit
relocation map. It does not create a second proof run for an accepted pilot.

The optional row001 path operates only on the original source host at its
original stage. Relocation registration for protected receipt bodies remains
forbidden, archive files are rejected, and no old receipt/log body is copied
into the new stage or final export. It checks the fixed three results,
399 suppliers, 798 installation entries at provider and installed paths
(1596 live pins), the existing kernel addendum and 292 owned declarations.
New metadata retains pins and the compact validation result. Actual use still
requires the original files to be present and to pass the live validator.

Successful raw command results, accepted seals and accepted anchors remain
restoration obligations if an object or dependency is missing. They are not
cache misses that permit proof replay. Failed normal output preservation is
restricted to an explicit non-success, nonzero-exit normal result with no
prior object; successful output cannot enter that path. Preserved failed
bytes are moved to an unused path rather than overwritten or credited.

## Scope and validation limits

The runner remains tied to the frozen 802-module source closure and eleven
new original-floor owners. The first interface uses exactly 625 old suppliers;
the pilot does not need finite-row bodies. Full-family completion requires
33 accepted mode records plus the final evidence export/readback. Runtime
trees and actual provider bytes remain subject to the original complete-tree
checks; metadata pins alone do not establish that live check.

The implementer reported 31 passing local synthetic recovery/schema tests
before freezing. The independent review did not broaden or repeat that test
suite. Its additional execution was the explicitly limited existing-row000
schema fixture described above.

P1 access is unavailable and no new cloud action was taken during this review.
No existing Lean source was modified, no compiler was launched, no accepted
owner was rerun, and no new theorem/floor/integral/P2.6 acceptance is claimed.
