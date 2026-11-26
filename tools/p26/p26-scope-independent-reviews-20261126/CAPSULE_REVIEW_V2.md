# Independent review of corrected supplier capsule v2

Status: **static review passed; live P1 execution and byte readback are not
claimed**. This supersedes the two open source-review findings in
`CAPSULE_REVIEW.md` for the separately named v2 and the new recovery candidate.
The possibly submitted v1 remains unchanged.

Reviewed inputs:

| File | Bytes | SHA256 |
|---|---:|---|
| build_p1_minimal_capsule_v2.py | 20560 | 9cd6baaeecf17acdea43a33748e942d2c2132bc624202d8d9bb2c5525287c986 |
| P1_CAPSULE_REQUEST_v2.json | 271339 | b07ae3d4fe26889b33438694aa7c011e2a7842c1d53478425dfc0633072612b8 |
| inspect_p1_capsule_recovery.py | 7796 | 50f76cdc10d43cfcd0c6781c19783ce7a00ce20c2fcb2d0e3a9fbf5ba58017f1 |

## Historical prefix connection corrected

The v2 builder reads the already pinned C-prefix EXPORT_MANIFEST and indexes
its exact original path/size/SHA256 identities. Its new `anchored` operation
requires a historical member before reading each current RUN, PARTIAL,
ROW_ACCEPTED, source, object, audit, command, result, log and owned inventory.
It also binds the original stage's input snapshot, installation, supplier and
verifier manifests and driver/helper controls. The nine object identities are
therefore constrained by the fixed original export before being selected.

The existing `export_selected_rows_v2.py` schema was checked directly. Its
manifest members preserve absolute `path`, `bytes`, `sha256`; the source
explicitly adds the controls, selected source/object/audit bodies,
ROW_ACCEPTED records and the same three-mode dependencies required by the v2
adapter. The compact already retained C-prefix CLOUD_EXPORT_SUMMARY confirms
the manifest/review pins and exactly098–106, nine targets,27 steps and2628
owned declarations. This review did not retrieve that cloud export body or
its archive.

The v2 request changes version/destination metadata only. Its189 selected
modules,14 source-body choices, source pins,178 canonical object pins,
row000/generic identities and nine prefix ordinals remain equal to the
independently checked v1 request and exact P3 missing inventory.

## Recovery classification corrected

The new inspector validates canonical paths, including ancestors, and rejects
all `row001` paths. It inspects only fixed control/output filenames. Before
using a summary it requires the declared archive, manifest, request and
builder paths to equal those fixed locations and their complete current pins.
It checks schema/version, success status,189 objects,14 sources,203 payloads,
204 archive members, scope flags and exact request/manifest module and member
sets. It distinguishes missing controls, partial metadata, partial archives,
empty output, invalid output and a completed artifact matching recorded
readback pins. It performs no writes, overwrites, deletion or rerun.

Its completed-v2 classification deliberately remains pending actual MCP task
success and live workflow review. It does not turn a summary or matching tar
hash into a proof acceptance, and it does not reopen/replay an old owner.

## Unchanged accepted boundaries

The payload remains189 `.olean` files plus14 `.lean` files and the new manifest.
There are no row001 files, receipt/log bodies, historical archives or entire
completed evidence groups. Prefix scope remains nine rows; no full-C claim is
made. Generic uses the original pinned context and all three accepted seals;
row000 object/seal identities remain the original published ones.

Packing retains exclusive creation and the full204-member name/type/size/hash
readback followed by watched-input rehash. Existing output requires recovery;
the builder does not silently replace or regenerate it. Since the original
submission was ambiguous and all cloud access is suspended, this source
approval does not authorize a blind repeated submission.

No cloud tool, Lean command, Git mutation or blocked row001 evidence-body
access occurred during this review.
