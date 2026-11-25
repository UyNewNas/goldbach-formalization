# P2.10 public certificate transport

## Intent and observed constraint

The completed public proof producer is commit
`94c7c507ab747cf4e05a4f19d8d4507cedfede38`, run `45611402948`, attempt 1.
All 36 numerical blocks and the collector succeeded. The collection artifact
`15041690180` is 635602594 bytes. The connected download tool rejects it with
`Artifact exceeds max size of 536870912 bytes`.

The receiving environment already holds the exact original public bootstrap.
The continuation must reuse that work and must not recompile or replay proofs.

## Approaches and implementation decision

Direct download is outside the observed per-file limit. Splitting the whole ZIP
would work but would transfer the already received bootstrap again. The chosen
implementation transports only the original index and 36 original block ZIPs,
then joins them with the existing exact bootstrap at the receiver. This is a
transport repair within the ongoing P2.10 continuation, not a change to its
mathematical scope or acceptance gates.

## Immutable source anchors

- Repository: `UyNewNas/goldbach-formalization`.
- Collection name: `p210-collection-45611402948-1`.
- Collection ZIP SHA256: `1965d3a92c336a4b1931835275e2602d14bef41bfd7cebcaeea3fa098ca597df`.
- Original index SHA256: `687c35f8ef018ad85e7cc68581dcadd98cd0acd22bd22f031dfd95966abfc70e`.
- Original bootstrap tar SHA256: `e17d879ab60ad21874b8b26ce20075a1b646af82ee18cf00749773ba5dc37370`.
- Resume plan SHA256: `46e739a5a5ddfa3ad6b0dd4697f1bf95bb9cbb21ef84ce1c7f32e2cb33162978`.
- Original importer SHA256: `b90f11e049080eff0ccc2d09e63f2d78ce88825791b5c4efdf6a92dc78be188c`.

## Producer and receiver contract

The transport-only CI job verifies the source artifact metadata, complete ZIP
bytes, exactly 38 original flat members, original index bytes, and every member
hash. It copies `index.json` and `block-08.zip` through `block-43.zip` byte for
byte. It streams and checks the omitted bootstrap, without including it in the
delivery. The output contains those 37 files plus `tail.json`.

`tail.json` has these exact top-level fields:

- `schema`: `p210-public-collection-tail-v1`.
- `source`: `repository`, `commit`, `run_id` (string), `run_attempt` (integer),
  `artifact_id`, `artifact_name`, `zip_bytes`, `zip_sha256`, `index_sha256`.
- `transport`: `commit`, `run_id` (string), `run_attempt` (integer).
- `bootstrap`: `filename` (`bootstrap.tar.gz`), `sha256`, `bytes`.
- `files`: the exact 37 delivered names, each mapping to `sha256` and `bytes`.
- `scope`: `modules` 598, `pages` 562, `rows` 8978,
  `terminal_integrated` false.
- `proof_compilation`: 0; `stock_replay`: 0.

The receiver verifies the new artifact metadata and ZIP hash, this manifest,
the original index SHA, and all delivered file hashes. It links the already
held, hash-verified bootstrap into an exact 38-file incoming directory. The
unchanged original importer then runs once, with installation enabled, and
independently validates all C/A/E bindings and origin counts. There is no new
proof compilation or stock replay; the importer's one version probe remains.

The source proof producer remains the original commit and run. A distinct
transport commit and run receive zero proof credit. Full P2.10 integration
remains false until the outstanding preparation and final gates pass.

## Publication and invariants

Remove only the push trigger of the completed numerical workflow in the same
commit that adds the transport job. The new job's push paths include only its
own workflow and transport script. Preserve manual dispatch and every original
proof job, C/A/E driver, Lean source, resume plan and importer byte. Check for
open PRs and the expected branch head before updating the branch.

No private environment export, credentials, signed URL or cache record is
published. The receiving wrapper remains a local operational script.
