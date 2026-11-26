# Direct Git transport of frozen P2.1 evidence

`publish_p21_evidence_git.py` prepares evidence objects in a newly created bare
repository. Its default operation is **prepare only**. The explicit `--push`
option may create only
`refs/heads/evidence/p2-1-20261126-6c7864ad`, and only while that ref is absent.
This transport performs no Lean compilation, replay, audit or repack-verifier
substitution. It always retains `full_p2_complete=false`.

## Frozen inputs and source tree

The original transfer helper must retain SHA256
`5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d`.
The production PLAN must retain SHA256
`ac1d24aaf71dbc1f5cf89f8ab205f25fd58d8689726c81337a2499666bae068b`.
The publisher loads that actual helper file and reuses its `load_plan`, `freeze`,
`regular`, `unchanged` and original capture validation.

Every frozen asset, source stamp and planned part digest is checked before
cloning. Each source is checked again while its bytes become Git objects. The
archive's 409 parts retain their original 1,200,000-byte boundaries, apart from
the shorter last part, and every `git hash-object -w` result must equal the
planned Git blob SHA.

The clone is bare, filtered with `blob:none`, shallow and restricted to the
specified source branch. Its HEAD must equal the supplied full `--expected-base`
SHA. The accepted commit/tree from the original PLAN are fetched without blobs;
the 140 TARGETS source paths must have identical Git blob entries in the accepted
tree and this base. TARGETS itself is checked against the original FINALIZATION
input hash. The running publisher's bytes must also match its file in the base.

The source snapshot and accepted Git identities stay those in the original
PLAN (`00af183…` and `1de0453…`). The later transport base is recorded separately.

## Prepared tree

All base entries remain unchanged. Only files under
`docs/verification/20261126-p2-1/` may be added:

- `archive-parts/part-00000.bin` through the last planned part;
- `original-assets/`, containing lossless xz copies of the original export
  manifest, joint receipt/log/probe, finalization, verification and retention;
- `ARCHIVE_PARTS.json`, `LOSSLESS_ASSETS.json`, `TRANSPORT_METHOD.json`;
- `DIRECT_GIT_PLAN.json`, preserving the exact original PLAN bytes.

Existing identical evidence blobs are reused. A differing existing destination
is an error. The complete resulting tree is compared with the base plus exactly
the prepared additions before a commit is created.

Existing archive capture xz blobs in the pinned base are paired with their
existing raw-part blobs, decompressed, and checked with the unchanged original
`validate_capture`. Their actual job IDs are retained. The remaining parts are
identified as direct Git transport; no MCP tasks or captures are invented.
`base_mcp_captures_verified` describes this base only. Other completed captures
may be appended by root in a later evidence commit.

All committed manifests have `record_phase: prepared_before_push` and
`local_archive_verified: false`. Actual publication success is recorded only in
the post-operation run report. `ARCHIVE_PARTS.json` includes the existing
reconstruction convention's `full_archive: {bytes, sha256}` alongside its
complete, ordered parts array.

## Invocation

First publish the reviewed helper into the source branch and read back its
commit SHA. Pass that exact new SHA as `--expected-base`; do not reuse an older
base that lacks this helper.

```sh
python3 -I -B /absolute/checkout/verification/part2/publish_p21_evidence_git.py \
  --helper /absolute/checkout/verification/part2/transfer_p21_evidence.py \
  --plan /absolute/retained/raw-transfer-20261126-a/PLAN.json \
  --source-branch work/p2-1-formal-proof-20261125 \
  --expected-base BASE_AFTER_REVIEWED_HELPER_PUBLICATION \
  --work-parent /absolute/retained
```

Without `--push`, this creates only an owned local bare repository and prepared
commit. Add `--push` only for the separately authorized actual publication run.
The cloud job can use one CPU, 2048 MB memory and a timeout up to 3600 seconds.

The publisher uses the normal existing Git authentication. It does not inspect
credentials. Git trace variables are removed from its child environment;
garbage collection and automatic maintenance are disabled. Push uses
`pack.window=0`, `pack.depth=0`, `pack.threads=1`, and an explicit empty-ref lease:

```text
--force-with-lease=refs/heads/evidence/p2-1-20261126-6c7864ad:
```

The target is checked with `ls-remote` before cloning and immediately before
push. Success additionally requires the subsequent remote SHA to equal the
prepared commit. Push uses the same fixed repository URL as these ref queries.
The publisher supplies no overrides for normal hooks or signing configuration.
The transparent author and committer are
`P2 evidence exporter <p2-evidence-exporter@example.invalid>`.

The run report is saved beside the uniquely created work directory and printed
as JSON. It retains the actual clone/fetch/ref-query/push return data. There is
no automatic cleanup; after confirmed push and readback, root can preserve the
report and remove only this invocation's owned bare directory.

## Verification boundary

The tests use explicitly synthetic source bytes and temporary local Git
repositories. No test invokes Git push, a cloud task or Lean. Run them with the
unchanged original helper next to the test, or explicitly set
`P21_TEST_ORIGINAL_HELPER` for staging:

```sh
P21_TEST_ORIGINAL_HELPER=/absolute/checkout/verification/part2/transfer_p21_evidence.py \
  python3 -B test_publish_p21_evidence_git.py
```

The regressions cover preparation and byte reconstruction, every auxiliary
compression round trip, wrong PLAN/part SHA, a source changed during object
writing, wrong cloned HEAD, an already existing evidence ref, a source delta
from the accepted tree, and removal of trace environment variables.

After real publication, root still must download/reconstruct the full original
archive and run the original `repack_winner9_private_evidence.py verify` with its
source-Git checks. Direct Git transport does not complete that local gate.
