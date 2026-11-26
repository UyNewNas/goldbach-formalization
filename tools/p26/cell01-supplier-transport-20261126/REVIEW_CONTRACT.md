# Cell01 three-file Git transport candidate

Route: **awaiting root review and explicit execution instruction**. No upload,
Git object creation, commit, push, P3 fetch, provider extraction or Lean command
has been executed by this candidate. The root selected this route after finding
no suitable direct P1-to-P3 private file transfer capability.

## Exact publication boundary

Repository: `UyNewNas/goldbach-formalization`.

New branch:
`work/p2-6-cell01-supplier-transport-20261126-557a12f3bcd7`.

The isolated root commit has no parents and exactly these three root files:

| Tree member | Bytes | SHA256 |
|---|---:|---|
| MANIFEST.json | 409031 | 8d001ee3a7bfbe4c2d6f7708c86b59977d3212053ba54bbe697143ed0a2064df |
| TRANSPORT.json | 2118 | 07aee0214bc3e209c0a97eed04f6db88122d38155e751abdbd0a17ffa5d587eb |
| objects-and-missing-sources.tar.xz | 39794840 | a16d07fe3489855e1c69a5c2658824b8b7fce7fc44ab527d3a88eb5e8451899b |

The capsule contains exactly the previously verified 189 objects, 14 source
bodies and its original manifest. It contains no row001 files or old receipt or
log bodies. TRANSPORT.json explicitly assigns zero new proof credit and binds
the successful original P1 build task, original builder/request pins and scope.
This code, deployment command and operational receipts are not tree members.

## P1 operation

`git_transport.py publish-p1` uses only the existing bare repository
`/workspace/p26-continuation-59264dd64286/publication.git`. It reads both origin
fetch and push URLs internally and requires exactly the authorized GitHub
repository. Credentials, authenticated URLs, raw Git stdout and stderr are never
printed or written to operational reports.

The new branch must be absent before object creation and immediately before
push. All three inputs are fingerprinted, MANIFEST scope is checked, and the
three blobs form a new root tree using Git plumbing. No checkout or index is
used. A PREPARED_COMMIT.json receipt is written before the ordinary non-force
push. The push names exactly one destination ref and disables tag following,
mirror mode and recursive submodule pushes. Existing user hook and signing
configuration remains active; a check or signing failure stops the operation.
Afterward the exact remote
ref is read back, input pins are rechecked, and the previous bare repository
HEAD bytes and resolved HEAD value must remain unchanged.

The source/request/output locations from the prior capsule build are not
modified. The two fixed capsule inputs are read directly from
`/workspace/p26-continuation-557a12f3bcd7/supplier-capsule/missing189-objects-and14sources-v2`.
Publisher control files and operational receipts go under the fresh directory
`/workspace/p26-continuation-557a12f3bcd7/cell01-git-transport-publish-v1`.

An interruption or rejection leaves evidence for recovery. There is no retry,
overwrite, deletion, branch reuse or force path. Automatic tool approval
rejections must be reported separately with their original reasons.

## P3 receipt operation

After successful publication yields its actual 40-character commit,
`git_transport.py fetch-p3 --commit COMMIT` initializes a new bare fetch
repository in the previously nonexistent directory
`/workspace/p26-cell01-supplier-transport-557a12f3bcd7`.

It reads only the authorized repository, requires the transport branch to name
the selected commit, and performs a shallow, tag-free fetch of that exact
commit. It checks the actual commit has no parents and the root tree contains
exactly the three regular blob names and sizes. Each blob is SHA256 checked
before exclusive writing into `payload/` and then checked again after writing.
Its TRANSPORT bytes must equal the reviewed local metadata.

RECEIVED.json records the actual commit and complete received pins. The archive
is not opened or extracted. No existing provider, original source stage or Lean
file is modified, and no Lean command is available in this script.

## Local verification

The focused synthetic tests cover wrong repository/host, existing or ambiguous
branch responses, a parented commit, an extra tree file and a changed payload.
They do not run Git publication, Lean, original proof steps or old test suites.
