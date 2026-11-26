# P2.1 direct Git evidence transport

The original cloud finalization and retained-copy verification have passed. The remaining task is to publish and independently recover the exact evidence bytes. This transport plan grants no Lean, kernel or mathematical credit, and keeps `full_p2_complete=false`.

## Observed basis for the change

The P2 task `be15fc6e2c5f405a9527353ceacfa220` performed a standard Git push dry run to `UyNewNas/goldbach-formalization`. The actual command returned zero and reported a new branch. It did not create that branch. The complete original MCP call capture is in `DIRECT_GIT_PREFLIGHT.json`; authentication material was not read or exported.

The existing MCP method has actually completed archive parts 0–4, 136–147 and 272–283: 29 parts, 34,800,000 archive bytes. Their raw calls remain in lossless capture blobs and their original small records are preserved byte for byte in `TRANSPORT_RECORDS_MCP_SUBSET.tar.xz`. The package's `PARTIAL` label refers to its coverage of the 409-part frozen plan. It does not claim that the other 380 parts were executed as MCP tasks. Seven auxiliary part captures were also recovered.

## Publication layout and gates

The code branch remains `work/p2-1-formal-proof-20261125`. The complete payload will be published on the separate evidence branch `evidence/p2-1-20261126-6c7864ad`, based on a pinned code commit containing the reviewed transport implementation. This keeps the complete payload independently retrievable for later verification and compilation work.

The publisher must use the unchanged original transfer helper, SHA256 `5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d`, and the unchanged transfer plan, SHA256 `ac1d24aaf71dbc1f5cf89f8ab205f25fd58d8689726c81337a2499666bae068b`. All source assets must match their frozen size, whole-file hash, part hashes, Git blob hashes and file stamps.

A fresh bare clone uses a blob filter and an exact expected base commit. The 140 selected source Git blobs must match the accepted commit `1de0453bee55bf1128be422787216937b8fda9c9`; the running publisher must match its bytes in the expected base. The new tree may only add the declared evidence paths and must preserve every existing entry. Actual MCP captures present in the base are replayed through the original capture validator.

The archive remains the exact original 490,564,596-byte file with SHA256 `066a46e41e34578a2adbf2a1120e8aba0470dfde44d6052bc8576d8fcb9aa212`. Its 409 Git blobs must match the original part plan. Auxiliary originals are compressed losslessly and retain explicit original and compressed byte/hash bindings.

Preparation is the default. An explicit push may only create the previously absent evidence ref, with an expected-empty lease, using the existing normal Git authentication, hooks and signing configuration. The observed remote ref must equal the prepared commit. Pre-push manifests describe preparation; the actual push result belongs to a separate post-operation report.

## Independent recovery still required

After publication, retrieve the exact Git objects by their frozen IDs, reconstruct the complete archive, verify every part and the full written file, and run the unchanged `repack_winner9_private_evidence.py verify` against the accepted source commit. Recover and check the original export manifest and full joint receipt as well. Only then update the final closure/publication status and read back the final remote heads.

The mathematical source snapshot remains `00af18335dcebcc5e24571e33be7791ff718fbff`. The query closure and its documented guards remain the accepted scope. Direct Git transport does not supply any downstream integral, historical serialized-array, final-constant or full-P2 theorem.
