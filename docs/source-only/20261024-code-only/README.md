# SOURCE_ONLY checkpoint — UNCOMPILED

This checkpoint archives installer-owned Lean source bytes and the installation ownership records. Every archived source is uncompiled and receives zero proof credit. No Lean/lake invocation, checker, numerical replay, local proof audit, or CI launch was performed for this checkpoint.

The accepted ROOT state stays at 266 modules and 8851 serialized declarations (8832 distinct constant full names). The main result remains OPEN at 30%. Root `ImbalancedChen.lean`, all ROOT266 accepted sources, existing user changes, and `.gitattributes` are outside the checkpoint boundary.

`source-manifest.json` records each archived source's exact SHA-256 and installer evidence. `ownership-ledger.snapshot.json` fixes the installer ledger bytes. `installation-manifests/` preserves batch decisions, including HOLDs. `import-dependencies.json` is a text inventory of project imports and their availability in the base commit; it is not compiler output. Missing unowned baseline dependencies remain HOLD and are not silently included. Clean-checkout compilability is not claimed. Sources excluded from the selected hub may still be retained as explicitly uncompiled archival material; inclusion in this archive is not a readiness or proof-acceptance claim.

The source blobs are made from a fixed byte snapshot using native Git `hash-object --no-filters`, with an isolated temporary index based on the parent commit. The original working-tree index is preserved byte for byte. Updating the branch to the new commit may consequently show staged differences against that new HEAD; those are an effect of retaining the old index and must not be cleared automatically.

The commit message includes `[skip ci]`; no CI run is requested. The local source archive receipt records the resulting commit, tree, remote branch verification, and original index hashes after push.
The frozen intake contains 418 source files (35,746,854 bytes), with a 302-import selected hub. Exactly three installer transactions replace Block18Data, Block27Data, and Block29Data with header-only repairs. The original frozen ownership ledger and these three explicit deltas together define the archived bytes; later writer batches are excluded. The import text inventory records 14 unowned dependencies absent from the base tree as HOLD.
