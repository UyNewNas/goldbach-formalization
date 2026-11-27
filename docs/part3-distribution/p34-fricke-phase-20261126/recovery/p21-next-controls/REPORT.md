# P2.1: frozen next control reads

## Decision

Read exactly two previously unread control bodies as inert text: **ordinal 306 (670 bytes)** and **ordinal 13854 (1,766 bytes)**, **2,436 bytes total**. Stop after those two bodies. The exact selectors, paths, hashes and offsets are in `plan.json`.

The 670-byte `owner-native-context.json` can establish the native owner's scope. The 1,766-byte `checkpoint_original_protocol.py` is the smallest member whose name directly identifies the checkpoint protocol. Its text may identify the format or the fields that a later read should select. These are prioritization inferences from metadata; neither body has been read in this planning task. Treat the Python file as data only.

The parent explicitly froze this next-read scope at the two control members. **CHECKPOINT.json is excluded from the next read.** No implementation or runner is supplied.

## Evidence used

The original inventory is `/workspace/library-files/p34-evidence-staging/continuation-20261126/p21-fingerprints/member-fingerprints.jsonl.gz`: **1,780,209 bytes**, SHA256 `e603930b3a3731fc75202d12fb9a11c57f77a8a3193c5b016c86573d6849620a`, decoded JSONL length **14,523,449 bytes**. Its 13,859 member rows supply all selectors and the classification below.

The completed five-manifest result at `/workspace/library-files/p34-evidence-staging/continuation-20261126/p21-five-manifests-v2/result.json` is **4,800 bytes**, SHA256 `c5e0f0781613506f750a42d5d26277440b7586d29f6d924fc3550382ca2c523c`. It records five completed selectors, 360,982 JSON values, zero boundaries or exact matches, 13,854 transit-only members, and the exact full TAR EOF identity. This task read that receipt only and did not reread any of the five manifest payloads.

## Remaining JSON classification

After subtracting the five completed selectors, the inventory labels **1,853 JSON identities** totaling **4,116,488,339 bytes** as previously new. Names alone do not establish their internal schemas.

| Metadata name category | Identities | Bytes |
| --- | ---: | ---: |
| Native `*.setup.json` | 711 | 1,954,665,901 |
| Native `*.trace.json` | 514 | 1,975,576 |
| Native qualified-module/package JSON | 514 | 2,026,779,030 |
| Native CHECKPOINT/QUALIFICATION/STAGED/batteries/receipt JSON | 5 | 75,854,073 |
| Named audit JSON | 73 | 17,575,921 |
| P2-private JSON | 33 | 3,636,895 |
| EXPORT_METADATA and two context compile-record JSON | 3 | 36,000,943 |

The first three groups comprise **1,739 native module/sidecar names and 3,983,420,507 bytes**. Qualified-module names belong to MathlibNt, AnalyticNumberTheory, PrimeNumberTheoremAnd and Architect. These metadata names supply no target-specific reason to decode that bulk region. They are left unselected, without asserting that their payloads contain no source.

There are also 11,539 remaining new Lean identities: 11,490 under native paths and 49 elsewhere in the worktree. Across the entire inventory there is no `Part3`, `Fricke`, `DoubleLambda`, `PhysicalE3`, `E3Block`, `ColorWindow`, `MediumPhase` or `MediumPhysical` member-name hit. This is a member-name observation, not a global source-absence result.

## Deferred checkpoint: exact identity and unresolved risk

- Ordinal: **13846**
- Full member name: `packages/all.tar.gz/context/native/056eab7ace6a9e1a3881273c5ffe135af12212d5795304d2be2cef543176ba40/files/3dda7bb0d87b9ea22adf05b124df602a4c0c0c0b6d823e5ce63f646a0a8cb168-CHECKPOINT.json`
- Content bytes: **67,075,207**
- Content SHA256: `aa44099f53c82b885c3bf56cdbaa74055d5b583a9e941facb47ffd2b0f01be2a`
- Header offset: **4,237,140,992**
- Data offset: **4,237,142,528**
- Payload end offset: **4,304,217,735**
- TAR type: `0`; codec hint: `json`

The `3dda7bb0…` filename prefix is not this member's content hash. Its independent content hash is `aa44099f…`.

Current metadata **cannot rule out project-source fields or embedded source inside this checkpoint**. No internal field path has been observed, so there is no justified field selector yet. The checkpoint is 33,520,775 bytes above the existing 32 MiB document cap and 33,657 bytes below 64 MiB. Its size does not justify a global cap change. The two frozen control reads may supply the schema evidence needed for a later, separately bounded field read.

## Transport and stopping boundary

The existing P2.1 outer is **44,304,524 bytes**, SHA256 `92c1067a1694ea74af4d15ee841199ab72094f2147b7651e77cf21f60e68faf4`. Preserve the single-stream XZ memory requirement **67,175,064 bytes**, full decoded TAR length **4,349,603,840 bytes**, and TAR SHA256 `782ed338be356af00590c74dc94b64b91f199f147544c1306b930127762195c8`.

The two selected bodies must match exact names, ordinals, offsets, lengths and SHA256 values. All other members remain transport-only. Preserve the previous 118 prior-complete, 196 same-run and one limited native-snapshot exclusions, together with compatible completed identities from resident receipts. The five completed manifests remain excluded.

Return the two bodies and any actual schema/owner facts, then stop. No automatic traversal of referenced paths, checkpoint decoding, unrelated compiled-object decoding, script execution, compilation or global absence claim is authorized by this plan.

This planning task performed metadata reads only and wrote this plan/report. No archive payloads or source bodies were scanned.
