# Full87 v3 native source gate

**Source-level verdict.** The successor addresses both corrections from the full87 v2 review. The four frozen inputs below are suitable for publication as source-gate configuration. No installation-period receipt, post-compile receipt, object, or fresh kernel replay was produced by this review.

| File | Raw bytes | SHA-256 | Raw Git blob |
| --- | ---: | --- | --- |
| stage_native_research_overlay_v3.py | 15242 | `29ffc5cca85a21751e5a423a4f96929ba06f7c4cc363ada29f7b0b69eb37bf38` | `f5fde14bff2cd3e5d9fdb4fea6b1938c8dd2e824` |
| NATIVE_RESEARCH_OVERLAY.json | 20177 | `fe5c4f8720d9649ab500589273a21c64f982a85ad724d84191a5df3b659267b9` | `9b895e3e3f478a47a52975bc7fe55b0b7acd0cb3` |
| HISTORICAL_METADATA_FIELD_ERRATUM.json | 2032 | `7cad5087a6d135c03bf59237918e825e79e83f075cebd6f737255117b2f8ffda` | `a5035ee59876fa5dbd8d3575dd8f25d4ecb18000` |
| SOURCE_GATE_V3_STATIC_CHANGE_NOTE.md | 2185 | `81317f5d8f7a312907e9416d8fc122d921d24c5b2b9127f604481319e19b3239` | `3577cde7c71fba9bac596be97834ac7c89660591` |

The original native plan is byte-identical to the earlier independent 43-row Git/source mapping at native commit `09b97db5764ade1246bfb77206baa1b124760958`. The v3 program retains exact research Git blob, size, canonical path, installed-byte readback and raw SHA-256 checks. The physical untracked census includes ignored files outside the root `.git` and `.lake`, records source/loadable identities and rejects observed unexpected loadables or symlinks. The callback passed to `os.walk` re-raises each directory-enumeration error.

Verification mode requires the original installation receipt and its independently bound SHA-256. It checks the source commit, run ID, attempt, native revision, plan SHA-256, acceptance-manifest SHA-256, gate-script SHA-256 and original install mode. The prior 43 rows must have unique expected canonical paths. All prior raw-byte identities and absolute paths are compared to actual files at the verification point. The complete recorded post-install physical census must equal the current pre-verification census. A missing or mutated input fails without repair. Original source blobs and resulting canonical files are read again. The new receipt binds the exact original receipt, its ordered source rows and its observed post-install census. The future driver must independently retain the installation receipt digest before compilation and bind the actual compiler observations between these two endpoints.

I independently recomputed the hash of the sorted 1,607 distinct source-module names from the previously reviewed v2 manifest. It is `7182083990021cce01c1e357f8de8148e636a4c24d7613c00be0b3328ec5f543`, as embedded in this source. The new gate requires the exact historical set as a subset of a duplicate-free future census, requires all 43 canonical native modules, and records the identity of the whole selected census. The future manifest must bind this gate script and plan. Validation that its enlarged set exhausts the actual new paid-I87 closure remains a separate review.

The historical erratum correctly distinguishes five changed blob fields in the 41-entry file table from the four top-level metadata changes. It identifies the original 1,046 names, 1,025 matching source bytes in v1, and 1,021 matches in v2. These counts agree with `FULL87_V2_METADATA_REVIEW.md` (SHA-256 `244c35a746e127e1e76d7d9b52c51fbf2710c35340a687814972b0e6b80bd01f`).

The source receipt explicitly records actual compiler flags and ABI as unverified. The 43 successful guarded native source commands, real setup/import/IR/plugin/object receipts, source-data and runtime binding, full fresh replay, and every selected unelided type and transitive axiom gate remain to be observed remotely. A readable, unchanged tree at two instants gives source identity at those instants. The actual compiler reads still require their producing command and import evidence. The old 27 targets and the new main row 84 have distinct evidence requirements.

I read the source and JSON, inspected the Python AST without importing the module, and recalculated byte digests. No stage, checker, guard, numerical evaluation, compilation or CI was run.
