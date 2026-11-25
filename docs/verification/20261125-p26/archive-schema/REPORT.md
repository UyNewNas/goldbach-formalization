# Saving19 exact schema owner

The 5,399 bytes from `parseInteger` through `decodeMoments` are moved unchanged into the genuine `P2OriginalSaving19ArchiveSchema` module. Their SHA256 remains `21b86bcf4e04123dc6841cd25e50dcd073ecd9c9ac4c077b0174578a96c57a30`. The original namespace, public definitions, structures, field types, defaults, deriving clauses, rational parsing, and all decoder bodies are preserved.

This owner imports the original `SourceJson` and Mathlib rational definitions. It allows actual per-cell typed decoding proofs to use the real definitions without importing all 26 raw inputs and the 217-module analytic supplier closure. It is an intended production module, with no stubbed declaration, axiom, placeholder proof, or altered parser.

Schema normal compilation and independent kernel checking both passed locally, about 2.14 seconds each, within the unchanged 4 GiB / 180 s / one-thread budget. The existing reader object was copied byte for byte and not recompiled. No raw file was read, no concrete typed decode was established, and no P1 all-owned acceptance is claimed.

The accompanying Core candidate imports Schema and removes exactly the moved decoder block. Its original getters and two exact parse-ofList bridges remain unchanged. The combined public named declaration inventory is identical with no duplicate FQN; generated private declarations will receive their own new owner audit. The new Core has not been compiled, and the v2 Core's old 224-export acceptance is not transferred.

The already published v4 first-seven input job remains pinned to its original commit and unchanged source files. It does not run the old v4 Core. After the remaining unchanged input owners are accepted, the new Schema/Core will be accepted separately. Any prior input receipts must keep their actual source commit and be checked against identical source/object/import/runtime/input context; they must not be relabeled or recompiled merely because this source layout changed.

All original concrete parse-success, cell-shape, row-shape, Q80/Q96, and ownership obligations remain open until their own proofs and checks succeed. This module split does not discharge them. See `SOURCE_MANIFEST.json`, `SOURCE_ORIGIN.json`, and `logs/` for exact fingerprints and local results.
