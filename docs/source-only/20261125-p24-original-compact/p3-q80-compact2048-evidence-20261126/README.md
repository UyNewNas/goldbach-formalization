# Full2048 P3 diagnostic evidence

This directory preserves the complete compressed evidence archive for the isolated P3 original-Q80 diagnostic with 2,048 proof blocks and 131,072 source-node facts. It does not grant canonical finite-A or full-324-module acceptance credit.

The original `evidence.tar.xz` is stored as three consecutive binary parts because a single base64 upload exceeded the tool's 16 MiB request-body limit. Splitting changed no archive bytes and omitted no evidence. The initial failed request is retained in `github-single-blob-upload-failure.json`; successful part-blob responses are retained separately.

## Rebuild and verify

Download `archive-parts-manifest.json`, `rebuild_archive.py`, and all three files under `archive/`, keeping their relative paths. Run with Python 3:

```sh
python3 rebuild_archive.py --output evidence.tar.xz
```

The script uses only the Python standard library. It verifies each part's size, SHA256, and Git blob SHA; concatenates parts in the declared order; verifies the exact complete archive and uncompressed tar streams; and hashes every tar member. It does not overwrite an existing output: an existing output must already match the complete archive hash. It does not extract member files.

The reconstructed archive is exactly **18,737,284 bytes**, SHA256:

```text
d7bffacf6698777981a58e765706d0f1823f6d860ba340cdc309faa356b6e9c3
```

Its uncompressed tar is exactly **257,495,040 bytes**, SHA256:

```text
983598e8a29f77151906bc398df7ca7c488a1db007e47eae45635cde5740cba8
```

The tar contains nine original evidence files and its internal `manifest.json`: the diagnostic Lean source and compile log/receipt; independent replay log; complete owned-audit log; complete block-inspection log; complete owned diagnostic receipt; and the exact instantiated audit and inspection sources. The nine original files contain **257,481,632 bytes** in total. No `.olean` object is included; the original receipt binds its on-P3 object SHA and unchanged inputs.

## Completed recovery checks

`verification.json` records the final complete reparse. The unmodified parser from original audit runner SHA256 `571b6137da5e1a1cf9ec9020e03b4f881bc4f0f3f36eae0aa9d62a3a5c0939d5` verified exact serialized/environment/declaration inventory equality for all **2,285 owned declarations**, all safety flags, all permitted transitive axioms, and all complete printed types. Those types contain **167,176,820 UTF-8 bytes**.

All **2,048 private safe block theorems** have 64 facts in a depth-six balanced conjunction. Their **131,072 indices cover 32,769 through 163,840 exactly once**, with grid 16,384 and completed index equal to query index in every fact. All 524,288 decimal integer fields were checked, and every block record matched the complete original receipt. Reversing exactly the two target-module substitutions in `Audit.lean` recovered original template SHA256 `2975fe381dfc6de3b297a67bcc9db9dd064bcad37a0b45ee13bc1fcd957ee85b`.

Paths inside `verification.json` describe the recovery environment. Reconstruction uses the relative paths in `archive-parts-manifest.json`. Archive partitioning and Git blob upload are transport operations; the original diagnostic audit scope and credit boundaries remain unchanged.
