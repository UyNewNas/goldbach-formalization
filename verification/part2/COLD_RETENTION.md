# P2.1 lossless capture retention

`cold_retain_p21_evidence.py` is a local storage wrapper. It adds no compiler,
kernel, cloud-task or mathematical credit. It loads the original
`transfer_p21_evidence.py` from its canonical file path, requires SHA256
`5c0369eb49ce5aed7798d0b69e58e26d0805f7d3d3b680c480d45f9654982a4d`, and uses that
file's unmodified `load_plan`, `accept` and `assemble` functions.

## Retain and restore

`retain` verifies the original hot binary and raw tool capture with `accept`.
It binds the compressed capture to the saved actual Git tool response
`result.structuredContent.sha`, verifies the decompressed capture SHA256,
reconstructs the binary from the saved `output_base64` pages, and runs the
original `accept` again. The complete restored acceptance receipt must equal
the original receipt, including the actual job ID and both byte digests.

The compressed original is retained in
`cold-captures/<asset>-<index>.json.xz`. The immutable
`<asset>.<index>.cold-retention.json` binds its bytes, the raw capture, the
original acceptance receipt and the saved publication responses. Creation is
atomic and never overwrites different existing record bytes. `retain` keeps
both hot originals; `hot_removal_by_retain: false` describes this operation.

`evict` is a separate, explicit operation. It first restores and accepts the
cold original, holds its file and binding records open, and checks their
unchanged identities through removal of any verified redundant hot copies.
It preserves the cold original and records removed hot filenames in a separate
immutable `<asset>.<index>.hot-removal.json`.

`assemble` replaces only the parsed plan's parts container with an equal-valued
list adapter. Values, order, indexing and length stay the same. The adapter
materializes one capture and binary at a time; the original `assemble` then
runs its own `accept` for that part and all its original full-file, existing-file
and hash checks. Temporary cleanup only removes files whose inodes are still
those created by this invocation. Corrupt or replaced cold originals cause an
error; no fallback weakens the original acceptance gates.

## Commands

Use canonical absolute paths for the helper, pinned plan, part directory and
assembly destination. `--xz-source` is optional and may point to the original
compressed upload file to avoid recompressing it. If omitted, the wrapper uses
an already retained cold file or recompresses with the publication's preset 6;
the resulting bytes must match the actual published blob exactly.

```sh
python3 -B cold_retain_p21_evidence.py --helper /absolute/transfer_p21_evidence.py retain /absolute/PLAN.json PLAN_SHA256 archive 0 /absolute/parts
python3 -B cold_retain_p21_evidence.py --helper /absolute/transfer_p21_evidence.py evict /absolute/PLAN.json PLAN_SHA256 archive 0 /absolute/parts
python3 -B cold_retain_p21_evidence.py --helper /absolute/transfer_p21_evidence.py assemble /absolute/PLAN.json PLAN_SHA256 archive /absolute/parts /absolute/archive.tar.xz
```

Assembly requires a valid cold-retention record and all its bound original
publication records for every part. The CLI has no synthetic-evidence mode.

## Local regressions

The tests use explicitly synthetic local fixtures. They perform no cloud,
GitHub or Lean calls and make no production-evidence claim. From a published
checkout, the test loads the original helper beside the wrapper by default:

```sh
python3 -B verification/part2/test_cold_retain_p21_evidence.py
```

For a staging directory whose original helper remains in another checkout,
set its actual path explicitly:

```sh
P21_TEST_ORIGINAL_HELPER=/absolute/verification/part2/transfer_p21_evidence.py python3 -B test_cold_retain_p21_evidence.py
```

The regressions cover lossless round trips, one-pair assembly, unchanged
original capture gates, actual Git SHA mismatches, corrupt cold files, existing
assembled output, interrupted assembly, immutable records, symlink rejection,
changed cold bytes after acceptance, and foreign inode preservation both before
and after temporary ownership registration.
