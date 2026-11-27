# P2.5 exact runtime byte recovery — 2026-11-27

This directory records recovery of missing runtime files needed to continue the
existing P2.5 proof sources. It does not add a theorem or change any original
verification gate.

`restore_exact_runtime.py` restores only files named in the independently hashed
original external snapshot. Each copied file must match the snapshot's byte
length and SHA256. Existing different files and symlink paths are rejected;
atomic no-overwrite publication prevents replacing a concurrently created file.
The script does not compile, qualify providers, generate historical receipts,
or award proof credit.

## Observed recovery

The P2 run completed on 2026-11-27 at 10:33:05 UTC (18:33:05 Asia/Shanghai).
It restored 4,962 files from the original CI packets and exact surviving donors.
There were no source-validation errors. The remaining 517 missing files are:

* 515 original native-provider receipts;
* the original byte-staging receipt;
* the original `Architect.Command/actual.setup.json`.

The prior inventory's 64,904 exact files were not rehashed by this recovery
attempt. These results therefore do not establish that the complete original
external qualification has been restored. In particular, the old R19 acceptance
gate, the historical 362/377 normal result, and the 54/69 owned result remain
unchanged. P2.5 is not proved by this operation.

`RESTORE_SUMMARY.json` contains the actual run summary, original input identities,
role counts, and the byte length and SHA256 of the full 3,177,002-byte remote
report. It is explicitly a summary, not a replacement for that full report.

## Frozen implementation and review

The executed recovery script has 19,729 bytes and SHA256
`257f70b2b3f6165fdcbb40852a93e9c4534221339f895bffb8b8c9e56237dab2`.
Its author and an independent reviewer each ran the ten filesystem fixtures in
`test_restore_exact_runtime.py`; all passed. The independent review found no
blocking defect within the specified recovery inputs and scope. The script's
own report keeps compile, kernel, cache-acceptance, qualification, complete
runtime-restoration, and P2.5 proof-credit flags false.

Further normal Lean compilation, stock `leanchecker` replay and full owned
declaration checks must produce their own evidence. New checks must not be
presented as reconstructed historical provider receipts or as R19 acceptance.
