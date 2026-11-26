# P1 prior-report writer compatibility

Two exports rejected the first prior report because the original
dependency compile used an older runner writer. The independently read P1
diagnostic from `job_9d9697cdbc4c40bc93c2f9e20512a05e` showed 18 distinct
prior reports, including 16 with a different writer. The diagnostic's
SHA-256 is `5a87ea1b0b5eaa3801fb0bf51f84361ace01fa075354505381e2cbc1c51c8f86`.
All 16 exceptions are fixed by original absolute report path, full
report SHA-256, and writer SHA-256.

The checksum of each Git writer source matches the diagnostic. The
`input_data` key construction and the parsed definitions for
`digest_json`, `compile_command`, `object_hashes`, and `can_reuse` agree
across the three historical commits and the current pinned runner. The
exporter still verifies the exact original successful stage, compile
record, input key, objects, and log for every reused dependency. The
receipt records the original writer and report status with the
successful-dependency-stage scope.

Five directed tests passed in 15.419 seconds. They cover the exact
diagnostic pins, a pinned older writer, unpinned and incorrect writer
identities, modified report bytes, a failed compile inside a correctly
pinned report, and historical graph and archive verification under the
current writer. The prior failed export was reproduced with the original
writer-equality check. No Lean checks were repeated.

Exporter SHA-256 is
`003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5`.
The patch is `exporter-lineage-compat.diff`, SHA-256
`499b4a9839293d9a9710d6d13e2c14b0ab7d4a201c53b97ca732ac32dd256154`.
