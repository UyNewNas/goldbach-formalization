# Narrow RootQ dependency-lineage review

Reviewer: `/root/p36_group_export_review`. Revised adapter SHA-256:
`23c99792fe2cac7ea7a0ebdbe76a60e4af494c7118a7c3fc73af794063741e78`.
No blocking finding. The original exporter remains byte-for-byte at
`003d628292e0b1d067e9f87d3aad6b2c6f2a64db5b117e06cbe6bbf37743fcf5`.

The reviewer compared all 31 original validation function code objects and all
16 old legacy pins: they are unchanged. The adapter adds only the exact report
`/workspace/p36-original-u5-20261125/.lake/p36-build/runs/20261125T151944.477149Z/report.json`,
writer SHA-256 `895a8bc67d6c28e4db0ce6954344e20679cb581e3b861bafed469852d5ee5d30`,
complete report SHA-256 `e79ea8a026224372ac58109bf0ccd4c3ded6d4ef447facf25f1c07ab7ca223ac`,
13,762,383 bytes. The independent P1 readout is retained in
`ROOT_Q_LEGACY_READOUT.jsonl`.

The old report's overall status remains FAILED. Its only newly allowed reuse
is the successful, non-strict dependency compilation of
`ImbalancedChen.P2OriginalU5RootQ`. The outer receipt limits this report to that
one module and exact compile-log archive member, and records its actual use,
size, hash and FAILED status. This gives no standalone owned acceptance to
RootQ and no retrospective success to the old group.

The reviewer independently read the old runner from Git revision
`e4ad395e4901628d85a27d17d0f87a16ea943433`, confirmed its writer hash, and compared
the syntax trees for `digest_json`, `compile_command`, `object_hashes`,
`can_reuse`, compilation input fields, input-key calculation and successful
record construction with the current driver. All matched. Current RootQ
source, independently recomputed input key, stage/record commands, exit status,
log path and log hash also agreed. Source, recursive dependency, compiler,
object/sidecar, exact command and full-log checks are preserved.

Eight focused tests passed independently in 4.917 seconds. Changed report
bytes/writer, a pinned old path disguised as the current writer, an unknown old
path, and reuse for another dependency were rejected. Owner/manifest/runtime
and missing-replay checks remained in place.

The readout and review do not substitute for full report-byte recovery. The
actual accepted group export and local verification must still include and
hash all 13,762,383 bytes of the original report and its original compile log.
The historical regression fixture limitations in INITIAL_ADAPTER_REVIEW.md
remain unchanged.
