# Existing P1 runtime configuration

`ACTUAL_CONFIGURATION.json` is the read-only observation from task
`job_b10eb546054d45fcabe3c452f6be7935`; SHA256
`df80ab63b089db26cc041d46406a12f71a346a1986e2562edcec5ac147267614`.
It records the live configuration contents, source220 counterparts and the
configuration/runtime bindings of the new PrefixBinding, Harmonic and
Ascending normal receipts. It does not run a compiler or change a file.

`review.json` independently checks this observation against the existing
Batch10 and Batch11 accepted archives. Its SHA256 is
`34960ea820d65e0220fc30e55ded702dfc710f5301771201f43958eba46ca880`.

## Exact boundary

| File | Git source220 | Existing runtime |
|---|---|---|
| `lean-toolchain` | 29 bytes; `62c2d9c0fc1ec4c67e151c11eff41ca004ef38e179cf9476c230406e6defedef` | Identical |
| `lake-manifest.json` | 3872 bytes; `35a9ca6f6feae3af4b1a74b6ad185e6b723702d47cc1ed41f7952bf67f28a849` | Identical |
| `lakefile.toml` | 394 bytes; `b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254` | 1823 bytes; `e696bda5c7f8478793603a3593b691a29df4e962cb9b7d3d2a358a3cbb546b48` |
| `lakefile.lean` | Absent | Absent |

The existing runtime lakefile includes the previously used
`-DmaxRecDepth=100000` and `-DmaxHeartbeats=4000000` arguments and additional
library declarations. Those exact bytes already occur in historical normal
receipt bindings. This hold repair does not add or increase these options.
The existing guard, serializer, both runtime state files and audit template
fingerprints are also identical across the 75 old and three new normals.

## Historical evidence checked

The Batch10 archive
`../batch10-accepted-evidence/verification.tar.xz`, SHA256
`49432bc69a385bfea32fc0a69990726ca4ebc5702da79019d296312c0382ec97`,
contains 71 normal receipts and 18 full-owned receipts covering those same
71 owners. The Batch11 archive
`../batch11-accepted-evidence/verification.tar.xz`, SHA256
`3fd7bf7c9d3ecca44bc63e37fa1054f8d8757690b8b507feed006aa681c1e3f0`,
contains four normal receipts and one full-owned receipt covering those
same four owners.

All 75 `dependency_context.configuration` maps equal the observed runtime.
All 75 `dependency_context.existing_runtime` maps equal those in the three
new normal receipts. For every old owner, the normal command succeeded;
its exact normal log path/hash and source plus five output fingerprints
match the corresponding full-owned receipt. The audit runtime-state hash
also matches. `review.json` provides archive fingerprints, representative
normal/audit member paths and hashes, and fingerprints of the complete
module-to-receipt indexes.

This establishes the runtime configuration's historical provenance. It
does not accept a new Wire owner. A normal receipt and a full-owned
acceptance remain distinct evidence, linked explicitly in this review.

## Caller gate

The Wire catalog retains its original `source_configuration_bindings`
and adds `runtime_configuration_bindings` with pinned evidence references.
The caller verifies source220 Git bytes in both modes. Cloud `--check` and
all `--run` operations additionally require the exact runtime configuration
and the historically bound guard, serializer, both state files and audit template.
An explicitly selected local source-only check requires source config
bytes and reports `SOURCE_CONFIG_ONLY_NOT_CLOUD_READY`.

No actual lakefile, resource guard/cap, Lean proof or existing verification
primitive was modified. This review made no cloud call and invoked no
compiler. Root owns publication, cloud checks and any subsequent normal or
full-owned verification.
