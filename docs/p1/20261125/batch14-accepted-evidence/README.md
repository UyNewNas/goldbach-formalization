# Batch14: two accepted owners, fourteen failed normals

Two additional owners completed actual normal compilation, independent kernel
replay, and the unchanged full environment-owned type/axiom audit at source
commit `4f7a975211bdbdccc76adc14734aa2de4a13b6ad`.

| Accepted owner | Owned declarations | Public declarations | Normal seconds | Kernel seconds |
| --- | ---: | ---: | ---: | ---: |
| `P4AOriginalFull87HistoryCore` | 33 | 33 | 22.084 | 13.221 |
| `Part3ActualWResidualCompletion` | 35 | 32 | 18.827 | 15.912 |
| Total | 68 | 65 | — | — |

The actual normal/audit task was `job_da0dbf3a47354142839556e1a64a8997`.
Its caller was the published Batch14 driver from
`73b740f11ff5aa04b980485f6700deeb99291291`, using the unchanged generic API
from `4cea0407c1258eaddd7d4952cffa4aea67310422`. The audit selected these two
owners on lane 0; lane 1 was empty. Its full-owned command exited 0 in
12.331 seconds.

## Independently checked evidence

The read-only export task `job_9af7b5f0b90146a5a9921dbd6be55eff` preserved the
original normal logs, command receipts, exact source/dependency/configuration
bindings, kernel logs, full-owned records and failed-owner evidence.

- [verification.tar.xz](verification.tar.xz) is 232,424 bytes, SHA256
  `94b30f0d579bdf21d7259092ced514912e06348d6228b184f9b2bb37a0ca3930`.
- [EXPORT_SUMMARY.json](EXPORT_SUMMARY.json) records the exported group results,
  compressed/uncompressed archive hashes and index hash. The archive contains
  its original `ARCHIVE_FILES.json` and 292 indexed payloads.
- [LOCAL_VERIFICATION.json](LOCAL_VERIFICATION.json) records the independent
  checks, exact owner and command hashes, source plus five-output fingerprints,
  standard-axiom restrictions, configuration and scope boundaries.

The saved ten export pages were checked for contiguous offsets and a complete
last page. Their decoded archive matches the published archive exactly. Every
indexed payload's size and SHA256 was verified both inside the archive and in
the extracted copy. The archive and export summary were left unchanged.

Each accepted normal command built exactly its requested owner, exited 0 and
had no project error. Its durable receipt matches the exact command JSON and
complete normal log. The pre-normal dependency context matches the durable
normal record, including all dependency object/trace fingerprints, runtime and
configuration bindings. All 254 project sources in the two-owner union match
their exact Git bytes at the stated source commit; the per-owner import
closures match the frozen audit plan.

Both independent `leanchecker --verbose` commands exited 0, with complete logs
hash-matching their command receipts. Source plus five-output fingerprints
agree between the normal records, the before-kernel snapshots and the final
audit result. The original successful normal logs were reused for the audit;
no successful normal compilation was replayed. Stock `--no-build` checks
before and after the audit exited 0 and emitted no new Built event.

The audit log's environment-owned name inventory matches all 68 unique
`AUDIT_RECORD` names exactly, and the records match `OWNED_EXPORTS.json`.
This includes the three private/generated declarations of Residual; HistoryCore
has 33 public declarations. The audit checks ownership from the environment,
rejects unsafe/axiom declarations, and records full types and type expressions.
Only `propext`, `Classical.choice` and `Quot.sound` occur as transitive axioms.
There are no `sorryAx` references or elided type output. The frozen e9 runner
and original audit template bindings remain unchanged.

## Configuration and Git preservation

The source snapshot's 394-byte `lakefile.toml` has SHA256
`b47ab03272d3a7ba7b57b44c279f1e1fe4c5b4702bc9290d1030011e2116d254`.
The normal commands used the separately pinned, existing 1,823-byte runtime
file with SHA256
`e696bda5c7f8478793603a3593b691a29df4e962cb9b7d3d2a358a3cbb546b48`.
Both bindings match the published runtime-configuration review. The toolchain,
manifest, guard, serializer, state files and audit template also match their
recorded pins. No runtime or memory-limit change is introduced by this evidence
review.

The complete symbolic task output has identical bootstrap Git-before and
Git-after states: HEAD `10b89181754c78c0e77616677295ee2105de0bb6` and porcelain
SHA256 `477507c474369d6cca90fc3c3d1f36e859a70226c5c89e71e2147bf82e8e7789`.
These match the archived worker's full before/after status bytes and bootstrap
binding. All four exported groups also preserve their worker Git states. The
four original protected root hashes remain the recorded published hashes.

## Failed work and cumulative scope

The same archive records failed normal compilation for all five Wire owners,
all five ordinary-frontier owners and all four other Full87 interiors. Those
14 owners have no `NORMAL_PASS` or audit acceptance receipt in this export and
receive no acceptance credit. The four interiors' seven errors are parser
errors at documentation-comment/scoped-option boundaries; later source-only
repair candidates are separate from these failed runs.

Reading the earlier successful receipt owner maps and owned inventories gives
78 distinct accepted continuation owners, with 1,224 owned and 986 public
declarations. These two owners are disjoint from that prior set. The cumulative
selected continuation therefore contains **80 accepted owners, 1,292 owned
declarations and 1,051 public declarations**.

This is a count of the selected Batch10/11/13/14 continuation owners. It is not
a claim about every project module, terminal P1 root or board obligation.
**Whole P1 remains incomplete.**

This local verification invoked no Lean, Lake or cloud task. It checked the
downloaded immutable evidence and exact Git source bytes. Compiled object bytes
are not included in this archive; the recorded five-output fingerprints agree
across the accepted run, and this offline review does not claim a fresh hash
check of the current cloud filesystem.
