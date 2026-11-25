# Batch11: all four proof repairs accepted

The four repaired owners at source commit
`220c14630ffd266f824bdbf0977147ecb740c0dd` passed normal compilation, independent
kernel replay and the unchanged full environment-owned type/axiom audit.
They contribute **165 owned declarations, including 159 public declarations**.

| Owner (prefix `ImbalancedChen.`) | Owned | Public |
| --- | ---: | ---: |
| `P2OriginalSaving19SimplexMoments` | 79 | 79 |
| `P4AUpperTaggedContinuationAccounting` | 9 | 9 |
| `P4BPrimeEulerOperatorWords` | 35 | 32 |
| `P5OriginalCommonRefinedPreservation` | 42 | 39 |

The existing theorem statements, assumptions and definitions were preserved.
The repairs address finite-list reduction and sum order, the negative signed
continuation branch, dependent induction and the finite smoothness-order bound,
and explicit Boolean/proposition conversions. The corresponding manuscript
passages and existing donor proofs were checked before editing; see
[the source repair records](../batch11-repairs/SOURCE_REPAIRS.json).

## Evidence

- [SUMMARY.json](SUMMARY.json) names the actual complete receipt and its hash.
- [verification.tar.xz](verification.tar.xz) contains 106 original evidence
  payloads: source preimage backups, exact source/normal dependency bindings,
  normal commands and full logs, kernel logs, complete owned declarations,
  frozen audit plan, runtime bindings and preserved dirty-Git state.
- [ARCHIVE_FILES.json](ARCHIVE_FILES.json) and
  [LOCAL_VERIFICATION.json](LOCAL_VERIFICATION.json) record the complete
  successful lossless-export/hash verification.
- [MCP_EXPORT_TASK.json](MCP_EXPORT_TASK.json) records the actual export.

Archive SHA256:
`3fd7bf7c9d3ecca44bc63e37fa1054f8d8757690b8b507feed006aa681c1e3f0`.
Complete audit receipt SHA256:
`842792d345c40ab67670a678fc162aed62c68b9e637a9f4d8dd4c0d8573ee741`.

The actual execution task `job_87b43a40cc004cc7a56fb03647c6b437` exited zero.
Its reviewed caller is published at
`9246927b8faebca3c06e4a5a47e733b5f13536db` and reuses the existing guards,
serializer, command recorder and e9 audit. The four owner closures contain 342
project modules; none of these repaired owners is an ancestor of the other 71
Batch10 owners. Those 71 accepted results were preserved.

Together, Batch10 and Batch11 accept **75 distinct selected owners, 1,177 owned
declarations and 962 public declarations**. These are this continuation's scoped
counts, not whole-project totals. The original four terminal roots remain
unchanged and unaccepted; `whole_P1_complete` remains false.
