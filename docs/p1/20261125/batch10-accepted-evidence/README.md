# Batch10: 71 accepted owners, including all 53 Higher units

The actual P1 private-compiler run built 71 of the 75 selected source owners at
`99c1f8ba1dc453b21f47e30b667db0de93d73387`. All 71 successful owners subsequently
passed independent `leanchecker` replay and the unchanged full environment-owned
type/axiom audit: **1,012 owned declarations, including 803 public declarations**.
All **53** Higher partition owners are included. Their original proof formulas,
normalizations, guard, serializer and checker were retained.

The four normal failures are preserved with their actual target diagnostics.
Their repaired sources and later acceptance belong to the separate
[Batch11 record](../batch11-accepted-evidence/README.md); this archive does not
retroactively relabel those failed source versions as passing.

## Evidence

- [SUMMARY.json](SUMMARY.json): exact accepted-owner list and 18 complete audit
  receipt paths, hashes and declaration counts.
- [verification.tar.xz](verification.tar.xz): 1,269 original evidence payloads,
  including full normal/kernel/audit logs, frozen plans, source/output bindings,
  execution commands, failure inspection, source/object census, G3 input census,
  and the two preserved existing-source variants.
- [ARCHIVE_FILES.json](ARCHIVE_FILES.json): every payload size and SHA256.
- [LOCAL_VERIFICATION.json](LOCAL_VERIFICATION.json): lossless retrieval and
  successful verification of the compressed archive, uncompressed tar, index,
  every payload and each complete audit receipt.
- [MCP_EXPORT_TASK.json](MCP_EXPORT_TASK.json): actual export command and result.

Archive SHA256:
`49432bc69a385bfea32fc0a69990726ca4ebc5702da79019d296312c0382ec97`.

The normal task was `job_56514f69b84e456cb6406d29f44150a6` (exit 1 because four
targets failed). The successful audit tasks were
`job_d7649e8fcb1145f6aae86385ac91e6cf`,
`job_c7581f18c2414f4d85a8fdc6aa5acdc1` and
`job_fd6275a5f29845d4b0bd1f34074f1c66`.
The completed normal work and completed audit lanes were reused, not replayed.

This is acceptance of the listed 71 owners. It does not accept the original P1
terminal roots, all numerical/archive obligations or the whole manuscript P1
proposition. Every original receipt keeps `whole_P1_complete: false`.
