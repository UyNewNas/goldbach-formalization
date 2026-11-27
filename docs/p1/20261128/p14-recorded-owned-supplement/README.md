# RecordedOldFifthBlockTotals: reuse the original normal compilation

This directory prepares **only the missing named kernel replay and complete-owned
audit** for `ImbalancedChen.P5RecordedOldFifthBlockTotals`. It does not establish
new acceptance until the unchanged existing gates actually succeed. P1.4 remains
incomplete.

## What the recovered originals establish

The complete original normal log is 9,272,545 bytes, SHA-256
`63da4b14f4b1f9dda09882e90464cf8cffd322667471932e2a4e4b2898ae8bb9`.
Its single Recorded success header is at line 135515:

```text
✔ [11144/11174] Built ImbalancedChen.P5RecordedOldFifthBlockTotals (20s)
```

The source context is the original 550,997-byte file with SHA-256
`db2dfc6e2ae8357ded33da4d3f5f938284db78ebaf5d6caa17d097d4ff5f3538`.
It binds the current 23,109-byte target source, SHA-256
`7a2548770d2e8f863ae30f9016b61845591b3f4882b60ec1b82bd43fdf1216fa`.
That source directly imports only Mathlib; its project source closure is this
single owner. The original CRLF bytes are preserved.

The **whole original aggregate exited 1**. Its original command and log remain
unchanged. The established `e9dadb4…` reuse API explicitly permits a selected
successful Built header in such an aggregate, while requiring the complete
SHA-bound raw log, complete Built set and source bindings.

There is a documented historical summary discrepancy. The old command's list
contains 42 Built modules; the complete raw log has 43 under the unchanged e9
parser, which accepts `✔`, `⚠` and `ℹ`. The additional success is exactly:

```text
ℹ [9985/10095] Built ImbalancedChen.P1CorrectedFifthCausalTupleDictionary (14s)
```

That line is at 65039. The new plan binds the actual complete 43-item raw-log set.
It preserves the old 42-item command record and records the discrepancy. It does
not grant the additional module any acceptance through this single-owner plan.

The source context does not record an execution Git commit. Accordingly,
`normal_logs.original-incremental-six-root.source_commit` is `null`, which the
unchanged e9 API copies as provenance metadata. The original context, command,
raw log and exact source hashes carry the original binding. The caller's explicit
publication commit is separate and is never substituted for an unknown old
execution commit.

## Lossless recovery and present object identity

The root submitted only the bounded reader; the assigned reader consumed all
11 output pages of task `job_12866a516d9149509e7f86889753a6db` to EOF. The
355,887-byte stdout has SHA-256
`284395149123bae0a1546da159f01c7f14f26ba90ae60adcfd250f16f85d7e39`.
The complete original log was reconstructed and independently rehashed. The
archive retains the original log, original source context, original command,
task metadata, all lossless pages, full stdout, read parameters and review.

All current source-plus-five files were present and unchanged during that read.
Their exact current sizes and hashes are frozen in `MANIFEST.json` and must still
match before and after the missing checks. The old inventory contains no
historical output hashes, so this current observation is **not described as the
snapshot at the original normal compilation**. E9's original no-build readiness
gate supplies the required current source/object readiness check.

## Unchanged execution path

The caller loads the original batch5 helper, batch10 primitives and e9 API from
fixed Git objects. It verifies the existing runtime review, both runtime states,
guard, serializer, configuration, historical full-owned template and protected
roots. It freezes one new plan and acquires original lane 0.

Inside that serializer, it calls the unchanged e9 runner with `--prepare-only`,
then explicitly `--lane 0`. The existing API itself performs:

1. Complete original normal-log/Built-set verification and project source binding.
2. Source-plus-five baseline and original stock `lake --no-build build` gate.
3. Named `leanchecker --verbose` for this owner.
4. The existing full-owned audit template, including private/generated names,
   complete types, type ASTs, universes and standard transitive axioms.
5. Its second stock no-build gate and unchanged source/output/evidence checks.

The empty lane 1 is never launched. No normal build, source installer, modern
`NORMAL_PASS` synthesis, lock edit or validator replacement is present. Any
existing execution or partial audit causes a hold for receipt inspection; there
is no automatic retry.

After publishing these files, root should extract the caller from that exact
commit and run `--source-commit FULL_PUBLISHED_COMMIT --check` first. The check is
strictly read-only and is not compilation credit. Only root schedules the same
caller with `--run`. Outputs live below
`/workspace/p1-complete-proof/20261128-p14-recorded-owned-supplement/`.

## Mathematical scope

This existing module proves arithmetic of 72 recorded block summaries. It does
not itself prove that their floors enclose ordinary integrals or identify actual
owners. The supplement retains that scope and makes no new theorem or manuscript
claim. It always leaves `whole_P1_4_complete` false.
