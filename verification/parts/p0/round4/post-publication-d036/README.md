# P0 Round 4 post-publication seal for `d0366ce`

This directory fixes the successful post-publication evidence for
`d0366ce64272e81faf6166a8a90050f56b328d38`. It changes no Lean source and does
not reinterpret any producer receipt.

## Bound GitHub Actions executions

| Workflow | Run | Job | Result | Immutable artifact |
|---|---:|---:|---|---|
| Lean core verification | [38289734671](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734671) | `114946653833` | success | `lean-verification-38289734671-1`, SHA256 `4d7499fd526651d70f73fb7cbbf98769ffc51d8a406e1bc80f96ad5dc0d20df8` |
| Variable envelope verification | [38289734726](https://github.com/UyNewNas/goldbach-formalization/actions/runs/38289734726) | `114946657574` | success | `variable-envelope-38289734726-1`, SHA256 `70cb8852b79d8409d1982016ba60823982a30d7320c80195620ecf058f5d31a7` |

The six API snapshots retain the exact run, job-step and artifact metadata. The
two ZIP files are the original downloaded artifacts. Their local SHA256 values
equal the digests published by GitHub.

## Core results

The core artifact binds the project commit and pinned Lean toolchain before the
checks run. Its complete outcomes are:

| Gate | Result | Evidence |
|---|---|---|
| Full project build | success | 9,802 jobs, exit 0, 2,640 seconds |
| Four explicit Round 4 targets | success | 3,407 jobs, exit 0, 4 seconds |
| Stock root `leanchecker` | success | replay includes the root `ImbalancedChen`, exit 0, 457 seconds |
| Root axiom audit | success | 5,872 declarations; only `propext`, `Classical.choice`, `Quot.sound`; exit 0 |
| Round 3 compiler type export | PASS | 198 declarations and one conditional bridge, commit unchanged during export |
| Round 4 compiler type export | PASS | 414 declarations and one conditional bridge, commit unchanged during export |

The Round 4 receipt gives the exact defining-module partition
`14 + 72 + 207 + 121 = 414`. The variable-envelope artifact independently
records 358 declarations, stock replays, a complete axiom inventory and zero
exit codes for every recorded stage.

## Recheck

Run from any directory:

```bash
python3 verification/parts/p0/round4/post-publication-d036/verify_post_publication.py
```

The verifier checks the fixed evidence hashes, safe ZIP membership, run/job and
artifact bindings, core stage exit codes and success markers, compiler-type
receipts, exact module counts, source commit stability, and the axiom
allowlists. A successful run prints a JSON object with `"status": "PASS"`.

## Deliberate boundary

This seals the P0 Round 4 integration commit; it does **not** close the
manuscript's analytic obligations. Both compiler-type receipts explicitly say
`hLower_hUpper_discharged=false`. The current main bridge remains conditional,
and the full historical construction, remaining numerical certificate ranges,
actual arithmetic distribution estimates, same-rho `K`, `hLower` and `hUpper`
remain tracked separately.
