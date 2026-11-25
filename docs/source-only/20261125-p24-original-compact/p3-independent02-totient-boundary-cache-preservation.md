# P3 independent02: cache-first check and two minimal lint repairs

Date: 2026-11-25. Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

## Actual diagnostic and decision

Root's P3 independent02 run uses source `dc6cb9c6`. The provided in-progress
log reports six unused simp arguments in `TotientReciprocalBudget.lean`
(original lines 43, 110, 142, 177), and one unused `ring` continuation in
`BoundaryGridBudget.lean` (original line 123).

Root required an exact-source lookup in the known 619-entry P2 registry
before changing either source. Both initial source SHA-256 values matched
successful old records, so both files were first preserved. Root then
commissioned the complete recursive source-closure check described below.
That check rejected reuse because an ancestor's source had changed, after
which root authorized the exact reported lint cleanup. There is no theorem,
assumption, constant, numerical definition, branch, list order, import or
linter-option change.

The preserved Totient module supplies the finite reciprocal-totient bound
with constant four and its finite discrepancy corollary. The preserved
Boundary module counts the four inclusive collars with full pair
multiplicity and a per-slice endpoint term. No new manuscript or numerical
claim is introduced by retaining these existing sources.

## One shared exact registry extraction

Known archive:
`docs/verification/20261125-p2-resume/evidence-numerical80-111-rank-20261125.slim.tar.xz`.

Unique member: `packages/all.tar.gz/context/records.json`.
The member's original bytes were copied, without JSON reserialization, to:

`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p2-records-619.json`.

- Size: **16,227,671 bytes**.
- Top-level records: **619**.
- SHA-256: `ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`.
- This is the same hash as the archive's export-manifest registry binding.

Other agents may read this shared file directly; no repeated archive scan
or extraction is needed.

## Exact two-row lookup

| Module | Pre-repair and recorded source SHA-256 | Recorded object SHA-256 |
|---|---|---|
| `ImbalancedChen.TotientReciprocalBudget` | `aa80ff2ad79f77405951f1e56e993a851a1b32ad46c970e7914adb94bdb2db86` | `60ecc49a248bb26806cc0132ff9d6949d64ce68d3660acefafb7ae4c3b826375` |
| `ImbalancedChen.BoundaryGridBudget` | `a36da7f8fc558d406e5e00b9790389438846198caa610540da8145471a419245` | `5934a2497f73075b93667d22e04e1d3dd1be255a73f535de7490bcf104d2d808` |

Both records have `cache_schema: 2`, `exit_code: 0`, and
`new_strict_compile: false`. Their original classification is
`COMPILED_CHECKPOINT_ONLY_NOT_KERNEL_ACCEPTANCE`. Both point to the original
project adoption receipt SHA
`c481b63afedeb846f3a07371518c692b3ce71eeb2050fe48b9fc2b527a763269`.

Their respective closure signatures are:

- Totient: `546c83daa64e6448e12c901a9eec7c5f6e4293bcb4a6dd84d87624b19d26e6b0`.
- Boundary: `c8127d69a684ebacc6fa17cadbb5c2c9985aef94c261324d8d36446bd6035986`.

Both records name `ImbalancedChen.CurvedRegionDiscrepancy` as their direct
project dependency, bound to object SHA
`ffc348c98dfb7ee96d3b3af93e3852be1eaac2b9d86a62af997bbc7f3c44b61b`
and dependency signature
`6119f180e392ee79a8bc52f0e60cfbf11182256a1a2206871ef2e495bffeae77`.

## Recursive source-closure result and repair decision

Root's project-cache agent checked the complete ten-module project closure
of each candidate. Its report is
`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p3-independent02-six-record-source-closures.json`,
SHA-256 `ab5861ff62c9777cdff1d5491f9e6599b3c1dfe503ea86c6675a780e78fdb0c6`.
The report's exact bytes were hash-checked here; its graph work was not
repeated.

Both candidates are blocked by the same chain:

`TotientReciprocalBudget / BoundaryGridBudget -> CurvedRegionDiscrepancy -> FiniteSieveModel`.

The archived `FiniteSieveModel` source SHA is
`9112139c826b1ebf81b12d69b873c179a2cbd6e17305ec3d0818032fb34bfb0c`,
whereas the current source SHA is
`3bda22d12455339b6678ebd14830379e79f488ebfee9605db2927af26529a594`.
Thus the approved exact-source migration cannot reuse these old complete
closures. A matching root-module source alone was not treated as acceptance,
and no old dependency signature was changed or reconstructed.

Root then authorized these minimal changes, all from the actual diagnostic:

| Original location | Exact cleanup |
|---|---|
| `TotientReciprocalBudget.lean:43,142` | Remove unused `Nat.cast_add` and `Nat.cast_one`; retain `Nat.cast_succ`. |
| Same file, 110 | Remove unused `inv_pow`; retain `one_div`. |
| Same file, 177 | Remove unused `inv_pow`; retain `one_div` and `mul_inv_rev`. |
| `BoundaryGridBudget.lean:123` | Remove only the reported unused `<;> ring` continuation after `field_simp`. |

These are six unused simp arguments and one unused tactic, on five source
lines. They change no mathematical step or estimate and do not identify a
new manuscript gap. Unreported tactics are retained.

| File | After-repair SHA-256 |
|---|---|
| `ImbalancedChen/TotientReciprocalBudget.lean` | `2ffa687a7e2e0904ae0eeb2954ed30be3b45b392513f859decb396e4d1cca8c4` |
| `ImbalancedChen/BoundaryGridBudget.lean` | `fbe43e345ffa187e495be2164149a2f010810a1c0f9d570f749d911bf71cb86f` |

## Static verification and remaining gate

All 24 theorem headers and all five computational declarations are
byte-identical to the pre-repair files. The diff has five insertions and
five deletions; `git diff --check` passes. No hypothesis, numerical algorithm,
branch or list order was altered, and no linter was disabled.

No Lean/Lake process, cloud task, full CI audit, compilation, kernel replay
or numerical evaluation was run here. The updated proofs are not yet
claimed to compile. Root owns the actual rerun and all subsequent physical
cache, kernel and completion checks.
