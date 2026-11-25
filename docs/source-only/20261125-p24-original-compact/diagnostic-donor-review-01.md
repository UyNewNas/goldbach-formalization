# Diagnostic donor reuse review 01

Date: 2026-11-25.

Verdict: the two Important findings are repaired and the reviewed scripts are ready for the scoped diagnostic donor preparation. This grants no proof acceptance, compile credit, kernel credit or native input qualification. The actual structure-01 donor preparation and structure-02 compiler retry were not run by this review.

## Reviewed and repaired scope

The helper transports the unchanged earlier diagnostic passes into a fresh private donor. It does not compile Lean, rewrite accepted records, or promote diagnostic outputs to accepted cache entries. The intended previous run is structure-01; only earlier rows with both exit codes zero and unchanged source/input bindings are eligible for reuse.

The initially reviewed helper SHA-256 was `2cb55a34c4d8241372daa123b14001805a2173dba1558a0e1b9539c896be4044`; its consumer was `e927dc5fbb1312f9eb29797ef5e9ba5b0e5e76fe467892d800d83f5680c7b6c2`.

Two Important findings were independently identified and reproduced with temporary-file fixtures:

1. An unchanged old external tree A did not bind the newly selected donor package tree B. The helper could reuse a previous pass even when B supplied different external object bytes.
2. Failure while copying the second output facet left a partial donor. Despite the missing completion receipt, the consumer's `--plan-only` selected its already copied source and `.olean` as a candidate.

## Repairs

- Before any payload copy or package symlink creation, the helper writes `DIAGNOSTIC_DONOR_INCOMPLETE`. It removes this marker only after writing the completed receipt. Copy exceptions abort preparation with the marker intact. The consumer rejects this marker before traversing sources, selecting candidates, or returning a plan.
- Shared checks require the ordered, resolved external library roots to equal those from the old `RUNTIME.json`; the project-library prefix must identify the old diagnostic output. The selected toolchain and compiler path/hash must match. Every old external input byte binding, actual module-object resolution and complete loadable facet set is rechecked. Different package trees are not migrated. An external mismatch now aborts preparation instead of publishing a reusable donor.
- The completed receipt binds the original runtime, before/after external snapshots, records and summary, plus the final private project sources and loadable facets. The consumer checks these bindings and the old stable-input condition before candidate selection. A completed donor with changed evidence, toolchain, private source/object bytes or facet inventory is rejected.
- The existing source-commit/current-source comparison, prior successful-exit checks, old project input hashes and project dependency facet-set comparisons remain. An individual source/project/output mismatch still records a skipped prior pass; ordinary donor objects retain only their pre-existing unqualified diagnostic role. Prior output copies also recheck their expected recorded hash immediately before copying.
- `proof_acceptance`, `compile_credit` and `kernel_credit` remain false. The existing consumer's runtime, fixed Mathlib pin, source ancestry, input stability and direct compiler checks are retained.

## Verification

The original eight temporary-file scenarios were retained as regression cases, with two further cases for an added external loadable facet and a different consumer toolchain. They exercise real helper/consumer code, temporary Git commits and real source/object files; only a specific copy IO failure is injected. The compiler binary is inert fixture data and is never executed.

Before the repair, the ten-case suite reported five expected failures: the two original issues, added external facets, changed consumer toolchain, and the newly required strict external-change abort. After the repair:

```text
python -B -m unittest discover -s verification/part2 \
  -p test_p24_prepare_diagnostic_donor.py -v

Ran 10 tests
OK
```

The root reviewer independently read the helper/consumer changes, reran the same ten fixtures successfully, and accepted the two repairs. `git diff --check` also passed. No Lean/Lake compiler, kernel replay, cloud build or CI dispatch was performed by this repair task. The tests establish fail-closed transport and diagnostic consumption behavior; they do not establish eligibility of the actual three structure-01 outputs until the helper runs against their real records and physical inputs.

## Frozen source identities

| File | SHA-256 |
|---|---|
| `verification/part2/p24_prepare_diagnostic_donor.py` | `2bd86d747a46234aa1edbce4165aa2c96a2cc00532b64a287278c284af631a83` |
| `verification/part2/p24_diagnostic_compile.py` | `9fa70f8c3071d0e644385048afc1392906837476c6c31993b133ca83326820fd` |
| `verification/part2/test_p24_prepare_diagnostic_donor.py` | `fdf0f106aa5cda51cf8f19ba41f3bdfecca81be160726f4ac766683be8cafd50` |
