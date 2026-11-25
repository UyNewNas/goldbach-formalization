# P3 independent03: four minimal strict-linter repairs

Date: 2026-11-25. Status: **SOURCE_REPAIR_PREPARED / FRESH_LEAN_CHECK_PENDING**.

## Actual failing input and bounded scope

The failures are from the completed P3 independent03 diagnostic at source
`0768785a`. Its local log is `p3-independent-symbolic-03.log`, 14,646 bytes,
SHA-256 `9e2196e6ea0b27b8b5b55488ce490001926435b0566106aa88f4525a0dd5e1b7`.
This task owns only `BoundaryCellContainment`, `FixedRoughCoefficients`,
`FirstExitOwnCubeSplice`, and `FirstExitFrontierInvariants`. The root agent
separately handles the other direct failures.

No Lean, Lake, cloud job, generator, or full CI/archive audit was run here.
The only production edits remove the eleven items explicitly reported by
that diagnostic: one ineffective tactic and ten unused simp arguments.

## Check the existing 619-record source closure before editing

The already extracted original registry was read directly from
`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p2-records-619.json`.
Its raw SHA-256 was checked against
`ee57e2a55adbf4564ed184eda0c4b4641c359be4da1113ed4ca8b8c090ee9388`.
No archive was re-extracted.

Using the existing comment/string-aware `imports` parser from
`verification/part2/inspect_winner9_owner_native.py`, each current target's
complete recursive `ImbalancedChen` import closure was walked. For each
node the current physical source SHA-256, old record's `source_sha256`,
old `exit_code`, and current/recorded project-import name sets were compared.
All 21 nodes in the union have old records with exit code zero and matching
project-import name sets. Captured current source hashes were rechecked
after the walk and had not changed. The source mismatches below are
sufficient to reject exact reuse from this registry.

| Target | Closure size, including target | Target source matches old record | Mismatching source nodes before this repair |
|---|---:|---|---|
| `BoundaryCellContainment` | 11 | Yes | `BoundaryGridBudget`, `FiniteSieveModel` |
| `FixedRoughCoefficients` | 15 | No | Target, `RoughPrimeUniverse`, `PhysicalUpperWeightBridge`, `FirstExitTree`, `FiniteSieveModel` |
| `FirstExitOwnCubeSplice` | 3 | No | Target, `FirstExitDepthSplice`, `FirstExitTree` |
| `FirstExitFrontierInvariants` | 5 | No | Target, `FirstExitDepthSplice`, `FirstExitTree`, `RoughPrimeUniverse` |

In particular, the unchanged pre-repair source of `BoundaryCellContainment`
does not make its old record reusable. Its dependency environment changed.
The common earlier foundational differences include `FirstExitTree`
`6ab5eeb1...` to `490490bf...` and `FiniteSieveModel` `9112139c...` to
`3bda22d1...`. Exact hashes, per-node bindings, and paths from each target
are recorded in
`/workspace/scratch/daaa8ebc2a3f/p24-ci-audit/p3-independent03-four-record-source-closures.json`,
SHA-256 `ecc6b27cec3443499d5aebb78660a26684bb8bb028a309e3d80a63009af57dec`.

This was a project-source identity check. It did not load historical
objects, validate runtime/native inputs, or award cache, kernel, or
compilation credit. No old dependency signature was rewritten.

## Exact changes and mathematical boundary

Locations below refer to the pre-repair files in the diagnostic.

| File and location | Exact removal |
|---|---|
| `BoundaryCellContainment:253` | Remove `change r * q <= N`, reported as doing nothing. Keep the preceding real cast normalization and `exact_mod_cast hN`. |
| `FixedRoughCoefficients:30` | Remove `firstExitRetainedLeaves_cons` from the nil case's simp list. |
| Same file, 33 and 36 | Remove `firstExitRetainedLeaves_nil` from both cons-case simp lists. |
| `FirstExitOwnCubeSplice:78` | Remove `firstExitRetainedPolynomial_cons` from the nil case's simp list. |
| Same file, 80 | Remove `firstExitRetainedPolynomial_nil` from the cons case's simp list. |
| `FirstExitFrontierInvariants:41,44,72,75,105` | Remove `firstExitDepthFrontier_cons` only from the five reported nil-case simp lists. |

The frozen 1106 `sieve-appendix.tex` from publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`, SHA-256
`15c9f561b870edb43ec1de3a8adf88b0b4561982f0617b58b26b1de966f9f9d8`,
was consulted for the causal prefix and first-exit identity conventions.
Earlier parent decisions, decreasing prime order, retained coefficients,
and literal continuation histories stay unchanged. The Lean proofs still
distinguish nil and cons cases; only the irrelevant other-constructor simp
lemma is removed from each reported list. The unchanged common theorem
that treats both list constructors retains both relevant simp lemmas.

For the boundary bridge, both product cutoffs stay inclusive and the lower
power cutoff stays strict. The deleted `change` repeated the natural-number
goal already present. The cast transport and exact real-region predicate
remain the same.

These are strict-linter expression repairs, with no new mathematical
estimate, lemma, assumption, branch, or changed statement. No mathematical
gap was identified in the eleven reported failures.

## Source SHA-256 bindings

| File | Before | After |
|---|---|---|
| `ImbalancedChen/BoundaryCellContainment.lean` | `12a74397730d07769c95cb7e1ab6adc4a3b570daedc49dbc65c0c0defd7ba80d` | `58a74f2c55a443bb9cd3751467b8316016b6d9333a1b5714edd1dd342f20a304` |
| `ImbalancedChen/FixedRoughCoefficients.lean` | `ca444f029bbe6c45b22d74e133a5e9fbb1ad4a4f729ba4cfd50efc0bdfc3a0d1` | `22494db2182529b0d05267604eaec12b3b178f9da8a75c28402b1113e745ac48` |
| `ImbalancedChen/FirstExitOwnCubeSplice.lean` | `8b45c5bc303236ad2eedcfb5041ea549307b1f67740386801f942493bb1380c8` | `42fcf157d04e77d7e525ae5fa491a76cb0d923a80eb75d7f6c92d799d091bfaf` |
| `ImbalancedChen/FirstExitFrontierInvariants.lean` | `041f9dcbd067d298264791cf18f6899965199a0741d1c8f894c434c2c5ab7809` | `ff7ab8a604da612b0df13a31cd7c01f2f0ca1bded20c58984b8d6323aacceae0` |

## Static verification and remaining gate

The pre-edit texts were captured before the cache check. Comparing them to
the final files shows all 42 theorem headers and all six computational
declarations byte-identical; imports are also identical. Counts by file
are respectively 11/3, 12/2, 7/1, and 12/0 (theorem headers/computations).
The diff is exactly ten line replacements and one deleted line, and
`git diff --check` passes. No linter setting, proof placeholder, new axiom,
`native_decide`, or `unsafe` declaration was introduced.

The next actual strict Lean run belongs to the root agent. These modified
sources have not been freshly compiled by this task and receive no new
compilation, kernel, numerical-evaluation, or P2.4-completion credit here.
