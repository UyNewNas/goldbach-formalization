# P2 strict run: compact frontier canonical owner import

Input commit: `fb61b4cd912765dc7975051055b0d2c3ed3d3714`.
Actual P2 job: `8fcc0987e7cc4f6f8d7613ee772f3609`.
Owned source: `ImbalancedChen/ActualExtendedThirdCompactFrontier.lean`.

The observed live log `/workspace/scratch/daaa8ebc2a3f/p24-p2-live/current.log`
was 27,316 bytes, SHA-256
`1b524137507292bac976acf22c8fe62c6d2e6770412e9eb9c6459b119a68c9a9`.
This binds the inspected snapshot while the job was running, not a final run.
It reports unknown `FirstExitValidSelection` at 62/81,
`firstExitFrontierTuples` at 94, `firstExitFrontierCandidates` at 149/167,
and `firstExitFrontierCandidates_weighted_sum_eq_tuple_sum` at 174.
The later displayed `sorry` goal is elaborator error recovery after those
unknown identifiers; it is not a source proof placeholder.

## Exact minimal change

Added one line:

```lean
import ImbalancedChen.FirstExitFrontierTupleReindex
```

Every other source byte is unchanged, including theorem statements, hypotheses,
proofs, the candidate-sum definition, and its original signed test.

The imported module owns `firstExitFrontierTuples`,
`firstExitFrontierCandidates`, their weighted sum equality, and the already-used
`mem_actualPrimeFrontierTuples_iff_of_cutoff_le_cap`. It imports the canonical
`FirstExitValidSelection` module. All these declarations are in namespace
`ImbalancedChen`, which the consumer already enters; no additional `open` or
name substitution is needed.

Classification: **missing dependency / declaration-resolution expression issue**.
Existing finite frontier and tuple proofs are reused. No new mathematical
claim or premise is introduced.

The frozen 1106 `sieve-appendix.tex` at publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e` was consulted: `sv:upper-cubes`
and `sv:first-exit` (41–80), plus `sv:finite-realization`'s compact refinement
and retention of ancestor decisions (265–303). The reused owner tests only
the proper parent prefix (`dropLast`) and leaves the next candidate's own
gate untested, as required by the existing consumer formula. No density
estimate, changed cutoff, or extra first-exit admission is supplied here.

## Static dependency delta

Using the existing `core_header` parser, both graphs were traversed with only
this file's import header varied between original and candidate bytes:

| Root | Project modules before | After | Change |
| --- | ---: | ---: | --- |
| `ActualExtendedThirdCompactFrontier` | 106 | 110 | Add `FirstExitFrontierInvariants`, `FirstExitFrontierTupleReindex`, `FirstExitOwnCubeSplice`, `FirstExitValidSelection`. |
| `P2OriginalCompactWholeFunctionalEndpoint` | 322 | 322 | No module added or removed; all four owners were already in the total closure. |

Non-project header-import name sets are unchanged: 86 for the frontier root,
136 for the total endpoint. These counts are import-name sets, not a new native
object census or qualification. No import cycle was found. The added edge makes
the owner's availability and dependency ordering explicit.

## Source binding and verification

- Before SHA-256:
  `8e15c650d9e5e0b7f72aa16589a4dbf2049687558482d096f48f7fee1635dbe7`.
- Candidate SHA-256:
  `260b087d53c8252f71d626a63db320d7fd1dcb62fa9025c30a3135aa34634638`.
- Exact one-line insertion reconstruction and `git diff --check` passed.

Only the owned Lean file and this note were edited. No other module's style
failures were changed. No CI/archive audit, Lean/Lake invocation, remote job,
index update, staging, or commit was performed. This candidate awaits actual
retry; no compile or kernel credit is assigned here.
