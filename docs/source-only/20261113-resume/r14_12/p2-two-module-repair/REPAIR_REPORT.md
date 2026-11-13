# P2 two-module proof-expression repair — source only

This successor repairs only `ActualThirdOriginalP4AOrdinaryOuterMinimum` and
`ActualThirdOriginalP4ASymmetricPairRealRescue`. It is **uncompiled**: compiled
modules **0**, kernel-verified modules **0**. ROOT must obtain independent source
review and the necessary GitHub compilation/kernel/type checks before acceptance.

## Exact input selection

The actual failed execution was run `43402135668`, job `131807322477`, driver head
`8efe66f50b8d3aff776883c051cee6d23f414a63`. FULL102 compilation failed at step 15;
kernel/types at steps 16/17 were skipped. Cache11+407 qualification, the single
FinitePi pilot and runtime audit do not constitute FULL102 proof acceptance.

The committed root selection SHA256 is
`0596571c8822b89866444081722b801c291f82f62871648fafa8911ac77dd825`.
The selected manifest SHA256 is
`e1ab63bdcb027e40c592138b7ca712e1af99864404a94ee893645ab0180fa3ff`.
It selects mathematical source `686024b292027816b712963167436c445df5e68e`, with
84 baseline modules and 18 ABI overlays. Both repaired modules are explicitly
**baseline** entries from `eb035a259f2f40853e9899f6d98af25852184fee`.

Source identity was cross-checked against:

- `output/resume-20261113/r13_03/P2_EXPECTED_102_SOURCE_ALLOWLIST.json`;
- the r6 actual-commit independent review;
- exact committed r6 root selection and manifest;
- the already-downloaded ZIP's `VALIDATION_MANIFEST.json`,
  `SOURCE_OBJECT_BINDINGS.json`, and `P2_STAGE_RECEIPT.json`;
- exact `commit:path` objects read from `output/t-batch-20261110/publish.git`.

No main-branch same-name source was used. Original source hashes, Git blobs,
postimage hashes, byte sizes and paths are frozen in
`SOURCE_PINS_AND_STATIC_CHECKS.json`.

## Failure localization and repair

The existing light ZIP was read statically, without another download:
`p2-integer-mass-lightlogs-43402135668.zip`, 3024874 bytes, SHA256
`b12acd1beb5a684c3f00315875b933555c168ae50e5d911804033f9d2f618c25`.
Its `batch-build.log` is 42542 bytes; lines 490–568 contain the complete relevant
failure contexts.

| Original source location | Classification | Proof-expression change |
| --- | --- | --- |
| OuterMinimum:174, `actual_new_mean_le_lower_corner` | Formal expression: `-1 + A` versus `A + -1` | Add `add_comm` to the existing `simpa only` set, retaining `hdiv` and the original inequality. |
| OuterMinimum:183, same theorem | Formal expression: the preceding `field_simp` has already closed the goal | Sequence the existing `ring` with `<;>` so it runs only on remaining goals. |
| OuterMinimum:204, `original_new_endpoint_cast` | Formal expression: `push_cast` normalized the target's numeral but left the cast numeral in `htheta` | Use `push_cast at htheta ⊢` so the existing real equality and target receive the same normalization; retain `rw [htheta]`. Also sequence the final existing `ring` with `<;>`. |
| PairRealRescue:215 and :320, the two saved-producer chord suppliers | Formal expression: ordinary `match k` versus the bridge's dependent match | Prepend `cases k <;>` to each existing branch transport proof. Both rise/fall tests remain exactly the original tests. |

The cast repair retains the original local equality
`(T₀ : ℝ) = (D₀ : ℝ) * thirdPrefixTheta`, and retains the original positivity and
nonzero premises. Here `D₀ = 48000 * 2^24 = 805306368000` and
`T₀ = 481573208064`; no numeric operand is replaced. `haBind`, `hz`, `hal`, `hD`
and `hz0` remain unchanged.

The two branch repairs directly reuse the published pattern at
`686024b2:docs/source-only/20261112-resume/t02/p2-repair-r5-r1/repaired/ImbalancedChen/ActualThirdOriginalP4ASymmetricSafeChordDirection.lean:229`
and its sibling `ActualThirdOriginalP4ABalancedSymmetricLeaf.lean:345`.
Both use `cases k <;> simpa only [...] using hbranch` for this exact bridge.
Both sibling modules were reported Built in the actual run's batch log.
The local r4 prerequisites repair also has the same pattern at line 436.
Repository history for the two failing module paths has no later same-path
repair to transplant. The proof changes above reuse the existing patterns
without rewriting the mathematical arguments.

All five reported error sites are classified as **formal expression** issues.
No omitted mathematical lemma or substantive mathematical gap was identified
in these sites. This is a source assessment, pending elaboration/kernel checks.

## Frozen scope and verification limits

`TWO_MODULE_PROOF_ONLY.patch` is the minimal unified diff against the selected
baseline objects. Exact allowlisted text-rewrite comparison reproduces both
postimages. A static declaration-header extraction compares all 30 OuterMinimum
and 22 PairRealRescue headers byte-for-byte; all are unchanged. It splits at each
top-level declaration start, then stops before `:=`, `where`, or the first
equation branch, so equation-style definitions are counted individually. This
extraction is a text check, not a Lean elaboration or kernel result. Imports, namespace,
definitions, theorem statements/parameters, interval and numeric operands,
branch/root/residual/low guards, source-reader calls and hypotheses are retained.
No `sorry`, `admit`, new axiom or opaque target is introduced.

Only this successor directory was written. No protected continuation HEAD,
index or worktree was changed. No Git/GitHub mutation, dispatch, quota check,
Lean/Lake/LSP, environment setup, stage/producer/proofguard/fixture/runtime or
certificate execution was performed, and no project Python helper was run.
The archive was used only as a static input. Independent Astra03 review and
ROOT-controlled GitHub validation remain required.
