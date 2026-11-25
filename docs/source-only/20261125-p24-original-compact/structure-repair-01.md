# P2.4 structural compatibility repair 01

Status: source changes prepared; fresh compilation and strict audit are pending.

## Actual failure used

The parent agent reported P1 diagnostic job `job_bd7fe422f9fd4031abc8debc0a85d8c2`: the 43-module diagnostic closure completed in 60.7 seconds with stable inputs. The transparent-alias module, coordinate propagation, and initial seed inventory passed. The two modules repaired here failed as follows:

- `P2OriginalInitialClosedTree.lean`, original line 163: rewrite could not match the partition namespace's `originalCompactThirdCorrection` against the canonical finite-reserve constant in the goal.
- `P4AOriginalClosedTreeStructuralAggregation.lean`, original line 193: the same rewrite mismatch.
- The structural module's strict linter also reported unused `omega` in the right-child decrease proofs at original lines 24, 97, and 118, and redundant `all_goals rfl` after the leaf equations at original lines 29, 103, and 123.

This repair uses the reported completed diagnostic as its failure case. No compiler or cloud job was invoked by this repair task.

## Root cause and minimal changes

The existing P interface repair defines
`OriginalThirdCompactPartitionSourceOnly.originalCompactThirdCorrection`
as a transparent abbreviation of
`OriginalThirdFiniteReserveSourceOnly.originalCompactThirdCorrection`.
The finite-reserve correction, integration domain, and kernel are unchanged. The aggregation rewrite lemma names the abbreviation, while the two terminal theorem statements explicitly name the canonical constant.

Each affected proof now starts with an explicit `change` to the partition abbreviation. The original rewrite chain then applies. The theorem statements still name the canonical finite-reserve constant exactly as before.

The three right-child decrease proofs now end at `simp_wf`, which the diagnostic showed had already closed those goals; the left-child `omega` proofs remain. The three leaf equations now end after their existing `conv_lhs`/well-founded unfolding step. No linter option is disabled.

This is a formal expression and strict-linter compatibility repair. It adds no manuscript premise, numerical bound, historical tree, charge certificate, or new mathematical argument. It is not a proof gap in the 1106 manuscript.

## Related root-owned interface adaptation

The root agent separately adapted the three `P2OriginalAdaptiveForestSourceIdentity.lean` consumers of `simp [splitCount]` to the existing `splitCount_leaf` and `splitCount_split` equations. Their theorem statements are unchanged. This is a required adaptation to the reused well-founded implementation's explicit computation interface, not an observed compiler error: the forest module was blocked before compilation in this diagnostic. Its changed proof bodies remain pending verification. This repair task did not edit that file.

## Planned diagnostic cache reuse

The root agent plans a private diagnostic donor containing the 32 source/import-ancestor-matched but still unqualified donor modules and the three freshly passed objects from this diagnostic. Source bytes for the passed objects will be recovered from commit `67e0791e` and checked against the recorded source identities and diagnostic inputs before reuse. This is intended to avoid recompiling the same three stable passed modules while testing the repaired descendants.

The donor is for diagnostics only. It must preserve the source, object, and dependency hash bindings recorded by the actual runs; it does not itself provide current combined-closure or P2.4 acceptance. The donor construction and retry are planned root-owned steps, not actions executed by this repair task.

## Source identity and static checks

Base commit for this comparison: `63fcd8691951b552078d928bb840c5eef46d0221`.

| File | Before SHA-256 | After SHA-256 | Original public theorem statements preserved |
|---|---|---|---:|
| `ImbalancedChen/P2OriginalInitialClosedTree.lean` | `fe7ee6d0d9e0f8937fa69100a7c403bce4d7c53da0174b03ff0fef20e8d20ca4` | `51182d9392cc86ed93e88c71954574585f8003d3453fd06836804457b8420ef1` | 8 |
| `ImbalancedChen/P4AOriginalClosedTreeStructuralAggregation.lean` | `c1835984d62c74d7ffcc8ab6d4bf9e7c8532b1e9cfc85e4c5e7cc4457c39a840` | `d06107cb9dc1a14dad42d3b35a4adec5835f969682b3f2b99d7ea2dc671129c1` | 12 |

The public theorem headers, including targets and premises, were compared against the base commit and are unchanged. A source scan found no executable `sorry`, `admit`, `axiom`, `native_decide`, or `unsafe` tokens. `git diff --check` passed for the two changed Lean files.

The parent agent will rerun the actual compilation and strict audit. This record does not claim that the revised sources compile, that the downstream forest has been checked, or that P2.4 is complete.
