# P2 strict03: original priority forest ledger proof repairs

Status: source-only candidate; original-checker retry required.

## Actual failure and frozen boundary

Input proof commit: `fcd0acba7dfc34cf14075b880e7a31aef1550b87`.
Actual P2 task: `c2edcc3a270e4e2aabb7155f3b8bc0e0`.
The complete run has ended. Its saved log is `p2-strict-symbolic-03.log`,
19,151 bytes, SHA-256
`3553e024808d4e959ba69b79575bc26a170604a7035e49a9e076d51b7d4f8205`.
The owned file is `ImbalancedChen/P2OriginalPriorityForestLedger.lean`;
its input bytes also match local repair HEAD
`2934bdb8a3f85f8c17dcc79d68dcd900d1c68e8c`.

Consulted the frozen publication commit
`3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`: the numerical appendix's
finite-verification scope and directed arithmetic, and
`verification/data/certify_extended_prefix.py` lines 402–437. The producer
adds every leaf's bounds to the full totals, puts only positive uncertainty
into the heap, subtracts the selected parent, adds side 0 then side 1, and
increments the split counter. Its relative-width/floor-midpoint selection and
serial allocation remain unchanged here. Producer SHA-256:
`1b77aa5deb90e0f39e06c776847a7e9fff27e23d584036955741b015ca05ad29`.

## Exact proof boundary

Ten existing proof bodies changed; all original theorem statements and all
computational declarations remain byte-identical.

| Original report | Minimal repair |
| --- | --- |
| 66: `List.append` versus `++` | Use the explicit `fun xs ys : List SeedCell => xs ++ ys` in `congrArg₂`, matching the existing tree/list equations. |
| 110, 117: function composition | Add `Function.comp_def` after the existing `List.map_map` rewrite. |
| 299–301: sum simplification order | Apply the two append-sum equations before unfolding the sum definitions; normalize empty map/sum terms explicitly, then retain the original `omega` proof. |
| 308: permutation direction | Use `List.Perm.swap p a`, whose conclusion has the required direction. |
| 452–464: constructor fields / append membership | Remove the indexed-away `st` from the `Step.split` case pattern; associate the replacement as `pre ++ (children ++ post)` before the existing membership cases. |
| 492, 496: induction script | Replace the reported unnecessary `simpa` with `simp`; explicitly bind the previous state in `Run.next`, and use the six-field `Step.split` pattern. |
| 522, 528, 539: kernel memory errors | Add one private function equality, `chargeTree_eq_attachCharges`, keeping its final `Run` proof argument unapplied. Instantiate it with `congrFun` and transport with `congrArg`; then use the existing attach/erase/list/local-bound lemmas without unfolding `chargeTree` at a concrete value. |
| 546: nested list cast | Reuse the already proved positional-module pattern: monadic integer-to-real list conversion equals `List.map` via `List.map_eq_flatMap`, then normalize `List.map_map` and `Function.comp_def`. |

The existing proof bodies are `tree_integer_boxes`, `completeTree_closedLeaves`,
`complete_integral_identity`, `refine_sum_updates`, `perm_move_parent`,
`step_preserves_invariant`, `run_complete_leaf_count`, `chargeTree_erase`,
`chargeTree_total`, and `chargeTree_local_iff`.

Classification: expression/API and proof-representation repairs, plus explicit
finite-list algebra already implied by the existing replacement identity.
No new enclosure premise, mathematical estimate, leaf omission, endpoint claim,
or substantive manuscript gap is introduced. The kernel-memory candidate needs
actual verification; no resource-success claim follows from this static change.

## Static checks and source hashes

- All **31 existing theorem headers**, including private helpers, are unchanged.
- All **20 complete definition/structure/inductive blocks** and imports are
  unchanged. The only new declaration is the private function equality above.
- `git diff --check` passed; no `sorry`, `admit`, axiom, native computation,
  unsafe declaration, linter setting, or resource override was added.
- Before SHA-256:
  `54413e8acd463748c4a874b76a8ad8183a6ad44f4db0fcad1fac399718a80550`.
- Candidate SHA-256:
  `54692ecb6f7fc9926b14291720586033ac8a49f43755600bb4f08300f6c7cbe7`.

Only the owned Ledger file and this note were edited for this task. The frozen
StateInduction repair was preserved. No P2 live-environment access, compilation,
remote task, broad audit, index update, staging, or commit was performed.
