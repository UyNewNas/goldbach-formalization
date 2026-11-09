# P5.6 → h34 — actual one-generation request all-action partition

Date: 2026-11-09 UTC.
Repository: `UyNewNas/goldbach-formalization`.
Independent h34 branch: `chatgpt/p5-h34-actual-request-all-action-partition-20261109`.
Latest verified incoming task HEAD: `43a957dc61334d04947af2fdcf4ed84529cd9732`.
Historical entry `0a3fa5aa639e74122fbef18be02f0ad6fa8a77a0` was inspected but NOT reused as the working baseline.
New mathematics commits: `9075949b8311075a3b3619b862031441b7265b73` (new file), `6ca60e35e5a4ffa121c0164e46112708f375553b` (proof-source filter-membership correction), and `54c0dec65865c4a550a03e8d1ad2b5184b1c324c` (explicit original106 action namespace).
New source: `Part5OriginalH430ActualRequestAllActionPartition.lean`.
Source blob at math HEAD: `0e46ad687609d499c2200a86eb00f49937413e04` (251 lines, 5 definitions, 10 candidate theorems).

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Checked handoff and why this is a different source increment

Read the original 20261105 request-admission REPORT/REGISTRY/EXTERNAL_INPUTS, then the current actual-Q signed-gap handoff from `43a957dc`. Checked the actual request/history, selected-level 106-bank supplier, and fixed read/action slot files. Older h34 task branches are ancestors of `43a957dc` in the remotely checked commit chain; this work therefore starts at that SHA, not at the historical entry. New independent path prevents contention with concurrent h34/P1.4/P3.6 task ownership.

The previous bank-level source theorem partitioned 106 selected bank actions, but did NOT enumerate the retained and Buchstab branches on the very same computed Fin level. This packet completes the FINITE, exactly selected, one-generation action partition. It DOES NOT claim the later all-action count induction.

## Exact candidate declarations

1. `actualChoice`: computes the genuine generation-`g+1` resolver on each actual `Index N n root tau p g` and reads the winning `roundDecision (iterate g)`. It handles scalar and specified-cell requests without identifying their distinct semantics.
2. `actual_choice_iff_selected`: equivalence with the existing `Selected g.val` predicate; no hypothetical action owner is supplied.
3. `retainedLevel`, `buchstabLevel`, `bankLevel`, `resolvedLevel`: finite sets of actual LIST positions at the same root and generation. No product/d/catalog quotienting or sum across unrelated generations.
4. `bank_level_iff_actual_bank`: uses the original `actionOfSlot`/`slotOfAction` bijection and all 106 bank rows.
5. `resolved_level_partition`: exact exhaustive union of retention, Buchstab and bank under the original `Choice` constructors.
6. `retained_buchstab_disjoint`, `retained_bank_disjoint`, `buchstab_bank_disjoint`: no list occurrence wins two alternatives in the same round.
7. `bank_level_sum_eq_original_106`: transports the previous `sum_selectedLevel` exactly to the bank part of the current partition.
8. `resolved_level_sum_all_actions`: arbitrary SIGNED test F over the actual Fin positions is exactly partitioned into retention + Buchstab + original 106 rows, without duplicate charges.
9. `unresolved_level_value_zero`: unresolved exterior positions have literally zero `requestValue (iterate (g+1))`, by the existing `resolve_none_value`, not by invented support excision.
10. `actual_level_request_value_all_actions`: the FULL original one-generation sum of `levelMark * requestValue (iterate (g+1))` splits exactly among retained, Buchstab and 106 bank selected positions. Original path marks, physical root Q, generation and occurrence multiplicities are unchanged.

There are ten candidate theorem declarations, four finite-position set definitions and one actual-selection definition. The full count is anchored to the exact source file. This is SOURCE COVERAGE ONLY. It is not yet a theorem that the original `Upsilon3/Upsilon4` counts are the same finite request history, nor a positive error bound or the original 430-level count induction. The original all-action retention/Buchstab quantitative comparison and base/seed/floor remain separate obligations.

## Fixed mathematical boundary

Manuscript mapping is unchanged: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, the old 2026-10-10 tracked edition (not silently switched to the 2026-11-06 public release). Toolchain Lean `v4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`. Original c/K, root norm 7/2, row norm 12, physical Q, true alpha, exact 106 slots and positive list-position marks all unchanged. No analytic theorem added or moved outside the manuscript.

Only this new task-owned directory is written; no production file, pinned manuscript, P1.4, P3.6, workflow, toolchain or master edit, merge, rebase or force push. The source uses no sorry, admit, custom axiom, unsafe or native escape.

## Validation — do not mark COMPILED

The connected GitHub repository grants owner push; remote source blob/diff are read back at the exact SHA after write. Local execution checks: `lean`, `lake`, `elan` not available on PATH, native Git DNS for GitHub unavailable, and these held source-only imports are not staged into a buildable pinned Lake import closure. Existing CI does not build these held packets without a staging process; do not change CI. No Lean elaboration, successful compile, kernel replay, transitive-axiom audit, CI build or finite numerical430 certification is claimed. Static token checks and Git object integrity are NOT Lean validation. All proof bodies and inherited finite guards are UNEVALUATED.

## Remaining exact manuscript-internal obligations

- Connect the genuine retention and Buchstab request-level quantitative source comparison to this actual selected Fin set, then run the full CLOSED-CELL count induction with the correct base/switched/seed/floor and predecessor boundary.
- Establish the actual selected-count owner, full/selected/inherited filtering, original U3/U4 root count weights and the exact original q/tag-to-history source identity; account for collision multiplicity and all six rejection lanes.
- Prove a useful signed quantitative payment against H430, not just the earlier actual-Q one-event-mass directional gap or whole-original-count envelope.
- Instantiate feedback rounding-to-integral, manuscript-local PP/same-rho, native-history proper/equality/inherit quality and outer Theta/count bridge.
- Build the single common 430+11 nested causal refinement; restore an isolated pinned dependency build and run Lean/kernel/axiom/finite checks.

**Next direct task:** stage this exact new module and its pinned request-level ancestors in a separate temporary compilation workspace, compile incrementally and repair any elaboration errors; then attach the literal request-level retention/Buchstab value to the three-way Fin partition without replacing the actual owner or altering the hand-written manuscript target.

**完整h34稿内证明仍未闭合。**
