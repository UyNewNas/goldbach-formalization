# P5.6 → h34: clipped Q80 anchor deterioration and recovery

Date: 2026-11-18 (Asia/Shanghai).
Work branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Actual remote predecessor HEAD: e22648772dbe5f30bd963e4780fb50acfd112369.
Mathematical-source commit: 63779ff5ff426214fc752df031a2759474e6ae6d.
Source: Part5OriginalH430ClippedAnchorRecovery.lean (312 nonempty/total Git added lines; 313 split lines including terminal newline).
Verified mathematical source blob: bc12ab1cc1a3a0de39daa5c1cb0cf7a394b34d59.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned toolchain: Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual independent mathematics added

The preceding selected-anchor-backward-variation source charged the entire downward variation of each original Q80 upper-table fixed endpoint. A downward movement entirely above the analytic reference F does not increase a positive reference-table gap and should not receive that whole charge. Conversely, a later rise of the Q80 cell can repair an earlier positive gap. The prior one-sided estimate discarded both clipping and recovery.

This source defines, at each original fixed cell i and literal update k→k+1 with reference z:

    rise(k,i,z) =
      min( max(0,z-H_{k+1}(i)), max(0,H_k(i)-H_{k+1}(i)) );

    recovery(k,i,z) =
      min( max(0,z-H_k(i)), max(0,H_{k+1}(i)-H_k(i)) ).

It supplies candidate Lean proofs of the exact identity

    max(0,z-H_{k+1}(i)) + recovery(k,i,z)
      = max(0,z-H_k(i)) + rise(k,i,z).

Finite range induction produces the genuine temporal balance for every actual preceding generation g:

    positiveAnchor(g) + cumulativeRecovery(g)
      = positiveAnchor(0) + cumulativeEffectiveRise(g).

This is strictly more informative than the previous one-sided seed-plus-gross-downward-variation estimate. It neither assumes Q80 monotonicity nor treats the two min terms as automatically small.

The action definitions preserve the ORIGINAL W1 fixed endpoint and W2 endpoints with the precise 4/5 and 1/5 coefficients. The actual selected Fin occurrence sums keep multiplicity, same-Q parent Theta and original nonnegative historical marks; no distinctness quotient or scalar-owner replacement is used. Candidate equalities compare true selected anchor payment + true selected recovery with selected zero-iterate anchor mismatch + effective deterioration. Candidate inequalities establish nonnegative recovery and show effective rise is at most the earlier gross backward-variation charge.

Finally, frozen_root_le_clipped_rise_with_floor_and_recovery puts BOTH existing real Q80 floor credits and the additional actual clipped anchor recovery on the LEFT of the original 430-root inequality. The RIGHT contains unchanged true zero-generation request seed, original physical Buchstab source, base/ideal positive deficit, actual selected initial anchor deficit and clipped effective rise, plus bank applied absolute error. The predecessor CLOSED-CELL property remains a visibly required, UNPROVED manuscript-local hypothesis. We do not infer that any source is paid or small.

## Exact source coverage

Eight definitions:
- effectiveAnchorRise
- effectiveAnchorRecovery
- actionEffectiveRise
- actionEffectiveRecovery
- actionCumulativeEffectiveRise
- actionCumulativeEffectiveRecovery
- bankSelectedAnchorRecovery
- bankSelectedEffectiveRise

Twelve candidate theorem bodies (including two private):
- effectiveAnchorRise_nonneg
- effectiveAnchorRecovery_nonneg
- effectiveAnchorRise_le_drop
- clipped_step_balance (private)
- clipped_range_balance (private)
- action_effective_rise_le_backward_drop
- action_effective_recovery_nonneg
- action_anchor_balance
- bank_selected_anchor_balance
- bank_selected_anchor_recovery_nonneg
- bank_selected_effective_rise_le_backward_variation
- frozen_root_le_clipped_rise_with_floor_and_recovery

These are proof-source candidates, NOT verified Lean theorems.

## Remaining manuscript-local duties

1. Establish quantitative payment for the literal selected zero-iterate positive anchor deficit and actual clipped rises, using the original Q80 base/fixed/switched/feedback/seed recurrence; nonnegative recoveries cannot be assigned an invented positive lower bound.
2. Prove complete original all-action preceding CLOSED-CELL induction, including seed, base, fixed, switched, true Q80 floors, and Buchstab/retention request supplies; control true strict-prime Buchstab physical source and terminal zero-generation seed.
3. Identify complete original U3/U4 full/selected/inherited arithmetic counts, root weight 7/2, owner, q/tag multiplicities and all rejection lanes. The present request-level physical sum alone does not do this.
4. Close manuscript-local PP/same-rho, signed Euler/native-history, outer integral–Theta–count correspondence and ONE correct common 430+11 causal refinement under the unchanged c/K and row norm 12.
5. Stage the pinned source-only import closure, compile this module and direct imports, repair genuine Lean errors, kernel replay, transitive-axiom audit and the inherited finite guards. Do not confuse static text/bytes with compilation.

## Validation and ownership

Remote branch HEAD and permission were checked before writing; the branch was exactly e22648772dbe5f30bd963e4780fb50acfd112369. Zero running and zero queued GitHub Actions on this dedicated branch were observed. The mathematics file was created only in the new owned source-only directory at commit 63779ff5ff426214fc752df031a2759474e6ae6d. Remote readback gave blob bc12ab1cc1a3a0de39daa5c1cb0cf7a394b34d59; GitHub compare against the predecessor showed 1 new file, +312/-0, ahead 1, behind 0.

Static text check on new proof-bearing code found no sorry, admit, axiom, unsafe or native_decide and balanced parentheses, brackets and braces. The local container has git but no lean/lake/elan. Native git ls-remote failed github.com DNS resolution. No pinned source-only dependency closure is staged here. The connector can write and read repository content, but does not expose a targeted GitHub Actions workflow dispatch operation; existing automatic workflows are NOT a substitute for a proven compile of this module.

Therefore: no Lean/Lake success, no kernel replay, no transitive-axiom audit, no finite-certificate replay, and no green node. This source-only increment does not touch production files, P1.4, P3.6, the frozen manuscript, CI, toolchain, original c/K, root norm 7/2, row norm 12, original same-Q/alpha or 430+11 budget.

**下一明确动作:** evaluate whether the original Q80 update can quantitatively bound the *effective* selected anchor rises, including the legal seed comparisons. Stage the fixed source-only imports and run a genuine incremental Lean compile before claiming proof correctness.

**完整h34稿内证明仍未闭合。**
