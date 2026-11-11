# P5.6 / h34 — actual sequential fixed-Q source-slot erasure

Date: 2026-11-12 (Asia/Shanghai).
Repository: UyNewNas/goldbach-formalization
Dedicated branch: chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109
Verified baseline: 0c6afbfc76f0d90316ea42ed55f416ed7012f0bb
New module: Part5OriginalH430SequentialSlotErasure.lean
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes @ ba6ec11d800eccc54406490631895e174de85766.
Pinned Lean v4.33.0-rc1; Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
Keep original c/K, root norm 7/2, row norm 12, true alpha and both signed U3/U4 -1/4 labels.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual manuscript-INTERNAL increment

The previous exact occupied-slot packet bounded arbitrary filtered source
capacity but did not distinguish costs of consecutive policy gates.
This new module proves candidate finite identities on the actual fixed-Q
rank-two lists, with list occurrence indices and original source slots
never collapsed into q/tag receipts.

A slot fails first AND second exactly if it fails first OR passes first
and fails second. Those two actual slot sets are disjoint. Thus, per Q,

  E_(first && second) = E_first
    + #(kept observed slots at first AND rejected at second).

Summing at precisely the observed original physical Q values gives

  actualErasedQSlotDebt(first && second)
    = actualErasedQSlotDebt(first)
      + actualSecondStageSlotDebt(first,second),

and the latter is nonnegative.  Actual surviving source slots are the
intersection of the two source-kept sets.

The exact original tagged signed negative-quarter identity consequently
reads

  originalU34SignedQuarter
    = -(1/4)*(F_both + E_first + E_second + L_six(1))
      + (1/4)*U_both.

The literal six rejection/collision lanes and the unused position slack
are still separate. The new second-stage term counts only actual first-
stage surviving source slots, not every q/tag receipt and not arbitrary
free history positions. No possible root mark or finite experimental
certificate is substituted for the original selected-count owner.

New definitions: sequentialQGate; actualSecondStageSlotDebt.
Candidate theorems: erased_slots_sequential_exact;
first_erased_disjoint_second_increment; erased_slots_sequential_card;
kept_slots_sequential_exact; second_stage_slot_debt_nonneg;
actual_sequential_erasure_debt_exact;
original_signed_quarter_sequential_debt_exact.

## Exact boundary and validation

This is a two-stage finite source ledger, NOT proof that either test
equals the frozen manuscript full/selected/inherited gate or is causal
under the 430+11 common history. No new external analytic theorem, axiom,
sorry/admit, target-equivalent hypothesis, unsafe/native escape, toolchain
change or CI edit has been added.

GitHub connector was used for exact baseline, branch ownership, prior
source and provenance reads. Local system lacks Lean/Lake/Elan, native
git cannot resolve github.com, and the frozen source-only dependency
closure is not installed; therefore this Lean module has NOT been
compiled, kernel replayed or subjected to transitive axiom and finite
certificate audits. These declarations remain candidates; zero green.

## Remaining internal gaps

1. Derive and bind TRUE frozen full/selected/inherited causally valid
   Q-dependent predicates; sequential Bool gates do not prove ownership.
2. Prove original root norm 7/2 weighted U3/U4 q/tag selected-count
   owner, multiplicities and both overlap tags.
3. Bound newly incurred erased slots, six rejection/collision lanes,
   the actual signed Euler first-excluded suffix and native histories.
4. Quantitatively control q-multiplied physical residual, selected
   errors and complete CLOSED-CELL predecessor induction incl. actual
   base/switched/seed/floor.
5. Match manuscript-internal PP/same-rho, outer integral–Theta–count
   and one common 430+11 causal refinement.
6. Stage pinned source-only imports and execute true Lean/Lake
   compilation, kernel replay, transitive axiom check and finite guards.

NEXT: instantiate genuine frozen manuscript owner stages rather than
silently treating generic tests as selected/inherited; establish their
causal histories and effective stage-two erasure payment. Compile the
direct new module and imports once the pinned environment is restored.

**Complete h34 manuscript-internal proof remains OPEN.**
