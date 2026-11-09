# P5.6 / h34 — actual next-table signed source residuals

Date: 2026-11-09.
Repository: UyNewNas/goldbach-formalization.
Branch: \`chatgpt/p5-h34-actual-nexttable-signed-source-residual-20261109\`.
Verified incoming remote HEAD: \`5167669f67ecfd467193bed8ad76ee56db3c2286\`.
Actual mathematics commit: \`c372f9c4af12fa26de251c779d157e93bc33a21f\`.
Source: \`Part5OriginalH430ActualNextTableSignedSourceResidual.lean\`.
Remote source Git blob read back: \`b0eb5a241af0fecd5f4c16ea8154fae9ec1dd532\`.
251 inserted source lines, four definitions and seven theorem **candidates**.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Fixed baseline and ownership

The previous h34 packet at \`5167669\` built a mixed-generation
retention-plus-selected coefficient read and a same-Q ideal envelope.
It explicitly did **not** identify the new-table bank/Buchstab request
values with old-array row reads. This packet addresses that exact open
boundary. The initial entry SHA \`0a3fa5a\` is historical, not the base.

The linked account has push permission. The new branch was created
from the verified incoming HEAD. The GitHub Actions in-progress
query returned zero runs at the ownership check. No other task's
file was edited, no CI settings or dependency pins were changed,
and no default-branch merge or force push was performed.

## Manuscript-local source added

1. \`actualNewTableRead\`: the exact generation-(g+1) requestValue
   sum over original generated Fin occurrences, including unresolved
   zero positions.
2. \`actualBankSourceGap\`: literal winning bank next-table read minus
   actual 106 bank coefficient rows applied to
   \`oldAtomValue (precedingH g) (precedingh g)\`.
   \`actual_bank_source_gap_eq_original_actions\` exposes every original
   action slot without counting unchosen alternatives.
3. \`actualBuchstabSourceGap\`: literal winning Buchstab next-table read
   minus its physical old-array coefficient read.
   \`actual_buchstab_source_gap_eq_winning_positions\` expands the
   gap to actual Fin history positions, retaining list multiplicity,
   physical rootQ and the literal old array.
4. \`actual_new_table_eq_retained_physical_plus_source_gaps\` gives
   the exact true next-table = retained+selected-physical + both
   unproved signed source gaps.
5. \`actual_new_table_same_q_gap_le_source_residuals\` gives

   |new-table - retained+selected same-Q ideal|
       <= |bank source gap| + |Buchstab source gap|
          + actualSelectedError.

   The selected coefficient error is paid exactly once; no new
   estimate for either source gap is assumed.
6. \`actualBankCandidateGap\` is the original sum of the actual
   106 \`markedBankCandidate\` values minus the physical bank old-array
   row read. \`actual_bank_source_gap_le_candidate_gap\` uses the
   original one-sided \`all_markedBankRead_le_candidate\` inequality.
   \`actual_new_table_same_q_one_sided_source_budget\` preserves the
   *signed* Buchstab source gap and candidate-bank gap; it does not
   assume either is nonnegative.
7. \`uniform_actual_new_table_same_q_source_residual_bound\` reuses
   the previous single pre-N threshold to replace only the paid
   \`actualSelectedError\` by \`epsilon * actualSelectedTheta\`.
   The two literal source gaps remain explicitly on the right.

These are exact feedback-source identities/inequalities, not a
CLOSED-CELL original arithmetic selected-count bound. No alternative
scalar action is substituted for a specified-cell winner.

## Remaining internal obligations

- Prove appropriate signed / absolute bounds on the **literal**
  \`actualBankSourceGap\` and \`actualBuchstabSourceGap\` from the
  original next-table rule, base/seed/floor and feedback recursion.
  A one-sided 106 bank candidate inequality alone does not pay both.
- Bound real predecessor L1 growth, and identify original
  U3/U4 complete selected-count source, physical root weights,
  full/selected/inherited owners and six rejection lanes, including
  q/tag event-key collisions and legitimate signed H430 payment.
- Establish the exact manuscript PP/same-rho integral consumer,
  native-history controls, outer Theta/count relationship and
  one causal 430+11 common nested refinement.
- Check the fixed Lean import closure, compile, replay the kernel
  certificates, audit transitive axioms and evaluate finite checks.

## Evidence boundary and installation

Manuscript map is unchanged:
\`UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766\`,
\`paper/source/manuscript-body.tex\`, blob
\`d529bea2ecfcc74d64fc1664ac770a3becaa7c79\`.
Lean v4.33.0-rc1 and Mathlib
\`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1\` remain pinned.
Original c/K, 7/2 root norm, bank 12 and Buchstab 5
norms, same-Q, original alpha and all counting multiplicities
are unchanged. No genuinely external analytic input was added.

The remote source file, blob and mathematics commit were read back;
the source has seven named theorem bodies and no forbidden
proof-escape tokens. This is STATIC evidence only. The execution
container has git but no lean, lake or elan, and native git clone
fails DNS resolution for github.com. The source-only pinned import
closure is not installed. No Lean/Lake compile, kernel replay,
transitive axiom audit, numerical430 certificate replay or successful
CI run was performed. The inherited finite guards remain UNEVALUATED;
nothing is marked COMPILED or green.

**Next exact action:** stage the fixed source-only import closure
and compile this new module with its direct predecessors. Then
derive the genuine next-table bank/Buchstab source-gap bounds
from the original recursion and floor/seed/base, not by asserting
their disappearance.

**完整h34稿内证明仍未闭合。**
