# P5.6 → h34 — actual selected row applied to genuine predecessor feedback

Date: 2026-11-09 UTC. Repository: `UyNewNas/goldbach-formalization`.
Dedicated branch: `chatgpt/p5-h34-actual-selected-feedback-operator-20261109`.
Incoming verified h34 HEAD: `245f3b46fad9a551be2a80df90e598f0b06ac2e5`.
Mathematics source commit: `93b08f5f3a1e674e6afe9554d3deabfcb4da4663`.
Math source: `Part5OriginalH430ActualSelectedFeedbackOperator.lean`.
Git blob: `34be1feb66d2b6c688b21f89b7a71c7d6f672771`.
One definition and five **candidate** theorem declarations, 173 added Lean lines.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Actual increment

The previous selected row budget gave exact bank/Buchstab winner-position masses and
`12 * actualBankTheta + 5 * actualBuchstabTheta`. It did NOT evaluate
the selected row on the actual predecessor feedback entries. This packet makes
that consumption explicit, while preserving the existing scalar/specified-cell
resolver, Fin occurrence multiplicity, original 106 bank, and separate norms.

- `actualSelectedOldRead` is the literal selected-row linear functional
  on `oldAtomValue (precedingH g) (precedingh g) b`, with no new count-owner data.
- `actual_selected_old_read_split` splits precisely the actual selected bank
  and Buchstab contribution; retention remains an exact read.
- `actual_selected_old_read_eq_winning_positions` rewrites that read to the
  ACTUAL Buchstab-or-bank Fin-position union, not a physical-product quotient.
- `nonnegative_row_old_input_bound` is a signed-value operator inequality
  for arbitrary old entries bounded in absolute value by M.
- `actual_selected_old_read_le_row_budget` transfers the genuine 12/5
  coefficient mass to the actual previous-array value.
- `uniform_actual_selected_old_read_operator` retains one threshold BEFORE
  N, n, root, tau, p, g, M and action selection. For every nonnegative M
  bounding the actual preceding entries it gives, in particular,

      |actualSelectedOldRead| <=
        (12 * actualBankTheta + 5 * actualBuchstabTheta) * M.

  It also reuses the earlier selected absolute error and genuine bank applied
  error bounds, keeping those as alternative estimates, not double payment.

The bounded M premise is a mathematical property of the previous feedback
array that a subsequent CLOSED-CELL induction must prove at its base and
successor. It is NOT supplied as an assumed original U3/U4 count theorem;
this packet does not claim the required base/seed is already available.

## Still OPEN, manuscript-internal

1. Prove the correct U3/U4 arithmetic count-source and selected/full/inherited
   owner correspondence, original root-weight normalization, stage filters,
   all six rejection lanes and physical q/tag multiplicities.
2. Prove the genuine CLOSED-CELL predecessor base, switched/fixed/seed/floor
   inequalities, and a valid previous-array M bound in the actual induction;
   link the new operator inequality to that successor without assuming
   arithmetic count coverage.
3. Prove the signed first-excluded Euler payment and effective H430 unpaid
   gap after collisions, not just the signed source decompositions.
4. Complete feedback-to-integral, manuscript PP/same-rho, native-history
   proper/equality/inherited mass, outer integral–Theta–count and common
   nested 430+11 causal refinement.

## Provenance, file ownership and validation

Fixed manuscript `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`
(`paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`).
Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
No change to c, K, root norm 7/2, bank row norm 12, separate Buchstab 5*Theta,
same-Q, real alpha, 106 actions or 430+11 schedule. No new external theorem.

GitHub connector confirmed write permission and no active workflow runs in the
latest run listing. The isolated h34 branch modifies only THIS new source-only
directory; no production modules, P1.4, P3.6, CI or manuscript changed.
No force push, merge or toolchain upgrade. Prior source and documentation were read.

The mathematics blob was committed and read back. This environment does not have
Lean, Lake or Elan, the staged fixed-version `ImbalancedChen/` import closure is
absent, and native Git DNS access remains unavailable. No GitHub CI dispatch,
Lean elaboration/compile, kernel replay, transitive axiom audit, or finite430
certification was carried out. Static source review is NOT a compile result.
All five theorem bodies are uncompiled candidates; ZERO green credit.

**Next:** stage the pinned import closure for the new source and run incremental
Lean checking, repairing any errors in the owned packet. Then use its actual
old-array bound in the genuine U3/U4 CLOSED-CELL base/successor, without assuming
a count owner or hiding q/tag debt.

**完整h34稿内证明仍未闭合。**
