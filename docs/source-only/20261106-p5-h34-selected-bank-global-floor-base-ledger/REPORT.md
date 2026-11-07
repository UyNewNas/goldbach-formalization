# P5.6 → h34 — selected 106-bank global floor/base occurrence ledger

Date: 2026-11-06 (America/Los_Angeles). Repository: UyNewNas/goldbach-formalization.
Working branch: chatgpt/p5-h34-request-admission-20261105. Checked prior remote HEAD: `1b2cbea7d55435809adf5c9f1be0d0a089b2ea08`.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766` (unchanged).

## New manuscript-internal increment

`Part5OriginalH430SelectedBankGlobalFloorBaseLedger.lean` extends the previous per-product signed-division arithmetic ledger to
the entire *actual selected* 106-bank generation family. Every summand uses
the native `Index N n root tau p g`, actual selected action, exact positive
mark and same-Q parent Theta, without quotienting repeated history occurrences.

Declarations:
- `occurrenceTheta`, `occurrenceScale`, `occurrenceScale_nonneg`.
- `selectedBankActualGap`, `selectedBankIdealGap`, `selectedBankRoundingLoss`,
  `selected_bank_floor_exact`, `selected_bank_rounding_nonneg`.
- `selectedBankRoundingEnvelope`, `selected_bank_rounding_le_envelope`.
- `selectedBankBaseMass`, `selectedBankFixedMass`,
  `selectedBankIdealFeedbackMass`, `selectedBankPrimeChildMass`,
  `selected_bank_ideal_components`.
- `actual_one_generation_base_feedback_floor_upper` and
  `actual_one_generation_base_feedback_upper`.

The global identity is
  selected ideal gap = selected actual gap + actual per-product floor loss,
with 0 <= floor loss <= original weighted-product-length envelope.
In the one-generation consumer the floor loss has a **positive term on
the left-hand side**, so it is a credit against the idealized feedback,
not another positive expense. The selected bank candidate is split into
the original base + W1/W2 fixed read + ideal feedback - strict-prime
selected children. No original base or seed inequality is claimed.

This is a manuscript-local algebraic and positivity increment, NOT a
U3/U4 selected-count equality or full CLOSED-CELL count induction.
It uses exactly the preceding conditional old-cell bound, not a
new target-equivalent hypothesis.

## Boundaries

SOURCE_ONLY / UNCOMPILED / UNEVALUATED. No CI dispatch, Lean elaboration,
kernel replay, axiom audit or finite numerical430 replay. Static text
inspection is not a proof check. This packet does not touch P1.4, P3.6,
production modules, dependencies, constants, parameters or CI.

Open internal obligations: derive the preceding CLOSED-CELL count bound
from the actual U3/U4 arithmetic selected source; apply literal base,
switched and seed inequalities; identify original root weights, owners and
full/selected/inherited filters including rejection multiplicities; connect
the outer Theta/integral counts, PP/same-rho and native-history masses;
construct the common causal 430+11 nested refinement. Do not classify
these manuscript-local consumers as external.

Next independent step: match the *selectedBankBaseMass* and
*selectedBankPrimeChildMass* terms to actual original U3/U4 source-count
and corresponding seed/base payments; retain the exact negative floor
correction and the real occurrence multiplicities.
