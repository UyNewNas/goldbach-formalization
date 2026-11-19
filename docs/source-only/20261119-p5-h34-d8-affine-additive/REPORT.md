# P5.6 → h34 | exact additive D8 two-affine payments

Date: 2026-11-19. Baseline: `768d8443c452246e99f9b8ae2181b9144240d2ee`.
Branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d`.

SOURCE_ONLY / PARTIAL_SOURCE_INCREMENT / UNCOMPILED / UNEVALUATED.
FULL_H34_OPEN. This packet modifies only the prior h34-owned second
D8 candidate and adds the new additive glue; other proof branches remain untouched.

## Actual Lean proof-body increment

1. Refactor `Part5OriginalH430D8SecondFourCell.lean` into two public
   statements: `genuine_d8_second_four_cell_ge_103_per_1000`, which
   proves the four-cell lower bound on the actual `cut..uHi` outer
   integral, and the original `genuine_d8_four_cell_ge_103_per_1000`,
   now a corollary using first-piece nonnegativity. This is a
   structural extraction of the EXISTING four-cell derivation, not a
   new assumption or duplicated full-D8 source.
2. Add `Part5OriginalH430D8TwoAffineAdditive.lean`.
   `second_piece_exact` identifies the real Ioo second-piece set
   integral with the original interval integral. The two independent
   original contributions then give
   `genuine_d8_two_affine_ge_108_per_1000`:
   1/200 + 103/1000 = 108/1000, counting each original affine once.
3. Combine the original three singleton floors (89,8,45)/1000,
   D5 130/1000, D6 110/1000, D7 27/1000 and the new D8
   108/1000. This is 517/1000 for all seven terms, divided by the
   SAME original 5, yielding the candidate
   `actual_lambda_ge_517_over_5000` (0.1034, versus 0.1024).
   Required lambda 0.13 and seven-source 0.65 are NOT established.

## Independent exact-rational diagnostic, NOT a Lean validation

The preceding second-four-cell floor is approximately 0.1032393182195;
the first-only Darboux floor approximately 0.0056264910571. Their
independent rational sum approximately 0.1088658092766 exceeds 0.108.
The fixed candidate lower total of all seven is 0.517, below 0.65.
No finite numerical evaluation is substituted for a proof.

## Integrity and validation boundary

Pre-write remote branch HEAD was `768d8443c452246e99f9b8ae2181b9144240d2ee`. No Lean, Lake,
Elan or pinned import closure installed in the local runtime.
Git HTTPS DNS resolution fails. An existing GitHub workflow is
visible, but no new workflow was dispatched; source-only docs are
not claimed to be in its compiled module set. No compiler, kernel,
transitive-axiom audit or inherited finite guard success is claimed.
No forbidden proof escapes, external axioms, target changes,
CI settings changes, dependency upgrades, P1.4 or P3.6 edits.

The earlier packet's REGISTRY source-blob pointer is amended so
the current branch preserves an honest source/blob mapping; the
old historical commit remains immutable.

## Manuscript-internal work still open

- Compile the exact source-only import chain with frozen v4.33.0-rc1.
- Obtain the strictly sufficient seven-source >=0.65 certificate
  (current candidate total only >=0.517) and correct base/seed.
- Actual 430-generation retention/Buchstab/bank all-action CLOSED-CELL
  induction, original U3/U4 selected-count weights and owner/rejection.
- Frozen intercept 20249/1000000, native-history mass,
  PP/same-rho, integral–Theta–count and common 430+11 causality.
- Kernel replay, transitive axiom audit and finite guards.

Complete h34 manuscript-internal proof remains OPEN.
