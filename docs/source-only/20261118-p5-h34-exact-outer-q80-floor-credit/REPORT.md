# P5.6 → h34: exact outer Q80 quotient floor and complete capped credit

Date: 2026-11-18 (Asia/Shanghai).
Work branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified predecessor HEAD: `a267f8c65989ce8a0cd09603cb36a220e66ddc75`.
Mathematical source commit: `9437873f1d7d073ce96f89d79d2878599b404ac1`.
Source: `Part5OriginalH430ExactOuterQ80FloorCredit.lean`, 332 source lines.
Git source blob: `26b9a8f1bf6fb6dec376894f6d42bc81fb998992`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned toolchain: Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Distinct mathematical contribution

The prior true-bank proof had an exact PER-PRODUCT feedback quotient/remainder identity, but left the final OUTER integer quotient from the original 106-bank candidate merely as a one-sided inequality. The actual producer's divisor is 1 for W1, 5 for W2. Those are not the same as the per-product Q80 divisions. The previous literal Q80 positive-excess inequality therefore contained an unrecognized final floor gap, albeit in a safe upper direction.

This packet uses the actual immutable row, its original point list, the actual integer feedback numerator and the original outer divisor to define `originalOuterRemainder` and `outerRoundingLoss`. Euclidean division gives an exact signed-array identity:

    candidate(old, row) / 2^80 + outerRoundingLoss(old, action)
      = baseValue(action) + fixedValue(old.upper, action)
        + feedbackValue(old, action).

The outer loss is nonnegative even for signed arrays. Together with the existing per-product `ideal_feedback_exact` identity, at each ORIGINAL selected Fin occurrence and the SAME parent Theta:

    preFloorAtom
      = literalQ80Gap + floorAtom(per-product) + outerFloorAtom(final).

The complete eligible credit is capped by `max 0 preFloorAtom` BEFORE multiplication by the positive original path mark. The positive-part identity now yields the exact finite selected-bank equality:

    bankLiteralQ80IdealExcess + bankCompleteFloorCredit
      = bankPreFloorIdealExcess.

This improves the earlier one-sided result, which only credited the per-product integer loss and dropped the final outer remainder. No positive credit is asserted outside the true selected occurrence, and no unselected action, repeated path, or W1/W2 divisor is altered. The frozen 430-root consumer is supplied with the complete capped credit on the LEFT while preserving the real zero-generation seed, positive Buchstab physical source, same-Q pre-floor bank ideal deficit, and bank applied error. The outer loss is not re-added as a positive error.

### Accurate declaration coverage

- Definitions: `originalPointNumerator`, `originalOuterRemainder`, `outerRoundingLoss`, `outerFloorAtom`, `bankCompleteFloorCredit`.
- Theorems: `outerRoundingLoss_nonneg`, `literal_candidate_plus_outer_floor_eq_real`, `prefloor_eq_literal_plus_both_floors`, `literal_atom_plus_complete_credit_eq_prefloor`, `bank_literal_plus_complete_credit_eq_prefloor`, `bank_complete_credit_nonneg`, `frozen_root_le_prefloor_with_complete_credit`.
- Auxiliary private theorem: `positive_sub_two_floor_credit`.

The new stronger root consumer still does NOT discharge preceding CLOSED-CELL or original arithmetic count-source identities.

## Still-open manuscript-internal obligations

1. Restore a genuinely small bound on the true positive pre-floor dynamic balance and the selected real W1/W2 endpoint defects using the original Q80 recurrence and seed. No new smallness premise was introduced.
2. Prove full original base/fixed/switched/seed/floor CLOSED-CELL count induction; pay original strict-prime Buchstab physical source and terminal seed.
3. Identify the real generated feedback tree with COMPLETE U3/U4 full/selected/inherited, root norm 7/2, owner, q/tag multiplicities and all rejected source lanes. A Fin-indexed sum is not yet this count-source identity.
4. Prove manuscript-local PP/same-rho, signed Euler/native-history, outer integral–Theta–count, and one common 430+11 causal refinement with original c/K and row norm 12.
5. Stage original fixed-version import closure, compile source module and dependencies, replay kernel and audit transitive axioms and finite guards.

Genuinely external PNT/Mertens/BV inputs are unchanged, with no new proof or axiom.

## GitHub validation and ownership

Compared remote branch HEAD with previous `a267f8c` before writing. The new Lean blob was created on the isolated h34 work branch at source commit `9437873f1d7d073ce96f89d79d2878599b404ac1`. Remote re-read confirmed source blob `26b9a8f1bf6fb6dec376894f6d42bc81fb998992`, 332 lines, 5 definitions and 8 theorem declarations (1 private); GitHub compare showed one added file +332/-0, ahead 1, behind 0 before documentation.

Static text inspection found no `sorry`, `admit`, `axiom` or `unsafe` declarations. This is NOT Lean parsing or compilation. The execution container has git, but no Lean/Lake/Elan or staged fixed-version import closure, and `git ls-remote` fails on local github.com DNS. The available GitHub connector can commit/read files but cannot target-dispatch a module-specific Actions workflow. Existing automatic workflow results, if present, do not verify this source-only module.

Therefore no actual Lean/Lake compilation success, kernel replay, transitive axiom audit, or finite 430 certification is claimed. **No green status. FULL_H34_OPEN.**

Next: independently build the pinned source-only import closure and compile this file, fix actual Lean errors if any, then quantify the selected pre-floor dynamic and anchor deficits and build the full CLOSED-CELL/count bridge.
