# P5.6 → h34: selected positive original-anchor payment

Date: 2026-11-18 (Asia/Shanghai).
Work branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.
Verified predecessor HEAD: `5c12d15081a9b7c285e9f7dec01288787e658991`.
Mathematical source commit: `450814aaf72feae836ac90026993ba6ac940dfd8`.
Source: `Part5OriginalH430SelectedPositiveAnchorPayment.lean`, 271 source lines.
Git source blob: `e18e92ee880eabb8e4d415fabdb65d4b14eb9bec`.
Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Pinned toolchain: Lean `v4.33.0-rc1`, Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Why this packet is distinct from the previous exact 82-anchor maximum

The previous packet formed a **single maximum** over all original 10 W1
and 36+36 W2 anchor appearances. This is a correct finite uniform bound,
but charges every selected winning bank action the *same* worst anchor
even if that action reads entirely different original anchors.

This packet defines `actionPositiveAnchorAllowance` using the precise
original winning action, predecessor Q80 table and specified-cell fixed
read. W1 pays only its real endpoint positive deficit; W2 pays its true
4/5 first endpoint plus 1/5 second endpoint positive deficits. It
does not convert a specified-cell action to a scalar owner and does not
count unselected bank actions or quotient repeated Fin occurrences.

Using original `selectedLevel` and positive `occurrenceScale`,
`bankSelectedPositiveAnchorPayment` is the real selected-action
nonnegative weighted sum. The manuscript-local candidate theorems give:

1. `actionPositiveAnchorAllowance_nonneg` without a predecessor
   CLOSED-CELL premise.
2. `fixedReadSlack_le_actionPositiveAnchorAllowance`: genuine fixed
   slack is bounded by its action's clipped endpoint deficits.
3. `actionPositiveAnchorAllowance_le_actualAnchorDefect`: every
   actionwise amount is no larger than the original 82-anchor max.
4. `bankSelectedPositiveAnchorPayment_nonneg` for actual generated
   selected occurrences, using original root window geometry.
5. `bankFixedSlackMass_le_selectedPositiveAnchorPayment`: the existing
   exact fixed-slack debt is bounded without a new supplied delta.
6. `bankSelectedPositiveAnchorPayment_le_uniformDefect`: the finer
   payment is no worse than the prior `actualAnchorDefect *
   bankSelectedTheta` charge.
7. `frozen_root_le_selectedPositiveAnchorPayment`: insert the finer
   payment into the actual frozen 430-level root inequality while
   retaining zero-generation seed, positive Buchstab source, dynamic
   ideal/base discrepancy, bank applied error and feedback floor
   credit on the correct (left) side.

Thus the previous coarse 82-anchor payment is refined to the exact
selected-action endpoint debt. The pointwise estimates are elementary
convexity / max clipping; their invocation on original selected Fin
positions is explicitly written, NOT assumed from a scalar-owner
supplier. No quantitative smallness has yet been proved.

## Still-open manuscript-internal obligations

- Obtain an effective bound on the **actual selected positive endpoint
  allowances** from the original Q80 recurrence/seed. A finer nonnegative
  ledger alone is not a payment against the h34 budget.
- Prove the full original base/fixed/switched/seed/floor CLOSED-CELL
  induction. The root consumer still explicitly assumes its predecessor
  closed-cell premise; no equality to final h34 is introduced.
- Pay dynamic `base + idealFeedback - dynamicIdeal` positive source,
  strict-prime Buchstab positive source, actual zero-level seed and
  all integer-Q80 remainder effects.
- Complete full original U3/U4 full/selected/inherited owner/count-source,
  root norm 7/2, q/tag multiplicities and rejection lanes.
- Prove manuscript-local PP/same-rho, signed Euler, native-history,
  outer integral–Theta–count and common nested 430+11 causal refinement.
- Restore pinned import closure, run actual Lean/Lake compilation and
  kernel replay, transitive axiom audit and finite numerical replay.

## Verification, access and ownership

Before writing, the remote h34 work branch compared IDENTICAL to the
previous HEAD, and GitHub Actions returned no runs on that branch.
Repository permissions allow push. Only a new isolated directory under
`docs/source-only/` is written; P1.4/P3.6, production sources,
dependencies and CI configuration are unchanged.

After source creation, the GitHub content endpoint returned the exact
new blob `e18e92ee880eabb8e4d415fabdb65d4b14eb9bec`; compare showed
one forward source commit and no behind commits. Static inspection
found no sorry/admit/axiom/unsafe declarations; this is NOT a Lean
parse, elaboration, build or proof check.

Local PATH contained git but NOT lean/lake/elan. `git ls-remote`
failed with DNS resolution for github.com. The fixed import closure is
not staged. The connected GitHub interface has file write/read but no
targeted workflow-dispatch action. No Lean/Lake compile, kernel replay,
transitive axiom audit or finite certification was performed.
**No green nodes; every new theorem remains an uncompiled candidate.**

**完整h34稿内证明仍未闭合。**
