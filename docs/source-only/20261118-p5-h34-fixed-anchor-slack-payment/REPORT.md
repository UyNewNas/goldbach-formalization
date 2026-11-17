# P5.6 → h34 — actual W1/W2 fixed-anchor slack to true selected-bank Theta

Date: 2026-11-18 (Asia/Shanghai).
Dedicated branch: chatgpt/p5-h34-full-tagged-actual-fin-20261112.
Verified predecessor: 0b556b4e2a2844a9324dc8a3574d31440336e94c.
Mathematical source commit: 7d5428978993c8811bd16a190108822c3d195cc6.
Source file: docs/source-only/20261118-p5-h34-fixed-anchor-slack-payment/Part5OriginalH430FixedAnchorSlackPayment.lean.
Git source blob: 8bf1f632783769f117c669fa404b06b8f463a570; 165 lines.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766.
Pinned Lean: v4.33.0-rc1; Mathlib: e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.**

## Mathematical source increment

The predecessor packet isolated a positive true fixed-read slack
fixedReference(F,a) - fixedValue(precedingH g,a). This is a real nonnegative
debt when the preceding CLOSED-CELL hypothesis holds; the predecessor did
not establish an upper bound small enough to pay the debt.

This packet makes its exact upper-payment structure concrete: define
FixedAnchorUpper(g,F,delta) using ONLY the original ten W1 endpoints and
36 W2 pairs. Each anchor requires the difference between F evaluated at
the original anchor and the actual previous table's floorValue at the
corresponding original query cell to be at most delta. It is a FINITE,
explicit, still-open manuscript-internal bound. It is NOT implied by
the existing one-sided predecessor CLOSED-CELL majorant.

The exact original W1 coefficient is 1. Original W2 fixed coefficients
are 4/5 and 1/5, summing to 1. Therefore the newly written candidates
prove (without a 106-fold, 5-fold or repeated-catalog multiplier):

  fixedReadSlack(g,a,F) <= delta_g, for all original 106 actions.

At every actual winning Fin occurrence, the old positive path mark and
same-Q parent Theta multiply this inequality. Using the previous true
occurrenceScale nonnegativity, the packet proves the candidate:

  bankFixedSlackMass(g,F) <= delta_g * bankSelectedTheta(g),

where bankSelectedTheta(g) is the sum of the EXISTING selected levelTheta
over the original 106 actions and actual winning list positions.

Finally the conditional frozen-root source bound retains the positive
feedback floor credit on the LEFT, the true seed at generation zero,
Buchstab positive physical source, positive dynamic-ideal debt and
applied bank error; only the fixed slack term is replaced by its
delta_g * actual selected-bank Theta envelope.

This is a genuine quantitative reduction to the original fixed-anchor
discrepancy, NOT a proof that delta_g is small, NOT a new numeric saving
and NOT a full h34 count-source bridge. No new exterior analytic theorem
or assumption equivalent to the final target was inserted.

## Unproved manuscript-internal inputs and validation

The preceding one-sided CLOSED-CELL condition remains unproved as a
full base/seed/switch/floor/action induction. The NEW fixed-anchor upper
condition is independent of that one-sided condition and is not yet
discharged from true prior table or integer/floor seed comparisons.
The dynamic base+idealFeedback−dynamicIdeal positive source, Buchstab
source and terminal seed remain unquantified. Original U3/U4 root
7/2 weighting, full/selected/inherited owner, q/tag and rejection
multiplicities, signed Euler/native-history, PP/same-rho, external
integral–Theta–count and common 430+11 refinement remain open.

The authenticated GitHub user has admin/push permission. Pre-write
branch HEAD was confirmed equal to 0b556b4e2a2844a9324dc8a3574d31440336e94c. No in-progress or queued
Actions runs on the dedicated h34 branch at the time of check; no
other branch/CI/workflow or source owned by P1.4/P3.6 was modified.
The mathematical source was added through a new Git tree/commit and
a non-force expected-SHA ref update, then fetched and compared.
Compare 0b556b4e2a2844a9324dc8a3574d31440336e94c...7d5428978993c8811bd16a190108822c3d195cc6: ahead 1 / behind 0 and exactly one
added 165-line Lean module. Exact source Git blob was reread.

The local execution container has git but no lean/lake/elan on PATH.
The original source-only import closure is not installed; this connector
can read/write GitHub but cannot run a Lean compiler or dispatch a
targeted Actions workflow. Therefore NO successful module compile,
kernel replay, transitive axioms audit, or finite certification exists.
A syntax/forbidden-token/delimiter scan and Git blob hash check are
strictly STATIC checks. NO green node was added.

## Next concrete action

Derive generation-wise delta_g estimates from the original INTEGER
precedingH/seed/Q80 CLOSED-CELL recurrence at the 82 actual anchor
appearances. Do not silently infer them from the one-sided majorant.
If such estimates are unavailable, move to the independent dynamic
ideal gap and book its correct positive payments. Stage the pinned
import closure for module-level Lean/Lake compilation before assigning
any compiled status.

**完整h34稿内证明仍未闭合。**
