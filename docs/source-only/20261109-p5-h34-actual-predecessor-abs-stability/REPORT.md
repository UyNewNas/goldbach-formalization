# P5.6 / h34 — actual predecessor absolute budget and signed selected-row stability

Date: 2026-11-09. Repository: `UyNewNas/goldbach-formalization`.
Branch: `chatgpt/p5-h34-actual-predecessor-abs-stability-20261109`.
Incoming verified h34 HEAD: `047c17d7c92388fd17d9622f9af8145b13295012` (not the historical 0a3fa5a entry).
Mathematics commit: `a3a013e504b85a4c32f41f8b317df8c6543051f6`.
Source: `Part5OriginalH430ActualPredecessorAbsStability.lean` (191 lines;
one definition and six manuscript-local theorem candidates).
Source blob: `fdf3eb36d3ba04501a7572a69cb133d4f43ca5fe`.

**PARTIAL_SOURCE_INCREMENT — SOURCE_ONLY — UNCOMPILED — UNEVALUATED — FULL_H34_OPEN.**

## Why this is a distinct increment

The previous `Part5OriginalH430ActualSelectedFeedbackOperator` bound the
true selected Buchstab/106-bank feedback operator subject to an arbitrary
caller-provided per-generation bound `M` on every actual predecessor
`oldAtomValue`. This module discharges that premise *for the literal array*
with `predecessorAbsMass g`, the sum of its genuine RowAtom absolute entries.
It also proves a signed perturbation estimate for **two arbitrary preceding
atom arrays** under the same genuine selected coefficient row. The latter
is the finite-operator comparison required before any future proposed
old-versus-integral feedback identification.

Mathematical statements (written as Lean proof candidates):

1. `predecessor_abs_mass_nonneg`: finite actual old-array absolute mass
   is nonnegative.
2. `predecessor_abs_le_mass`: every old RowAtom is bounded by its actual
   preceding-generation absolute mass. No separate `M` hypothesis.
3. `actual_selected_old_read_l1_envelope`: the true preceding array's
   selected-row read satisfies
   `|read_g| <= (12*bankTheta_g + 5*BuchstabTheta_g)*predecessorAbsMass_g`
   when the existing row nonnegativity and 12/5 bounds hold.
4. `actual_selected_row_difference_l1`: for *any signed* vectors `v,w`,
   the difference of their evaluations under the actual winning row
   has magnitude at most
   `(12*bankTheta_g+5*BuchstabTheta_g)*sum_b |v_b-w_b|`.
   This does not assume or assert that `w` is already an analytic integral.
5. `uniform_actual_predecessor_abs_stability`: one pre-`N` threshold
   packages the actual selected absolute error, bank applied error,
   concrete predecessor bound and arbitrary-vector stability.
   All original root/prime/tau/n conditions are kept.
6. `actual_selected_old_read_zero_of_zero_thetas`: if *both actual*
   bank and Buchstab Theta vanish, the actual selected old-array read
   vanishes without dividing by zero or assuming old arrays vanish.

Only genuinely selected Buchstab and original 106 bank rows enter these
norm estimates; retention is still an exact predecessor read, not a
paid coefficient row. Original `12 Theta_bank` and `5 Theta_Buchstab`
are distinct: no new 17*Theta bank allowance, no duplicate error payment.

## Mathematical boundary — what is NOT paid or proved

The explicit `predecessorAbsMass` is not known here to be at most one,
uniformly bounded in generation, or equal to a manuscript count norm.
The perturbation theorem says nothing about the analytic `w` vector
until the actual manuscript integral/floor/seed consumer is constructed.
No original U3/U4 arithmetic selected-count owner, full/selected/inherited
filter, root weight, six-rejection signed payment, proper/equality/inherit
native-history mass, PP/same-rho, or common 430+11 nested realization
is claimed. Do not infer full CLOSED-CELL induction.

## Frozen dependencies and scope

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes`
commit `ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex` blob
`d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.
Pinned Lean `v4.33.0-rc1`; Mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
No fixed-version changes, no production/CI edits, no changes to P1.4
or P3.6, no default-branch merge, no new axiom or external theorem.
Original c/K, root norm 7/2, row norm 12, real alpha and common-Q
requirements are untouched.

## Validation and next dependency

Actual GitHub source blob and commit are read back. Repository write
permission and distinct h34 branch ownership were checked. At this run
there were zero in-progress GitHub Actions workflows on the repository.
The local environment reports no `lean`, `lake` or `elan` executable,
and no staged dependency-complete source-only import closure.
No Lean/Lake elaboration/compilation, kernel replay, transitive axiom
audit, or finite numerical430 replay took place. The source is
**CANDIDATE ONLY**, never COMPILED; no green status is awarded.

Next: identify the literal preceding feedback table's *correct* bound
from original base/seed/floor data, use the difference estimate against
the *actual* same-Q integral vector (not an arbitrary invented surrogate),
and tie its result into the genuine closed-cell successor inequality
with U3/U4 count owner. Install the original pinned imports in a safe
isolated incremental build and repair any actual Lean errors.

**完整h34稿内证明仍未闭合。**
