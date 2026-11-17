# P5.6 → h34 — actual CLOSED-CELL positive debt: fixed-cell slack versus same-Q dynamic ideal

Date: 2026-11-18 (Asia/Shanghai). Dedicated branch: `chatgpt/p5-h34-full-tagged-actual-fin-20261112`.

Verified predecessor HEAD: `c1a1f4942d1e89293d42065f5d9be1add51e7b8f`.
Mathematical source commit: `61c9dd0ca568467ca08a5cfaf027853e6f0f98ca`.
Source: `Part5OriginalH430ClosedCellIdealSplit.lean` (291 lines; 5 definitions and 8 theorem candidates, including one private helper). Git blob `c446b48a57d8e9b266a0993c5ea388bef215ca3d`.

Pinned manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`.
Lean `v4.33.0-rc1`; Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN.** None of the new declarations has been checked by the Lean kernel.

## Concrete new manuscript-internal argument

The predecessor packet `Part5OriginalH430ClosedCellPositivePrefloor` bounds the real selected-bank pre-floor positive gap by the original W1/W2 CLOSED-CELL fixed-reference envelope, but it did not separate the new fixed-reference surplus from the ideal dynamic integral component.

The pinned `cellReadIdeal_split` and `readFixed_value` yield the signed exact identity, for each genuine original action and any signed previous arrays:

`idealCellProfile(H,h,a) = fixedValue(H,a) + dynamicIdealProfile(H,h,a)`.

Here `dynamicIdealProfile` uses the existing `dynamicIdeal` coefficients (the original strict-prime integral row); no changed 4:1 weights, scalar owner, prime rho or Q is introduced.

Define at the actual previous generation `g`:

- `A_g(a) = baseValue(a) + idealFeedbackValue(iterate g,a) - dynamicIdealProfile(precedingH g,precedingh g,a)`.
- `S_g(a,F) = fixedReference(F,a) - fixedValue(precedingH g,a)`.

The exact selected-bank CLOSED-CELL pre-floor atom is now `theta_g(l) * (A_g(a) + S_g(a,F))`, at the original `Fin` occurrence `l`. The explicit predecessor hypothesis `floorValue (iterate g true) i ≤ F s` on every `queryCell i` implies `S_g(a,F) ≥ 0`; it does NOT imply `S_g=0` or pay its mass.

With true nonnegative same-Q parent theta and original positive marks, the clipped positive-part sandwich is:

`B_g^ideal ≤ B_g^closed(F) ≤ B_g^ideal + B_g^fixed-slack(F)`.

This is both a valid pointwise upper bound and a useful *lower* obstruction: predecessor CLOSED-CELL substitution can increase, not erase, the real positive gap. The surviving fixed-slack mass is explicitly nonnegative and charged once for every winning 106-bank list position. The proof candidate reuses the existing rootHistory admission chain rather than inventing arbitrary positive weights.

Finally `frozen_root_le_ideal_balance_plus_fixed_slack` inserts the upper sandwich into the previous TRUE root 430-generation consumer. It retains the zero-generation seed, actual Buchstab positive source, original applied bank absolute error, and capped feedback floor credit **on the left**. No true U3/U4 selected-count source identification, seed/base/PP or numeric budget is claimed.

## File ownership, rules, remote evidence

Authenticated repository owner had push permission. The dedicated branch HEAD was checked at `c1a1f4942d1e89293d42065f5d9be1add51e7b8f` immediately before source mutation; no h34 Actions job was in progress. Another *unrelated* P4 Actions job was in progress, so no CI configuration, workflow or shared file was touched. A new task-owned source-only file was committed using a Git tree and non-force branch update with expected prior SHA, then fetched again: source blob `c446b48a57d8e9b266a0993c5ea388bef215ca3d`; compare from `c1a1f4942d1e89293d42065f5d9be1add51e7b8f` to `61c9dd0ca568467ca08a5cfaf027853e6f0f98ca` reports precisely one newly added 291-line Lean file (ahead 1 / behind 0).

The local execution container has `git` but no `lean`, `lake`, or `elan`, and `git ls-remote` could not resolve `github.com`. The pinned source-only import closure is not staged in the container. The GitHub connector performs repository reads/writes but cannot compile Lean or dispatch a targeted Actions run. **No Lean/Lake compilation was attempted successfully, no kernel replay, no transitive axioms audit, and no numerical finite replay.** Token scan, actual Git blob readback, and comparison do **not** imply formal verification; no green node.

The original manuscript version, c/K, root norm 7/2, row norm 12, same-Q, actual alpha, selected-cell/scalar distinction, literal Q80 divisions, repeated owner/payment occurrences, and 430+11 levels were left unchanged. No `sorry`, `admit`, custom axiom, `unsafe`, external-number-theory theorem implementation, force push or main-branch merge. P1.4, P3.6 and CI settings were untouched.

## Remaining manuscript-internal obligations

1. Quantitatively pay **both** the selected positive analytic base + unrounded feedback − true same-Q dynamic ideal gap `B_g^ideal` and the **nonnegative original W1/W2 fixed slack** `B_g^fixed-slack`. Neither is bounded by the already established applied-error epsilon-Theta. The LOWER sandwich explicitly prohibits silently deleting the fixed slack.
2. Establish predecessor CLOSED-CELL hypothesis through authentic base, fixed, switched, seed, full Q80 floors and all-action arithmetic induction, rather than importing it as a final licence.
3. Pay actual winning Buchstab strict-prime positive physical sources and zero-generation seed with true chosen predecessors; keep applied error and capped floor credit in their mathematically correct direction.
4. Identify the whole original U3/U4 owner-weighted (root norm 7/2) full/selected/inherited count source, genuine q/tag multiplicities, rejections, signed Euler/native-history, PP/same-rho, outer integral–Theta–count and ONE common nested 430+11 causal refinement.
5. Reconstruct the pinned source-only import closure and compile the new module and direct dependencies. Repair any actual errors, then kernel replay, transitive axiom audit and finite guards. Do not mark green before actual success.

**Next:** search the pinned analytic same-Q/dynamic ideal source for a pointwise positive upper under the original q/tag and seed quantifiers; separately bound the W1/W2 fixed slack in terms of the *actual* predecessor floor/seed growth. Do not reuse signed aggregate cancellation as a bound on positive parts.

**完整h34稿内证明仍未闭合。**
