# P5.6 → h34 — literal two-step policy retention into the actual rank-two frontier

Date: 2026-11-07.
Repository: UyNewNas/goldbach-formalization.
Branch: `chatgpt/p5-h34-request-admission-20261105`.
Verified predecessor HEAD: `3029ce176821dfd43e045d58f15e9666d4b84353`.
Mathematical source commit: `a5b52ac2002d8380297cf4929f4c3314efdc29f7`.
Source blob: `4ab5dcc13ed0134a6432e5bb809a12b40ab084ac`.
Pinned manuscript: UyNewNas/chen-imbalanced-semiprimes@`ba6ec11d800eccc54406490631895e174de85766`,
`paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`.

**PARTIAL_SOURCE_INCREMENT / SOURCE_ONLY / UNCOMPILED / UNEVALUATED / FULL_H34_OPEN**

## What is new

Previous `Part5OriginalH430ActualSecondRosserRetention` linked a prime factor
`ell | q` of the ORIGINAL U3/U4 tagged receiver to two literal
`firstExitNextSelectionCandidates` steps and checked ordinary Rosser
policy at the root's *actual* tag/p-specific `originalPhysicalQ`.
It did not connect those two steps with the recursively scanned
`firstExitDepthFrontier 2`.

New module: `Part5OriginalH430ActualRankTwoFrontierSupport.lean`
(162 lines, 2 public candidate theorem bodies, 2 private helper proof bodies).
The private helper `skip_preserves_frontier` uses the actual skip branch.
`retained_next_lifts_to_frontier` uses the literal enumerator's
before/selected/after decomposition, its exact physical remainder,
the actual policy test, and induction over skipped labels to lift a
continuation into the recursive frontier.

`retained_original_second_in_actual_rank_two_frontier` applies
that transport twice (rank-one selected root, then second rank), starting
with the original roughPrimeUniverse N cap 0 z0. It returns a member of
`firstExitDepthFrontier 2` evaluated with the SAME per-tag/root physical Q.
Its exact prefix is `[ell, arithmeticPrime z]`, its sign is true, and
its actual mass is `1/(p-1) * 1/(ell-1)`, as delivered by the preceding
historical candidate theorem. The state is not duplicated per q.

`original_retained_receipt_rank_two_support` applies that to a genuine
original tagged U3/U4 selected receiver. It retains `ell.Prime`,
`ell | arithmeticQuotientPrime z`, the *original* half-open
`N^a <= ell < p` window, the same actual Q, and the true frontier
state. No arbitrary replacement policy or cross-root common Q occurs.

## Strict mathematical boundary

This implication goes from **actually rank-two-retained original q factor**
to **actual rank-two historical frontier support**. Its converse, the
full/selected/inherited count filtration, actual q-specific owner,
injectivity/capacity, original weighted selected count, and payment of
any original q occurrence remain OPEN. Several original q/tag receipts
may share one historical state, and this packet never multiplies the
historical mass by such multiplicities. An appearance of a frontier
state is not a paid first-exit correction.

Physical z0/phase matching, six non-event rejection lanes, signed
Euler direction, all-action CLOSED-CELL induction, base/switched/seed/floor,
feedback-to-integral/Theta/count, manuscript-local PP/same-rho,
native-history and common 430+11 nested refinement remain OPEN.

Original c/K, root norm 7/2, row norm 12, true alpha, closed nodes,
specified-cell/scalar distinction, original occurrences and payments,
and fixed manuscript remain unchanged. No P1.4/P3.6 or production
files changed. No external analytic proof, target-equivalent assumption,
new axiom, sorry, admit, unsafe escape, toolchain upgrade or CI dispatch.

## Verification and next action

Source uploaded under independent h34 directory. Remote source blob and
git diff must be distinguished from Lean elaboration/kernel replay:
no Lean/Lake executable available locally, no build, no kernel replay,
no transitive axiom audit, no numerical430 or other finite certificate
evaluation, no CI triggered. Finite guards remain **UNEVALUATED**;
no green/formal credit is claimed.

Next: prove the *reverse direction with exact admission and list-position
conditions* only if justified by the actual recursion, then construct
one nonduplicating owner/capacity map from original (tag,p,q) receipts
through full/selected/inherited histories. Preserve every unmatched
original receipt as an explicit unpaid term. Do not reinterpret the
rank-two support as an injective correspondence or payment.

**完整h34稿内证明仍未闭合。**
