# P1.4 — actual PLUS-beta full-modulus power-filter integration

Baseline: `288de02a8edb1d046e84c462a1a83c0d2b8e0a99` on `chatgpt/p1-full87-fifth-rank-power-tail-20261117`.
Task branch: `chatgpt/p1-full87-plus-beta-power-filter-20261117`.
New source commit: `6e695155b47a36cb91a737f22a9a7fd716a741c7`.
New source: `P4AOriginalFull87PlusBetaPowerFilter.lean`, Git blob `7fb58d445854672e15c8ff05fd07883f7e6f630f`.

## Actual mathematical change

Previous source proves for every actual fifthExclusive occurrence and every actual sixth candidate `p ∈ fifth.remainingAfter`:

`X < a * (p :: fifth.selectedAfter).prod → X^5 < a^5 * fifth.selectedAfter.prod^6`.

This packet uses that *same* proof to remove exactly zero summands from the ORIGINAL `attachedLeafTest N cap 1 w L (highQTest X F) true (p :: fifth.selectedAfter)`. The retained index set is the original `actualSmallRosserSupport N cap w`, filtered by the STRICT inequality `X^5 < a^5 * fifth.selectedAfter.prod^6`.

The theorem `actual_fifth_plus_attachment_eq_large` is a finite `Finset.sum_filter` identity. Excluded terms have `a^5*b5^6 ≤ X^5`, which forces `¬ X < a*b6`; the original highQTest is then exactly zero. The PLUS-beta value, complete modulus `a*b6`, strict cutoff endpoint, original prime `p`, coefficient sign, and each genuine Rosser index are unchanged.

`actual_fifth_sixth_continuation_eq_large` transports this reduction through the real post-fifth ordered `List.map` for any original policy. It preserves true sixth-gate admission, signedTreeCoefficient and original fifth.massAfter. `actual_fifth_one_sided_value_eq_large` retains the RAW-only positive and LICENSED-only negative assignment separately; the fifth-BOTH branch is unchanged.

`actual_one_sided_event_value_eq_large` and `actual_one_sided_event_map_eq_large` apply it to the existing `actualFifthSixthWithoutBoth` producer. Genuine `sixthFromBoth` events are *not* given the fifth mask and are left exactly as before. The map equality permits `g=id` and `g=abs` without deduplicating List occurrences. The large `a^5*b5^6 > X^5` remainder remains in the original signed high-q sum; NO numerical reserve was paid.

This is the first literal PLUS-beta finite-support filter based on the actual fifth-power inequality, not a new producer, coefficient, parent, geometry argument, or PP estimate.

## Verification, scope, and limits

- GitHub source blob remotely fetched and matched `7fb58d445854672e15c8ff05fd07883f7e6f630f`. Five candidate theorems with explicit proof bodies; no forbidden proof escape tokens found in this file.
- SOURCE_ONLY / UNEVALUATED / UNCOMPILED. In this execution environment `lean --version`, `lake --version`, and `elan --version` all exited 127 (command not found), and pinned dependencies are not available; no Lean elaboration or type-check was performed. Therefore the candidate may contain Lean syntax, elaboration, or proof errors. A static scan and remote hash are NOT kernel validation.
- No test of the full 87-domain original numerical archive. No kernel replay, transitive axiom audit, independent mathematical review or CI.
- No new axioms, large external numerical foundations, Codex, changes to main/master, merge, or force push.

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`; `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Fixed Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. c=49044063/25000000, K=8452171/1250000 unchanged.

## Remaining precise manuscript obligations

1. Apply the equal original event maps directly to `actualSixthOnlyExclusiveAbsInvoice` and stopped signed delta under the existing frozen epsilon/X hypotheses, without counting outside/producer/receiver bills again.
2. Obtain an actual *quantitative* same-rho estimate for retained fifthExclusive large-weight indices `X^5 < a^5*b5^6`; this file does not make their values small or vanish.
3. Address unmodified `sixthFromBoth` complete-modulus high-q terminal contributions, RAW eighth, and every physical-rho modulus inside a common licensed fixed theta.
4. Reconcile small-Rosser epsilon, compiler/density reserves, exact prime PP input, centre/modulus-prime corrections, ordinary integral, weighted actualParent, saved87 certificate, rank9/changed/tagged, and two independently paid reserves.
5. Pinned Lean/Lake compilation, kernel replay, transitive axiom audit, independent validation. P1.4 remains YELLOW.

The next actionable proof is the signed and absolute invoice substitution on the same existing source List; do not confuse this finite identity with a paid analytic tail bound.
