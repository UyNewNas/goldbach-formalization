# P1.4 — exact root-to-eighth weighted frontier and physical failed corrections

**SOURCE_ONLY / UNEVALUATED / UNCOMPILED / ZERO KERNEL CREDIT. P1.4 YELLOW.**

## Recovery and fixed material

Baseline: `9a9b03497bcc114d1bd0bea455c77578deae378e` on `chatgpt/p1-full87-physical-failed-weight-20261106` (confirmed identical against the live branch before creating this independent continuation).
Independent branch: `chatgpt/p1-full87-weighted-root-transport-20261106`.
New proof source: `docs/source-only/20261106-full87-weighted-root-transport/P4AOriginalFull87WeightedRootTransport.lean`.
Source commit: `bba40c536659f46398fe753ed155bd4a92fc9c0c`.
Source Git blob: `0afbb97b6f5ba621f7a0c75a8b4868575f5186c7`.

Manuscript remains `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, section 4. Toolchain remains Lean `v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `09b97db5764ade1246bfb77206baa1b124760958`; c=`49044063/25000000`, K=`8452171/1250000`.

## Actual new candidate mathematics

The first theorem is an induction on the **existing** `firstExitDepthFrontier` recursion for any policy, ordered carrier, rank k and finite real prime-weight h. It establishes, with a fixed starting history `pre` and base mass M,

`Frontier(k, policy, h, pre, positive, M * product(h over pre), remaining)`
`= map (mass := M * product(h over actual selectedPrefix)) (Frontier(k, policy, unit, pre, positive, M, remaining))`.

The skip subtree does not multiply mass. The successful select subtree multiplies exactly h(p) and prepends p. Rejections never enter a frontier state; the parent policy and order do not depend on h. The root corollary uses pre=[] and M=1. Equality is of **ordered occurrence lists**, hence it preserves duplicate occurrences, signs, full selected prefix and actual target-deleted remaining suffix.

The next candidate instantiates this at the **actual new licensed-sixth parent** `sixthPolicy`, rank eight, the original `roughPrimeUniverse` and original `ownerAtPrefix`/ `point8 ∈ trim` filter. Because the selector reads selectedPrefix but not mass, it commutes with the state reweighting. The exact result is
`states(..., halfProductDensity, c) = (states(..., unit, c)).map (massReweight halfProductDensity 1)`.
It does not equate the new sixth parent with an older raw sixth parent.

The last candidate combines this state-list equality with the **existing** `correction_eq_failed_attempt_sum`, using the existing actual frozen ordinary continuation level, to express the whole owned eighth-state physical correction as an ordered sum over genuine weighted rejected attempts. Each event starts with the exact eighth-prefix product, and the same recursion multiplies the post-eight successful selections, rejected prime and Euler suffix **once**. It does NOT assert an equivalent statement for the complete root signed physical sieve or a nonnegative signed saving; no deletion factor is inserted here.

Source-only declarations: `massReweight`, `firstExitDepthFrontier_weight_transport`, `root_frontier_weight_transport`, `owned87_weighted_states_transport`, `owned87_weighted_occurrence_mem`, `owned87_physical_correction_eq_actual_failed_sum`. The four latter proof bodies and generic induction are **not Lean checked**. No new axioms/target-equivalent certificate fields.

## Checks and limitations

- GitHub: source file and actual Git blob were read back; content/commits validated, only this proof packet changed. Source static scan for prohibited proof escape constructs and balanced delimiters passed. No AGENTS.md exists at root, docs, docs/source-only, according to actual 404 checks.
- Independent exact Fraction synthetic recursion with fixed seed 20261106: 5,000 cases, 47,043 root frontier occurrences, 27,109 weighted failed attempts, zero mismatches. This checks exact list transport, owner-filter commutation and direct correction/event-sum equality. The test uses synthetic histories, NOT the original archived 87-domain states. An initial test script contained a Python `math.prod` calling error; corrected and then all checks completed. No claim of Lean evaluation.
- Lean/Lake: **NOT RUN**, fixed toolchain not available in this run. No kernel replay, transitive axiom check, CI dispatch, original saved87 archive replay or independent review. Formal contribution to accepted proof: ZERO.
- No edits outside this new packet; no main/master mutation, no forced update, no outside-input implementation, no Codex or local user-machine access.

## Remaining manuscript-internal obligations and next precise move

The root→eighth physical mass transport now has a *candidate proof body*. Next match the exact full owned-state `halfProductDensity` failed correction above to the **same physical g_N signed coefficient** and existing `targetDeletionFactor` inequality from `44731a0`, without multiplying the eighth prefix or charging a deletion twice. This needs a signed event-by-event density difference ledger, not just a cap monotonicity claim. The rank-nine inherited-square loss is separate. Same-source ordinary exit-series/residual integral, primitive/centre/modulus errors, sixth filter, original saved87 archive, full changed/tagged, two reserves and common-rho final assembly all remain unproved.

External ordinary Rosser/PNT-Mertens/PP analytic inputs: registered precisely in INPUT_BOUNDARY.md, UNVERIFIED and NOT IMPLEMENTED/INVOKED.
