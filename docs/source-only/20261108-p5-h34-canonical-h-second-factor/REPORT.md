# P5.6 → h34 — one genuine retained h-stage second choice per original q receipt

UTC: 2026-11-08. **PARTIAL_SOURCE_INCREMENT / FULL_H34_OPEN / SOURCE_ONLY / UNCOMPILED / UNEVALUATED**.

- Repository/branch: `UyNewNas/goldbach-formalization`, `chatgpt/p5-h34-request-admission-20261105`.
- Verified previous head: `8fe4f8bab905974539ace2f5c8658d0c59ffd109`; mathematics source commit: `d0d5f2139a94f500a2cfacde75166e53315986dd`.
- New source: `Part5OriginalH430CanonicalHSecondFactor.lean`, 216 lines, 7 theorem proof candidates, 4 definitions. Git blob: `b674a36c3f4cb7c5ee58d699d226e0f3c564951f`.
- Fixed manuscript: `UyNewNas/chen-imbalanced-semiprimes@ba6ec11d800eccc54406490631895e174de85766`, `paper/source/manuscript-body.tex` (blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`). Pinned Lean v4.33.0-rc1 / Mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.

## New manuscript-INTERNAL proof candidate scope

The predecessor `8b138bb` identified original U3/U4 q/tag h-start rank-two candidates, but even an admitted q can have **multiple** prime factors ell<p. Naively summing its retained prime-factor candidates would repeat the ORIGINAL q count. This packet constructs a unique deterministic candidate **per original q receipt** from actual retained Rosser factors, while preserving the original U3/U4 tag, p, q, phase, and tag-specific physical Q.

1. `hRetainedFactors` is the *actual* finite set of ell<p prime divisors of this q passing `retainedOriginalSecond` for the literal ordinary lower h-start. `mem_h_retained_factors_iff` derives the finiteness cutoff from the real second-stage policy; it does not assume a new owner.
2. `h_retained_factors_nonempty_iff` identifies this nonempty finite set with the existing exact `hasRetainedOriginalSecond` q predicate.
3. `canonicalHSecond` uses the finite minimum only when nonempty; `canonical_h_second_mem` proves that every charged choice really belongs to the actual retained-factor set. There is no value-based fallback used to pay any q.
4. `hCanonicalReceipts` retains precisely original h-stage q/tag receipts with at least one actual retained factor. `hCanonicalPairs` associates **one** canonical ell with each such original receipt. `h_canonical_pairs_count_exact` proves equality of pair and q-receipt cardinalities.
5. `h_canonical_pairs_signed_exact` proves the same **without cancellations** for arbitrary original q/tag-dependent real signed weights, including overlapping root bands. There is no double count of one q with several retained second factors.
6. `h_canonical_pair_valid` checks actual divisibility, primality and the second Rosser predicate at the correct physical Q. `h_canonical_pair_literal_window` maintains the actual conditional lower h-start window **N^a ≤ ell < p < N^h**, and the literal Rosser prefix `[ell,p]`.

The proof candidate does **not** say different original q/tag receipts yield different historical `(Q,p,ell)` events. A given event can still be selected by many distinct q. Thus even this one-per-q allocation does not establish an injective **q-to-history** owner, event payment, full/selected/inherited gate, correct root count weight or a sign bound on any Euler correction.

## Frozen manuscript owner check — boundary, not a new premise

The pinned manuscript `manuscript-body.tex` (around lines 690–715 and 879–900) distinguishes ordinary **lower** trees beginning at `w=a,h` from **upper** U3/U4 selected costs using `H_430(max(2,L/a))` in the enhanced range. Consequently the lower `h` stage in this file **must not** be substituted as the true U3/U4 upper-count owner. The projection presieve `z0=N^omega` is separately symbolic. This is a genuine unresolved object/phase match, not an excuse to move the manuscript's own source obligations to the external list.

## Still unpaid manuscript-INTERNAL obligations

1. Find and instantiate real U3/U4 upper H430 count stage, root Q and root weights, actual physical z0 and upper/lower policy; identify exact `full/selected/inherited` owner and complete reject/carrier lanes. The new canonical receipt pairing does not solve this.
2. Prove **across q and tags** distinct/chargeable historical events or retain exact collision surpluses, original occurrences and true signed Euler suffix/payable amount. A one-per-q factor choice is weaker than one-per-event payment.
3. Bound high-cutoff, p-rough, root-policy, Rosser-failed, erased, same-key multiple q/tag, frozen-only and other discrepancy lanes with correct signs; preserve explicit arithmetic vs historical mass gap.
4. Close the actual request-level all-action CLOSED-CELL count induction, bank/base/switched/seed/floor, feedback to integrals/Theta/count and manuscript-local PP/same-rho compatibility.
5. Native history proper/equality/inherit mass, simultaneous outer count and one common 430+11 nested causal refinement at original c/K, root norm 7/2 and row norm 12.

## Engineering, scope and validation

The mathematics source was committed alone as `d0d5f2139a94f500a2cfacde75166e53315986dd` and its blob/diff was read back. It added 216 lines to **one** new file (0 deletions), with 7 candidate theorem declarations and 4 definitions. Static forbidden-proof-token scan passed. Those checks are **not** Lean parsing, elaboration, compilation or kernel checking.

No Lean/Lake on the available execution PATH. **NOT RUN:** Lean elaboration/compilation, kernel replay, transitive-axiom audit, independent verification, numerical430 certificate replay or CI. Finite certification remains **UNEVALUATED**, formal green credit zero. No new external theorem, custom axiom, sorry, admit, unsafe/native escape, target-equivalent hypothesis, toolchain upgrade, manuscript revision, CI dispatch or CI configuration change. P1.4/P3.6 and all earlier packets remain untouched.

**NEXT:** trace the actual U3/U4 upper H430 owner and selected-count phase from the frozen manuscript and existing formalized count consumer. Use the canonical h-stage source only when the genuine stage agrees; otherwise retain the h-stage as a conditional diagnostic. Do NOT create another abstract owner/filter, nor infer upper payment from the present cardinal identity.

**完整 h34 稿内证明仍未闭合。**
