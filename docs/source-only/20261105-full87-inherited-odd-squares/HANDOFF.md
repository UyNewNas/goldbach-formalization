# P1.4 — actual post-eight inherited-square elimination, continuation checkpoint

## Immutable recovery navigation
- Base HEAD actually read and compared: 637a97922225749d76cff384a69b9237d8a26c72 on chatgpt/p1-full87-post8-suffix-20261105. Comparison was identical.
- This task's exclusive branch: chatgpt/p1-full87-post8-inherited-squares-20261105. Its source commit: f8d39fb7069b1e235d5943336c748b7265b36b81. Final HEAD must be re-read on recovery.
- New Lean source: P4AOriginalFull87InheritedOddSquares.lean (282 lines, four theorem candidates), install path ImbalancedChen/P4AOriginalFull87InheritedOddSquares.lean. Source Git blob SHA-1 verified by readback: 5707ff92064d9a0ef7824790c5a46532f4112ec2.
- Prior source: docs/source-only/20261105-full87-post8-guards/P4AOriginalFull87Post8GuardExtraction.lean, blob ab3da5050d3b9f44d465bdadc7166f10c5f3e04e; REPORT, REGISTRY, INPUT_BOUNDARY and HANDOFF were read. The prior handoff remains intact.
- Manuscript pin: UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b, paper/source/manuscript-body.tex lines 350–485, blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79 confirmed by GitHub. No replacement of the manuscript.
- Native pinned definition read: subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958, MathlibNt/SieveTheory/LiLiuPrereqWFSmallRosser.lean (UpperAdmissibleSet and upperAdmissible_of_insert_min); no update. Lean v4.33.0-rc1, mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1.
- Original constants remain c=49044063/25000000, K=8452171/1250000.

## Mathematical result and its actual limit

Let S be a finite set of ODD cardinality which passes literal upper square tests at the single frozen real level R, and let p<q<r for EVERY r in S. Set T=S union {q,p}. For each old r, the suffix {x in T:r<=x} is IDENTICAL to its old suffix in S. At q, the suffix has |S|+1 elements (even) and has no upper square test; at p, the suffix is all T (odd). Thus

  UpperAdmissibleSet R T iff (prod T)*p^2 < R.

The least old r0=min S has an active odd test (prod S)*r0^2<R. Since p*q<r0^2, the whole T product is ALSO <R. Both inherited-old-square and total-cutoff disjuncts in the preceding packet are therefore ruled out for a TWO-step extension of a successful odd guard at the SAME level.

For a distinct ordered LIST, the actual ordinary upper policy at odd sign rejects p::q::older iff R <= ((p::q::older).prod)*p^2. This is an actual finite consequence, not an asymptotic mean.

Four candidate theorem names:
1. upper_two_min_insert_iff_last_square — exact old suffixes and both new suffix parities.
2. upper_two_min_total_lt — old minimum square pays the complete product.
3. upper_reject_after_certified_odd_iff_last_square — the literal Boolean ordinary policy, with Nodup ensuring finset/list product agreement.
4. owned87_post8_later_odd_reject_last_square — from real owned87 states, the two actual frozen levels, the post-eight successful trace and a genuine retained leaf, for any correctly ordered prospective double extension.

The fourth statement does NOT claim an arbitrary proposed pair actually occurs as the first rejected branch. Source extraction, order, odd/cardinality, Nodup and actual first-rejection attachment remain proof obligations. A genuine post-eight successful rank-nine odd guard permits its next rank-eleven extension to use this lemma; the rank-nine test itself does not.

## Why rank nine is different

The actual rank-eight prefix was accepted at historical dynamic levels, not necessarily the post-eight frozen level. There is no previous accepted odd frozen-level test before rank nine. The last packet's exact synthetic counterexample remains: ascending set [3,5,1009,1013,1019,1021,1031,1033,1039] at R=158857908555780469977886 passes the total-product cutoff and new 3-square, but fails the inherited 1009-square. That example cannot be used as a previous successful same-level odd guard.

## Tests and validation boundary

A finite exact-integer script checked 59,538 qualifying combinations of an accepted odd-cardinality prior set and two smaller primes from a 15-prime carrier, across boundary levels. All qualifying new total products were below R, and every upper rejection coincided exactly with the new least-prime square: 27,791 rejections and 31,747 acceptances. It also reproduced the rank-nine inherited-square counterexample. These tests are NOT Lean validation, original87 array evaluation, or a proof of the asymptotic.

GitHub readback confirmed the new source blob, 282 lines, four theorem candidates and no forbidden proof escape token. No Lean/Lake build, kernel replay, transitive-axiom check, original87 numerical archive, CI, Codex, workstation, or independent source review was performed: SOURCE_ONLY / UNCOMPILED / UNEVALUATED / formal credit 0.

## Next actions (do not restart or claim more than proved)
1. Derive older.Nodup, Odd older.toFinset.card and p<q<all-older from the ORIGINAL descending rough carrier, genuine selected sublist and post8OddTrace parity. Establish that the real FIRST rejected pair belongs to this traversal. Apply the fourth lemma only for rank eleven or later.
2. Handle rank-nine inherited historical squares separately; either prove the needed level comparisons for actualParent and finiteCap or charge the loss. Do not infer a new-last-square failure unconditionally.
3. Convert literal full-product*p^2 bounds to exact normalized log hprior/hexit/hpair and last-prime reconstruction; continue to the same-source exit-series/integral and actual error/reserve payments.
4. Remaining: primitive/modulus-prime/centre smallness, sixth-filtered signed gain, saved87 original archive binding, changed/tagged coverage, two distinct compiler/density reserves, same-rho assembly and Lean/kernel/independent verification.

No existing source, full-q beta, sign, occurrence count, parent, cap, archive, dependency pin, main/master, other branch or workflow was changed.
