# P1.4: actual rank-five event length and localized sixth high-q tail

Baseline: 9a326cb35cfa683f607bd53d3ad98a9ec96160b3 (the verified previous ordered-sixth-suffix handoff).
Independent branch: chatgpt/p1-full87-fifth-rank-power-tail-20261117.
New source commit: 7f2eedba0bd89297697e6ffb5f5c0cf3864e81bc.
Candidate: P4AOriginalFull87FifthRankPowerTail.lean, blob cee43d5de43903f5c1381aaa832f2ed98381259a.

## Actual mathematical delta

Earlier actual_fifth_exclusive_sixth_modulus_power_bound required an independent premise selectedAfter.length=5. This packet proves the missing premise from the ORIGINAL fifthSixthWithoutBoth producer (structural induction on the same remaining list). In the fifth-BOTH branch, sixthFromBoth cannot be confused with fifthExclusive; for one-sided children the selectedAfter is literally p::pre. At an actual sharedRankFour source, the established rank-four length invariant supplies pre.length=4. Hence every original fifthExclusive occurrence has selectedAfter.length=5, with no assumed field, alternative parent, extra mask, sorting, deduplication, or source replacement.

The same original ordered history then supplies the COMPLETE sixth rough modulus bound without the artificial length premise:
  ((p :: fifth.selectedAfter).prod)^5 <= fifth.selectedAfter.prod^6
for every p in the actual fifth.remainingAfter.

Crucially the high-q bound applies to the FULL modulus a*(p::selected).prod, including original Rosser index a, not just rough factors. A candidate with X < a*b6 necessarily has
  X^5 < a^5*b5^6.
Thus if a^5*b5^6 <= X^5, this exact (a,p) occurrence cannot be high-q. All other (a,p) remain in the SAME original signed physical rho. The result is a precise per-modulus cutoff, NOT a claim that all fifth events or sixth-even tails disappear.

## Verification and limits

SOURCE_ONLY / UNEVALUATED / UNCOMPILED. The environment has no lean, lake, elan commands (each version check exit 127), nor the pinned Mathlib/native module dependency closure. The source blob is recorded and fetched back; no Lean elaboration, kernel replay, transitive axiom check, full original 87-domain archive replay, or independent validation. Candidate may contain elaboration/type errors. No external prime-distribution proof or input was implemented, called, or inferred from this arithmetic.

Manuscript unchanged: UyNewNas/chen-imbalanced-semiprimes at 9731290e8f53cffda44129906cde6a965eaa869b; paper/source/manuscript-body.tex blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79. Lean v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1; native 09b97db5764ade1246bfb77206baa1b124760958; c=49044063/25000000, K=8452171/1250000 unchanged.

## Remaining true obligations

1. Integrate the per-(a,p) small fifth-weight cutoff into the REAL original plus-beta finite high-q sum for each actual fifthExclusive occurrence, using the genuine beta support and no sign/occurrence loss. Keep a^5*b5^6 > X^5 as a signed remainder; obtain actual same-rho quantitative payment instead of pretending it is empty.
2. SixthFromBoth already-sixth terminals require separate complete-modulus support or signed discrepancy estimate. RAW eighth and all physical rho require a genuinely licensed fixed exponent.
3. Fix epsilon/density/compiler reserve compatibility, exact same-rho signed sharp PP and centres/modulus-prime adjustments, ordinary residual integral, weighted actualParent loss, saved87 numerical source certification, rank9/changed/tagged and two independent reserve payments.
4. Compile under exactly the pinned Lean/Lake project toolchain and separately replay kernel, audit transitive axioms and seek independent review. P1.4 remains YELLOW.

No main/master, no merge, no force push, no CI, no Codex, no additional resources.
