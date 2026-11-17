# P1.4 — exact cancellation of the full-q region above N

Baseline confirmed directly from GitHub: `b1774c73dbb3ea2075f7491f34624b62b950cf3e` (centre-prime-capacity packet). Independent continuation: `chatgpt/p1-full87-superN-cancellation-20261118-0415`.

## Manuscript-side mathematical change

This packet is not another renamed Rosser test. It corrects the **scope of separate error payments** after the real signed receiver has been decomposed into four arithmetic pieces. At every **complete** physical modulus `d>N`, the original positive receiver source has zero divisibility fibre. For non-prime N the centre-prime AP correction is also identically zero (the P=N exception would invalidate this if N were prime). Consequently the actual primitive discrepancy is **not** zero on these moduli; instead,

```
primitiveError N d = modulusPrimeTerm N d - primeMass N * densityTest d,  for d>N.
```

These are genuine compensating terms: taking absolute values of the untruncated primitive/density/modulus parts before cancelling d>N can create an artificial payment. The source proves the identity pointwise, then transports its signed above-N version through the **same** original `actualFixedSignedFifthTail` (one `receiverTest N` event population, original parent/history, ordered repeated sixth carrier, original full a*b Rosser PLUS beta and strict high-q test).

Most importantly, it establishes **a bounded full-q four-source stopped identity**, now with `atMostN N` applied to each arithmetic terminal test before its absolute value. The resulting centre correction uses exactly the prior `actualCentreCapacityBudget` **once**. The previous RAW-outside / producer / LICENSED-outside physical bills are unchanged and remain separate. No extra sign assumption or source-recomputed policy was introduced.

This improves the *validity of the error-payment target*: all newly isolated primitive and modulus-prime discrepancies have exact q<=N support. It does **not** prove either signed sum is o(H_N), nor imply the fixed `q<=N^theta, theta<1` and smooth-singleton PP admission. No new numerical saving or completion claim.

## Evidence and verification

- Full Lean candidate: `P4AOriginalFull87SuperNCancellation.lean`, source commit `02091b1ef2dd26380b3e975408e7f5c7fcb034d9`.
- Independent *finite rational diagnostic*: for each non-prime integer `N=2..150` and all `d=N+1..N+25`, direct enumeration of prime prefix, centre AP, receiver fibre, primitive correction and exact totient mean confirmed `receiver=centreAP=0` and `primitiveError=modulusPrimeTerm-primeMass*densityTest`. **2,850 pairs, zero failures**. This does not test the Lean nested-event recursion.
- Runtime `lean --version` / `lake --version` / `elan --version`: all exit **127**, “command not found”. Pinned Lean/mathlib/native dependencies are not present; no compilation was attempted, and source-only import-path staging is still required.
- Status: **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. No kernel replay, transitive axiom audit, saved87 archive replay or independent mathematical review. Candidate may have elaboration or tactic errors.
- New source contains no prohibited proof escape tokens, and the GitHub blob is verified separately. This is not type checking.

## Frozen versions and remaining exact obligations

Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex` blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (re-read this run). Lean `leanprover/lean4:v4.33.0-rc1`; mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`; native `09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000.

Next mathematical step is not another identity. Split the actual **q<=N** primitive discrepancy into `q<=N^theta` and `N^theta<q<=N` with a **fixed** theta and prove a real, same-rho signed bound for the latter before calling registered external PP on the first; separately pay the modulus-prime correction at full q, centre capacity versus H_N, density-to-original ordinary residual integral, and the two independent reserves. Unfiltered sixth BOTH, RAW eighth, actualParent/saved87, rank9 and complete changed/tagged coverage remain open.

There was no CI, no Codex, no update of another branch, no pin change or resource expansion.
