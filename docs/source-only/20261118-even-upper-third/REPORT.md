# P1.4 — even-centre full-q upper-third exact prime switch

## Actual recovery
Baseline: `a2093deb1ac54aa02b3c9f7c918dc3d0590d52be`, branch `chatgpt/p1-full87-upper-half-prime-switch-20261118-0510`. The parent branch was compared with the exact baseline and found identical before a new independent branch was created. Re-read its REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF, complete 252-line source, `ChenInitialPrimeSource.lean`, the original variable-fifth physical ledger and the frozen manuscript. The relevant root/ancestor AGENTS.md paths did not exist.

## Mathematical increment beyond the previous N/2 window
For even N and n in the ORIGINAL target-deleted `chenPrimeReceiverSource N`, we have 0<n<=N and coprime(n,N). For complete d|n with N<3d, write n=kd. Then 1<=k<3. If k=2, 2 divides n and N, contradicting actual coprimality. Hence k=1, n=d.

Thus the ORIGINAL receiver fibre at each such complete d is exactly `{d}` or empty, not merely <=floor(N/d); this extends the former N<2d identity to N<3d for even N. Reindexing retains the exact strict X<d and gives, for every unchanged finite support S and signed weight rho,

```
sum_{d in S, N<3d, X<d} rho(d) R_N(d)
= sum_{P in chenAdditivePrimeCarrier N,
       N-P in S, N<3(N-P), X<N-P} rho(N-P).
```

The actual-physical corollary uses `actualSmallRoughModuli (policy false)` and `actualSmallRoughRho (policy false)` without rebuilding a policy or changing small Rosser beta, rough factors, sign or complete modulus. A second corollary specifically retains `2d<=N`, so **N/3<d<=N/2** is a mathematically new switched slice beyond the last run's N/2<d; `3d=N` stays out, `2d=N` stays in. Both are still exact signed prime sums, not o(H_N) estimates.

This uses the original receiver's arithmetic coprimality, not a geometric-null argument or external PP. It does **not** prove the switched sum small and does not handle N^theta<d<=N/3, or the same-parent full87 actual stopped/ordinary integral bridge. No reserve or outside bill is paid.

## Source and evidence
- `P4AOriginalFull87EvenUpperThird.lean`, new candidate commit `4ee351cb5f56f03e748f1c29743e66d2f10ea5bd`; blob `6738e779c1681884e2f28c7aa22829f9ef138688`, 214 newline-delimited lines; source fetched back from branch. No `sorry`, `admit`, `axiom`, `unsafe` or `native_decide` token found in its static scan.
- Independent exhaustive integer diagnostic: for all even N from 2 through 1000 and every d<=N with N<3d, direct enumeration of the actual prime carrier and receiver divisibility confirms the singleton indicator. **167167 cases, zero failures**. In the newly added N/3<d<=N/2 slice, **6834 nonempty** receiver singleton cases; first at (N,d,P)=(8,3,5). The even hypothesis is material: odd N=11, d=4 has receivers 4 and 8 in the fibre, so the extension cannot be applied to odd N.
- `lean --version`, `lake --version`, `elan --version`: all unavailable, shell status 127. No Lean type check, no source-only import staging, no kernel replay, no axiom audit, no archive replay, no independent review. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; elaboration/proof tactic errors are possible. The imported variable-fifth physical ledger itself is source-only, so the fixed dependency closure must be checked rather than assumed.

## Frozen boundary and next obligation
Manuscript `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`; c=49044063/25000000, K=8452171/1250000. No pins changed.

External signed sharp-prime PP: anchors `eq:current-PP`, `lem:current-sharp-prime`, `eq:current-sharp-pi`, exact original signed physical rho, complete coprime squarefree q<=N^theta with **fixed** theta<1, permitted smooth-singleton endpoint, H_N normalization and original conditions; **REGISTERED_NOT_PROVED_NOT_CALLED**, no callsite. The present N/3<q<=N prime switch is NOT a permitted PP instance.

Next: verify this mathematical extension with correctly staged fixed-version Lean imports if available. More importantly, establish genuine signed control for the newly switched N/3<full q<=N zone at the original RAW-minus-LICENSED coefficients, then handle N^theta<full q<=N/3, without replacing by two unsigned bounds. Other liabilities: full87 actual parent/ordinary integral, primitive/modulus-prime/centre error bills, raw/finite/filtered loss, three physical outside bills, separate compiler and density reserves, unfiltered sixth BOTH, RAW eighth, saved87, rank9 and changed/tagged. P1.4 stays YELLOW.
