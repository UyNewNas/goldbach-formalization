# P1.4 — weighted original-prime primitive recentering on the actual full-beta rho

**Verified predecessor:** 37a469f35d6f7a0d0d9e30d1b50347edf576e37a, branch chatgpt/p1-full87-weighted-sharp-smooth-20261107. **This packet:** chatgpt/p1-full87-weighted-primitive-recenter-20261107.

**Pinned manuscript:** UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b; paper/source/manuscript-body.tex; Git blob d529bea2ecfcc74d64fc1664ac770a3becaa7c79; \`eq:current-PP\` (lines 258–278) and \`lem:current-sharp-prime\` (742–779). Pins and c=49044063/25000000, K=8452171/1250000 unchanged.

## New manuscript-internal candidate proofs

* \`P4AOriginalFull87WeightedPrimitiveRecentering.lean\` (187 lines; source commit 64090382f7289bf101b60264f7d1ae392cedbd1d): the **weighted** full-prime coprime mass equals full weighted prime mass minus the *actual weighted prime divisors of d*, including signed W and the d=0 Lean convention. For nonprime centre N, the previous packet's \`originalSmoothLiteral\` is converted to a weighted AP sum with the same \`actualSmallRoughModuli (P false)\` and \`actualSmallRoughRho (P false)\`, frozen outside the prime summation. This yields
  \[
  S_W-T_W\sum_{d\in Q_P}\rho_P(d)/\varphi(d)
  =\sum_{d\in Q_P}\rho_P(d)\,\mathrm{PrimitiveDisc}_W(N,d)
   -\sum_{d\in Q_P}\rho_P(d)\,\mathrm{ModPrimeMass}_W(d)/\varphi(d).
  \]
  The correction has the **negative sign** and retains full modulus, coefficient, and the original prime prefix, including primes dividing the centre N (except nonprime p=N).
* \`P4AOriginalFull87WeightedModulusMeanBridge.lean\` (71 lines; source commit 7c5bae88b525f8dae07dafd203cadba637150def): **crucial q-dependent analytic-main-term distinction**. For an arbitrary profile X(d), the same finite identity is
  \[
  S_W-\sum_{d\in Q_P}\rho_P(d)X(d)/\varphi(d)
  =\sum_d\rho_P(d)\,\mathrm{PrimitiveDisc}_W
   -\sum_d\rho_P(d)\,\mathrm{ModPrimeMass}_W(d)/\varphi(d)
   +\sum_d\rho_P(d)(T_W-X(d))/\varphi(d).
  \]
  The last term is a genuine **unpaid** difference, not a definition made equal to zero. This prevents confusing the manuscript's \(X_W^{(q)}\) with the finite **prime** mass \(T_W=\sum_{p\in\mathrm{prefix}}W(p)\).

This is not a new abstract policy, PP assumption, Gevrey supplier, or equivalent-to-the-target structure field. It is a finite algebraic identification for the existing physical coefficient; sixth/eighth are obtained by the original \`sixthPolicy\` and \`policy\` parameters, with no change in their definition. The actual 87-history arithmetic distribution is still open.

## Actual checks

* GitHub source files created and independently fetched; matching blobs b50d3ed4e53b3b5789d24c1e579b2a7bb5d57b1e and 6fe828004568a0f0a9ff2ad41822f3c97b4d1ee1.
* 5,000 exact rational synthetic cases, with random signed physical rho, arbitrary rational W (including negative), random modulus-specific X, nonprime N and full modulus carriers including 0; zero counterexamples. One test run: D=0 in 184 cases, modulus 0 in 868 cases, mixed-sign rho in 4,216 cases. This validates the mathematical arithmetic identities under those synthetic cases only, not actual saved87.
* Static forbidden-construct scan: no \`sorry\`, \`admit\`, \`axiom\`, \`native_decide\`, or \`unsafe\`; delimiter check passed.
* **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**. No Lean/Lake available and source-only module imports are not project-installed. NO kernel replay, transitive-axiom check, independent review, saved87 replay or CI. Zero formal acceptance credit.

## Exact remaining proof obligations

1. Construct/identify the actual manuscript Gevrey singleton W, prove support/nonnegativity and permitted Euler derivatives at \(\delta=(\log N)^{-B}\) with fixed B>A+3; previous weighted sharp/smooth packet still needs this.
2. Identify the PP analytic **q-dependent** mean \(X_W^{(q)}\) and prove a true bound for \(\sum_d \rho_P(d)(T_W-X_W^{(d)})/\varphi(d)\), not its disappearance. Where the PP's own normalization differs from a prime-sampled T_W, retain the genuine analytic mean-boundary term.
3. Invoke the previously licensed smooth singleton signed PP *only after* checking actual q≤N^(7/32), squarefree, (q,N)=1, supported policy and frozen same rho; no external result reproved here.
4. Control weighted modulus-prime correction and central p|N source deletion, primitive discrepancy and sharp/smooth mean error relative to H_N with fixed parameters then N→∞.
5. Rank9 historical/cubic fees, ordinary residual integral, sixth filtering, saved87 full-source numerical gain, changed/tagged, two separately funded compiler/density reserves and final same-rho assembly remain YELLOW.

No new axiom, admitted lemma, analytic theorem, asymptotic payment, or P1.4 closure is claimed.
