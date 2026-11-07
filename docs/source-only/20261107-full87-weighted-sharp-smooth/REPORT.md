# P1.4 — exact original-prime sharp-to-smooth same-rho arithmetic bridge

Predecessor verified HEAD: `6d0b59b01dfde7b561592cf3ab8deb5efb306153`; branch `chatgpt/p1-full87-weighted-sharp-smooth-20261107`. Manuscript is pinned to `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b` / `paper/source/manuscript-body.tex` / blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, lines 739–779, Lemma `lem:current-sharp-prime`. The fixed Lean/mathlib/native toolchain and c,K are unchanged. The preceding packet's entire Lean source, REPORT, REGISTRY, INPUT_BOUNDARY, HANDOFF and native real coefficient/prime definitions were read; applicable AGENTS.md paths were checked and absent.

## Substantive mathematical correction and proof packet

The previous `signedEndpointBoundary` is the sum of two *unweighted signed* fibres, and MUST NOT be mistaken for the sharp-minus-smooth change for a general smoothing weight. This packet uses the genuine window factors `1-W p` for p<N and `-W p` for p>N, with W=1 below N-D, 0≤W≤1; p=N is explicitly excluded.

`P4AOriginalFull87WeightedSharpSmooth.lean` proves candidates:
1. An algebraic EXACT finite sharp-minus-smooth identity, using `chenPrimePrefix (N+D)`, the actual `actualSmallRoughModuli (P false) N cap w z`, and the same `actualSmallRoughRho (P false) N cap w z L`; no auxiliary coefficient and no discarded occurrence.
2. Sharp source identification with the original prefix through N, and with the unsuppressed inclusive prefix when N is nonprime (in particular even N>2).
3. The correct weighted signed boundary has absolute value at most the previous actual lower+upper endpoint invoices, and hence at most `2 Σ_{1≤m≤D}τ(m)` per genuine policy and `4 Στ(m)` for sixth/eighth together.
4. Both gap=0 and D=0 are treated without applying a finite divisor count to zero.

This corrects the previous warning that the same-rho signedEndpointBoundary was not literally a smoothing difference, replacing it with the exact nontrivial weighted identity. It does not infer signed saving monotonicity.

## Checks actually performed
- Independent 3,000-case deterministic finite arithmetic simulation of the actual weighted identity and absolute invoice with randomly signed bounded physical coefficients; 0 counterexamples, including 761 prime-centre, 205 D=0 and 2,630 nonempty-window cases.
- No Lean/Lake executable available here; source is SOURCE_ONLY / UNEVALUATED / UNCOMPILED. No kernel replay, transitive-axiom check, independent review, original saved87 archive evaluation or CI dispatch.

## Remaining exact obligations
The analytic smoothing weight must be shown to satisfy the above support and positivity hypotheses and permitted Euler-derivative budget; the *exact mean* smoothing boundary needs its own control. The permitted signed smooth-original-prime PP must be instantiated on the very same coefficient and bounded squarefree support q≤N^(7/32). The external divisor summatory estimate, prime divisor correction and lower fixed-power trim remain registered but unverified, not invoked. No H_N comparison or reserve payment is claimed. Unresolved: original modulus-prime H_N control; rank9 historical/cubic fees; ordinary integral; sixth filtering; saved87 signed source gain; changed/tagged coverage; two independent reserves and final same-rho assembly. P1.4 YELLOW.
