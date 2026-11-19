# P1.4 — original reflected-prime Abel transfer (source-only)

Baseline: `541c757da0dcbe437297d840238e331a08386ed4` (the verified reflected-nonprime handoff, original branch unchanged). New branch `chatgpt/p1-full87-reflected-prefix-abel-20261119-1910`.

**Substantive manuscript-internal derivation.** For the ORIGINAL quotient room (R_b), full modulus (b=(p::pre).prod), and original PLUS coefficient (β^+), set (w_b(a)=1_{a\in R_b}β^+(a)), (u_b(a)=1_{N-ab\in chenPrimePrefix(N)}). For any explicit per-full-modulus reference scalar (μ(b)), let (Q_b(k)=\sum_{a<k}(u_b(a)-μ(b))). With **exact quotient endpoint** (m_b=\lfloor N/b\rfloor+1) (using Lean natural division, including the b=0 empty-room case), finite summation by parts gives

```
sum_{a in R_b, reflected prime} beta(a)
 = mu(b) * sum_{a in R_b} beta(a)
   + sum_{t < m_b} (w_b(t)-w_b(t+1))*Q_b(t+1).
```

Consequently the original **reflected nonprime signed complement** is ((1-μ(b))\sum_{a\in R_b}β(a)) MINUS that exact prefix-discrepancy variation term. A separate conditional inequality bounds its absolute magnitude by (E_b V_b), with (V_b=\sum_{t<m_b}|w_b(t)-w_b(t+1)|), requiring the **explicit** prefix condition (∀k≤m_b, |Q_b(k)|≤ E_b). The latter has NOT been supplied or proven: it is a real distinct arithmetic obligation, not an equivalent restatement of the weighted target.

This source further lifts the **finite exact identity** to the SAME actual RAW-only/LICENSED-only signs, the original ordered fifth/sixth List occurrences, original sharedRankFour parent, frozen survivor selector and stopped RAW-minus-LICENSED physical ledger after lower is subtracted once. No geometry-to-arithmetic shortcut, no double reserve, no silent parameter change.

**Verification:** SOURCE_ONLY / UNEVALUATED / UNCOMPILED. The current 4 GiB environment returns 127 for `lean --version`, `lake --version`, `elan --version`; elaboration, kernel replay, transitive axiom check, independent review **not done**. No claim that the source typechecks. A static delimiter/prohibited-token check is not a formal proof. The candidate does **not** prove that (μ) is the right same-ρ AP main term, that (E_b V_b) is affordable relative to (H_N), or that β variation is small; a bare prime-counting mean is not a weighted signed estimate.

Frozen manuscript: `9731290e8f53cffda44129906cde6a965eaa869b`, body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`. Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`, c=49044063/25000000, K=8452171/1250000. No CI/Codex/main writes or expansion.

**Next exact steps:** (1) stage earlier source-only imports at their matching module paths and typecheck the new finite Abel and global signed-List theorems, repairing errors; (2) identify an authenticated same-rho unweighted **primitive reflected AP prefix** theorem for the full actual modulus b and the requested clock/center corrections, if available; (3) calculate genuine β-room variation and event-level signed or absolute budget relative to (H_N); (4) proceed to lower-half correction, ordinary residual integral, saved87 and changed/tagged/rank9 coverage, two independent reserves. P1.4 stays YELLOW.
