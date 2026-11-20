# P1.4 — real-source primitive tail of the actual full87 physical delta

**P1.4 YELLOW; SOURCE_ONLY / UNEVALUATED / UNCOMPILED.**

## Frozen recovery
- Verified prior source-only branch HEAD: `0533d3db49ca2b03404f2970b0875fd9367bc1ac`, from `chatgpt/p1-full87-low-physical-delta-20261120-1710`.
- This independent branch `chatgpt/p1-full87-real-primitive-tail-20261120-1810` was created at that exact commit, preserving all existing packets.
- New source commit: `82fe02b65430b526aac004b3b5b81e7b45e9aac6`, `docs/source-only/20261120-real-primitive-tail/P1Full87RealPrimitiveTail.lean`, Git blob `b7fa205ead36d6cc594b209fe124247ef8cb3e5b` (184 newline-separated lines, including final empty line).
- Manuscript pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, manuscript Blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` (no version change).
- Locked tools: Lean `leanprover/lean4:v4.33.0-rc1`, mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native `subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958`. Parameters c=49044063/25000000 and K=8452171/1250000 unchanged.

## New mathematical candidate
Fix the original RAW and LICENSED strategies R,S, identical (N,cap,w,z,L), and physical carrier
`Q = actualSmallRoughModuli (S false) ... ∪ actualSmallRoughModuli (R false) ...`.
Use the **actual** support-zero-extended coefficient `rho = trueDDeltaRho (R false) (S false) N cap w z L`.
Under `1 ≤ w`, previous source-only lemma gives `d < w^5 → rho d = 0`. Define `Qhi = Q.filter (fun d => w^5 ≤ (d:ℝ))`; this is a **zero-coefficient reindexing**, not a new sieve or branch mask.

1. `actual_full87_real_primitive_three_books_high_only` supplies exact finite equalities for the original real-source `physicalDensitySum`, `realPhysicalCoprimeCorrection`, and `realPhysicalDistributionError` when Q is replaced by Qhi **only for rho**.
2. For that SAME original delta, the signed real-source primitive distribution error obeys
   `|E(Q,rho)| ≤ ∑ d∈Qhi |realHalfProductCongruenceMass(b,N,T,d) - realHalfProductCoprimeMass(b,N,T,d)/phi(d)|`.
   The coefficient factor is **one**, by the previously authored actual delta unit bound. This is a finite absolute invoice, NOT an o(H_N) estimate.
3. `actual_full87_real_receiver_high_three_books` identifies the full unfiltered real half-product receiver sum of `physicalDivisorSum Q rho (N-m)` with the original source cardinality times the Qhi density, plus Qhi coprime correction and Qhi signed primitive discrepancy. This keeps a single real source, same actual delta and no duplicated low-d payment.

Both public theorem statements are actual original-policy instances; the one private helper proves finite zero-tail reindexing. Neither RAW nor LICENSED alone is truncated and no positive-majorant implication for signed rho is asserted. The strict cutoff `d < w^5` is unchanged; equality is allowed in Qhi. No new analytic hypothesis, axiom, sorry, admit, native_decide or unsafe escape.

## Remaining mathematical obligations
- Existing fifth-factor, true-d unit-bound, and low-d vanishing antecedents are themselves **UNCOMPILED SOURCE_ONLY**; no theorem here removes their transitive risk.
- Authenticate final frozen full87 compiler epsilon, `w=N^(epsilon^2)`, z,L, cap and true physical `rho_N` at the actual source. The separate compact third-family installation does not establish this.
- Prove causal signed PP licence for the final LICENSED rho and common smooth `W_N`; do not license this delta merely by unit size.
- Estimate the **same** Qhi primitive discrepancy invoice relative to H_N, including allowed coefficient class, source smoothing and modulus-prime effects. Exact cancellation of low terms does not bound the high tail.
- Reconcile rank5/7/9/+ first disagreement with actual 87 owner occurrences, raw/finite/filtered changed/tagged, BOTH/inherited and common dynamic parents.
- Pay stopped events, net outside, producer ledger, lower-half and ordinary residual-integral conversion; authenticate saved87 numerical geometry and separate compiler/density reserves. No double payment.

## Actual verification
- Remote GitHub source Blob re-read at source commit: `b7fa205ead36d6cc594b209fe124247ef8cb3e5b`. Static forbidden escape scan: negative. These are SOURCE_ONLY checks.
- `lean --version` exit 127, `lake --version` exit 127, `elan --version` exit 127 (command not found). Current cgroup `memory.max=4294967296` bytes. No matching toolchain available, no Lean type checking performed. The source-only dependencies are not staged as importable `ImbalancedChen` modules.
- Status: **UNEVALUATED / UNCOMPILED**, no kernel replay, no transitive axioms audit, no independent review, no CI dispatch, no Codex, no main/master modification, no force-push and no additional resource allocation.
