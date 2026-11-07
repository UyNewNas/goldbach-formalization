# P1.4 — true pinned singleton PP mean and one-time original-prime endpoint invoice

Baseline HEAD: 51fc6058737df85700b62e027685176fdbf8ff6d, predecessor packet docs/source-only/20261107-full87-weighted-primitive-recentering. New branch: chatgpt/p1-full87-true-singleton-pp-20261107. Pinned manuscript 9731290; eq:current-PP lines 258-278 and lem:current-sharp-prime lines 742-779; no toolchain/constant changes.

## Nontrivial manuscript identification

The pinned manuscript **defines** X_W^(q) = sum over (p1...pk,q)=1 of W_N(p1,...,pk). Thus for singleton k=1, in the exact source universe S = chenPrimePrefix(N+D), X_W^(q) equals finiteCoprimeMass S W q. Previous arbitrary-X comparison theorem correctly retained T_W-X(q), but under the manuscript's actual definition T_W-X_W^(q) = weightedModulusPrimeMass (already proved by the previous weighted mass partition). The modulus-prime correction cancels, not by claiming either charge is negligible, but algebraically and on the same real signed rho.

New source P4AOriginalFull87TrueSingletonPPMean.lean includes:
1. original_smooth_true_singleton_PP_remainder: literal actual originalSmoothLiteral minus signed coprime X_W^(q)/phi(q) equals the SAME full-q signed finitePrimitiveDiscrepancy.
2. original_sharp_true_singleton_PP_exact: combine with the old true sharp/smooth formula, preserving (1-W) lower endpoint and minus W upper endpoint, no duplicated endpoint payment.
3. original_sharp_true_singleton_PP_invoice: when W is interior-one and [0,1], absolute sharp-minus-coprime-mean error is bounded by the actual signed primitive remainder plus the same two endpoint invoices.

The equalities remain at one real N,D,cap,w,z,L and the same P false physical modulus/rho. No unrelated sieve is subtracted. The original fixed two policies may each instantiate P; this source does NOT claim a new global population theorem.

## Verification

Internal exact Fraction independent arithmetic: 1,200 cases of smooth minus coprime mean = signed primitive remainder (random signed rho, signed W, varying full moduli including zero), 0 mismatches; 1,500 cases of sharp-coprime equality and invoice (interior-one W in [0,1], mixed-sign rho), 0 mismatches. These tests do not execute Lean proof terms or authenticate actual saved87 values.

Static source contains no prohibited escape constructs. Git blob, branch HEAD and proof packet are to be read back from GitHub after commit. Status: SOURCE_ONLY / UNEVALUATED / UNCOMPILED, zero kernel acceptance. No Lean/Lake, CI dispatch, kernel replay, axiom audit, independent review, Codex, user workstation, or saved87 replay.

## Still open

Gevrey singleton W and exact prime support; fixed derivative orders and signed PP permission; actual original q positivity, coprime/squarefree, q cutoff; smooth coprime mean to sharp pi(N) density boundary and centre deletion; finite endpoint divisor-sum asymptotic; low prime trim; actual rank9 weighted historical/cubic fees; ordinary residual; sixth filtration; saved87 original geometry/numerics; changed/tagged; two independent reserves and same-rho final assembly. P1.4 stays YELLOW.

NEXT concrete action: prove the actual lower/upper endpoint *coprime mean boundary* for the physical support using the pinned W and the already-known rho absolute one-bound, then independently verify the q-support permissions; do not reintroduce a fictional free X(q) mismatch.
