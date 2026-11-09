# P1.4 — true signed-W low-q weighted Gram and Cauchy invoice

## Recovery
Recovered last confirmed HEAD **d23b2b5728ba6b54351209ce715d106e60b3da4a** on `chatgpt/p1-full87-lowq-signed-gram-20261109`. Read the previous HANDOFF, REPORT, REGISTRY, INPUT_BOUNDARY and complete 113-line unweighted Gram source, its full predecessor primewise source, the original 20261105 eighth owner arithmetic and signed source helper, ChenInitialPrimeSource, archive source-index and cell-indexed weight reports. Root/docs/docs-source-only/ImbalancedChen AGENTS paths were checked and did not exist. The new task's independent branch is `chatgpt/p1-full87-weighted-gram-prime-cost-20261109`; GitHub commit must be verified after publication, not presumed.

Frozen manuscript: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`, `paper/source/manuscript-body.tex`, blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; inspected lines 400–485. Project `lean-toolchain` is leanprover/lean4:v4.33.0-rc1; mathlib e4c91783ca8e6a7c693ae624ade32fd22d4e43c1, native subfish-zhou/goldbach-lean@09b97db5764ade1246bfb77206baa1b124760958; c=49044063/25000000 and K=8452171/1250000 unchanged.

## Genuine missing step now represented in candidate proof
The previous original low-q Gram was **unweighted** `sum_p k(p)^2`; the actual original signed error is `E_low=sum_p W(p) k(p)`, with no assumed nonnegativity of W. Reusing the SAME original RAW/LICENSED complete-q physical coefficients `A(d)=supportedPhysicalRho_RAW(d)-supportedPhysicalRho_LICENSED(d)`, original `Q=pairActualLowQModuli` containing **d=X**, original `T=chenPrimePrefix(N+D)`, and original one-prime contrast `kappa_N(p,d)`, let `k(p)=sum_(d∈Q) A(d)kappa_N(p,d)`.

The new `P4AOriginalFull87LowQWeightedGramInvoice.lean` (212 LF lines; Git blob **561e9be6a7dd91d928979a851f7fee44df8ffdc7**) proves two linked SOURCE_ONLY candidate statements:

```
G_W := sum_(p∈T) |W(p)| * k(p)^2
    = sum_(d,f∈Q) A(d) A(f) sum_(p∈T) |W(p)| kappa(p,d) kappa(p,f)
E_low^2 <= (sum_(p∈T) |W(p)|) * G_W.
```

The proof is finite: it proves the explicit pairwise-variance identity `sum_(p,q) lambda(p)lambda(q)(u(p)-u(q))^2 = 2(M*G-L^2)`, applies nonnegative `lambda=|W|`, then a triangle inequality allowing **signed W**. No covariance field, fake PP bound, independence or favorable cross-correlations are postulated. Off-diagonal terms may be negative; only the full weighted Gram is nonnegative. It is an **alternative** to previous low-q B(d)C_W(d) or primewise L1 invoices, never an extra reserve.

The gain over the last packet is precisely that its unweighted second moment can no longer be mistaken for the weighted norm controlling the actual PP invoice. It does **not** establish `G_W=o(H_N^2/sum|W|)`, a real saved87 numerical saving, or a legal analytic PP cutoff.

## Actual checks
- `python3 CHECK_SYNTHETIC.py`: **1,800** exact Fraction synthetic cases, **0** algebraic counterexamples; **1,516** cases with negative W, **890** with negative off-diagonal weighted total, **1,453** strict Cauchy cases, **1,159** with d=1. Synthetic coefficients and prime sets are NOT original saved87 replay.
- Candidate source hash: Git blob **561e9be6a7dd91d928979a851f7fee44df8ffdc7**, SHA-256 `da856db6ef95858dd7b6db8acc1fa09d6e2d4546ca2a83ad6e1854471a10c09e`; no sorry/admit/native_decide/unsafe. Static checks are NOT Lean elaboration.
- `lean --version`, `lake --version`, `elan --version` each exited **127** (`command not found`). No local pinned toolchain/closure; container Git external DNS failed. **SOURCE_ONLY / UNEVALUATED / UNCOMPILED**; no kernel replay, transitive axiom audit or independent review.
- No CI/Actions dispatch, Codex, pin upgrade, external analytical proof, forced push, main/master mutation or extra compute.

## Exact remaining yellow obligations
1. Authenticate an actual individual saved87 **geometric** witness (source polygon/affine inequalities) and actual N-dependent `Source c`, `states`, dynamic `actualParent`, shared history and original signed selected/ordinary integral/gain. Archive label and rational-total transport is not physical authentication; source reports explicitly identify missing raw witness files.
2. Obtain a TRUE same-`H_N` quantitative upper bound for the original `|W|`-weighted Gram or select one previous positive budget as alternative. Do not discard signed cross terms or double-pay.
3. Verify actual Gevrey W_N, valid integer PP X, fixed-before-N parameters, original licensed full-q family; external §4 PP stays REGISTERED_NOT_PROVED / NOT_CALLED.
4. Pay high-q producer, stopped and five-frontier, raw/finite/filtered, ordinary, rank9, changed/tagged, centre/endpoints and independent compiler/density reserves once each.
5. Stage the exact fixed source-only import graph in the pinned Lean toolchain; targeted Lake/Lean type-check, separate kernel replay, transitive axiom audit and independent review.

**P1.4 remains YELLOW.**
