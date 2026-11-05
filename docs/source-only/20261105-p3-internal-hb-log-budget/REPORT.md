# P3.6 — manuscript-internal HB log / original-group inverse-log budget

Base commit: `6e5a634075431c33497e93374a28b8c3e8d17d35`.
Base tree: `04f68dcad367bc3c4ee718826b874b5f6904df94`.
Branch: `chatgpt/p3-internal-hb-log-budget-20261105`.
Packet: `docs/source-only/20261105-p3-internal-hb-log-budget/`.
Paper pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. Full P3.6 remains yellow.**

This increment treats only a manuscript-internal multiplier obligation. It does
not implement an external analytic theorem, add an axiom, certify imported
analytic implementations, or close full PP. The five proof files are candidates
with complete written proof bodies, not compiler-accepted results.

## Manuscript correspondence

The freshly read prime-product completion, lines 90–160, first uses
Lambda(n)/log(n) on each ORIGINAL prime group, and then the order-three HB
identity. Each HB term in each original group has ONE distinguished log slot.
Consequently the factor to carry through geometric separation is

    product_j log(n_pick(j)) / log(product_(i in group j) n_i).

The denominator is the original GROUP product. It is not the selected slot.
A selected slot equal to one contributes log(1)=0; it is never assigned an
inverse log. The Möbius signs, HB binomial coefficients, factorials and marked
scalar masses are not altered or re-proved by the new multiplier dictionary.
The HB expansion/carrier coverage is not inferred from that dictionary.

## 1. Genuine scalar extensions, including the pole

Write S for the actual pinned Real.smoothTransition. Define

    L(y)=S(y+1)*(1-S(y-2))*y,
    R_a(y)=S(2*y/a-1)*(1-S(y-2))/y,  a>0.

L(y)=y for 0<=y<=2, and R_a(y)=1/y for a<=y<=2. Both are zero outside
[-1,3]. R_a is identically zero on y<=a/2, so its apparent singularity at zero
is removed by a genuine zero neighbourhood. The proof does not rely on
Lean's totalized 1/0 to assert differentiability.

The new proof bodies establish C-infinity by the local division rule off zero
and the zero-germ rule at zero. For each fixed order, continuity bounds the
actual iterated derivative on the compact interval; zero-germ differentiation
supplies the complement. Together with the existing S and logStep bounds, this
supplies one global bound for all four scalar kinds at each fixed order.
The constant may depend on the FIXED positive exponent floor a. There is no
claim of uniformity as a tends to zero.

## 2. The physical source supplies the normalization domain

Let ell=log N, n_i>=1, and let P_j be the actual product of the slots of group j.
Assume the manuscript's primitive source-size conditions, with alpha,c,C>0
fixed BEFORE N:

    P_j >= c*N^alpha for every original group,
    product_i n_i <= C*N.

The finite product comparisons prove n_i<=P_group(i)<=product_i n_i.
A single target threshold supplies

    ell>=1, 2*abs(log c)<=alpha*ell, log C<=ell.

It follows for every later tuple, dimension and grouping that

    0<=log(n_i)/ell<=2,
    alpha/2<=log(P_j)/ell<=2.

This is `P3HBLogSourceDictionary.eventually_log_domains`. It does not assume
a normalized-log bound or a nonempty positive-mass family. It uses only the
stated physical sizes; no PNT/Mertens or distribution estimate is involved.

Taking a=alpha/2 and exactly one pick(j) in each original group, the identity

    product_j L(log(n_pick(j))/ell)*R_a(log(P_j)/ell)
      = product_j log(n_pick(j))/log(P_j)

is proved term by term. All powers of ell cancel EXACTLY; no extra log(N)^g
normalization loss is introduced. The unit-slot term is proved zero separately.
On this physical domain every individual ratio lies in [0,1]. This does not
assert positivity of any unrelated signed sieve/HB coefficient.

## 3. Exact composition with the preceding product chart

The existing Expr/jet/jets, ordinary coordinateDeriv and mixed definitions are
reused. `P3SmoothScalarJets` is a reusable scalar interpretation with a proved
chain/product-rule correspondence; it is not a replacement derivative definition.
Its scalar-bound hypotheses are discharged by the concrete profiles above before
stating the new chart endpoint.

The old product expression is lifted exactly, then multiplied by the two
logarithmic leaves per original group. Their affine slopes are 0 or
1/((m+1)*ell). For ell>=1 these and the old slopes are bounded by the SAME
fixed majorant two. Constants precede all later scale offsets, group maps,
choices of log slots, widths, targets and lanes.

`hbProfile_eq_physical` sets each slot to U_i*exp(z_i), uses the previous exact
original-group product identity, and identifies the extended multiplier with
physicalProfile times the original HB ratio. `eventually_physical_hb_identity`
supplies the scalar-core conditions from the actual power bounds above.
Equality is asserted on admitted source points, NOT for arbitrary real points
outside that domain. The extension off the source is smooth and compact.

The complete trim remains at N^(1-kappa0), not a residual quotient. All group
hats and the old U5 multiplier stay in the expression. A separate finite identity
sums all four lanes with the SAME rho and arbitrary signed arithmetic tests.
No arithmetic filter or analytically admissible keep policy is manufactured.

## 4. Actual mixed and L1 endpoint

The new terminal declarations are

    P3U5HBLogMixedL1.exists_hbProfile_mixed_bound
    P3U5HBLogMixedL1.exists_hbD_budget
    P3U5HBLogMixedL1.exists_physical_hbD_polylog

For fixed d,g,a and derivative order q, the written proofs supply

    abs(partial_is hbProfile) <= C_(d,g,a,q)*(m+1)^q.

The old fixed cube [-2,2]^d supports the profile and every mixed derivative.
Zero-germ differentiation, derivative continuity and compact support supply
actual integrability. The D quantity is defined as the genuine sum of L1 norms
of the doubled-coordinate mixed derivatives. The resulting written bounds are

    D_HB <= C_(d,g,a)*(m+1)^(2d),
    D_HB <= C_(d,g,a)*log(N)^(2dB) if m+1<=log(N)^B.

Thus adding the HB numerator/group-denominator factors changes the fixed
constant, not the previous 2dB logarithmic degree. The endpoint has no caller
PP, Fourier, energy, composite derivative or L1 estimate. Its physical-data
specialization is a bound for the EXTENSION; the separate source identity is
what licenses using that extension in the unchanged finite arithmetic sums.

## Remaining manuscript obligations

General original W and its admitted mixed-derivative class still need composition.
The Fourier representation, Fourier L1/tail calculation and arithmetic tail
payment after the complete modulus sum, including exact-product exceptions,
are not supplied here. Neither are causal/history and whole-atom licensing,
source coverage for the full HB expansion, unsupported high-rank/enhanced
classes, or final same-rho PP assembly. A unit HB log slot is NOT the unresolved
empty Gamma mother word; no empty-word coverage is claimed.

No change is made to the two-stage smoothing/harmonic limit. This derivative
budget at varying m does not establish an arithmetic wall-mass rate at m(N).
None of these remaining internal obligations has been moved to EXTERNAL_INPUTS.

## Validation and provenance

The base ref and immutable commit/tree were fetched anew. The three directly
reused prior proof-file bytes were compared with their recorded Git blob IDs.
The pinned basic ContDiff locality API was inspected. No lock/toolchain change
was made. No external research paper was re-proved or newly certified.

The source-contract check was written first and failed on the missing first
module. After implementation the independent script checks source presence and
named endpoints, scans forbidden forms and balanced delimiters, and runs finite
formula regressions. CHECKS.json records the actual results. Numerical guard
checks use an independent transition model, not Lean's function. Symbolic and
rational checks do not prove Python/Lean correspondence.

Lean and Lake were not present. A public-source download attempted in the
container failed at DNS; no toolchain installation succeeded. No Lean
elaboration, kernel replay, transitive axiom audit, repository numerical
producer, proof guard, CI dispatch, Codex task or independent subagent review
was run. VERIFY.lean is unexecuted. There is NO new green status. Earlier
source-only imports and the known native-extension dependency gap remain.

Only this new packet is added on its own branch with skip-CI requested.
Production, prior packets, manuscript, main branch, dependency lock, toolchain,
excluded full87 work and external tracker remain unchanged. No PR or merge.

## Scoped status increment

    蓝｜HB每原组一个log槽位／原组逆log的真实光滑延拓与单位项处理源码 [commit]
    蓝｜稿内固定幂次范围到共同N阈值、实际log比值与log(N)精确抵消源码 [commit]
    蓝｜既有组合乘子×全部HB log比值的实际mixed／L1与2dB次预算源码 [commit]
    黄｜一般原W、Fourier表示／尾项与完整算术付款
    黄｜causal许可、HB全来源覆盖、空母词、高秩／增强与完整稿内PP总装
    稿外｜仅沿用输入登记；不实现、不新增验收
