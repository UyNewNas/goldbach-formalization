# P3.6 — manuscript-internal product-chart multiplier budget

Base: `d296beb2ef371ed1bcef330867c82489154ac2e3`.
Base tree: `454cc54739ce379611eb5e99a0b6fb5bdbd1528b`.
Branch: `chatgpt/p3-internal-product-chart-20261104`.
Packet: `docs/source-only/20261104-p3-internal-product-chart/`.
Paper pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. Full P3.6 remains yellow.**

This packet advances the previous atlas-only derivative ledger to the PRODUCT
of the existing U5 atlas multiplier, every original-group smooth dyadic hat,
and one smooth COMPLETE-product trim. It proves the source identities and the
mixed-derivative/L1 budget for those concrete factors together. It does not
claim a Fourier estimate, a full bound for an arbitrary original W, an HB
logarithm/inverse-log budget, causal admission, or a final PP theorem.

## Manuscript correspondence

The freshly read prime-product completion, section 2, lines 71–118, introduces
eta(product/T^(1-kappa0)), then psi(r)=chi(r)-chi(2r), before HB; the smooth
original-group factors remain after HB without inserting a sharp group-product
cut. Section 4, read at the same paper pin in the preceding increment, uses
D=sum_S ||partial_(2S) w||_1. This increment supplies the D-side for the combined
concrete multipliers, not the Fourier integration-by-parts or arithmetic tail
steps that consume D.

The old source-only packets are not modified. Basic calculus and integration
interfaces are reused. No external research theorem is implemented, relabelled
as an internal result, or introduced as a new Lean axiom.

## 1. Exact scalar eta and psi with uniform log-derivative control

Use the same actual S=`Real.smoothTransition` and set

    eta(r)=S(r-1), chi(r)=1-eta(r), psi(r)=eta(2r)-eta(r),
    T(y)=eta(exp y), hat(y)=T(y+log 2)-T(y).

Eta has the manuscript's plateaus: zero below 1, one above 2. T is identically
zero for y<=0 and one for y>=log 2. Positive derivative orders vanish on the
OPEN plateaus; genuine continuity and compactness on [0,log 2] supply a global
bound for each fixed derivative order. Order zero uses the exact [0,1] bound.
No factor exp(offset), group-scale loss or assumed composite derivative bound
is inserted. The positive endpoint derivatives are not discarded.

The source proves hat(log r)=psi(r) for r>0, the range [0,1], support in
[-log 2,log 2], and exact finite telescoping. Its partition-of-unity theorem
has explicit endpoint/coverage hypotheses, not a claim for an unspecified
finite range of dyadic indices.

The previous Expr, normalized jet, coordinateDeriv and mixed definitions are
REUSED. A new two-profile interpretation handles S and T. Chain/product rules
prove equality with actual repeated coordinate derivatives. Global bounds on
both scalar profiles are supplied before all later offsets and slope data;
the finite family bound is not an assumed estimate for the desired chart.

## 2. Product expression, not separate bounds without product losses

The new productProfile is the literal previous compact atlas profile times

    T(b_complete + sum_i z_i) * product_j hat(b_j + sum_(i in group j) z_i).

Every slot has one group label. The expression uses ALL group hats and one
complete trim. The syntax lift identifies the prior atlas/cutoff expression
exactly; it does not construct a replacement root or average rho.

With s=m+1, the added affine slopes are 0 or 1/s, hence uniformly at most one;
the existing atlas slopes remain at most two for log N>=1. The same finite
jet calculus pays EVERY cross term of the product rule. For fixed d, g, q,
one constant precedes all later chart data and supplies

    |partial_(i1)...partial_(iq) productProfile| <= C_(d,g,q)*(m+1)^q.

The fixed number g of original groups affects the constant, not the exponent
q. No constant is chosen after a particular ratio, trim, target or slot map.

## 3. Actual physical products and unchanged source

For positive group bases G_j and one assignment of individual variables,

    groupValue_j = G_j * exp(sum_(slot i=j) z_i),
    completeValue = product_j groupValue_j.

The proved identity is

    completeValue = (product_j G_j)*exp(sum_i z_i).

Moreover G_j can be the actual product of individual lower scales U_i;
`groupValue_eq_slotProduct` then identifies the group with the product of
U_i*exp(z_i), including empty groups with value one. The two U5 coordinates
use two DISTINCT chosen original groups. The explicit pair-slot map is proved
to give exactly their original log coordinates, not independently assigned
geometric tests.

At b_j=log(G_j/R_j) and b_complete=log(product_j G_j/T), `physicalProfile`
is proved equal to productProfile, where physicalProfile is defined DIRECTLY
using eta(completeValue/T), psi(groupValue_j/R_j), and the old smooth U5 weight.
The final endpoint sets T=N^(1-kappa0). It never replaces this by a residual
quotient or by the physical/auxiliary modulus level.

The compact window remains the same fixed [-2,2]^d extension. On the original
individual chart [0,log 2]^d it equals one, so the physical profile equals the
unextended product there. Summing the four lanes restores the compact window
times the group hats and complete trim, NOT a constant one on all of R^d.
An exact finite identity keeps the same rho in every term for arbitrary signed
arithmetic tests. It is not an analytic licence for arbitrary filtered weights.

## 4. Actual mixed L1 ledger and terminal

The old zero-germ lemma on the open complement of the fixed cube proves support
of all mixed derivatives; their continuity follows from the new jet identity.
Genuine compact-support integrability is supplied, rather than relying on a
totalized integral with unknown integrability. Summing the actual doubled-
coordinate L1 norms yields

    D_product <= C_(d,g)*(m+1)^(2d).

Under m+1<=log(N)^B, this is C_(d,g)*log(N)^(2dB). The final declaration is

    ImbalancedChen.P3U5ProductChartMixedL1.exists_physicalProduct_D_polylog

It chooses C after d,g,B but BEFORE N, positive original group bases/scales,
slot assignment, the two U5 group labels, kappa0, m and lane. Its premises are
only those primitive parameter/positivity constraints and log N>=1. No Fourier,
PP, derivative, L1 or energy estimate is an input. Kappa0's analytic range and
causal/source admission remain separate obligations; this derivative statement
by itself does not license any value of kappa0 in a PP application.

## External-input boundary and remaining internal obligations

EXTERNAL_INPUTS.json references the existing external research register. No new
PNT, Mertens, SW, BV, large-sieve, spectral-gap, ABL or Kuznetsov implementation
or axiom is added. The old imported analytic chains are not newly audited.

Still internal and open:

- Multiplication by the remaining general original geometric W and the actual
  HB log/inverse-log factors, with their own allowed class budgets and uniform
  parameter order. The theorem above is not renamed the complete PP weight.
- Fourier representation, Fourier L1/tail bounds, and the arithmetic application
  AFTER the full signed modulus sum, including the exact-product exception.
- The actual causal/history and whole-atom licence, sharp-lane arithmetic wall
  payment when required, original empty-mother identification/payment, unsupported
  high-rank/enhanced classes, and the final same-rho PP assembly.

A derivative bound for m=m(N) does not upgrade the earlier fixed-m harmonic
wall approximation to a rate uniform in m(N). No such change of limits is made.
No original root is frozen or replaced; the excluded full87 work is unchanged.

## Validation performed

The base branch and immutable Git tree were freshly read. The three previous
proof-file bytes from the mounted packet were checked against their Git blob
IDs. The locked ExpDeriv import was inspected; no toolchain/lock change is made.
Four new proof modules contain 797 lines and 72 declarations, including helpers.

The included script passed 800 exact group-product/pair-slot cases, 1,300
numerical log-hat/telescoping/support model cases, 600 exact signed-source
partition cases, and 28 symbolic mixed-chain/product-rule cases. The symbolic
model includes exponential composition but uses polynomial surrogate scalar
functions. The numerical transition is an independent smooth-step model, not
Lean execution. These tests do not prove Python/Lean correspondence or validate
the global analytic derivative/L1 bounds. Static comment-stripped forbidden-form
and delimiter scans passed; CHECKS and INVENTORY contain the actual receipts.

No Lean/Lake executable was present. No elaboration, kernel replay, transitive
axiom audit, independent reviewer, repository producer, proof guard, CI dispatch,
Codex task or child agent was used. VERIFY remains unexecuted. No new green
status is claimed. Source-only imports and the previously identified local
native-extension dependency gap still require the separate verification workflow.

Only this new packet is published on a new branch, with skip-CI requested.
Production, older packets, manuscript, main branch, dependency lock, toolchain,
full87 and external tracker are unchanged. No PR, merge, release or manuscript
publication is performed.

## Scoped status increment

    蓝｜原组光滑dyadic hats与完整乘积trim的真实log轮廓、端点及有限分割源码 [commit]
    蓝｜原U5乘子×全部组hats×完整trim的实际mixed导数与统一常数源码 [commit]
    蓝｜原组/完整乘积精确识别、同rho有限来源重组与固定支撑L1源码 [commit]
    蓝｜该组合D≤C_(d,g)(m+1)^(2d)及2dB次对数预算源码 [commit]
    黄｜其余原W/HB因子、Fourier分离/尾项、算术墙项与causal许可
    黄｜空母词、高秩/增强及完整稿内同rho PP总装
    稿外｜仅沿用输入登记；不实现、不新增验收
