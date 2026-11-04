# P3.6 — manuscript-internal mixed derivative budget for the actual U5 atlas

Base commit: `317fe75ebe3f9ee4735fe392e810c931b00d7519`.
Base tree: `0c887356225e2e9a47a6c62445ce87df0f3254bb`.
Branch: `chatgpt/p3-internal-chart-budget-20261104`.
Packet: `docs/source-only/20261104-p3-internal-chart-budget/`.
Manuscript inspected at `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.

**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED. P3.6 REMAINS YELLOW.**

This packet supplies a quantitative derivative and mixed-L1 ledger for the
EXISTING four-owner U5 smooth multiplier. It does not supply the other factors
of the full geometric PP weight, the Fourier transform identity, a PP wall
estimate, causal-policy admission, or the unrestricted high-rank theorem.
No external research theorem is implemented or introduced as a new Lean axiom.

## Manuscript location and scope

The freshly read `distribution-prime-product-completion-20261010.txt`, lines
143–180, section 4, fixes individual logarithmic coordinates and introduces a
compact extension equal to the old profile on the individual rectangle. Its
quantity D is the sum of L1 norms of the partial derivatives that differentiate
each selected coordinate twice. The Fourier calculation and the later arithmetic
tail payment are different obligations. This increment supplies that D ledger
for the atlas MULTIPLIER, rather than declaring C-infinity to be a quantitative
budget or confusing harmonic wall mass with arithmetic discrepancy.

## 1. Finite jets are proved to be actual derivatives

`P3AffineTransitionJets.lean` defines a small finite expression language for
constants, derivatives of the genuine `Real.smoothTransition`, constant affine
slopes, sums and products. The normalized differentiation operation inserts the
actual slope and applies the ordinary product rule. A common dilation s is kept
outside the normalized operation.

Crucially `coordinateDeriv` and `mixed` are defined using mathlib's ordinary
`deriv`, not by evaluating the formal jet. `eval_hasDerivAt` invokes the chain
and product rules and differentiability of every scalar transition derivative.
`mixed_eq_jets` then proves

`mixed(is, eval(e))(x) = s^length(is) * eval(jets(is,e))(x)`.

Every finite expression has a global bound after its affine slopes are bounded.
For the transition leaves this actually invokes the existing repository theorem
`P4B.exists_smoothTransition_global_derivative_bound`. This is basic calculus
reuse, not an imported bound on the desired composite profile. A finite maximum
majorant supplies ONE constant for every lane and every ordered q-fold coordinate
derivative, before offsets, slope data, scale and evaluation point are chosen.
No finite jet expression is executed as a Lean decision certificate.

## 2. Exact existing atlas on complete original-group log coordinates

`P3U5LogChartDerivativeBudget.lean` retains the four original affine margins.
Their coefficients, including signs, are

`(-1,-1), (0,-1/2), (3/2,3/2), (-3/2,-2)`.

With ell=log N and arbitrary group scales R_0,R_1, each slot has tag none,
some 0 or some 1. The source coordinate is exactly

`x_i = log(R_i)/ell + sum_(slot j = i) z_j / ell`.

For positive R_i it is proved equal to

`log(R_i * exp(sum_(slot j=i) z_j))/ell`.

Thus no separate residual quotient, rounded root, sharp group-product boundary,
modulus-dependent slot assignment, or modified integer coefficient is inserted.
Tags may represent the HB variables belonging to the two ORIGINAL groups; none
represents variables outside those groups. Their arithmetic source/admission is
not assumed to follow merely from this dictionary.

The actual compact extension is

`chi(z) = product_i S(z_i+2)*(1-S(z_i-1))`,
`wtilde_l(z) = chi(z)*smoothWeight(m,l,chartPoint(z))`.

Here S is exactly `Real.smoothTransition`. Chi is independent of m. The source
proves chi=1 on [-1,1]^d and, in particular, the extended profile equals the
previous profile on [0,log 2]^d. The four extended weights sum to chi everywhere,
NOT to one on all of R^d; they sum to one on the original individual chart.
The physical level, rootQ and rho are not averaged or replaced.

The compact cutoff is represented by affine slopes 1/(m+1), while the atlas
slopes are the listed original coefficients divided by ell. At ell>=1 every
slope has absolute value <=2. The jet constant therefore precedes ell, N, group
scales, tags, m and lane. The new source terminal is

`exists_profile_mixed_bound(d,q)`:

`abs(partial_is wtilde_l(z)) <= C_(d,q)*(m+1)^q`.

No composite derivative, variation, Fourier or PP bound is a premise.

## 3. Actual integrability and the D ledger

`P3U5ChartMixedL1Budget.lean` proves that the profile vanishes outside the fixed
closed cube [-2,2]^d. Zero-germ differentiation on its OPEN complement proves
the same support statement for every repeated mixed derivative. No equality
wall or original arithmetic label is discarded by this argument.

Continuity of each derivative follows from the proved jet identity. Compact
support supplies genuine integrability; this avoids relying on totalized
integrals of nonintegrable functions. The whole-space integral is identified
with the fixed-cube integral, then bounded by the pointwise derivative budget.
The cube's finite real volume is retained in the fixed constant; no numerical
volume computation is needed.

For each finite coordinate subset S, `doubled S` lists every selected coordinate
twice. Its length is 2*card(S)<=2d. `atlasD` is the ACTUAL sum of whole-space L1
norms of these derivatives. `exists_atlasD_budget` proves the source endpoint

`atlasD <= C_d*(m+1)^(2d)`.

Consequently `exists_atlasD_polylog` supplies

`atlasD <= C_d*(log N)^(B*(2d))`

when log N>=1 and m+1<=(log N)^B. B and d are fixed first. All later chart data
follow the same constant. This is an explicit polylogarithmic derivative budget
for the atlas multiplier, not a claim that all other PP profile factors have
already been composed with it.

The last statement concerns DERIVATIVES only. It does not upgrade the preceding
harmonic approximation from fixed m to m=m(N), provide a wall-mass rate, or pay
any signed sharp-lane arithmetic defect. The sequential approximation obligations
remain distinct and retain their original parameter order.

## External-input boundary and open internal work

`EXTERNAL_INPUTS.json` references the existing classical-input register. No PNT,
Mertens, SW, BV, large sieve, spectral gap, ABL or Kuznetsov proof is added. The
pinned mathlib calculus and integration APIs were consulted; no dependency or
compiler version was changed. Existing imported external-source implementations
are neither newly implemented nor freshly certified by this packet.

Still INTERNAL: the full product of atlas, original geometric weight, group hats,
smooth complete-product trim and all relevant Fourier profiles; the actual
Fourier representation/tail and its arithmetic application; causal keep/history
and source licensing; empty-mother identification/payment; unsupported high-rank
and enhanced classes; the remaining medium/long reductions and final same-rho PP
assembly. These are not moved into the external register to make the node blue.
The earlier local-native dependency and source-only installation gaps remain.

## Checks actually performed

Three proof modules contain 613 source lines and 66 inventoried declarations, counting
private lemmas, definitions, abbreviations and the finite syntax type. The line
scanner omits the inline attribute-prefixed `shift_zero` theorem (67 declarations
in the three proof files including it). The new
VERIFY file is NOT executed. No Lean/Lake executable is available in the runtime;
no compiler, kernel replay, transitive-axiom check, project producer, CI dispatch,
Codex task or child agent was run. There is no independent reviewer this turn.

The included script ran 60 exact chain/product-rule model cases, 1,440 rational
affine group/cutoff cases, and 635 mixed-order/power-degree cases. The jet model
uses a polynomial transition, not Lean's smoothTransition, and proves no global
analytic derivative bound. These are independent algebra regressions, not a
proof of correspondence with Lean. Comment-stripped forbidden-form scans,
delimiter checks and source inventories also passed. They are not elaboration.

The delivered archive is a new source-only packet. Existing production files,
prior packets, the paper, main branch, lock file, toolchain, excluded full87 work
and external tracker are unchanged. Only a new branch is published, with skip-CI
requested; no PR, merge, release or manuscript publication is performed.

## Scoped tracker increment

```text
黄｜P3.6（稿内证明范围）
    蓝｜实际U5四分支乘子的原分组log坐标与固定compact延拓源码 [this commit]
    蓝｜实际任意阶mixed偏导、固定支撑与全空间L1供应源码 [this commit]
    蓝｜该乘子D≤C_d(m+1)^(2d)及明确polylog预算源码 [this commit]
    黄｜其余chart因子乘积、Fourier分离/尾项及PP算术墙项付款
    黄｜causal许可、空母词、高秩/增强与完整同rho PP稿内总装
稿外｜沿用登记；只记录，不实现，不增加验收状态
```

These blue leaves mean scoped proof-source coverage only. No new green item is
claimed. The final delivery uses the actual GitHub-returned commit SHA.
