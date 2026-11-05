# P3.6 — primitive geometric W joined to the actual U5/HB chart

Manuscript pin: `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`.
Source-only base: `de582e6ff4ba430a30889f7c7366a9cf7faa9da4`, branch: `chatgpt/p3-internal-original-w-20261105`.
**SOURCE ONLY / UNCOMPILED / KERNEL-UNVERIFIED / NOT THE FULL PP THEOREM.**

## What is actually new

The preceding `de582e6` packet provided the smooth compact U5 multiplier,
original-group dyadic hats, complete-product trim and selected HB
log(original slot)/log(original group) ratios. This packet introduces the
**original arbitrary geometric factor W** as a primitive differentiable
function, without pretending that all W are expressible as a finite product
of prescribed transition functions.

The paper's original prime-product module §1 (original labelled primes and
fixed smooth families) describes fixed-polylog mixed Euler derivative norms
as a permitted geometric class; §4 lines 151–170 uses
`D = sum_(S subset [d]) ||partial_(2S) w||_1` to pay the Fourier step.
Under log coordinates `z_i = log(n_i/U_i)`, the relevant primitive
derivatives are ordinary coordinate derivatives. This **does not**
construct W from a new arithmetic filter or change the old rho.

`P3FiniteMixedLeibniz.lean` proves a finite Leibniz identity for the
repository's genuine `mixed` and `coordinateDeriv` operators:
each ordered derivative occurrence chooses either W or H, and all
`2^q` choices (including repeated coordinates and their multiplicities)
are retained. The identity is derived from genuine `HasDerivAt.mul`
and finite sums. The primitive hypotheses are
`Compatible (fun js => mixed js W)` and the corresponding condition
for H, not a bound for the target product.

`P3U5OriginalWComposition.lean` discharges the H compatibility
condition with the **actual prior HB expression and scalar jets**, not
with a new assumed H derivative. Finite, uniform constants are collected
for all H derivatives up to q. This supplies a mixed derivative budget
for `W * hbProfile` with only a primitive bound on the W partials:
```
  |mixed_is (W * hbProfile)| <= C_(d,g,a,q) M (m+1)^q,
  when |mixed_js W| <= M for all |js| <= q.
```
C is fixed before ell, chart group scales, group/pair slot assignments,
the selected HB log slots, smoothing width, target parameters and W.
Its dependence on the fixed positive inverse-log floor a is explicit.

`withOriginalW_eq_physical` identifies the extended profile on admitted
physical source points with W times the exact old physical profile and
the ORIGINAL HB logarithm ratio. `same_rho_withOriginalW` retains an
identical integer rho in each signed finite arithmetic sum. The user must
still supply the original physical W to its log-coordinate pullback.

`P3U5OriginalWMixedL1.lean` proves derivative continuity from
the finite Leibniz sum, compact support for every mixed derivative from
the OLD fixed `[-2,2]^d` window, and actual integrability. The new D is
defined as a real integral, never as a convenient upper-bound variable.
The written endpoint is
```
  exists_originalWD_budget:
  D_(W*HB) <= C_(d,g,a) M (m+1)^(2*d)
```
where only W's OWN continuous, legitimate mixed derivatives of orders
at most `2*d` are required to have global bound M.

The logarithmic endpoint is
```
  exists_originalWD_polylog:
  D_(W*HB) <= C_(d,g,a) A (log N)^(E + B*(2*d))
```
provided the independent primitive W derivative class has bound
`A*(log N)^E` up to order 2d and `m+1 <= (log N)^B`.
No Fourier, PP discrepancy, or target product derivative bound is a
premise. This explicitly pays W's E cost rather than hiding it.

## What this does NOT establish

The manuscript allows a fixed geometric W class; our theorem has a
**specific sufficient primitive class**, namely a common pointwise
bound for all partial derivatives up to 2d, plus derivative legitimacy
and continuity. The theorem does NOT prove that every named manuscript
geometric family satisfies this class. It does not settle whether an
original W specified only by integrated norms (rather than global
pointwise norms) can be admitted without a further product estimate.
In particular, it is a conditional geometric-class lemma, not a
conditioned PP conclusion smuggled into a structure.

No full physical W_N pullback/equivalence from the original labelled
prime variables is implemented. Nor is the HB expansion/source coverage,
causal or whole-atom permission, empty Gamma mother words, unsupported
high-rank/enhanced coefficient types, Fourier transform/inversion/tail,
the full modulus-summed arithmetic error, or the b=T exact-product
exception. Fixed m harmonic walls remain distinct from m(N) rates.

The only new imports are the preceding source-only packets; their
module installation and Lean elaboration have NOT been checked.

## Validation (independent, not Lean)

GitHub blob contents were read back. A delimiter/forbidden-token scan
of all three proof modules found zero unmatched round/square/curly
counts and zero prohibited proof escapes. An independent exact integer
polynomial implementation checked **168** multi-index Leibniz cases
(dimension 1–3, derivative order 0–6, eight coefficient/degree seeds),
including repeated coordinates. All 168 agreed between derivatives of
the product and the full two-choice partition sum. Those model checks do
not validate Lean syntax or Mathlib API compatibility.

No Lean/Lake, kernel replay, CI, proof guard, numerical producer or
transitive axiom audit was triggered. No green verification status.
Only an isolated source-only branch is created with [skip ci].
No PR, merge, toolchain change, manuscript update, full87 change,
external input proof, or global tracker update.

## Next concrete internal task

1. Bind the actual manuscript W_N on labelled original primes to
   `W(fun i => U_i * exp(z_i))` and prove the positive scale log inverse
   on each retained individual HB rectangle.
2. Inspect each used W_N for the exact derivative norm class and
   discharge the primitive W hypotheses, or prove a weighted Sobolev/
   integrated-norm variant if that is the only permitted class.
3. Establish the actual Fourier transform and tail (F), then pay the
   tail only AFTER the full modulus sum, with the b=T branch separated.
4. Preserve the same rho, signed masses, multiplicities, causal
   permissions and exact coprime mean across the actual PP insertion.

## Status

    蓝｜有限混合Leibniz/真实重复坐标交叉项源码 [this commit]
    蓝｜原W的允许原始导数假设×实际HB乘子的mixed预算源码 [this commit]
    蓝｜原W组合乘子固定支撑、L1及E+2dB对数D预算源码 [this commit]
    黄｜实际物理W_N的逐族接入、完整允许范数类核实
    黄｜Fourier表示与尾项、完整模数求和及b=T算术付款
    黄｜causal/whole-atom、HB全来源、空母词、高秩/增强、同rho总装
    稿外｜外部经典输入只沿用登记，不实现
