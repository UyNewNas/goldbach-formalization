# P3.5: explicit transported J price for the raw positive chart

## Baseline and changes

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`7f9e4ed8e79804ef57a1291c70447ea186430468`. The containing commit is the
new SHA. Adds only `Part3OriginalRawChartTransport.lean` and this report
under `docs/source-only/20261120-p35-raw-chart-transport/`. Source
SHA-256: `d0a4529a120d73f70b16822042cf38059d62b5deb8075f74ec2c67bb56ef982a`.

## Exact proposed inequality

For epsilon>0, the candidate first chooses one C_epsilon>0, before all
original chart, residue, level and Fourier parameters. Set V=2^j,
M=V-1/2, Z=fixedZ, W=max(V,Z²/V), G=|a| nu, L=U/nu. Define the already
written transport price

    P(C,epsilon,Q,M,W) = max(1,W/(Q+M))^(3/4)
        * C ((1+Q)(1+M))^epsilon (Q+M) M.

For nonzero original a, either chart and Poisson sign, every original
Fourier marking ell and every actual positive test scale Y, the proposed
theorem gives the original positive strict-exceptional chart bound

    (sum_slots |T_{z,i}|)^2
      <= (Kcos B(ell,Y))^2 (2+log(4V+1))^2
         * (P(C,epsilon,Z/2,M,W)+P(C,epsilon,Z,M,W))/4
         * 2 C_sieve (1+G L/Z) sum_{z in levels} B_z².

Here T is the literal pre-removal raw positive trace slot,
`Kcos=1/cos(3pi/8)`, and
`B(ell,Y)=8 integral_{u>0} cosh(u) |profile(ell,Y,u)| du`. The existing
`rowMass` is B_z². Quantifiers in Lean are `exists C>0, for all D,k,
upper,J,j,ell, a!=0, for all r,negativeM,Y>0`; C can depend on epsilon
only. Y and ell are retained explicitly in B, and C does not absorb it.

Derivation: `positive_chart_with_raw_sieve` supplies one phase omega for
both endpoint-corrected J ranges before r, sign and Y. Apply the
existing `full_J_with_transport` to exactly that omega at Q=Z/2 and
Q=Z, both at W. Positivity of the original mass and raw n cost permits
substitution into the same squared Cauchy inequality. The n row remains
level-dependent and is never supplied to J. The two prices and the 1/4
native normalization are retained exactly; no sum over the six scales,
regular spectrum, oldforms, continuous spectrum or zero lanes is made.

The result has **two real, potentially large extra costs**: the raw
factor 1+|a|U/Z and the transport exponent 3/4. For Z>=2V, W=Z²/V;
the transport factor at Q=Z grows at least like (Z/(2V))^(3/4). It
cannot be absorbed into an absolute constant and is not the original
7/32 expense. B(ell,Y) is an exact integral, not yet controlled by the
original 14eta/28eta Fourier budget. This is a lossy positive-sign
strict-exceptional piece only. It does not prove original (24), the full
J theorem, spectral gap, ABL return, or the unified 7/32 result.

## Sources and exact boundary

* `Part3OriginalRawChartSieve.lean`, blob
  `0e2524f186f7331598b08667371c307b3a45a161`: previous raw chart
  Cauchy and fixed-level n aggregation, with exact J sums still present.
* `Part3OriginalAllChartLossyPair.lean`, blob
  `01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`: `transportedPrice` and
  `full_J_with_transport`. The latter composes the initial J region at
  X0=Q+M with the existing positive-frequency 3/4 transport; it does not
  supply sharp full-range J. This packet newly applies that candidate to
  the raw trace, not just the already-reduced n pair.
* `Part3OriginalPositiveProfileBudget.lean`, blob
  `ca79a7931650cc487c847df8e90e862d8a03a29a`: actual test profile and
  dependence on the earlier uncompiled high-positive m-row vanishing.
  Every inherited source is still source-only and UNEVALUATED.
* Original manuscript pin
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79` rechecked;
  distribution module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`,
  §7 (24) and §10(vii). The exact coefficient dependence and input
  limitations were reread from `AVGJ_APPLICABILITY.md` at
  `49a6978d28dabbb7eacaa73c872bb15238e7b4af`, blob
  `e4a4e3e8b5798d9f4616a297b9e1082d4130e36c`.
* Pascadi v3, arXiv:2404.04239v3, Theorem J (3.34)–(3.35), ABL v1
  Lemmas 3.1–3.2, and the numerical gap retain the prior registration,
  exact normalization and missing formal suppliers. No new external
  input or proof of an external theorem is introduced in this packet.

## Verification and next obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axiom check: not performed. Independent review: not performed.
`UNEVALUATED`: yes, including all dependencies. No Lean/Lake executable
is on PATH and the exact import closure is not staged. No compiler ran;
there is no compiler exit code or log. Configuration reread: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot
be verified. Stack 8192 KiB; virtual-memory limit unlimited; no limit
changed. `sha256sum` gave the hash above, and `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` on the candidate returned
exit 1 (no matches). Neither is compilation; no CI was launched.

Next stage the exact import closure and compile/replay this candidate
and its dependencies, then audit axioms. Bound the test profile in the
original scale/mark order; replace or pay the explicit transport and
raw n losses using actually available hypotheses, or formally supply
the sharper J and discrete ABL inputs. The negative-sign K transform,
regular, holomorphic and continuous returns, both zero lanes, actual
cutoff tail, 14eta/28eta, 128C and original N-threshold/reserve order
remain open.
