# P3.5: small-S transport payment, source-only handoff

## Baseline and candidate

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734` was read at
`5ff48667e56cc9b468c0ee9b5efeec7add24388e`. The enclosing commit supplies
the new SHA. This packet adds only `Part3OriginalSmallScaleTransport.lean`
and this report under `docs/source-only/20261119-p35-small-S/`.

Candidate source SHA-256:
`bd0049917693126a951b0abd3f5b579f499ed5270cf6a3eca6682db3af19027b`.

## Actual, restricted deduction

For `delta>=0`, `x>=1`, and the **original** dyadic scale
`S=scaleS D.key`, restrict to `S<=x^(delta/2)`. The proposed theorem
`smallS_transport_factor` retains either original chart
`Z=S^2` or `Z=2*S^2`, the actual `V=2^j`, the endpoint-corrected
`M=V-1/2`, and either J level scale `Q=Z/2` or `Q=Z` (indeed any
`Q>=Z/2`). It aims to establish the concrete charge

    max(1, max(V,Z^2/V)/(Q+M))^(3/4) <= 6*x^delta.

Reason: `V>=1`, `M>=V/2`, `Q>=Z/2` give `V/(Q+M)<=2`,
`Z/(Q+M)<=2`, and `Z/V<=Z`; hence the ratio is at most `2+2Z`.
The actual two-chart definition gives `Z<=2S^2<=2x^delta`, while
`x^delta>=1`. Since the base is at least one, its `3/4` power is at most
the base. This proof intentionally pays the slightly weaker constant 6;
the exponent `delta` is an explicit extra **squared-energy** cost.

The proposed `smallS_pair` composes this with the already source-only
`all_chart_pair_with_transport`. It preserves the original common phase,
two endpoint-corrected m-level sums, n-side level-dependent square mass,
both chart and sign flags, and all actual slot weights. The initial mean's
epsilon and the new delta are quantified independently, and the added
factor is displayed on each of the two J prices. It does not assert the
subfamily covers all admissible original data or even that every chosen
delta has a nonempty admissible instance. In particular it does not
remove the loss for `S>x^(delta/2)`, supply sharp J, prove 7/32, or close
the original full (24). The raw oldclass reduction, regular and continuous
return, denominator gap, both zero lanes, actual tail, `14eta`/`28eta`,
`128C` enlargement and joint budget remain separate.

## Selected sources and paper version

* `docs/source-only/20261119-p35-all-chart-lossy/Part3OriginalAllChartLossyPair.lean`,
  Git blob `01f0a4bbdf3deddb96a4533b007cb4beadc8cab6`: the existing
  reduced pair with explicit 3/4 transport; it is uncompiled and has an
  unstaged transitive import closure.
* `docs/source-only/20261102-resume-30m/medium_outer_energy/Part3OriginalMaskedOuterEnergy.lean`,
  Git blob `5527a39aea97152b4bcc853b3ff06b0bb8494772`: actual `scaleS` and
  positivity. The previous six-scale adapter and its cutoff remain
  unchanged and are not required by this isolated candidate.
* `docs/source-only/20261102-resume-30q/automorphic_dictionary/Part3OriginalTwoZSourceAssembly.lean`,
  Git blob `62d248aa63bd5d66db39f681732ead8291d8c7ae`: the two actual
  `fixedZ` chart values. The original weighted J and pair sources are
  documented in the previous all-chart handoff.
* Paper is `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  `paper/source/manuscript-body.tex` blob
  `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, and distribution module
  blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §§7 and 10(v)–(vii).
  The classical input boundary remains Pascadi v3 A/J, ABL v1 3.1/3.2,
  regular sieve and the correctly normalized spectral gap; none is newly
  assumed as a Lean axiom or proved in this packet.

## Verification, limits, next step

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including inherited candidate proof bodies. `command -v lean` and
`command -v lake` found neither binary; the pinned import closure is not
staged. No compiler ran, so there is no compiler exit status or log.
The baseline configuration records Lean `leanprover/lean4:v4.33.0-rc1`,
mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, and native goldbach
`09b97db5764ade1246bfb77206baa1b124760958`. Stack limit 8192 KiB;
virtual memory unlimited. No resources were expanded.

`sha256sum` produced the candidate hash above; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). This static text check is not elaboration. No CI, Codex, or user
machine was invoked. Next type-check the exact selected source closure,
replay the kernel and inspect transitive axioms; then check whether the
small-S condition is useful for the actual admissible atlas and pay its
delta in the original common reserve. Handle the complementary S range
with sharp J or another independently justified input, rather than
absorbing a moving 3/4 loss into a constant.
