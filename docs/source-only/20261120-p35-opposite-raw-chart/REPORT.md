# P3.5: opposite-sign original exceptional chart

## Baseline and proof packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`a9a4b4ddc0b78ff3c7810f6d05b4bfd568de1137`. The containing commit is
the new SHA. Adds `Part3OriginalOppositeRawChart.lean` and this report
under `docs/source-only/20261120-p35-opposite-raw-chart/`. Lean source
SHA-256:
`9ad520fdfe195bd670bd94899946268143bec25371c09cf023cfd9051f184c8a`.

## Exact candidate and proof

For an original ell and a fixed Y>0, the candidate chooses a nonnegative
K-transform budget B(ell,Y) **before** D, the original level chart,
cutoffs, r and the sign. For original data D with nonzero residue a,
the actual key k, chart `upper`, and original clipped dyadic m block,
it then chooses a single phase omega before r and the Poisson sign.
When the original composite sign obeys `traceNegative D k negativeM =
true`, it proposes

    (sum_{(z,i) in Slots} |(8 KTransform(order_{z,i},spectralTest ell Y))
                           conjugate(M_{z,i}) N_raw(z,i)|)^2
     <= B(ell,Y)^2 * (2+log(4V+1))^2
        * (J_(Z/2)(W,j,omega)+J_Z(W,j,omega))/4
        * 2 C_sieve (1+|a| nu L/Z) sum_{z in levels} B_z²,

where V=2^j, W=max(V,Z²/V), L=rowLength=U/nu, `B_z²=rowMass`, and
`Slots` contains only the original occupied levels and native strict
exceptional indices. The n coefficient is the literal level-dependent
pre-removal row; the original m interval and phase are untouched.

The proof takes B directly from the existing `exceptional_bound` for
the actual test and factor `8*kTransform`. On each actual strict
exceptional native index, `order_exceptional` supplies a real order in
[0,1/2], so that bound applies on the same z and i. After a finite
triangle inequality, split the *unweighted* m/n product with the exact
sqrt(W^tau) and reciprocal factor. Cauchy uses one sigma-index set.
`original_chart_J_one_phase` pays the m square by the two native J
intervals with the same omega and the exact native 1/4 normalization;
`inverse_raw_energy_le` pays the inverse-weight raw n square using
separate fixed-level estimates and the displayed |a| nu L/Z price.
No level-dependent n sequence is presented as a J input. The source's
`traceNegative=true` is the original opposite-sign condition, and
`oppositeRawSlot` is definitionally the discrete summand in the
existing opposite trace source (on its original Row).

B is allowed to depend on ell and Y; the existing compact-test estimate
does not give the quantitative original Fourier/scale budget needed to
pay it uniformly. This candidate proves no extra K-transform bound and
does not transfer the positive-sign cosine denominator to the opposite
branch. J is left as the two exact energies. The n cost is raw and may
be much larger than the manuscript's ABL cost. Hence this is only the
opposite-sign finite strict-exceptional piece, not all of (24), the
continuous return, full J, a 7/32 gap, or the unified small-kernel bound.

## Sources and boundary

* `Part3OriginalPrescribedOppositeTrace.lean`, blob
  `aceea7d1e291c700367a7df4d422d6137fd2877c`: actual raw discrete K
  summand, original Row and `traceNegative=true` condition. Its full
  discrete-plus-continuous trace is not reproved or claimed here.
* `Part3ActualPrescribedTraceWeights.lean`, blob
  `f7042ecf874254495c9b8702eff85b38ba80109e`: `exceptional_bound`,
  valid for fixed ell, Y>0, all alpha in [0,1/2] with original factor 8;
  it provides B before levels, with no quantitative uniformity in ell,Y.
  `Part3ActualUnitBandSpectralMass.lean` provides `order_exceptional`.
* `Part3OriginalRawChartSieve.lean`, blob
  `0e2524f186f7331598b08667371c307b3a45a161`: actual raw inverse-weight
  n-energy and the real enlarged cost. The positive-profile dependency
  is imported through that file but is not used as a K-transform bound.
  All selected sources and their dependencies remain UNEVALUATED.
* Rechecked `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`; its distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24) and
  §10(vii), remains the manuscript pin. Pascadi v3 Theorem J (3.34)–
  (3.35), ABL v1 Lemmas 3.1–3.2, and the gap retain the version,
  normalization and missing-supplier boundary in the prior reports and
  `AVGJ_APPLICABILITY.md`. This packet introduces no new external input.

## Verification and remaining obligations

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including the K estimate, chart J completion and raw fixed-level
sieve candidates. `command -v lean` and `command -v lake` returned no
binary; exact imports are unstaged. No compiler ran; no compiler exit
code or log exists. Rechecked source configuration: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`. Installed versions cannot
be verified. Stack 8192 KiB, virtual-memory limit unlimited; unchanged.
`sha256sum` gave the above hash; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). Static inspection is not compilation; no CI ran.

Next: stage exact imports, compile/replay and check transitive axioms;
prove the actual ell/Y cost for this K budget, pay or replace the raw n
loss using the correct ABL eigenspace argument, and supply sharp J. The
two zero lanes, actual truncation tail, regular and continuous terms,
14eta/28eta, 128C enlargement and original N-threshold/reserve order
remain separate obligations.
