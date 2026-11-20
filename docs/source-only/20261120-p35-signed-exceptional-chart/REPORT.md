# P3.5: one m phase for both original exceptional trace signs

## Baseline and packet

Continuation branch `chatgpt/p3-5-bounded-chart-20261119-1734`, parent
`32ab2b49b2a6b5552cc9928a1f9dd70b3400fa7d`. The containing commit is the
new SHA. Adds `Part3OriginalSignedExceptionalChart.lean` and this report
under `docs/source-only/20261120-p35-signed-exceptional-chart/`. Lean
source SHA-256:
`1a9d22d2321f0852129b3644c118e4a9e491dc71707cf04c0deb2751c3dab3b6`.

## Exact proposed statement and deduction

For fixed original Fourier mark ell and scale Y>0, choose B(ell,Y)>=0
before the data D, chart, key, cutoffs, residue mark and Poisson sign.
For the actual `traceNegative D k negativeM`, define `signedRawSlot` to
be the original `8*kTransform * star(M)*N_raw` when true, and the
original same-sign `nativeWeight * star(M)*N_raw` when false. No trace
formula is re-established by this definition. For nonzero residue a,
the candidate chooses one omega for the actual common m block, before
r and **before either value of negativeM**, and states

    (sum_{(z,i) in Slots} |signedRawSlot_{z,i}|)^2
      <= B(ell,Y)^2 * (2+log(4V+1))^2
         * (J_(Z/2)(W,j,omega)+J_Z(W,j,omega))/4
         * 2 C_sieve (1+|a|nu L/Z) sum_{z in levels} B_z².

Here V=2^j, W=max(V,Z²/V), L=U/nu, and `Slots` uses the two
endpoint-corrected original level pieces and the actual *strict*
exceptional native basis at each level. `N_raw` retains its actual
level-dependent coefficient and signed index; B_z² is the original
rowMass. The existence of the single omega for **both** signs is the
new merge, not merely the conjunction of two prior existential phase
statements.

For fixed ell,Y, the existing actual opposite-transform candidate
`exceptional_bound` supplies a nonnegative BK uniformly in the real
order alpha in [0,1/2]. The earlier actual positive-slot candidate gives
`Kcos*profileBudget(ell,Y)` for the original same-sign product, with
Kcos=1/cos(3pi/8) and the uncompiled high-positive m-row vanishing
dependency. Take B=max(BK,Kcos*profileBudget). Each signed raw slot is
bounded by B |M| |N_raw| on the same z,i. Select omega once via the
existing `original_chart_J_one_phase` and apply finite Cauchy with the
same W^tau square-root splitting. The existing raw fixed-level n-energy
bound pays the displayed |a|nu L/Z cost. The `/4` remains the native
rhoK=2R normalization. No n side is passed as a common sequence to J.

The K budget and the positive profile still depend on ell,Y without the
uniform quantitative original Fourier/scale estimate. The raw n cost
may be very large, and both J sums remain unevaluated. This candidate is
restricted to the finite strict-exceptional **discrete** piece on one
chart and is not original (24), full-range J, ABL removal, a numerical
gap, regular/holomorphic/continuous return, or all-cost 7/32. It does
not sum the two Poisson signs together or the six smooth scales.

## Source and input boundary

* `Part3OriginalOppositeRawChart.lean`, blob
  `469e5a02af54d5eec66b22941e452a605f3f9764`: original opposite raw
  slot and prior separate-phase candidate. Its original sign-specific
  trace is `Part3OriginalPrescribedOppositeTrace.lean`, blob
  `aceea7d1e291c700367a7df4d422d6137fd2877c`.
* `Part3OriginalPositiveProfileBudget.lean`, blob
  `ca79a7931650cc487c847df8e90e862d8a03a29a`: actual positive slot and
  profile budget, conditional on its unevaluated cosine/high-order chain.
* `Part3OriginalRawChartSieve.lean`, blob
  `0e2524f186f7331598b08667371c307b3a45a161`: raw inverse-weight n
  energy after separately invoking the source-only fixed-level sieve.
* `Part3ActualPrescribedTraceWeights.lean`, blob
  `f7042ecf874254495c9b8702eff85b38ba80109e`: actual K exceptional
  uniform-order estimate at each fixed ell,Y. No new external theorem is
  added; Pascadi v3 Theorem J, ABL v1 Lemmas 3.1–3.2, the numerical gap
  and their missing formal suppliers stay in the parent reports and
  `AVGJ_APPLICABILITY.md`.
* Manuscript pin rechecked:
  `UyNewNas/chen-imbalanced-semiprimes@9731290e8f53cffda44129906cde6a965eaa869b`,
  body blob `d529bea2ecfcc74d64fc1664ac770a3becaa7c79`, distribution
  module blob `19f9672bc9b6d455045213c5e23e10433a9569d2`, §7 (24) and
  §10(vii), matching the established chain.

## Validation and outstanding work

`SOURCE_ONLY`: yes. `COMPILED`: no. `KERNEL_REPLAYED`: no. Transitive
axioms: not checked. Independent review: not performed. `UNEVALUATED`:
yes, including both trace-transform candidates and the raw fixed-level
chain. Lean/Lake not on PATH and exact imports unstaged; no compiler ran,
so no compiler exit code or log exists. Rechecked source pins: Lean
`leanprover/lean4:v4.33.0-rc1`, mathlib
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, native
`09b97db5764ade1246bfb77206baa1b124760958`; installed versions cannot
be checked. Stack 8192 KiB, virtual memory unlimited, unchanged.
`sha256sum` gave the above hash; `rg -n
'\b(sorry|admit|axiom|unsafe|native_decide)\b'` returned exit 1 (no
matches). Neither is compilation. No CI was launched.

Next stage exact imports, compile/replay and inspect transitive axioms.
Prove quantitative uniform scale/mark budgets for both transforms,
replace or pay the raw n cost and independently supply the sharp J.
Actual regular and continuous contributions, both zero-frequency lanes,
the truncated tail, different 14eta/28eta Fourier weights, 128C and
the original N-threshold/reserve order remain separate obligations.
