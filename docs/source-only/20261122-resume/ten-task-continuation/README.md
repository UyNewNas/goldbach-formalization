# Manuscript source continuations — 22 November 2026

This package continues `codex/yellow-closure-20261110` from
`be3b6ef8f8459bf7ac2ba5a2f5e2cc9ed009cad8`. Its mathematical reference is
the frozen 6 November manuscript in
`UyNewNas/chen-imbalanced-semiprimes/paper/release-20261106/en`.

All files are **source only and uncompiled**. Independent review of the
mathematical statements, proof text, selected dependency signatures and
scope found no blocking issue in the sources listed below. This is not
elaboration, kernel replay, an axiom audit or complete dependency-profile
qualification. No new green node or full yellow-node closure is claimed.

## Wu complete-product inner cap: unsifted mass

`ImbalancedChen/P2WuProductInnerUnsiftedLoss.lean` extends the previously
published inner-cap loss estimate from prime outputs to the entire
unsifted labelled prime-tuple mass. It reuses the original cap, the
labelled product fibre bound and the native shrinking-box Theta estimate.

For each fixed rank cap, one common threshold precedes every legal
BoxIndex and pays the rank-summed loss as epsilon times the original
`boxTheta`, with the original `Q=N^(1/2-delta)`. The integer collar
includes product exactly N, repeated prime slots and rank zero.

An exact total-variation decomposition separates the loss already paid
by this cap from the remaining wall's outside leakage and inside
attenuation. Those two remaining terms are not estimated here. No new
PP, density or equivalent target assumption is introduced.

Manuscript correspondence: `argument.tex`,
`prop:current-positive-product`, and the positive smooth outer
approximation in its proof. The native Wu dictionary is an existing
formalization interface; this source does not replace the manuscript's
distinct low-product trim.

## Critical constant modes on an actual cusp tail

`ImbalancedChen/Part3CriticalConstantPairTail.lean` proves that, for
Y>0 and nonzero real t, the actual pair
A*y^(1/2+it)+B*y^(1/2-it) is square integrable on y>Y with density
dy/y^2 exactly when A=B=0. At t=0 these two powers coincide and the
correct condition is A+B=0.

The proof retains the mixed term. A positive dilation
c=exp(pi/(2*t)) gives
D(y)+c*D(c*y)=2*(norm(A)^2+norm(B)^2)/y, where
D(y)=norm(F(y))^2/y^2. This also covers negative t. The existing
inverse-height integrability obstruction completes the argument.

The same file applies the result to the ordinary Eisenstein series'
actual unit-period mean at infinity at every positive level.
`ImbalancedChen/Part3NativeCriticalMeanTail.lean` applies it to the
existing horocycle mean in any pair of normalized native cusp frames,
with the actual incoming channel and continued scattering entry.

Manuscript correspondence: `analytic-appendix.tex`,
`app:classical` and `ana:regular-norm`. These results concern the
spatial constant coefficient. They do not identify the formal
Plancherel measure with an individual Eisenstein vector's spatial norm.

The independent threshold basis sqrt(y), sqrt(y)*log(y) is a different
problem from the coalescing two powers at t=0; its mixed classification
is not supplied in this package. Full spectral expansion, normalized
Kuznetsov/large-sieve inputs and the complete manuscript theorem remain
separate obligations.

## Reused source locations

The new sources use existing modules; they do not copy them into this
package. The module search path must include the following existing
source-only files at the stated base revision as well as the production
sources and the new modules:

| Module | Existing repository path |
| --- | --- |
| `ImbalancedChen.P2WuProductInnerThetaPayment` | `docs/source-only/20261121-resume/wu-product-inner-cap/ImbalancedChen/P2WuProductInnerThetaPayment.lean` |
| `ImbalancedChen.Part3ActualCriticalScatteringEntry` | `docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier/Part3ActualCriticalScatteringEntry.lean` |

Their existing transitive source dependencies are still required.
This table records direct source provenance, not a new installation
or a certified import closure. The project's Lean and Mathlib pins
are unchanged.

`PUBLIC_SOURCE_MANIFEST.json` records exact source identities and
direct imports. Publication uses `[skip ci]`; no validation run is
claimed by this source delivery.

