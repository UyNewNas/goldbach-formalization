# P3.5 external input and exact adapter boundary

## Frozen manuscript

The mathematical target remains Appendix A.5 and its input registry in the
[20261106 manuscript](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/b09e5791235ea2249ebc100db9d728251b276efa/paper/release-20261106/en/analytic-appendix.tex).
The appendix blob is `7cf3bbb16cd8924565eb439e474e0674f04631da`, SHA-256
`e2d46ac61f2ae2add02a9c432bc4defec3fd3449230e586d5445a44da01d1548`.
Its Fourier payment is at lines 705–717; regular spectra and shell payment
at 743–801; the returned polynomial and physical substitution at 803–911.
No parameter range or printed spectral normalization is changed here.

## Registered outside input

**Drappeau, Lemma 4.4, equation (4.12), specialized to weight zero
`κ = 0`.** [Author PDF, page 13](https://drappeau.perso.math.cnrs.fr/documents/divtm-siegel.pdf#page=13).
For a smooth test supported at a fixed positive ratio of scale `Y`, with
normalized derivatives through order four bounded by one, this supplies a
common constant multiplying

\[
L(Y)\min\!\left(1,\frac{1+Y\sqrt Y}{1+|t|^3}\right),\qquad
L(Y)=\frac{1+|\log Y|}{1+Y},\quad Y>0.
\]

The constant is uniform over the unit test family, scale and real height.
The parity specialization matters: the same-sign estimate in the general
statement has a factor `(1+|t|)^κ`. The present adapter does not cover a
nonzero parity by silently dropping that factor.

The external lemma is registered here, not declared as a Lean axiom and not
reproved. Its actual application to the native transforms remains outside
the two new modules. The formula uses `Y*sqrt Y`; for positive `Y` this is
the same scale power as the reference's `Y^(3/2)`.

## Existing native definitions to match

The following are existing source definitions, not newly accepted modules.
They were inspected at the source-only history
`fa22a56829ee880404516a36d498ce27dcb32f92`.

| Spectrum | Existing native expression | Source locator |
| --- | --- | --- |
| Holomorphic, `k=2(j+1)` | `4*i^k * integral J_(k-1)(q)*Φ(q) dq/q` | [Part3ActualPositiveHolomorphicWeights](https://github.com/UyNewNas/goldbach-formalization/blob/fa22a56829ee880404516a36d498ce27dcb32f92/docs/source-only/20261112-resume/t04/positive-test-next/Part3ActualPositiveHolomorphicWeights.lean), `holWeight` |
| Same-sign, real `t` | `integral regularKernel(q,t)*Φ(q) dq/q`, whose nonzero-height kernel is `2*pi*i/sinh(pi*t)*(J_(2it)-J_(-2it))` | [Part3ActualPrescribedPositiveJ](https://github.com/UyNewNas/goldbach-formalization/blob/fa22a56829ee880404516a36d498ce27dcb32f92/docs/source-only/20261112-resume/t04/positive-test-next/Part3ActualPrescribedPositiveJ.lean) and [Part3ActualPositiveJRotationPair](https://github.com/UyNewNas/goldbach-formalization/blob/fa22a56829ee880404516a36d498ce27dcb32f92/docs/source-only/20261112-resume/t04/positive-test-next/Part3ActualPositiveJRotationPair.lean) |
| Opposite-sign, real `t` | `8*cosh(pi*t) * integral K_(2it)(q)*Φ(q) dq/q` | [Part3ActualOppositeBesselTransform](https://github.com/UyNewNas/goldbach-formalization/blob/fa22a56829ee880404516a36d498ce27dcb32f92/docs/source-only/20261112-resume/t04/bessel-next/Part3ActualOppositeBesselTransform.lean), `kTransform`, `oppositeWeight` |

At zero height, the native same-sign source uses its continuous kernel
extension; it is not the totalized quotient with denominator zero.
`regular_transform` also supplies local integrability for the original
actual test. Its separate `fixed_regular_decay` chooses a constant after
`ell` and `Y`; that declaration alone does not provide the uniform Fourier
input required here.

The later
[printed row source](https://github.com/UyNewNas/goldbach-formalization/blob/fa22a56829ee880404516a36d498ce27dcb32f92/docs/source-only/20261123-yellow-node-owners/y04_spectral_732/ImbalancedChen/Part3OriginalPrintedPrescribedRows.lean)
keeps `holWeight/2`, continuous `positiveWeight/4` or `oppositeWeight/4`, and
the discrete native weight multiplied by `M₁/4`. The printed continuous row
already includes the cusp sum and `1/pi`. These factors cannot be changed
when applying the generic envelope result. Matching these source expressions
does not promote their missing import closure to an accepted environment.

## What the two Lean modules prove

`Part3ActualSpectralTestNormalization` constructs

\[
N_d(\ell)=\operatorname{finiteTestJetConstant}(d)(1+|\ell_0|)^d>0,
\qquad \psi_{d,\ell,Y}=N_d(\ell)^{-1}\operatorname{spectralTest}(\ell,Y).
\]

For every `Y>0`, the function is smooth, has compact support inside
`[Y/16,16Y]`, and satisfies `Y^n * norm(iteratedDeriv n ψ q) <= 1` for
every `n<=d` and every real `q`. Multiplication by the same positive
normalization recovers the original actual test. Thus `d=4` has a concrete
unit-family witness. Its mode cost is paid by the existing actual Fourier
budget:

\[
\sum_\ell |\operatorname{actualCoeff}(\rho,\sigma,\ell)|N_4(\ell)
 \le C(1+\rho)^{28}.
\]

The theorem proves summability and chooses `C>0` before `rho>=0` and
`|sigma|<=1`. There is no scale in `N_d` or the budget constant.

`Part3DrappeauRegularEnvelope` takes the lower-level transform bound

\[
\|H(t)\|\le E\min\!\left(1,\frac{1+Y\sqrt Y}{1+|t|^3}\right)
\]

and the two separate cumulative quadratic energy inequalities. It derives
finite-cut and positive-measure integral bounds with coefficient `260*E`.
For `K=max(1,2Y)`, it reuses the accepted mixed-tail consumer with auxiliary
parameter zero and high coefficient `E*(1+Y*sqrt Y)/sqrt K`. This gives
`32*E*(1+Y*sqrt Y)/K^3 <= 64*E`; the low cut costs `E`, and the accepted
base-height comparison supplies the factor four. The physical `Y` is still
arbitrary and positive; the zero auxiliary parameter is not a scale
restriction. The measure result proves global `Integrable` before using a
whole-line complex integral or its signed cutoff limit.

## Precise remaining obligations

The new modules do not assume the desired bilinear spectral return. The
conditional envelope module does assume its displayed lower-level
transform estimate; the normalization module is unconditional over the
actual tests and actual Fourier coefficients.

To apply them to P3.5, the continuation must still instantiate the registered
external estimate on the actual native transforms, transport it through
positive scalar normalization, preserve the printed row factors, and connect
the actual separate cumulative energy suppliers. Existing Y04/regular-three
source work should supply those rows once its six missing dependencies are
recovered. See [bounded source recovery](SOURCE_RECOVERY.md).

Exceptional-spectrum/ABL payment, level and Fourier assemblies, and the
final physical substitution must be connected with their actual hypotheses;
these components alone certify neither the full spectral polynomial nor
P3.5. No substantive mathematical gap in the manuscript is established by
these source-availability or interface obligations.
