# The continuous orthogonal projection of the original marked packets

The four Lean source candidates identify the marked Eisenstein covariance with the inner product of the actual continuous orthogonal projections on the original weight-zero quotient of \(\Gamma_0(z)\). They also express the full spatial pairing of the two marked packets as the sum of the existing discrete cuspidal series and the absolutely integrable continuous contribution. The endpoint is `OriginalProjectedContinuousCovariance20261112.original_projected_trace`.

For a positive level \(z\), write \(K_z\) for the closure of the linear span of all centered zero-mode Poincaré series formed from smooth compactly supported height profiles, with all normalized integral cusp frames allowed. The earlier operator \(S_g\) synthesizes incoming logarithmic data at the normalized frame \(g\). This package proves on the whole fixed-level quotient Hilbert space that

\[
\frac12\sum_{a} S_{g_a} S_{g_a}^*=\operatorname{proj}_{K_z},\qquad
K_z=(\mathbb C{\bf1})^\perp \cap H_{\rm cusp}(z)^\perp .
\]

Here \(H_{\rm cusp}(z)\) is the previously defined geometric all-frame cusp subspace. A vector belongs to it precisely when every normalized frame annihilates its zero mode. The range of simultaneous native synthesis is exactly \(K_z\), so the range is closed. For the manuscript packets \(V_M,V_N\), put \(B_{V,a}(t)=\int\overline V\,E_a(1/2+it)\,d\mu_z\) and \(P=\operatorname{proj}_{K_z}\). Then

\[
\langle P V_N, P V_M\rangle =
\int_{\mathbb R}\frac{1}{4\pi}\sum_a \overline{B_{V_M,a}(t)}B_{V_N,a}(t)\,dt .
\]

The marked weak-adjoint theorem already supplies absolute integrability and retains the original common \(m\)-block and phase, signed \(n\)-index and both radial test factors. The projections onto the original constant line vanish for both packets. Adding their previously computed complete cuspidal trace, with its original \(K\)-Bessel orders and signed functionals, gives \(\langle V_N,V_M\rangle\). [Marked weak adjoint](https://github.com/UyNewNas/goldbach-formalization/blob/1c0d8d194157d87a3e7e8ad0ca6a8ec87c9df6c2/docs/source-only/20261112-resume/t04/mixed-continuous-next/Part3OriginalMarkedWeakAdjoint.lean) [Original cuspidal trace](https://github.com/UyNewNas/goldbach-formalization/blob/62af0da0e7668d17d1add82141f009b89010211a/docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier/Part3OriginalCuspidalPoincareTrace.lean)

## Mathematical steps

1. On each centered generator the Hilbert analysis coordinate agrees a.e. with the conjugate of its actual boundary column. The centered cross-frame Gram gives the equality after testing on every compact smooth logarithmic function. Density and angular Fourier unitarity extend it to the whole channel. The explicit equivalences through the native cusp orbits identify the manuscript cusp parameter with the original signed-row class. The previously established full-line spatial Gram then yields \(\frac12\sum_a\langle A_a x,A_a y\rangle=\langle x,y\rangle\) on generator pairs. [Spatial generator Gram](https://github.com/UyNewNas/goldbach-formalization/blob/78ae6ad15bb52ec4a60e311f10e75bdc3ce8ef03/docs/source-only/20261112-resume/t04/spectral-next/Part3ActualZeroModeSpatialGram.lean)
2. Log-height density puts the range of each \(S_g\) in the closed generator span. For a generator \(y\), \(TAy-y\) lies in that span and is orthogonal to it by the generator Gram. The closed kernel of \(TA-I\) extends the equality to the span. The adjoint of each \(S_g\) kills its orthogonal complement. Together these identities give the orthogonal projection and the range assertion.
3. Compact logarithmic tests determine the actual normalized horocycle mean as a distribution. Substituting \(y=e^u\) recovers every original continuous compact height test. If a cuspidal vector had constant projection \(c{\bf1}\), its bounded zero-mode adjoint would equal \(-c e^{-u/2}\) a.e. On \(u\le0\) the squared norm dominates \(|c|^2\), and that half-line has infinite measure. Thus \(c=0\). This proves the physical complement identification using the true quotient pairing and the actual constant inside it.
4. The resulting three projections give the weight-zero quotient Gram identity for arbitrary spatial vectors. On the original \(N,M\) vectors the residual term is zero. The physical continuous factor retains the \(1/(4\pi)\) in `nativeProduct`, the old `classProduct` and the two actual `radialProbe` factors. The cuspidal series retains its original unconditional `HasSum` assertion at the source level.

## Manuscript boundary

The distribution argument specifies the common clipped interval, marked phase, and the formal Plancherel form, with cusps \(\infty,1\) at the very same level. Its stated Kuznetsov convention also specifies the \(dt/\cosh(\pi t)\) expression after the physical Bessel/Fourier factors have been converted. The present identity uses the unit-leading Eisenstein vectors with their full \(dt/(4\pi)\) spatial density. Comparing the physical test transforms to that arithmetic trace kernel, the signed geometric identity, regular and exceptional absolute large sieves, and the uniform all-cost \(7/32\) estimate still require their own inputs. [Distribution argument](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L349-L380) [Classical conventions](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/final-classical-input-correspondence-20261010.txt)

The `api-selection` directory supplies the dependency version for staging this package. One declaration-local `open scoped Classical in` makes the equality test on the native cusp-row quotient decidable in the statement of `centered_cross`. The earlier module used `classical` inside its proof. The selected source, unified diff, and header-by-header identities retain its entire mathematical statement and proof text.

This is source-only work with zero kernel credit. Prior obligations on transitive staging of the native cuspidal basis remain attached to its imported trace. The proof of global mean zero in this package uses the log-height adjoint and Lebesgue measure. The old resolvent-based global-mean-zero proof supplies no premise to that argument. No local proof, numerical certificate, or CI was executed. The earlier two packages remain at their published bytes.
