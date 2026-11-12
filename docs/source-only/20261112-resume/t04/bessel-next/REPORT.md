# The opposite-sign Bessel transform at the original two cusps

The seven source candidates connect the two physical height probes to the Macdonald transform in the marked weight-zero trace. They also give an absolutely convergent, pointwise inverse for the manuscript's prescribed period-64 test and apply it to the complete arithmetic row. The transfer from the two-probe spectral identity to that prescribed test remains open. [Manuscript §10](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L463-L483)

## The two-probe transform

Write \(\Phi=\Phi_{\psi,\phi,-}\) for the signed Bruhat test in the preceding package and \(P_\psi(\nu)=\operatorname{orderProbe}(1,\psi,\nu)\). For every complex order \(\nu\) the new source gives

\[
  8\int_0^\infty K_{2\nu}(q)\Phi(q)\,\frac{dq}{q}
   =\overline{P_\psi(\overline{\nu})}\,P_\phi(\nu).
\]

Both height profiles are continuous, compactly supported in the positive half-line, and may be complex valued. The complex conjugation comes from the original \(N,M\) inner-product order. The proof substitutes \(x=a\sinh v\) and \(q=4\pi\sqrt{ab}\cosh v\) in the actual orbit integral. With \(A=2\pi a\), \(B=2\pi b\), the resulting \(v\)-integral is

\[
 \int_{\mathbb R} e^{\,i(A-B)\sinh v}K_{2\nu}(2\sqrt{AB}\cosh v)\,dv
     =K_\nu(A)K_\nu(B).
\]

The contour shift used here is the existing fixed-order \(K_0\) shift. The original positive support floors bound the transformed kernel by a constant times \(\exp(-\delta\cosh v/2)\) with \(\delta>0\). Applying both Jacobians to the norm integral proves absolute integrability before Fubini. The factors \(2\sqrt y\) in each Whittaker probe and the factor \(1/2\) in the joint measure give the eight in the displayed formula. [Earlier marked Bruhat test](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/docs/source-only/20261112-resume/t04/kuznetsov-next/Part3ActualMarkedBruhatTest.lean)

For real \(t\), put \(H_\Phi(t)=8\cosh(\pi t)\int_0^\infty K_{2it}(q)\Phi(q)\,dq/q\). The theorem `original_opposite_trace` uses this literal integral at every real height, including zero. It gives the original \(\sum_a\overline{M(R_a)}\,N(R_a)H_\Phi(t)\,dt/(4\pi\cosh(\pi t))\) over all singular cusps of the same positive level \(z\). Each discrete coefficient uses \(8\int K_{2\nu}\Phi\,dq/q\) at the basis eigenvalue's actual order \(\nu\), including the real exceptional orders and the threshold. The original residue and Poisson signs determine the block condition `traceNegative = true`. This condition gives \(h<0\) for every licensed second index. Consequently the level-one diagonal also vanishes. The generalized modulus is \(d\sqrt z\), the argument is \(4\pi\sqrt{p|h|}/(d\sqrt z)\), and both original marking coefficients keep their original phases. [Earlier arithmetic trace and phase conversion](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/docs/source-only/20261112-resume/t04/kuznetsov-next/Part3OriginalMarkedArithmeticTrace.lean)

Drappeau's weight-zero specialization of (4.11) displays this factor \(8\cosh(\pi t)\). Equations (4.14), (4.18) and (4.19) use the opposite signed second index, the continuous prefactor \(1/(4\pi)\) and products of \(\sqrt{|n|}\rho(n)\). In the weight-zero Whittaker convention \(W_{0,it}(4\pi |n|y)=2\sqrt{|n|y}\,K_{it}(2\pi|n|y)\), so the coefficient multiplying \(2\sqrt y K_{it}\) is the manuscript \(R(n)=\sqrt{|n|}\rho(n)\). Pascadi's (3.18) separately prints \(4/\pi\) with its own Whittaker and Fourier convention. The equality proved in these sources uses the repository's literal Laplace-defined \(K\) and the original \(R\). [Drappeau (4.7)–(4.19)](https://arxiv.org/pdf/1504.05549v4#page=11) [ABL §3](https://arxiv.org/pdf/2005.13915v1#page=7) [Pascadi §3.3](https://arxiv.org/html/2404.04239v3#S3.SS3)

## The prescribed test and the complete arithmetic row

For every original mode \(\ell\), \(Y>0\) and \(q>0\), `prescribed_inverse` proves the absolute integrability and equality

\[
  \mathrm{spectralTest}(\ell,Y,q)
   =\frac{2}{\pi^2}\int_0^\infty
      t\sinh(\pi t)\,H_{\mathrm{spectralTest}(\ell,Y)}(t)\, K_{2it}(q)\,dt .
\]

The actual cutoff has strict positive compact support. Pullback by \(q=\exp r\) yields a smooth compact log test. Substituting \(\tau=2t\) in the repository's pointwise KL inversion gives the displayed coefficient and retains its absolute-convergence proof. The forward integral is also identified with the existing `kTestTransform` on its original packet data. [Existing pointwise inversion](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/ImbalancedChen/Part3ActualKLCompactPointwiseInversion.lean)

The theorem `original_opposite_modulus_inverse` evaluates this inverse at every licensed original \(q=4\pi\sqrt{p|h|}/(c\sqrt z)\) on the actual chart \(Y=\mathrm{chartY0}\). The existing finite support `enlargedModuli` accounts for the entire prescribed-test arithmetic modulus sum under \(0<N\leq4\,\mathrm{cScale}\). Its finite weighted \(t\)-integral, including \(M\sqrt{\mathrm{fixedZ}}\), the common \(p\) coefficient, and the signed beta, equals `fullModulusRow`. The proof exchanges the integrable terms on that finite set. [Original full-modulus cusp input](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/docs/source-only/20261102-resume-30r/actual_kuznetsov/Part3OriginalFullModulusCuspInput.lean)

## Remaining spectral inputs

For the prescribed opposite-sign test the source now recovers every geometric value used in the row. Passing from the induced-test pretrace to its full infinite cuspidal and continuous spectral expression still requires an admissible sequence or operator argument controlling both sides of the limit, including evaluation on the exceptional orders. The KL pointwise inverse and its scalar majorant alone give no bound on the automorphic spectral functional. The same-sign formula of Drappeau (4.13) also contains the even-weight holomorphic spectral term (4.15) and a different Maass transform (4.10). The local radial KL sources and weight-zero quotient resolution supply neither that term nor a full same-level holomorphic trace. The public Trace Formula Project currently lists its congruence-group volume as planned. [Drappeau Lemma 4.5](https://arxiv.org/pdf/1504.05549v4#page=12) [Trace Formula Project](https://stevenecreech.github.io/trace-formula/)

The regular large sieve, the exceptional inequalities for the original common interval and fixed-level rows, all-cost \(7/32\), and kernel verification remain open. The four predecessor packages retain their original source selections and staging holds. This package has zero formal credit. The author used source, Git and hash inspection for verification. [Manuscript classical-input correspondence](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/final-classical-input-correspondence-20261010.txt)
