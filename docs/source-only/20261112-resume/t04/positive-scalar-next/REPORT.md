# The scalar packet at small positive heights

For a smooth compact logarithmic product test of integral one and a smooth compact ratio test of integral zero, the two actual K functions in the positive-sign scalar Poincaré pairing have an explicit limit when both heights tend to zero. Write \(s=\log(ab)+R\), \(w=\tfrac12\log(a/b)\), and \(L=\log\pi+(s-R)/2\). The test multiplies \(4K_\nu(2e^{L+w})K_\nu(2e^{L-w})\). The factor four comes from the two original \(2\sqrt y\,K_\nu\) radial coefficients. [Physical scalar pairing and cusp normalization](https://github.com/UyNewNas/goldbach-formalization/blob/4733b07d186b2b6aad89e5b9b782c35cc27ebd37/docs/source-only/20261112-resume/t04/kuznetsov-next/Part3OriginalMarkedArithmeticTrace.lean)

Subtracting \(4K_\nu(2e^L)^2\) inside the ratio integral is exact because the ratio test has integral zero. As \(R\) increases, the centered kernel converges to

$$
-4\Gamma(1+\nu)\Gamma(1-\nu)\,w^2
  \left(\frac{\sinh(\nu w)}{\nu w}\right)^2 .
$$

The continuous value of the quotient at zero is one. The actual nonzero-order Gamma waves come from the two convergent I series. Their common circle \(|\nu|=3/4\) has no Gamma poles. The majorant for the product remainder is \(O_U(e^{L/2})\) on \(|w|\le U\), and the maximum modulus principle gives the same bound throughout the disk. This proves an \(O_{\eta,h}(e^{-R/4})\) error for the tested disk and convergence at every fixed imaginary order outside it. Integrating at zero gives \(-4\int w^2h(w)\,dw\). At a nonzero order the limit is \(2\Gamma(\nu)\Gamma(-\nu)\int h(w)\cosh(2\nu w)\,dw\).

For \(|t|\ge1\), the two actual K-series and the Gamma reflection identity bound \(\cosh(\pi t)|K_{it}(a)K_{it}(b)|\) by \(C_B/|t|\) for \(0<a,b\le B\). The change of coordinates \((s,w)\mapsto(s/2+w,s/2-w)\) has absolute Jacobian one. It places the translated test under the compact logarithmic Hamiltonian \(-\partial_x^2+e^{2(x+c)}\), with \(c=\log(2\pi)-R/2\). One physical Green identity in \(x\) gives \(\cosh(\pi t)|F_R(it)|\le C_{\eta,h}|t|^{-3}\) for every \(R\ge0\). The fixed-level unit-band bound grows as \(O_{z,m}(1+T)\). The resulting real-frequency tail has a summable majorant at each fixed ratio window. [Native Hamiltonian transfer](https://github.com/UyNewNas/goldbach-formalization/blob/ca092596f3612af8b4da25b279ce9210091ee0cb/ImbalancedChen/Part3ActualKLCompactTestIntegrationByParts.lean)

The five source files end at **packet_limit**, **response_zero**, **response_nonzero** and **packet_high**. The manuscript ratio cutoffs, their limit in the marked discrete sum and continuous integral, and the original modulus identity are subsequent obligations. The second cutoff limit must treat each actual complementary index at its fixed level because the order-disk bound depends on the ratio window. The registry records the inherited finite-dimensionality, multiplicity and cuspidal eigenvalue positivity sources for that step. The full positive trace also requires the even-weight Petersson term and its identity-cell contribution. [Manuscript spectral tests and sign split](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt)

These are source-only results pending remote kernel checking of the listed files and suppliers. Parent yellow counts and the uniform \(7/32\) energy budget retain their prior status.
