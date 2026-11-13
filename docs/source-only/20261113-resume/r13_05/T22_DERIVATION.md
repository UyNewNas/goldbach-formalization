# The restricted fixed-level exceptional inequality on the original cusps

For the manuscript's notation the level is \(z\ge1\), the dyadic length is \(L\ge1/2\), and \(R_{j,\mathfrak a}(n)=\sqrt{|n|}\,\rho^{\rm ABL}_{j,\mathfrak a}(n)\). Write \(\alpha_j=\sqrt{1/4-\lambda_j}\) on \(\lambda_j<1/4\). The positive quadratic form requested in §10(vii) is

\[
  \sum_{\lambda_j<1/4} X^{2\alpha_j}
  \left|\sum_{n\asymp L} b_n R_{j,1}(n)\right|^2 .
\]

Each level permits its own arbitrary complex sequence; the sequence is common to the entire spectral sum at that level. The fixed-level expression contains neither a regular spectral cutoff nor an extra reciprocal cosine. In the native Whittaker convention the frequency mode is \(2\sqrt y\,R_{j,\mathfrak a}(n) K_{\alpha_j}(2\pi |n|y)\). The factor 2 persists in the common probe. There is no further factor of \(\sqrt{|n|}\) on the resulting \(R\)-functional.

## Uniform multiplicity at small normalized height

In infinity coordinates use the bottom rows \((zc,d)\) of \(\gamma=\bigl(\begin{smallmatrix}a&b\\zc&d\end{smallmatrix}\bigr)\). In the original cusp-one coordinates, the actual normalized chart gives the bottom row \(\sqrt z\,(zc-a,d-b)\) of \(\sigma_1^{-1}\gamma\). The two integer pairs in the respective expressions are primitive. At infinity the determinant of any two rows is divisible by \(z\). At cusp one, dilation multiplies the integral determinant by \(z\). Nonparallel rows therefore have absolute determinant at least \(z\) in both charts.

For a given \(w=x+iy\), take the real vector \(v=(C\sqrt y,(Cx+D)/\sqrt y)\) associated to the normalized lower row \((C,D)\). Its squared length equals \(1/\operatorname{Im}(\sigma^{-1}\gamma w)\); the absolute determinant between any two vectors equals that between their lower rows. In the closed radius-\(Y^{-1/2}\) disk, angles between distinct projective directions consequently have \(|\sin(\theta-\theta')|\ge zY\). A half-circle argument, or two dominant-coordinate slope charts with signs identified, bounds the number by an absolute constant times \(1+1/(zY)\). This includes the case \(zY>1\), where there is at most one direction.

Parallel integer primitive rows differ by a sign. Once the sign is fixed, the tops of two determinant-one integer matrices with the same bottom differ by an integer multiple of it. At cusp one the resulting conjugate translation belongs to \(\Gamma_0(z)\) precisely when the integer multiple is divisible by the cusp width \(z\); at infinity the width is 1. In normalized coordinates the remaining action is translation by an integer, of which at most one representative reaches the half-open width-one strip. Opposite matrix signs induce the same action in the effective group. These identifications justify counting physical hits by the projective directions and remove any hidden horizontal multiplicity.

## A coherent packet of probes

Fix one nonnegative smooth bump \(g\) supported on a compact subinterval of the positive line, for instance \([1,2]\), with \(\int g(u)\,du/u>0\). For \(0<\delta\le1\), the positive-height seed in the \(n\)-th signed nonzero Fourier mode is \(\psi_n(y)=\sqrt y\,g(|n|y/\delta)\). Its support in the dyadic coefficient range has common lower height \(\gg\delta/L\). In the Hilbert space whose first inner-product variable is conjugate-linear use \(V=\sum_n\overline{b_n}V_n\). The unfolded probe against each exceptional basis vector has one positive scalar independent of the frequency multiplying the desired complex functional,

\[
 \langle V,u_j\rangle = Q_{\alpha_j}(\delta)\sum_n b_nR_{j,\mathfrak a}(n),\qquad
 Q_\alpha(\delta)=2\int g(u) K_\alpha(2\pi\delta u)\,du/u.
\]

At any point, Cauchy's inequality with the actual number of packet hits bounds the square of its periodization by the new overlap bound times the periodization of the packet square. Positive unfolding then gives an integral of the **whole packet** square on the seed strip. The horizontal integral removes all unequal Fourier frequencies before the modulus coefficients are summed. The remaining integral for each nonzero mode is \(\int |\psi_n(y)|^2dy/y^2=\int |g(u)|^2du/u\), independent of the frequency and of \(\delta\). Consequently

\[
  \|V\|^2\ll (1+L/(z\delta))\sum_n|b_n|^2 .
\]

The real Macdonald representation \(K_\alpha(t)=\int_0^\infty e^{-t\cosh s}\cosh(\alpha s)\,ds\) gives a uniform positive lower bound on \(Q\). Restrict to \(s\in[\log(1/\delta),\log(1/\delta)+1]\). Throughout the fixed bump support the argument \(2\pi\delta u\cosh s\) is bounded above by an absolute constant. For \(\alpha\ge0\), \(\cosh(\alpha s)\ge\delta^{-\alpha}/2\). Thus \(Q_\alpha(\delta)\gg\delta^{-\alpha}\), uniformly even as \(\alpha\downarrow0\). Finite Bessel's inequality followed by monotone bounded nonnegative sums suffices for the entire exceptional subfamily. The proof needs no bound on its cardinality.

## The manuscript range

For \(0<X\le\max(1,z/L)\), choose \(\delta=1/\max(1,X)\). Squaring the probe lower bound produces the target \(X^{2\alpha_j}\), and the multiplicity factor is \(\ll1+L/z\). For \(0<X\le A\max(1,z/L)\), where \(A\) is an absolute constant, comparison against the endpoint costs at most \(\max(1,A)\) since \(0\le2\alpha_j\le1\) follows from nonnegativity of the Laplacian. In particular the actual numerator-side weight \(2+R/L\) with \(R\le z\) costs a factor at most 3. An original bound with \((zL)^\epsilon\) follows after a constant \(2^\epsilon\), including \(z=1, L=1/2\). A zero Fourier mode cannot occur in a nonzero dyadic packet. The constant function has no nonzero Fourier coefficient; the endpoint \(\lambda=1/4\) belongs to the regular spectrum under the strict exceptional predicate. These statements do not use the numerical spectral-gap input.
