# Independent calculation for the original all-weight holomorphic sum

Fix the manuscript level \(N\ge1\), positive marks \(m,h\), and its actual smooth test \(\Phi=\mathrm{spectralTest}(\ell,Y)\), \(Y>0\). Put \(j\ge0\), \(k=2j+2\), \(n=k-1\), \(e_k=i^k\), and let \(I_n=\int_0^\infty J_n(x)\Phi(x)\,dx/x\), \(w_j=4e_k I_n\). The original spectral multiplicity is the finite basis index for the full \(S_k(\Gamma_0(N))\) in each individual weight.

## Absolute sum over forms as well as weights

Suppose a width-one normalized frame \(g\) at infinity or cusp one has strip bound

\[
\int_1^\infty\int_0^1 |(f|_k\sigma_g)(x+iy)|^2 y^{k-2}\,dx\,dy\ \le M_N\|f\|_{\rm Pet}^2.
\]

One may take a fixed finite covering multiplicity here. In integer coordinates the dilation by the cusp width \(v\in\{1,N\}\) preserves hyperbolic area and takes this strip to \(0<x<v,\ y>v\). At that height the strip is covered by at most \(v+2\) translates of the standard modular fundamental domain. The phase of the weight section drops out of its square, and each translated domain has energy bounded by the full canonical \(\Gamma_0(N)\) energy. The resulting bound is uniform in the weight. If the norm is given on another measurable representative carrier, this last comparison uses equality of the integrals of the invariant nonnegative Petersson density.

The single positive Fourier coefficient on each horizontal interval satisfies

\[
 |a_{g,f}(m)|^2 e^{-4\pi m y}\le\int_0^1 |(f|_k\sigma_g)(x+iy)|^2\,dx .
\]

After multiplication by \(y^{k-2}\), the incomplete Gamma integral dominates \(e^{-4\pi m}\Gamma(k-1)/(4\pi m)^{k-1}\). Indeed \((u+1)^{k-2}\ge u^{k-2}\) for \(u\ge0\); equality holds at weight two. For the original \(R_{g,f}(m)=\sqrt m\,a_{g,f}(m)/(4\pi m)^{k/2}\) we therefore get

\[
 4\pi\Gamma(k-1)|R_{g,f}(m)|^2\le M_N e^{4\pi m}\|f\|_{\rm Pet}^2 .
\]

Apply this to the Riesz representative of the **whole functional** and use Parseval in the complete ONB of this weight. This gives the very same upper bound for \(4\pi\Gamma(k-1)\sum_i|R_{g,e_i}(m)|^2\) with no dimension factor. Finite Cauchy–Schwarz at the two real frames bounds

\[
 \Gamma(k)|w_j|\sum_i |\overline{R_{\infty,e_i}(m)}R_{1,e_i}(h)|
 \ \le\frac{M_N e^{2\pi(m+h)}}{4\pi}\,n|w_j|.
\]

The compact test gives \(|I_n|\ll_{\ell,Y}(8Y)^n/n!\), so the right side is summable in \(j\). This proves absolute summability on the dependent index \((j,i)\), allowing sums over all weights and all basis elements in either legitimate grouping. For this assertion an estimate only on the absolute value of the *already summed* Fourier products is insufficient.

## Independent denominator estimate and trace normalization

Write \(C=d\sqrt N\), \(Q=4\pi\sqrt{mh}/\sqrt N\), \(q_d=Q/d\) for \(d\ge1\) and \((d,N)=1\). T25 bounds the actual complex group phase \(S_d^*=e(h/N)S_d(m\bar N,h)\) by a positive \(B_m(d)\) with \(\sum B_m(d)/d^2<\infty\). Since all relevant \(n\ge1\), the integer Bessel series gives

\[
 |J_n(q_d)| \le d^{-1}\frac{(Q/2)^n}{n!}\exp((Q/2)^2).
\]

Hence \(\sum_{d,j} |(S_d^*/C)\,2n I_n J_n(q_d)|<\infty\) by the product of the arithmetic majorant and the factorial order majorant. This comparison retains two inverse powers of \(d\) at \(j=0\). It places no positive lower bound on \(q_d\), and the fact that \(\Phi\) has compact support does not truncate the modulus sum of its holomorphic projection.

In A21 let \(\Delta_k=4\pi\Gamma(k-1)\sum_i\overline R_{\infty,e_i}(m)R_{1,e_i}(h)\), \(\delta=\mathbf1_{N=1,m=h}\). Its fixed-weight equality is \(\Delta_k=\delta+2\pi i^{-k}\sum_d S_d^*J_n(q_d)/C\). Multiplying by \(nw_j/(4\pi)\) gives the native spectral summand \(\Gamma(k)w_j\sum_i\overline R_{\infty,e_i}(m)R_{1,e_i}(h)\). The coefficient of each geometric Bessel term is \(2n I_n\), since \(i^{-k}w_j=4I_n\). The actual profile is thus \(\chi_{\rm hol}(q)=\sum_j 2n I_n J_n(q)\). The preceding absolute denominator estimate identifies its geometric sum \(G_{\rm hol}=\sum_d S_d^*\chi_{\rm hol}(q_d)/C\).

The elementary recurrence \(nJ_n(x)=x(J_{n-1}(x)+J_{n+1}(x))/2\) and \(e_{2j+2}=(-1)^{j+1}\) telescope to \(\sum_j nw_j=-2\int J_0\Phi\,dx\). The integral now carries ordinary \(dx\). Writing \(H\) for the full native spectral sum, the resulting identity is

\[
 G_{\rm hol}= H+\frac{\delta}{2\pi}\int_0^\infty J_0(x)\Phi(x)\,dx .
\]

This calculation is for fixed original parameters. Uniform large-sieve estimates in those parameters and the scalar contribution in the positive Kuznetsov formula require separate arguments.
