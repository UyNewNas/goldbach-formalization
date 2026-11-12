# A lift of the prescribed opposite-sign test

This is an independent analytic route to a later source proof. No Lean or kernel claim is attached to this derivation.

Let \(\Phi\in C_c^\infty(0,\infty)\). Write \(q=4\pi\sqrt k\) and \(F(k)=\Phi(4\pi\sqrt k)/\sqrt k\), extended by zero for \(k\leq0\). On the original geometric side a rank-one product of the height profiles enters as \(H(a,b)=\psi(a)\overline{\phi(b)}\). For a general smooth height function of two variables the same formula becomes

\[
 \frac1{\sqrt k}\int_{a>0}\!\int_{\mathbb R}
 H\left(a,\frac{k}{a(1+s^2)}\right)
 e^{2\pi i(a-b)s}\,ds\,\frac{da}{a},\qquad b=\frac{k}{a(1+s^2)}.
\]

Set \(p=ab\), \(w=\frac12\log(a/b)\), and take \(H(a,b)=h(p)g(w)\). At fixed \(s\), \(da/a=dw\). The two possible signs of \(s=\sqrt{(k-p)/p}\) produce conjugate oscillations with argument \(4\pi\sqrt{k-p}\sinh w\). Choose

\[
g(w)=2\sqrt\pi\cosh w\exp[-4\pi^2\sinh^2 w].
\]

With \(u=\sinh w\), its normalized Gaussian integral against either oscillation is \(e^{-(k-p)}\). Since \(|ds/dp|=k/(2p^{3/2}\sqrt{k-p})\), summing the two signs gives

\[
 \Phi_H(4\pi\sqrt k)/\sqrt k=(K*f)(k),
 \quad K(u)=\mathbf 1_{u>0}\frac{e^{-u}}{\sqrt u},\quad f(p)=h(p)p^{-3/2}.
\]

The beta integral gives \((K*K)(u)=\pi e^{-u}\mathbf 1_{u>0}\) almost everywhere. Take \(f=\pi^{-1}K*(F'+F)\) and \(h(p)=p^{3/2}f(p)\) for \(p>0\). Fubini followed by the fundamental theorem of calculus yields \(K*f=F\) pointwise: the last integral is \(e^{-k}\int_{-\infty}^k (e^xF(x))'dx=F(k)\). The support of \(f\) is bounded below by the original positive support floor of \(F\), its derivatives come from convolution with derivatives of \(F'+F\), and its positive tail and all its derivatives decay exponentially. In log coordinates all derivatives of \(H(e^x,e^y)\) decay faster than \(e^{-A(|x|+|y|)}\) for each fixed \(A\). This follows from exponential decay in \(p=e^{x+y}\) and Gaussian decay in \(\sinh((x-y)/2)\). Below a fixed value of \(x+y\), the function vanishes identically.

One way to pass this identity through the actual trace uses a locally finite smooth partition in each log coordinate. Expand each localized box as a smooth periodic function on a strictly larger box and multiply the Fourier atoms by a fixed compact window equal to one on the first box. Integration by parts twice in each coordinate gives an absolutely summable double Fourier series on that box. The mixed derivative estimates provide any desired exponential weight in the two box indices. In this way \(H=\sum_j c_j\psi_j\overline{\phi_j}\) with smooth compact factors. Each atom on box \(i\) has magnitude bounded by the same window \(\chi(\log a-i)\), independently of its Fourier mode. Its physical signed Poincaré vector is dominated by the zero-mode window, whose quotient norm costs at most \(C_{N,n}(e^{-i/2}+e^{-i})\) after the fixed frequency dilation. The exponential decay of the coefficients therefore gives

\[
 \sum_j |c_j|\,\|V_{M,\psi_j}\|\,\|V_{N,\phi_j}\|<\infty.
\]

For the finite original markings the fixed constant also absorbs their weights and frequencies. Physical Bessel and Cauchy–Schwarz bound the absolute cuspidal series and the integral of the absolute continuous covariance of each atom pair by that product of norms. Tonelli then justifies exchanging the tensor sum with both native spectra. This bound includes real exceptional orders without an index-counting assumption. In the scalar transform, every nonzero box has \(ab\) uniformly bounded away from zero even after the fixed enlargement. The old \(K\) estimate \(C_{\nu,\delta}\exp[-\delta\cosh v/2]\) therefore gives an absolutely summable bound for the order-\(\nu\) transform of the tensor sum, for each fixed \(\nu\). It identifies the common multiplier with the actual transform of \(\Phi\). The same support floor makes all geometric evaluations zero beyond a common finite modulus cutoff for each fixed marking. This argument would identify the prescribed opposite-sign trace if its explicit test lift, tensor expansion, and Hilbert norm estimates are supplied in source.
