# Fixed-level unit-band mass

For the unit-frequency native probe \(P_\psi(it)=2\int_0^\infty\overline{\psi(y)}K_{it}(2\pi y)dy/y^{3/2}\), take \(\psi_T(y)=y^{3/2+iT}K_0(2\pi y)\). The change \(q=2\pi y\) and the positive-argument two-\(K\) Mellin formula at \(s=1-iT\) give

\[
 P_{\psi_T}(it)=2(2\pi)^{-1+iT}2^{-2-iT}
 \frac{\Gamma((1-iT+it)/2)^2\Gamma((1-iT-it)/2)^2}{\Gamma(1-iT)}.
\]

For \(T>0\) this yields

\[
 |P_{\psi_T}(it)|^2=\frac{\pi}{16}\frac{\sinh(\pi T)}{T}
 \frac1{\cosh^2(\pi(T-t)/2)\cosh^2(\pi(T+t)/2)}.
\]

At \(T=0\) use the value \(\pi^2/[16\cosh^4(\pi t/2)]\). For \(T\ge1\) and \(\big||t|-T\big|\le1\) the square is bounded below by \(c/[(1+T)\cosh(\pi t)]\) with a universal \(c>0\). This lower bound concerns the even radial probe; it works for both signs of continuous height without postulating pointwise symmetry of the individual arithmetic coefficients.

The concrete cutoff source uses the scaled profile \(\sqrt y\,(Cy)K_0(Cy)(Cy)^{iT}\,w_k(\log(Cy))\), where \(C=2\pi|m|\). It multiplies the bare unit-frequency profile above by \((2\pi)^{1+iT}\) at \(m=1\). The general-frequency limit in this convention is \(2\,\mathrm{probeIntegral}(T,\nu)\). Thus its squared regular norm is \(\pi^3\sinh(\pi T)/(T[\cosh(\pi T)+\cosh(\pi t)]^2)\). The squared logarithmic norm of the positive envelope has the universal majorant \(\int_0^\infty qK_0(q)^2dq=1/2\) and its moment is bounded by \(\sqrt C\int_0^\infty q^{-1/2}K_0(q)dq\).

After any smooth compact cutoff the probe is dominated by the nonnegative zero-mode profile \(g(y)=y^{3/2}K_0(2\pi y)\) times that cutoff. Its log-space squared norm is \(\int_0^\infty yK_0(2\pi y)^2dy\) and its residual moment is \(\int_0^\infty y^{-1/2}K_0(2\pi y)dy\). Both are finite by the actual Mellin sources. Under the true signed frequency dilation \(g_m(y)=|m|^{-1/2}g(|m|y)\), the first integral is invariant and the moment acquires a factor \(\sqrt{|m|}\). The resulting majorant in physical quotient norm can depend on level and signed marking. It is uniform over the cutoff and \(T\). Fatou applies to nonnegative spectral masses, or to finite discrete subcollections before taking the supremum. No ambient norm for an individual Eisenstein series is required.

The original continuous rows concern the infinity and cusp-one observation frames and sum over all native source cusps. In a general normalized observation frame the existing discrete Whittaker source uses the actual eigenbasis. An analogous explicit continuous coefficient in every such observation frame would require its own nonzero Fourier proof. A fixed nonzero, nonnegative compact height test bounds the total unnormalized exceptional squared coefficient mass because \(K_\kappa(y)\ge K_0(y)>0\) at every real order \(\kappa\). An additional bare factor \(1/\cos(\pi\kappa)\) would need control near \(\kappa=1/2\). The actual paired opposite-sign test cancels that factor before estimating.
