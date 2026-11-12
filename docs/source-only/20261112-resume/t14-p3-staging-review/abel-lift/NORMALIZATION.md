# Fixed-argument audit of the prescribed opposite-sign test

Fix a Fourier marking and a height scale \(Y>0\). In the manuscript implementation \(\Phi(q)=\chi(q/Y)e(\ell_0 q/(64Y))\), with \(e(x)=\exp(2\pi i x)\). The compact support of \(\chi\) lies in \((1/16,16)\). All bounds below allow constants depending on this fixed test.

## Original orbital integral

The published `orbitTest` integrates the horizontal variable on the whole real line and puts `star` outside both integrals. Its radial weight is \(a^{-2}\overline{\psi(a)}\). Compact positive supports kill the part \(a\le0\). For a positive argument \(q=4\pi\sqrt{k}\), set \(X=as\), \(b=k/[a(1+s^2)]\). Before conjugation the characters are \(e(-as)e(bs)\) for the opposite-sign row. After conjugation the product is \(H(a,b)=\psi(a)\overline{\phi(b)}\), with character \(e((a-b)s)\). The change in measure is \(dX\,da/a^2=ds\,da/a\), and \(4\pi/q=1/\sqrt k\). This gives a complex-linear transform of the post-conjugation profile,

\[
  T H(4\pi\sqrt k)=\frac1{\sqrt k}\int_{\mathbb R}\int_0^\infty
  H(a,b)e((a-b)s)\,\frac{da}{a}\,ds .
\]

For a separated compact positive pair the absolute integral is finite. If both factors are nonzero, \(p=ab\) is bounded below by the product of their support floors, so \(s\) ranges over a bounded interval. The Gaussian lift below has its own absolute bound. Its formula is defined on \(a,b>0\). To write the same integral over all real heights, extend \(H\) by zero outside the positive quadrant. Evaluating the displayed profile algebraically also at two negative heights would introduce an additional contribution.

## Change of variables and constants

Let \(p=ab=k/(1+s^2)\), \(w=\frac12\log(a/b)=\log(a/\sqrt p)\) and \(H(a,b)=h(p)g_\alpha(w)\). Then \(da/a=dw\) at fixed \(s\), and \(a-b=2\sqrt p\sinh w\). Write

\[
  g_\alpha(w)=\sqrt{\alpha/\pi}\cosh w\,e^{-\alpha\sinh^2 w},\qquad
  \lambda=4\pi^2/\alpha,\qquad \alpha>0 .
\]

Putting \(v=\sinh w\) reduces the inner integral to the absolutely integrable Fourier Gaussian at real frequency \(4\pi\sqrt p\,s\). The resulting multiplier is \(e^{-4\pi^2ps^2/\alpha}=e^{-\lambda(k-p)}\). In particular \(\int g_\alpha=1\). On either side of \(s=0\), the inverse derivative has magnitude \(k/(2p^{3/2}\sqrt{k-p})\). Both signs give the same multiplier. Hence

\[
  T H(4\pi\sqrt k)=\sqrt k\int_0^k\frac{e^{-\lambda(k-p)}}{\sqrt{k-p}}\frac{h(p)}{p^{3/2}}\,dp .
\]

The endpoints excluded for these two smooth coordinate charts have measure zero. The endpoint at \(p=k\) has a locally integrable inverse square-root singularity. If \(h\) vanishes for \(p\le A\), \(A>0\), and is continuous, then the pre-oscillatory absolute orbital mass is at most \(2\sqrt{\max(k/A-1,0)}\sup_{A\le p\le k}|h(p)|/\sqrt k\) for \(k\ge A\), and it vanishes below \(A\).

## A pointwise inverse

Define \(F(k)=\Phi(4\pi\sqrt k)/\sqrt k\) for \(k>0\), and extend it by zero. The support lies in \([A,B]\), with \(A=(Y/(64\pi))^2\) and \(B=(4Y/\pi)^2\). This smooth function vanishes on a neighborhood of the origin. Write \(D=F'+\lambda F\) and \(K(v)=1_{v>0}e^{-\lambda v}/\sqrt v\), taking \(K(0)=0\). Set \(f=K*D/\pi\), \(h(p)=p^{3/2}f(p)\) for \(p>0\), extended by zero below.

For \(z>0\), scaling \(v=zt\) gives \((K*K)(z)=e^{-\lambda z}\int_0^1[t(1-t)]^{-1/2}dt=\pi e^{-\lambda z}\). For \(z\le0\) the supported integration region is empty up to a null set. At a fixed \(k\), Tonelli on \(q<p<k\) gives the exact absolute double integral

\[
  \int_{q<p<k} K(k-p)K(p-q)|D(q)|\,dq\,dp
   =\pi\int_{-\infty}^k e^{-\lambda(k-q)}|D(q)|\,dq<\infty .
\]

Fubini thus applies at every \(k\). Convolution with \(D\) followed by the ordinary complex-valued FTC yields \((K*f)(k)=e^{-\lambda k}\int_{-\infty}^k(e^{\lambda q}F(q))'\,dq=F(k)\). This pointwise conclusion permits evaluation at each physical marked modulus. The singular boundaries of the integral introduce no point mass.

## Support and derivatives

The one-sided support of \(K\) forces \(f=0\) on \(( -\infty,A]\). Since \(K\in L^1\) and each derivative of \(D\) is smooth, compactly supported and bounded, differentiation against the fixed \(v=k-q\) measure gives \(f^{(r)}=K*D^{(r)}/\pi\). For \(k>B+1\), this bounds each derivative by \(e^{-\lambda k+\lambda B}\|D^{(r)}\|_1/[\pi\sqrt{k-B}]\). Multiplication by \(k^{3/2}\) and repeated \(k\partial_k\) cost only polynomial powers on this tail. The gap near zero supplies smoothness across zero for the extension of \(h\).

In log heights \(x=\log a,y=\log b\), write \(s_0=x+y\), \(d=(x-y)/2\). The \(s_0\)-derivatives of \(h(e^{s_0})\) vanish below \(\log A\), and for every \(L>0\) are \(O_{j,L}(e^{-L|s_0|})\). Each derivative of \(g_\alpha(d)\) is a polynomial in \(\sinh d,\cosh d\) times \(e^{-\alpha\sinh^2d}\), and is \(O_{j,L}(e^{-2L|d|})\). Applying the chain rule and \(|x|+|y|=\max(|s_0|,2|d|)\) gives the all-orders estimate \(O_{r,t,L}(e^{-L(|x|+|y|)})\) for each mixed derivative. These constants may depend on the original marking and \(Y\).

## Normalization at the trace boundary

The published scalar transform uses \(K_{2\nu}(q)\Phi(q)\,dq/q\). The continuous multiplier is \(8\cosh(\pi t)\,\mathrm{kTransform}_{it}(\Phi)\). The original continuous density divides its same-level singular-cusp covariance \(\sum_{\mathfrak a}\overline{X_{\mathfrak a}}Y_{\mathfrak a}\) by \(4\pi\cosh(\pi t)\). The orbital inverse acts only on \(\Phi\). Applying a trace identity to its noncompact two-variable lift also requires control of the series of compact physical probes and of the geometric and spectral interchanges.
