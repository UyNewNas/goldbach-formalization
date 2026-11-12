# The prescribed positive test on the width-\(\pi\) strip

Fix the original mode \(\ell\) and \(Y>0\). Put \(\Phi(q)=\mathrm{spectralTest}(\ell,Y,q)\). Its extension by zero is smooth, including at zero, and has compact support in \((Y/16,16Y)\). All test transforms in this proof are complex linear in \(\Phi\). For \(n=2j+1\) let
\[
 m_n=\int_0^\infty J_n(q)\Phi(q)\,\frac{dq}{q},\qquad
 \Phi_c(q)=\Phi(q)-\sum_{j=0}^\infty 2n m_n J_n(q).
\]
The \(J_n\) are the integer orders of the original Gamma series. The already proved fixed-scale estimate gives \(|m_n|\le C(8Y)^n/n!\). Write \(C\Phi(s)=\int_0^\infty\Phi(q)\cos(qs)\,dq\), \(P(w)=\int_0^\infty\Phi(q)\cos(q\cosh w)\,dq/q\), and \(\widehat f(\xi)=\int_{\mathbb R}f(w)e^{-i\xi w}\,dw\). Thus the real Mathlib Fourier frequency is \(\xi/(2\pi)\).

## The two entire representations

For \(Z\ne0\), multiply the two absolutely convergent exponential series with arguments \(qZ/2\) and \(-q/(2Z)\). In their product the terms indexed by \((k+n,k)\) sum to \(Z^nJ_n(q)\), and the terms indexed by \((k,k+n)\) sum to \((-1)^nZ^{-n}J_n(q)\). Count the diagonal \(n=0\) once. Subtract the same identity with \(-Z\) in place of \(Z\), and divide by two. The result is
\[
 \frac{e^{q(Z-Z^{-1})/2}-e^{-q(Z-Z^{-1})/2}}{2}
 =\sum_{j\ge0}J_n(q)(Z^n-Z^{-n}).
\]
Absolute convergence is uniform for bounded \(q\) and \(Z\) in compact annuli. Substitution \(Z=i e^z\) gives \(\sin(q\cosh z)=2\sum_j(-1)^jJ_n(q)\cosh(nz)\). Substitution \(Z=e^{i\theta}\) gives \(\sin(q\sin\theta)=2\sum_j J_n(q)\sin(n\theta)\). Integrating against \(\Phi(q)/q\) commutes with these sums and their derivatives by the factorial bound on \(J_n\) on the compact support. This is the Jacobi–Anger expansion for the original series. [DLMF 10.12.1–10.12.3](https://dlmf.nist.gov/10.12)

Define
\[
 B(z)=\int_0^\infty e^{iq\cosh z}\Phi(q)\,\frac{dq}{q}
            -2i\sum_{j\ge0}(-1)^j m_n e^{-nz}.
\]
Changing the sign of both exponents gives the second expression
\[
 B(z)=\int_0^\infty e^{-iq\cosh z}\Phi(q)\,\frac{dq}{q}
            +2i\sum_{j\ge0}(-1)^j m_n e^{nz}.
\]
The equality follows by subtracting and using the integrated Jacobi–Anger formula. Both expressions are entire. On compact sets, each derivative in \(z\) of the integral has a single integrable compact-\(q\) majorant, and the differentiated sums converge locally uniformly. This argument also proves the identity for a complex period-64 mode.

For \(z=x+iy\), \(0\le y\le\pi\), use the first formula for \(x\ge0\) and the second for \(x\le0\). Then \(\left|e^{\pm iq\cosh z}\right|\le1\). With \(|x|\ge1\), \(|\cosh z|^2=\sinh^2 x+\cos^2 y\gg e^{2|x|}\). The support of \(\Phi(q)/q\) lies strictly inside \((0,\infty)\), so \(M\) integrations by parts in \(q\) bound its integral by \(\|(\Phi/q)^{(M)}\|_1 |\cosh z|^{-M}\). After \(r\) derivatives in \(z\) the integrals instead use finitely many smooth tests \(q^k\Phi(q)/q\), \(0\le k\le r\), with outer factors \(O_r(e^{r|x|})\). Choose \(M>r+A\) to bound these by \(O_{r,A}(e^{-A|x|})\). In the series, \(\sum n^r |m_n| e^{-n|x|}\le e^{-|x|}\sum n^r |m_n|\). In particular,
\[
 \sup_{0\le y\le\pi}|B^{(r)}(x+iy)|\le C_r e^{-|x|}.
\]
All constants may depend on the fixed \(\ell,Y\).

Use both entire representations and \(\cosh(z+i\pi)=-\cosh z\) to obtain \(B(z+i\pi)=B(-z)\). On the real boundaries,
\[
 B(w)=P(w)+iQ(w),\qquad B(w+i\pi)=P(w)-iQ(w),\qquad Q(-w)=-Q(w).
\]
Indeed the integral terms add to \(2P(w)\), and the odd correction changes sign. For \(w\ge0\),
\[
 Q(w)=\int_0^\infty\Phi(q)\sin(q\cosh w)\,\frac{dq}{q}
             -2\sum_j(-1)^j m_n e^{-nw}.
\]
Define \(h(w)=Q'(w)/\pi\) on the full line. This is smooth and even, and, writing \(s_n=(-1)^{j+1}=i^{n+1}\),
\[
 \pi h(w)=\sinh w\,C\Phi(\cosh w)-\sum_j2n\,s_n m_n e^{-nw}\quad(w\ge0).
\]
Every derivative is \(O_r(e^{-|w|})\). On the positive half line the first integral is rapidly decreasing in \(e^w\); the \(n\ge3\) series contributes \(O_r(e^{-3w})\) with the same estimate for each derivative. Therefore \(h(w)=(2m_1/\pi)e^{-w}+O(e^{-3w})\), with termwise differentiated remainders. With \(s=\cosh w\) this implies \(2h(w)\,dw=((2m_1/\pi)s^{-2}+O(s^{-4}))\,ds\) as \(s\to\infty\). This leading term is relevant to the weight-two modulus limit.

## The actual strip shift

For every \(\xi\in\mathbb C\) with \(|\operatorname{Im}\xi|<1\), integrate \(B(z)e^{-i\xi z}\) on the rectangle with corners \(-R,R,R+i\pi,-R+i\pi\). The integrand is entire. Each vertical side has integral bounded in norm by \(\pi C_0 e^{\pi|\operatorname{Re}\xi|}e^{-(1-|\operatorname{Im}\xi|)R}\). Both horizontal integrals are absolutely convergent. Orienting the upper side from right to left gives
\[
  (\widehat P-i\widehat Q)(\xi)=e^{-\pi\xi}(\widehat P+i\widehat Q)(\xi).
\]
Integration by parts on the real axis gives \(\pi\widehat h=i\xi\widehat Q\), with zero boundary terms by the same exponential estimate. Since \(1+e^{-\pi\xi}\ne0\) on this *open* strip,
\[
 \boxed{\ \widehat h(\xi)=\frac{\xi}{\pi}\tanh(\pi\xi/2)\widehat P(\xi)\ }. 
\]
The integral transforms are holomorphic there, by dominated differentiation on each strictly smaller strip. The formula at \(\xi=0\) gives \(\int h=0\). Evenness also gives \(\int wh=0\), and expanding at zero yields \(\widehat h''(0)=\widehat P(0)=-\int w^2h(w)\,dw\).

At a real height \(t\ne0\), the existing (4.10) theorem gives \(4\widehat P(2t)=(2\pi/t)\coth(\pi t)\widehat h(2t)\). At \(t=0\) its actual value is \(4\widehat P(0)= -4\int w^2 h(w)\,dw\), and the expression for \(t\ne0\) has this limit. At any complementary height \(0<\alpha<1/2\), its existing positive numerator is \(8\int_0^\infty\cosh(2\alpha w)P(w)\,dw=4\widehat P(2i\alpha)\). The same strip identity gives this as \(-2\pi\widehat h(2i\alpha)/(\alpha\tan(\pi\alpha))\). The actual spectral coefficients divide by \(\cosh(\pi t)\) and \(\cos(\pi\alpha)\), respectively. Thus their scalar factors away from zero are \(2\pi/(t\sinh(\pi t))\) and \(-2\pi/(\alpha\sin(\pi\alpha))\). Height \(1/2\) is excluded. [Drappeau, (4.9), (4.10) and Lemma 4.5](https://arxiv.org/pdf/1504.05549)

## Pointwise subtraction of the holomorphic rows

The following quarter-strip computation applies to every \(q\ge0\), including zero. Orthogonality of the odd sines on \((0,\pi/2)\) in the second Jacobi–Anger formula gives
\[
 J_n(q)=\frac{2}{\pi}\int_0^{\pi/2}\sin(q\sin\theta)\sin(n\theta)\,d\theta .
\]
Apply Cauchy's theorem to \(e^{i(q\sin z+n z)}\) in \(0\le\operatorname{Re}z\le\pi/2,\ 0\le\operatorname{Im}z\le R\). On the top its modulus is \(e^{-q\cos(\operatorname{Re}z)\sinh R-nR}\le e^{-nR}\). The left vertical integral is purely imaginary; the right vertical integral has real part \(s_n\int_0^R e^{-nw}\cos(q\cosh w)\,dw\). On taking real parts and letting \(R\to\infty\), the addition formula for cosine yields
\[
 \frac{\pi}{2}J_n(q)=
 \int_0^{\pi/2}\cos(q\sin\theta)\cos(n\theta)\,d\theta+
 s_n\int_0^\infty e^{-nw}\cos(q\cosh w)\,dw. 
\]
In particular both sides are ordinary integrals. There is no implicit measure supported at \(s=1\).

The even extension \(x\mapsto\Phi(|x|)\) is smooth compactly supported; ordinary Fourier inversion gives \((\pi/2)\Phi(q)=\int_0^\infty C\Phi(s)\cos(qs)\,ds\) for all \(q\ge0\). On \(0<s<1\) change variables \(s=\sin\theta\) and differentiate the integrated second Jacobi–Anger formula to obtain \(\cos\theta\, C\Phi(\sin\theta)=2\sum_j n m_n \cos(n\theta)\). On \(s>1\) use \(s=\cosh w\). Both changes are monotone; \(s=1\) is a Lebesgue null endpoint. The integral on the upper part is absolutely convergent because \(C\Phi\) is Schwartz. Termwise integration on the bounded low interval costs at most \(\tfrac\pi2\sum n|m_n|\); on the upper half line the exponential corrections cost at most \(\sum |m_n|\). Substituting the quarter-strip equality into the lower part and collecting the upper part gives
\[
 \boxed{\ \Phi_c(q)=2\int_0^\infty h(w)\cos(q\cosh w)\,dw
       =\int_{\mathbb R}h(w)\cos(q\cosh w)\,dw,\qquad q\ge0.\ }
\]
In particular for \(q=0\) the original \(\Phi(0)\) and all \(J_{2j+1}(0)\) vanish, consistently giving zero mass.

Finally the (4.9) weight is \(4s_n m_n\). The previously established original holomorphic diagonal identity gives \(\sum_j 4n s_n m_n=-2\int_0^\infty J_0(q)\Phi(q)\,dq\). Using the explicit value of \(h\) at zero yields
\[
 \frac{h(0)}2=\frac1{2\pi}\int_0^\infty J_0(q)\Phi(q)\,dq .
\]
The two sides describe the scalar before any equal-cusp/equal-mark indicator. The small-height packet limit, its exchanges with the spectrum and the Petersson interpretation of the complementary odd-\(J\) rows are separate steps.
