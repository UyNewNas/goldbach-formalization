# The positive strip for the prescribed complex test

Fix the original marking and scale \(Y>0\). Write \(\Phi=\mathrm{spectralTest}\,\ell\,Y\), supported in a compact subinterval of \((0,\infty)\). For \(n=2j+1\) put \(m_n=\int_0^\infty J_n(q)\Phi(q)\,dq/q\), \(\epsilon_n=(-1)^j\) and \(i^{n+1}=-\epsilon_n\). The expansion of \(J_n\) in powers of \(q\) bounds \(|m_n|\) by \(C_R(R/2)^n/n!\) on a support ending at \(R\). This allows polynomial factors in \(n\) and exponential factors \(e^{An}\) for each fixed \(A\).

Use the two measures

\[
 C_\Phi(s)=\int_0^\infty\Phi(q)\cos(qs)\,dq,\qquad
 P(w)=\int_0^\infty\Phi(q)\cos(q\cosh w)\,\frac{dq}{q}.
\]

Define \(\widehat f(\xi)=\int_{\mathbb R}f(w)e^{-i\xi w}\,dw\). The parity-zero sign and factor \(4i^{n+1}\) for the holomorphic weight follow from (4.9) in the archived Drappeau paper. Its (4.10) gives the positive \(J\)-difference with prefactor \(2\pi i/\sinh(\pi t)\). The geometric argument in (4.13) is \(4\pi\sqrt{mn}/c\).

## Odd-order subtraction and inversion

For odd \(n>0\), integrate \(\exp(i(q\sin z+n z))\) around the rectangle \([0,\pi/2]+i[0,T]\). For \(q\geq0\) the magnitude of the top integral is bounded by \(\pi e^{-nT}/2\). The left vertical contribution is purely imaginary. The right vertical contribution has real part \(i^{n+1}\int_0^\infty e^{-nw}\cos(q\cosh w)\,dw\). On the bottom insert the sine Jacobi–Anger series and integrate its product with \(\sin(n\theta)\). The odd sine modes are orthogonal on \([0,\pi/2]\) with squared norm \(\pi/4\). This gives

\[
 \frac{\pi J_n(q)}2=\int_0^{\pi/2}\cos(q\sin\theta)\cos(n\theta)\,d\theta
       +i^{n+1}\int_0^\infty e^{-nw}\cos(q\cosh w)\,dw .
\]

Differentiating the \(\Phi(v)\,dv/v\)-tested sine Jacobi–Anger series gives
\(\cos\theta\, C_\Phi(\sin\theta)=2\sum_{n\ {\rm odd}} n m_n\cos(n\theta)\). The even extension of \(\Phi\) is smooth and compactly supported. Apply ordinary cosine Fourier inversion to it. Split the inversion integral at \(s=1\), using \(s=\sin\theta\) below 1 and \(s=\cosh w\) above 1. Substitution of the preceding two equalities gives the pointwise result for all \(q\geq0\)

\[
 \Phi(q)-2\sum_{n\ {\rm odd}} n m_n J_n(q)
   =\int_{\mathbb R}h(w)\cos(q\cosh w)\,dw,\qquad
 \pi h(w)=\sinh w\,C_\Phi(\cosh w)+2\sum_{n\ {\rm odd}} n\epsilon_n m_n e^{-nw}\quad (w\geq0)
\]

with even extension. Rapid decay of \(C_\Phi\) by integration by parts and the factorial majorant justify all sums and integrals. In particular, \(\int h=0\) by \(q=0\). The splitting point has zero Lebesgue measure. All endpoint terms have been evaluated in convergent one-dimensional integrals.

## Boundary values and the Fourier identity

Use the two entire representations

\[
 B_\pm(z)=\int_0^\infty\Phi(q)e^{\pm iq\cosh z}\,\frac{dq}{q}
          \mp 2i\sum_{n\ {\rm odd}}\epsilon_n m_n e^{\mp nz}.
\]

The entire extension of the sine Jacobi–Anger series to \(\theta=\pi/2+iz\) gives \(\int\Phi(q)\sin(q\cosh z)\,dq/q=2\sum_n\epsilon_n m_n\cosh(nz)\). This proves \(B_+=B_-\) also for complex \(\Phi\). For \(\Re z\geq1,\ 0\leq\Im z\leq\pi\), \(|e^{iq\cosh z}|\leq1\) and \(|\cosh z|\geq\sinh(\Re z)\). Integration by parts in \(q\) bounds the integral in \(B_+\) by \(C_Ne^{-N\Re z}\). Use \(B_-\) on the left half-strip. The correcting series gives \(O(e^{-|\Re z|})\) on either end. Fixed real derivatives have the same decay there by further integration by parts.

The bottom boundary is \(P+iQ\) and the top boundary is \(P-iQ\), where \(P\) is even and \(Q(w)=\int\Phi(q)\sin(q\cosh w)\,dq/q-2\sum_n\epsilon_n m_n e^{-nw}\) is odd. On the right, \(Q'(w)=\pi h(w)\). On the left the same equality follows by parity, including the common value at zero by continuity. Thus the even function \(h\) is smooth at the origin with exponentially decaying derivatives. The adjacent-order Bessel recurrence gives \(2\sum_n n\epsilon_n J_n(q)=qJ_0(q)\) by telescoping. In particular

\[
  \frac{h(0)}2=\frac1{2\pi}\int_0^\infty J_0(q)\Phi(q)\,dq .
\]

For complex \(\xi\) with \(|\Im\xi|<1\), integrate \(B(z)e^{-i\xi z}\) around \([-T,T]+i[0,\pi]\). The sides are \(O_\xi(e^{-(1-|\Im\xi|)T})\) and the top Fourier factor is \(e^{\pi\xi}\). Therefore

\[
 \widehat P-i\widehat Q=e^{-\pi\xi}(\widehat P+i\widehat Q),\qquad
 \widehat h(\xi)=\frac{i\xi}{\pi}\widehat Q(\xi)
                =\frac{\xi}{\pi}\tanh(\pi\xi/2)\widehat P(\xi).
\]

The denominator \(1+e^{-\pi\xi}\) has no zero in the open strip. The boundary convention and integration by parts determine both factors of \(i\). At zero, \(\widehat h(\xi)=\xi^2\widehat P(0)/2+O(\xi^4)\). This gives the threshold limit \(4\widehat P(0)\).

For real \(t\ne0\), the positive scalar \(4\widehat P(2t)\) is \(2\pi\coth(\pi t)\widehat h(2t)/t\). For the actual exceptional order \(0<\alpha<1/2\) the same scalar evaluated at \(t=i\alpha\) is \(-2\pi\cot(\pi\alpha)\widehat h(2i\alpha)/\alpha\). Evenness gives the same value at the other representative. Both are linear identities for the prescribed complex test.

The native coefficient includes the denominator in Drappeau (4.16) or (4.17). Dividing by \(\cosh(\pi t)\) or \(\cos(\pi\alpha)\) gives respectively \(2\pi\widehat h(2t)/(t\sinh(\pi t))\) and \(-2\pi\widehat h(2i\alpha)/(\alpha\sin(\pi\alpha))\). The continuous measure has the additional fixed factor \(1/(4\pi)\); all scalar identities above precede the marked Fourier coefficients and the spectral integration. Under Mathlib's \(2\pi\)-frequency convention the evaluation is at \(t/\pi\). At zero the common numerator is \(-4\int w^2h(w)\,dw\), also \(-8\int_0^\infty(\partial_\nu J_\nu(q)|_{\nu=0})\Phi(q)\,dq/q\) by the existing threshold identity.

For \(w\to+\infty\) the \(n=1\) term gives \(h(w)=(2m_1/\pi)e^{-w}+O(e^{-3w})\), with the same remainder decay after any fixed number of derivatives. With \(s=\cosh w\) the density \(2h(w)\,dw\) has leading term \((2m_1/\pi)s^{-2}\,ds\) and remainder \(O(s^{-4})\,ds\). A zero value of \(m_1\) is allowed. The positive-sign geometric recovery subtracts all odd rows with their actual \(m_n\). The pinned holomorphic nonvanishing theorem in the supplied positive-weight package applies to all sufficiently high odd orders for the original zero mode at each fixed scale.
