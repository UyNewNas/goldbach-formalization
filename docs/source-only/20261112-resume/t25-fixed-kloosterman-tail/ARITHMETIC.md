# Absolute modulus tail for the positive weight-two row

Fix a nonzero integer \(m\). For \(d\ge1\) write
\[
 K_d(a,b)=\sum_{x\in(\mathbf Z/d)^\times}e_d(ax+bx^{-1}),\qquad e_d(v)=\exp(2\pi i v/d).
\]
Here \(K_1=1\). We give a majorant \(B_m(d)\), independent of the second marking, such that for every integer \(n\) and every unit \(u\bmod d\),
\[
 |K_d(um,n)|\le B_m(d),\qquad
 \sum_{d\ge1} B_m(d)d^{-2+\delta}<\infty\quad(0\le\delta<1/4).
\]
It permits arbitrary \(d\)-dependent choices of \(n_d,u_d\). It is not an individual saving at all moduli.

## A prime with nonzero first frequency

For a prime \(p\), put \(U=\mathbb F_p^\times\), \(k(x)=(x,x^{-1})\). Orthogonality twice after expanding the fourth power yields the unnormalized identity
\[
 \sum_{a,b\bmod p}|K_p(a,b)|^4=p^2 E,\qquad
 E=\#\{(x,y,v,w)\in U^4:k(x)+k(y)=k(v)+k(w)\}.
\]
An ordered quadruple contributes the product of two complete character sums at the coordinate differences, each \(p\) for a zero difference and zero otherwise. If \(x+y=0\), both inverse sums vanish and \(w=-v\); exactly \((p-1)^2\) quadruples occur. Otherwise equality of inverse sums gives
\[
 (x+y)/(xy)=(x+y)/(vw)\quad\Rightarrow\quad xy=vw.
\]
Thus \((v-x)(v-y)=0\), and \((v,w)\) is \((x,y)\) or \((y,x)\). Counting both possibilities even when equal gives \(E\le3(p-1)^2\), also at \(p=2\).

If \(a\ne0\bmod p\), the \(p-1\) pairs \((at,b/t)\), \(t\in U\), are distinct by the first coordinate. The substitution \(x\mapsto tx\) proves equality of their sums with \(K_p(a,b)\), also when \(b=0\). Keeping only this orbit in the nonnegative fourth moment gives
\[
 (p-1)|K_p(a,b)|^4\le3p^2(p-1)^2,\qquad |K_p(a,b)|^4\le3p^2(p-1)\le3p^3.
\]
In particular \(2p^{3/4}\) suffices. No Weil estimate is used.

## CRT with the same fixed marking

For coprime \(q,r\), put \(u=r^{-1}\bmod q,\ v=q^{-1}\bmod r\). The exact physical CRT identity is
\[
 K_{qr}(m,n)=K_q(um,un)K_r(vm,vn).
\]
The unit substitution gives \(K_q(um,b)=K_q(m,ub)\), and likewise on the other side. The first marking is again literally \(m\); the second can vary. No multiplicativity for untwisted parameters has been assumed.

Define the nonnegative multiplicative function on positive integers \(B_m(1)=1\) with
\[
 B_m(p)=2p^{3/4}\quad(p\nmid m),\qquad B_m(p)=p\quad(p\mid m),\qquad B_m(p^k)=p^k\quad(k\ge2).
\]
The prime estimate, the triangle bound \(|K_{p^k}|\le\varphi(p^k)\le p^k\), and induction on coprime prime-power factors by the preceding CRT identity prove the majorant for all \(n\). A further unit substitution proves it for \(um\). The slots can also be interchanged by inversion of the summation unit.

## Convergence with a little room

Put \(0\le\delta<1/4,\ \lambda=1-\delta,\ W(d)=B_m(d)d^{-2+\delta}\). The local positive-exponent sum is
\[
 L_p=\sum_{k\ge1}W(p^k)=
 \begin{cases}2p^{-5/4+\delta},&p\nmid m,\\p^{-1+\delta},&p\mid m\end{cases}
 +\frac{p^{-2\lambda}}{1-p^{-\lambda}}.
\]
Only finitely many primes divide the positive integer \(|m|\). The good-prime exponent \(5/4-\delta\) exceeds one. The denominator in the second term is at least \(1-2^{-\lambda}>0\), and \(2\lambda>1\). Comparison with ordinary integer power series gives \(\sum_p L_p<\infty\). This includes \(p=2\) without stationary phase.

For each finite prime set \(S\), expansion over finite exponent ranges and then monotone limits give
\[
 \sum_{d\ge1:\,\mathrm{primeFactors}(d)\subseteq S}W(d)=\prod_{p\in S}(1+L_p)\le\exp\big(\sum_p L_p\big).
\]
Taking the primes dividing any finite set of integers bounds every finite partial sum. This proves global summability without invoking an Euler-product theorem that assumes it. For \(D\ge1\) the tail for \(d>D\) of the unweighted-modifier sum \(\sum_d B_m(d)d^{-2}\) is at most \(D^{-\delta}\sum_d W(d)\).

## Original cusp-one frame and weight two

The pinned cuspOneMatrixSum_eq_phase_mul_kloosterman for \(z,d>0,\ (d,z)=1\) gives
\[
 S_{\infty,1}(m,n;d\sqrt z)=e(n/z)\,K_d(m\,\overline z_d,n),\qquad \overline z_d=\mathrm{inverseResidue}(d,z).
\]
The phase has modulus one, and the inverse is a unit for **that \(d\)**. Thus \(|S_{\infty,1}|\le B_m(d)\), including \(d=1,z=1,n=0\) wherever the arithmetic coefficient is used. For the infinity-infinity cusp the ordinary sum restricted to \(z\mid d\) inherits the same majorant. A separate congruence expansion of another cusp into at most \(z\) ordinary sums at varying second markings would inherit \(zB_m(d)\).

For physical positive \(m,h\) set \(C=d\sqrt z,\ A=4\pi\sqrt{mh}\). The summand is \(S_{\infty,1}(m,h;C)J_1(A/C)/C\). The order-one Poisson representation,
\[
 J_1(x)=(x/\pi)\int_{-1}^1e^{ixt}\sqrt{1-t^2}\,dt,\qquad |J_1(x)|\le |x|/2,
\]
or just the order-one Taylor series at zero for fixed indices, bounds the tail by a constant multiple of the arithmetic series. The global Poisson bound gives summand majorant \(A B_m(d)/(2zd^2)\), hence a tail at most \(A(2z)^{-1}D^{-\delta}\sum_dW(d)\). Growth in the positive second marking in this last bound is at most square-root; the arithmetic majorant itself is uniform for all integers. Nothing here identifies the reproducing vector at weight two, passes the Hecke limit, or proves the full trace identity.
