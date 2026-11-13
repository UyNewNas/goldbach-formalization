# Fixed marked positive orbital limit

Use the original positive first and second frequencies \(m,b\), level \(z>0\), \(d>0\) coprime to \(z\), \(C=d\sqrt z\), \(q=4\pi\sqrt{mb}/C\), and \(k=(q/(4\pi))^2\). Distinguish the cutoff index \(n\) from both arithmetic frequencies. In the rank-one source the outer conjugation makes the input \(H(a,b')=\psi(a)\overline{\phi(b')}\). After this conjugation both additive characters have a positive sign. At fixed \(a>0\), put \(X=a\sigma\) and \(b'=k/[a(1+\sigma^2)]\). The positive induced test is

\[
 \frac1{\sqrt k}\int_{\mathbb R}\int_0^\infty
 H(a,b') e((a+b')\sigma)\,\frac{da}{a}\,d\sigma,\qquad e(x)=e^{2\pi i x}.
\]

The T04 height is \(H_{R,n}(a,b')=\sqrt{p}\,\eta(\log p+R)\,h_n(w)\) in the positive quadrant and zero elsewhere. Here \(p=ab'=k/(1+\sigma^2)\), \(w=(\log a-\log b')/2\), and \(\eta\) is the normalized compact product bump. The ratio window subtracts its mass against this same unit bump. Hence \(\int h_n=0\), \(h_n\to h\) pointwise, and \(|h_n(w)|\le L e^{-|w|}\) with the same \(L\) for every \(n\). Each finite parameter pair has a compact positive log-height support. The support bounds \(p\) below and \(|w|\) above. They bound \(|\sigma|\) at fixed \(k\) and make the pre-oscillatory integral absolutely convergent.

## Physical change of variables

At fixed \(\sigma\), \(a=\sqrt p\,e^w\), \(b'=\sqrt p\,e^{-w}\) and \(da/a=dw\). The two signs of \(\sigma\) now pair with the same \(H\), giving a factor of two and the real cosine of \(4\pi\sqrt{k-p}\cosh w\). Each original \(h_n\) can be complex. Complex linearity survives the sign pairing. On \(\sigma>0\), the inverse \(\sigma=\sqrt{(k-p)/p}\), \(0<p<k\), has derivative of magnitude \(k/[2p^{3/2}\sqrt{k-p}]\). Consequently, with \(s=\log p+R\), \(p=e^{s-R}\), and

\[
 V_n(v)=\int_\mathbb R h_n(w)\bigl(\cos(v\cosh w)-1\bigr)\,dw,
\]

the induced test is

\[
 \Phi_{R,n}(q)=\int_{p<k}\eta(s)\,\frac{\sqrt k}{\sqrt{k-p}}\,
     V_n(4\pi\sqrt{k-p})\,ds .
\]

Indeed, the factors \(k^{-1/2}, 2,\sqrt p,k/(2p^{3/2}\sqrt{k-p})\) give \(\sqrt k\,dp/(p\sqrt{k-p})\). The last substitution changes \(dp/p\) into \(ds\). The end \(p=k\) comes from \(\sigma=0\), a null cut point. The \(p\)-Jacobian is locally integrable there. In the final formula the numerator \(V_n\) also vanishes at zero.

## Both limits at the physical arguments

For \(0<v\le1\), split the two halves of the \(w\)-integral at \(T=\log(1/v)\). On \(0\le |w|\le T\), use \(|\cos u-1|\le u^2/2\) and \(\cosh w\le e^{|w|}\). This contributes at most \(L v^2(e^T-1)\le Lv\). On \(|w|>T\) the bound \(2Le^{-|w|}\) contributes \(4Lv\). For \(v\ge1\), the global bound \(4L\) suffices. Thus \(|V_n(v)|\le5Lv\) for every \(n\) and \(v\ge0\). Substituting \(v=4\pi\sqrt{k-p}\) cancels the square root at \(p=k\), giving

\[
 |\Phi_{R,n}(q)|\le5Lq\,\|\eta\|_1 .
\]

This holds for all \(R\) and \(n\). For fixed \(q>0\), large \(R\) makes \(p=e^{s-R}<k\) throughout the fixed support of \(\eta\), and \(p\to0\) there. The denominator ratio tends to one, \(V_n\) is continuous by dominated convergence, and \(\int\eta=1\). Thus first \(\Phi_{R,n}(q)\to V_n(q)\) at fixed \(n\). Next \(h_n\to h\) under the integrable majorant \(2L e^{-|w|}\), so \(V_n(q)\to\Phi_c(q)\) by the actual positive projection and zero mass.

For the original \(\infty/1\) matrix sum \(S_z(m,b;d)\), the T25 arithmetic source bounds its norm by \(B_m(d)\) and gives \(\sum_{d\ge1}B_m(d)/d^2<\infty\). Both families of marked summands have the same summable bound, up to a fixed factor,

\[
 \frac{|S_z(m,b;d)|}{C}q\le
 \frac{4\pi\sqrt{mb}}{z}\frac{B_m(d)}{d^2}.
\]

The coprimality indicator can be retained throughout. Zero modulus belongs to the separate identity cell. The arithmetic source needs a fixed nonzero first frequency. The constant in the geometric bound may depend on the fixed marking and scale.

## Identity cell

The source supplies \(e(b/z)\) times the conjugated radial pairing at \(z=1,\ m=b\). There \(e(b)=1\), since \(b\) is integral. The two scaled seeds contribute \(m^{-1}\), while \(a=my\) contributes \(m\,da/a^2\), leaving exactly \(\int_0^\infty H_{R,n}(a,a)\,da/a^2\). On the diagonal \(p=a^2\), \(w=0\), so this is \(\int_0^\infty \eta(2\log a+R)h_n(0)\,da/a=h_n(0)/2\). Passing \(n\to\infty\) gives the original indicator times \(h(0)/2=(2\pi)^{-1}\int J_0(q)\Phi(q)\,dq\). It enters with positive sign alongside the positive-modulus geometric sum.
