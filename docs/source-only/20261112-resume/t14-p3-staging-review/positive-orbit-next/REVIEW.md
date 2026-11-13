# Independent review of the positive Bruhat orbital limits

**The six new source modules pass static mathematical review for the geometric side of the fixed positive marked pair.** They supply 23 public theorems and 10 public definitions. The result includes both ordered limits, absolute convergence over the original positive moduli at all three stages, and the identity cell at equal cusp and mark. Elaboration and kernel acceptance remain unverified. [Source and declaration audit](SOURCE_AUDIT.json)

The first mark is the original positive common-block frequency \(p\), the second mark is the signed integer \(b\) on a row where `traceNegative=false`, and the level is \(z>0\). A nonzero source residue and membership in the original \(n\)-carrier imply \(b>0\). The first mark satisfies \(p\geq 2^j\) on its prescribed common interval. For \(d\in\mathbb N_{>0}\) coprime to \(z\), the denominator is \(C=\sqrt z\,d\) and the argument is \(q=4\pi\sqrt{p|b|}/C\). The complex coefficient is the original infinity/cusp-one matrix sum divided by \(C\), with the same reciprocal phase. [Upstream source objects](UPSTREAM.json)

In the original rank-one integral the outer conjugation gives \(H(a,b')=\psi(a)\overline{\phi(b')}\) and the positive orbit phase \(e((a+b')\sigma)\). Put \(k=(q/(4\pi))^2\), \(X=a\sigma\), \(u=ab'=k/(1+\sigma^2)\), and \(w=(\log a-\log b')/2\). The original measure becomes \(d\sigma\,dw\). Compact support at each finite parameter pair gives absolute integrability for the two product interchanges. The opposite signs of \(\sigma\) act on the exponential and sum to twice a cosine. This preserves the full complex ratio function \(h_n\).

For the positive slope, \(|d\sigma/du|=k/(2u^{3/2}\sqrt{k-u})\). The factors from the two slopes, the original \(4\pi/q\), the height amplitude \(\sqrt u\), and this derivative leave \(\sqrt{k}\,du/(u\sqrt{k-u})\). Substituting \(s=\log u+R\) gives the exact test

\[
 \int_{e^{s-R}<k}\eta(s)\,\frac{q}{v}\,V_n(v)\,ds,
 \qquad v=4\pi\sqrt{k-e^{s-R}},\qquad
 V_n(v)=\int h_n(w)\cos(v\cosh w)\,dw .
\]

The boundary \(u=k\) is a null singleton. The established zero mass of each \(h_n\) and its uniform exponential tail give \(|V_n(v)|\le A v\) for all \(v>0\). The source proves this with a translate of an integrable exponential. Splitting directly at \(|w|=\log(1/v)\) for \(v\le1\) gives the same uniform order. Thus the bound on the integrand is \(Aq|\eta(s)|\) even at the approach to the square-root endpoint. At fixed \(q>0,n\), first \(R\to+\infty\) gives \(V_n(q)\) by the exact mass-one identity. Next \(n\to\infty\) gives the prescribed positive residual \(\Phi_c(q)\) by the actual cosine projection. [Independent normalization and estimates](NORMALIZATION.md)

At the arithmetic arguments the joint bound for the induced test, ratio response and residual is \(Bq\). The fixed-mark T25 majorant gives the single summable bound \((4\pi B\sqrt{p|b|}/z)B_p(d)/d^2\) on all three sets of summands. Restriction from natural numbers to positive natural numbers is injective. Both filter exchanges with the signed complex sums use this same bound and retain the coprimality restriction. The arithmetic result fixes the mark and scale. [Pinned APIs](PINNED_API.json)

On the identity cell \(z=1,\ p=b\), the source phase is \(e(b)=1\). The two radial seeds give \(p^{-1}\), while \(a=py\) changes \(dy/y^2\) to \(p\,da/a^2\). Taking \(s=2\log a+R\) leaves \(+h_n(0)/2\) at every \(R\). Its limit is \(+\operatorname{diagonalMoment}_0(\Phi)/(2\pi)\) on precisely that cell.

One proof API use in the previously reviewed positive strip needed correction. The pinned theorem `intervalIntegral.integral_Iic_add_Ioi` names the common cut point `b`. I missed the unqualified name and the incorrect named argument in the earlier review. Independent byte substitution verifies one changed line at 147 of the selected strip source. The selection adds zero mathematical declarations. The same two cutoff arguments were corrected in the new chart and response modules. The selected product source explicitly fixes the constant numerator \(q\) in its filter limit. [One-line strip selection](STRIP_API_SELECTION.json)

The verified scope ends at each original positive marked geometric pair. The parent assembly owns the weighted finite carrier sums, the discrete and continuous spectral limits, and the complete positive pretrace identity. Kernel and installation credit for this static package remain zero.
