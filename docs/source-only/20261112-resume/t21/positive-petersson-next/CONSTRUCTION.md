# Petersson's formula on the two original cusp charts

Fix a positive integer \(N=z\), \(r\ge1\), \(k=2r\), \(a=k-1\), and positive original Fourier marks \(m,h\). Write \(e(t)=\exp(2\pi i t)\). Use the original \(\Gamma_0(N)\) carrier with \(d\mu=dx\,dy/y^2\) and an inner product conjugate-linear on the left. The original scaling matrices are \(\sigma_\infty=1\) and \(\sigma_1=\mathtt{oldSL}(N)\), each of parabolic period one.

For \(d\ge1\), \((d,N)=1\), write \(C_d=\sqrt N\,d\) and \(S_d=\mathtt{cuspOneMatrixSum}(N,d,m,h)=e(h/N)S(m\bar N,h;d)\), with inverse modulo \(d\). At each even weight one has

\[
 4\pi\Gamma(k-1)\sum_i\overline{R_{i,\infty}(m)}R_{i,1}(h)
  ={\bf1}_{N=1,\,m=h}
   +2\pi i^{-k}\sum_{\substack{d\ge1\\(d,N)=1}}
      {S_d\over C_d}J_a(4\pi\sqrt{mh}/C_d).                    \tag{1}
\]

The basis runs over all cusp forms of this weight. Each modulus series converges absolutely, including weight two. The argument fixes \(N,m,k\). Drappeau's (4.15) applies \(\Gamma(k)\dot\Phi(k)\) to the basis sum. The phase \(e(h/N)\) in (1) comes from the old cusp chart.

## The actual Hilbert space

For an actual cusp form \(f\), Mathlib's global arithmetic-group bound makes \(y^rf(w)\) bounded on the finite-volume carrier. It gives an \(L^2\) vector there and its pointwise Hermitian product with the vector for \(g\) is \(y^{2r}\overline f g\). If this vector vanishes, the invariant continuous density \(y^{2r}|f|^2\) vanishes almost everywhere on the carrier. It descends to the actual orbit quotient. The published conull effective tiling and full support of hyperbolic volume make the density zero throughout the upper half plane. Since \(y>0\), \(f=0\).

The full modular group space of weight \(k[\mathrm{SL}_2(\mathbb Z):\Gamma_0(N)]\) is finite-dimensional in the pinned library. Among finite sets of points choose one whose common evaluation kernel in this space has minimum dimension. Any nonzero member would give another point strictly decreasing that dimension. Thus these evaluations separate the full-level space. If \(f\) at level \(N\) vanishes at those points, so does its finite coset norm, because the identity coset contributes \(f(w)\) to the product. The norm form is zero, hence \(f=0\) by the pinned norm theorem. The same finite evaluations give a complex-linear injection of the entire level-\(N\) space into a finite power of \(\mathbb C\). The integral norm therefore admits a complete finite ONB of actual forms at every weight. This includes the zero-dimensional case.

Let \(a_{f,g}(m)\) be the native \(q\)-coefficient of \(f|_k\sigma_g\). Then \(R_{f,g}(m)=\sqrt m\,a_{f,g}(m)/(4\pi m)^r\). The Riesz representative \(P_m\) of \(f\mapsto G_m a_{f,\infty}(m)\) is unique, with \(G_m=\Gamma(k-1)/(4\pi m)^{k-1}\). Its expansion in the full ONB gives

\[
 a_{P_m,1}(h)=G_m\sum_i\overline{a_{i,\infty}(m)}a_{i,1}(h). \tag{2}
\]

Multiplication by \((\sqrt m/\sqrt h)^{k-1}\) converts the right side of (2) to the left side of (1). Drappeau's same-cusp (4.26) prints \(4\Gamma(k-1)\) against \(R\). The factor from the unscaled integral and the actual (4.7) in (2) is \(4\pi\Gamma(k-1)\). The positive trace uses (4.9) and (4.15). Equations (4.18) and (4.19) concern opposite signs.

## Regularized Poincaré sum

For \(0<s\le1\) take the actual parabolic sum

\[
 P_{m,s}(w)=\sum_{\gamma\in\Gamma_\infty\backslash\Gamma_0(N)}
                  (y^s e(mw))|_k\gamma .
\]

Translations and central sign preserve the seed under the weight-\(k\) slash. Signed primitive bottom rows give the published parametrization. On any compact subset of the upper half plane, \(|cw+d|/\sqrt{c^2+d^2}\) is bounded below by a positive constant by compactness on the real unit circle and \(\Im w>0\). Also \(|e(m\gamma w)|\le1\). The absolute sum is bounded by \(O_K(\sum_{(c,d)\ne0}(c^2+d^2)^{-(k+2s)/2})\), finite for \(k+2s>2\). Hence \(P_{m,s}\) is continuous and is slash-invariant by parabolic coset reindexing.

For every actual cusp form \(f\), the weight-zero density of each term against \(f\) is the translate of the periodic function \(y^{k+s}\overline{e(mw)}f(w)\). The original carrier parabolic unfolding applies. A vertical absolute majorant on the strip is \(O(y^{r+s-2}e^{-2\pi m y})\), integrable at both ends also for \(r=1\). At a fixed height the integral over one period selects \(e^{-4\pi my}a_{f,\infty}(m)\). Therefore

\[
 \int_{\Gamma_0(N)\backslash\mathbb H}y^k\overline{P_{m,s}(w)}f(w)\,d\mu
   =(4\pi m)^{-(k+s-1)}\Gamma(k+s-1)a_{f,\infty}(m).        \tag{3}
\]

## Arithmetic in every cusp

For \(g=\left(\begin{smallmatrix}a_0&b_0\\c_0&d_0\end{smallmatrix}\right)\in\mathrm{SL}_2(\mathbb Z)\), use the integral coordinate of \(P_{m,s}|_k g\) and common period \(N\). Write \(M=\gamma g=\left(\begin{smallmatrix}A&B\\C&D\end{smallmatrix}\right)\). Choose the central sign so \(C>0\). These bottom rows have precisely \((C,D)=1\), \(Cd_0-Dc_0=0\bmod N\). Indeed the latter is the bottom-left condition for \(Mg^{-1}\). Any such primitive pair can be completed to \(M\), and all remaining choices differ by left integral translation. A class with \(C=0\) occurs exactly when \(N\mid c_0\). It has representative \((0,1)\), its negative represents the same class, and its contribution is \(y^se(mw)\).

Split \(D\) modulo \(CN\) and translate \(w\) by multiples of \(N\). The finite factor at horizontal mode \(e(nx/N)\) is

\[
 K_g(C,n)=\sum_{\substack{D\bmod CN\\(C,D)=1\\Cd_0-Dc_0=0\bmod N}}
          e\!\left({mD^{-1}\over C}+{nD\over CN}\right).
\]

The inverse is modulo \(C\). Translating \(x\) by \(D/C\) gives the positive sign of \(nD/(CN)\). Insert \(N^{-1}\sum_{t\bmod N}e(t(Cd_0-Dc_0)/N)\). Writing \(D=u+Cj\) makes the \(j\)-sum either zero or \(N\). This gives

\[
 K_g(C,n)=\sum_{\substack{t\bmod N\\N\mid n-tCc_0}}
         e(tCd_0/N)\,S((n-tCc_0)/N,m;C).                       \tag{4}
\]

Inversion on the units exchanges the two arguments of \(S\). The T25 fixed-mark Euler bound gives \(B_m(C)\ge0\), uniform in every integer second argument, with \(\sum_C B_m(C)/C^2<\infty\). Thus \(|K_g(C,n)|\le NB_m(C)\) at every cusp. Formula (4) includes \(n=0\) and arbitrary composite levels.

## Limit at weight two

Set \(M_0=2\pi m/(C^2y)\), \(b(u)=(u+i)^{-1}\) and \(d(u)=(1+u^2)^{-1}\). The substitution \(u=(x+D/C)/y\) gives the real horizontal kernel

\[
 E_{k,s,M_0}(u)=b(u)^k(1+u^2)^{-s}\exp(-iM_0 b(u)).
\]

For \(k\ge2,\ 0\le s\le1,\ M_0\ge0\), \(|E(u)|\le d(u)\), since \(\Re[-iM_0 b(u)]=-M_0/(1+u^2)\). Its logarithmic derivative \(L\) satisfies

\[
 L=-kb-2sud+iM_0b^2,\qquad L'=kb^2-2sd+4su^2d^2-2iM_0b^3,\qquad
 E''=(L^2+L')E .
\]

Since \(|b|\le1,\ d\le1,\ |u|d\le1/2\), the \(L^1\) norms of \(E,E',E''\) are bounded uniformly for \(C\ge1,\ y\ge y_0>0,\ 0\le s\le1\). The constant depends on \(k,m,y_0\). Both \(E,E'\) tend to zero at both ends. Two integrations by parts and the \(L^1\) bound at frequency zero give \(|\widehat E(\xi)|\ll_{k,m,y_0}(1+|\xi|)^{-2}\) for the transform with kernel \(e(-\xi u)\).

Each horizontal periodization converges locally uniformly in \(x\) by the bound \(O((1+u^2)^{-1})\). Partition the real line into intervals of length \(N/y\) to compute its Fourier coefficients. These are absolutely summable by the preceding estimate; Fourier uniqueness identifies the ordinary Fourier sum with the continuous periodization everywhere. The contribution to \(P_{m,s}|_k g\) at \(C,n\) is

\[
 {K_g(C,n)\over N}\,C^{-k-2s}y^{1-k-s}
   \widehat E_{k,s,2\pi m/(C^2 y)}(ny/N)e(nx/N).              \tag{5}
\]

On \(y\ge y_0\), (4) and (5) have the common summable majorant \(O_{k,m,N,y_0}\bigl(B_m(C)C^{-2}(1+|n|)^{-2}\bigr)\). On \(y\ge1\) there is the additional factor \(y^{1-k}\), uniformly in \(s\). For each \(C,n\), dominated convergence gives the \(s\downarrow0\) limit of the \(u\)-integral. It is uniform for \(y\) on compact positive height intervals. Indeed the \(s\)-dependent kernel factor differs from one by \(|1-(1+u^2)^{-s}|\), with integral majorant \(d(u)\) independent of \(M_0,\xi\). The outside factors \(C^{-2s}y^{-s}\) converge locally uniformly for fixed \(C\). The double majorant proves locally uniform convergence to \(P_0\) in each integral cusp. The weight-\(k\) slash action passes to the limit.

For a fixed \(C\) at \(s=0\), only finitely many residue classes remain. Each periodization sums holomorphic rational–exponential functions with a locally uniform bound \(O_K((1+|l|)^{-k})\) on the \(l\)-th right translate. It is holomorphic. Formula (5) gives locally uniform convergence of the sums grouped by \(C\), hence \(P_0\) is holomorphic. At every integral cusp, (5) also gives \(P_0|_k g=O(y^{1-k})+O(e^{-2\pi my})\), uniformly in \(x\) as \(y\to\infty\). Every cusp of \(\Gamma_0(N)\) is represented by an integral \(g\). Thus \(P_0\) belongs to the actual space of cusp forms.

To pass (3) to the limit, take the same majorant in (5) with \(y_0=1/2\). At that height and above, every integral chart satisfies
\[
 y^r |(P_{m,s}|_k g)(w)|\le K\,y^{1-r}
       +y^r(1+y)e^{-2\pi my}.
\]
Both terms are bounded on \(y\ge1/2\), uniformly in \(0<s\le1\) and \(g\). Every point of \(\mathbb H\) is an integral translate of a point in the standard fundamental domain, where \(y\ge\sqrt3/2\). The determinant-one height/slash identity transports this uniform bound on \(y^r |P_{m,s}|\) to the entire half-plane. The published original carrier has finite hyperbolic volume. Multiplication by the global bound on \(y^r |f|\) therefore gives a constant integrable majorant for the density in (3). Take \(s=1/(n+1)\) and use dominated convergence. Equation (3) gives \(\langle P_0,f\rangle=G_m a_{f,\infty}(m)\) for every actual \(f\), hence \(P_0=P_m\).

## Native Fourier coefficient at cusp one

At \(g=\mathtt{cuspOneMatrix}\), \(c_0=d_0=1\). Thus \(D\equiv C\bmod N\). Coprimality with \(C\) forces \((C,N)=1\). Each residue can be written uniquely as \(D=C+Nl\bmod CN\), where \(l\bmod C\) is a unit. Then \(D/(CN)=1/N+l/C\), while \(A\equiv(Nl)^{-1}\bmod C\). Their phases sum to \(e(h/N)S(m\bar N,h;C)\) after inverting \(l\). This equals the original matrix sum. The fixed dilation \(\mathrm{diag}(\sqrt N,1/\sqrt N)\) changes the integral cusp period \(N\) to one and its lower-left entry \(d\) to the real modulus \(C_d=\sqrt N\,d\). It acts by \(w\mapsto Nw\) and the weight factor \(N^{k/2}\). For \(N=1\) the unique zero-denominator class gives \({\bf1}_{m=h}\).

For a positive real modulus \(C=C_d\) in the normalized chart, the determinant gives \(Mw=A/C-1/[C^2(w+D/C)]\). Unit right translations therefore give the orbital sum of a single representative

\[
 e(mA/C)C^{-k}\sum_{l\in\mathbb Z}(w+D/C+l)^{-k}
          \exp\{-2\pi i m/[C^2(w+D/C+l)]\}.                    \tag{6}
\]

Put \(V=-2\pi i m/C^2\). Expand the exponential. The Taylor sum can be interchanged with the integer sum since \(|w+D/C+l|\ge\Im w\), \(k\ge2\), and \(\sum_t(|V|/\Im w)^t/t!<\infty\). The pinned Lipschitz identity gives

\[
 \sum_l(w+l)^{-(a+t+1)}
   ={(-2\pi i)^{a+t+1}\over(a+t)!}\sum_{h\ge1} h^{a+t}e(hw).
\]

For the next interchange take \(\beta=\pi\Im w>0\) and bound \((\beta h)^t/(a+t)!\le e^{\beta h}\). The two remaining majorants are factorial in \(t\) and \(h^ae^{-\beta h}\) in \(h\). The coefficient at \(h\), after taking out the endpoint phases \(e((mA+hD)/C)\), is

\[
 C^{-k}\sum_{t\ge0}{V^t(-2\pi i)^{a+t+1}h^{a+t}\over t!(a+t)!}
  ={2\pi i^{-k}\over C}
         \left({\sqrt h\over\sqrt m}\right)^a J_a(4\pi\sqrt{mh}/C).
\]

This is the literal alternating factorial series of the existing \(\mathtt{generalJ}\). The fixed coefficient can be extracted through the \(C\)-sum using (5) at any positive height. Independently, \(J_a(t)=O_{a,m,h,N}(t^a)\) for \(0\le t\le4\pi\sqrt{mh/N}\); with \(a\ge1\) this bounds the absolute modulus series in (1) by a constant times \(\sum_d B_m(d)/d^2\). Combining the coefficient with (2) gives (1).
