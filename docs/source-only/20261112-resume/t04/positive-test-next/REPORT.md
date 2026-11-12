# The prescribed positive-sign Bessel weights

Nine source files give the even-weight transform and the regular and complementary Maaß weights for the paper’s original period-64 test at every positive scale. The original marked Maaß sum and the continuous integral converge absolutely. The preceding source for all six scale pairs retains its full positive arithmetic term. These files have source-only status and zero formal credit. Kernel checking and the inherited supplier staging remain open.

The paper uses the trivial character, weight zero, the original infinity and one observation frames, and every singular incoming cusp of the same level. The arithmetic parameter $s=1$ still leaves an occupied positive Poisson branch whenever the original joint coefficient and common marking are occupied. The positive formula in Drappeau (4.13) has a holomorphic, a Maaß and an Eisenstein term. Formulae (4.9), (4.10) and (4.15)–(4.17) fix the Bessel factors below. [Manuscript §10](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L463) · [Classical correspondence](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/final-classical-input-correspondence-20261010.txt) · [Drappeau, pp. 11–12](https://arxiv.org/pdf/1504.05549v4#page=11)

## The archimedean factors

For even weight $k=2j+2$ write $n=2j+1$. The moment is $m_n=\int_0^\infty J_n(q)\Phi(q)\,dq/q$ and $\dot\Phi(k)=4i^km_n$. The Gamma-series coefficient bound gives $|m_n|\le C_{\ell,Y}(8Y)^n/n!$. The actual three-term recurrence implies absolute convergence and the exact identity

$$
\sum_{j\ge0}(2j+1)\dot\Phi(2j+2)=-2\int_0^\infty J_0(q)\Phi(q)\,dq .
$$

For the original zero Fourier marking and $(8Y)^2\le(n+1)/4$, the real part of the defining integral is strictly positive. The Bessel series tail is bounded by one third of the positive leading term throughout the support, and the cutoff equals one on $(Y,2Y)$. Thus these positive-sign holomorphic test weights occur already on a prescribed test. The corresponding cusp-form coefficients and their sum require their own Petersson calculation.

For real $t$ the source proves

$$
\widetilde\Phi(t)=2\pi i\int_0^\infty
\frac{J_{2it}(q)-J_{-2it}(q)}{\sinh(\pi t)}\Phi(q)\,\frac{dq}{q}
=8\int_0^\infty P(u)\cos(2tu)\,du ,
\qquad
P(u)=\int_0^\infty\cos(q\cosh u)\Phi(q)\,\frac{dq}{q}.
$$

At $t=0$ the kernel is $-8\,\partial_\nu J_\nu(q)|_{\nu=0}$. The two principal-slit values $K_{2it}(\varepsilon+iq)$ and $K_{2it}(\varepsilon-iq)$ give the regularized physical integral. At each positive $\varepsilon$, a product of two actual $L^1$ majorants proves Fubini. The compact $q$ support and the integrability of $\cosh u\,|P(u)|$ permit the two limiting integrals as $\varepsilon\downarrow0$. The even profile $P$ is Schwartz. Its derivatives have the form $A(\cosh u)+\sinh u\,B(\cosh u)$ with Schwartz functions $A,B$. The second Fourier transform gives a Schwartz representative for $\widetilde\Phi$ with the full-line frequency $t/\pi$ in the library’s convention. Consequently each fixed marking and scale has all polynomial decay bounds.

For $0<\alpha<1/2$, the same calculation gives $8\int_0^\infty P(u)\cosh(2\alpha u)\,du$. Its physical numerator is $2\pi[J_{-2\alpha}-J_{2\alpha}]/\sin(\pi\alpha)$. On the earlier exceptional budget’s range the kernel is exactly minus four times its Pascadi-normalized kernel at order $2\alpha$. Strict positivity of the original native cuspidal eigenvalues and finiteness of their fixed-level sublevel $λ\le1/4$ give $\cos(\pi\alpha)>0$ separately at every complementary parameter. These facts enter the absolute convergence proof. [Original native exceptional indices](https://github.com/UyNewNas/goldbach-formalization/blob/f16653991419f0d20e64d8639a102833683d9794/docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier/Part3OriginalExceptionalJNativeCompletion.lean)

## Original markings and remaining positive trace

The last source uses the original $M,N$ on both observations, with the complex conjugate on $M$. The continuous term retains the full real line and the factor $1/(4\pi\cosh\pi t)$ exactly once. The fixed-level unit-band mass bound and the fifth Schwartz bound give an integrable continuous majorant and a summable regular cuspidal majorant. The complete multiplicity index supplies a finite complementary sum at this level. The same $r,k,z,J,j,\ell$, phase, scale, row and Poisson arguments used by the original caller remain explicit. [Original six-scale caller](https://github.com/UyNewNas/goldbach-formalization/blob/f16653991419f0d20e64d8639a102833683d9794/docs/source-only/20261112-resume/t04/prescribed-trace-next/Part3OriginalSixOppositeSpectrum.lean)

Write $D=\delta_{z=1,p=h}(2\pi)^{-1}\int J_0\Phi\,dq$. With the physical Petersson factor $4\pi\Gamma(k-1)$, the identity above places $-D$ in the spectral holomorphic term when it is expanded geometrically. Solving for the geometric holomorphic summand would give $G_{\mathrm{hol}}=H+D$. The complementary geometric positive-sign term still needs the physical equality $G_{\mathrm{rem}}=M+E-D$, including its actual fixed modulus sums and spectral limits. The previous opposite-sign Gaussian lift has phase involving $\sinh w$. The positive-sign phase involves $\cosh w$, and a fresh construction of the complementary test is required. The complete positive trace in all six scale pairs, its regular and exceptional uniform level costs, and the final $7/32$ estimate remain open.
