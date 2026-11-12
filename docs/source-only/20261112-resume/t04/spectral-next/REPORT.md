# P3: removing the contour error in the native zero-mode Gram

This source candidate proves the spatial Gram identity on the smooth compact zero-mode Poincaré generators. It applies at every positive integral level and every pair of integral cusp frames. At fixed level, all incoming cusps appear, with unit leading term, integration over the whole real parameter line (including the central parameter) and the factor $1/(4π)$. No hypothesis supplies a scattering bound, edge limit, residual decomposition or Plancherel identity.

Write $V=P_{h,ψ}$ and $W=P_{g,φ}$ for the **physical** zero-mode vectors in the quotient $L²$ space with its original hyperbolic measure. If $v_{V,a}(t)=∫\overline{V}\,E_a(1/2+it)\,dμ_N$, the candidate gives

$$
\langle V,W\rangle=
\langle V,\operatorname{proj}_{\mathbf1}W\rangle+
\frac1{4π}\int_{\mathbb R}\sum_a v_{V,a}(t)\overline{v_{W,a}(t)}\,dt .
$$

The orientation is for the conjugate-first spatial inner product. The pole at one is the previous physical constant projection, with the same reciprocal quotient volume. The parameters and profiles are arbitrary in the actual native families. No individual Eisenstein series is being placed in $L²$.

**What was missing.** The preceding [seven-file contour packet](https://github.com/UyNewNas/goldbach-formalization/tree/3a46b3f0a4ee8ee7e628c9234717fae03064a52b/docs/source-only/20261110-yellow-closure-10t/t08_actual_spectral_supplier) already had the full-line physical cusp product, both absolutely integrable vertical scalar contours, and their relation to the spatial inner product with a retained limit of a horizontal error. Its critical integrability comes from native scattering unitarity, Schwartz Mellin profiles and the finite cusp sum. Initial integrability comes from original Poincaré Mellin synthesis and Fubini with the majorant from the real-axis absolutely convergent Eisenstein series. Neither premise uses the proposed Gram identity.

**Actual growth estimate.** On $1/2<σ≤3/2$, $|t|≥1$, put $δ=σ-1/2$. The new source proves

$$
δ\,|\Phi_{gh}(σ+it)|\le C_{N,g,h}e^{π|t|},
\qquad δ\,|F_{g,h,φ,ψ}(σ+it)|\le C_{N,g,h,φ,ψ}e^{π|t|}.
$$

Here $F=H_φ(s)(\mathbf1_{[h]=[g]}J_ψ(s)+\Phi_{gh}(s)J_ψ(1-s))$ is exactly the preceding scalar. The constants are calculated or obtained from a compact-set bound on known functions; they are not new premises and need not be uniform in level. For Young’s actual divisor matrix the factor at $p\mid d\mid L$ has norm at least $1-p^{-1}$, uniformly down to $σ=1/2$. The two unitriangular determinants are one. Bounding the adjugate by its finite determinant expansion and retaining the positive lower bound for the level factor controls Cramer’s coefficients. The nonprincipal completed Fourier series has its existing summable K-Bessel envelope on a compact positive height band. For the conductor-one family, the two completed zeta waves are bounded there uniformly in $|t|≥1$: the modified theta kernel is absolutely Mellin integrable at the real strip endpoints, the two endpoint powers dominate every interior power, and the two polar terms have denominator of modulus at least one. The native ordinary prefactor is then the previously proved bound with its **one** factor $δ^{-1}$.

Every native cusp is handled by the finite dilations of its primitive character slots in its actual Young expansion, with the original totient, characters and level factors. Applying the path bound to the normalized height-one horocycle gives the true outgoing coefficient; subtracting the incoming orbit delta costs at most one. The two test Mellin factors are bounded on the strip by their compact log-height support.

**Contour and residue.** The published contour uses the analytically extended $F-r/(s-1)$ where $r$ is the physical residue. That function alone generally has a non-integrable $1/t$ tail in absolute value on an individual side. Use instead

$$
U(s)=\operatorname{reg}(F,r)(s)+r/s
     =F(s)-\frac{r}{s(s-1)}\quad(s\ne1).
$$

The auxiliary pole at zero is outside the entire strip. The singularity at one is removed by the previously computed residue. On both vertical sides the rational term is dominated by $4|r|/(1+t²)$, so each vertical restriction of $U$ is absolutely integrable. Along each horizontal side it obeys the same first-power relative estimate.

For $T≥1$, multiply $U$ by the entire function

$$
G_T(s)=\exp\!\left(\frac{π+2}{T}\left((s-1)^2-\tfrac14\right)\right)
       \left(1+\left(\frac{s-1/2}{T}\right)^2\right).
$$

On a horizontal side $t=±T$, the polynomial is exactly $(δ/T)(δ/T±2i)$, of norm at most $3δ$. The Gaussian has norm at most $e^{-(π+2)T}$. Both weighted horizontal integrals tend to zero, each bounded by $3C e^{-2T}$ on an interval of length one. On the two vertical segments the Gaussian has norm at most one and the polynomial at most five. At each fixed vertical parameter the full multiplier tends to one. Dominated convergence on the growing segments uses $5|U|$, with no extra moment of the smooth tests and no estimate for an isolated $L(1+it)^{-1}$. Cauchy’s formula therefore equates the two **unweighted** integrals of $U$. Applying the finite unweighted rectangle to $U$ makes its oriented flux tend to zero. The correction $r/s$ costs at most $2|r|/T$ on those horizontal sides. This proves that the *original* edge tends to zero for real $T\to+\infty$; the existing physical contour limit gives the displayed Gram.

**Manuscript and remaining work.** The [medium manuscript, §7, lines 349–380](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L349-L380) uses the formal **continuous quadratic form** at level $z$, cusps infinity and one. [Classical correspondence §§2–4](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/final-classical-input-correspondence-20261010.txt) fixes the $R(n)=\sqrt{|n|}\rho(n)$ convention, the signed marked coefficient, a common clipped $m$-interval and a common additive phase. [Young §8](https://arxiv.org/html/1710.03624v2#S8) gives the orthogonality correspondence; [Drappeau §4](https://arxiv.org/pdf/1504.05549v4) and [Pascadi §3](https://arxiv.org/html/2404.04239v3#S3) give the trace and large-sieve conventions. This candidate proves a genuine spatial generator identity relevant to that input. It does not yet identify the extended spectral transform of the nonzero marked $M,N$ packets with their literal compact spatial Eisenstein pairings, nor prove the signed geometric trace for the manuscript's physical test. The discrete oldform norms, absolute regular and exceptional sieves, Kim–Sarnak uses and full-cost uniform $7/32$ estimates remain separate. No parent yellow is discharged.

The five Lean files were statically reviewed; independent source review began before freeze. No local Lean, Lake, LSP, staging, guard, numerical witness or CI execution was performed. No kernel/green credit. The exact files, direct import source pins and existing transitive staging holds are in REGISTRY.json.
