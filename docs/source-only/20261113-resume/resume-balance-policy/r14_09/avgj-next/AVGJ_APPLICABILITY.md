# P3.5, Medium §10(vii), on the original moving-residue data

**The paper's call to Theorem J is valid on the m side.** On the n side the coefficients genuinely depend on the level. The formal library supplies the native m-side DFT and a uniform fixed-level sieve. The two Lean files here use them to prove the initial level-average bound and to pay the entire reduced n square in the two-sided Cauchy product. The full m-side mean at the physical weight is still required for (24). All new results are source-level, without elaboration or kernel acceptance. [Medium §§7,10, lines 349–380 and 463–483](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/paper/source/modules/distribution-medium-completion-20261010.txt#L349) · [Pascadi v3, Theorem J, (3.34)–(3.35)](https://arxiv.org/html/2404.04239v3#S3.SS4)

## Two distinct coefficient sequences

Fix the original data, completed prefix mark, primary key $(\nu,U,\text{sign})$, physical $Z$ chart, one of the six smooth scales, Poisson sign and dyadic $V=2^j$. The global integer cutoff $J$ is chosen before $z$. The original signed $y$ has $|y|=\nu n$ with $n>0$. Write $e(t)=\exp(2\pi it)$, $G=|a|\nu$ and $s=\pm1$ for the composite sign from the residue, $y$ and Poisson sign. The common Poisson block is $I=[V,\min(2V,J+1))\cap\mathbb N$. Negative Poisson frequencies transfer the minus sign to the other Fourier argument by the Kloosterman substitution $u\mapsto-u$. The infinity argument remains positive in both branches.

The four normalized variables are $t,v=m/V,w=\nu n/U,\zeta=z/Z$ with $c/C=\sqrt{vw/\zeta}/t$. Thus the four-coordinate periodic extension is the same for the whole fixed chart. At each mark $\ell\in\mathbb Z^4$ its scalar Fourier coefficient is independent of $(z,n,c,m)$. The test is $\chi(q/Y_0)e(\ell_0 q/(64Y_0))$, where $Y_0=4\pi\sqrt{|a|VU}/(C\sqrt Z)$. The positive physical support and the outer normalizations $D/C$, $C\sqrt Z$ are those of (P0)–(P6). With the native convention putting the conjugate on the m functional, the two actual functionals before oldform removal are

$$
 M_{z,i}=\sum_{m\in I}e(-\ell_1m/(64V))R_{z,i,\infty}(m),\qquad
 N^{\rm raw}_{z,i}=\sum_{n\in\mathcal N_z} b_{z,n}\,
          e(-sGn/z)R_{z,i,1}(sGn),
$$

where

$$
 b_{z,n}=\mathrm{blockBeta}(z,y)\,
           e\left(\frac{\ell_2\nu n}{64U}+\frac{\ell_3z}{64Z}\right).
$$

The upper/lower chart before recasting level endpoints is $Z=S^2$ or $2S^2$. The one-bounded alignment of the original kernel at $(z,y)$ and the earlier scalar prefix coefficient live in the original coefficient construction and outer sum. The row multiplicities are already inside $\mathrm{blockBeta}$, and $z=s_1s_2$ is a single level in the quadratic sum. Neither the $z$ Fourier phase nor an alignment phase needs to move onto $M_{z,i}$. The Cauchy product may absorb any separate scalar level weight into the n functional, squaring its absolute value there. For the displayed physical row the named n coefficient already contains the level phase, and the user-facing bound below has no extra level weight. [Original (P4)–(P6) and the signed cusp conversion](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-S1-Poisson-spectral-return-20261010.txt#L153)

The support enforces $(a,z)=1$, $(n,a)=1$, $\nu\mid a^\infty$. Thus $(n,G)=(G,z)=1$. The geometric condition is $(c,z)=1$. In ABL's notation $q=1,r=z,s_{\rm ABL}=1$, the character is trivial, the newform level $q_f\mid z$, and a legal dilation $d\mid z/q_f$. The cofactor $z/\gcd(dq_f,z)$ divides $z$ and has no prime factor of $G$. Consequently ABL's $K$ equals 1 for each $d$. Lemma 3.1 in $R(n)=\sqrt{|n|}\rho_{\rm ABL}(n)$ normalization gives

$$
 R_{f_d,1}(sGn)=\lambda_d(G)e(s(G-1)n/z)R_{f_d,1}(sn).
$$

Both signs give the residual functional

$$
 N_{z,i}=\sum_{n\in\mathcal N_z} b_{z,n} e(-sn/z)R_{z,i,1}(sn),\qquad
 B_z^2=\sum_{n\in\mathcal N_z}|\mathrm{blockBeta}(z,y)|^2.
$$

Here $\lambda_d$ can depend on $d$. Within an eigenpacket all vectors have the same eigenvalue. Squaring the orthonormal combination, using (3.3) and the unit norm of each dilation, and restoring an orthonormal basis by positivity costs $\ll_\delta(zG)^\delta G^{7/32}$ for the **squared** norm after allowing divisor losses. Only the n norm undergoes this operation. In particular the rigorous route bounds the product of the m and n norms after Cauchy. A bound on the new sum of matched-coordinate products alone would not imply that product bound. The earlier raw sum and the diagonal sum of reduced products need no asserted equality. ABL explicitly repeats the reduction for the exceptional quadratic form after (3.8). The step uses the finite-place Hecke bound and the actual oldclass basis. ABL's argument for continuous channels is distinct and already has its own installed candidate. [Assing–Blomer–Li, (3.3) and Lemma 3.1](https://arxiv.org/pdf/2005.13915v1#page=8) · [Exceptional quadratic form and its reduction, p. 11](https://arxiv.org/pdf/2005.13915v1#page=11)

## Theorem J at the manuscript parameters

For Pascadi the scaling matrix is the identity, $\omega\in\mathbb R/\mathbb Z$ is independent of the level, and $M,Q\ge1/2$. T08 uses $\rho^K=2R$ and $\tau=2\sqrt{1/4-\lambda}$ on the full strict exceptional native ONB. Thus its complete sum $\mathrm{pascadiJ}$ is four times the complete $R$-coefficient sum. A different orthonormal basis at fixed eigenvalue gives the same sum of squares. The positive $1/\cos(\pi\tau/2)$ in the original trace is uniformly bounded using the actual archimedean gap (or Selberg's weaker uniform gap for this particular denominator). Positivity $\lambda>0$ by itself only gives a level-dependent reciprocal bound. Theorem J itself uses no cosh denominator. Pascadi's proof of Corollary 17, especially (5.34) and its two subsequent displayed sums, makes exactly this separation of a common infinity sequence from level-dependent coefficients and level weights. [Pascadi, Theorem J](https://arxiv.org/html/2404.04239v3#S3.SS4) · [Pascadi, proof of Corollary 17](https://arxiv.org/html/2404.04239v3#S5.SS3)

For $M=V-1/2$, $(M,2M]\cap\mathbb N=[V,2V)\cap\mathbb N$, including $V=1$. The phase denominator stays $64V$. The common clipped prefix has period $P=4V+1$ in T08's finite completion. Its normalized DFT coefficients $c_h$ have $\sum_h |c_h|\le 2+\log P$. On the entire set of $(z,i)$ coordinates the same identity is

$$
 M_{z,i}=\sum_{h\bmod P}c_h
       \sum_{m\in [V,2V)}e\left(m\left[-\ell_1/(64V)+h/P\right]\right) R_{z,i,\infty}(m).
$$

Minkowski on the weighted Hilbert sum costs $(2+\log P)^2$ in the squared norm. The maximizing $h$ can depend on the full chart and $\ell$. It is picked once for all levels, both printed level intervals and all multiplicities. The closed physical plateau $Z\le z\le 2Z$ is covered by $(Z/2,Z]$ and $(Z,2Z]$. Enlarging the physical subset after the sum becomes nonnegative preserves the inequality; this operation introduces the missing levels, including noncoprime ones, on the m norm alone. The other norm retains its original coprime levels.

Set $W=\max(V,Z^2/V)$ and $L=U/\nu$. Q20 proves $W\le4\max(M,Q^2/M)$ for both $Q=Z/2,Z$. Thus Theorem J (3.34) bounds each full m energy at $W$ by $C_{\delta,4}(QM)^\delta(Q+M)M$, uniformly in the chart, phase and level. These parameters give the paper's full permitted range. For the other norm use $Y_n=2+Z/L$, for which $Y_n\le3\max(1,z/L)$ on occupied levels. The published fixed-level estimate yields

$$
 \sum_{i\in E_z}Y_n^{\tau_{z,i}}|N_{z,i}|^2
 \le4 C_A(1+L/Z)B_z^2,
 \qquad C_A=32/c_{\rm probe}^2 .
$$

This use needs only the proved fixed-level range. It avoids any appeal to the stronger optional fixed-level $z^2/L^3$ term. When the weight generated by $Y_0^{-1}$ exceeds $W$ after splitting with $Y_n$, the primary sources use the independently required gap $\tau\le7/32$ to bound $(Y_m/W)^{\tau}$ by $\max(1,(Y_m/W)^{7/32})$. The high-weight transport has its own explicit loss. The preceding two full m sums are precisely the unpaid analytic term when passing from the new Lean inequality to this paper conclusion.

The unweighted Fourier-coefficient sum in (P6) must incorporate the fixed Bessel derivative order. With four derivatives, the production bound gives $W_4\ll x^{28\eta}$, $W_4^2\ll x^{56\eta}$ when $\rho\le x^\eta$. The cutoff enlargement costs at most another $x^{2\eta}$ at the squared stage. For the tight occupied families $S\le2x$, $Q\le2S^2\le8x^2$, and, for $0<\eta\le1$ beyond the common cutoff threshold, $M\le V\le x^\eta S\le2x^2$. Then $(QM)^\delta\le16^\delta x^{4\delta}$. For a prescribed squared allowance $0<b\le\min(1,\epsilon,\sigma/10)$ one can reserve $b$ for these J/separation steps, choose $\eta=b/232$, $\delta=b/16$, and allow the remaining $b/2$ for the squared logarithm and constants at one sufficiently large $x$. Other packet/divisor/oldform and polynomial-scale costs require their own allocated allowances. The Fourier derivative order and ambient polynomial exponents precede these choices. The tail order can subsequently grow with $1/\eta$. All constants and the final threshold precede moving $a$, levels, frequencies, cutoffs and sources. The argument allows polynomial $|a|$ (including $a=N$ in the stated original range), so it never uses a theorem whose constant depends on the chosen residue. [Original parameter choices (P5)–(P8)](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/9731290e8f53cffda44129906cde6a965eaa869b/proof-library/source/lichtman-S1-Poisson-spectral-return-20261010.txt#L298)

## What the new Lean source proves

1. `Part3OriginalExceptionalJInitialAverage.signed_row` reindexes the untouched fixed-level bound at signed indices $s n$, using $|sn|=n$ and injectivity on the genuine positive support. It converts the whole-basis summable expression to the native finite strict exceptional spectrum by positivity. `initial_average` proves on T08's actual full level and eigenspace sum

   $$
   \mathrm{pascadiJ}(Q,X,j,\omega)
    \le16C_A(1+\max(1,A))(Q+M)M,
   \quad 0<X\le A\max(1,Q/M).
   $$

   Here $M=2^j-1/2$, $Q\ge1/2$, $A\ge0$. The constant precedes $Q,j,X,\omega$. There are at most $2Q$ levels and $2M$ frequencies. The factor four from $\rho^K$ is included. In particular this supplies the initial weight $X=1$, $A=1$ on precisely the norm required in the level-switching induction.

2. `Part3OriginalExceptionalPostRemovalPair.reduced_row_square` instantiates the same finite sum at cusp one with the original signed reduced row. It uses the genuine $\nu n$ support, the original modulated coefficient, and $|e(-sn/z)|=1$. In `original_pair_to_pascadi`, $F_{z,i}=W^{\tau/2}|M_{z,i}|$ and $G_{z,i}=Y_n^{\tau/2}|N_{z,i}|$ (the code writes the positive square roots). On the union of the occupied pieces it gives, for one $\omega$,

   $$
    (\sum FG)^2\le(\sum F^2)(\sum G^2)\le
    (2+\log(4V+1))^2\frac{J_{Z/2}(W,\omega)+J_Z(W,\omega)}4
      \;4C_A(1+L/Z)\sum_z B_z^2.
   $$

   Every $J_Q$ on the right is the already defined full `pascadiJ`. This is an unconditional inequality on the reduced coefficient pair. The proof takes no full-J premise, no spectral character-removal identity, no numerical gap hypothesis, and no equality between the reduced product and the raw trace. The raw discrete ABL conversion and the quantitative $J_Q(W,\omega)$ are independent parents.

## Full-range source obligation and prior-source map

The small-weight result cannot be extended to the claimed threshold by calling the same statement with a variable $A$. Already $M\asymp Q\to\infty$ gives $\max(1,Q/M)\asymp1$, whereas $\max(M,Q^2/M)\asymp Q$. Even in the physical scale comparison $V\asymp S$, $Z\asymp S^2$, the initial and desired weights scale as $S$ and $S^3$. This shows the difference between the two permissible weight ranges. A pointwise upper bound on $\tau$ moves the loss into a positive power of that ratio.

The classical proof calls for all-level diagonal $\infty,\infty$ input, with $c$ a multiple of $q$. Drappeau (4.29) switches the level range to one near $\pi MX/Q$ (trivial character). It requires uniformity for Mellin-twisted coefficients and a different smooth diagonal test from the manuscript's mixed-cusp test. Equation (4.30) initiates the improved interval estimate by opening both short exponential sums at inverse residues mod $c$ and averaging over their modulus. The common additive phase transfers to the two opposite shifts in those sums. The initial strong bound and the level-switching recurrence yield the optimal range by induction. Drappeau's compact proof says explicitly which parts of DI it uses, including the bound for the sum of the inverse-residue products in Proof 4.7 and the induction in Proof 4.8. Pascadi's own Theorem J supplies the requested uniform $\omega$ including all real shifts. A finite Bessel inequality at individual levels only supplies the initial estimate above. The regular sieve, the existing prescribed $\infty,1$ six-scale identity and a coprime oldform reduction individually lack these diagonal level-switching and inverse-pair estimates. [Drappeau, §4.2, (4.29)–(4.30) and proofs](https://arxiv.org/html/1504.05549v4#S4.SS2) · [Deshouillers–Iwaniec, Inventiones 70](https://doi.org/10.1007/BF01390728)

The published source through `d4e47591d188d01a440f24fc3e612b3515cefd4d` was searched by filename and content in the read-only Git mirror, and checked against the 38-checkpoint synchronization inventory. The only Lean blob matching `pascadiJ` or `original_chart_J_one_phase` there is the T08 finite completion. No unconditional full-range DI/Deshouillers–Iwaniec supplier on the named coefficients, or equivalent level-switching and inverse-pair proof, was identified in the audited sources. The printed theorem is a legitimate paper-level input. Its formal proof, the discrete oldclass realization and the quantitative gap remain substantial formal obligations. The common-m/signed-n split is an exact reconstruction in the paper, not a manuscript-level gap.

| Reused source on the publication branch | Exact role |
| --- | --- |
| `20261102-resume-30q/automorphic_dictionary/Part3OriginalTwoZFourierAssembly`, `original_chart_atom_hasSum`, `chart_hasSum`, `norm_modulatedBeta` | Whole fixed-chart separated series, with all original weights and the norm of modulated beta |
| `20261102-resume-30q/actual_spectral_energy/Part3OriginalClassicalSpectralSupports`, `commonPoissonCompleted_classical_support`, `original_J_threshold_comparison` | Corrected printed $M,Q$ and threshold comparison |
| Same directory, `Part3OriginalRowOldformArithmetic`, `original_index_coprime_abl_argument`, `original_abl_argument_coprime_level`, `original_oldformExceptionalInteger_eq_one` | Exact coprimalities and $K=1$ on actual rows |
| `20261102-resume-30r/oldform_continuous/Part3OriginalPrincipalTraceRow`, `principalTraceSign_cases`, `traceIndex_eq_principalTraceSign`, `traceBeta_eq_principal_phase` | Exact composite sign and pre-removal phase |
| `20261102-resume-30s/S/s20_normalized_kuznetsov/Part3OriginalNativeCuspFunctionals`, `originalMFunctional`, `originalNFunctional`, `original_native_row_product` | Common infinity mark and the original signed composite cusp-one mark on the same native basis |
| `20261110-yellow-closure-10t/t08_actual_spectral_supplier/Part3OriginalExceptionalJNativeCompletion`, `original_M_eq_shifted_full` (145), `pascadiJ_eq_four_mul` (207), `native_common_interval_completion` (236), `original_chart_J_one_phase` (351) | Existing common-interval DFT and genuine Hilbert/Minkowski bound. Its conclusion still explicitly contains the full energies. No J or ABL premise in that theorem |
| Same T08 directory, `Part3OriginalContinuousClassRemoval.reduced` and `Part3OriginalCumulativeContinuousRemoval.original_cumulative_removal` | The first defines the exact Fourier functional for every $R:\mathbb Z\to\mathbb C$ (a map $(\mathbb Z\to\mathbb C)\to\mathbb C$). Only this definition is reused on discrete $R$. The second applies to the continuous spectral measure |
| `20261113-resume/r13_04/fixed-level-a/Part3OriginalFixedLevelExceptionalSieve.manuscript_range` | Published seven-source result at its stated range, reused directly |
| `ImbalancedChen/Part3ZExceptionalThresholdGeometry.spectral_tau_weight_le` and `Part3ActualWeightedSpectralBudget.actual_uniform_xeta_weighted_budget` | Prior threshold-power algebra conditional on the eigenvalue lower bound, and a separate genuine Fourier seminorm budget |

Original final obligations for all-cost $7/32$, (24)/(25), regular estimates, the pre-removal cuspidal ABL step and whole PP retain their stated scopes. No local compiler, Lake, LSP, proof program, runtime fixture or certificate was executed.
