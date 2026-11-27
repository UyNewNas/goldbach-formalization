# Original U5 lower tree, finite differences and a positive ordinary term

The manuscript pin is `UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`, under `paper/release-20261106/en/`. The local Git blob IDs are `4513d5d4887f1450ffb0e5cd23ae4beb0c3372f6` for `sieve-appendix.tex`, `76c890d8e5afed69dde968cc9cdbef1c9334f721` for `numerical-appendix.tex`, and `6dc573201b74d0fef8021ebea20889de09d1a20b` for `argument.tex`. The Lean comparison starts at `UyNewNas/goldbach-formalization@f7e0304fc866485eb5784ef7f4dc540b43f44872`. This review states the mathematical contracts. The continuation ledger and verification receipts record their implementation status.

## The finite identity

Write $a=417/5000$, $z=N^a$, and $B=p_1p_2$ for an original ordered pair. Its initial cap is $C_0=V(\log_N p_2,\log_N p_1)-2b$. Here $V(t,u)$ uses the larger prime first in the manuscript notation. The Lean dictionary `level u t` takes the smaller coordinate first. The finite selector includes its lower cutoff and uses a strict upper cutoff. The limiting triangle in Numerical Appendix lines 391–411 differs on its null lower face. Those lines give the two-mark root and distinguish the ordinary term from the admitted defect. The ordinary lower changes occur after admission at full ranks 3, 4 and 5. The fourth changes the continuation only after the incoming even cube passes. Fourth-prefix restoration makes a separate pre-cube change on a rejected prefix. Sieve Appendix lines 358–382, 383–402 and 483–492 give the relevant timing and signs.

For $k=1,2,3$, let $\mathcal F_k$ be the list of admitted rough prefixes at selected depth $k$ in the literal `evenFirstExitPolicy (selectedPolicy R bank b false N t)`. Its carrier consists of target-deleted primes strictly below $z$, with lower cutoff zero and the chosen enumeration cap. For the even targets of the manuscript this also excludes 2, as in Sieve Appendix line 222. The combinatorial Lean identity allows every $N\ge2$. For a prefix stored newest first, $H=[q_k,\ldots,q_1]$, put $d_H=\prod_{i=1}^kq_i$, $q=q_k$, and $w_H=\prod_{i=1}^k(q_i-1)^{-1}$. Write $C(H)$ for the cap after accepting $H$, and $C(H^-)$ for the cap at its tail $H^-=[q_{k-1},\ldots,q_1]$. For both levels keep the *complete* rough prefix in the residual divisor,

$$
Q_o=N^{C(H^-)}/(Bd_H),\qquad Q_n=N^{C(H)}/(Bd_H).
$$

Let $D^\pm(q,Q)$ be the literal ordinary Rosser density below the strict prime ceiling $q$, with the same target and enumeration cap. The three corrections use the following summands.

| $k$ | Full rank | Summand for $H\in\mathcal F_k$ |
|---|---|---|
| 1 | 3 | $w_H[D^+(q,Q_o)-D^+(q,Q_n)]$ |
| 2 | 4 | $w_H[D^-(q,Q_n)-D^-(q,Q_o)]$ |
| 3 | 5 | $w_H[D^+(q,Q_o)-D^+(q,Q_n)]$ |

With $\Delta_k$ the sum of its row in the table, the retained polynomial is exactly $D^-(z,N^{C_0}/B)+\Delta_1+\Delta_2+\Delta_3$. For the canonical enumeration cap $\lceil z\rceil$ this is `P5OriginalU5CausalFinite.fullDensity` of the selected policy. Indexing by the actual prefix list preserves multiplicities, and a frozen inherited action has identically zero difference. Replacing the level for the first $k-1$ stages by its actual value and then freezing gives four finite polynomials. Adjacent polynomials agree above their common admitted $k$th frontier. Terminal summands cancel. The frozen-frontier identity gives exactly one signed ordinary residual per retained prefix on each side. The accepted incoming gate proves that the final prefix itself is admissible at its old level, and the prefix theorem gives admissibility at its new level. Every subsequent cap after depth three is inherited.

The finite tree suppliers are `P3OriginalU5WarmRosserAdmission` (`rowLevel` and the two public admission theorems), `ImbalancedChen.firstExitRetainedPolynomial_frozenParity_splice_sub_eq_density_sum` in `ActualFrozenFrontierDensity.lean`, and `ImbalancedChen.evenFirstExitRetainedPolynomial_eq_fixedEvenRoughDensity` in `FixedEvenRoughCoefficients.lean`. The continuation source is `P3OriginalU5ThreeFrontierIdentity`. The paper's subtree summation is explicit at Sieve Appendix lines 55–79, 124–128 and 445–463. The three integral signs and the dependence on the inherited fourth cap appear at Numerical Appendix lines 473–512. The scalar $\nu$ in those unmarked reference integrals is replaced here by the literal two-mark starting cap.

## Which sign comparison enters the proof

A true fresh action increases $C(H)$ by `P2OriginalPairSourceReceiver.freshCheck`. The finite identity above is an equality between signed numbers. Sieve Appendix lines 220–251 and 483–492 evaluate the two literal residuals separately. The nonnegative gains displayed at Numerical Appendix lines 490–512 are integrals of the limiting factors.

Cap order alone cannot prove a sign for every finite polynomial covered by the combinatorial first-exit identity. For example, take the upper ordinary tree on $\{3,5,7\}$ and a multiplicative test weight $\xi(p)=3/4$. Increasing the level from $343$ to $344$ admits the prefix $7$; its continuation includes $5$ and $3$ singly, while $7\cdot5\cdot3^3>344$ excludes their joint choice. The *upper* polynomial increases by $-(3/4)(1-3/4-3/4)=3/8$. This example concerns the generic multiplicative test. For the physical Goldbach weights the argument below establishes the required one-sided estimate by uniform approximation and pays its error.

## Uniform comparison on a changed prefix

Fix the receiver $R$ and let $d=R.\mathrm{epsilon}>0$. The bounds below hold simultaneously over all meshes and candidate banks. If the least rough coordinate $u=\log_N q$ is below $d$, `exponentCode` returns `none`, whose box upper endpoint `qHi` is $59/250$. The two original marked upper endpoints each dominate $a$. Every earlier rough upper endpoint is nonnegative. A successful `select` supplies `sourceCheck`, so its last full-square test would force

$$
2a+2(59/250)=1597/2500 < \mathrm{rowCap}\le153/256 .
$$

The left rational is larger than the right rational. Thus a changed frontier has $d\le u<a$, with every earlier rough prime in the same half-open band $[N^d,N^a)$. The upper cap holds on an actual fresh action. This reasoning uses the source square evaluated on the rounded *box* exponents, since the physical least exponent may be below the receiver's mesh.

Write $O=\log_N Q_o$ and $M=\log_N Q_n$. Then $O\le M\le1$. At rank 3, $O=C_0-\log_N B-u$, and $C_0-\log_N B\ge34/125-2/1000>3a$ for the working buffer. At rank 4 the incoming cube gives $O>2u$. At rank 5 let $v$ be the preceding rough coordinate. The preceding even cube and cap inheritance give $O>2v-u>u$. Hence every changed odd frontier satisfies $u\le O$, and the changed even frontier satisfies the stronger $2u\le O$.

For a fixed $d>0$ and any error $\eta>0$, a sufficient supplier gives a single threshold for all $d\le u\le O\le M\le1$ and all enumeration caps covering $N^u$. For even $N$ above that threshold it gives

$$
D^+(N^u,N^O)-D^+(N^u,N^M)\ge-\eta C_N/\log N
$$

and, when $2u\le O$,

$$
D^-(N^u,N^M)-D^-(N^u,N^O)\ge-\eta C_N/\log N .
$$

For the lower difference, use the uniform two-sided compact estimate at $(u,\beta/u)$ and monotonicity of $f$ for $s\ge2$. For the upper difference, put $u_\beta=\min(u,\beta/3)$ and $s_\beta=\max(3,\beta/u)$. The strict first-cube identity changes the cutoff to $N^{u_\beta}$ *exactly*, and $s_\beta u_\beta=\beta$. This places each pair in a single rectangle $d/3\le u_\beta\le1$, $3\le s_\beta\le\max(3,1/d)$. Both coordinates are nondecreasing in $\beta$. Since $F\ge0$ and $F$ is decreasing in the weak sense, $(2e^{-\gamma}/u_\beta)F(s_\beta)$ is nonincreasing. This argument covers an old or new ratio at one and a change straddling three. Take two errors of $\eta/2$ before subtracting.

The local sources are `ActualRosserResidualDensity` (the pair of compact normalized thresholds), `ActualRosserCubeReduction.lean` lines 88–96 (the exact cutoff move), `ActualThirdPrefixTailIntegralCore.lean` lines 110–130 (lower factor monotonicity) and the odd source-layer argument in `ActualSieveGapTailDecay.lean` lines 48–64 (upper factor antitonicity). `P3OriginalU5ResidualComparison` states the joint comparison, including the original upper endpoint. No hypothesis imports a sign comparison for the finite raw densities.

## Payment and positivity at the original scale

1. For fixed $R$, put $e=\min(d,a/2)$ and $K_R=\exp(1+\log(a/e))$. The total $w_H$ on the changed histories at *each* depth is eventually at most $K_R$. To see this, give each enumerated prime the weight $g(p)=(p-1)^{-1}$ on the target-deleted band $[N^d,N^a)$ and zero elsewhere. Each changed history keeps its full weight. A skip-or-select induction on the same admitted tree bounds the sum at every fixed depth by $\prod_p(1+g(p))\le\exp(\sum_p g(p))$. The sum is bounded by the mass on $[N^e,N^a)$, which tends to $\log(a/e)$ by `tendsto_actualPrimeReciprocalMass`. This argument allows arbitrary prime enumeration caps. It retains history multiplicities without identifying the admitted carrier with a candidate family before its gate. The source contracts are `FirstExitFrontierWeightBound.exists_frontier_window_weight_bound` and `P3OriginalU5ChangedFrontierSupport.eventually_original_U5_changedMass_le`.
2. For every original marked pair, the initial buffered residual exponent lies in $[34/125-2/1000,2083/5000]$ for every $0\le b\le1/1000$. Its ordinary ratio lies in $[3,5]$. The compact lower-density estimate and $f(s)\ge f(3)=2e^\gamma\log(2)/3$ give, for instance, the uniform positive row lower constant $c_0=2\log(2)/(3a)$ in units $C_N/\log N$. The rectangle $[1/10,11/100)\times[3/25,13/100)$ belongs to the original marked selector and has limiting reciprocal-totient mass $m=\log(11/10)\log(13/12)>0$. Strict ordering and $\varphi(p_1p_2)=(p_1-1)(p_2-1)$ identify this exact mass. `P3OriginalU5OrdinaryRootDensity` uses the original total pair denominator, the moving buffered level and this positive rectangle. The root positivity is independent of receiver selection.
3. Take $\eta=c_0/(6K_R)$ in the residual comparison. Each of the three losses is at most $\eta K_R C_N/\log N$ because its error is multiplied by the actual nonnegative changed weight. Combine the three bounds with the exact identity. Each selected-policy row is eventually at least $(c_0/2)C_N/\log N$ uniformly in the original pair. Multiplying by the positive reciprocal-totient weights of all original pairs gives the concrete sufficient bound $(c_0m/4)C_N/\log N$ once the rectangle mass reaches $m/2$. This step only needs an upper estimate for the active frontier weights. The order of quantifiers fixes $R$ and its cutoff $d$ before the common threshold. The two source contracts are `P3OriginalU5SelectedDensityLower.exists_original_U5_selected_row_lower` and `P3OriginalU5SelectedDensityLower.exists_original_U5_selected_pair_lower`.

Let $c>0$ be the selected-pair lower constant and set the normalized density reserve $\kappa=c/2$. For every mesh and upper tolerance $\varepsilon_{\max}>0$, `P3OriginalU5PairNormalizedDensityReserve.exists_rounded_U5_pair_normalized_density_reserve` supplies one $0<\varepsilon<\min(1/8,\varepsilon_{\max},1/272)$, one $\tau_0>0$ and one threshold. For every large even $N$, every bank at that mesh and every $0<\tau\le\tau_0$, the literal signed double sum of `roundedRho` over the original pairs and rounded support, divided by $\varphi(\mathrm{fullModulus}(t,k))$, is at least $(c/2)C_N/\log N$. Every nonzero coefficient in these same rows has $\mathrm{fullModulus}(t,k)<N^{599/1000}$. The buffer in both statements is $1/1000$. The source contract is `P3OriginalU5PositiveRoundedDensity.exists_original_U5_positive_rounded_density`.

The unrounded and rounded lower bounds concern ordinary signed densities. The enhanced $h_{248}$ term requires count estimates for the fully admitted marked families in Numerical Appendix lines 396–411 and Argument lines 635–649. Common physical levels and the matching signed prime-product discrepancy have the separate requirements in Argument lines 98–141 and Sieve Appendix lines 496–531 and 1090–1101. A positive total pair mass alone supplies neither the mass of a requested sparse subfamily nor a discrepancy estimate for its rounded coefficient.
