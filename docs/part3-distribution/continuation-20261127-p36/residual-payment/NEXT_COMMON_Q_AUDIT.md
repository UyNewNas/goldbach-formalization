# Original U5 physical levels and signed rounded atoms

The 1106 source is the English release at `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`. The finite policy, level, residual and endpoint requirements appear in `coefficient-appendix.tex` lines 14–125 and `sieve-appendix.tex` lines 496–531. The coefficient identity and prime-product insertion appear in `coefficient-appendix.tex` lines 129–232 and 491–641 and `argument.tex` lines 98–159.

## The physical root that can be constructed now

The original U5 envelope on its ordered pair triangle is
\[
 L(u,t)=\max\{v(t),v(t+u),W(a)\},\qquad a=417/5000.
\]
The literal selected row starts with exponent \(L(u,t)-2b\). On the rectangle \(0.135<u<0.14\), \(0.145<t<0.15\), its winning value is \(v(t)=(1+t)/2\). With the buffer included the level there is \(N^{-2b}\sqrt{Np_2}\). Fixing this number fixes the integer \(p_2\) at each target. Grouping by exact equality of the pointwise seed thus does not supply a fixed number of positive-mass families on this rectangle. The detailed rectangle comparisons are recorded in [the earlier transport audit](../../continuation-20261125-p36/COARSE_ROOT_V_TRANSPORT_ANALYSIS.md).

`P3OriginalU5CommonPhysicalRoot.lean` implements an alternative policy. It uses the existing finite external-pair cells \(j\) from `P3OriginalU5CoarseRootV`. Its exponent is \(\lambda_j=\inf_{x\in j}L(x)-2b\). The manuscript's displayed coarse-infimum example concerns its three-slot alternative. The Lean construction takes the infimum of the actual U5 root expression above. Within a cell the two actual exterior prime coordinates enter the original `pairRoot`, and every decision uses `pairPlan R bank (2*b) λ_j`. Thus the source checks keep their original buffer.

| New declaration | Concrete output |
| --- | --- |
| `exists_physical_root_mesh`, `physicalSeed_initial_squares` | For any positive tolerance, choose a single mesh before all targets and prime pairs. The downward seed change is at most that tolerance. Every root has \(1/2<\lambda_j<153/256\), residual exponent between \(3a\) and \(5a\), and \(2(\lambda_j-u-t)\le1-u-t\). Both outer full squares and the first rough-head square hold. |
| `sum_rows`, `policy_eq_owner_trace` | Arbitrary real signed row sums regroup exactly by the external cells. The concrete Boolean policy reads the owner's actual checked trace with the same two prime labels. |
| `trace_cap_mem`, `trace_cap_eq_on_codes` | A finite alphabet of possible caps is fixed before \(N\). On a fixed root cell, equal bank codes on the two exterior slots and the chronological rough word give equal incoming cap values, even across targets. |
| `root_residualLevel_power`, `ordinary_child_cap`, `ordinary_child_residualLevel` | At the root the denominator is \(p_1p_2\). From full rank five onward a chronological suffix \(K\) keeps the parent's total level and divides its residual by \(\prod K\). |

These are source statements pending their own strict compile and kernel audit. The signed lower-bound and rounding-payment theorems for the old `selectedPolicy` continue to refer to that policy. Changing the buffer row by row to fit \(\lambda_j\) would also change the higher-rank checks.

## The joint coefficient still needed

`P2LowerFiniteCellRounding.cell` groups rough divisors by their complete ordered list of rough fine labels. For fixed external \(t\), positive coefficients use containment of this cell in the raw support and negative coefficients use nonempty intersection. `P2LowerFiniteCellBetaCompiler.rho_at_product` then gives the actual attached small beta-minus or beta-plus according to that sign. Varying the two external primes can change the raw support used in those containment and intersection tests. Equality of the coarse trace cap leaves the cube admission test on the actual word to be checked.

The next geometric statement should take a single external cell, two actual marked prime pairs in it, and one complete fine rough-label word. Evaluate the fixed physical policy on both pairs. On the jointly refined boxes, prove equality of the retained decisions up to the terminal rank or identify the first disagreeing decision on a proper wall. The available cap-code comparison, first-disagreement lemma in `P3OriginalU5WarmMixedReusedCore`, and whole rough-fibre inner/outer tests give the finite inputs. Apply the wall mass estimate on the actual joint carrier, including both external coordinates, and charge the omitted cells in the count and density of the chosen coefficient. At the root, arbitrary additive accuracy is now available for the physical exponent. For a numerical enhanced U5 conclusion, all three later frontier contributions and the required positive marked query carriers still need their actual mass.

A physical factorization of the chosen coefficient then needs a single allocation per entire remaining atom. It must retain the rescaled endpoints, the two-sided interval for the selected product, the full and selected-complement squares, and the appropriate fresh or three-slot W branch. The ordered residual factorials, signed external scalar, small beta factor and global squarefree restriction are part of the physical coefficient. `ActualPrimeFineWordMultiplicity` and the existing group-convolution modules supply identities once the whole-atom labels and partition match. The native U5 square suppliers refer to the raw attached coefficient. A one-sided density estimate for two different coefficients does not bound their signed primitive discrepancy.

## Distribution boundary

The arithmetic sum displayed by the rounded count is \(\sum_t\operatorname{rowSignedPrimitive}(N,\epsilon,\tau,P(t),t)\), at the complete modulus \((t_1t_2)k\). The exact primitive term contains the coprime mean for that modulus. For a direct classical slice, the rounded rough universe divides the strict primorial and the two original marked primes recover the unique pair and quotient. This gives a one-bounded real coefficient after regrouping. A below-half-level estimate can then pay the part inside its supported classical range and leave the complement with its original sign. The existing tagged integer pushforward and native U5 fibre uniqueness locate the algebra to reuse. The rounded real regrouping still needs its own identification.

The manuscript proves its insertion proposition for coefficient families which have passed the whole-atom checks. Its analytic branches use the restricted medium estimate, the below-half-level estimates and the one- and two-long rough-variable comparison. The stronger logarithmic savings absorb the fixed scalar norm and the chart count. Applying those inputs to the particular rounded U5 sum requires the actual atom decomposition and its support, collision and endpoint payments. The final PP proposition itself is part of the manuscript proof. No additional distribution axiom or credit for that total estimate follows from this audit.
