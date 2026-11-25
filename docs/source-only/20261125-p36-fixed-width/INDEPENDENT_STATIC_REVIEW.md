# Fixed-width slab reserve: independent static review

**Status: mathematical implication and quantifier order checked; source only and uncompiled.** This review does not confer kernel acceptance, add an owned compilation target, or close P3.6.

The reviewed candidate is `ImbalancedChen/P3OriginalU5FixedWidthSlabReserve.lean`, 4,943 bytes, SHA-256 `76e20ecdebb2d2d2accecef691544181703ed32cd8b38f10704100d3e18ed68a`. The five reused source files listed in `SOURCE_INDEX.json` were independently retrieved at `c6b89774822580c731a236ac66dcd7466ac8a0e6`; all five SHA-256 values matched that index. No Lean process was started for this review.

## Exact reused contracts

The [old affine-slab theorem](https://github.com/UyNewNas/goldbach-formalization/blob/c6b89774822580c731a236ac66dcd7466ac8a0e6/ImbalancedChen/P1ActualMovingAffineSlab.lean) bounds the literal finite prime-box slab mass by

\[
 E_K(a_j,b_j,\delta/|v_j|;N)\,T_N,
 \qquad
 T_N=\operatorname{actualPrimeBoxMass}(N,j\!.\operatorname{removeNth}a,j\!.\operatorname{removeNth}b).
\]

It requires a nonzero selected coefficient, positive lower exponent, a larger upper exponent, nonnegative width, `1 < N`, and `3 ≤ N ^ a j`. Its center is an unrestricted real number. The candidate supplies every one of these hypotheses at a common threshold.

The [coordinate-slab envelope](https://github.com/UyNewNas/goldbach-formalization/blob/c6b89774822580c731a236ac66dcd7466ac8a0e6/ImbalancedChen/P1ActualMovingCoordinateSlab.lean) is exactly

\[
 E_K(a,b,w;N)=\frac{2w}{a}
   +\frac{bK}{a^2\log N}
   +\frac{1}{N^a-1}.
\]

Thus its width-zero instance tends to zero and its positive-width leading term can be separated by an exact algebraic identity. The last term is the retained closed endpoint atom; the new argument does not discard it. The [uniform interval constant](https://github.com/UyNewNas/goldbach-formalization/blob/c6b89774822580c731a236ac66dcd7466ac8a0e6/ImbalancedChen/P1OriginalFourthMovingPrimeIntervalBound.lean) precedes all targets, caps and endpoints. Although that interval contract states an even-target bound, the reused actual-coordinate and affine theorems already perform the target-2 upper-carrier argument and apply to every sufficiently large target. The candidate does not silently remove an evenness premise.

The [actual prime-box limit](https://github.com/UyNewNas/goldbach-formalization/blob/c6b89774822580c731a236ac66dcd7466ac8a0e6/ImbalancedChen/ActualPrimeBoxMass.lean) gives

\[
 T_N\longrightarrow L=\prod_{i:\mathrm{Fin}\,k}
       \log\frac{(j\!.\operatorname{removeNth}b)_i}
                    {(j\!.\operatorname{removeNth}a)_i}.
\]

Its namespace is `ImbalancedChen`, so the candidate's unqualified uses resolve through its enclosing namespace; an additional `open P1ActualMovingAffineWallMass` is not required for these two names. The dimension-zero tail is also covered by this old contract.

## Inequalities and quantifiers

For fixed `a`, `b`, `v`, `j` and positive reserve `eta`, put `C = |L| + 1`. Then `C > 0` and `L < C`, so eventually `T_N < C`. The choice

\[
 \delta=\frac{\eta |v_j|a_j}{8C}>0
\]

is made before both `N` and the center. Choose one threshold making `N ≥ 2`, `N ^ a j ≥ 3`, `T_N < C`, and `E_K(a_j,b_j,0;N) < eta / (4C)` hold simultaneously. The exact split is

\[
 E_K(a_j,b_j,\delta/|v_j|;N)
 =\frac{\eta}{4C}+E_K(a_j,b_j,0;N)
 <\frac{\eta}{2C}.
\]

The envelope is nonnegative under the hypotheses. Consequently the old slab bound is at most `E * C`, which is strictly less than `eta / 2`, hence less than `eta`. The candidate's slightly weaker final inequality is valid and retains a strict reserve.

The resulting order is exactly `∃ delta > 0, ∃ N0 ≥ 2, ∀ N ≥ N0, ∀ center, mass < eta`. Neither choice depends on the center or on a subsequent value of `N`. Therefore any center depending on the external pair and on `N` can be substituted. There is no assertion of uniformity over varying boxes or slopes: in particular a family with `|v j|` approaching zero would require an additional argument. Passing to one mesh for finitely many fixed wall templates and paying a finite union remains a separate consumer step.

## Expression review and manuscript boundary

The initial 4,914-byte candidate had SHA-256 `126ac23729bf0dd9638cbc0e695afb65f71bf8e9b01081b0039b454c1965f6ea`. Static inspection of the pinned `Mathlib/Tactic/Positivity/Core.lean` found that the `hE0` use of `positivity` should receive a direct scalar lower-bound hypothesis. The author added only `have haj : 0 < a j := ha j` before that step. Deleting that one line from the reviewed final candidate exactly recovers the initial SHA-256. The theorem statement, assumptions, quantifier order and mathematical proof are unchanged. This was a static expression finding, not an observed compilation failure.

The [1106 coefficient appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/coefficient-appendix.tex), subsection “Finite approximation and strict margins,” calls for small proper-wall mass on the compact remainder and a joint finite policy after ancestor decisions are frozen. The [1106 sieve appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e/paper/release-20261106/en/sieve-appendix.tex), lower-coefficient realization and finite-feedback passages, retains the original prefix decisions and common refinement. This candidate supplies one fixed-width, center-uniform arithmetic wall estimate relevant to that step. It does not supply mixed warm-fibre coverage, finite-union payment, the signed density comparison, or the complete PP conclusion. Identically inherited regions are not reclassified as proper walls by this theorem.

No substantive mathematical gap was found in the stated implication. The remaining acceptance step for this candidate is actual compilation and the usual source/object/kernel/axiom verification, after its dependencies are selected and its scope is explicitly scheduled. Existing P15 source text was reused as a contract, not relabeled as new compiled evidence by this review.
