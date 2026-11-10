# T08 · Physical oldform expansion in all original cusp channels

**P3.5 remains yellow.** Every genuine character Eisenstein oldform with `q²B∣N` now has a finite expansion in the original width-normalized cusp Eisenstein functions on `Re(s)>1`. The index is Mathlib’s actual projective cusp quotient at level `N`. At every integral cusp frame, the expansion coefficient equals the physical incoming height limit for real `s>1`. T10 independently reviewed the three SHA256-pinned source modules in `CLASS_NORM_REGISTRY.json`. They have no compilation or kernel-verification credit.

## From the actual lattice to the native cusp functions

Let `p=qB` and write `v=(C,D)` for an oriented primitive integer row. Dividing `(pc,d)` by its positive content permutes all primitive rows, including both axes. Its inverse divides `(C,pD)` by `h=gcd(C,pD)=gcd(C,p)`. The original physical complex-power seed changes by `(h²/p)^s`. The actual character weight on the inverse row is `χ(C/h) χ(pD/h)`. For an element of Γ₀(N), its integral degeneracy conjugate has off-diagonal entries divisible by `q`. This preserves the signed character product and the content on each original right orbit.

The allowed rows of the archived parabolic function at frame `g` are exactly the orbit of the bottom row of `g⁻¹`. The row classes correspond bijectively to the projective cusp orbits, with the central negative identity in Γ₀(N). Absolute convergence permits grouping the primitive series over these disjoint classes. The original cusp function includes the factor `w^(−s)`, where `w` is its proved primitive width. Consequently the coefficient for a frame with first column `(a,c)` is

`χ(−c/h) χ(pa/h) (w h²/p)^s,` with `h=gcd(c,p)`.

The finite sum using these coefficients equals the physical oldform pointwise throughout `Re(s)>1`, including conductor one. For primitive `q>1`, the previous supplement gives its continuation as a whole to `Re(s)≥1/2`. This is the oldform-to-cusp direction of Young’s change of basis, written directly on the original projective cusp classes. [Young, Theorem 7.1](https://arxiv.org/html/1710.03624v2#S7)

## Physical incoming normalization

In the normalized observing frame `h`, the two zero-first-coordinate rows contribute the same indicator that `g` and `h` represent the same projective cusp. Their sum cancels the original factor `1/2`. For real `s>1` the height-one primitive Eisenstein series dominates the remaining rows after division by `y^s`. The limit at any fixed horizontal coordinate therefore equals `1` on the diagonal and `0` off it. On the diagonal the two computed widths agree. Applying these limits to the finite expansion recovers the displayed oldform coefficient in any observing frame and proves linear independence of the original parabolic functions at those real parameters.

| Module | Actual terminal |
| --- | --- |
| `Part3ActualCharacterCuspRowReduction` | `original_row_expansion`, `original_row_summable` and `rowWeight_invariant` for the literal original signed lattice and every legal dilation. |
| `Part3ActualCharacterCuspExpansion` | `nativeCuspEquiv`, `cuspCoefficient_explicit`, `actual_oldform_eq_native_cusps` and `finite_cusp_sum_continues`. |
| `Part3ActualParabolicIncoming` | `parabolic_incoming`, `native_parabolic_independent` and `oldform_incoming` on the actual normalized charts for real `s>1`. |

## Premise delta for the original yellow node

The elementary proof of Young (7.1) on the native cusp orbits, the identification of its two widths and signed rows, the initial-half-plane physical incoming coefficient, and initial independence now have source proofs. Earlier T08 modules supply the actual nontrivial primitive-character Fourier families, two original cusp amplitudes, and the S21 arithmetic removal for an individual dilation. R21, R23, R30 and S20 supply the genuine cuspidal operator, modes, basis and original Whittaker rows. R22 supplies the distinct principal family. S22, R20 and R24 supply the recorded test budgets, jets and tails.

The reverse cusp-to-oldform change, individual critical-line cusp continuations and a complete critical class with the `4π` formal norms and (dt/`4π`) continuous spectral normalization remain open. So do the normalized signed full trace, the holomorphic and Maass basis/norm comparisons, full-class ABL removal, the printed Pascadi A/J and regular spectral inequalities on the same coefficients, the KS spectral gap on this realization, both original level ranges and their combined uniform (7/32) bound with the full test and descendant costs. T06’s Fourier cost and T07’s actual-count application still have to enter that same terminal. The original root budget remains `c=49044063/25000000` and `K=8452171/1250000`. [Young, §8](https://arxiv.org/html/1710.03624v2#S8) [Drappeau, §4](https://arxiv.org/pdf/1504.05549v4) [Assing, Blomer and Li](https://arxiv.org/pdf/2005.13915v1)

The remaining passage is substantial missing native spectral mathematics and a classical normalization comparison. No contradiction to the original analytic assertion has been supplied. This second supplement preserves the 10 earlier T08 source files and their frozen records. T10’s review checks mathematical scope and source definitions. The hold set and all finite computational guards retain their prior status.
