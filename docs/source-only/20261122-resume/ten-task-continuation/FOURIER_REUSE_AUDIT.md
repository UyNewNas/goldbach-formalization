# Fourier source reuse and the current finite family

This is a manuscript and source audit, not a new formal theorem or an
acceptance record. No new Lean file is needed for the generic analytic
steps identified below. The existing source candidates must be reused.

The mathematical reference is
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/`. In particular, the exact
`coefficient-appendix.tex` blob is `10f3e2efb2074a9b97148a5151956e1d450be13f`.

## 1. The HB coordinate count is fixed after choosing the finite family

`argument.tex`, `eq:current-PP`, and `coefficient-appendix.tex`,
`app:prime-products`, fix at most kStar labelled original primes. The
order-three HB identity in `coef:HB` chooses j_i in {1,2,3} for each
original group. Its term contains j_i truncated Moebius slots,
j_i-1 integer slots and one logarithm slot. Therefore

$$m=\sum_{i=1}^{k}2j_i\le 6k\le 6k_\ast.$$

Unit occurrences are still positions. A root-atlas mesh parameter also
called m in older implementations is a different parameter. Its moving
resolution, when used, retains its own restoration budget. The current
manuscript does not require an unbounded HB coordinate count after the
finite policy and original family have been fixed.

## 2. The fixed mixed-derivative budget

On an actual positive HB rectangle, let
`P_i(u)=product_{owner(a)=i}(U_a*exp(u_a))`. Differentiation in slot a
pulls back the original Euler derivative for its owner:

$$\partial_{u_a}=p_i\partial_{p_i}\quad\text{at }p_i=P_i(u).$$

An ordered derivative word retains every repeated owner. Here
`D_w = sum_{S subset {1,...,m}} ||partial_{2S} w||_1`, with each axis
in S differentiated twice. Each literal `doubled S` has length at most
2m, hence at most 12kStar; each original
group occurs at most twelve times. The original coupled geometric
profile, each original group's dyadic factor and reciprocal logarithm,
one complete-product trim, and a compact logarithmic plateau all remain
in the product rule. In particular, the mixed terms of a coupled
original profile cannot be replaced by a product of independent
six-coordinate estimates.

With the actual pointwise Euler bounds through these fixed orders,
the finite Leibniz expansion, bounded logarithmic support and at most
2^m subsets give `D_w <= C*(1+log N)^E` for a fixed E. An actual source
must supply those bounds or its corresponding existing `Family`
instance. An integrated original-group bound alone does not remove
the pullback measure and multiplicity obligations.

## 3. Physical Fourier normalization and one common cutoff

For the manuscript transform
`hat(w)(xi)=integral w(u)*exp(-i*xi.u) du`, integration by parts gives

$$|\widehat w(\xi)|\le D_w\prod_a(1+\xi_a^2)^{-1},\qquad
  (2\pi)^{-m}\int|\widehat w(\xi)|\,d\xi\le 2^{-m}D_w.$$

For H>0 and m>=1, the union of coordinate tails gives a normalized H-box tail
at most `m*D_w/(pi*2^(m-1)*H)`, hence at most `m*D_w/H`.
The zero-dimensional complement is empty. Mathlib's frequency eta
corresponds to the manuscript's `xi=2*pi*eta`.

The original chartBank and hbBank have the existing fixed logarithmic
restoration budget with exponent 7kStar; each original HB expansion has
absolute binomial coefficient sum seven. Their dyadic scales start at
a fixed positive constant; different unit-occurrence dictionaries use
scales 1/2 or 1. Any additional independent smooth-label grid retains
its own multiplicity cost, beyond the original 7kStar bank budget.
If the actual full-modulus
nonzero-difference and coprime-mean account is bounded by
`x*(1+log N)^F`, and the actual derivative budget has exponent E, one
may choose a common logarithmic H with exponent
`A+E+F+7kStar+1`. The coefficients' real norms and HB role weights must
be included in F. The complete-product scale gives `log x` comparable
to `log N`. This displayed choice uses the original banks; if an
additional independent grid is used, its logarithmic multiplicity
degree must also be added to the cutoff exponent.

The exact product equal to the target is a separate contribution,
bounded with the original support exponent. It is not included by
putting a divisor function at zero. In older source notation this is
the `B=T` case; it is distinct from a marked prefix also denoted B.

## 4. Existing sources to reuse

The following repository-relative paths are in
`UyNewNas/goldbach-formalization@f0a0cbbe181c58c61d8e13cb30d9ae358095993f`.
The path prefix in this table is `docs/source-only/`.

| Existing module | Path | Exact Git blob |
| --- | --- | --- |
| All-rank ordered-occurrence Fourier bridge | `20261028-resume-30c/pp_fourier/P5ActualAllRankOccurrenceFourierBridge.lean` | `4b9144c8998c830c76f223932cabbd94374cafb7` |
| Independent original-group logarithm normalization | `20261028-resume-30g/pp_derivatives/P5ActualIndependentGroupLogNormalization.lean` | `b3dffbddb265d21a3214afdc5cfeef019618b398` |
| Actual HB child mixed-Fourier budget | `20261110-yellow-closure-10t/t06_actual_mixed_fourier/P3ActualHBChildMixedFourier.lean` | `b88a9e111db458be40e66cbdb55cfa674bba2447` |
| Native full-Q atlas tail with one H | `20261028-resume-30e/pp_fourier/P5NativeFullQHBAtlasTailPayment.lean` | `3c5b8d826e332cefe33836eabd7a4b7b79634455` |
| Actual HB atlas scalar inventory | `20261028-resume-30e/pp_fourier/P5ActualHBAtlasScalarInventory.lean` | `458ca199e7e9581c84dd0a6058fcde76ad3698e3` |
| Post-modulus logarithmic cutoff and exact-product payment | `20261028-resume-30d/pp_fourier/P5ActualHBPostModulusLogCutoff.lean` | `b007b7fb80e2c3d26a18877b356516da04b7bf9e` |
| Actual U7--U9 source licence | `20261110-yellow-closure-10t/t06_actual_mixed_fourier/P3OriginalU789ActualAtlasLicence.lean` | `f5335127a8bc291f870462ced1f9fcbee0833195` |

The generic all-rank statements take an admitted `Family kStar`.
The concrete U7--U9 licence supplies its specified six smooth sources;
it does not admit every marked or switched source. The native atlas
payment uses its existing native coefficient dictionary, including
the exact mean and product-equality case. It is not an estimate for an
arbitrary newly supplied physical coefficient. None of these tail
results supplies the signed arithmetic estimate for the retained modes.

## 5. The actual marked-source connection still required

For the ordinary L5/L6 marked calls, the receiving variable is the
single original prime. The marked pair belongs to the complete physical
modulus `(p1*p2)*d`; it does not add two Fourier coordinates to that
particular receiving weight. Switched product calls retain their own
original product variables.

The U5 `signedPrimitiveSum` and the U6 physical-rho pushforward preserve
the labelled signed discrepancies. Their enclosing count bounds keep
the separate prime/centre or quotient-prime corrections.
Their current callers still require a correspondence to the manuscript's
whole boxes, frozen ancestor choices and actual compiled integer rho.
A level fixed for one marked pair and its descendants must not be
silently identified with the common level fixed for a whole atom box.

The next binding must identify the actual finite count and exact
coprime mean under that same coefficient, then invoke the appropriate
arithmetic branch for each retained mode. The selected-complement
squares, physical support, squarefree-collision account and density
corrections remain part of that binding.

The coordinate and normalization distinctions are formal-expression
issues. The fixed-order chain rule and tail-budget calculation are
fillable omitted derivations, with existing generic source candidates.
Actual source admission and same-rho retained-mode payment remain
specific mathematical and formal obligations. This audit found no
evidence of a manuscript counterexample and creates no new green node.
All cited source-only files retain their existing uncompiled and
kernel-unverified status.
