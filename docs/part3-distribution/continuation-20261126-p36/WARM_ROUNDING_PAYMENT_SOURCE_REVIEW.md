# Literal U5 warm rounding payment: source review

**Status: source candidate only. This note records the contract and proof design;
it does not certify Lean elaboration, strict compilation, official kernel replay,
declaration ownership, or transitive axioms.**

The new module is `ImbalancedChen/P3OriginalU5WarmRoundingPayment.lean`.
Its baseline is `102c46c652fd10138071582aab083d7e3c0140dd` on the original U5
continuation. The existing warm-cover, moving-wall-payment and canonical-wall
sources are reused from their frozen packets at that commit. Their installation
and verification are separate from this new connecting argument.

## Exact public endpoint

`exists_uniform_selected_U5_roundingLoss_lt` fixes the coarse mesh, `epsilon > 0`,
the explicit upper-cutoff condition

```
attachmentNu * epsilon ^ 2 < (417 / 5000 : Real)
```

and a reserve `eta > 0`. Positivity of the lower rough exponent
`omega = attachmentNu * epsilon ^ 2` is derived, using the unchanged
`attachmentNu = 34/125`. The theorem then chooses `tau0 > 0` and `N0 >= 2`
before all of the following:

- every `N >= N0` with `Even N`;
- every original `PairRange R` and `CandidateBank mesh`;
- every rational buffer satisfying `0 <= buffer <= 1/1000`;
- every original pair `t in pairSupport N`;
- every enumeration cap;
- every positive fine width `tau <= tau0`.

Its conclusion is the literal existing

```
roundingLoss (selectedPolicy R bank buffer false N t)
  N enum (smallCutoff N epsilon) (cutoff N) tau < eta.
```

The fixed rank bound is `M = rawRank epsilon`. The address types, linear forms,
row constants and number of reserves depend only on the fixed coarse mesh and
`epsilon`. Numerical centers may depend on every later original plan, seed,
target and pair; the reused payer is uniform over all such centers. The final
fine width and threshold therefore need no later pair-dependent choices.

## Existing suppliers and the new connection

`P3OriginalU5WarmMixedWallCover.selected_U5_mixed_wall_cover` already derives a
proper wall at the charged modulus itself, including when that modulus is the
rejected member of its mixed fibre. It preserves all ancestor admissions,
coarse-code changes, inherited caps and the original warm pair root.
`selected_U5_mixed_rank` derives the rank bound from the original raw witness in
the same complete label fibre. Neither coverage nor raw retention of the charged
modulus is an input to the new endpoint.

`whole_word_eq_canonicalPrefix` only identifies the two existing coordinate
representations at the full rank of `d.primeFactorsList`. The complete `take`
is the original reversed list, and `primeHistoryTuple_ofFn` together with
`ofFn_wordPoint` preserves that list exactly. No new ordering, canonical
factorization or representative selection is introduced, and this equality
does not need a primality or universe-membership hypothesis.

For each rank, `ProperWall` is the finite subtype of the original `WallIndex`
whose linear form is nonzero. `Fintype.equivFin` enumerates that subtype for the
existing arithmetic payer. `selectedCenters` reads the unchanged `pairPlan`,
twice-buffered plan argument, original `rootSeed` and actual `pairRoot.word.sum`.
The coverage theorem supplies properness, so the subtype discards no charged
mixed point. Rank zero has no wall addresses and is handled by the existing
empty-family case of the payer.

The scalar

```
rowConstant mesh rank = 1 + sum_w max 1 (norm (wallForm w))
```

is positive and bounds each original oscillation factor. This turns a single
fine-width inequality into membership in the exact `canonicalWallModuli` set.
It is independent of the real cap values and the number of later fine atoms.

`roundingLoss_le_sum_selectedWallCharge` uses the actual coefficient error
at each natural modulus. On an unmixed fibre the existing
`coefficient_eq_raw_of_not_mixed` makes that error zero. On a mixed fibre the
actual cover places it in the wall set at its own bounded rank. All error
summands are nonnegative, so additional wall sets may overcount them. Finite
sum interchange then gives an upper bound by the existing `wallRoundingCharge`
for each rank, with exactly the same original policy and coefficients.
`selectedWallCharge` is only a transparent abbreviation for that original
charge, not a replacement mass.

For every rank `r : Fin (M+1)`, the existing
`exists_uniform_centers_full_residual_wall_payment` is applied with reserve
`eta / (M+2)`. Its positive wall width is divided by `rowConstant mesh r`.
A finite minimum, padded with width one, gives `tau0`; a finite supremum,
padded with threshold two, gives `N0`. Thus every `0 < tau <= tau0` is legal.
The sum of all rank reserves is at most

```
(M+1) * eta / (M+2) < eta.
```

The moving-wall payer already includes the full canonical prefix/tail
factorization, reciprocal totient weights and entire residual divisor sum.
Those arithmetic proofs, the fixed-width slab envelope, target-prime deletion
and closed endpoint atoms are reused unchanged.

## Manuscript scope and remaining obligations

The manuscript pin remains
`UyNewNas/chen-imbalanced-semiprimes@3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`,
`paper/release-20261106/en/coefficient-appendix.tex`, subsection “Finite
approximation and strict margins,” together with `sieve-appendix.tex`,
equation `sv:physical-lower`. This connection supplies an actual arithmetic
rough-box error for the fixed original warm policy. It does not discard
identically inherited regions or infer a density lower bound from
coefficientwise order alone.

The endpoint does not identify the raw and rounded rho, evaluate the raw density,
pay the separate beta error, or claim a common physical Q, whole-atom tensor
identity, complete three-factor licence, family admission or PP conclusion.
The all-smaller-width physical modulus cap is a separate scalar consequence of
the existing support supplier and is not implemented in this module.

No Lean process, cloud job, commit or push was performed by the author of this
module. The required next evidence is compilation of the exact selected source,
official checker replay and the complete defining-module/type/transitive-axiom
inventory, restricted to the established allowed axioms. A source scan or this
proof-design review is not a substitute for those checks.
