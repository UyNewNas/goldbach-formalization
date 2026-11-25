# P2.9: fixed-word inner profile versus the original sharp mass

**SOURCE_ONLY_UNCOMPILED. Formal credit = 0; kernel credit = 0.**

This increment connects the original bounded inner physical-profile sum at one fixed old word `w` and one common `Q` to the original `ordinaryBad`. The right side retains the existing weighted complete-product noncoprime slice and an explicit count on the original proper strips. The sharp term has coefficient one.

The new module is `ImbalancedChen.P2FiniteMarkedGamma5InnerComparison`. Its principal theorem is:

```lean
theorem inner_sum_le_ordinaryBad_add_errors
    (N : ℕ) (Q h : ℝ) (w : List ℕ)
    (hN : 0 < N) (hd : 0 < w.prod)
    (hR : 1 < Q / (w.prod : ℝ)) (hh : 0 < h) :
    (∑ s : Split, if admissibleSplit s then
      boundedInnerSlice N s.1.val s.2.val (log Q) h w else 0) ≤
      ordinaryBad N Q w.prod +
      (∑ s : Split, if admissibleSplit s then
        noncoprimeSlice N s.1.val s.2.val (log Q) h w else 0) +
      ∑ s : Split, ((properStripTuples N Q h w s).card : ℝ)
```

All named mass functions on the left and the first two terms on the right are reused from their original owners. No new `J` or replacement ordinary mass is defined. The old-word equality, original cutoff `N^frozenLeafCutoffFloor`, width `radialWidth h`, original bounded `Split`, and prime enumerator `Fin (2*N+1)` remain literal.

## Exact decomposition

Every summand is the original `boundedProfileWeight`, restricted by the original inclusive complete-product condition `M≤N`. The comparison classifies each tuple as follows.

1. Zero profile/prefix weight contributes zero.
2. If the complete product is not coprime to `N`, its original weight is paid by the existing `noncoprimeSlice`. This allowance is weighted; it is not replaced here by an unqualified cardinal bound.
3. On the remaining complete-coprime part, accepted sharp geometry gives every original raw gate. Each fresh prime divides the complete product, so both fresh primes meet the original target-coprimality requirement. The tuple therefore belongs to the already constructed `sharpTuples`.
4. A supported inner tuple failing accepted geometry lies in the original `properStrip` by the accepted `inner_nonzero_failure_mem_properStrip` theorem.

The global profile bound in `[0,1]` controls the sharp and strip terms by unit indicators. Summing over the bounded prime enumerator gives the per-split inequality. Summing over `Split` then calls `sharp_count_le_ordinaryBad` exactly once. This retains coefficient one on `ordinaryBad`; no shape, root-cell, split-cardinality or product-fibre factor is charged to the sharp mass.

The proper-strip term may overlap the sharp term at a boundary. The argument is an upper bound by nonnegative terms, so this overlap is harmless.

## The new strip carrier

`properStripTuples N Q h w s` is a filter of the same original `Part3.labelledPrimeTuples`. It requires:

- Original split admission and literal `w = tuplePrefix (tupleValues v)`.
- Nonzero value of the unchanged physical profile.
- Original inclusive inner cap `M≤N`.
- Complete-product coprimality to `N`.
- The accepted module's original `properStrip` predicate at the same physical log point.

Complete-product coprimality belongs only to the clean/error partition. It is **not** asserted to be equivalent to membership in `badLabels`. In particular, `ordinaryBad` receives no new tail-coprimality condition. Tuples excluded by whole-product noncoprimality are retained in the original positive allowance, including possible tail factors that the original sharp source allows.

Nonzero profile support is kept in the strip carrier so that its true coordinate floor is available to later arithmetic wall-count consumers. This file does not assume or prove such an error-payment estimate.

## Coordinates and edge cases

The only new coordinate lemma, `tuple_physical_logPoint`, applies the existing `logPoint_prefix_eq_log_product` to the original old coordinates. The prefix is exactly `(tuplePrefix u).prod`, while fresh and tail coordinates are read through the existing `slotEquiv`. It introduces no sort, product image or coordinate deletion.

The lemma holds for all positive natural coordinates. Thus it covers an empty old block, where the old product is one and its logarithm is zero. The tail may be empty or may contain repeated primes. No disjointness or distinctness condition is added. The actual raw/sharp dictionary retains inclusive lower endpoints, strict fresh upper endpoints and pair order, the inclusive bad wall, and the inclusive product cap.

The finite comparison requires only `h>0`. It does not require `h≤1/8`; that additional restriction remains in the separate existing uniform payment interfaces. It does not add a square-root scale, floor assumption, rank licence or actual-source hypothesis. The displayed `R>1` premise is the premise of the reused `raw_iff_passed` interface. For actual history positions its source is the existing `scale_and_alpha` scale bound; this increment remains the fixed-word consumer before the original marked sum is transported.

## Existing inputs

| Input | Exact reuse |
| --- | --- |
| `P2FiniteMarkedGamma5NonradialSupport`, blob `2091608eaeec53f3f8b60224fb7b10048642805e` | Accepted proper-strip definition and actual inner failure support theorem. |
| `P2FiniteMarkedGamma5LogExtension`, blob `d77be7de024ec574ac5c53dae627a093c34ce0e2` | Existing `raw_iff_passed` with its positive scale hypotheses. |
| `P2FiniteMarkedGamma5PhysicalExtension`, blob `2f776e2b4f9d5125b1df887d0e5da01e2c52dd1b` | Existing prefix-log identity and global profile bounds. |
| `P2FiniteMarkedGamma5IntegerSupport`, blob `5cce5dcab54c50ec68612002349fd4efa032fe05` | Existing complete-product identity under `finToPhysical`. |
| `P2FiniteMarkedGamma5SharpTupleCount`, blob `892aeebed19b3e4fe97e31d5f4c7421915c52498` | Existing sharp carrier and coefficient-one all-split comparison to original `ordinaryBad`. |
| `P2FiniteMarkedGamma5ActualRadialAggregate`, blob `93062adda7fdc87780a9c684c046652c567558d9` | Unchanged `boundedProfileWeight`, `boundedInnerSlice`, old-prefix and split definitions. |
| `P2FiniteMarkedGamma5ActualTargetExclusion`, blob `510d3c6bb031ece73d15adb60da4121434f01700` | Unchanged weighted `noncoprimeSlice`. No arithmetic payment is reproved. |

The inspected existing candidates already supplied the geometric support trichotomy, raw/source inverse, original sharp cost, radial split and noncoprime aggregation. They did not contain this finite fixed-word comparison from the original `boundedInnerSlice` to the original `ordinaryBad` plus those two explicit errors. This file composes those suppliers; it does not reprove them.

## Manuscript classification

The fixed source is the [1106 manuscript, commit a988cba584d803ae2856a0de50efb582f4f3dd6a](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en).

- [sieve-appendix.tex, lines 634–660](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L634-L660) fixes the positively marked pair/rough-cofactor expression.
- [sieve-appendix.tex, lines 763–776](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L763-L776) keeps the inclusive bad region and its positive upper cost.
- [argument.tex, lines 400–407](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L400-L407) describes positive geometric outer approximations and the order of the limits.

This is an **expression / finite-sum omitted derivation**, using already supplied pointwise and arithmetic dictionaries. It proves no new analytic strip estimate. The passage to a uniformly negligible error and to an admitted global smooth selected-history family remains separate.

## Marked-history and validation boundaries

The comparison is at one literal old word and common `Q`, before multiplying by the original positive `levelMark` and summing over the original dependent `B p`. It neither replaces these indices nor merges path occurrences. A later exact marked sum must keep the sharp term as the original sum of `levelMark * ordinaryBad`. Only the positive errors may then be bounded with the existing `prefixWeight_le_shapeCard` and finite root-cell/rank budgets.

This increment supplies no complete marked-history comparison, proper-strip epsilon payment, all-depth strip aggregation, global smooth mask, original `J` identification or PP licence. The 29 H247/native-Wu conditions remain the separately recorded native-binder compatibility branch; their necessity for the manuscript mainline is not established.

Exact input selection is registered in `REGISTRY.json`, including the current TupleCount/ProfileCollar/NaturalMass header overrides and inherited owner postimages. The new source does not change any accepted or queued input. Accepted thin modules do not automatically qualify the mixed historical receiving closure.

The author and independent review agent read the complete 243-line source. The root also reported a complete mathematical review. No mathematical blocker was identified in the physical/log dictionary, three-part pointwise comparison, noncoprime allowance, or coefficient-one final sum. These are static reviews. No normal compile, kernel replay, full-owned audit, cloud job, commit or ref update was performed by this author. The new module remains source-only with zero formal/kernel credit.
