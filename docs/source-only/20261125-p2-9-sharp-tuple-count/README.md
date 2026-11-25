# P2.9: sharp complete-tuple count into the original ordinary Gamma5 mass

**Status: SOURCE_ONLY_UNCOMPILED. Formal credit = 0; kernel credit = 0.**

This increment proves a single-direction finite counting dictionary. For a fixed literal old word `w` with `0 < w.prod`, all sharp complete prime tuples in the existing bounded split enumerator inject into the original `badLabels` / `roughNumbers` source. The resulting upper bound has coefficient **one**, including the sum over all bounded splits.

It does not assume the desired count comparison, a product-map injection, a fibre bound, a rank-admission conclusion, or a smooth realization of the selected-history mask.

## Public result and exact carrier

The new module is `ImbalancedChen.P2FiniteMarkedGamma5SharpTupleCount`. Its main theorem is:

```lean
theorem sharp_count_le_ordinaryBad (N : ℕ) (Q : ℝ) (w : List ℕ)
    (hd : 0 < w.prod) :
    (∑ s : Split, ((sharpTuples N Q w s).card : ℝ)) ≤
      P2EnhancedBadGamma5ArithmeticGeometry.ordinaryBad N Q w.prod
```

Here `Split` and `admissibleSplit` are the original definitions in `P2FiniteMarkedGamma5ActualRadialAggregate`. Their bound is the existing `frozenSourceRankBound`. This file does not replace that constant or reconstruct its actual-source proof.

For `s = (k,r)`, `sharpTuples` is a filter of exactly:

```lean
Part3.labelledPrimeTuples (k.val + (2 + r.val)) (2 * N)
```

The filter requires:

- The original `admissibleSplit s`.
- Literal equality `w = tuplePrefix (tupleValues v)`, preserving all old coordinates.
- Target coprimality of both fresh primes.
- Every gate in the existing `program r.val`, evaluated by the original `raw N Q w.prod` on the fresh and tail blocks.

The last two blocks are read through the existing `slotEquiv`. The enumeration remains `Fin (2*N+1)`, as in the previously defined bounded raw profile sums. No unrestricted support equivalence or surjectivity from the original source is asserted.

## Why the coefficient is one

The total finite carrier is the sigma set over the existing `Split`. A tuple decodes to:

```text
([q0, q1], m),  where m = (List.ofFn tail).prod.
```

The existing `raw_source_inverse` supplies, rather than assumes:

1. The ordered fresh pair belongs to the original `badLabels N Q w.prod`.
2. The cofactor belongs to the original `roughNumbers` with exactly the old denominator and cutoff.
3. Its canonical factor list is exactly the tuple's tail list.

The first two facts place the decoded tuple in the original pair/cofactor source. To prove injectivity, the old rank is recovered as `w.length`, while the tail rank is recovered as `m.primeFactorsList.length`. Once these two dependent indices are equal, the original fixed old list, the retained ordered pair, and the canonical tail determine the whole `List.ofFn` of natural coordinates. Existing `List.ofFn_injective` and `tupleValues_injective` recover the bounded tuple.

The proof therefore never asserts that a complete product determines its ordered tuple. It does not charge `k^k`, a shape factor, a root-cell factor, or a split factor against `ordinaryBad`. Existing `Finset.card_le_card_of_injOn` and `card_sigma` finish the cardinal comparison. The target sigma cardinal is proved equal to the existing `ordinaryBad` definition, whose fully qualified name and body are unchanged.

## Endpoint and multiplicity conventions

The sharp gates keep their original conventions: lower cutoffs are inclusive, fresh upper cutoffs and fresh pair order are strict, the bad-square wall is inclusive, and the total-product cap is inclusive. Equality at the bad wall and at complete product `N` is retained.

The tail is nondecreasing and may repeat primes. It may be empty; then `m=1` and its canonical factor list is empty. No tail coprimality or fresh-tail/old-tail disjointness is introduced. The old list may also be empty at this ambient level; the existing actual-history exclusion of that case is not replaced. Every old coordinate is retained literally. No collision or square-factor error payment is newly claimed.

The theorem holds for arbitrary `N` and real `Q` under its single external positivity assumption on `w.prod`. Sharp tuple membership itself supplies the listed prime and raw conditions. In particular, no additional positive-scale or nonempty-tail hypothesis is hidden in the comparison.

## Reused sources and duplicate check

| Existing source | Exact use |
| --- | --- |
| `P2FiniteMarkedGamma5SharpSourceInverse`, blob `f5b78e0867db4aa6e6ba48147df45a25e0c41862` | Original pair/cofactor membership and canonical tail, called unchanged. |
| `P2FiniteMarkedGamma5ActualRadialAggregate`, blob `93062adda7fdc87780a9c684c046652c567558d9` | Original `Split`, `admissibleSplit` and `tuplePrefix`. |
| `P2FiniteMarkedGamma5EulerWordBudget`, blob `37f17bea5ff8988f0b3853d1da45acf9560f490d` | Existing exact old/fresh/tail slot equivalence. |
| `P2FiniteMarkedGamma5RadialNaturalMass`, current header-repair blob `5a22a4e7aeb47b39b7052e9a184703d577e5c112` | Existing `tupleValues` and its injection. Declaration bodies match the prior `6d51477…` source. |
| `P2EnhancedBadGamma5ArithmeticGeometry`, blob `dfd20b345e55f6a5820a6facf300d6c739cd867d` | Unchanged `badLabels` and original `ordinaryBad` target. |

The inspected active/source-only inventories and the actual-rank, physical-plateau, root-cell and existing raw-source candidates did not contain this coefficient-one, cross-split Gamma5 count consumer. The classical T07 `count_tuples` and `original_rank_iff` supplied useful exact-list proof patterns, but concern the other switched words and a different old-slot shape. They are not relabelled as Gamma5 results or reproved here. The original sharp Gamma5 cost and `SeedConvertedMass` estimates are unchanged.

## Manuscript scope

The fixed manuscript is [1106 release, commit a988cba584d803ae2856a0de50efb582f4f3dd6a](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en).

- [sieve-appendix.tex, lines 634–660](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L634-L660): the original positive marked pair/rough-cofactor expression. This dictionary relates its original discrete source to the complete labelled-prime coordinates.
- [sieve-appendix.tex, lines 763–776](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L763-L776): the inclusive bad region and the replacement by its positive upper estimate. This increment neither modifies that estimate nor charges the ordinary bad mass again.
- [argument.tex, lines 359–407](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L359-L407): the later admitted-family and positive approximation requirements remain separate.

This is an **expression / finite counting dictionary**. Its source proof uses existing factorization and sharp membership suppliers. It introduces no new analytic estimate or manuscript-external axiom.

## What remains after this result

The theorem bounds the sharp filtered tuple count. It does not yet compare the whole existing `selectedInnerMass` with `ordinaryBad`. That comparison must still retain the original selected-history `B p` and positive `levelMark` and account for tuples on softened nonradial boundaries or with excluded fresh primes. The earlier target-exclusion consumer supplies a positive allowance for the latter event; it is not an equality with the fresh-only exception.

There is no claim here of a two-way finite sum identity, surjectivity onto all original cofactors, payment for every nonradial wall, a global smooth selected-history mask, an original `J` identification, or a prime-product licence. The 29 H247/native-Wu endpoints remain a separate sufficient-condition/compatibility branch of the existing native binder; their necessity for the manuscript's enhanced finite-family result has not been established.

## Source selection and verification boundary

The exact source inputs and hashes are registered in `REGISTRY.json`. The receiving closure must select the existing owner postimages for moved declarations, including the frozen constants, actual-rank owner, prime-divisor floor, Part3 tuple definitions, and P5z fibre owner if reachable. No original owner may be loaded alongside a relocated declaration with the same public name.

The registry inherits the existing actual-radial and sharp-inverse source selections, with current tuple/header overrides taking precedence: TupleCount `de40d26…`, ProfileCollar `33196c7…` and NaturalMass `5a22a4e…`. The last two are dependency-agent header-only repairs; their imports and declaration/proof blocks are unchanged. This increment edits none of them.

The full historical import closure has not been qualified by this source increment. Previously accepted thin objects do not automatically qualify a combined history import. No new owner extraction, old-native rebuild, compilation, kernel replay, owned-declaration audit, commit or branch update was performed by this author.

Static checks: source readback and UTF-8 SHA256, exact upstream signatures at the fixed Mathlib pin, absence of prohibited proof escape hatches, dependent-index reconstruction, literal target definition, and preservation of empty/repeated tails. Compilation and complete receiving-closure validation remain with the parent/dependency gate.
