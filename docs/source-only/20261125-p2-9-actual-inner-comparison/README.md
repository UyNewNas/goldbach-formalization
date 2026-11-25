# P2.9: actual marked-history inner comparison

**SOURCE_ONLY_UNCOMPILED. Formal credit = 0; kernel credit = 0.**

This increment multiplies the fixed-word inner comparison by the original positive `levelMark` and sums over the original root prime and dependent selected positions `B p`. The sharp contribution remains the literal original marked sum of `ordinaryBad` with coefficient one. The noncoprime and proper-strip terms remain separate positive errors.

The module is `ImbalancedChen.P2FiniteMarkedGamma5ActualInnerComparison`. The actual-history assumptions are retained: `2≤N`, `0≤t≤1/12`, `1/(n+1)≤11/384` and `h>0`. There is no new restriction on the original selected subfamilies `B`.

## Actual comparison

For one remaining depth, the main theorem states:

```lean
selectedInnerMass N n dep t h B ≤
  (∑ p ∈ originalBand N .U4, ∑ l ∈ B p,
    levelMark l *
      ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)) +
  selectedNoncoprimeMass N n dep t h B +
  selectedProperStripMass N n dep t h B
```

The public theorem is `selectedInnerMass_le_original_add_errors`. Its all-depth counterpart, `allDepthSelectedInnerMass_le_original_add_errors`, uses the existing `Fin 431` depth budget and the existing `allDepthSelectedInnerMass` and `allDepthSelectedNoncoprimeMass`. Its sharp term is exactly:

```lean
∑ dep : Fin 431, ∑ p ∈ originalBand N .U4, ∑ l ∈ B dep p,
  levelMark l * ordinaryBad N (rootQ N n .U4 t p) (wordProduct l)
```

There is no shape, root-code, rank or depth-cardinality multiplier on this base sum. Summing the original depth budget is not a claim that every generation is simultaneously a single original counting source.

## Original positions and actual scale

The proof first uses the existing root-code partition to put the original `rootQ` at its exact `cellQ`. The root prime `p`, dependent type `LevelIndex N n .U4 t p dep`, `B p` and every path occurrence remain present.

For a selected position `l∈B p` with `p` in the root cell, `prefixWeight_pos_of_mem` proves that the coefficient of its exact old word is positive. Two applications of `single_le_sum` retain that original contribution, and `mark_pos` supplies its positivity. No cancellation or uniqueness of a product image is used.

The already shared `P2FiniteMarkedGamma5ActualHistoryScale.of_prefixWeight_ne_zero` then supplies the positive old product and `cellQ/w.prod>1` needed by the fixed-word comparison. This file does not rederive `scale_and_alpha`, `scale_identity` or the actual source scale, and does not ask the caller to assume those conclusions for each selected position.

The original `wordProduct l` is definitionally the product of `(levelOccurrence l).current.old`. Multiplication by the original nonnegative mark is therefore exact. The three resulting finite sums are combined, and the existing `ordinaryBad_original_cells` and `selectedNoncoprimeMass_eq_cells` rewrite the first two back to their original expressions.

## Proper-strip error and its payment interface

The only new per-depth mass definition is:

```lean
def selectedProperStripMass (N n dep : ℕ) (t h : ℝ)
    (B : (p : ℕ) → Finset (LevelIndex N n .U4 t p dep)) : ℝ :=
  ∑ p ∈ originalBand N .U4, ∑ l ∈ B p, levelMark l *
    ∑ s : Split, ((properStripTuples N (rootQ N n .U4 t p) h
      (levelOccurrence l).current.old s).card : ℝ)
```

Split admission is already a predicate inside the unchanged `properStripTuples`. No extra outer admission branch is inserted.

`selectedProperStripMass_eq_cells` identifies this expression exactly with the raw cell sum used by the independent proper-wall payment consumer. `allDepthSelectedProperStripMass` and `allDepthSelectedProperStripMass_eq_cells` retain the same dictionary over `Fin 431`. The latter right side is the exact raw target of `P2FiniteMarkedGamma5ActualProperPayment.absolute_all_depth_cell_proper_payment`.

This file does not prove or reprove that payment. It also does not apply `prefixWeight_le_shapeCard` to the sharp mass. Those coarse finite factors belong only to the independent positive-error estimates.

## Preserved arithmetic and boundaries

The underlying fixed-word comparison retains the complete original tuple, including empty old/tail blocks and repeated tail primes. Complete-product coprimality is only the partition used to define the positive noncoprime allowance and clean proper-strip carrier. No tail-coprimality or distinctness restriction is added to the original `ordinaryBad`.

All original endpoint conventions and the equality-inclusive bad wall and inner product cap are unchanged. The weighted noncoprime allowance is the existing `selectedNoncoprimeMass`, not a replacement unweighted target. No `thetaConversion` or other original conversion factor is removed from a different mass: this theorem explicitly concerns the existing raw ordinary-profile and raw ordinaryBad marked sums displayed above.

The finite comparison uses `h>0`. Existing error-payment theorems later impose `h≤1/8`. No width choice or asymptotic epsilon claim is made in this source.

## Exact inputs

| Input | Role |
| --- | --- |
| `P2FiniteMarkedGamma5InnerComparison`, blob `421dfa2bac402d5d71a4b90cf854e3916454147c` | Fixed-word inner inequality, with original sharp mass and explicit errors. |
| `P2FiniteMarkedGamma5ActualHistoryScale`, blob `c2ef1b809fcc311813464dac4d71577075f3e7bb` | Sole owner of the shared actual scale-from-prefix coefficient helper. |
| `P2FiniteMarkedGamma5ActualRootCells`, blob `88dcd460198c101d181267599b8666247f738e5f` | Exact cell/rootQ dictionary and unchanged ordinaryBad marked sum identity. |
| `P2FiniteMarkedGamma5ActualRadialAggregate`, blob `93062adda7fdc87780a9c684c046652c567558d9` | Original inner masses, depth budget, prefix coefficient and selected index conventions. |
| `P2FiniteMarkedGamma5ActualTargetExclusion`, blob `510d3c6bb031ece73d15adb60da4121434f01700` | Original noncoprime masses and exact cell dictionary. |

The known source inventory and direct suppliers were checked before adding the consumer. Existing root-cell identities, prefix coefficient bounds, fixed-word comparison and positive error payments are reused. No existing proof is relabelled as a new proof of the same statement. Exact hashes, current header overrides and inherited owner selections are in `REGISTRY.json`.

## Manuscript and completion boundary

The fixed manuscript is [1106 release, commit a988cba584d803ae2856a0de50efb582f4f3dd6a](https://github.com/UyNewNas/chen-imbalanced-semiprimes/tree/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en).

The common-query/marked-family framework is in [sieve-appendix.tex 494–552](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L494-L552), the same positive marked pair/cofactor source in [634–660](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L634-L660), and the positive outer approximation and order of limits in [argument.tex 400–407](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/argument.tex#L400-L407).

This is a finite marked-sum transport. It closes the passage from the fixed-word comparison to the actual selected positions while retaining the original base coefficients. It does not construct a globally admitted smooth selected-history mask, identify the original `J`, prove a PP licence, or discharge W1/W2. The separate 29 H247/native-Wu binder compatibility branch is not asserted to be necessary for the manuscript mainline.

Root and independent review have read the complete 204-line source and found no mathematical blocker. These are static reviews. The exact-source mixed historical closure still requires its receiving binding and ordinary compile/kernel/full-owned gates. No accepted or queued input was changed. This author created only Git blobs, with no cloud job, commit or ref update.
