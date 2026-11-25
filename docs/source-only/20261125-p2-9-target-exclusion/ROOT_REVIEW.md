# Root review: actual frozen-cutoff target exclusion

Reviewed source: Git blob `68641a9d05fdd4ceafb60a22656d310e63ee2083`,
SHA256 `9b4296b5ee2d5213f07850f49094759b7fed57f9ba2ff9a1ac345bfb3b8de5a5`
(8,134 UTF-8 bytes, 167 lines).

Status: **SOURCE_ONLY_UNCOMPILED**. Static mathematical/source review grants
zero normal-compilation, kernel, endpoint or complete-P2.9 credit.

## Review conclusions

- The carrier keeps the original ordered-prime enumerator, actual fixed
  floor `cut N = N^(frozenLeafCutoffFloor/2)`, complete product at most
  `2*N`, and failure of coprimality of that complete product with `N`.
- Positivity and the already existing prime-divisor floor send the complete
  product to the exact old `p5U7ActualBadRough` carrier.
- The original finite product-fibre theorem bounds every fibre by
  `k^k`. Ordered and repeated prime coordinates are retained. Rank zero
  remains in the fixed finite sum; its empty product is 1, so its exception
  carrier is empty.
- The original logarithmic target-divisor count is reused, not assumed
  anew or reproved. Multiplying it by the existing all-rank multiplicity
  and `log N/N` yields
  `(2*multiplicity/log 2) * (log N)^2/N^cutExponent` for `N>1`.
- The existing log-power decay theorem applies because the already
  established `cutExponent_pos` is strictly positive. The eventual
  threshold pays every original bounded rank at once, with mark
  multiplier one.
- Root checked the pinned Mathlib
  `Mathlib/Data/Nat/Prime/Basic.lean` at
  `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`:
  `Nat.Prime.not_coprime_iff_dvd` has conclusion
  `¬Coprime m n ↔ ∃p, Prime p ∧ p ∣ m ∧ p ∣ n` without a prime
  premise. The old supplier's use of this API is correct.
- The independent reviewer separately checked the entire new mathematical
  argument, including zero rank, repetitions and the majorant constant.

## Deliberately retained boundaries

The old arithmetic supplier itself is source-only and imports the broad
historical `P5U7OriginalSourceMass` owner. This is not a qualified thin
compilation closure. Existing relocated declaration owners must be selected
as recorded in REGISTRY before combining the sources; no old object credit
is inferred.

This is one unit-weight ambient exception payment. It does not aggregate
the exception with the actual selected-history marks, identify the inner
profile mass with ordinaryBad, supply global smooth selection, identify
ordinary J, or establish a PP licence. Fresh-prime coprimality with N is an
arithmetic source condition distinct from geometric-wall equalities.
No mathematical gap or contradiction in the manuscript is inferred from
the still missing formal integration.
