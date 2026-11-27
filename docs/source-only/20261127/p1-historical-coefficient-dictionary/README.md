# Actual historical small/rough coefficient dictionary

Status: **SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE**.

`P1OriginalHistoricalCoefficientDictionary.lean` is a new exact coefficient
interface for the literal historical `trueDDeltaRho`. It contains three
definitions, five public theorems and one private support helper. No new
axiom, unfinished proof, asymptotic estimate or missing-medium premise is
introduced. No Lean/cloud compilation or Git write was performed.

## Mathematical content

Fix the original `old`, `fresh`, `N`, `cap`, `w`, `z`, `L`. Put

```text
A = actualSmallRosserSupport N cap w
R_f = fixedRoughSupport fresh N cap w z
R_o = fixedRoughSupport old N cap w z
delta(b) = 1_{R_f}(b) - 1_{R_o}(b)
B_mu(a,b) = mu(b) * (betaPlus(a) if 0 <= mu(b), else betaMinus(a)).
```

On every actual pair `a in A`, `b in R_f union R_o`, the module proves

```text
trueDDeltaRho old fresh N cap w z L (a*b) = delta(b) * B_mu(a,b).
```

The order matters. The original Mobius sign chooses the small Rosser
member; the policy-mask difference is multiplied afterwards. For example,
deleting a retained positive-Mobius rough modulus contributes
`-betaPlus(a)`. Attaching directly to the negative policy difference would
instead select `betaMinus(a)` and would change the original coefficient.

The original physical carrier is proved to be exactly

```text
smallRoughModuli A (R_f union R_o).
```

This is the original union of physical supports, with no added physical
modulus. The existing cutoff-separated factorization theorem makes the
product map injective on this carrier. The new complex test identity
therefore reindexes the original signed sum without a divisor multiplicity
or an absolute discrepancy.

The final theorem uses the literal filter

```lean
if a * b ∈ remainingModuli B N
  (trueDDeltaSupport old fresh N cap w z)
then G (a * b) else 0
```

at the complete physical product. Unfolding the existing `remainingModuli`
keeps **both** `panModulusCutoff N B < a*b` and
`(a*b : Real) < (N : Real)^(599/1000)`, in addition to the original physical
support. There is no quotient-modulus filter and no change to `N`, `cap`,
`w`, `z` or `L`.

## Public API

| Theorem | Exact conclusion |
| --- | --- |
| `trueDDeltaSupport_eq_smallRoughModuli` | Identifies the original physical support union with the common actual small/rough product carrier. |
| `trueDDeltaRho_eq_actual_difference` | Removes only redundant zero extension and keeps fresh-minus-old order. |
| `trueDDeltaRho_mul` | Gives the actual pair coefficient as the mask difference times the original Mobius-selected small coefficient. |
| `trueDDeltaRho_test_eq_pair_sum` | Reindexes any complex test of the original signed coefficient on its physical support. |
| `remaining_trueDDeltaRho_test_eq_pair_sum` | Reindexes the historical remaining-modulus test with its complete-product filter unchanged. |

The actual history call sites in the previously frozen
`P1OriginalHistoricalExactMediumResidual.lean` use `old = S false`,
`fresh = R false` for comparison, and `old = eight false`,
`fresh = six false` for saving. They can apply the last theorem directly:

```lean
remaining_trueDDeltaRho_test_eq_pair_sum B (S false) (R false) N cap w z L G
remaining_trueDDeltaRho_test_eq_pair_sum B (eight false) (six false) N cap w z L G
```

These are call-site instantiations of the existing policies. No replacement
policy, guessed policy parameter list, or new family structure is defined.

## Reused sources and API audit

The project sources were read at
`UyNewNas/goldbach-formalization@6d87764cbc9fce5b10a2665a458619e44d8255ae`.
The dependency manifest pins mathlib to
`e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`.
Exact restored byte bindings are in the sibling `SOURCE_BINDINGS.json`.

| Existing source | API used or checked |
| --- | --- |
| `P1Full87TrueDPolicyDelta.lean` | Original `trueDDeltaSupport` and `trueDDeltaRho` definitions and their order. |
| `P1Full87TrueDUnitBound.lean` | Bounded review confirmed that its Mobius mask and zero-extension equalities are private; its public targets give bounds, not the new exact pair identity. The existing unit bound is not reproved. |
| `FiniteUpperCarrierCore.lean` | `actualSmallRoughRho_eq_on_common_carrier`, preserving the same coefficient when the rough carrier is enlarged by zero. |
| `ActualSmallRosser.lean` | `actualSmallRosserSupport_smallPrimeSupportedAt`. |
| `FixedRoughCoefficients.lean` | `fixedRoughSupport_roughPrimeSupportedAt` and the original masked-Mobius coefficient definition. |
| `SmallRoughAttachment.lean` | `smallRoughRho_eq_zero_of_not_mem`, `smallRoughRho_mul`, `smallRough_mul_injOn`; the latter already uses `smallRough_factorization_unique`. Its existing sum proofs verify the `Finset.sum_image` and `Finset.sum_product` call patterns. |
| `SignSensitiveAttachment.lean` | Exact definition `c * if 0 <= c then betaPlus else betaMinus`. |
| `P1OriginalHistoricalMiddlePointwiseData.lean` | The unchanged literal `remainingModuli` definition. |
| Mathlib `Data/Finset/Prod.lean`, `Data/Finset/Image.lean` | `Finset.product_union`, `Finset.image_union`, checked at the pinned revision. |
| Mathlib `Data/Complex/Basic.lean` | `Complex.ofReal_mul`, checked at the pinned revision and imported explicitly. |

The bounded existing-API search found no public theorem with the exact
new pair/masked-test conclusions among these sources. This is a bounded
source review, not a claim about every uninspected historical archive.

## Manuscript link and remaining scope

The frozen 1106 `coefficient-appendix.tex`, in the subsection **The
coefficient identity and squarefree restriction**, retains the sign of
each atom when attaching the small-prime beta weight and invokes uniqueness
of the small/rough decomposition. The new module supplies that exact
sign/uniqueness interface for the already defined historical policy
difference. The same subsection keeps squarefreeness in the physical
coefficient and pays its removal separately in the analytic tensor.

The new pair dictionary remains on the original physical supports.
It does not identify the policy mask with constants on the endpoint word
atoms, replace it by a three-factor unrestricted tensor, remove collision
terms, supply four medium gates, or prove `RestrictedMediumTarget`.
Those tasks remain necessary before applying the complete medium bound.
This module is a necessary exact algebraic connection, not a nonzero medium
payment and not a proof of P1.5.

## Verification state

The restored source blobs were checked against their frozen Git blob
identities. In particular, the prior `MEDIUM_BOUNDARY.md` is exactly
13,129 bytes with SHA-256
`48c24afc57153a40b687ca482a99bed828b0ce192952cdd15df2cc9221779079`.
The new proof has been read against the public APIs above and statically
checked for forbidden placeholders. An independent source review of the
same 9,079-byte source found no definite mathematical error or apparent
API/type mismatch; see `INDEPENDENT_SOURCE_REVIEW.json`. No elaboration, named-kernel replay, or full-owned
acceptance is claimed; the current cloud connection limitation does not
turn a static review into compilation evidence.
