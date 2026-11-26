# Actual singleton: complete-group log normalization

**Source-only; not elaborated, not kernel checked, and no new formal acceptance.**
This packet adds two small connections between existing suppliers. It does not
repeat the old one-long or medium Atlas normalization, the tuple reindexing,
the support proof or the physical local-level proof.

## The exact pointwise identity

`scalarProfile_eq_originalChart_div_log` composes two existing statements:

1. `AllGroupHBLogNormalization.normalized_listExtension` identifies the
   normalized licence on **all integer words** with the original extension
   divided by `wordLog`.
2. `ActualLowerNormalizedAtlasOccurrence.normalized_singleton_profile`
   identifies the normalized singleton extension, its original trim `eta`
   and chart `psi` with the real `scalarProfile`.

For the same `kap,B,N,cj,kap0,n`, the new composition is

\[
  (\operatorname{scalarProfile}(n):\mathbb C)
  =\frac{\operatorname{originalChart}
      (\operatorname{actualLicence}(\mathrm{kap},B,N))
      \,N\,\kappa_0\,[c_j]\,[n]}{\log(n:\mathbb R)}.
\]

The identity is valid for every natural integer, including 0 and 1 with Lean's
totalized division. It requires no primality assumption. The denominator is
the logarithm of the complete original group product, so unit HB factors are
not removed and no nonzero logarithm is imposed on individual factors.

## The actual tuple connection

`eventually_actual_tuple_normalized_profile` starts from an original nonzero
singleton chart and a genuine ordered factor tuple

```text
fs in factorTuples (2*(j+1)) n
assignedWeight (beforeHBCutoff K [cj]) (hbCutoff cj) (roles j) bs fs != 0
```

It uses the already published `actual_tuple_to_rectangle` to obtain precisely

```text
bv = blockVector (2*(j+1)) bs
ns = wordVector (2*(j+1)) fs
ns in rectangle bv
completeProduct ns = n
```

The existing `eventually_original_singleton_numeric_reserves` supplies
`1 <= originalMediumLow` and `64*originalMediumLow^6 < n`. Thus the complete
integer has `n > 1` and `log n > 0`. The pointwise quotient identity then
gives nonzero `integerProfile` at this same tuple. No reverse use of
`normalize_nonzero` and no new small-denominator hypothesis is needed.

The statement calls the existing
`P1OriginalSingletonPhysicalLevel.scalarProfile_complete_support` for

\[
N^{1-\kappa_0}<\operatorname{completeProduct}(ns)\le 2N.
\]

The assumptions are the original `kap0 < 1`, `0 < zeta <= 1/20000`,
`kap < 1`, the original nonzero chart, factor-tuple membership and nonzero
assigned tuple weight. Its eventual threshold precedes `kap,B,K,cj,j,n,bs,fs`
and the arbitrary finite `Q` and complex signed `rho`.

Its final term identity is

```text
hbSlots(original cutoff, original rowRoles, ns)
  * integerProfile(ns)
  * wordKernel Q rho N [completeProduct ns]
= assignedWeight(original cutoff, original roles, bs, fs)
  * (originalChart [cj] [n] / log n)
  * wordKernel Q rho N [n].
```

Both sides keep the same `Q`, `rho`, physical residue `N` and complete
count-minus-exact-coprime-mean kernel. This is a pointwise transport of the
existing kernel, not a new estimate or a separately altered mean.

## Existing work checked and reused

All tracked Lean references to `scalarProfile`, `normalized_listExtension`
and `normalized_singleton_profile` at published commit
`6b3edcc901cb49f19fdccba882db1d357d77bb7e` were located. The nearby
implementations have distinct scopes:

| Existing statement | Scope preserved here |
| --- | --- |
| `AllGroupHBLogNormalization.normalized_listExtension` | Exact normalization on every integer word |
| `ActualLowerNormalizedAtlasOccurrence.normalized_singleton_profile` | Already-normalized singleton profile identity |
| `P1OriginalSingletonOneLongRectangle.actual_log_normalization` | Whole selected one-long Atlas identity; not repeated |
| `P1OriginalSingletonMediumRectangles.actual_log_normalization` | Whole selected medium Atlas identity; not repeated |
| `P1OriginalSingletonOneLongProfile.realProfile_nat` | Continuous normalized profile evaluated at an integer; not the raw-chart/nonzero bridge |
| `P1OriginalSingletonTwoLongDictionary.actual_tuple_to_rectangle` | The actual individual ordered tuple and complete signed HB weight |
| `P1OriginalSingletonRemainingTypeIGeometry.eventually_original_singleton_numeric_reserves` | Uniform numerical reserves from the actual nonzero original chart |
| `P1OriginalSingletonPhysicalLevel.scalarProfile_complete_support` | Actual normalized-profile trim and physical upper support; reused unchanged |

The inspected references did not already supply the two new pointwise
connections. This is a bounded relevant-source comparison, not a claim about
unretrieved historical sources. Exact source and statement/proof hashes are
recorded in `SOURCE_REVIEW.json`.

PhysicalLevel is bound to the published
`1576fac11ccf44b4fc6e652fc76e8c2f71655f58` source, SHA256
`9b2986d114f8a05db3eba003b619ad5dfea729ef516d84d420ecd9a83b8f09b9`.
Its source publication is not Lean or kernel acceptance.

An independent read-only review by `p15_resume_source_paths` examined the
frozen 6210-byte candidate (SHA256
`52dc4794ef932a82c4cc1fb7bbca9d0cc9d8072bd4713968c9ee6191f4fc13d8`).
It found no concrete mathematical contract error or definite API mismatch.
The review checked totalized division at zero logarithms, the existing real
power/log/cast APIs, the six-part tuple supplier, and the unchanged
PhysicalLevel support and same-Q/rho kernel. No Lean or cloud execution was
part of that review.

## Manuscript scope and remaining gaps

The fixed manuscript is `UyNewNas/chen-imbalanced-semiprimes` at
`a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/coefficient-appendix.tex`, SHA256
`267af54481f344e806d4cb3ad602aa7f32020b930845e2aa152b7daaa2f9a440`.
The relevant passage is the original product trim, prime replacement
`Lambda(n)/log n`, retained original smooth chart and factorization over HB
variables, followed by the complete-product scale and Fourier separation
(lines 507–565). The logarithm belongs to the original group integer before
that factorization.

This bridge concerns one actual tuple. It neither assumes nor concludes that
an aggregate signed `blockCoefficient` is nonzero, or that every integer of
the closed rectangle has nonzero profile. It does not select two long slots,
attach them to a whole-complement block, identify the finite P2 short carrier
with the selected complement, or recover the complete Fourier integral.
The published two-long selector and physical local-level statement remain
separate interfaces to be connected at their proper scope.

No rough-to-Brun E3 payment, sharp-strip estimate, Fourier L1 budget, outer
HB/chart payment, or final discrepancy estimate is a premise or a conclusion.
The known source-closure stop at `Part3TwoLongFixedMRectangularCore` is not
resolved or searched again here. Complete recursive source/native readiness
and actual Lean validation remain pending. The files add no compiler credit
and do not close P1.5.

`verify_static.py` checks source pins, declaration ranges, fixed imports and
the absence of forbidden proof tokens. It does not invoke Lean, Lake, a kernel
audit or a cloud compiler.
