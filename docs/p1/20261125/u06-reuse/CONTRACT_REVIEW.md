# U06 singleton short-medium proof-contract review

Date: 2026-11-25. Scope: the eight existing U06 sources in the November 23
ten-task-continuation packet and the relevant pinned November 6 manuscript
passages. This is a static statement and proof-body review. It does not claim
compilation, kernel verification, canonical-source adoption, dependency-closure
acceptance, or completion of P1.5. No formal sources were edited and no compiler
or cloud jobs were run for this review.

## Exact reviewed sources

All paths in the following table are relative to
`docs/source-only/20261123-resume/ten-task-continuation/`. All eight current file
SHA-256 values equal their entries in `PUBLIC_SOURCE_MANIFEST.json`.

Manifest path:
`docs/source-only/20261123-resume/ten-task-continuation/PUBLIC_SOURCE_MANIFEST.json`.
Manifest SHA-256:
`df526b7e8063dd5243b9a9612142534ce66cb8c07524f75de874d32d4e22fae3`.

| Packet-relative path | SHA-256 | Git blob recorded by the manifest |
| --- | --- | --- |
| `ImbalancedChen/P1OriginalSingletonShortMediumLiveRow.lean` | `c73b094db778475662fad9f1aff39b39f05a3aca464c7300165a07a1d90e48a5` | `fdfbe28dc76e5f757b0d2066674faf97df6d0e31` |
| `ImbalancedChen/P1OriginalSingletonShortMediumSignedRow.lean` | `86aa038c8ac7c770ad823fe92fa772d86ae029ee6f87687c0fb27309e5000eff` | `544b6cd68c2a06568f64cd78cff2490f5384a5bf` |
| `ImbalancedChen/P1OriginalSingletonShortMediumTriplePayment.lean` | `5341cb741309772a0936b82a29daecdba7ec0f4a8216c698e6d65a17a9551169` | `a53e2aadf60a9f7c8ab894e974fbd3d7d194d340` |
| `selected-api/ImbalancedChen/P1OriginalSingletonMediumAdmissible.lean` | `2b7326964683702261ad1d3e6db5ae2baa32f2ac9635e438e4b02cde99ecf970` | `282c78415b8050731418aa6e179b651df8a81df0` |
| `selected-api/ImbalancedChen/P1OriginalSingletonMediumLiveRowInventory.lean` | `2769fe6b6d6fb9ddf9783018c48af5bae659ee807bba6c6c9d4ea70a3e3268f6` | `1fdf6f0a9c252f140734c00f821ec3b6238555c2` |
| `selected-api/ImbalancedChen/P1OriginalSingletonMediumRestoringBudget.lean` | `8d1538d1a0bf48bacd415e885ac06802bfa325d7adbefffea354ea25047e03d9` | `f66123effe4f6ee334e22ef87b1807f7da6b396d` |
| `selected-api/ImbalancedChen/P4BOriginalShortMediumTriplePayment.lean` | `89181ef823d4a8477a1ab6fd78640dee3d5730c71442189cfa02f99042cef843` | `75e7de7ef3de1c4bf65bbcc5cfcf7a29b6627483` |
| `selected-api/ImbalancedChen/P4BOriginalMediumRestoringBudget.lean` | `46c014a3256a38df6b19f5c2d33ef5fe9e4f118f14d08df34bdc9ac3a28efc73` | `c19716a15613ef539b43b79e960733cfc9a1888a` |

The manifest labels every one of these sources `source_only: true`,
`compiled: false`, and `kernel_verified: false`. Its recorded packet base is
`47a617fd24a5076f3caa6440058a61c5e13aa75c`; its production-source base is
`be3b6ef8f8459bf7ac2ba5a2f5e2cc9ed009cad8`. Those metadata fields are not
acceptance evidence for the reviewed sources.

## Finding

U06 supplies a precise local removal argument for the original singleton HB
row. It does not establish the complete physical singleton PP estimate. No
circular public hypothesis asserting the desired `signedError`, mode, or
live-row bound was found in the reviewed chain.

Write `R_free I` for the exact terminal source expression

```lean
P5Z.SmoothChartHBDyadicPartition.scalar I.j.val *
  occurrenceAtom kap 6 I.P.N I.cj K kap0 I.j.val I.bs
    (products I.P) (fun q => (free I.P q : ℂ))
```

`exists_live_row_cost` proves that, for each fixed natural logarithmic accuracy
`A`, there is a nonnegative `C` and an eventual physical-`N` threshold such that

```text
norm (R_free I - remainingRow I K) <= C * N / (log N)^A.
```

`eventually_live_row_removed` applies that result with `A = 3` and the existing
normalization bridge to obtain, for every fixed `eta > 0`,

```text
norm (R_free I - remainingRow I K) <= eta * singularNormalization N.
```

### The explicit remainder is retained

For a fibre with `U <= x^(1/16)`, `remainingFibre` is the sum of the complete
post-modulus Fourier tail and the retained-band contribution of all words
outside the selected low-first, length-three subset. For a longer fibre it is
the entire original fibre. `remainingRow` sums these terms over the actual
live complement bank, with the original HB scalar. In the subtraction the
tail cancels because it is retained; U06 does not estimate it away.

The terminal estimate therefore bounds the removed contribution, not the
complete row and not an implicitly zero remainder.

## Signed arithmetic-to-row derivation

1. `P1OriginalSingletonShortMediumTriplePayment.eventually_short_three_signed`
   derives arbitrary logarithmic accuracy for the actual singleton native
   `atom.signedError`. The additional refined-family boundary
   `Q1^3 * (Q2 * Q3)^4 <= V^2 * scale^(-1/100)` is proved from the occupied
   owners, actual raised-action grouping, low-first rank three, and short-head
   condition. It is not left as a new external assumption of the public
   singleton payment theorem.
2. `word_eq_kernel` and `remaining_reconstruction` identify the same restored
   words and complete-modulus signed kernel. `exists_mode_cost` subtracts the
   surviving-word mode and applies the proved native-atom estimate. The real
   and imaginary identities preserve the complex signed expression.
3. The actual original-profile partition covers the live complement bank at
   cap `2N`. Fourier integration pays its L1 norm. The original HB scalar is
   restored once. Local accuracy `A + 82` pays 72 Fourier logarithms, six role
   logarithms, three modulus-owner logarithms, and one complement-count
   logarithm, yielding the stated physical-`N` row bound.

The native atom retains complete product `x = U * V`, physical residue `N`,
the original rough HB head, its complementary convolution, and three actual
occupied modulus owners. The third owner includes the original small Rosser
factor. The raised-action grouping survives through the existing `same_word`
identities; it is not reselected after examining discrepancy. The singleton
uses its own live support at cap `2N`, not a substituted pair-mother cap.

## Crucial coefficient boundary: free to physical rho

The terminal uses `products P` and `free P`. These retain the same original
`Params`, signed word weights, and the same free coefficient in the count and
exact coprime-mean terms. They are nevertheless the analytic comparison
channel after releasing global squarefreeness.

The existing
`docs/source-only/20261112-resume/t05/collision-next/P4BOriginalCollisionTensor.lean`
defines `free` and `error` separately and proves `difference`:

```text
sum over products of free * F - sum over P.S of P.rho * F
  = sum over products of error * F.
```

Thus `free` is not definitionally interchangeable with physical `P.rho`.
Existing generic collision lemmas are useful ingredients, but the U06 terminal
does not apply a complete physical singleton collision/restoration payment.
Its actual support, amplitudes, restoring factors, outer sums, parameter gates,
and common threshold must be supplied when assembling that correction.

The packet `README.md` explicitly states this same `products/free` boundary
and retains long heads, short-head remaining words, post-modulus Fourier tails,
outer chart/HB assembly, trim, and complete PP. This is a faithful partial scope,
not evidence of a mathematical contradiction.

## Hypotheses, uniformity, and circularity check

The terminal fixes `K`, Fourier order, desired accuracy, `omega > 0`, `T`,
and the small parameters before selecting `C` and the eventual threshold. It
then quantifies over the actual index `I`, subject to:

```text
kap < 1
0 < zeta <= 1/20000
0 < kappa <= zeta/200000
kap0 < kappa / (4 * (1 + kappa)),  kap0 < 1
I.P.N = N,  I.P.omega = omega,  I.P.T = T
0 <= I.P.e <= 1/2048,  0 < I.P.q
I.P.T <= zeta,  0 <= I.P.ell,  2 * I.P.ell <= zeta/16
```

The uniform choices precede the actual chart, HB row, selected position,
complement, frequency, word, and occupied-owner choices. The result gives no
numerical `C` or `N0`, and does not assert uniformity when fixed `omega` or `T`
is replaced by an `N`-dependent parameter.

The possible circular-premise points were checked directly:

- `Index` carries original data, selection, occupation, support, and frequency
  conditions, not the desired discrepancy bound.
- `MediumAdmissible` carries geometric and coefficient gates, not the desired
  `signedError` inequality. The admissible subtype is populated using
  `eventually_low_three`.
- Actual singleton `uniform_auxiliary` supplies `UniformAuxiliarySW`, with its
  own all-auxiliary-moduli/coprimality quantifiers. It is not the desired final
  signed-error estimate renamed as a premise.
- Private `mode_restoration` and `fibre_difference` accept intermediate bounds;
  their public callers discharge these inputs using the preceding payment
  theorem and mode estimate.

## Pinned manuscript anchors

Manuscript repository: `UyNewNas/chen-imbalanced-semiprimes`.
Commit: `a988cba584d803ae2856a0de50efb582f4f3dd6a`.
Edition path: `paper/release-20261106/en/`.

The existing local copy used for the review is
`/workspace/scratch/32a3e5d7265b/audit/sources/new/paper/release-20261106/en/`.

| File and stable anchor | Requirement relevant to U06 |
| --- | --- |
| `argument.tex`, `eq:current-PP` | The same physical signed coefficient occurs in the count and exact coprime mean. |
| `argument.tex`, tensor discussion before `eq:current-HB`; `coefficient-appendix.tex`, `coef:tensor-identity`, `coef:collision` | The partition is fixed before estimating discrepancy. Global squarefreeness remains physical; its analytic release requires a separately paid collision correction. |
| `coefficient-appendix.tex`, `coef:HB`, `coef:complete-scales` | Exact order-three HB, retained original smooth chart, at most six variables per original group, and complete-product local scale. |
| `coefficient-appendix.tex`, Fourier discussion after `coef:complete-scales` and `coef:mixed-moment` | Retained modes pay Fourier L1. Post-modulus tails and exact difference zero have separate estimates. |
| `coefficient-appendix.tex`, `coef:rough-SW` | The actual rough slot has the auxiliary-coprimality SW input. |
| `coefficient-appendix.tex`, `coef:prime-product-insertion`, closing assembly paragraph | Full PP assembles remaining branches, chart/scalar costs, prime powers, collisions, and trim at one eventual threshold for the fixed family. |
| `introduction.tex`, `eq:current-normalization` | `H_N = C_N * N / (log N)^2`. |
| `argument.tex`, `lem:current-sharp-prime` | The sharp singleton endpoint still requires the permitted smooth-singleton PP instance and its coefficient hypotheses. |

The manifest's pinned Git blobs for the three cited files are respectively
`90234d94460f1d7d59982635d7bf54c9b19250da` (`argument.tex`),
`10f3e2efb2074a9b97148a5151956e1d450be13f` (`coefficient-appendix.tex`), and
`ff099f8ce9e1d8cbb6a87b92fe59a2622a400252` (`introduction.tex`).

## Classification and retained obligations

The eight omitted canonical U06 modules already have bounded proof bodies in
the packet. Four selected-API revisions are expression/positivity repairs; the
fifth extracts the mother-independent geometric owner-length argument, with
the old pair entry instantiating it. No new mathematical hypothesis or
replacement theorem was found necessary by this static contract review.
Canonical adoption and actual verification remain separate requirements;
unresolved providers or source selection must not be hidden by this review.

For the P1.5 board, retain obligations for physical collision restoration, the
explicit remainder, full chart/HB and fixed-parameter-family assembly,
trim/prime-power/exact-zero and independent reserves, complete same-coefficient
PP, and any downstream quantitative or numerical constants. The local
`eta * H_N` removal theorem alone does not discharge them. These retained
obligations are outside this U06 terminal's claimed scope; their presence is
not by itself proof of a substantive defect in the terminal derivation.

No green-node, closure-completion, or global P1-completion credit follows from
this document. This review concerns current P1.5/U06, not deferred U04/P2.
