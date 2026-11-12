# Actual HB grouped derivatives: reuse decision

The requested actual original-group higher-order identity already has an unchanged, independently source-reviewed implementation. No new Lean source or arbitrary-overlap induction was written. This packet records the exact actual instance and its existing consumers; it adds no formal or kernel credit and does not close whole PP, the full original-W class, or K.

The inspected P3 snapshot is `chatgpt/p3-internal-original-w-20261105@a29bd6b4cba6d1b7e8cd48165f3a0f76f040082b`. Its `P3HBOriginalGroupJetLeibnizStep` is a genuine one-letter derivative of a finite sum of jets. Its generic allocation API permits arbitrary repeated or overlapping subsets J and arbitrary complex cutoffs. That stronger generic type is not the actual-instance requirement identified below, and its remaining generic reindexing theorem is not marked closed here.

## Actual instance and manuscript scope

Frozen manuscript `9731290e8f53cffda44129906cde6a965eaa869b`, `proof-library/source/distribution-prime-product-completion-20261010.txt`, §2 applies the order-three HB identity separately to each original prime at its scale R_i. Each resulting HB variable has one original owner. The group cutoffs in §4(F) are the resulting factors ψ(c_i exp(sum_group z_j)). The complete-product η cutoff in §2 is a separate coupled factor. Neither source identifies an actual ψ-family consisting of arbitrary overlapping or repeated J_i. Later coupled physical/root/prefix constraints belong to the ambient W; they must retain their own actual derivative or integrated-class suppliers.

The precise old source instance is:

- `owner : Fin m → Fin k`, with J_i the fibre `{a | owner a = i}`. Thus every actual HB occurrence has exactly one group, including repeated owner labels and omitted unit slots.
- `c_i = groupBase owner U i / R i > 0`. Independent group scales are retained; they are not forced equal.
- `actualPsi owner U R z = ∏ i, ψ(groupProduct owner U i z / R i)`.

`P5GroupedOccurrenceLogShift.groupLog_shift` changes exactly the unique owner's group sum. `P5ActualEtaPsiOccurrenceBudget.actualPsi_eq_groupTensor` identifies the literal ψ-product with offsets `b_i = log c_i`. Its existing `occWord_groupTensor` gives, for every ordered list w of actual directions, including repetitions,

    occWord w actualPsi z
      = ∏ i, iteratedDeriv ((w.map owner).count i) psiLog
          (log c_i + groupLog owner i z).

This is the complete higher-order derivative identity for the actual partition product. The allocation choice is forced by each derivative letter's unique owner; there is no missing g-way Leibniz reindexing at this instance. The old source proves the identity by word induction, rather than supplying it as an axiom or derivative-envelope field. It is valid at arbitrary finite m and k; dimension-zero and repeated directions are retained.

## Existing consumers, including complex Fourier values

The actual constructed χ, ψ and η are real. `P5OccurrenceEuclideanMixedIntegral.coordWord_euclideanLift` already transports every ordered occurrence word to the complex-valued Euclidean lift, using the genuine Fréchet chain rule and `Complex.ofRealCLM`. `integral_norm_coordWord` transports the actual derivative L1 integral with the native PiLp measure equivalence. Thus complex Fourier values and independent positive c_i do not require a second arbitrary-complex-cutoff proof.

For the other actual factors, `P5OccurrenceWordFourFactorLeibniz.occWord_four` already supplies the complete ordered four-factor allocation. `P5ActualEtaPsiOccurrenceBudget.exists_actualChart_word_budget` applies it to ambient W, complete-product η, grouped ψ and plateau. This theorem retains the original real `Family.mixedEuler` input; it does not construct that input for every current physical caller.

The Nov10 T06 packet already provides the actual-instance adapter requested by the scope gate:

- `P3ActualHBChildMixedFourier.childLog_iterated_ofReal` converts the actual real cutoff's iterated derivatives to its existing P3 complex child.
- `shiftedChildTensor_physical` retains the distinct rectangle base U and original dyadic base; `occWord_refinedChart_exact` exposes the full coupled ordered allocation, including all cross terms.
- `exists_refined_fourier_budgets` consumes the unchanged all-rank chart and Fourier suppliers, retaining Family.
- `P3ActualUpperPairChildFourier.exists_refinedUpper_fourier_width_budget` is the existing concrete legal-width real upper-pair instance, without an abstract Family input. Its resolution corollary is per chart and does not pay total atlas restoration.

The exact two T06 source hashes are `88da0602726a095332e8f2a32510eacf2afd9ccb2ab303c78bc271cb7fc97ab1` and `56a13fc4c39981762cb47a2f4916558889299d29fb280cb1287824a98f24eb86`. Their unchanged T10 scoped source review is reused. The earlier independent batch30c review also explicitly accepted the actual group tensor counts, translated scales, cutoff constants and occurrence-to-Euclidean conversion. No review is upgraded to an elaboration or kernel receipt.

## Norm and growth boundary

The real cutoff is `eta s = smoothTransition (s-1)`, `chi = 1-eta`, `psi s = eta (2*s)-eta s`. Existing `eta_bounds` gives both eta values in [0,1], hence |ψ|≤1 at order zero by elementary subtraction. No unproved cutoff normalization is introduced. Existing `finite_order_constants` and `groupTensor_word_bound` give uniform scalar constants and a bound M^k; in the actual all-rank consumer k≤kStar is fixed before the target grows, so the old bound M^kStar is a fixed constant. It is not being applied with k equal to a growing atlas count.

The newer generic allocation estimate g^r(3C)^g is not asserted to be polylogarithmic for growing g. Neither that estimate nor a proposed replacement by C^r discharges the separate actual ambient/integrated-W membership or total resolution-dependent atlas/restoring-norm obligation. Those are the precise remaining analytic inputs; this inspection finds no new substantive mathematical gap in the partition ψ-product identity itself.

## Exact source and deployment receipts

`REUSE_MAP.json` pins 15 existing source roots/named predecessors, their direct imports, declaration locations, SHA256 and Git-blob identities, the exact P3 snapshot and manuscript, and the old review receipts. This is a reuse map, not a complete installation manifest.

Seven selected sources have exact bytes in the inspected P3 tree. Six upstream original helpers (`P5GroupedOccurrenceLogShift`, `P5OccurrenceLeibnizAllocation`, `P5AllWordAmbientOccurrenceBound`, `P5GroupedAmbientOccurrenceChain`, `P5MixedEulerTwoStepLeibniz`, `P5AdmissibleAllRankIntegerGeometricFamily`) are recovered at their original ignored `.lake/proof-continuation/source-reviews/drafts/` paths; their bytes match the old frozen registry hashes. Their exact blobs are absent anywhere in that P3 tree. The two T06 adapters likewise are not in that P3 tree. This statement concerns that immutable P3 snapshot only; it does not claim they are absent from every other published branch. Future installation must stage original bytes through an explicitly verified source map and retain the full imports; missing installation is not a reason to reprove the source.

## Status

The scoped reuse audit is complete. New Lean sources: zero. Original/frozen/production sources modified: zero. Whole original-W caller coverage, complete closure installation and remote elaboration/kernel checks, total atlas costs, Medium(M)/spectral supply and actual signed two-atlas PP remain separate. No yellow node or parent status is promoted.

Only source reads, immutable local Git reads and source/hash/JSON metadata were used. No Lean, Lake, LSP, guard, numerical proof evaluation, Git mutation, remote write, CI, quota check or child spawn occurred. The preliminary Mathlib/Lean text snapshots under `reused/` were exploratory reads for the abandoned generic reindexing route; they are not new dependencies or publication files.
