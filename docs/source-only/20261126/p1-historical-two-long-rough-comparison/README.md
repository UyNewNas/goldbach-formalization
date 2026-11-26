# P1.5: original historical rough comparison on actual singleton scales

**SOURCE ONLY / NOT ELABORATED / NO LEAN OR KERNEL ACCEPTANCE. P1.5 remains open.**

This additive packet continues baseline `dc1e74ee5c15471d6dd22e4e2c609d5e79b0169d` on `work/p1-5-actual-means-20261125`. It connects the existing finite positive Brun comparison to the original historical P1 coefficient, and supplies the finite scalar gates at the actual singleton block scale. Existing source contracts are reused; their prior acceptance status is not upgraded here.

## New source

| File | Main new interface | Scope |
|---|---|---|
| `P1OriginalHistoricalTwoLongRoughComparison.lean` | `finite_rough_comparison` | Finite rough-minus-upper estimate on the original historical modulus set and signed coefficient |
| Same file | `historical_shortSequence_rough_comparison` | Original ordered, signed short sequence; its mass comes from the existing mass theorem, and the upper polynomial is identified with `historicalRowCore` |
| `P1OriginalSingletonRoughComparison.lean` | `eventually_actual_singleton_rough_comparison_gates` | Actual-cutoff epsilon, Brun support, short-slot caps and physical historical modulus bounds |
| Same file | `eventually_actual_singleton_rough_comparison` | Instantiation on the actual singleton rectangle, with those gates discharged |

The two files contain 3 public definitions, 10 public theorem source candidates and 1 private helper theorem. None receives new formal acceptance in this packet.

## Finite comparison and its proof structure

Let `Q = historicalModuli B old fresh N cap w z`, `rho = historicalRho old fresh N cap w z L`, and let `alpha` be a finite signed short sequence. Write

\[
\mu=\sum_m\lVert\alpha_m\rVert,\qquad
Y=Z^{2j+1},\qquad
\varepsilon=\operatorname{brunEpsilon}(j,\operatorname{smallPrimes}(Z)).
\]

For the actual left/right Mellin profiles and their positive smooth envelopes `E,J`, the new finite source derives

\[
\begin{aligned}
\lVert H_{\mathrm{rough}}-H_{UU}\rVert
\le{}&2\operatorname{p2Price}(E,J)Y^2\mu\operatorname{momentBudget}(D)\\
&+2\mu\operatorname{meanPrice}(\delta,U)
      \operatorname{meanPrice}(\delta,V)R(D)\\
&\quad\cdot\left(2UV\varepsilon\operatorname{densityLog}(x)
       +2\operatorname{densityLog}(x)(U+V)Y+2Y^2\right),
\end{aligned}
\]

where `R(D) = (4 * (1 + log(max 1 D)))^16`. Both historical sums have exactly the same `Q`, complex `rho`, physical target `N`, and original short coefficient. The difference is between the two literal rough masks and the upper/upper Brun polynomial.

The proof calls existing suppliers as follows:

1. `actual_pair_E3` gives the two positive gap products and twice the exact mean. Profile labels and log flags remain distinct from the two Brun gap flags.
2. `polynomial_P2` and `historical_modulus_moment` pay the two gap-polynomial discrepancies.
3. `gapPairMean_point` receives the actual factorial epsilon through `gap_density_B2`. The exact coprime mean retains one inverse totient and the non-coprime-short zero branch.
4. The nonnegative terms with divisor powers 0, 1 and 2 are bounded by the fourth power. The original `sum_divisor_fourth_moment_le_log` then pays their sum on the same historical modulus set.
5. `smoothBrunTupleCore_eq_expansion` and a finite reindexing identify the upper polynomial with the original `historicalRowCore`. `shortSequence_mass` supplies the mass of the original ordered signed pushforward.

**The epsilon term acquires only a fixed logarithmic reciprocal moment. It does not acquire `D`, `Y` or another subpower factor.** The `momentBudget D` term belongs to the polynomial discrepancy payment. The proof introduces no gap-mean, P2, short-mass or desired-discrepancy estimate as an assumed analytic input.

This follows the frozen [1106 coefficient appendix](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/8ca3f6a7f6bbaf6f67c96e80a5065eca9838e703/paper/release-20261106/en/coefficient-appendix.tex), especially the positive rough-product gap and two-rough-error argument. Its exact file binding is in `SOURCE_BINDINGS.json`.

## Actual singleton instantiation

The caller uses the original active rectangle, the selected distinct long positions, and the original low-short-position condition. It fixes

\[
X_0=\prod_a\operatorname{lower}(b_a),\quad
Z=\operatorname{beforeHBCutoff}(\mathrm{cutoffOrder},[c_j]),\quad
J=\operatorname{halfOrder}(X_0),\quad
D=\lfloor X_0^{1199/2000}\rfloor.
\]

The existing `FixedScaleTransport`, `FixedRectangleScale` and `ActualBrunDensity` interfaces supply `1 < X0`, `1 <= Z`, `Z^(2*J+1) <= X0`, `epsilon <= 1`, each short-slot cap, and the original historical bound `q <= D`. In particular, epsilon at most one follows by choosing unit density constants and zero logarithmic orders, rewriting by the original full-scale identity, and cancelling the positive `X0`.

The short sequence still uses `ShortPositions i k`, `hbCutoff cj`, `xi a.val` and `rowRoles j a.val`. Its mass is bounded by

\[
\operatorname{shortScale}(\mathrm{shortBlocks})
\,(1+\log X_0)^{|\operatorname{ShortPositions}(i,k)|}.
\]

No empty-index, unit-block or short-coprimality exclusion is added. The eventual physical threshold precedes the variable chart, row, profile order, tuple, historical policies, delta and all frequencies. The caller retains the original geometric conditions and `0 < delta <= 1/4`; it does not assume the scalar gates it is meant to supply.

## Source adoption and ownership

To adopt this packet, map its two Lean files to their `ImbalancedChen` module paths and retain the existing selected providers. This packet is not a standalone complete import closure.

The historical side uses the existing [P2 packet](../p1-historical-two-long-p2/) and [rough packet](../p1-historical-two-long-rough/). The rough packet's three shared owners remain `P1HistoricalTwoLongBrunSubstitutionData`, `P1HistoricalTwoLongExactPairMeanData` and `P1HistoricalTwoLongFiniteRoughData`. The six Brun support/coefficient declarations remain owned by `p1-historical-two-long-p2/support/Part3TwoLongBrunSupport.lean`.

Use the rough packet's `selected-api/P4BOriginalCoprimeSmoothE1.lean` and `selected-api/P4BOriginalPositiveLongEnvelope.lean`, with their previously registered import-only routes. If old providers enter the selected closure, use their existing complementary postimages: `Part3TwoLongLiteralBrunSubstitution`, `P4BOriginalSameRhoCoprimeE1`, `P4BOriginalPairMeanNorm`, `P4BOriginalTwiceMeanPayment`, `P4BOriginalRoughPairFinite`, `P4BOriginalEnvelopePolynomialPayment`, and the P2 packet's `Part3TwoLongActualLowerBrunMoment`. Do not also install the unstripped archived versions beside the shared owners.

The singleton side follows [ActualBrunDensity](../p1-singleton-actual-brun-density/) through `FixedScaleTransport`, `FixedRectangleScale`, physical support, finite two-long geometry and the original short-mass interface. Preserve the existing complementary providers for `P1OriginalSingletonPhysicalLevel` and `P4BOriginalNoMediumPairRows`. If the later complete dictionary is adopted, preserve the existing `SameRhoFibres` / complementary `P4BOriginalTwoLongActualDictionary` pair as well.

The authoritative original extraction and ownership records are:

- [rough extraction binding](../p1-historical-two-long-rough/EXTRACTION_BINDING.json) and [rough source review](../p1-historical-two-long-rough/SOURCE_REVIEW.json);
- [Brun support extraction binding](../p1-historical-two-long-p2/support/EXTRACTION_BINDING.json);
- [fixed rectangle extraction binding](../p1-singleton-fixed-rectangle-scale/EXTRACTION_BINDING.json) and [review](../p1-singleton-fixed-rectangle-scale/SOURCE_REVIEW.json);
- [two-long dictionary review](../p1-singleton-two-long-dictionary/SOURCE_REVIEW.json).

No old provider or build/acceptance driver is changed by this packet. The 13 entries in `SOURCE_BINDINGS.json` bind the directly reviewed source contracts, not the entire transitive closure.

## Review and observed verification limits

Independent static review checked the source APIs, exact coefficients and means, the finite sums, all scalar-gate conjunctions, threshold placement, and the final caller. One concrete issue was found: the caller's multiplication association differed from the supplier despite a bare `exact`. The caller now uses the supplier's identical left association. The final review found no remaining blocking source-review findings.

Final file hashes, declaration inventory, the fixed review finding and explicit declined judgments are recorded in `STATIC_REVIEW.json`. All 13 pinned input files matched their byte lengths, SHA-256 and baseline Git blobs. Both new files passed the forbidden-proof-token scan. These are static source checks, not Lean tests.

Observed compiler status on 2026-11-26:

- The user-designated P1 private 32 GB service returned `McpServerError: Session terminated` (`INVALID_ARGUMENT`, JSON-RPC 32600) on system information and retrieval of old task `job_cda017c5183c4b5ba80a8a2182f446ba`. That task's current result remains unknown.
- The previously designated Cloud Compile fallback reported Lean `4.33.0-rc1` and Mathlib `e4c91783ca8e6a7c693ae624ade32fd22d4e43c1`, matching the project pin. Its read-only workspace-inventory command was rejected with `retained-job limit reached; ask owner to archive jobs`. No command task was created. No archive tool was exposed.
- No local Lean executable was available in the inspected locations. No new normal build, kernel check or full-owned-declaration audit ran.

The existing fourteen-target resumption queue and its original evidence remain unchanged. In particular, the old M batch is still failed overall; its separately accepted Licensed result is not treated as acceptance of the whole batch. P1.5 is not added to the closed-node PR.

## Remaining boundaries

The inherited `Part3TwoLongFixedMRectangularCore` source is still unavailable. Its registered SHA-256 is `2be2789f712144fc7411849340caafe2c5caa2dc6de9ad96125590a9e9374b8b`. This packet neither reconstructs it nor substitutes a new proof. The existing Fourier/selector source boundaries also remain: `P2OriginalFiniteTentBankSelectorMargins`, `P5AllRankMixedFourierPointwise`, `P5AllRankCauchyKernelIntegral`, `P5PositiveFourProfileLocalZeroSmooth`, `P5ActualFourNativeBoxFullNorm`, `P5OriginalFourSelectedSmoothWBindingGap`, and `P5AllWordAmbientOccurrenceBound`.

Mathematically, the new connection concerns smooth two-long rough profiles and the same upper core. The original sharp strips and Fourier reconstruction, final outer HB/chart/selector budget, full signed medium contribution, and common-threshold historical terminal still need their existing source chains completed and verified. The four scalar error-rate suppliers already present on the baseline are reused conceptually; this packet does not duplicate them or claim that their final outer assembly has been completed.
