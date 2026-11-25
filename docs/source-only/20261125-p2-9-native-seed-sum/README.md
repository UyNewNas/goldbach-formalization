# Exact positive-seed sum on fixed native coordinates

Status: **SOURCE_ONLY_UNCOMPILED**. Formal, kernel, endpoint and new-native credit: **0**.

## Exact increment

`P2FiniteMarkedGamma5NativeSeedSum.lean` supplies the missing finite sum dictionary from the original positive seed positions to the existing fixed native coordinate chart. It uses the actual original selector, actual dependent `LevelIndex`, literal selected reads and original edge coefficients.

For a fixed depth `d`, `Index d` consists of a shape sequence `Fin d → StepShape` with no transport edge, and its owner/choice sequence `Fin d → ReadLabel`. This type contains no target `N`, root precision, root prime or continuous parameter. The existing finite-index theorem supplies its finiteness. At depth 430, every coordinate tuple has the original distinguished root slot and precisely the active slots of each edge.

For any test `F : ℕ → List ℕ → ℝ`, the first public sum theorem proves

\[
\sum_{p\in\mathrm{originalBand}(N,k)}
 \sum_{\ell\in\mathrm{seedPositions}(N,n,k,t,p)}
 \mathrm{levelMark}(\ell)\,F(p,\mathrm{old}(\ell))
 =
 \sum_{i:\mathrm{Index}(430)}\sum_x
 1_{\mathrm{literalSelected}(i,x)}\,
 \mathrm{fixedWeight}(i)\,F(x_{\rm root},\mathrm{coordinateOld}(i,x)).
\]

The left side is the original sum, written directly in the theorem statement. The right side has a unique contribution for each original occurrence. No sign or smoothness assumption on `F` is required.

Under the original conditions `2 ≤ N`, `0 ≤ t ≤ 1/12` and `1/(n+1) ≤ 11/384`, the second sum theorem replaces the literal occurrence predicate by the already-defined real set
`P2FiniteMarkedGamma5RealSelectedPrefix.selected n k t i.shape i.reads` evaluated at `physicalPrime N∘x`. Its coordinate carrier `primeTuples` retains the exact original root band and requires every actual native slot to be prime and coprime to `N`. These conditions are derived from the original source, not imposed as a new deletion.

The public endpoints are:

- `seed_sum_eq_literal_coordinates`: exact original seed/mark/old-word sum for every `N,n,k,t`.
- `literal_iff_selected`: exact identification with the existing selected real domain on the original prime carrier.
- `seed_marked_sum_eq_selected_coordinates`: the combined coordinate sum under the original scale and parameter conditions.
- `coordinate_weight`: original product of edge weights equals a constant depending only on the fixed shape/read index.

## Why the reindexing preserves occurrences

The proof uses the existing `accepts_iff_unique_reads` and `recover_path`. Equality of two decoded codes first gives equality of the shape sequence from the literal edge list; the unique checked reads then determine every owner and choice; the original root and each active edge slot recover the complete tuple.

The source-side index is still the original dependent `LevelIndex N n k t p 0`. The already-proved `history_itinerary_nodup`, restricted to the original level list, supplies its path injectivity. A single `Finset.sum_bij` transports the whole finite sum. Products of primes never serve as equality keys.

Native pair slots keep the original small/large order. The old word is computed by the original `replay` and `nextRequest`, so its distinct append convention is also retained. Repeated prime values remain separate labelled coordinates. Retained and other zero-arity edges introduce no dummy prime summation; the retained owner remains in the read label.

`fixedWeight` evaluates the existing edge-weight product at dummy `Fin(0+1)` coordinates. This merely defines a coefficient independent of `N`. The existing `pathAt_weight_independent` proves equality with the actual coefficient. No primality, acceptance or physical path at target zero is claimed.

## Source of the prime and coprime conditions

The original `original_band_prime` theorem states `p.Prime ∧ p.Coprime N`. Its proof reads both properties from `chenAdditivePrimeCarrier`. In particular, coprimality is not inferred from `p < N`.

For the remaining native slots, the source proof uses `root_coherent`, the original `ChosenPath`, `child_admission` and `child_coherent`. Each active slot belongs to the exact `appendedWord` of that edge. Thus all arithmetic conditions on `primeTuples` are already true for each selected occurrence.

## Deduplication and manuscript scope

The following existing suppliers were inspected and reused or distinguished:

| Existing supplier | Existing result | Role here |
|---|---|---|
| `FixedNativeItinerary` | Fixed index finiteness, unique reads, path recovery, fixed coefficient | Reused directly |
| `SelectedSeedTerminal` | Original positive seed iff full accepted path and positive terminal read | Reused directly |
| `RealSelectedPrefix` | Existing real selected set iff the literal seed/read predicate | Reused directly |
| `EmittedPathMultiplicity` | No duplicate itinerary in original history | Reused for source position injectivity |
| `EmittedWordBox` | Shape/old-word mark bounds and decoding | Checked; it does not provide this native coordinate sum |
| `OwnedRootCounts` | Exact root-class marked count and first-prime shell | Checked; different root-count dictionary |
| `ActualRadialAggregate` | Exact partition by shape/old word and original root cells | Checked; it does not replace moving positions by fixed NativeSlot tuples |
| `NativePrefixFubini` | Joint native-coordinate integral strip limits | Checked; no discrete seed-sum reindexing |

The source-only and active inventories at the fixed project baseline and the new suppliers in commit `12dd8b011185ef351a80bae40cd240993ad6f288` were checked. No identical existing complete seed-to-native-coordinate consumer was found. This is a focused audit, not a claim that a default-branch keyword search exhausts every historical object.

The manuscript anchor is [1106 sieve appendix, finite marked families and retained slots](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L494-L531), together with its [fixed finite queries and boundary treatment](https://github.com/UyNewNas/chen-imbalanced-semiprimes/blob/a988cba584d803ae2856a0de50efb582f4f3dd6a/paper/release-20261106/en/sieve-appendix.tex#L1090-L1101). The new step is a finite indexing/transport deduction omitted from that prose, not a new analytic theorem.

## Exact source selection and verification boundary

The coherent source-selection baseline is commit `12dd8b011185ef351a80bae40cd240993ad6f288` and
`docs/verification/20261125-p2-9-geometric-family/CURRENT_SOURCE_SELECTION.json`,
blob `8dcc05f4d7d1debdc87128fc8f68a82129870c9b`. Retain its effective overrides and owner postimages. No accepted or queued module is changed by this package.

The new source blob is `785864d13f6abf37ef29c93d72ea728ffd7ffc38`.
Its UTF-8 SHA256 is `701bff06d02e91450c837f7901b37e0bdf6438993709b64dc37d90a562f1b50f`
(17,021 bytes; 360 lines). Exact direct and reused supplier bindings appear in `REGISTRY.json`.

Author static review and independent full-source mathematical review by `/root/p29_review` passed. The Git blob was read back and matched the source bytes and SHA256. **No compiler, kernel replay, full-owned audit or receiving-closure acceptance was run for this module.** The inherited mixed history closure remains unqualified; the root audit reports five unlocated old supplier nodes and `RealizedBuchstabSupply` in that boundary. Earlier accepted thin modules do not qualify this consumer automatically.

This package does not smooth the selected indicator, prove a selected-boundary arithmetic payment, identify a global `J`, supply a same-`rho` prime-product estimate, or realize an arbitrary subset `B` as a smooth geometric selection. It does not introduce H247/native-Wu compatibility endpoints as manuscript necessities.
