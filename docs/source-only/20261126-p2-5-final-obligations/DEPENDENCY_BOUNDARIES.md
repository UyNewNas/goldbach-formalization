# P2.5: existing proof chain and remaining acceptance boundaries

Read-only source review on 2026-11-26. No production source, staged file,
verification gate, compiler state, or acceptance flag is changed by this note.
This is a dependency checklist, not a proof-completion receipt.

## Frozen manuscript target

Manuscript commit `3ffa2d159c9974e2ca6d5f930c0f2c16baa0135e`:

- `paper/release-20261106/en/numerical-appendix.tex`, `num:upper-table`,
  certificate field `/upper_saving_bounds/15`: `G16 >= 1543640141 / 10^14`.
- `argument.tex`, `eq:current-eighth-saving`, and `sieve-appendix.tex`,
  `sv:eighth-range` / `sv:eighth-density`: the density is
  `4*(M-R6)/((R6-S8)*(M-S8)*product(t_i))`.
- `proof-library/source/eighth-prefix-family-20261009.tex`: original ascending
  IDs `0,1,2,3,4,5,6,8,9,10,11,12,13,14`, 14 cells, 39,741 simplices,
  `R=L3=R6=D(t2+t3)`, `M=A(t1+t8)-10^-6`, Jacobian 1,
  simplex volume `abs(det)/8!`, separate simplex Q96 floors.
- The exact adopted floor numerator is
  `1222997719565324892497827`, with denominator `2^96`.
  Old cell 7's `74010257929342545968375/2^96` is a separate slot and must not
  be added to this 14-cell certificate. No Chen factor `1/4` or ordering
  factorial is introduced in the density.

These manuscript locations and formulas were cross-checked by the manuscript
review agent. This note uses that review rather than repeating retrieval.

## Existing numerical-to-integral chain: reuse, do not rewrite

All module paths in this table are under `ImbalancedChen/`. Namespace prefixes
are `ImbalancedChen.`; use the namespace actually declared in each file.

| Boundary | Existing exact declarations | Remaining work |
| --- | --- | --- |
| Original bytes to decoded cells | `P2OriginalSaving16FiniteArchive.lean`: namespace `P2OriginalSaving16OriginalArchive`, `original_parse_success_tag`, `original_parse_success` | Obtain current acceptance of all 14 original parses. Reuse accepted cell00 decoding and equality transports. |
| Actual rational vertices to actual simplex operations | Same file: `original_simplex_operations`; specification `simplexValid` in `P2OriginalSaving16FiniteCore.lean` | Prove/accept all 11 conjuncts for each original simplex, including determinant, gap, ten means, Jensen expression and individual floor. Stored field values alone are insufficient. |
| Actual individual floors to exact total | Same file: `original_q96_aggregate`; `P2OriginalSaving16OriginalArchive.lean`: `original_q96_aggregate_real` | Accept the sum of 39,741 separately computed floors, not a floor of the sum. |
| Actual vertices to the original 96-row cell closure | `P2OriginalSaving16OriginalArchive.lean`: `original_strict_centers`, `original_vertices_all96`, `original_vertex_mem_closure` | Accept the finite original-row checks. The closure theorem already derives the analytic inclusion. |
| One actual simplex to its integral | `P2OriginalSaving16JensenFloor.lean`: `original_simplex_jensen`, `original_simplex_q96`; `P2OriginalSaving16SimplexBinding.lean`: `jensenQ_cast`, `original_row_q96` | Compile/replay/audit these existing proofs after their dependencies. `original_row_q96` already supplies all geometry and encoding premises from the same original witness. |
| Every simplex to the double integral sum | `P2OriginalSaving16SimplexBinding.lean`: `historical_endpoint_le_sum_simplex_integrals` | No new summation theorem is needed. It combines the exact aggregate and all per-simplex inequalities. |
| Original pulling data to null within-cell overlaps | `P2OriginalSaving16PullingOwnership.lean`: `original_face_incidence_shape`, `original_pulling_bindings`, `original_row_separator`, `original_within_cell_null_overlap` | Accept original face parsing/incidence/pulling identities and the existing separating-hyperplane proof. |
| Null overlaps to the actual 14-cell integral | `P2OriginalSaving16OwnedIntegral.lean`: `ownedSupport_pairwise_disjoint`, `ownedUnion_integral`, `original_simplex_integral_sum_le_source_integral`, `historical_endpoint_le_source_integral` | Accept the existing inner-union proof. It already concludes the exact historical lower bound on the actual source region, without assuming that lower bound. |

The necessary finite geometry leaves for the ownership argument are
`original_facet_indices` and `original_facet_incidence` in OriginalArchive,
plus the finite pulling shape and binding statements. The ownership route
requires a disjoint positive inner union; it does **not** need an exhaustive
triangulation or proof that every cell point is in a saved simplex.

`original_headers`, `original_patterns`, `original_counts`, and
`original_positive_normal_balance` are additional existing source assertions.
They should retain their ordinary module verification; they must not be
misdescribed as logically necessary new geometric premises of OwnedIntegral.
In particular, the current final theorem does not consume normal-balance or
whole-cell coverage.

### Cell00 work that is already available

- `P2Saving16Cell00Decoded.cell00_decode` has a current accepted receipt in
  `docs/verification/20261126-p2-5-resumed/consumer-attempt005/`.
- Existing consumer candidate `P2Saving16Cell00OriginalParse` transports
  decoding to the exact original `archive 0`; its current continuation is
  managed by the parent task.
- Existing `P2Saving16Cell00OriginalArithmetic` in
  `docs/source-only/20261126-p2-5-cell00-original-arithmetic/ImbalancedChen/`
  supplies `cell00_original_simplex_operations` and
  `cell00_original_floor_numerator = 13236428172062120`, reusing the typed
  AllRowsArithmetic proofs. Do not redo the eight determinants or floors.
- `P2Saving16Cell00OriginalFloors` proves stored-field floor facts. Those are
  useful transports, but they alone do not establish `jensenQ` at actual
  vertices; the OriginalArithmetic bridge is the missing distinction.
- Existing cell00 finite geometry/pulling candidates and the parent's
  original-archive transports should be reused. Their source presence gives
  no acceptance credit until actual checks pass.
- These cell00 statements cover eight simplices. Their acceptance will not
  establish the 13 other cells or the all14 aggregate.

## Actual 96 rows and full87 source: existing exact connection

`ImbalancedChen/P2OriginalSaving16Full87SourceBinding.lean` already contains:

- `original_rows_exact`: all `14*96` original ordered affine rows, each of
  their nine rational coefficients, equal the full87 ascending source rows.
- `sourceRows_iff_full87_source`, `region_eq_full87_sourceUnion`:
  equality of the actual sources, not merely matching navigation IDs.
- `source_selected_and_cap`: selected mask `{0,7}`, new cap `M`, comparison `R`.
- `source_histories_at_own_third_prefix`: history bounds against the
  **ideal** third-prefix cap. Its conclusion is not an actual lambda6 bound.

`ImbalancedChen/P2Saving16Full87IntegralIdentity.lean` already contains:

- `sourceDensity_eq_kernel`, `atlasCell_integral_eq`,
  `region_integral_eq_sum_full87_cells`;
- `full87_integral_eq_fourteen_add_complement`: exact decomposition into
  the 14-cell region and the other 73 full87 cells.

This is the correct direct adapter for the G16 source contribution. Once a
full87 sum already includes these cells, G16 cannot be subtracted again as an
additional independent gain.

## Actual causal history and one common schedule

The detailed manuscript explicitly warns that raw `L3=R` is not a lower bound
for an arbitrary already frozen actual third cap. The required construction
uses a common refinement of the first three coordinates before `N` and before
the eight-prime child. Existing source candidates already address this:

| Existing file under `docs/source-only/` | Declaration and exact role |
| --- | --- |
| `20261102-resume-30k/saving16_glue/P2OriginalSaving16HistoricalMesh.lean` | `exists_actual_historical_mesh`: one original historical mesh, fixed before `N`/child, puts all four histories below its third exponent and that exponent below `R` on the full retained trim. |
| `20261102-resume-30k/saving16_glue/P2OriginalSaving16CommonOldPolicy.lean` | `exists_common_actual_parent_on_trim`: actual first stop and third support, `lambda3 <= lambda6 <= R`, all required history bounds, unchanged old fifth gain, without an assumed `current <= R` port. |
| Same file | `exists_uniform_realized_frontier_gain`: feeds that actual parent into the existing arithmetic residual comparison. It is a pointwise residual theorem, not a prime-sum limit. |
| `20261102-resume-30o/saving16_weak_face/P2OriginalFourteenWholeFamilyLower.lean` | `exists_actual_whole_family_lower_at_original_cutoff`: whole-family lower bound with its harmful complement paid. |
| `20261102-resume-30s/s11_saving16_complete/P2OriginalSaving16WholeIntegralPresieve.lean` | `exists_original_bank_whole_integral_schedule`: one original archive/history schedule and the whole integral for the literal fourteen splice on `policy6`. The file explicitly leaves full-sixth/full87 chronology separate. |
| `20261110-yellow-closure-10t/t03_saved87_actual_gain/P4AOriginalFull87OrdinarySignedGain.lean` | `common_history_on_trim`: supplies `HistoryOnTrim` from `P4AOriginalFull87ActualCommonHistory.exists_original_common_history`, with shared `e`, `q`, displacement and a threshold stable for all later `q`. |

Do not insert an equality between the old literal-fourteen splice and the
final full87 compiled tree. Use the actual full87 chronology/schedule source
selection when joining those endpoints. The existing lightweight relocation
and recovered source packages identify that selection without changing any
mathematical statement:

- `20261126-p2-5-lightweight-original-schedule/`;
- `20261126-p2-5-original-schedule-recovery/`;
- `20261125-p2-5-fourteen-family/owners/` postimages, not pre-extraction owners.

## Signed compiler: existing identities versus a remaining estimate

The exact finite signed split is already implemented in production
`P2Saving16NegativeFiniteCore.lean` and
`P2Saving16FourteenNegativeFibrePartition.lean`:
`negativeInner_exact_split14` retains all fourteen selected pair families and
one unchanged complement. The signed coefficient, original small divisor,
full rough word and full modulus are retained.

Existing source-only `P2Saving16R17StrictFourteenCorners.r17_strict_fourteen_corners`
and `P2Saving16FourteenCornerReciprocalResidual.r17_error_at_fourteen_corners`
are under `20261125-p2-5-fourteen-family/ImbalancedChen/`. They combine:

- all96 closed-box source geometry and actual upper-corner cap gates;
- ordinary occurrences on the actual schedule;
- one beta, aligned mesh `k`, `N0`, complete `Q` and compiled `rho`;
- the exact identity `realPhysicalDistributionError b N T Q rho = E`;
- a counting upper bound which still includes `E`, `ceil z`, and `T+1`.

The recovered `P2Saving16All96ClosedBox.all96_same_Q_signed_product` already
supplies all96 source rows and the literal same-Q signed product. The
lightweight `P4AOriginalR17PaidIntegral.original_signed_density_and_count_below`
already supplies the density and counting comparison on one shared schedule.
Do not recreate these wrappers.

**Still absent from this selected chain is the required quantitative bound on
that exact `realPhysicalDistributionError`**, on the same compiled `Q/rho` and
the same beta/mesh/threshold schedule, strong enough with the retained tails
for the final endpoint. An exact expansion of `E` is not such an estimate.
This is a remaining analytic proof obligation, rather than a Lean expression
or import-compatibility problem. This review has not established that the
manuscript assertion is false or that no proof exists elsewhere.

## Minimal completion order and status limits

1. Finish current analytic dependency acceptance using the already prepared
   round6 repairs. Round5 accepted AffineSimplexGeometry and Q96FloorCore,
   but not FourteenPhysicalAtlas, CellOwnership, JensenFloor, Full87SourceBinding,
   Full87IntegralIdentity, NegativeFiniteCore or FourteenNegativeFibrePartition.
2. Accept the existing cell00 equality consumers and finite geometry chain;
   use the original per-cell definitions for the remaining 13 cells and
   preserve the actual all14 total/ownership claims.
3. Accept the existing SimplexBinding/PullingOwnership/OwnedIntegral chain.
   The exact G16 integral lower endpoint then already has its theorem.
4. If exposing the manuscript's decimal-rational table entry, the remaining
   display adapter is only the exact comparison
   `1543640141/10^14 <= 1222997719565324892497827/2^96`, followed by transitivity.
   No existing Lean occurrence of the decimal numerator was found in the
   targeted production/source-only search; this adapter is not the missing
   analytic proof.
5. Use the existing actual full87 schedule and same-Q/rho identities for the
   arithmetic interpretation. A claim about the final compiled counting
   endpoint additionally requires the quantitative error supplier described
   above; finite certificate acceptance alone cannot supply it.

Current round5 receipt:
`docs/verification/20261126-p2-5-resumed/p2-round5-attempt005/RUN_RESULT.json`.
It records 336/377 normal successes, 44/69 owned targets accepted,
`accepted=false`, `P2_5_proved=false`. This note makes no claim about the
currently submitted round6 until its actual receipt is available.
