# Cell00: typed arithmetic to the original archive

**SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.** This package adds one
module with two theorem declarations. No Lean execution, cloud task,
production installation, accepted object, or acceptance-ledger change is
included. Public preparation baseline:
`5cc2b181f51be2f20ce316256fe2cdf3e691ca69`. The metadata-equivalent local
commit `408e38f61774924a39ef5975d34c1bad506fec7a` has the identical tree
`557620248a0437258cc2090d7d3c40cbc897ede2`; this equality was checked
directly from both Git commit objects.

## Exact proposed conclusions

```lean
cell00_original_simplex_operations :
  ∀ s : Fin (archive (0 : Fin 14)).simplices.size,
    simplexValid (archive (0 : Fin 14)) s

cell00_original_floor_numerator :
  cellFloorNumerator (0 : Fin 14) = 13236428172062120
```

The first theorem transports
`P2Saving16Cell00AllRowsArithmetic.cell00_simplex_operations` through
`P2Saving16Cell00OriginalFloors.cell00_original_payload`. Its index remains
the original dependent `Fin (archive 0).simplices.size`; it is not replaced
by a new eight-element model. The second unfolds only the existing
`cellFloorNumerator` and transports `cell00_geometric_floor_sum` through
the same equality. It therefore concerns the actual geometric expression
in `P2OriginalSaving16FiniteCore`, not merely the stored `jensenFloor` or
`jensenBound` record fields.

There is no new numerical decision. In particular the source neither
decides the original parser again nor recomputes the accepted stored
floors, determinants, means, or Jensen values. Its two imports use the
existing finite-core namespace and do not import the pending all-cell
`P2OriginalSaving16FiniteArchive` or its analytic owner.

## Reuse and pending prerequisites

Existing current source, retained preimages, local reference sources, and
the tracked history of the consumer/remaining-arithmetic packages were
searched before authoring. The existing all-cell
`original_simplex_operations` and `original_q96_aggregate` are source-only
closed checks; they do not supply an accepted cell00 transport certificate.
No equivalent accepted cell00 bridge was found. GitHub default-branch code
search for `cellFloorNumerator` and commit search for `cell00` returned no
results; those empty indexes are not treated as proof that no other branch
has work. The exact existing suppliers below are reused without edits.

| Supplier | Exact contribution | Gate at preparation |
| --- | --- | --- |
| `P2Saving16Cell00OriginalFloors.cell00_original_payload` | `archive 0 = cell00Payload`, through the original parser and decoder | Pending FieldDecode and the existing Decoded, OriginalParse and OriginalFloors consumers |
| `P2Saving16Cell00AllRowsArithmetic.cell00_simplex_operations` | All eight original eleven-conjunct guards on the typed payload | Row00 is accepted; Row01–Row07 and the all-row owner still require their gates |
| `P2Saving16Cell00AllRowsArithmetic.cell00_geometric_floor_sum` | Eight separately floored geometric Jensen values sum to `13236428172062120` | Same all-eight-row dependency |
| This module | Equality transport to the original dependent guard and original cell numerator | No compilation, replay or owned audit attempted |

The current FieldDecode attempt002 did not pass; a source
candidate or failed same-name object cannot satisfy the first row. The
exact successful FieldDecode source selection must be recorded when
available. This package selects no replacement FieldDecode source and
cannot authorize reuse of a failed object.

Before accepting this owner, a future runner must select the exact two
direct-import sources pinned in `MANIFEST.json`, bind every transitive
accepted dependency to its own source/object/receipt, and use one project
module provider. OriginalFloors and AllRowsArithmetic must each have
strict normal compilation, independent kernel replay and complete owned
declaration audit, including private/generated declarations. This module
must then pass the same three gates. The actual owned declaration count
is pending; the source count of two is not an audit count. Successful
verification would close precisely the two cell00 conclusions above.

## Correspondence with the November 6 manuscript

The reviewed manuscript is
`UyNewNas/chen-imbalanced-semiprimes@a988cba584d803ae2856a0de50efb582f4f3dd6a`,
`paper/release-20261106/en/`. Exact file hashes are in `MANIFEST.json`.

`argument.tex`, equation `eq:current-eighth-saving`, specifies the saving
density

\[
  \frac{4(M-R_6)}{(R_6-S_8)(M-S_8)\prod_{i=1}^{8}t_i}.
\]

Its accompanying paragraph excludes a Chen quarter and an ordering
factorial. The unchanged `FiniteCore` expressions retain the factor four,
the two residual factors and eight coordinate factors, the original
comparison cap, and the `1/1000000` buffered cap. The `8!` divisor in
physical simplex volume is the determinant-to-volume conversion; it does
not introduce a density ordering factorial.

`numerical-appendix.tex`, equation `num:simplex-moment` and its preceding
paragraph, require rational vertices tested against the original affine
inequalities, face incidences and pulling triangulation, and give the
exact barycentric moment formula. For dimension eight this is consistent
with the existing volume divisor `8!`, mean-gap divisor `9`, and weighted
factor-mean divisor `10`. This bridge uses those unchanged definitions
through the existing row proofs. It does not itself prove the moment
formula or source geometry.

The same appendix permits a nonnegative positive saving to be bounded on
an inner subset. That is the justification for reusing the existing
owned-support lower-bound chain without adding whole-cell exhaustion as
a new requirement. Exact membership and nonoverlap of the selected
supports still need their existing proofs. The cell00 numerator above is
the certificate value already present in `Cell00StoredFloors`, not a
claim that this integer is printed in the manuscript.

No substantive manuscript proof gap is inferred from these two transport
steps. Their remaining issues are dependency acceptance and Lean
elaboration/resource validation. The existing finite incidence and
pulling checks remain concrete verification obligations.

## What remains after this cell00 bridge passes

This section maps existing obligations; it introduces no replacement
proof source. A single accepted cell00 bridge does not make any listed
all-cell theorem accepted.

| Obligation | Existing owner or theorem to reuse | Contribution still required |
| --- | --- | --- |
| Original decoding of the other thirteen cells | `P2OriginalSaving16FiniteArchive.original_parse_success_tag`, then its existing `original_parse_success` | Archive indices 1–13, corresponding to original source IDs 1,2,3,4,5,6,8,9,10,11,12,13,14; retain original parser, decoder and input order |
| Every remaining simplex guard | `P2OriginalSaving16FiniteArchive.original_simplex_operations` | Original eleven-conjunct `simplexValid` for all rows of those thirteen cells; cell00 supplies only the index-0 instance |
| Full Q96 aggregate | `P2OriginalSaving16FiniteArchive.original_q96_aggregate` | The other thirteen original cell numerators and the exact fourteen-term sum `1222997719565324892497827`; retain separate simplex floors |
| Both archive counts | `P2OriginalSaving16FiniteArchive.original_counts` | Original totals `39741` simplices and `39381` active8 records; cell00 contributes 8 and 45 respectively, but does not certify the other totals |
| Original physical source facts | `P2OriginalSaving16OriginalArchive` | Its existing seven closed checks: `original_headers`, `original_patterns`, `original_strict_centers`, `original_vertices_all96`, `original_facet_indices`, `original_positive_normal_balance`, `original_facet_incidence` |
| Original pulling data | `P2OriginalSaving16PullingOwnership` | Its existing `original_faces_parse_tag`, `original_face_incidence_shape`, `original_pulling_bindings`; face-ledger decoding is not a new full-text parse |
| Geometric and integral chain | `P2OriginalSaving16JensenFloor`, `P2OriginalSaving16SimplexBinding`, `P2OriginalSaving16PullingFaceInduction`, `P2OriginalSaving16PullingOwnership`, `P2OriginalSaving16OwnedIntegral` | Compatible normal/replay/complete-owned acceptance of the existing finite-to-real Jensen, source-closure, separating-wall and almost-everywhere ownership chain through `historical_endpoint_le_source_integral` |
| Whole P2.5 assembly | Existing `ACCEPTANCE_SCOPE.md` and its named Full87/common-schedule/signed-compiler suppliers | One compatible ordinary fourteen-cell account, the retained seventy-three Full87 complement terms and signed harmful complement, actual fourth-bank/parent/history binding, one compiler reserve, and the exact same-coefficient P3 distribution input |

At the level of the existing unaccepted global count targets, removing
cell00 leaves `39741 - 8 = 39733` simplex rows and `39381 - 45 = 39336`
active8 records. These are bookkeeping differences of the proposed
global targets, not new formal count certificates. No per-cell record is
generated here. The existing all-cell proof names and statements should
be retained when their proof bodies can be composed from accepted
individual certificates. This package does not modify them.
