# OriginalFloors: explicit equality motives

This is an uncompiled proof-expression candidate. It retains all ten public theorem statements, the original payload-equality proof, the two imports, every option and every existing assumption. Only nine proof bodies change. There are no new definitions, public declarations or private helpers. `SOURCE_IDENTITY.json` records a reverse replacement that reconstructs the original source bytes exactly.

## Actual observation

The parent reported actual P3 attempt008 task `5011f1278a684d54b873533f8e562676`: OriginalFloors normal timed out with exit 124 after 600.331 seconds. Its log is empty, SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`. The aggregate result SHA is `a95712c736aea7495c6a41916e82b1f27d04772e2584fed50c13486ce6bb33dd`; the export is being retrieved separately. The empty log does not identify an individual failed theorem or establish a specific internal reduction stack.

The same attempt reproduced all ten missing dependency objects with their original hashes, then accepted OriginalParse through normal, independent replay and complete owned audit. That Parse object has SHA-256 `5bb7d93c7f336040afae0aedfb5b5f26c5c78f9a61400738ca2f299c0760c03f`, with seven owned declarations. Its source and accepted gates are not changed or rerun by this candidate. OriginalArithmetic and OriginalSourceFacts were still pending; they are not recorded as failures.

## Existing theorem reused

Lean 4.33.0-rc1 already supplies the opaque theorem:

```lean
theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α}
    (h₁ : a = b) (h₂ : motive a) : motive b
```

The candidate applies that existing theorem with an explicit motive over a symbolic `CellRecord`. For example, simplex count becomes:

```lean
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      c.simplices.size = 8)
    cell00_original_payload.symm
    P2Saving16Cell00StoredFloors.cell00_simplex_count
```

The other eight motives are the corresponding unchanged complete conclusions with only the record `archive (0 : Fin 14)` replaced by the variable `c`. This includes the original dependent `Fin` indices, simplex shape conjunction, per-row stored-floor identities and both sums. The same existing typed supplier discharges every premise. No finite certificate is evaluated again, and the original separate Q96 floors are retained.

The runtime source `Lean/Elab/BuiltinNotation.lean` implements `▸` by abstracting occurrences from the expected type, checking a synthesized motive and constructing an equality recursor. `Init/Prelude.lean` already defines `Eq.subst` as a theorem. Explicitly applying this opaque theorem avoids the automatic motive search and direct specialized recursor expression. This is a targeted resource hypothesis supported by the expression shape and the earlier successful Parse symbolic-wrapper pattern; the candidate still requires actual strict compilation, kernel replay and the full owned audit. It is not described as already resolving the timeout.

## Pending consumers with the same expression shape

The existing OriginalArithmetic source has two closed transports: `cell00_original_simplex_operations` and `cell00_original_floor_numerator`. The former can use the existing `Eq.subst` with motive `fun c => ∀ s : Fin c.simplices.size, simplexValid c s`. The latter can use the original complete geometric-floor-sum expression as its motive and the existing `cell00_geometric_floor_sum` supplier. Its present `unfold cellFloorNumerator` is a separate named-definition conversion; if an actual later diagnostic identifies that conversion as expensive, the accepted Parse pattern suggests putting only that conversion into a private theorem with a symbolic cell index and a conclusion headed by `cellFloorNumerator i`.

OriginalSourceFacts has two closed transports: the complete `cell00_original_headers` conjunction and `cell00_original_facet_indices`. Their exact motives are already present in their public statements; abstracting the record preserves `originalId (0 : Fin 14)` and all dependent facet/vertex indices. Both existing typed facts remain the complete suppliers.

Those two original pending source files have not been changed. Exact optional before/after candidates and patches are now retained separately under `optional-pending-consumers/`, with `CANDIDATES_NOT_SELECTED.json` explicitly recording their pending status and exclusion from the primary `SOURCE_OVERRIDE.json`. They change only the same four closed equality-transport bodies; the arithmetic candidate retains its existing `unfold cellFloorNumerator`, and adds no symbolic bridge or other helper. Neither pending owner is claimed to have failed or passed. No new general transport theorem is needed because `Eq.subst` already provides it.

## Manuscript and acceptance boundary

These statements transport previously checked cell00 record facts through the accepted original parser/decoder equality. They do not add a numerical or analytic hypothesis, establish a new manuscript theorem, or alter the November 6 extraction formulas. In particular, stored Jensen floors are still distinguished from geometric `jensenQ` values, and no fourteen-cell aggregate, pulling ownership, physical-cell geometry, integral endpoint or P2.5 claim is added.

`SOURCE_OVERRIDE.json` gives the exact new source specification and original preimage. The parent and the separate v9 driver owner handle original receipt retrieval, current-context qualification, publication and compilation. No Lean or remote task was run while preparing this source candidate.
