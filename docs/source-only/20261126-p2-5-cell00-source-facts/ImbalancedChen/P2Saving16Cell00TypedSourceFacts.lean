import ImbalancedChen.P2OriginalSaving16FiniteCore
import ImbalancedChen.P2Saving16Cell00StoredFloors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The cell00 instances of the existing header and original-facet-index
guards, evaluated on the existing typed payload. The header reuses the
accepted vertex-dimension and simplex-count facts. Its three scalar
equalities are definitional. Only the ten saved facet-index bounds need
a new finite-array decision; the positive count reduces to `0 < 8`.

This owner does not identify the payload with the original archive and
does not prove source-cell membership, the 96 affine inequalities,
normal balance, face incidence, pulling ownership, or the Q96 endpoint.
-/
namespace ImbalancedChen.P2Saving16Cell00TypedSourceFacts

open P2OriginalSaving16OriginalArchive (originalId)
open P2Saving16Cell00TypedPayload (cell00Payload)

set_option Elab.async false

/-- Exact cell00 specialization of the existing `original_headers`
conjunction, with the decoded payload still explicit. -/
theorem cell00_headers :
    cell00Payload.cellId = originalId (0 : Fin 14) ∧
    cell00Payload.dimension = 8 ∧
    cell00Payload.physicalJacobian = 1 ∧
    (∀ v : Fin cell00Payload.vertices.size,
      (cell00Payload.vertices[v]).size = 8) ∧
    0 < cell00Payload.simplices.size := by
  refine ⟨rfl, rfl, rfl,
    P2Saving16Cell00StoredFloors.cell00_vertex_dimensions, ?_⟩
  rw [P2Saving16Cell00StoredFloors.cell00_simplex_count]
  decide +kernel

/-- The original ten saved facet IDs address the existing 96-row table.
No assertion about their supporting geometry or completeness is made. -/
theorem cell00_facet_indices :
    ∀ (f : Fin cell00Payload.facetOriginalIndices.size),
      cell00Payload.facetOriginalIndices[f] < 96 := by
  decide +kernel

#print axioms cell00_headers
#print axioms cell00_facet_indices

end ImbalancedChen.P2Saving16Cell00TypedSourceFacts
