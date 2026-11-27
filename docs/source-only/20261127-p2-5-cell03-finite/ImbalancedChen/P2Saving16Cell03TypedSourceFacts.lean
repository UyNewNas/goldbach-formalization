import ImbalancedChen.P2OriginalSaving16FiniteCore
import ImbalancedChen.P2Saving16Cell03StoredFloors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The cell03 instances of the existing header and original-facet-index
guards, evaluated on the existing typed payload. The header reuses the
accepted vertex-dimension and simplex-count facts. Its three scalar
equalities are definitional. Only the 11 saved facet-index bounds need
a new finite-array decision; the positive count reduces to `0 < 21`.

This owner does not identify the payload with the original archive and
does not prove source-cell membership, the 96 affine inequalities,
normal balance, face incidence, pulling ownership, or the Q96 endpoint.
-/
namespace ImbalancedChen.P2Saving16Cell03TypedSourceFacts

open P2OriginalSaving16OriginalArchive (originalId)
open P2Saving16Cell03TypedPayload (cell03Payload)

set_option Elab.async false

/-- Exact cell03 specialization of the existing `original_headers`
conjunction, with the decoded payload still explicit. -/
theorem cell03_headers :
    cell03Payload.cellId = originalId (3 : Fin 14) ∧
    cell03Payload.dimension = 8 ∧
    cell03Payload.physicalJacobian = 1 ∧
    (∀ v : Fin cell03Payload.vertices.size,
      (cell03Payload.vertices[v]).size = 8) ∧
    0 < cell03Payload.simplices.size := by
  refine ⟨rfl, rfl, rfl,
    P2Saving16Cell03StoredFloors.cell03_vertex_dimensions, ?_⟩
  rw [P2Saving16Cell03StoredFloors.cell03_simplex_count]
  decide +kernel

/-- The original 11 saved facet IDs address the existing 96-row table.
No assertion about their supporting geometry or completeness is made. -/
theorem cell03_facet_indices :
    ∀ (f : Fin cell03Payload.facetOriginalIndices.size),
      cell03Payload.facetOriginalIndices[f] < 96 := by
  decide +kernel

#print axioms cell03_headers
#print axioms cell03_facet_indices

end ImbalancedChen.P2Saving16Cell03TypedSourceFacts
