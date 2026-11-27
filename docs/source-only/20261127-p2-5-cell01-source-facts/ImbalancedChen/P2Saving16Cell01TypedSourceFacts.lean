import ImbalancedChen.P2OriginalSaving16FiniteCore
import ImbalancedChen.P2Saving16Cell01StoredFloors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The cell01 instances of the existing header and original-facet-index
guards, evaluated on the existing typed payload. The header reuses the
accepted vertex-dimension and simplex-count facts. Its three scalar
equalities are definitional. Only the twelve saved facet-index bounds need
a new finite-array decision; the positive count reduces to `0 < 81`.

This owner does not identify the payload with the original archive and
does not prove source-cell membership, the 96 affine inequalities,
normal balance, face incidence, pulling ownership, or the Q96 endpoint.
-/
namespace ImbalancedChen.P2Saving16Cell01TypedSourceFacts

open P2OriginalSaving16OriginalArchive (originalId)
open P2Saving16Cell01TypedPayload (cell01Payload)

set_option Elab.async false

/-- Exact cell01 specialization of the existing `original_headers`
conjunction, with the decoded payload still explicit. -/
theorem cell01_headers :
    cell01Payload.cellId = originalId (1 : Fin 14) ∧
    cell01Payload.dimension = 8 ∧
    cell01Payload.physicalJacobian = 1 ∧
    (∀ v : Fin cell01Payload.vertices.size,
      (cell01Payload.vertices[v]).size = 8) ∧
    0 < cell01Payload.simplices.size := by
  refine ⟨rfl, rfl, rfl,
    P2Saving16Cell01StoredFloors.cell01_vertex_dimensions, ?_⟩
  rw [P2Saving16Cell01StoredFloors.cell01_simplex_count]
  decide +kernel

/-- The original twelve saved facet IDs address the existing 96-row table.
No assertion about their supporting geometry or completeness is made. -/
theorem cell01_facet_indices :
    ∀ (f : Fin cell01Payload.facetOriginalIndices.size),
      cell01Payload.facetOriginalIndices[f] < 96 := by
  decide +kernel

#print axioms cell01_headers
#print axioms cell01_facet_indices

end ImbalancedChen.P2Saving16Cell01TypedSourceFacts
