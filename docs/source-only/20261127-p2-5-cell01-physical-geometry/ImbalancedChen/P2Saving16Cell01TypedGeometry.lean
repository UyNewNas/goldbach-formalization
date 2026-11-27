import ImbalancedChen.P2OriginalSaving16FiniteGeometryCore
import ImbalancedChen.P2Saving16Cell01TypedPayload
import ImbalancedChen.P2Saving16Cell01TypedSourceFacts
import ImbalancedChen.P4AOriginalAscendingCell1Affine

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The four existing rational geometry guards specialized to Cell01's typed
payload and the unchanged original source-1 physical 96-row table. The
center is the existing first-simplex barycenter, and every saved vertex
is tested against every physical row. Boundary vertices use weak signs.
The facet checks retain the original twelve IDs and both full conjunctions.

No row table, vertex, normal weight, facet incidence list, or stored
minimum is copied or substituted. The row owner and these fresh proof
owners require their actual verification; accepted row arithmetic alone
does not supply physical-cell membership. This module does not transport
the typed payload to the original archive, prove coverage or ownership,
or establish the source-region integral or final Q96 endpoint.
-/
namespace ImbalancedChen.P2Saving16Cell01TypedGeometry

open scoped BigOperators
open P2OriginalSaving16OriginalArchive (evalQ interiorCandidate point)
open P2Saving16Cell01TypedPayload (cell01Payload)
open P2Saving16Cell01TypedSourceFacts (cell01_facet_indices)
open P4AOriginalAscendingCell1Affine (rows1)

set_option Elab.async false

/-- Exact Cell01 specialization of the original strict-center guard. -/
theorem cell01_strict_center :
    ∀ k : Fin 96, 0 < evalQ (rows1 k).2 (interiorCandidate cell01Payload) := by
  decide +kernel

/-- All saved vertices satisfy all 96 original physical inequalities. -/
theorem cell01_vertices_all96 :
    ∀ (v : Fin cell01Payload.vertices.size) (k : Fin 96),
      0 ≤ evalQ (rows1 k).2 (point cell01Payload v.val) := by
  decide +kernel

/-- The complete original size, positivity, and normal-balance guard. -/
theorem cell01_positive_normal_balance :
    cell01Payload.positiveNormalBalance.size = cell01Payload.facetOriginalIndices.size ∧
    (∀ f : Fin cell01Payload.facetOriginalIndices.size,
      0 < cell01Payload.positiveNormalBalance.getD f.val 0) ∧
    ∀ j : Fin 8,
      (∑ f : Fin cell01Payload.facetOriginalIndices.size,
        cell01Payload.positiveNormalBalance.getD f.val 0 *
          (rows1 ⟨cell01Payload.facetOriginalIndices[f], cell01_facet_indices f⟩).2
            j.succ) = 0 := by
  decide +kernel

/-- The full original facet-list size and membership/zero equivalence. -/
theorem cell01_facet_incidence :
    cell01Payload.facetOriginalIndices.size = cell01Payload.facetVertices.size ∧
    ∀ (f : Fin cell01Payload.facetOriginalIndices.size)
      (v : Fin cell01Payload.vertices.size),
        (v.val ∈ (cell01Payload.facetVertices.getD f.val #[]).toList ↔
          evalQ (rows1 ⟨cell01Payload.facetOriginalIndices[f], cell01_facet_indices f⟩).2
            (point cell01Payload v.val) = 0) := by
  decide +kernel

#print axioms cell01_strict_center
#print axioms cell01_vertices_all96
#print axioms cell01_positive_normal_balance
#print axioms cell01_facet_incidence

end ImbalancedChen.P2Saving16Cell01TypedGeometry
