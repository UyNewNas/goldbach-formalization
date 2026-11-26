import ImbalancedChen.P2OriginalSaving16FiniteGeometryCore
import ImbalancedChen.P2Saving16Cell00TypedPayload
import ImbalancedChen.P2Saving16Cell00TypedSourceFacts
import ImbalancedChen.P4AOriginalAscendingCell0Literal96

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The four existing rational geometry guards specialized to Cell00's typed
payload and the unchanged original source-0 physical 96-row table. The
center is the existing first-simplex barycenter, and every saved vertex
is tested against every physical row. Boundary vertices use weak signs.
The facet checks retain the original ten IDs and both full conjunctions.

No row table, vertex, normal weight, facet incidence list, or stored
minimum is copied or substituted. The row owner and these fresh proof
owners require their actual verification; accepted row arithmetic alone
does not supply physical-cell membership. This module does not transport
the typed payload to the original archive, prove coverage or ownership,
or establish the source-region integral or final Q96 endpoint.
-/
namespace ImbalancedChen.P2Saving16Cell00TypedGeometry

open scoped BigOperators
open P2OriginalSaving16OriginalArchive (evalQ interiorCandidate point)
open P2Saving16Cell00TypedPayload (cell00Payload)
open P2Saving16Cell00TypedSourceFacts (cell00_facet_indices)
open P4AOriginalAscendingCell0Literal96 (rows)

set_option Elab.async false

/-- Exact Cell00 specialization of the original strict-center guard. -/
theorem cell00_strict_center :
    ∀ k : Fin 96, 0 < evalQ (rows k).2 (interiorCandidate cell00Payload) := by
  decide +kernel

/-- All saved vertices satisfy all 96 original physical inequalities. -/
theorem cell00_vertices_all96 :
    ∀ (v : Fin cell00Payload.vertices.size) (k : Fin 96),
      0 ≤ evalQ (rows k).2 (point cell00Payload v.val) := by
  decide +kernel

/-- The complete original size, positivity, and normal-balance guard. -/
theorem cell00_positive_normal_balance :
    cell00Payload.positiveNormalBalance.size = cell00Payload.facetOriginalIndices.size ∧
    (∀ f : Fin cell00Payload.facetOriginalIndices.size,
      0 < cell00Payload.positiveNormalBalance.getD f.val 0) ∧
    ∀ j : Fin 8,
      (∑ f : Fin cell00Payload.facetOriginalIndices.size,
        cell00Payload.positiveNormalBalance.getD f.val 0 *
          (rows ⟨cell00Payload.facetOriginalIndices[f], cell00_facet_indices f⟩).2
            j.succ) = 0 := by
  decide +kernel

/-- The full original facet-list size and membership/zero equivalence. -/
theorem cell00_facet_incidence :
    cell00Payload.facetOriginalIndices.size = cell00Payload.facetVertices.size ∧
    ∀ (f : Fin cell00Payload.facetOriginalIndices.size)
      (v : Fin cell00Payload.vertices.size),
        (v.val ∈ (cell00Payload.facetVertices.getD f.val #[]).toList ↔
          evalQ (rows ⟨cell00Payload.facetOriginalIndices[f], cell00_facet_indices f⟩).2
            (point cell00Payload v.val) = 0) := by
  decide +kernel

#print axioms cell00_strict_center
#print axioms cell00_vertices_all96
#print axioms cell00_positive_normal_balance
#print axioms cell00_facet_incidence

end ImbalancedChen.P2Saving16Cell00TypedGeometry
