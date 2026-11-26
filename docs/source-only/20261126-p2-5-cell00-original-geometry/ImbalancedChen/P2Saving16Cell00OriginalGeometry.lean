import ImbalancedChen.P2Saving16Cell00OriginalSourceFacts
import ImbalancedChen.P2Saving16Cell00TypedGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the four complete typed Cell00 geometry guards through the
existing original-payload equality. All 96 physical rows, the strict
center condition, weak vertex inequalities, positive normal-balance
conjunction, and facet-incidence equivalences remain unchanged. The
dependent facet bounds use the existing original source-fact theorem.

This thin consumer needs the actual accepted Literal96 and TypedGeometry
dependency context. It does not import or prove the global fourteen-cell
guards, source-domain closure, geometric separation, integral comparison,
or final Q96 endpoint. No numerical calculation is repeated here.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalGeometry

open scoped BigOperators
open P2OriginalSaving16OriginalArchive (archive evalQ interiorCandidate point)
open P2Saving16Cell00OriginalFloors (cell00_original_payload)
open P2Saving16Cell00OriginalSourceFacts (cell00_original_facet_indices)
open P4AOriginalAscendingCell0Literal96 (rows)

/-- The original first-simplex center is strict for every physical row. -/
theorem cell00_original_strict_center :
    ∀ k : Fin 96, 0 < evalQ (rows k).2 (interiorCandidate (archive (0 : Fin 14))) := by
  simpa only [cell00_original_payload] using
    P2Saving16Cell00TypedGeometry.cell00_strict_center

/-- Every original saved vertex satisfies all 96 weak physical inequalities. -/
theorem cell00_original_vertices_all96 :
    ∀ (v : Fin (archive (0 : Fin 14)).vertices.size) (k : Fin 96),
      0 ≤ evalQ (rows k).2 (point (archive (0 : Fin 14)) v.val) := by
  simpa only [cell00_original_payload] using
    P2Saving16Cell00TypedGeometry.cell00_vertices_all96

/-- Preserve size, positivity of every weight, and all eight balance equations. -/
theorem cell00_original_positive_normal_balance :
    (archive (0 : Fin 14)).positiveNormalBalance.size =
        (archive (0 : Fin 14)).facetOriginalIndices.size ∧
    (∀ f : Fin (archive (0 : Fin 14)).facetOriginalIndices.size,
      0 < (archive (0 : Fin 14)).positiveNormalBalance.getD f.val 0) ∧
    ∀ j : Fin 8,
      (∑ f : Fin (archive (0 : Fin 14)).facetOriginalIndices.size,
        (archive (0 : Fin 14)).positiveNormalBalance.getD f.val 0 *
          (rows ⟨(archive (0 : Fin 14)).facetOriginalIndices[f],
            cell00_original_facet_indices f⟩).2 j.succ) = 0 := by
  simpa only [cell00_original_payload] using
    P2Saving16Cell00TypedGeometry.cell00_positive_normal_balance

/-- Preserve facet-list size and the full original membership/zero equivalence. -/
theorem cell00_original_facet_incidence :
    (archive (0 : Fin 14)).facetOriginalIndices.size =
        (archive (0 : Fin 14)).facetVertices.size ∧
    ∀ (f : Fin (archive (0 : Fin 14)).facetOriginalIndices.size)
      (v : Fin (archive (0 : Fin 14)).vertices.size),
        (v.val ∈ ((archive (0 : Fin 14)).facetVertices.getD f.val #[]).toList ↔
          evalQ (rows ⟨(archive (0 : Fin 14)).facetOriginalIndices[f],
            cell00_original_facet_indices f⟩).2
              (point (archive (0 : Fin 14)) v.val) = 0) := by
  simpa only [cell00_original_payload] using
    P2Saving16Cell00TypedGeometry.cell00_facet_incidence

#print axioms cell00_original_strict_center
#print axioms cell00_original_vertices_all96
#print axioms cell00_original_positive_normal_balance
#print axioms cell00_original_facet_incidence

end ImbalancedChen.P2Saving16Cell00OriginalGeometry
