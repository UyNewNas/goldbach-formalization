import ImbalancedChen.P2Saving16Cell01OriginalSourceFacts
import ImbalancedChen.P2Saving16Cell01TypedGeometry

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the four complete typed Cell01 geometry guards through the
existing original-payload equality. All 96 physical rows, the strict
center condition, weak vertex inequalities, positive normal-balance
conjunction, and facet-incidence equivalences remain unchanged. The
dependent facet bounds use the existing original source-fact theorem.

This thin consumer needs the actual accepted Cell1Affine.rows1 and TypedGeometry
dependency context. It does not import or prove the global fourteen-cell
guards, source-domain closure, geometric separation, integral comparison,
or final Q96 endpoint. No numerical calculation is repeated here.
-/
namespace ImbalancedChen.P2Saving16Cell01OriginalGeometry

open scoped BigOperators
open P2OriginalSaving16OriginalArchive (archive evalQ interiorCandidate point)
open P2Saving16Cell01OriginalParse (cell01_original_archive)
open P2Saving16Cell01TypedPayload (cell01Payload)
open P2Saving16Cell01OriginalSourceFacts (cell01_original_facet_indices)
open P4AOriginalAscendingCell1Affine (rows1)

/-- The original first-simplex center is strict for every physical row. -/
theorem cell01_original_strict_center :
    ∀ k : Fin 96, 0 < evalQ (rows1 k).2 (interiorCandidate (archive (1 : Fin 14))) := by
  exact Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ k : Fin 96, 0 < evalQ (rows1 k).2 (interiorCandidate c))
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    P2Saving16Cell01TypedGeometry.cell01_strict_center

/-- Every original saved vertex satisfies all 96 weak physical inequalities. -/
theorem cell01_original_vertices_all96 :
    ∀ (v : Fin (archive (1 : Fin 14)).vertices.size) (k : Fin 96),
      0 ≤ evalQ (rows1 k).2 (point (archive (1 : Fin 14)) v.val) := by
  exact Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ (v : Fin c.vertices.size) (k : Fin 96),
        0 ≤ evalQ (rows1 k).2 (point c v.val))
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    P2Saving16Cell01TypedGeometry.cell01_vertices_all96

/-- Preserve size, positivity of every weight, and all eight balance equations. -/
theorem cell01_original_positive_normal_balance :
    (archive (1 : Fin 14)).positiveNormalBalance.size =
        (archive (1 : Fin 14)).facetOriginalIndices.size ∧
    (∀ f : Fin (archive (1 : Fin 14)).facetOriginalIndices.size,
      0 < (archive (1 : Fin 14)).positiveNormalBalance.getD f.val 0) ∧
    ∀ j : Fin 8,
      (∑ f : Fin (archive (1 : Fin 14)).facetOriginalIndices.size,
        (archive (1 : Fin 14)).positiveNormalBalance.getD f.val 0 *
          (rows1 ⟨(archive (1 : Fin 14)).facetOriginalIndices[f],
            cell01_original_facet_indices f⟩).2 j.succ) = 0 := by
  exact (Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ hf : (∀ f : Fin c.facetOriginalIndices.size, c.facetOriginalIndices[f] < 96),
        c.positiveNormalBalance.size =
            c.facetOriginalIndices.size ∧
        (∀ f : Fin c.facetOriginalIndices.size,
          0 < c.positiveNormalBalance.getD f.val 0) ∧
        ∀ j : Fin 8,
          (∑ f : Fin c.facetOriginalIndices.size,
            c.positiveNormalBalance.getD f.val 0 *
              (rows1 ⟨c.facetOriginalIndices[f],
                hf f⟩).2 j.succ) = 0)
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    (fun _ => P2Saving16Cell01TypedGeometry.cell01_positive_normal_balance)) cell01_original_facet_indices

/-- Preserve facet-list size and the full original membership/zero equivalence. -/
theorem cell01_original_facet_incidence :
    (archive (1 : Fin 14)).facetOriginalIndices.size =
        (archive (1 : Fin 14)).facetVertices.size ∧
    ∀ (f : Fin (archive (1 : Fin 14)).facetOriginalIndices.size)
      (v : Fin (archive (1 : Fin 14)).vertices.size),
        (v.val ∈ ((archive (1 : Fin 14)).facetVertices.getD f.val #[]).toList ↔
          evalQ (rows1 ⟨(archive (1 : Fin 14)).facetOriginalIndices[f],
            cell01_original_facet_indices f⟩).2
              (point (archive (1 : Fin 14)) v.val) = 0) := by
  exact (Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ hf : (∀ f : Fin c.facetOriginalIndices.size, c.facetOriginalIndices[f] < 96),
        c.facetOriginalIndices.size =
            c.facetVertices.size ∧
        ∀ (f : Fin c.facetOriginalIndices.size)
          (v : Fin c.vertices.size),
            (v.val ∈ (c.facetVertices.getD f.val #[]).toList ↔
              evalQ (rows1 ⟨c.facetOriginalIndices[f],
                hf f⟩).2
                  (point c v.val) = 0))
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    (fun _ => P2Saving16Cell01TypedGeometry.cell01_facet_incidence)) cell01_original_facet_indices

#print axioms cell01_original_strict_center
#print axioms cell01_original_vertices_all96
#print axioms cell01_original_positive_normal_balance
#print axioms cell01_original_facet_incidence

end ImbalancedChen.P2Saving16Cell01OriginalGeometry
