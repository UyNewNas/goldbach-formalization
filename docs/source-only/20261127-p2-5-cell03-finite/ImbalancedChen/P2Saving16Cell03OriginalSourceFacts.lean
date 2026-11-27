import ImbalancedChen.P2Saving16Cell03OriginalParse
import ImbalancedChen.P2Saving16Cell03TypedSourceFacts

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the two complete cell03 source-fact guards through the existing
original-archive equality. No parser, decoder, dimensional check, or
facet-index decision is executed again by these proof bodies. The
original dependent Fin indices remain in the conclusions.

The original payload equality and both typed guards must be accepted
before this owner can receive proof credit. These two instances do not
establish any all-fourteen-cell statement or source-cell geometry.
-/
namespace ImbalancedChen.P2Saving16Cell03OriginalSourceFacts

open P2OriginalSaving16OriginalArchive (archive originalId)
open P2Saving16Cell03OriginalParse (cell03_original_archive)
open P2Saving16Cell03TypedPayload (cell03Payload)

theorem cell03_original_headers :
    (archive (3 : Fin 14)).cellId = originalId (3 : Fin 14) ∧
    (archive (3 : Fin 14)).dimension = 8 ∧
    (archive (3 : Fin 14)).physicalJacobian = 1 ∧
    (∀ v : Fin (archive (3 : Fin 14)).vertices.size,
      ((archive (3 : Fin 14)).vertices[v]).size = 8) ∧
    0 < (archive (3 : Fin 14)).simplices.size :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      c.cellId = originalId (3 : Fin 14) ∧
      c.dimension = 8 ∧
      c.physicalJacobian = 1 ∧
      (∀ v : Fin c.vertices.size,
        (c.vertices[v]).size = 8) ∧
      0 < c.simplices.size)
    (show archive (3 : Fin 14) = cell03Payload from cell03_original_archive).symm
    P2Saving16Cell03TypedSourceFacts.cell03_headers

theorem cell03_original_facet_indices :
    ∀ (f : Fin (archive (3 : Fin 14)).facetOriginalIndices.size),
      (archive (3 : Fin 14)).facetOriginalIndices[f] < 96 :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ (f : Fin c.facetOriginalIndices.size),
        c.facetOriginalIndices[f] < 96)
    (show archive (3 : Fin 14) = cell03Payload from cell03_original_archive).symm
    P2Saving16Cell03TypedSourceFacts.cell03_facet_indices

#print axioms cell03_original_headers
#print axioms cell03_original_facet_indices

end ImbalancedChen.P2Saving16Cell03OriginalSourceFacts
