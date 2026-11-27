import ImbalancedChen.P2Saving16Cell01OriginalParse
import ImbalancedChen.P2Saving16Cell01TypedSourceFacts

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the two complete cell01 source-fact guards through the existing
original-archive equality. No parser, decoder, dimensional check, or
facet-index decision is executed again by these proof bodies. The
original dependent Fin indices remain in the conclusions.

The original payload equality and both typed guards must be accepted
before this owner can receive proof credit. These two instances do not
establish any all-fourteen-cell statement or source-cell geometry.
-/
namespace ImbalancedChen.P2Saving16Cell01OriginalSourceFacts

open P2OriginalSaving16OriginalArchive (archive originalId)
open P2Saving16Cell01OriginalParse (cell01_original_archive)
open P2Saving16Cell01TypedPayload (cell01Payload)

theorem cell01_original_headers :
    (archive (1 : Fin 14)).cellId = originalId (1 : Fin 14) ∧
    (archive (1 : Fin 14)).dimension = 8 ∧
    (archive (1 : Fin 14)).physicalJacobian = 1 ∧
    (∀ v : Fin (archive (1 : Fin 14)).vertices.size,
      ((archive (1 : Fin 14)).vertices[v]).size = 8) ∧
    0 < (archive (1 : Fin 14)).simplices.size :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      c.cellId = originalId (1 : Fin 14) ∧
      c.dimension = 8 ∧
      c.physicalJacobian = 1 ∧
      (∀ v : Fin c.vertices.size,
        (c.vertices[v]).size = 8) ∧
      0 < c.simplices.size)
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    P2Saving16Cell01TypedSourceFacts.cell01_headers

theorem cell01_original_facet_indices :
    ∀ (f : Fin (archive (1 : Fin 14)).facetOriginalIndices.size),
      (archive (1 : Fin 14)).facetOriginalIndices[f] < 96 :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ (f : Fin c.facetOriginalIndices.size),
        c.facetOriginalIndices[f] < 96)
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    P2Saving16Cell01TypedSourceFacts.cell01_facet_indices

#print axioms cell01_original_headers
#print axioms cell01_original_facet_indices

end ImbalancedChen.P2Saving16Cell01OriginalSourceFacts
