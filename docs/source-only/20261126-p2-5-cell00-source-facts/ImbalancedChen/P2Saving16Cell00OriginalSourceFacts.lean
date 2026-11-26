import ImbalancedChen.P2Saving16Cell00OriginalFloors
import ImbalancedChen.P2Saving16Cell00TypedSourceFacts

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the two complete cell00 source-fact guards through the existing
original-archive equality. No parser, decoder, dimensional check, or
facet-index decision is executed again by these proof bodies. The
original dependent Fin indices remain in the conclusions.

The original payload equality and both typed guards must be accepted
before this owner can receive proof credit. These two instances do not
establish any all-fourteen-cell statement or source-cell geometry.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalSourceFacts

open P2OriginalSaving16OriginalArchive (archive originalId)
open P2Saving16Cell00OriginalFloors (cell00_original_payload)

theorem cell00_original_headers :
    (archive (0 : Fin 14)).cellId = originalId (0 : Fin 14) ∧
    (archive (0 : Fin 14)).dimension = 8 ∧
    (archive (0 : Fin 14)).physicalJacobian = 1 ∧
    (∀ v : Fin (archive (0 : Fin 14)).vertices.size,
      ((archive (0 : Fin 14)).vertices[v]).size = 8) ∧
    0 < (archive (0 : Fin 14)).simplices.size :=
  cell00_original_payload.symm ▸ P2Saving16Cell00TypedSourceFacts.cell00_headers

theorem cell00_original_facet_indices :
    ∀ (f : Fin (archive (0 : Fin 14)).facetOriginalIndices.size),
      (archive (0 : Fin 14)).facetOriginalIndices[f] < 96 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00TypedSourceFacts.cell00_facet_indices

#print axioms cell00_original_headers
#print axioms cell00_original_facet_indices

end ImbalancedChen.P2Saving16Cell00OriginalSourceFacts
