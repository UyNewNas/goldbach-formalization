import ImbalancedChen.P2Saving16Cell00OriginalParse
import ImbalancedChen.P2Saving16Cell00StoredFloors

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the checked payload's eight stored-floor identities, finite
indexing facts, and sums to the unchanged original `archive (0 : Fin 14)`.
The exact original text, complete reader value, and original typed decoder
are connected by the selected OriginalParse consumer.

The stored Jensen bound is still a field of the decoded record. These
statements do not prove that it equals `jensenQ` of the vertices, and do
not prove `simplexValid`, any all-cell finite guard, or P2.5. The last sum
contains eight separate Q96 floors in the original simplex order.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalFloors

open P2OriginalSaving16OriginalArchive (archive)
open P2OriginalSaving16JensenFloor (q96Floor)
open P2Saving16Cell00TypedPayload (cell00Payload)
open P2Saving16Cell00OriginalParse (cell00_original_archive)
open scoped BigOperators

theorem cell00_original_payload : archive (0 : Fin 14) = cell00Payload :=
  cell00_original_archive

theorem cell00_original_simplex_count :
    (archive (0 : Fin 14)).simplices.size = 8 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_simplex_count

theorem cell00_original_active8_count :
    (archive (0 : Fin 14)).active8.size = 45 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_active8_count

theorem cell00_original_vertex_count :
    (archive (0 : Fin 14)).vertices.size = 16 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_vertex_count

theorem cell00_original_vertex_dimensions :
    ∀ v : Fin (archive (0 : Fin 14)).vertices.size,
      ((archive (0 : Fin 14)).vertices[v]).size = 8 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_vertex_dimensions

theorem cell00_original_simplex_shape :
    ∀ s : Fin (archive (0 : Fin 14)).simplices.size,
      let r := (archive (0 : Fin 14)).simplices[s]
      r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧
      (∀ k : Fin 9, r.vertexIds.getD k.val 0 < (archive (0 : Fin 14)).vertices.size) ∧
      r.gapWeightedMeans.size = 10 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_simplex_shape

theorem cell00_original_stored_jensen_floors :
    ∀ s : Fin (archive (0 : Fin 14)).simplices.size,
      ((archive (0 : Fin 14)).simplices[s]).jensenFloor =
        q96Floor ((archive (0 : Fin 14)).simplices[s]).jensenBound :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_stored_jensen_floors

theorem cell00_original_stored_floor_guard :
    (∀ s : Fin (archive (0 : Fin 14)).simplices.size,
      ((archive (0 : Fin 14)).simplices[s]).jensenFloor =
        q96Floor ((archive (0 : Fin 14)).simplices[s]).jensenBound) ∧
    (archive (0 : Fin 14)).simplices.size = 8 ∧
      (archive (0 : Fin 14)).active8.size = 45 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_stored_floor_guard

theorem cell00_original_stored_jensen_floor_sum :
    (∑ s : Fin (archive (0 : Fin 14)).simplices.size,
      ((archive (0 : Fin 14)).simplices[s]).jensenFloor) = 13236428172062120 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_stored_jensen_floor_sum

theorem cell00_original_separate_stored_floor_sum :
    (∑ s : Fin (archive (0 : Fin 14)).simplices.size,
      q96Floor ((archive (0 : Fin 14)).simplices[s]).jensenBound) = 13236428172062120 :=
  cell00_original_payload.symm ▸ P2Saving16Cell00StoredFloors.cell00_separate_stored_floor_sum

#print axioms cell00_original_payload
#print axioms cell00_original_stored_jensen_floors
#print axioms cell00_original_simplex_shape
#print axioms cell00_original_stored_floor_guard
#print axioms cell00_original_separate_stored_floor_sum

end ImbalancedChen.P2Saving16Cell00OriginalFloors
