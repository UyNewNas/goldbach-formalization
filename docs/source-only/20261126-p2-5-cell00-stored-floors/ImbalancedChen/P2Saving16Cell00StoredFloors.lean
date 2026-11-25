import ImbalancedChen.P2Saving16Cell00TypedPayload
import ImbalancedChen.P2OriginalSaving16Q96FloorCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Candidate arithmetic certificates for the eight stored cell00 simplex
bounds.  Each row uses the unchanged original `q96Floor` definition and
the exact typed-payload candidate.  The longest, 338-character bound in
row04 is checked first so a future strict run reaches that obligation first.

These statements do not identify the payload with the original decoder,
or a stored Jensen bound with `jensenQ` of the corresponding vertices.
They establish neither `simplexValid` nor any all-cell archive guard.
The sum below contains eight separate floors, in original simplex order.
-/
namespace ImbalancedChen.P2Saving16Cell00StoredFloors

open P2Saving16Cell00TypedPayload
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators

set_option Elab.async false

theorem simplex04_stored_jensen_floor :
    simplex04.jensenFloor = q96Floor simplex04.jensenBound := by decide +kernel

theorem simplex00_stored_jensen_floor :
    simplex00.jensenFloor = q96Floor simplex00.jensenBound := by decide +kernel

theorem simplex01_stored_jensen_floor :
    simplex01.jensenFloor = q96Floor simplex01.jensenBound := by decide +kernel

theorem simplex02_stored_jensen_floor :
    simplex02.jensenFloor = q96Floor simplex02.jensenBound := by decide +kernel

theorem simplex03_stored_jensen_floor :
    simplex03.jensenFloor = q96Floor simplex03.jensenBound := by decide +kernel

theorem simplex05_stored_jensen_floor :
    simplex05.jensenFloor = q96Floor simplex05.jensenBound := by decide +kernel

theorem simplex06_stored_jensen_floor :
    simplex06.jensenFloor = q96Floor simplex06.jensenBound := by decide +kernel

theorem simplex07_stored_jensen_floor :
    simplex07.jensenFloor = q96Floor simplex07.jensenBound := by decide +kernel

theorem cell00_simplex_count : cell00Payload.simplices.size = 8 := by rfl

theorem cell00_active8_count : cell00Payload.active8.size = 45 := by rfl

theorem cell00_vertex_count : cell00Payload.vertices.size = 16 := by rfl

theorem cell00_vertex_dimensions :
    ∀ v : Fin cell00Payload.vertices.size,
      (cell00Payload.vertices[v]).size = 8 := by decide +kernel

/-- Only the finite indexing and array-size conjuncts of the original
simplex operation guard. No volume, positivity, or Jensen identity occurs. -/
theorem cell00_simplex_shape :
    ∀ s : Fin cell00Payload.simplices.size,
      let r := cell00Payload.simplices[s]
      r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧
      (∀ k : Fin 9, r.vertexIds.getD k.val 0 < cell00Payload.vertices.size) ∧
      r.gapWeightedMeans.size = 10 := by decide +kernel

theorem cell00_stored_jensen_floors :
    ∀ s : Fin cell00Payload.simplices.size,
      (cell00Payload.simplices[s]).jensenFloor =
        q96Floor (cell00Payload.simplices[s]).jensenBound := by
  intro s
  fin_cases s
  · exact simplex00_stored_jensen_floor
  · exact simplex01_stored_jensen_floor
  · exact simplex02_stored_jensen_floor
  · exact simplex03_stored_jensen_floor
  · exact simplex04_stored_jensen_floor
  · exact simplex05_stored_jensen_floor
  · exact simplex06_stored_jensen_floor
  · exact simplex07_stored_jensen_floor

theorem cell00_stored_floor_guard :
    (∀ s : Fin cell00Payload.simplices.size,
      (cell00Payload.simplices[s]).jensenFloor =
        q96Floor (cell00Payload.simplices[s]).jensenBound) ∧
    cell00Payload.simplices.size = 8 ∧ cell00Payload.active8.size = 45 :=
  ⟨cell00_stored_jensen_floors, cell00_simplex_count, cell00_active8_count⟩

theorem cell00_stored_jensen_floor_sum :
    (∑ s : Fin cell00Payload.simplices.size,
      (cell00Payload.simplices[s]).jensenFloor) = 13236428172062120 := by decide +kernel

/-- Compose the eight previously checked floor equalities; do not repeat
their rational-floor computations inside one combined decision. -/
theorem cell00_separate_stored_floor_sum :
    (∑ s : Fin cell00Payload.simplices.size,
      q96Floor (cell00Payload.simplices[s]).jensenBound) = 13236428172062120 := by
  calc
    (∑ s : Fin cell00Payload.simplices.size,
      q96Floor (cell00Payload.simplices[s]).jensenBound) =
        ∑ s : Fin cell00Payload.simplices.size,
          (cell00Payload.simplices[s]).jensenFloor := by
      apply Finset.sum_congr rfl
      intro s _
      exact (cell00_stored_jensen_floors s).symm
    _ = 13236428172062120 := cell00_stored_jensen_floor_sum

#print axioms simplex04_stored_jensen_floor
#print axioms cell00_stored_jensen_floors
#print axioms cell00_simplex_shape
#print axioms cell00_stored_floor_guard
#print axioms cell00_separate_stored_floor_sum

end ImbalancedChen.P2Saving16Cell00StoredFloors
