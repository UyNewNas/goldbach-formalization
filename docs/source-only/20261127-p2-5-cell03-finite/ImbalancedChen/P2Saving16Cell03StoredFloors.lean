import ImbalancedChen.P2Saving16Cell03TypedPayload
import ImbalancedChen.P2OriginalSaving16Q96FloorCore

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The original Cell03 candidate supplies 21 separate stored Jensen bounds.
Each floor uses the unchanged original q96Floor definition. The separate sum,
ordered row indices and finite shapes are checked without replacing any data.
These equations alone establish no determinant, geometric Jensen identity,
original-archive arithmetic guard, pulling ownership or integral endpoint.
-/
namespace ImbalancedChen.P2Saving16Cell03StoredFloors

open P2Saving16Cell03TypedPayload
open P2OriginalSaving16JensenFloor (q96Floor)
open scoped BigOperators

set_option Elab.async false

theorem simplex00_stored_jensen_floor :
    simplex00.jensenFloor = q96Floor simplex00.jensenBound := by decide +kernel

theorem simplex01_stored_jensen_floor :
    simplex01.jensenFloor = q96Floor simplex01.jensenBound := by decide +kernel

theorem simplex02_stored_jensen_floor :
    simplex02.jensenFloor = q96Floor simplex02.jensenBound := by decide +kernel

theorem simplex03_stored_jensen_floor :
    simplex03.jensenFloor = q96Floor simplex03.jensenBound := by decide +kernel

theorem simplex04_stored_jensen_floor :
    simplex04.jensenFloor = q96Floor simplex04.jensenBound := by decide +kernel

theorem simplex05_stored_jensen_floor :
    simplex05.jensenFloor = q96Floor simplex05.jensenBound := by decide +kernel

theorem simplex06_stored_jensen_floor :
    simplex06.jensenFloor = q96Floor simplex06.jensenBound := by decide +kernel

theorem simplex07_stored_jensen_floor :
    simplex07.jensenFloor = q96Floor simplex07.jensenBound := by decide +kernel

theorem simplex08_stored_jensen_floor :
    simplex08.jensenFloor = q96Floor simplex08.jensenBound := by decide +kernel

theorem simplex09_stored_jensen_floor :
    simplex09.jensenFloor = q96Floor simplex09.jensenBound := by decide +kernel

theorem simplex10_stored_jensen_floor :
    simplex10.jensenFloor = q96Floor simplex10.jensenBound := by decide +kernel

theorem simplex11_stored_jensen_floor :
    simplex11.jensenFloor = q96Floor simplex11.jensenBound := by decide +kernel

theorem simplex12_stored_jensen_floor :
    simplex12.jensenFloor = q96Floor simplex12.jensenBound := by decide +kernel

theorem simplex13_stored_jensen_floor :
    simplex13.jensenFloor = q96Floor simplex13.jensenBound := by decide +kernel

theorem simplex14_stored_jensen_floor :
    simplex14.jensenFloor = q96Floor simplex14.jensenBound := by decide +kernel

theorem simplex15_stored_jensen_floor :
    simplex15.jensenFloor = q96Floor simplex15.jensenBound := by decide +kernel

theorem simplex16_stored_jensen_floor :
    simplex16.jensenFloor = q96Floor simplex16.jensenBound := by decide +kernel

theorem simplex17_stored_jensen_floor :
    simplex17.jensenFloor = q96Floor simplex17.jensenBound := by decide +kernel

theorem simplex18_stored_jensen_floor :
    simplex18.jensenFloor = q96Floor simplex18.jensenBound := by decide +kernel

theorem simplex19_stored_jensen_floor :
    simplex19.jensenFloor = q96Floor simplex19.jensenBound := by decide +kernel

theorem simplex20_stored_jensen_floor :
    simplex20.jensenFloor = q96Floor simplex20.jensenBound := by decide +kernel

theorem cell03_simplex_count : cell03Payload.simplices.size = 21 := by rfl

theorem cell03_active8_count : cell03Payload.active8.size = 165 := by rfl

theorem cell03_vertex_count : cell03Payload.vertices.size = 23 := by rfl

theorem cell03_vertex_dimensions :
    ∀ v : Fin cell03Payload.vertices.size,
      (cell03Payload.vertices[v]).size = 8 := by decide +kernel

/-- Only the finite indexing and array-size conjuncts of the original
simplex operation guard. No volume, positivity, or Jensen identity occurs. -/
theorem cell03_simplex_shape :
    ∀ s : Fin cell03Payload.simplices.size,
      let r := cell03Payload.simplices[s]
      r.simplexId = s.val ∧ r.vertexIds.size = 9 ∧
      (∀ k : Fin 9, r.vertexIds.getD k.val 0 < cell03Payload.vertices.size) ∧
      r.gapWeightedMeans.size = 10 := by decide +kernel

theorem cell03_stored_jensen_floors :
    ∀ s : Fin cell03Payload.simplices.size,
      (cell03Payload.simplices[s]).jensenFloor =
        q96Floor (cell03Payload.simplices[s]).jensenBound := by
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
  · exact simplex08_stored_jensen_floor
  · exact simplex09_stored_jensen_floor
  · exact simplex10_stored_jensen_floor
  · exact simplex11_stored_jensen_floor
  · exact simplex12_stored_jensen_floor
  · exact simplex13_stored_jensen_floor
  · exact simplex14_stored_jensen_floor
  · exact simplex15_stored_jensen_floor
  · exact simplex16_stored_jensen_floor
  · exact simplex17_stored_jensen_floor
  · exact simplex18_stored_jensen_floor
  · exact simplex19_stored_jensen_floor
  · exact simplex20_stored_jensen_floor


theorem cell03_stored_floor_guard :
    (∀ s : Fin cell03Payload.simplices.size,
      (cell03Payload.simplices[s]).jensenFloor =
        q96Floor (cell03Payload.simplices[s]).jensenBound) ∧
    cell03Payload.simplices.size = 21 ∧ cell03Payload.active8.size = 165 :=
  ⟨cell03_stored_jensen_floors, cell03_simplex_count, cell03_active8_count⟩

theorem cell03_stored_jensen_floor_sum :
    (∑ s : Fin cell03Payload.simplices.size,
      (cell03Payload.simplices[s]).jensenFloor) = 41059550060734548977 := by decide +kernel

/-- Compose the 21 previously checked floor equalities; do not repeat
their rational-floor computations inside one combined decision. -/
theorem cell03_separate_stored_floor_sum :
    (∑ s : Fin cell03Payload.simplices.size,
      q96Floor (cell03Payload.simplices[s]).jensenBound) = 41059550060734548977 := by
  calc
    (∑ s : Fin cell03Payload.simplices.size,
      q96Floor (cell03Payload.simplices[s]).jensenBound) =
        ∑ s : Fin cell03Payload.simplices.size,
          (cell03Payload.simplices[s]).jensenFloor := by
      apply Finset.sum_congr rfl
      intro s _
      exact (cell03_stored_jensen_floors s).symm
    _ = 41059550060734548977 := cell03_stored_jensen_floor_sum

#print axioms simplex04_stored_jensen_floor
#print axioms cell03_stored_jensen_floors
#print axioms cell03_simplex_shape
#print axioms cell03_stored_floor_guard
#print axioms cell03_separate_stored_floor_sum

end ImbalancedChen.P2Saving16Cell03StoredFloors
