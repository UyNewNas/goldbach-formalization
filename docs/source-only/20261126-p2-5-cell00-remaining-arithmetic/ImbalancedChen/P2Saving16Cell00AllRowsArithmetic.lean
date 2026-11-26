import ImbalancedChen.P2Saving16Cell00Row00Arithmetic
import ImbalancedChen.P2Saving16Cell00Row01Arithmetic
import ImbalancedChen.P2Saving16Cell00Row02Arithmetic
import ImbalancedChen.P2Saving16Cell00Row03Arithmetic
import ImbalancedChen.P2Saving16Cell00Row04Arithmetic
import ImbalancedChen.P2Saving16Cell00Row05Arithmetic
import ImbalancedChen.P2Saving16Cell00Row06Arithmetic
import ImbalancedChen.P2Saving16Cell00Row07Arithmetic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Assemble the eight exact original operation guards after their separate row
owners are accepted. This file performs no determinant, rational-mean, Jensen,
or Q96 calculation. It reuses the existing sum of the eight separate stored
floors. The named payload is not identified with archive 0 in this module.
-/
namespace ImbalancedChen.P2Saving16Cell00AllRowsArithmetic

open P2OriginalSaving16OriginalArchive (simplexValid simplexVertices jensenQ)
open P2OriginalSaving16JensenFloor (q96Floor)
open P2Saving16Cell00TypedPayload (cell00Payload)
open scoped BigOperators

set_option Elab.async false

/-- Every one of the original eleven-conjunct row guards. -/
theorem cell00_simplex_operations :
    ∀ s : Fin cell00Payload.simplices.size, simplexValid cell00Payload s := by
  intro s
  fin_cases s
  · exact P2Saving16Cell00Row00Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row01Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row02Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row03Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row04Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row05Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row06Arithmetic.simplex_valid
  · exact P2Saving16Cell00Row07Arithmetic.simplex_valid

/-- Extract the original final conjunct without deciding any floor again. -/
theorem cell00_geometric_jensen_floors :
    ∀ s : Fin cell00Payload.simplices.size,
      (cell00Payload.simplices[s]).jensenFloor =
        q96Floor (jensenQ (simplexVertices cell00Payload (cell00Payload.simplices[s]))) := by
  intro s
  rcases cell00_simplex_operations s with
    ⟨_, _, _, _, _, _, _, _, _, _, hfloor⟩
  exact hfloor

/-- Transport the accepted sum of eight separate stored floors. -/
theorem cell00_geometric_floor_sum :
    (∑ s : Fin cell00Payload.simplices.size,
      q96Floor (jensenQ (simplexVertices cell00Payload (cell00Payload.simplices[s])))) =
        13236428172062120 := by
  calc
    (∑ s : Fin cell00Payload.simplices.size,
      q96Floor (jensenQ (simplexVertices cell00Payload (cell00Payload.simplices[s])))) =
        ∑ s : Fin cell00Payload.simplices.size,
          (cell00Payload.simplices[s]).jensenFloor := by
      apply Finset.sum_congr rfl
      intro s _
      exact (cell00_geometric_jensen_floors s).symm
    _ = 13236428172062120 := P2Saving16Cell00StoredFloors.cell00_stored_jensen_floor_sum

#print axioms cell00_simplex_operations
#print axioms cell00_geometric_jensen_floors
#print axioms cell00_geometric_floor_sum

end ImbalancedChen.P2Saving16Cell00AllRowsArithmetic
