import ImbalancedChen.P2Saving16Cell03Row00Arithmetic
import ImbalancedChen.P2Saving16Cell03Row01Arithmetic
import ImbalancedChen.P2Saving16Cell03Row02Arithmetic
import ImbalancedChen.P2Saving16Cell03Row03Arithmetic
import ImbalancedChen.P2Saving16Cell03Row04Arithmetic
import ImbalancedChen.P2Saving16Cell03Row05Arithmetic
import ImbalancedChen.P2Saving16Cell03Row06Arithmetic
import ImbalancedChen.P2Saving16Cell03Row07Arithmetic
import ImbalancedChen.P2Saving16Cell03Row08Arithmetic
import ImbalancedChen.P2Saving16Cell03Row09Arithmetic
import ImbalancedChen.P2Saving16Cell03Row10Arithmetic
import ImbalancedChen.P2Saving16Cell03Row11Arithmetic
import ImbalancedChen.P2Saving16Cell03Row12Arithmetic
import ImbalancedChen.P2Saving16Cell03Row13Arithmetic
import ImbalancedChen.P2Saving16Cell03Row14Arithmetic
import ImbalancedChen.P2Saving16Cell03Row15Arithmetic
import ImbalancedChen.P2Saving16Cell03Row16Arithmetic
import ImbalancedChen.P2Saving16Cell03Row17Arithmetic
import ImbalancedChen.P2Saving16Cell03Row18Arithmetic
import ImbalancedChen.P2Saving16Cell03Row19Arithmetic
import ImbalancedChen.P2Saving16Cell03Row20Arithmetic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Assemble the 21 exact original operation guards after their separate row
owners are accepted. This file performs no determinant, rational-mean, Jensen,
or Q96 calculation. It reuses the existing sum of the 21 separate stored
floors. The named payload is not identified with archive 3 in this module.
-/
namespace ImbalancedChen.P2Saving16Cell03AllRowsArithmetic

open P2OriginalSaving16OriginalArchive (simplexValid simplexVertices jensenQ)
open P2OriginalSaving16JensenFloor (q96Floor)
open P2Saving16Cell03TypedPayload (cell03Payload)
open scoped BigOperators

set_option Elab.async false

/-- Every one of the original eleven-conjunct row guards. -/
theorem cell03_simplex_operations :
    ∀ s : Fin cell03Payload.simplices.size, simplexValid cell03Payload s := by
  intro s
  fin_cases s
  · exact P2Saving16Cell03Row00Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row01Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row02Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row03Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row04Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row05Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row06Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row07Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row08Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row09Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row10Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row11Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row12Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row13Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row14Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row15Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row16Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row17Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row18Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row19Arithmetic.simplex_valid
  · exact P2Saving16Cell03Row20Arithmetic.simplex_valid

/-- Extract the original final conjunct without deciding any floor again. -/
theorem cell03_geometric_jensen_floors :
    ∀ s : Fin cell03Payload.simplices.size,
      (cell03Payload.simplices[s]).jensenFloor =
        q96Floor (jensenQ (simplexVertices cell03Payload (cell03Payload.simplices[s]))) := by
  intro s
  rcases cell03_simplex_operations s with
    ⟨_, _, _, _, _, _, _, _, _, _, hfloor⟩
  exact hfloor

/-- Transport the accepted sum of 21 separate stored floors. -/
theorem cell03_geometric_floor_sum :
    (∑ s : Fin cell03Payload.simplices.size,
      q96Floor (jensenQ (simplexVertices cell03Payload (cell03Payload.simplices[s])))) =
        41059550060734548977 := by
  calc
    (∑ s : Fin cell03Payload.simplices.size,
      q96Floor (jensenQ (simplexVertices cell03Payload (cell03Payload.simplices[s])))) =
        ∑ s : Fin cell03Payload.simplices.size,
          (cell03Payload.simplices[s]).jensenFloor := by
      apply Finset.sum_congr rfl
      intro s _
      exact (cell03_geometric_jensen_floors s).symm
    _ = 41059550060734548977 := P2Saving16Cell03StoredFloors.cell03_stored_jensen_floor_sum

#print axioms cell03_simplex_operations
#print axioms cell03_geometric_jensen_floors
#print axioms cell03_geometric_floor_sum

end ImbalancedChen.P2Saving16Cell03AllRowsArithmetic
