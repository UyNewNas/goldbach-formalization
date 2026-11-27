import ImbalancedChen.P2Saving16Cell01Row00Arithmetic
import ImbalancedChen.P2Saving16Cell01Row01Arithmetic
import ImbalancedChen.P2Saving16Cell01Row02Arithmetic
import ImbalancedChen.P2Saving16Cell01Row03Arithmetic
import ImbalancedChen.P2Saving16Cell01Row04Arithmetic
import ImbalancedChen.P2Saving16Cell01Row05Arithmetic
import ImbalancedChen.P2Saving16Cell01Row06Arithmetic
import ImbalancedChen.P2Saving16Cell01Row07Arithmetic
import ImbalancedChen.P2Saving16Cell01Row08Arithmetic
import ImbalancedChen.P2Saving16Cell01Row09Arithmetic
import ImbalancedChen.P2Saving16Cell01Row10Arithmetic
import ImbalancedChen.P2Saving16Cell01Row11Arithmetic
import ImbalancedChen.P2Saving16Cell01Row12Arithmetic
import ImbalancedChen.P2Saving16Cell01Row13Arithmetic
import ImbalancedChen.P2Saving16Cell01Row14Arithmetic
import ImbalancedChen.P2Saving16Cell01Row15Arithmetic
import ImbalancedChen.P2Saving16Cell01Row16Arithmetic
import ImbalancedChen.P2Saving16Cell01Row17Arithmetic
import ImbalancedChen.P2Saving16Cell01Row18Arithmetic
import ImbalancedChen.P2Saving16Cell01Row19Arithmetic
import ImbalancedChen.P2Saving16Cell01Row20Arithmetic
import ImbalancedChen.P2Saving16Cell01Row21Arithmetic
import ImbalancedChen.P2Saving16Cell01Row22Arithmetic
import ImbalancedChen.P2Saving16Cell01Row23Arithmetic
import ImbalancedChen.P2Saving16Cell01Row24Arithmetic
import ImbalancedChen.P2Saving16Cell01Row25Arithmetic
import ImbalancedChen.P2Saving16Cell01Row26Arithmetic
import ImbalancedChen.P2Saving16Cell01Row27Arithmetic
import ImbalancedChen.P2Saving16Cell01Row28Arithmetic
import ImbalancedChen.P2Saving16Cell01Row29Arithmetic
import ImbalancedChen.P2Saving16Cell01Row30Arithmetic
import ImbalancedChen.P2Saving16Cell01Row31Arithmetic
import ImbalancedChen.P2Saving16Cell01Row32Arithmetic
import ImbalancedChen.P2Saving16Cell01Row33Arithmetic
import ImbalancedChen.P2Saving16Cell01Row34Arithmetic
import ImbalancedChen.P2Saving16Cell01Row35Arithmetic
import ImbalancedChen.P2Saving16Cell01Row36Arithmetic
import ImbalancedChen.P2Saving16Cell01Row37Arithmetic
import ImbalancedChen.P2Saving16Cell01Row38Arithmetic
import ImbalancedChen.P2Saving16Cell01Row39Arithmetic
import ImbalancedChen.P2Saving16Cell01Row40Arithmetic
import ImbalancedChen.P2Saving16Cell01Row41Arithmetic
import ImbalancedChen.P2Saving16Cell01Row42Arithmetic
import ImbalancedChen.P2Saving16Cell01Row43Arithmetic
import ImbalancedChen.P2Saving16Cell01Row44Arithmetic
import ImbalancedChen.P2Saving16Cell01Row45Arithmetic
import ImbalancedChen.P2Saving16Cell01Row46Arithmetic
import ImbalancedChen.P2Saving16Cell01Row47Arithmetic
import ImbalancedChen.P2Saving16Cell01Row48Arithmetic
import ImbalancedChen.P2Saving16Cell01Row49Arithmetic
import ImbalancedChen.P2Saving16Cell01Row50Arithmetic
import ImbalancedChen.P2Saving16Cell01Row51Arithmetic
import ImbalancedChen.P2Saving16Cell01Row52Arithmetic
import ImbalancedChen.P2Saving16Cell01Row53Arithmetic
import ImbalancedChen.P2Saving16Cell01Row54Arithmetic
import ImbalancedChen.P2Saving16Cell01Row55Arithmetic
import ImbalancedChen.P2Saving16Cell01Row56Arithmetic
import ImbalancedChen.P2Saving16Cell01Row57Arithmetic
import ImbalancedChen.P2Saving16Cell01Row58Arithmetic
import ImbalancedChen.P2Saving16Cell01Row59Arithmetic
import ImbalancedChen.P2Saving16Cell01Row60Arithmetic
import ImbalancedChen.P2Saving16Cell01Row61Arithmetic
import ImbalancedChen.P2Saving16Cell01Row62Arithmetic
import ImbalancedChen.P2Saving16Cell01Row63Arithmetic
import ImbalancedChen.P2Saving16Cell01Row64Arithmetic
import ImbalancedChen.P2Saving16Cell01Row65Arithmetic
import ImbalancedChen.P2Saving16Cell01Row66Arithmetic
import ImbalancedChen.P2Saving16Cell01Row67Arithmetic
import ImbalancedChen.P2Saving16Cell01Row68Arithmetic
import ImbalancedChen.P2Saving16Cell01Row69Arithmetic
import ImbalancedChen.P2Saving16Cell01Row70Arithmetic
import ImbalancedChen.P2Saving16Cell01Row71Arithmetic
import ImbalancedChen.P2Saving16Cell01Row72Arithmetic
import ImbalancedChen.P2Saving16Cell01Row73Arithmetic
import ImbalancedChen.P2Saving16Cell01Row74Arithmetic
import ImbalancedChen.P2Saving16Cell01Row75Arithmetic
import ImbalancedChen.P2Saving16Cell01Row76Arithmetic
import ImbalancedChen.P2Saving16Cell01Row77Arithmetic
import ImbalancedChen.P2Saving16Cell01Row78Arithmetic
import ImbalancedChen.P2Saving16Cell01Row79Arithmetic
import ImbalancedChen.P2Saving16Cell01Row80Arithmetic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Assemble the 81 exact original operation guards after their separate row
owners are accepted. This file performs no determinant, rational-mean, Jensen,
or Q96 calculation. It reuses the existing sum of the 81 separate stored
floors. The named payload is not identified with archive 1 in this module.
-/
namespace ImbalancedChen.P2Saving16Cell01AllRowsArithmetic

open P2OriginalSaving16OriginalArchive (simplexValid simplexVertices jensenQ)
open P2OriginalSaving16JensenFloor (q96Floor)
open P2Saving16Cell01TypedPayload (cell01Payload)
open scoped BigOperators

set_option Elab.async false

/-- Every one of the original eleven-conjunct row guards. -/
theorem cell01_simplex_operations :
    ∀ s : Fin cell01Payload.simplices.size, simplexValid cell01Payload s := by
  intro s
  fin_cases s
  · exact P2Saving16Cell01Row00Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row01Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row02Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row03Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row04Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row05Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row06Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row07Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row08Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row09Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row10Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row11Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row12Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row13Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row14Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row15Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row16Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row17Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row18Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row19Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row20Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row21Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row22Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row23Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row24Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row25Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row26Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row27Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row28Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row29Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row30Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row31Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row32Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row33Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row34Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row35Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row36Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row37Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row38Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row39Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row40Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row41Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row42Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row43Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row44Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row45Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row46Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row47Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row48Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row49Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row50Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row51Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row52Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row53Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row54Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row55Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row56Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row57Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row58Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row59Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row60Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row61Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row62Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row63Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row64Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row65Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row66Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row67Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row68Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row69Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row70Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row71Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row72Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row73Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row74Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row75Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row76Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row77Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row78Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row79Arithmetic.simplex_valid
  · exact P2Saving16Cell01Row80Arithmetic.simplex_valid

/-- Extract the original final conjunct without deciding any floor again. -/
theorem cell01_geometric_jensen_floors :
    ∀ s : Fin cell01Payload.simplices.size,
      (cell01Payload.simplices[s]).jensenFloor =
        q96Floor (jensenQ (simplexVertices cell01Payload (cell01Payload.simplices[s]))) := by
  intro s
  rcases cell01_simplex_operations s with
    ⟨_, _, _, _, _, _, _, _, _, _, hfloor⟩
  exact hfloor

/-- Transport the accepted sum of 81 separate stored floors. -/
theorem cell01_geometric_floor_sum :
    (∑ s : Fin cell01Payload.simplices.size,
      q96Floor (jensenQ (simplexVertices cell01Payload (cell01Payload.simplices[s])))) =
        292535084187454643081 := by
  calc
    (∑ s : Fin cell01Payload.simplices.size,
      q96Floor (jensenQ (simplexVertices cell01Payload (cell01Payload.simplices[s])))) =
        ∑ s : Fin cell01Payload.simplices.size,
          (cell01Payload.simplices[s]).jensenFloor := by
      apply Finset.sum_congr rfl
      intro s _
      exact (cell01_geometric_jensen_floors s).symm
    _ = 292535084187454643081 := P2Saving16Cell01StoredFloors.cell01_stored_jensen_floor_sum

#print axioms cell01_simplex_operations
#print axioms cell01_geometric_jensen_floors
#print axioms cell01_geometric_floor_sum

end ImbalancedChen.P2Saving16Cell01AllRowsArithmetic
