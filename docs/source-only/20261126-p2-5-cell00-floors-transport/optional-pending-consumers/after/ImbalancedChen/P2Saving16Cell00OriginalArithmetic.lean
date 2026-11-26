import ImbalancedChen.P2Saving16Cell00OriginalFloors
import ImbalancedChen.P2Saving16Cell00AllRowsArithmetic

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the existing complete typed-payload row guards and geometric
floor sum to the unchanged original archive at cell 0. The exact original
payload equality and the all-eight-row composition must first be accepted
with their selected dependencies. This file performs no parsing, decoding,
determinant, rational-mean, Jensen, or Q96 calculation.

The second conclusion is the original cellFloorNumerator definition: the
sum of eight separately floored geometric Jensen values. No other cell,
all-cell guard, source membership, pulling ownership, integral endpoint,
or whole P2.5 theorem is asserted here.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalArithmetic

open P2OriginalSaving16OriginalArchive (archive simplexValid cellFloorNumerator)
open P2Saving16Cell00OriginalFloors (cell00_original_payload)

/-- The unchanged eleven-conjunct guard, on the original dependent index. -/
theorem cell00_original_simplex_operations :
    ∀ s : Fin (archive (0 : Fin 14)).simplices.size,
      simplexValid (archive (0 : Fin 14)) s :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ s : Fin c.simplices.size,
        simplexValid c s)
    cell00_original_payload.symm
    P2Saving16Cell00AllRowsArithmetic.cell00_simplex_operations

/-- The original cell numerator, preserving every separate Q96 floor. -/
theorem cell00_original_floor_numerator :
    cellFloorNumerator (0 : Fin 14) = 13236428172062120 := by
  unfold cellFloorNumerator
  exact Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      (Finset.univ.sum fun s : Fin c.simplices.size =>
        P2OriginalSaving16JensenFloor.q96Floor
          (P2OriginalSaving16OriginalArchive.jensenQ
            (P2OriginalSaving16OriginalArchive.simplexVertices c c.simplices[s]))) =
        13236428172062120)
    cell00_original_payload.symm
    P2Saving16Cell00AllRowsArithmetic.cell00_geometric_floor_sum

#print axioms cell00_original_simplex_operations
#print axioms cell00_original_floor_numerator

end ImbalancedChen.P2Saving16Cell00OriginalArithmetic
