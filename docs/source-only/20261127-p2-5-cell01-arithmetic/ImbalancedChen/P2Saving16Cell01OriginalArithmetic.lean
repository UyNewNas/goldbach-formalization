import ImbalancedChen.P2Saving16Cell01OriginalParse
import ImbalancedChen.P2Saving16Cell01AllRowsArithmetic

/-! Source candidate awaiting verification of the original parse and all 81 typed rows.
The explicit record motives transport the guard and the sum of individually floored
Jensen values along the equality between archive 1 and the typed payload.
-/
namespace ImbalancedChen.P2Saving16Cell01OriginalArithmetic

open P2OriginalSaving16OriginalArchive (archive simplexValid cellFloorNumerator)
open P2Saving16Cell01OriginalParse (cell01_original_archive)
open P2Saving16Cell01TypedPayload (cell01Payload)

/-- The unchanged eleven-conjunct guard, on the original dependent index. -/
theorem cell01_original_simplex_operations :
    ∀ s : Fin (archive (1 : Fin 14)).simplices.size,
      simplexValid (archive (1 : Fin 14)) s :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ s : Fin c.simplices.size,
        simplexValid c s)
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    P2Saving16Cell01AllRowsArithmetic.cell01_simplex_operations

/-- The original cell numerator, preserving every separate Q96 floor. -/
theorem cell01_original_floor_numerator :
    cellFloorNumerator (1 : Fin 14) = 292535084187454643081 := by
  unfold cellFloorNumerator
  exact Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      (Finset.univ.sum fun s : Fin c.simplices.size =>
        P2OriginalSaving16JensenFloor.q96Floor
          (P2OriginalSaving16OriginalArchive.jensenQ
            (P2OriginalSaving16OriginalArchive.simplexVertices c c.simplices[s]))) =
        292535084187454643081)
    (show archive (1 : Fin 14) = cell01Payload from cell01_original_archive).symm
    P2Saving16Cell01AllRowsArithmetic.cell01_geometric_floor_sum

#print axioms cell01_original_simplex_operations
#print axioms cell01_original_floor_numerator

end ImbalancedChen.P2Saving16Cell01OriginalArithmetic
