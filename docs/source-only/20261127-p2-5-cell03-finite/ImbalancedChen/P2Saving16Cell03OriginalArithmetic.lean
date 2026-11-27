import ImbalancedChen.P2Saving16Cell03OriginalParse
import ImbalancedChen.P2Saving16Cell03AllRowsArithmetic

/-! Source candidate awaiting verification of the original parse and all 21 typed rows.
The explicit record motives transport the guard and the sum of individually floored
Jensen values along the equality between archive 3 and the typed payload.
-/
namespace ImbalancedChen.P2Saving16Cell03OriginalArithmetic

open P2OriginalSaving16OriginalArchive (archive simplexValid cellFloorNumerator)
open P2Saving16Cell03OriginalParse (cell03_original_archive)
open P2Saving16Cell03TypedPayload (cell03Payload)

/-- The unchanged eleven-conjunct guard, on the original dependent index. -/
theorem cell03_original_simplex_operations :
    ∀ s : Fin (archive (3 : Fin 14)).simplices.size,
      simplexValid (archive (3 : Fin 14)) s :=
  Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      ∀ s : Fin c.simplices.size,
        simplexValid c s)
    (show archive (3 : Fin 14) = cell03Payload from cell03_original_archive).symm
    P2Saving16Cell03AllRowsArithmetic.cell03_simplex_operations

/-- The original cell numerator, preserving every separate Q96 floor. -/
theorem cell03_original_floor_numerator :
    cellFloorNumerator (3 : Fin 14) = 41059550060734548977 := by
  unfold cellFloorNumerator
  exact Eq.subst
    (motive := fun c : P2OriginalSaving16OriginalArchive.CellRecord =>
      (Finset.univ.sum fun s : Fin c.simplices.size =>
        P2OriginalSaving16JensenFloor.q96Floor
          (P2OriginalSaving16OriginalArchive.jensenQ
            (P2OriginalSaving16OriginalArchive.simplexVertices c c.simplices[s]))) =
        41059550060734548977)
    (show archive (3 : Fin 14) = cell03Payload from cell03_original_archive).symm
    P2Saving16Cell03AllRowsArithmetic.cell03_geometric_floor_sum

#print axioms cell03_original_simplex_operations
#print axioms cell03_original_floor_numerator

end ImbalancedChen.P2Saving16Cell03OriginalArithmetic
