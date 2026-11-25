import ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows

/-!
Properness of the existing 97 source gates in each of the original 13 cells.
This is only the data-independent first conjunct of original_gate_checks.
The literal pool and index map are imported unchanged; no original vertex,
archive parser, row floor, or source-inclusion obligation is asserted here.
-/
namespace ImbalancedChen.P2OriginalSaving19GateProper

open OriginalAscendingThirteenLiteralAffineRows

private theorem literalPool_normal_nonzero :
    ∀ p : Fin 103, ∃ j : Fin 8, literalPool p j.succ ≠ 0 := by
  decide +kernel

theorem original_gate_normals_nonzero (c : Fin 13) (g : Fin 97) :
    ∃ j : Fin 8, exportedCoefficients c g j.succ ≠ 0 :=
  literalPool_normal_nonzero (literalIndex c g)

end ImbalancedChen.P2OriginalSaving19GateProper
