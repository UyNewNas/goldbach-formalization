import ImbalancedChen.P2OriginalSaving19Cell05MomentBounds
import ImbalancedChen.P2OriginalSaving19Moment05Shape

/-! A concrete, original-record Q80 equality candidate. The evaluator is the
unchanged prefix algorithm on canonical encodings of the actual coordinates.
No host-computed moment or floor is supplied as a hypothesis. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Pilot

noncomputable section
open P2OriginalSaving19Cell05MomentBounds
open P2OriginalSaving19Moment05Decoding

def originalMomentRow (r : Fin 56) : P2OriginalSaving19Archive.MomentRecord :=
  momentConcrete05.rows[r.val]'(P2OriginalSaving19Moment05Shape.row_bound r)

def computedFactor (r : Fin 56) (j : Fin 10) : ℤ :=
  P2OriginalLogMomentQ96ArithmeticPure.factorFloorQ80 (prefixMoment r j)

theorem row000_factor00 :
    computedFactor 0 0 = (originalMomentRow 0).factorFloorsQ80[0]! := by
  decide +kernel

#print axioms row000_factor00

end
end ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Pilot
