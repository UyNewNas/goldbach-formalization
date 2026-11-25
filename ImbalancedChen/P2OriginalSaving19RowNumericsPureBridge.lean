import ImbalancedChen.P2OriginalSaving19RowNumerics
import ImbalancedChen.P2OriginalSaving19RowNumericsPure
import ImbalancedChen.P2OriginalLogMomentQ96ArithmeticBridge

/-! SOURCE-ONLY integration candidate. Both sides are the same original
ten-clause guard. The old RowNumerics owner and its analytic dependencies
must be ready before this new bridge receives its own verification. -/
namespace ImbalancedChen.P2OriginalSaving19RowNumericsPureBridge

theorem rowDataChecksFor_iff_original
    (v : Fin 9 → Fin 8 → ℚ) (g : P2OriginalSaving19Archive.GeometryRow) :
    P2OriginalSaving19RowNumericsPure.RowDataChecksFor v g ↔
      P2OriginalSaving19RowNumerics.RowDataChecksFor v g := Iff.rfl

#print axioms rowDataChecksFor_iff_original

end ImbalancedChen.P2OriginalSaving19RowNumericsPureBridge
