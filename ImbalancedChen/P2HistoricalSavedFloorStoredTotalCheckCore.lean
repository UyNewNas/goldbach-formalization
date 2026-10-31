import ImbalancedChen.P2HistoricalSavedFloorRowsSourceCore

/-! Exact original saved-total integer definitions, separated from analytic
row soundness. No change to data, row carrier, defaulted lookup, or check. -/
namespace ImbalancedChen.P2HistoricalSavedFloorRowsBinder

noncomputable section
open scoped BigOperators
open Certificates.PairedV2 Certificates.PairedV2.FullMask

/-- Literal aggregate field in the same frozen JSON.  It includes the
defect credits, exactly as do the original saved row numerators. -/
def sourceSavedFloorTotal : ℤ := 11290806845175652020270

/-- Integer aggregate equality is checked separately from all analytic
backend licences; this source-only file does not claim its evaluation. -/
def storedTotalCheck : Bool :=
  decide ((∑ r : Row, (frozenSavedRow r).savedQ80) = sourceSavedFloorTotal)

end

end ImbalancedChen.P2HistoricalSavedFloorRowsBinder
