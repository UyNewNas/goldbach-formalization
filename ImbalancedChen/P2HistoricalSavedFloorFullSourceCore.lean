import ImbalancedChen.P2HistoricalSavedFloorRowsSourceCore
import ImbalancedChen.P2HistoricSieveCore
import ImbalancedChen.P2HistoricLogComputeCore

/-! Original concrete historical source-check definitions, moved verbatim.
Their analytic contracts remain in the original FullBinder facade. -/
namespace ImbalancedChen.P2HistoricalSavedFloorFullBinder

noncomputable section
open Certificates.PairedV2 Certificates.PairedV2.FullMask
open Certificates.P2HistoricQ80DefectLookup
open P2HistoricalSavedFloorRowsBinder

/-- Exactly `author.Ordinary(16384).f`, whose maximum is eight. -/
def actualSf : ℚ → I80 := P2HistoricSieveTableSemantics.sf 16384 8

/-- Exactly the historical Q80 `log(I(q))` wrapper. -/
def actualLog : ℚ → I80 := Certificates.P2HistoricLogPointInterpreter.logI

/-- Full-output equality with the original stored numerator and grid keys. -/
def fullSourceRowCheck (r : Row) : Bool := sourceOutputCheck actualSf actualLog r


end

end ImbalancedChen.P2HistoricalSavedFloorFullBinder
