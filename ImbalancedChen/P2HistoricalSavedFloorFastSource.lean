import ImbalancedChen.P2HistoricQ80ReplayChecked
import ImbalancedChen.P2HistoricalSavedFloorFullSourceCore

namespace ImbalancedChen.P2HistoricalSavedFloorFastSource
open P2HistoricSieveTableSemantics P2HistoricSieveFiniteReplay
open P2HistoricQ80ReplayData P2HistoricalSavedFloorFullBinder
open Certificates.P2HistoricQ80DefectLookup

def fastSf (q : ℚ) : I80 :=
  pointWith 16384 8 (prefixReader 16384 8 36864 nodes) q.num (q.den : ℤ)

/-- Globally identical source interpreter; no assumption on q is needed. -/
theorem fastSf_eq_actualSf : fastSf = actualSf := by
  funext q
  exact sf_prefixReader_eq (g := 16384) (maximum := 8) (N := 36864) (by decide) (by decide) nodes nodes_zero nodes_step q

end ImbalancedChen.P2HistoricalSavedFloorFastSource
