import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock031
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock032
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock033
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock034
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock035
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock036
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock037
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock038
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock039
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock040

/-!
Original closed TypedValid obligations, retained at their existing data-block
boundaries. Each public statement and resource limit is unchanged. The proof
command uses the same kernel reduction accepted for block000. Acceptance of
these further blocks must be established by their own normal/kernel/owned audit.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveRange
noncomputable section

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block031_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock031.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block032_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock032.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block033_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock033.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block034_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock034.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block035_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock035.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block036_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock036.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block037_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock037.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block038_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock038.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block039_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock039.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block040_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock040.rows.toList, TypedValid row := by
  decide +kernel

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
