import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock131
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock132
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock133
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock134
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock135
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock136
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock137
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock138
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock139
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock140

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
theorem block131_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock131.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block132_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock132.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block133_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock133.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block134_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock134.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block135_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock135.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block136_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock136.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block137_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock137.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block138_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock138.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block139_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock139.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block140_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock140.rows.toList, TypedValid row := by
  decide +kernel

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
