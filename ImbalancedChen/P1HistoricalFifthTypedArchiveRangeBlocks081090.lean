import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock081
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock082
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock083
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock084
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock085
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock086
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock087
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock088
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock089
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock090

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
theorem block081_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock081.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block082_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock082.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block083_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock083.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block084_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock084.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block085_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock085.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block086_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock086.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block087_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock087.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block088_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock088.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block089_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock089.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block090_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock090.rows.toList, TypedValid row := by
  decide +kernel

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
