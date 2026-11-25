import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock111
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock112
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock113
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock114
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock115
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock116
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock117
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock118
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock119
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock120

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
theorem block111_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock111.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block112_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock112.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block113_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock113.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block114_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock114.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block115_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock115.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block116_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock116.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block117_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock117.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block118_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock118.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block119_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock119.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block120_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock120.rows.toList, TypedValid row := by
  decide +kernel

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
