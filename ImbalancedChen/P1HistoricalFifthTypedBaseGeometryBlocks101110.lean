import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock101
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock102
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock103
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock104
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock105
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock106
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock107
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock108
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock109
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock110

/-!
Original closed LowerKeyBounds obligations, retained at their existing data-block
boundaries. Each public statement and resource limit is unchanged. The proof
command uses the same kernel reduction accepted for block000. Acceptance of
these further blocks must be established by their own normal/kernel/owned audit.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block101_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock101.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block102_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock102.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block103_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock103.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block104_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock104.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block105_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock105.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block106_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock106.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block107_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock107.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block108_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock108.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block109_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock109.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block110_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock110.rows.toList, LowerKeyBounds row := by
  decide +kernel

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
