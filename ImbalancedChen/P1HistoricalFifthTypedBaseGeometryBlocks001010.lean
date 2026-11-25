import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock001
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock002
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock003
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock004
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock005
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock006
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock007
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock008
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock009
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock010

/-!
Original closed LowerKeyBounds obligations, retained at their existing data-block
boundaries. Each public statement and resource limit is unchanged. The proof
command uses the same kernel reduction accepted for block000. Acceptance of
these further blocks must be established by their own normal/kernel/owned audit.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block001_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock001.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block002_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock002.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block003_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock003.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block004_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock004.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block005_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock005.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block006_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock006.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block007_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock007.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block008_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock008.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block009_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock009.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block010_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock010.rows.toList, LowerKeyBounds row := by
  decide +kernel

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
