import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock011
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock012
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock013
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock014
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock015
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock016
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock017
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock018
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock019
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock020

/-!
Original closed LowerKeyBounds obligations, retained at their existing data-block
boundaries. Each public statement and resource limit is unchanged. The proof
command uses the same kernel reduction accepted for block000. Acceptance of
these further blocks must be established by their own normal/kernel/owned audit.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block011_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock011.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block012_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock012.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block013_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock013.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block014_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock014.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block015_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock015.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block016_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock016.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block017_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock017.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block018_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock018.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block019_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock019.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block020_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock020.rows.toList, LowerKeyBounds row := by
  decide +kernel

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
