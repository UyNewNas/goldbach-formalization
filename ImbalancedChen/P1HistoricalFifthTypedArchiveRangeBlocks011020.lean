import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore
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
Original closed TypedValid obligations, retained at their existing data-block
boundaries. Each public statement and resource limit is unchanged. The proof
command uses the same kernel reduction accepted for block000. Acceptance of
these further blocks must be established by their own normal/kernel/owned audit.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveRange
noncomputable section

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block011_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock011.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block012_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock012.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block013_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock013.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block014_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock014.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block015_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock015.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block016_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock016.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block017_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock017.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block018_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock018.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block019_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock019.rows.toList, TypedValid row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block020_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock020.rows.toList, TypedValid row := by
  decide +kernel

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
