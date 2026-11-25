import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock141
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock142

/-!
Original closed LowerKeyBounds obligations, retained at their existing data-block
boundaries. Each public statement and resource limit is unchanged. The proof
command uses the same kernel reduction accepted for block000. Acceptance of
these further blocks must be established by their own normal/kernel/owned audit.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block141_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock141.rows.toList, LowerKeyBounds row := by
  decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block142_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock142.rows.toList, LowerKeyBounds row := by
  decide +kernel

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
