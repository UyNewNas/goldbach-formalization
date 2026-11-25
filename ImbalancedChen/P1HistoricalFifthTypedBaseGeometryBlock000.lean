import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000

/-!
The original closed block000 LowerKeyBounds obligation, retaining its exact
public statement, actual data and resource limits. Kernel reduction is
requested explicitly. The full base-geometry module imports this obligation
and retains all other 142 original block obligations and their aggregation.
This source has not yet received normal/kernel/full-owned acceptance.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block000_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock000.rows.toList, LowerKeyBounds row := by
  decide +kernel

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
