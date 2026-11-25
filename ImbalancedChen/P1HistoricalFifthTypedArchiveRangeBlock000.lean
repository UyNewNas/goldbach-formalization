import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeCore
import ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000

/-!
The original closed block000 TypedValid obligation, with exactly its original
public statement, data and resource limits. Kernel reduction is requested
explicitly. This block is imported by the full archive range module; it is
not a replacement for any of the other 142 blocks or the original NPY check.
This source has not yet received normal/kernel/full-owned acceptance.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveRange
noncomputable section

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block000_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000.rows.toList, TypedValid row := by
  decide +kernel

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
