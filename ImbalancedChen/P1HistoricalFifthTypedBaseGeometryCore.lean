import ImbalancedChen.P1OriginalPrefixRowDecodeSoundness

/-!
Existing LowerKeyBounds definition and its constructive instance, factored
from P1HistoricalFifthTypedBaseGeometry for individual block acceptance.
All five original lower keys retain the same 1..77 bounds.
This source has not yet received normal/kernel/full-owned acceptance.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
open P1OriginalPrefixRowDecodeSoundness

/-- The original generator uses all five keys in8..77; only1..77 is needed
here. Opaque fields and masks never enter this lower-key check. -/
def LowerKeyBounds (row : FifthWireRow) : Prop :=
  ∀ k : Fin 5, 1 ≤ row.lo k ∧ row.lo k ≤ 77

instance lowerKeyBoundsDecidable (row : FifthWireRow) : Decidable (LowerKeyBounds row) := by
  unfold LowerKeyBounds
  infer_instance

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
