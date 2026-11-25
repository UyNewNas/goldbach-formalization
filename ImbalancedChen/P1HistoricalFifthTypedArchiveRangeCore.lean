import ImbalancedChen.P1HistoricalFifthNpyFrame
import Mathlib.Tactic

/-!
Existing TypedValid definition and its constructive instance, factored from
P1HistoricalFifthTypedArchiveRange so individual actual data blocks can be
accepted and reused without recomputing the entire 143-block module.
No bound, data value or public declaration type has changed.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveRange
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload

-- The source grid is exactly400; valid mask means the original conservative
-- decoder's nonnegative signed mask condition, without a geometric flag.
def TypedValid (row : FifthWireRow) : Prop :=
  row.grid = 400 ∧ 0 ≤ row.mask ∧ ∀ column : Fin 10,
    -(half64 : ℤ) ≤ wireColumns row column ∧ wireColumns row column < (half64 : ℤ)

-- Fin10 and signed integer comparisons have constructive decidability.
-- No classical choice or externally evaluated Boolean is a proof premise.
instance typedValidDecidable (row : FifthWireRow) : Decidable (TypedValid row) := by
  unfold TypedValid
  infer_instance

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
