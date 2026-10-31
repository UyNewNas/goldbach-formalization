import Mathlib.Data.Int.Basic

/-! Original frozen-row public carrier moved verbatim, not a replacement. -/
namespace ImbalancedChen.P2HistoricalSavedFloorRowsBinder

structure FrozenSavedRow where
  sourceOrdinal : ℕ
  tIndex : ℕ
  uIndex : ℕ
  savedQ80 : ℤ
  deriving Inhabited, DecidableEq, Repr

end ImbalancedChen.P2HistoricalSavedFloorRowsBinder
