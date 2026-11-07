import Mathlib.Data.Int.Basic

/-! Original subdivision checkpoint fields, transcribed without recomputation.
SOURCE_ONLY / UNCOMPILED / ZERO_CREDIT. Old/new are distinct stored Q80
parent numerators, not child d/A/B and not asserted integral values. -/
namespace ImbalancedChen.P5SubdivisionStoredParentTypes

structure StoredParent where
  sourceIndex : ℕ
  oldQ80 : ℤ
  newQ80 : ℤ
  deriving DecidableEq, Repr

end ImbalancedChen.P5SubdivisionStoredParentTypes
