import ImbalancedChen.P2Saving16Cell03TypedPayload
import ImbalancedChen.P2Saving16Cell03DirectParse

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell03 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/

namespace ImbalancedChen.P2Saving16Cell03PayloadBinding

open P2Saving16Cell03Segments (rootValue)
open P2Saving16Cell03TypedPayload (rawRoot)

theorem rootValue_eq_rawRoot : rootValue = rawRoot := by
  rfl

#print axioms rootValue_eq_rawRoot

end ImbalancedChen.P2Saving16Cell03PayloadBinding
