import ImbalancedChen.P2Saving16Cell00TypedPayload
import ImbalancedChen.P2Saving16Cell00DirectParse

/-!
Complete AST identity between the original reader's certified value and
the named field decomposition used by the candidate typed payload.
This equality retains all seventeen fields, their order, and every nested
value. It does not assert typed decoding or a finite arithmetic guard.
-/

namespace ImbalancedChen.P2Saving16Cell00PayloadBinding

open P2Saving16Cell00Segments (rootValue)
open P2Saving16Cell00TypedPayload (rawRoot)

theorem rootValue_eq_rawRoot : rootValue = rawRoot := by
  rfl

#print axioms rootValue_eq_rawRoot

end ImbalancedChen.P2Saving16Cell00PayloadBinding
