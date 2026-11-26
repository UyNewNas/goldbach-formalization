import ImbalancedChen.P2Saving16Cell00TypedPayload
import ImbalancedChen.P4AOriginalAscending14Literal42

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

The complete existing four-conjunct pattern guard, specialized to the
cell00 typed payload and original source ID 0. Both source mask arrays
and `literalLeftMasks` are reused unchanged. No new mask table, row
recipe, parser, parent policy, or assumption is introduced.

The existing literal-pattern owner and its dependencies must be reused
from their successful verification. This module supplies no acceptance
for them and does not import the pending all-cell archive guards.
-/
namespace ImbalancedChen.P2Saving16Cell00TypedPatterns

open P2Saving16Cell00TypedPayload (cell00Payload)
open P4AOriginalAscending14Literal42 (literalLeftMasks)

set_option Elab.async false

/-- Exact cell00 instance of the existing pattern conjunction, with
`sourceId (atlasCell 0)` reduced to its original source index 0. -/
theorem cell00_patterns :
    cell00Payload.leftMasks.toList.toFinset = literalLeftMasks (0 : Fin 15) ∧
    Disjoint cell00Payload.leftMasks.toList.toFinset
      cell00Payload.rightMasks.toList.toFinset ∧
    cell00Payload.leftMasks.toList.toFinset ∪
      cell00Payload.rightMasks.toList.toFinset = Finset.Icc 1 63 ∧
    6 ∈ cell00Payload.rightMasks.toList.toFinset := by
  decide +kernel

#print axioms cell00_patterns

end ImbalancedChen.P2Saving16Cell00TypedPatterns
