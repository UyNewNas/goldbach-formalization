import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic.Positivity

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.

Mechanical relocation of the original frozen-history constants and the
original source-rank definition. Every fully qualified name and defining
expression is unchanged. Select the recorded owner postimages whenever
the original history modules are in the same import closure.

The cutoff is fixed before the scale or source occurrence. No numerical
evaluation of its reciprocal or of the resulting rank is performed.
-/
namespace ImbalancedChen.Part5OriginalH430FrozenRootRefinement
noncomputable section

def frozenResidualFloor : ℝ := (11 / 384) / (101 : ℝ)^440
def frozenLeafCutoffFloor : ℝ := frozenResidualFloor / 6

theorem frozenLeafCutoffFloor_pos : 0 < frozenLeafCutoffFloor := by
  unfold frozenLeafCutoffFloor frozenResidualFloor
  positivity

end
end ImbalancedChen.Part5OriginalH430FrozenRootRefinement

namespace ImbalancedChen.P2FiniteMarkedGamma5ActualRank
noncomputable section
open Part5OriginalH430FrozenRootRefinement

/-- Fixed by the existing frozen-history cutoff before N or any source
occurrence is chosen. The number 440 is a depth budget, not this rank. -/
def frozenSourceRankBound : ℕ := ⌊frozenLeafCutoffFloor⁻¹⌋₊

end
end ImbalancedChen.P2FiniteMarkedGamma5ActualRank
