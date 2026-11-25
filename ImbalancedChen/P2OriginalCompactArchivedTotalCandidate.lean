import ImbalancedChen.P2OriginalCompactQ80CacheEncloser
import ImbalancedChen.P2OriginalCompactConcreteLoop

/-!
SOURCE ONLY / UNCOMPILED / CLOSED FINITE BODY UNEVALUATED.

This equality binds the original source-computed fixedUpper, through the
frozen exact shared-array implementation, to the archived whole upper
rational. The compact integer is the original comparison target; the
separate frozen historical candidate must still supply the actual run total.
No saved first-integral, tail, table, or charge-list literal is installed as
an evaluator. This file performs no adaptive run and defines no evaluator.

The rfl body below has NOT been elaborated or evaluated by the author.
Successful reduction, its truth, and practical kernel resources remain open.
-/
namespace ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly

open P2OriginalCompactQ80EncloserSourceOnly
open P2OriginalCompactQ80CacheEncloserSourceOnly

/-- Original archived whole upper endpoint, distinct from the stop target. -/
def archivedOriginalUpper : ℚ :=
  1230679674488580033396846301 / 180734410032387061618573312

set_option maxRecDepth 0 in
set_option maxHeartbeats 0 in
/-- Closed source equality candidate. Its table, first series and tail are
computed by the unchanged original cache source; no numerical result was
observed while authoring this term. Status: UNEVALUATED. -/
theorem cached_fixed_plus_original_compact_eq_archived_candidate :
    fastFixedUpper +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
      archivedOriginalUpper := by
  rfl

/-- Symbolic exact cache transport; neither table implementation is reduced
to prove this transfer. The closed finite equality remains a dependency. -/
theorem original_fixed_plus_original_compact_eq_archived_candidate :
    fixedUpper +
        (P2OriginalCompactConcreteLoopSourceOnly.historicalUpper : ℚ) / (scale : ℚ) =
      archivedOriginalUpper := by
  rw [← fastFixedUpper_eq]
  exact cached_fixed_plus_original_compact_eq_archived_candidate

end ImbalancedChen.P2OriginalCompactArchivedTotalCandidateSourceOnly
