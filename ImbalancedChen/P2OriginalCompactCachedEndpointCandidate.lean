import ImbalancedChen.P2OriginalCompactCachedRun

/-!
SOURCEONLY / UNCOMPILED / DECISIVE FINITE GUARD UNEVALUATED.

This separate path imports no legacy slow historical-candidate module. Its
closed proof attempt evaluates the incremental shared-array computation.
Symbolic exactness then transfers the same result to the original source
computation. No sourceState/2M run is reduced while proving that equivalence.

The source body is not a report of successful elaboration or evaluation.
Array caching removes a specific repeated-table dependency; no feasible
kernel resource bound or original analytic enclosure soundness is claimed.
-/
namespace ImbalancedChen.P2OriginalCompactCachedEndpointCandidateSourceOnly

open P2OriginalCompactConcreteLoopSourceOnly
open P2OriginalCompactCachedRunSourceOnly

set_option maxRecDepth 0 in
set_option maxHeartbeats 0 in
/-- Closed cached finite proof attempt. Status remains UNEVALUATED. -/
theorem cachedHistoricalEndpointCheck_candidate : cachedHistoricalEndpointCheck = true := by
  rfl

/-- Exact equality transfers the checked statement, without requiring the
legacy slow `rfl` proof attempt to elaborate or reducing its computation. -/
theorem originalHistoricalEndpointCheck_viaCache_candidate : historicalEndpointCheck = true := by
  rw [← cachedHistoricalEndpointCheck_eq]
  exact cachedHistoricalEndpointCheck_candidate

theorem cached_historical_ordered_charges_candidate :
    cachedOrderedUpperCharges.sum = 144590669409566793572719 ∧
      cachedOrderedUpperCharges.length = 2000021 := by
  rw [cachedOrderedUpperCharges_eq]
  exact historical_ordered_charge_fields originalHistoricalEndpointCheck_viaCache_candidate

theorem original_complete_chargeTree_viaCache_candidate :
    P4AOriginalClosedTreeStructuralAggregationSourceOnly.totalCharge originalChargeTree =
      144590669409566793572719 := by
  rw [originalChargeTree_total]
  exact (historical_check_fields originalHistoricalEndpointCheck_viaCache_candidate).2.1


theorem cached_complete_chargeTree_candidate :
    P4AOriginalClosedTreeStructuralAggregationSourceOnly.totalCharge cachedChargeTree =
      144590669409566793572719 := by
  rw [cachedChargeTree_eq]
  exact original_complete_chargeTree_viaCache_candidate
end ImbalancedChen.P2OriginalCompactCachedEndpointCandidateSourceOnly

