import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block000
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block001
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block002
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block003
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block004
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block005
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block006
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block007
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block008
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block009
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block010
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block011
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block012
import ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Block013

/-! All 560 original Q80 factor values, assembled from kernel-checked blocks. -/
namespace ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Complete
noncomputable section
open P2OriginalSaving19Cell05MomentQ80Pilot

theorem all_factors (r : Fin 56) (j : Fin 10) :
    computedFactor r j = (originalMomentRow r).factorFloorsQ80[j.val]! := by
  fin_cases r
  · exact P2OriginalSaving19Cell05MomentQ80Block000.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block000.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block000.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block000.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block001.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block001.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block001.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block001.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block002.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block002.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block002.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block002.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block003.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block003.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block003.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block003.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block004.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block004.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block004.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block004.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block005.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block005.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block005.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block005.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block006.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block006.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block006.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block006.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block007.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block007.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block007.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block007.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block008.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block008.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block008.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block008.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block009.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block009.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block009.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block009.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block010.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block010.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block010.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block010.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block011.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block011.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block011.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block011.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block012.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block012.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block012.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block012.all_factors 3 j
  · exact P2OriginalSaving19Cell05MomentQ80Block013.all_factors 0 j
  · exact P2OriginalSaving19Cell05MomentQ80Block013.all_factors 1 j
  · exact P2OriginalSaving19Cell05MomentQ80Block013.all_factors 2 j
  · exact P2OriginalSaving19Cell05MomentQ80Block013.all_factors 3 j

#print axioms all_factors

end
end ImbalancedChen.P2OriginalSaving19Cell05MomentQ80Complete
