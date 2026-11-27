import Mathlib.Tactic.FinCases
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock000
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock001
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock002
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock003
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock004
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock005
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock006
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock007
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock008
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock009
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock010
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock011
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock012
import ImbalancedChen.P2OriginalSaving19Cell00SeparationBlock013

/-! All 1,540 original Cell00 pairs have a proper separating affine form.
This finite theorem has no measure or integral conclusion. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Separation
theorem all_pairs (r s : Fin 56) (h : r < s) : Checks r s := by
  fin_cases r
  · exact Block000.row000 s h
  · exact Block000.row001 s h
  · exact Block000.row002 s h
  · exact Block000.row003 s h
  · exact Block001.row004 s h
  · exact Block001.row005 s h
  · exact Block001.row006 s h
  · exact Block001.row007 s h
  · exact Block002.row008 s h
  · exact Block002.row009 s h
  · exact Block002.row010 s h
  · exact Block002.row011 s h
  · exact Block003.row012 s h
  · exact Block003.row013 s h
  · exact Block003.row014 s h
  · exact Block003.row015 s h
  · exact Block004.row016 s h
  · exact Block004.row017 s h
  · exact Block004.row018 s h
  · exact Block004.row019 s h
  · exact Block005.row020 s h
  · exact Block005.row021 s h
  · exact Block005.row022 s h
  · exact Block005.row023 s h
  · exact Block006.row024 s h
  · exact Block006.row025 s h
  · exact Block006.row026 s h
  · exact Block006.row027 s h
  · exact Block007.row028 s h
  · exact Block007.row029 s h
  · exact Block007.row030 s h
  · exact Block007.row031 s h
  · exact Block008.row032 s h
  · exact Block008.row033 s h
  · exact Block008.row034 s h
  · exact Block008.row035 s h
  · exact Block009.row036 s h
  · exact Block009.row037 s h
  · exact Block009.row038 s h
  · exact Block009.row039 s h
  · exact Block010.row040 s h
  · exact Block010.row041 s h
  · exact Block010.row042 s h
  · exact Block010.row043 s h
  · exact Block011.row044 s h
  · exact Block011.row045 s h
  · exact Block011.row046 s h
  · exact Block011.row047 s h
  · exact Block012.row048 s h
  · exact Block012.row049 s h
  · exact Block012.row050 s h
  · exact Block012.row051 s h
  · exact Block013.row052 s h
  · exact Block013.row053 s h
  · exact Block013.row054 s h
  · exact Block013.row055 s h

#print axioms all_pairs
end ImbalancedChen.P2OriginalSaving19Cell00Separation
