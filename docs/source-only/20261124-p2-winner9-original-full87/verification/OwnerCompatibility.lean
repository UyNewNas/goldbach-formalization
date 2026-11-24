import ImbalancedChen.OriginalDescendingFifteenLiteralAffineRows
import ImbalancedChen.OriginalAscendingThirteenLiteralAffineRows
import ImbalancedChen.P2OriginalDescendingEighthLogSemantics
import ImbalancedChen.P2OriginalThirdMinorantLogDictionary
import ImbalancedChen.P2Winner9OriginalFull87Bridge

/-! Source-only integration check. Install the four refactored original
owners together with the cores before compiling this file. Successful import
must establish that the original owners and the bridge have one definition
of each moved constant. This probe is not a complete P2 theorem. -/

set_option pp.fullNames true in
#check ImbalancedChen.P2Winner9OriginalFull87Bridge.terminal41_integral_eq_original

#print axioms ImbalancedChen.P2Winner9OriginalFull87Bridge.terminal41_integral_eq_original
