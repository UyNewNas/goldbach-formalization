import ImbalancedChen.P2OriginalSaving19Cell00Row000Input
import ImbalancedChen.P2OriginalSaving19PrefixMoments

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell00Row000MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell00Row000
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 152000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 546743, 0, 0]

def deviationDenominators : Fin 10 → Nat := ![1782600184365, 1782600184365, 14068437311760, 11012698888620, 9659674874668, 8307465959975, 2235302123040, 2018018969148, 2018018969148, 2017984527468]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![254627647755, 316116215051, 90540387735, 235395823663, 235395823663, 70898898525, 123886496370, 0, 5740280],
    ![254627647755, 316116215051, 90540387735, 235395823663, 235395823663, 70898898525, 61943248185, 0, 5740280],
    ![0, 614885672960, 1742764809540, 1960047963432, 1960047963432, 1982735610960, 2009602561980, 2195432306535, 2195438046815],
    ![0, 491908538368, 2070939329580, 1998511611616, 2940071945148, 2350193109420, 1651652382900, 2704687602045, 2704681861765],
    ![491908538368, 0, 1804606618528, 1587323464636, 1587323464636, 1451197579468, 1289995873348, 1351939121533, 1351933381253],
    ![2195438046815, 1580552373855, 452673237275, 235390083383, 235390083383, 553017148775, 929154463055, 5740280, 0],
    ![707295144750, 338363740974, 0, 217283153892, 217283153892, 296689920240, 390724248810, 452667496995, 452673237275],
    ![490011990858, 551500558154, 325924730838, 0, 0, 79406766348, 173441094918, 235384343103, 235390083383],
    ![490011990858, 551500558154, 325924730838, 0, 0, 306317683308, 297362032968, 235418784783, 235390083383],
    ![490011990858, 551500558154, 325924730838, 470780166766, 0, 306283241628, 297327591288, 235384343103, 235390083383]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_ROW000_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_ROW000_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_ROW000_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell00Row000MomentFloor
