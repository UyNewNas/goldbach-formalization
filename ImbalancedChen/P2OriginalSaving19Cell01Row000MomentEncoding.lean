import ImbalancedChen.P2OriginalSaving19Cell01Row000Input
import ImbalancedChen.P2OriginalSaving19PrefixMoments

/-! SOURCE CANDIDATE: this new cell01 owner has not been compiled or
independently kernel-replayed. Existing suppliers are imported unchanged. -/

/-! Exact nonnegative integer encodings of the actual nine ordered vertices.
The existing prefix evaluator is used unchanged. Host-generated literals
are connected to the decoded row by closed Lean equalities below. No
saved field, moment value or final floor is an assumption. -/
namespace ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open scoped BigOperators
open P2OriginalSaving19Cell01Row000
open P2OriginalSaving19RowNumericsPure
open P2OriginalLogMomentQ96ArithmeticPure
open P2OriginalSaving19PrefixMoments

def gapScale : Nat := 34000000

def gapNats : Fin 9 → Nat := ![0, 0, 0, 0, 0, 0, 171843, 0, 0]

def deviationDenominators : Fin 10 → Nat := ![579447228360, 579447228360, 198797806200, 762174741440, 11693981880, 530236503860, 227240617380, 187420521792, 655971826272, 655960630752]

def deviationNats : Fin 10 → Fin 9 → Nat :=
  ![![82768579320, 295144554936, 132542099445, 132542099445, 99020080200, 82766979960, 56584463040, 0, 1865920],
    ![82768579320, 295144554936, 132542099445, 132542099445, 99020080200, 82766979960, 28292231520, 0, 1865920],
    ![0, 11377284408, 21332308305, 21332308305, 24379764600, 28443039660, 36225146580, 40266893940, 40267027220],
    ![0, 106187987808, 82959598715, 82959598715, 108355067840, 132734718200, 130625003600, 215501698160, 215501698160],
    ![3346253400, 669245304, 1254834945, 1254834945, 1434097080, 0, 2782083360, 2782083360, 2782067680],
    ![281869190540, 202228199684, 132543032405, 132543032405, 159970139060, 82767912920, 113169859040, 932960, 0],
    ![85329233220, 39820095588, 0, 49775119485, 52822575780, 85328776260, 53597572980, 61681067700, 61681600820],
    ![45509137632, 0, 59730143382, 9955023897, 13002480192, 45508680672, 13777477392, 21860972112, 21861505232],
    ![159281981712, 0, 209066697357, 209066697357, 175544678112, 159291577872, 104816829432, 76524597912, 76515268312],
    ![159281981712, 0, 209055501837, 209055501837, 175533482592, 159280382352, 104805633912, 76513402392, 76515268312]]

def prefixMoment (j : Fin 10) (k : Nat) : ℚ :=
  normalizedMoment gapNats (deviationNats j) (deviationDenominators j) k

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT gap_encoding_before"
  err.flush

theorem gapScale_ne : gapScale ≠ 0 := by decide +kernel

theorem gap_encoding : ∀ i : Fin 9,
    gapQ (vertices i) = (gapNats i : ℚ) / (gapScale : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT deviation_encoding_before"
  err.flush

theorem deviationDenominators_ne : ∀ j : Fin 10, deviationDenominators j ≠ 0 := by
  decide +kernel

theorem deviation_encoding : ∀ (j : Fin 10) (i : Fin 9),
    1 - factorsQ (vertices i) j / topsOf row j =
      (deviationNats j i : ℚ) / (deviationDenominators j : ℚ) := by
  decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_CELL01_ROW000_MOMENT encoding_complete"
  err.flush

#print axioms gapScale_ne
#print axioms gap_encoding
#print axioms deviationDenominators_ne
#print axioms deviation_encoding

end ImbalancedChen.P2OriginalSaving19Cell01Row000MomentFloor
