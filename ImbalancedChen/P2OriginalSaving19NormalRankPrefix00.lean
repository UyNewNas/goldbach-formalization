import ImbalancedChen.P2OriginalSaving19PositiveBalanceSegments00

/-! The fifth original field, normal_rank; reuse all four accepted prior fields.
Exact original bytes are candidate data; the original reader equations below
are the Lean checks. No whole-file decide or replacement reader is used. -/
namespace ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false

open ImbalancedChen.P2OriginalSaving19Archive

def normalRankPrefixChars00 : List Char := ['\r', '\n', ' ', ' ', '"', 'n', 'o', 'r', 'm', 'a', 'l', '_', 'r', 'a', 'n', 'k', '"', ':', ' ', '8', ',']
def normalRankKey00 : String := String.ofList ['n', 'o', 'r', 'm', 'a', 'l', '_', 'r', 'a', 'n', 'k']
def normalRankValue00 : SourceJson := .number (String.ofList ['8'])
def normalRankAcc00 : List (String × SourceJson) :=
  (normalRankKey00, normalRankValue00) :: positiveBalanceAcc00

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 normal_rank_before_binding"
  err.flush

theorem geometryChars00_normal_rank_prefix :
    (geometryChars00.drop 359).take 21 = normalRankPrefixChars00 := by rfl

theorem geometryChars00_normal_rank_split :
    geometryChars00.drop 359 = normalRankPrefixChars00 ++ geometryChars00.drop 380 := by
  calc
    geometryChars00.drop 359 =
        (geometryChars00.drop 359).take 21 ++ (geometryChars00.drop 359).drop 21 :=
      (List.take_append_drop 21 (geometryChars00.drop 359)).symm
    _ = normalRankPrefixChars00 ++ (geometryChars00.drop 359).drop 21 :=
      congrArg (fun p => p ++ (geometryChars00.drop 359).drop 21) geometryChars00_normal_rank_prefix
    _ = normalRankPrefixChars00 ++ geometryChars00.drop 380 := by rw [List.drop_drop]

theorem object_normal_rank_prefix (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 13) (SourceJson.white (normalRankPrefixChars00 ++ tail)) positiveBalanceAcc00 =
      SourceJson.object (fuel + 12) (SourceJson.white tail) normalRankAcc00 := by rfl

theorem geometryChars00_normal_rank_step :
    SourceJson.object 195130 (SourceJson.white (geometryChars00.drop 359)) positiveBalanceAcc00 =
      SourceJson.object 195129 (SourceJson.white (geometryChars00.drop 380)) normalRankAcc00 := by
  exact (congrArg (fun s => SourceJson.object 195130 (SourceJson.white s) positiveBalanceAcc00)
      geometryChars00_normal_rank_split).trans
    (object_normal_rank_prefix 195117 (geometryChars00.drop 380))

theorem geometryChars00_through_normal_rank :
    SourceJson.value 195135 geometryChars00 =
      SourceJson.object 195129 (SourceJson.white (geometryChars00.drop 380)) normalRankAcc00 := by
  exact geometryChars00_through_positive_balance.trans geometryChars00_normal_rank_step

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_FULL_CELL00 normal_rank_complete"
  err.flush

#print axioms geometryChars00_normal_rank_prefix
#print axioms geometryChars00_normal_rank_split
#print axioms object_normal_rank_prefix
#print axioms geometryChars00_normal_rank_step
#print axioms geometryChars00_through_normal_rank

end ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic
