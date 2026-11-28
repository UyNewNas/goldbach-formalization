import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerNode000To006

/-! Complete original face_ledger array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To006.jsonItems)

theorem array_open_prefix :
    (sourceRest 69087).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 69087 = arrayOpenChars ++ sourceRest 69088 := by
  calc
    sourceRest 69087 = (sourceRest 69087).take 1 ++ (sourceRest 69087).drop 1 :=
      (List.take_append_drop 1 (sourceRest 69087)).symm
    _ = arrayOpenChars ++ (sourceRest 69087).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 69087).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 69088 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 69087 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 81) (sourceRest 69087) =
      SourceJson.array (fuel + 80) (SourceJson.white (sourceRest 69088)) [] :=
  (congrArg (SourceJson.value (fuel + 81)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 80) (SourceJson.white (sourceRest 69088)) [] =
      .ok (arrayValue, sourceRest 124012) := by
  simpa only [arrayValue, ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To006.blockPush_reverse, List.reverse_nil, List.nil_append]
    using (ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding.FaceLedgerNode000To006.array_original fuel [])

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 81) (sourceRest 69087) =
      .ok (arrayValue, sourceRest 124012) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end FaceLedgerValue

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
