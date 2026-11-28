import ImbalancedChen.P2OriginalSaving19Geometry06ScalableAllOriginalConstraintMinimaNode000To006

/-! Complete original all_original_constraint_minima array value from a balanced tree.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace AllOriginalConstraintMinimaValue

noncomputable def arrayOpenChars : List Char := ['[']
noncomputable def arrayValue : SourceJson := .arr ((ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To006.blockPush []).reverse)

theorem array_open_prefix :
    (sourceRest 63977).take 1 = arrayOpenChars := by rfl

theorem array_open_split : sourceRest 63977 = arrayOpenChars ++ sourceRest 63978 := by
  calc
    sourceRest 63977 = (sourceRest 63977).take 1 ++ (sourceRest 63977).drop 1 :=
      (List.take_append_drop 1 (sourceRest 63977)).symm
    _ = arrayOpenChars ++ (sourceRest 63977).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 63977).drop 1) array_open_prefix
    _ = arrayOpenChars ++ sourceRest 63978 :=
      congrArg (fun tail => arrayOpenChars ++ tail) (sourceRest_drop 63977 1)

theorem value_array_open (fuel : Nat) :
    SourceJson.value (fuel + 117) (sourceRest 63977) =
      SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 63978)) [] :=
  (congrArg (SourceJson.value (fuel + 117)) array_open_split).trans (by rfl)

theorem array_all_blocks (fuel : Nat) :
    SourceJson.array (fuel + 116) (SourceJson.white (sourceRest 63978)) [] =
      .ok (arrayValue, sourceRest 66061) := ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing.AllOriginalConstraintMinimaNode000To006.array_original fuel []

theorem value_array_original (fuel : Nat) :
    SourceJson.value (fuel + 117) (sourceRest 63977) =
      .ok (arrayValue, sourceRest 66061) :=
  (value_array_open fuel).trans (array_all_blocks fuel)

#print axioms array_open_prefix
#print axioms array_open_split
#print axioms value_array_open
#print axioms array_all_blocks
#print axioms value_array_original

end AllOriginalConstraintMinimaValue

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
