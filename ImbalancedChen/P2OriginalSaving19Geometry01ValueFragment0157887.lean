import ImbalancedChen.P2OriginalSaving19Geometry01ValueFragment0157887Block000
import ImbalancedChen.P2OriginalSaving19Geometry01ValueFragment0157887Block001

/-! Complete external array child; only previously checked small block equations are composed.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def fragment0157887OpenChars : List Char := ['[']
noncomputable def fragment0157887Acc000 : List SourceJson := []
noncomputable def fragment0157887Acc001 : List SourceJson := fragment0157887Block000.blockPush fragment0157887Acc000
noncomputable def fragment0157887Acc002 : List SourceJson := fragment0157887Block001.blockPush fragment0157887Acc001
noncomputable def fragment0157887Chars : List Char := '[' :: (fragment0157887Block000.blockChars ++ fragment0157887Block001.blockChars)
noncomputable def fragment0157887Value : SourceJson := .arr (fragment0157887Acc002.reverse)

theorem value_fragment0157887 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 47) (fragment0157887Chars ++ tail) = .ok (fragment0157887Value, tail) := by
  have hinput : fragment0157887Chars ++ tail = '[' :: (fragment0157887Block000.blockChars ++ (fragment0157887Block001.blockChars ++ (tail))) := by
    simp only [fragment0157887Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 47) (fragment0157887Chars ++ tail) =
        SourceJson.value (fuel + 47) ('[' :: (fragment0157887Block000.blockChars ++ (fragment0157887Block001.blockChars ++ (tail)))) :=
      congrArg (SourceJson.value (fuel + 47)) hinput
    _ = SourceJson.array (fuel + 46) (SourceJson.white (fragment0157887Block000.blockChars ++ (fragment0157887Block001.blockChars ++ (tail)))) fragment0157887Acc000 := by rfl
    _ = SourceJson.array (fuel + 37) (SourceJson.white (fragment0157887Block001.blockChars ++ (tail))) fragment0157887Acc001 := fragment0157887Block000.array_block fuel (fragment0157887Block001.blockChars ++ (tail)) fragment0157887Acc000
    _ = .ok (fragment0157887Value, tail) := fragment0157887Block001.array_block fuel (tail) fragment0157887Acc001

theorem fragment0157887_open_prefix :
    (sourceRest 157887).take 1 = fragment0157887OpenChars := by rfl

theorem fragment0157887_open_split : sourceRest 157887 = fragment0157887OpenChars ++ sourceRest 157888 := by
  calc
    sourceRest 157887 = (sourceRest 157887).take 1 ++ (sourceRest 157887).drop 1 :=
      (List.take_append_drop 1 (sourceRest 157887)).symm
    _ = fragment0157887OpenChars ++ (sourceRest 157887).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 157887).drop 1) fragment0157887_open_prefix
    _ = fragment0157887OpenChars ++ sourceRest 157888 :=
      congrArg (fun tail => fragment0157887OpenChars ++ tail) (sourceRest_drop 157887 1)

theorem fragment0157887_original_split : sourceRest 157887 = fragment0157887Chars ++ sourceRest 162880 := by
  calc
    sourceRest 157887 = fragment0157887OpenChars ++ (sourceRest 157888) := fragment0157887_open_split
    _ = fragment0157887OpenChars ++ (fragment0157887Block000.blockChars ++ (sourceRest 161886)) := congrArg (fun rest => fragment0157887OpenChars ++ (rest)) fragment0157887Block000.block_original_split
    _ = fragment0157887OpenChars ++ (fragment0157887Block000.blockChars ++ (fragment0157887Block001.blockChars ++ (sourceRest 162880))) := congrArg (fun rest => fragment0157887OpenChars ++ (fragment0157887Block000.blockChars ++ (rest))) fragment0157887Block001.block_original_split
    _ = fragment0157887Chars ++ sourceRest 162880 := by simp only [fragment0157887Chars, fragment0157887OpenChars, List.cons_append, List.nil_append, List.append_assoc]

theorem value_fragment0157887_original (fuel : Nat) :
    SourceJson.value (fuel + 47) (sourceRest 157887) =
      .ok (fragment0157887Value, sourceRest 162880) :=
  (congrArg (SourceJson.value (fuel + 47)) fragment0157887_original_split).trans
    (value_fragment0157887 fuel (sourceRest 162880))

#print axioms value_fragment0157887
#print axioms fragment0157887_open_prefix
#print axioms fragment0157887_open_split
#print axioms fragment0157887_original_split
#print axioms value_fragment0157887_original

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
