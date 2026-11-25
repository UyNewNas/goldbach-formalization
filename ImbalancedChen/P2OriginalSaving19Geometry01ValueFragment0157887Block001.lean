import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Grouped external original-reader transitions; child certificates remain opaque.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace fragment0157887Block001

noncomputable def piece0008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def piece0008Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '9'])]) :: ((.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '9'])]) :: (acc))

theorem array_piece0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (piece0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 35) (SourceJson.white tail) (piece0008Push00 acc) := by
  rfl

noncomputable def piece0009Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def piece0009Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: (acc)

theorem array_piece0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 35) (SourceJson.white (piece0009Chars00 ++ tail)) acc =
      .ok (.arr ((piece0009Push00 acc).reverse), tail) := by
  rfl

noncomputable def blockChars : List Char := piece0008Chars00 ++ piece0009Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := piece0009Push00 (piece0008Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = piece0008Chars00 ++ (piece0009Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 37) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 37) (SourceJson.white (piece0008Chars00 ++ (piece0009Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 37) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 35) (SourceJson.white (piece0009Chars00 ++ (tail))) (piece0008Push00 (acc)) := array_piece0008 fuel (piece0009Chars00 ++ (tail)) (acc)
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_piece0009 fuel (tail) (piece0008Push00 (acc))

theorem block_original_prefix :
    (sourceRest 161886).take 994 = blockChars := by rfl

theorem block_original_split : sourceRest 161886 = blockChars ++ sourceRest 162880 := by
  calc
    sourceRest 161886 = (sourceRest 161886).take 994 ++ (sourceRest 161886).drop 994 :=
      (List.take_append_drop 994 (sourceRest 161886)).symm
    _ = blockChars ++ (sourceRest 161886).drop 994 :=
      congrArg (fun part => part ++ (sourceRest 161886).drop 994) block_original_prefix
    _ = blockChars ++ sourceRest 162880 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 161886 994)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (sourceRest 161886)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 162880) :=
  (congrArg (fun chars => SourceJson.array (fuel + 37) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 162880) acc)

#print axioms array_piece0008
#print axioms array_piece0009
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block
#print axioms array_block_original

end fragment0157887Block001

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
