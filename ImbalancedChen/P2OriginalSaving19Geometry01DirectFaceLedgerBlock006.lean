import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock006

noncomputable def fragment0176960Acc00000 : List SourceJson := []

noncomputable def fragment0176960Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0176960Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0176960_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (fragment0176960Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (fragment0176960Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0176960Acc00100 : List SourceJson := fragment0176960Chunk000Push00 fragment0176960Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176960_array_chunk_000"
  err.flush

noncomputable def fragment0176960Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0176960Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]) :: (acc))

theorem array_fragment0176960_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (fragment0176960Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 27) (SourceJson.white tail) (fragment0176960Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0176960Acc00200 : List SourceJson := fragment0176960Chunk001Push00 fragment0176960Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176960_array_chunk_001"
  err.flush

noncomputable def fragment0176960Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0176960Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]) :: (acc))

theorem array_fragment0176960_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (fragment0176960Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (fragment0176960Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0176960Acc00300 : List SourceJson := fragment0176960Chunk002Push00 fragment0176960Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176960_array_chunk_002"
  err.flush

noncomputable def fragment0176960Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0176960Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '7'])]) :: (acc))

theorem array_fragment0176960_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (fragment0176960Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 23) (SourceJson.white tail) (fragment0176960Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0176960Acc00400 : List SourceJson := fragment0176960Chunk003Push00 fragment0176960Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176960_array_chunk_003"
  err.flush

noncomputable def fragment0176960Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0176960Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]) :: (acc))

theorem array_fragment0176960_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0176960Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0176960Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0176960Acc00500 : List SourceJson := fragment0176960Chunk004Push00 fragment0176960Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176960_array_chunk_004"
  err.flush

noncomputable def fragment0176960Chars : List Char := '[' :: (fragment0176960Chunk000Chars00 ++ fragment0176960Chunk001Chars00 ++ fragment0176960Chunk002Chars00 ++ fragment0176960Chunk003Chars00 ++ fragment0176960Chunk004Chars00)
noncomputable def fragment0176960Value : SourceJson := .arr (fragment0176960Acc00500.reverse)

theorem value_fragment0176960 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 32) (fragment0176960Chars ++ tail) =
      .ok (fragment0176960Value, tail) := by
  have hinput : fragment0176960Chars ++ tail = '[' :: (fragment0176960Chunk000Chars00 ++ (fragment0176960Chunk001Chars00 ++ (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0176960Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 32) (fragment0176960Chars ++ tail) =
        SourceJson.value (fuel + 32) ('[' :: (fragment0176960Chunk000Chars00 ++ (fragment0176960Chunk001Chars00 ++ (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 32)) hinput
    _ = SourceJson.array (fuel + 31) (SourceJson.white (fragment0176960Chunk000Chars00 ++ (fragment0176960Chunk001Chars00 ++ (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail))))))) fragment0176960Acc00000 := by rfl
    _ = SourceJson.array (fuel + 29) (SourceJson.white (fragment0176960Chunk001Chars00 ++ (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail)))))) fragment0176960Acc00100 := array_fragment0176960_chunk_000 fuel (fragment0176960Chunk001Chars00 ++ (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail))))) fragment0176960Acc00000
    _ = SourceJson.array (fuel + 27) (SourceJson.white (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail))))) fragment0176960Acc00200 := array_fragment0176960_chunk_001 fuel (fragment0176960Chunk002Chars00 ++ (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail)))) fragment0176960Acc00100
    _ = SourceJson.array (fuel + 25) (SourceJson.white (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail)))) fragment0176960Acc00300 := array_fragment0176960_chunk_002 fuel (fragment0176960Chunk003Chars00 ++ (fragment0176960Chunk004Chars00 ++ (tail))) fragment0176960Acc00200
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0176960Chunk004Chars00 ++ (tail))) fragment0176960Acc00400 := array_fragment0176960_chunk_003 fuel (fragment0176960Chunk004Chars00 ++ (tail)) fragment0176960Acc00300
    _ = .ok (fragment0176960Value, tail) := array_fragment0176960_chunk_004 fuel (tail) fragment0176960Acc00400

noncomputable def fragment0176560Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0176560Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0176560Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7'])]
noncomputable def fragment0176560Acc00100 : List (String × SourceJson) := (fragment0176560Field000Key00, fragment0176560Field000Value00) :: fragment0176560Acc00000
noncomputable def fragment0176560Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0176560_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 36) (SourceJson.white (fragment0176560Field000Chars00 ++ tail)) fragment0176560Acc00000 =
      SourceJson.object (fuel + 35) (SourceJson.white tail) fragment0176560Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176560_object_field_000"
  err.flush

noncomputable def fragment0176560Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0176560Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0176560Acc00200 : List (String × SourceJson) := (fragment0176560Field001Key00, fragment0176560Field001Value00) :: fragment0176560Acc00100
noncomputable def fragment0176560Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0176560_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 35) (SourceJson.white (fragment0176560Field001Chars00 ++ tail)) fragment0176560Acc00100 =
      SourceJson.object (fuel + 34) (SourceJson.white tail) fragment0176560Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176560_object_field_001"
  err.flush

noncomputable def fragment0176560Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0176560Field002Value00 : SourceJson := .number (String.ofList ['3', '7'])
noncomputable def fragment0176560Acc00300 : List (String × SourceJson) := (fragment0176560Field002Key00, fragment0176560Field002Value00) :: fragment0176560Acc00200
noncomputable def fragment0176560Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '7', ',']

theorem object_fragment0176560_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 34) (SourceJson.white (fragment0176560Field002Chars00 ++ tail)) fragment0176560Acc00200 =
      SourceJson.object (fuel + 33) (SourceJson.white tail) fragment0176560Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176560_object_field_002"
  err.flush

noncomputable def fragment0176560Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0176560Field003Value00 : SourceJson := fragment0176960Value
noncomputable def fragment0176560Acc00400 : List (String × SourceJson) := (fragment0176560Field003Key00, fragment0176560Field003Value00) :: fragment0176560Acc00300
noncomputable def fragment0176560Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0176560Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0176560Field003Chars00 : List Char := fragment0176560Field003HeaderChars00 ++ fragment0176960Chars ++ fragment0176560Field003SuffixChars00

noncomputable def fragment0176560Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0176560Field003Key00, result.1) :: fragment0176560Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0176560Field003Key00, result.1) :: fragment0176560Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0176560_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 33) (SourceJson.white (fragment0176560Field003HeaderChars00 ++ rest)) fragment0176560Acc00300 =
      (SourceJson.value (fuel + 32) rest).bind (fragment0176560Field003AfterValue00 (fuel + 32)) := by rfl

theorem object_fragment0176560_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 33) (SourceJson.white (fragment0176560Field003Chars00 ++ tail)) fragment0176560Acc00300 =
      SourceJson.object (fuel + 32) (SourceJson.white tail) fragment0176560Acc00400 := by
  have hinput : fragment0176560Field003Chars00 ++ tail = fragment0176560Field003HeaderChars00 ++ (fragment0176960Chars ++ (fragment0176560Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0176560Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 33) (SourceJson.white (fragment0176560Field003Chars00 ++ tail)) fragment0176560Acc00300 =
        SourceJson.object (fuel + 33)
          (SourceJson.white (fragment0176560Field003HeaderChars00 ++ (fragment0176960Chars ++ (fragment0176560Field003SuffixChars00 ++ tail)))) fragment0176560Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 33) (SourceJson.white s) fragment0176560Acc00300) hinput
    _ = (SourceJson.value (fuel + 32) (fragment0176960Chars ++ (fragment0176560Field003SuffixChars00 ++ tail))).bind
        (fragment0176560Field003AfterValue00 (fuel + 32)) := object_fragment0176560_field_003_header fuel (fragment0176960Chars ++ (fragment0176560Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0176960Value, fragment0176560Field003SuffixChars00 ++ tail)).bind (fragment0176560Field003AfterValue00 (fuel + 32)) :=
      congrArg (fun result => result.bind (fragment0176560Field003AfterValue00 (fuel + 32)))
        (value_fragment0176960 (fuel + 0) (fragment0176560Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 32) (SourceJson.white tail) fragment0176560Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176560_object_field_003"
  err.flush

noncomputable def fragment0176560Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0176560Field004Value00 : SourceJson := .number (String.ofList ['4', '2'])
noncomputable def fragment0176560Acc00500 : List (String × SourceJson) := (fragment0176560Field004Key00, fragment0176560Field004Value00) :: fragment0176560Acc00400
noncomputable def fragment0176560Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0176560_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 32) (SourceJson.white (fragment0176560Field004Chars00 ++ tail)) fragment0176560Acc00400 =
      .ok (.obj (fragment0176560Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0176560_object_field_004"
  err.flush

noncomputable def fragment0176560Chars : List Char := '{' :: (fragment0176560Field000Chars00 ++ fragment0176560Field001Chars00 ++ fragment0176560Field002Chars00 ++ fragment0176560Field003Chars00 ++ fragment0176560Field004Chars00)
noncomputable def fragment0176560Value : SourceJson := .obj (fragment0176560Acc00500.reverse)

theorem value_fragment0176560 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 37) (fragment0176560Chars ++ tail) =
      .ok (fragment0176560Value, tail) := by
  have hinput : fragment0176560Chars ++ tail = '{' :: (fragment0176560Field000Chars00 ++ (fragment0176560Field001Chars00 ++ (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0176560Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 37) (fragment0176560Chars ++ tail) =
        SourceJson.value (fuel + 37) ('{' :: (fragment0176560Field000Chars00 ++ (fragment0176560Field001Chars00 ++ (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 37)) hinput
    _ = SourceJson.object (fuel + 36) (SourceJson.white (fragment0176560Field000Chars00 ++ (fragment0176560Field001Chars00 ++ (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail))))))) fragment0176560Acc00000 := by rfl
    _ = SourceJson.object (fuel + 35) (SourceJson.white (fragment0176560Field001Chars00 ++ (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail)))))) fragment0176560Acc00100 := object_fragment0176560_field_000 fuel (fragment0176560Field001Chars00 ++ (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 34) (SourceJson.white (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail))))) fragment0176560Acc00200 := object_fragment0176560_field_001 fuel (fragment0176560Field002Chars00 ++ (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 33) (SourceJson.white (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail)))) fragment0176560Acc00300 := object_fragment0176560_field_002 fuel (fragment0176560Field003Chars00 ++ (fragment0176560Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 32) (SourceJson.white (fragment0176560Field004Chars00 ++ (tail))) fragment0176560Acc00400 := object_fragment0176560_field_003 fuel (fragment0176560Field004Chars00 ++ (tail))
    _ = .ok (fragment0176560Value, tail) := object_fragment0176560_field_004 fuel (tail)

noncomputable def fragment0179691Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0179691Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0179691Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]
noncomputable def fragment0179691Acc00100 : List (String × SourceJson) := (fragment0179691Field000Key00, fragment0179691Field000Value00) :: fragment0179691Acc00000
noncomputable def fragment0179691Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0179691_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0179691Field000Chars00 ++ tail)) fragment0179691Acc00000 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0179691Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0179691_object_field_000"
  err.flush

noncomputable def fragment0179691Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0179691Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0179691Acc00200 : List (String × SourceJson) := (fragment0179691Field001Key00, fragment0179691Field001Value00) :: fragment0179691Acc00100
noncomputable def fragment0179691Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0179691_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0179691Field001Chars00 ++ tail)) fragment0179691Acc00100 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0179691Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0179691_object_field_001"
  err.flush

noncomputable def fragment0179691Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0179691Field002Value00 : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def fragment0179691Acc00300 : List (String × SourceJson) := (fragment0179691Field002Key00, fragment0179691Field002Value00) :: fragment0179691Acc00200
noncomputable def fragment0179691Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',']

theorem object_fragment0179691_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0179691Field002Chars00 ++ tail)) fragment0179691Acc00200 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0179691Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0179691_object_field_002"
  err.flush

noncomputable def fragment0179691Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0179691Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]]
noncomputable def fragment0179691Acc00400 : List (String × SourceJson) := (fragment0179691Field003Key00, fragment0179691Field003Value00) :: fragment0179691Acc00300
noncomputable def fragment0179691Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0179691_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0179691Field003Chars00 ++ tail)) fragment0179691Acc00300 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0179691Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0179691_object_field_003"
  err.flush

noncomputable def fragment0179691Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0179691Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0179691Acc00500 : List (String × SourceJson) := (fragment0179691Field004Key00, fragment0179691Field004Value00) :: fragment0179691Acc00400
noncomputable def fragment0179691Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0179691_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0179691Field004Chars00 ++ tail)) fragment0179691Acc00400 =
      .ok (.obj (fragment0179691Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0179691_object_field_004"
  err.flush

noncomputable def fragment0179691Chars : List Char := '{' :: (fragment0179691Field000Chars00 ++ fragment0179691Field001Chars00 ++ fragment0179691Field002Chars00 ++ fragment0179691Field003Chars00 ++ fragment0179691Field004Chars00)
noncomputable def fragment0179691Value : SourceJson := .obj (fragment0179691Acc00500.reverse)

theorem value_fragment0179691 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0179691Chars ++ tail) =
      .ok (fragment0179691Value, tail) := by
  have hinput : fragment0179691Chars ++ tail = '{' :: (fragment0179691Field000Chars00 ++ (fragment0179691Field001Chars00 ++ (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0179691Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0179691Chars ++ tail) =
        SourceJson.value (fuel + 20) ('{' :: (fragment0179691Field000Chars00 ++ (fragment0179691Field001Chars00 ++ (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0179691Field000Chars00 ++ (fragment0179691Field001Chars00 ++ (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail))))))) fragment0179691Acc00000 := by rfl
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0179691Field001Chars00 ++ (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail)))))) fragment0179691Acc00100 := object_fragment0179691_field_000 fuel (fragment0179691Field001Chars00 ++ (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail))))) fragment0179691Acc00200 := object_fragment0179691_field_001 fuel (fragment0179691Field002Chars00 ++ (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail)))) fragment0179691Acc00300 := object_fragment0179691_field_002 fuel (fragment0179691Field003Chars00 ++ (fragment0179691Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0179691Field004Chars00 ++ (tail))) fragment0179691Acc00400 := object_fragment0179691_field_003 fuel (fragment0179691Field004Chars00 ++ (tail))
    _ = .ok (fragment0179691Value, tail) := object_fragment0179691_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_before_reader"
  err.flush

noncomputable def chunk0009LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0009SuffixChars00 : List Char := [',']
noncomputable def chunk0009Chars00 : List Char := chunk0009LeadChars00 ++ fragment0176560Chars ++ chunk0009SuffixChars00
noncomputable def chunk0009Push00 (acc : List SourceJson) : List SourceJson := fragment0176560Value :: acc

noncomputable def chunk0009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89)
      (SourceJson.white (chunk0009LeadChars00 ++ (fragment0176560Chars ++ rest))) acc =
      (SourceJson.value (fuel + 88) (fragment0176560Chars ++ rest)).bind
        (chunk0009AfterValue00 (fuel + 88) acc) := by rfl

theorem array_chunk0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 88) (SourceJson.white tail) (chunk0009Push00 acc) := by
  have hinput : chunk0009Chars00 ++ tail = chunk0009LeadChars00 ++ (fragment0176560Chars ++ (chunk0009SuffixChars00 ++ tail)) := by
    simp only [chunk0009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 89) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 89)
          (SourceJson.white (chunk0009LeadChars00 ++ (fragment0176560Chars ++ (chunk0009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 89) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 88) (fragment0176560Chars ++ (chunk0009SuffixChars00 ++ tail))).bind
        (chunk0009AfterValue00 (fuel + 88) acc) := array_chunk0009_head fuel (chunk0009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0176560Value, chunk0009SuffixChars00 ++ tail)).bind
        (chunk0009AfterValue00 (fuel + 88) acc) :=
      congrArg (fun result => result.bind (chunk0009AfterValue00 (fuel + 88) acc))
        (value_fragment0176560 (fuel + 51) (chunk0009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 88) (SourceJson.white tail) (chunk0009Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_before_reader"
  err.flush

noncomputable def chunk0010LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0010SuffixChars00 : List Char := [',']
noncomputable def chunk0010Chars00 : List Char := chunk0010LeadChars00 ++ fragment0179691Chars ++ chunk0010SuffixChars00
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson := fragment0179691Value :: acc

noncomputable def chunk0010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 88)
      (SourceJson.white (chunk0010LeadChars00 ++ (fragment0179691Chars ++ rest))) acc =
      (SourceJson.value (fuel + 87) (fragment0179691Chars ++ rest)).bind
        (chunk0010AfterValue00 (fuel + 87) acc) := by rfl

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 88) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white tail) (chunk0010Push00 acc) := by
  have hinput : chunk0010Chars00 ++ tail = chunk0010LeadChars00 ++ (fragment0179691Chars ++ (chunk0010SuffixChars00 ++ tail)) := by
    simp only [chunk0010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 88) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 88)
          (SourceJson.white (chunk0010LeadChars00 ++ (fragment0179691Chars ++ (chunk0010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 88) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 87) (fragment0179691Chars ++ (chunk0010SuffixChars00 ++ tail))).bind
        (chunk0010AfterValue00 (fuel + 87) acc) := array_chunk0010_head fuel (chunk0010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0179691Value, chunk0010SuffixChars00 ++ tail)).bind
        (chunk0010AfterValue00 (fuel + 87) acc) :=
      congrArg (fun result => result.bind (chunk0010AfterValue00 (fuel + 87) acc))
        (value_fragment0179691 (fuel + 67) (chunk0010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 87) (SourceJson.white tail) (chunk0010Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0009Chars00 ++ chunk0010Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0010Push00 (chunk0009Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 89) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0009Chars00 ++ (chunk0010Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 89) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 89) (SourceJson.white (chunk0009Chars00 ++ (chunk0010Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 89) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 88) (SourceJson.white (chunk0010Chars00 ++ (tail))) (chunk0009Push00 (acc)) := array_chunk0009 fuel (chunk0010Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 87) (SourceJson.white tail) (blockPush acc) := array_chunk0010 fuel (tail) (chunk0009Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 176554).take 3954 = blockChars := by rfl

theorem block_original_split : sourceRest 176554 = blockChars ++ sourceRest 180508 := by
  calc
    sourceRest 176554 = (sourceRest 176554).take 3954 ++ (sourceRest 176554).drop 3954 :=
      (List.take_append_drop 3954 (sourceRest 176554)).symm
    _ = blockChars ++ (sourceRest 176554).drop 3954 :=
      congrArg (fun part => part ++ (sourceRest 176554).drop 3954) block_original_prefix
    _ = blockChars ++ sourceRest 180508 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 176554 3954)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 89) (SourceJson.white (sourceRest 176554)) acc =
      SourceJson.array (fuel + 87) (SourceJson.white (sourceRest 180508)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 89) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 180508) acc)

#print axioms array_fragment0176960_chunk_000
#print axioms array_fragment0176960_chunk_001
#print axioms array_fragment0176960_chunk_002
#print axioms array_fragment0176960_chunk_003
#print axioms array_fragment0176960_chunk_004
#print axioms value_fragment0176960
#print axioms object_fragment0176560_field_000
#print axioms object_fragment0176560_field_001
#print axioms object_fragment0176560_field_002
#print axioms object_fragment0176560_field_003_header
#print axioms object_fragment0176560_field_003
#print axioms object_fragment0176560_field_004
#print axioms value_fragment0176560
#print axioms object_fragment0179691_field_000
#print axioms object_fragment0179691_field_001
#print axioms object_fragment0179691_field_002
#print axioms object_fragment0179691_field_003
#print axioms object_fragment0179691_field_004
#print axioms value_fragment0179691
#print axioms array_chunk0009_head
#print axioms array_chunk0009
#print axioms array_chunk0010_head
#print axioms array_chunk0010
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock006

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
