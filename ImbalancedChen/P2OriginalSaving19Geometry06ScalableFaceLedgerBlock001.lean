import ImbalancedChen.P2OriginalSaving19Geometry06ScalableInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock001

noncomputable def fragment0083014Acc00000 : List SourceJson := []

noncomputable def fragment0083014Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083014Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0083014_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (fragment0083014Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 31) (SourceJson.white tail) (fragment0083014Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0083014Acc00100 : List SourceJson := fragment0083014Chunk000Push00 fragment0083014Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083014_array_chunk_000"
  err.flush

noncomputable def fragment0083014Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083014Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0083014_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (fragment0083014Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (fragment0083014Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0083014Acc00200 : List SourceJson := fragment0083014Chunk001Push00 fragment0083014Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083014_array_chunk_001"
  err.flush

noncomputable def fragment0083014Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083014Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9'])]) :: (acc))

theorem array_fragment0083014_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (fragment0083014Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 27) (SourceJson.white tail) (fragment0083014Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0083014Acc00300 : List SourceJson := fragment0083014Chunk002Push00 fragment0083014Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083014_array_chunk_002"
  err.flush

noncomputable def fragment0083014Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083014Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: (acc))

theorem array_fragment0083014_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (fragment0083014Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (fragment0083014Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0083014Acc00400 : List SourceJson := fragment0083014Chunk003Push00 fragment0083014Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083014_array_chunk_003"
  err.flush

noncomputable def fragment0083014Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0083014Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0'])]) :: (acc))

theorem array_fragment0083014_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (fragment0083014Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0083014Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0083014Acc00500 : List SourceJson := fragment0083014Chunk004Push00 fragment0083014Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083014_array_chunk_004"
  err.flush

noncomputable def fragment0083014Chars : List Char := '[' :: (fragment0083014Chunk000Chars00 ++ fragment0083014Chunk001Chars00 ++ fragment0083014Chunk002Chars00 ++ fragment0083014Chunk003Chars00 ++ fragment0083014Chunk004Chars00)
noncomputable def fragment0083014Value : SourceJson := .arr (fragment0083014Acc00500.reverse)

theorem value_fragment0083014 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 34) (fragment0083014Chars ++ tail) =
      .ok (fragment0083014Value, tail) := by
  have hinput : fragment0083014Chars ++ tail = '[' :: (fragment0083014Chunk000Chars00 ++ (fragment0083014Chunk001Chars00 ++ (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0083014Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 34) (fragment0083014Chars ++ tail) =
        SourceJson.value (fuel + 34) ('[' :: (fragment0083014Chunk000Chars00 ++ (fragment0083014Chunk001Chars00 ++ (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 34)) hinput
    _ = SourceJson.array (fuel + 33) (SourceJson.white (fragment0083014Chunk000Chars00 ++ (fragment0083014Chunk001Chars00 ++ (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail))))))) fragment0083014Acc00000 := by rfl
    _ = SourceJson.array (fuel + 31) (SourceJson.white (fragment0083014Chunk001Chars00 ++ (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail)))))) fragment0083014Acc00100 := array_fragment0083014_chunk_000 fuel (fragment0083014Chunk001Chars00 ++ (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail))))) fragment0083014Acc00000
    _ = SourceJson.array (fuel + 29) (SourceJson.white (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail))))) fragment0083014Acc00200 := array_fragment0083014_chunk_001 fuel (fragment0083014Chunk002Chars00 ++ (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail)))) fragment0083014Acc00100
    _ = SourceJson.array (fuel + 27) (SourceJson.white (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail)))) fragment0083014Acc00300 := array_fragment0083014_chunk_002 fuel (fragment0083014Chunk003Chars00 ++ (fragment0083014Chunk004Chars00 ++ (tail))) fragment0083014Acc00200
    _ = SourceJson.array (fuel + 25) (SourceJson.white (fragment0083014Chunk004Chars00 ++ (tail))) fragment0083014Acc00400 := array_fragment0083014_chunk_003 fuel (fragment0083014Chunk004Chars00 ++ (tail)) fragment0083014Acc00300
    _ = .ok (fragment0083014Value, tail) := array_fragment0083014_chunk_004 fuel (tail) fragment0083014Acc00400

noncomputable def fragment0082563Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0082563Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0082563Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]
noncomputable def fragment0082563Acc00100 : List (String × SourceJson) := (fragment0082563Field000Key00, fragment0082563Field000Value00) :: fragment0082563Acc00000
noncomputable def fragment0082563Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0082563_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 38) (SourceJson.white (fragment0082563Field000Chars00 ++ tail)) fragment0082563Acc00000 =
      SourceJson.object (fuel + 37) (SourceJson.white tail) fragment0082563Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082563_object_field_000"
  err.flush

noncomputable def fragment0082563Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0082563Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0082563Acc00200 : List (String × SourceJson) := (fragment0082563Field001Key00, fragment0082563Field001Value00) :: fragment0082563Acc00100
noncomputable def fragment0082563Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0082563_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 37) (SourceJson.white (fragment0082563Field001Chars00 ++ tail)) fragment0082563Acc00100 =
      SourceJson.object (fuel + 36) (SourceJson.white tail) fragment0082563Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082563_object_field_001"
  err.flush

noncomputable def fragment0082563Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0082563Field002Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0082563Acc00300 : List (String × SourceJson) := (fragment0082563Field002Key00, fragment0082563Field002Value00) :: fragment0082563Acc00200
noncomputable def fragment0082563Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '0', ',']

theorem object_fragment0082563_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 36) (SourceJson.white (fragment0082563Field002Chars00 ++ tail)) fragment0082563Acc00200 =
      SourceJson.object (fuel + 35) (SourceJson.white tail) fragment0082563Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082563_object_field_002"
  err.flush

noncomputable def fragment0082563Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0082563Field003Value00 : SourceJson := fragment0083014Value
noncomputable def fragment0082563Acc00400 : List (String × SourceJson) := (fragment0082563Field003Key00, fragment0082563Field003Value00) :: fragment0082563Acc00300
noncomputable def fragment0082563Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0082563Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0082563Field003Chars00 : List Char := fragment0082563Field003HeaderChars00 ++ fragment0083014Chars ++ fragment0082563Field003SuffixChars00

noncomputable def fragment0082563Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0082563Field003Key00, result.1) :: fragment0082563Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0082563Field003Key00, result.1) :: fragment0082563Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0082563_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 35) (SourceJson.white (fragment0082563Field003HeaderChars00 ++ rest)) fragment0082563Acc00300 =
      (SourceJson.value (fuel + 34) rest).bind (fragment0082563Field003AfterValue00 (fuel + 34)) := by rfl

theorem object_fragment0082563_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 35) (SourceJson.white (fragment0082563Field003Chars00 ++ tail)) fragment0082563Acc00300 =
      SourceJson.object (fuel + 34) (SourceJson.white tail) fragment0082563Acc00400 := by
  have hinput : fragment0082563Field003Chars00 ++ tail = fragment0082563Field003HeaderChars00 ++ (fragment0083014Chars ++ (fragment0082563Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0082563Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 35) (SourceJson.white (fragment0082563Field003Chars00 ++ tail)) fragment0082563Acc00300 =
        SourceJson.object (fuel + 35)
          (SourceJson.white (fragment0082563Field003HeaderChars00 ++ (fragment0083014Chars ++ (fragment0082563Field003SuffixChars00 ++ tail)))) fragment0082563Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 35) (SourceJson.white s) fragment0082563Acc00300) hinput
    _ = (SourceJson.value (fuel + 34) (fragment0083014Chars ++ (fragment0082563Field003SuffixChars00 ++ tail))).bind
        (fragment0082563Field003AfterValue00 (fuel + 34)) := object_fragment0082563_field_003_header fuel (fragment0083014Chars ++ (fragment0082563Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0083014Value, fragment0082563Field003SuffixChars00 ++ tail)).bind (fragment0082563Field003AfterValue00 (fuel + 34)) :=
      congrArg (fun result => result.bind (fragment0082563Field003AfterValue00 (fuel + 34)))
        (value_fragment0083014 (fuel + 0) (fragment0082563Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 34) (SourceJson.white tail) fragment0082563Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082563_object_field_003"
  err.flush

noncomputable def fragment0082563Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0082563Field004Value00 : SourceJson := .number (String.ofList ['8', '7'])
noncomputable def fragment0082563Acc00500 : List (String × SourceJson) := (fragment0082563Field004Key00, fragment0082563Field004Value00) :: fragment0082563Acc00400
noncomputable def fragment0082563Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '8', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0082563_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 34) (SourceJson.white (fragment0082563Field004Chars00 ++ tail)) fragment0082563Acc00400 =
      .ok (.obj (fragment0082563Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082563_object_field_004"
  err.flush

noncomputable def fragment0082563Chars : List Char := '{' :: (fragment0082563Field000Chars00 ++ fragment0082563Field001Chars00 ++ fragment0082563Field002Chars00 ++ fragment0082563Field003Chars00 ++ fragment0082563Field004Chars00)
noncomputable def fragment0082563Value : SourceJson := .obj (fragment0082563Acc00500.reverse)

theorem value_fragment0082563 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 39) (fragment0082563Chars ++ tail) =
      .ok (fragment0082563Value, tail) := by
  have hinput : fragment0082563Chars ++ tail = '{' :: (fragment0082563Field000Chars00 ++ (fragment0082563Field001Chars00 ++ (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0082563Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 39) (fragment0082563Chars ++ tail) =
        SourceJson.value (fuel + 39) ('{' :: (fragment0082563Field000Chars00 ++ (fragment0082563Field001Chars00 ++ (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 39)) hinput
    _ = SourceJson.object (fuel + 38) (SourceJson.white (fragment0082563Field000Chars00 ++ (fragment0082563Field001Chars00 ++ (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail))))))) fragment0082563Acc00000 := by rfl
    _ = SourceJson.object (fuel + 37) (SourceJson.white (fragment0082563Field001Chars00 ++ (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail)))))) fragment0082563Acc00100 := object_fragment0082563_field_000 fuel (fragment0082563Field001Chars00 ++ (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 36) (SourceJson.white (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail))))) fragment0082563Acc00200 := object_fragment0082563_field_001 fuel (fragment0082563Field002Chars00 ++ (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 35) (SourceJson.white (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail)))) fragment0082563Acc00300 := object_fragment0082563_field_002 fuel (fragment0082563Field003Chars00 ++ (fragment0082563Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 34) (SourceJson.white (fragment0082563Field004Chars00 ++ (tail))) fragment0082563Acc00400 := object_fragment0082563_field_003 fuel (fragment0082563Field004Chars00 ++ (tail))
    _ = .ok (fragment0082563Value, tail) := object_fragment0082563_field_004 fuel (tail)

noncomputable def fragment0086467Acc00000 : List SourceJson := []

noncomputable def fragment0086467Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0086467Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6'])]) :: (acc))

theorem array_fragment0086467_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0086467Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0086467Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0086467Acc00100 : List SourceJson := fragment0086467Chunk000Push00 fragment0086467Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086467_array_chunk_000"
  err.flush

noncomputable def fragment0086467Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0086467Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0086467_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0086467Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0086467Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0086467Acc00200 : List SourceJson := fragment0086467Chunk001Push00 fragment0086467Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086467_array_chunk_001"
  err.flush

noncomputable def fragment0086467Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0086467Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0086467_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0086467Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0086467Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0086467Acc00300 : List SourceJson := fragment0086467Chunk002Push00 fragment0086467Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086467_array_chunk_002"
  err.flush

noncomputable def fragment0086467Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0086467Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0086467_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0086467Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0086467Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0086467Acc00400 : List SourceJson := fragment0086467Chunk003Push00 fragment0086467Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086467_array_chunk_003"
  err.flush

noncomputable def fragment0086467Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0086467Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc)

theorem array_fragment0086467_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0086467Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0086467Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0086467Acc00500 : List SourceJson := fragment0086467Chunk004Push00 fragment0086467Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086467_array_chunk_004"
  err.flush

noncomputable def fragment0086467Chars : List Char := '[' :: (fragment0086467Chunk000Chars00 ++ fragment0086467Chunk001Chars00 ++ fragment0086467Chunk002Chars00 ++ fragment0086467Chunk003Chars00 ++ fragment0086467Chunk004Chars00)
noncomputable def fragment0086467Value : SourceJson := .arr (fragment0086467Acc00500.reverse)

theorem value_fragment0086467 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 24) (fragment0086467Chars ++ tail) =
      .ok (fragment0086467Value, tail) := by
  have hinput : fragment0086467Chars ++ tail = '[' :: (fragment0086467Chunk000Chars00 ++ (fragment0086467Chunk001Chars00 ++ (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0086467Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 24) (fragment0086467Chars ++ tail) =
        SourceJson.value (fuel + 24) ('[' :: (fragment0086467Chunk000Chars00 ++ (fragment0086467Chunk001Chars00 ++ (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 24)) hinput
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0086467Chunk000Chars00 ++ (fragment0086467Chunk001Chars00 ++ (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail))))))) fragment0086467Acc00000 := by rfl
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0086467Chunk001Chars00 ++ (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail)))))) fragment0086467Acc00100 := array_fragment0086467_chunk_000 fuel (fragment0086467Chunk001Chars00 ++ (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail))))) fragment0086467Acc00000
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail))))) fragment0086467Acc00200 := array_fragment0086467_chunk_001 fuel (fragment0086467Chunk002Chars00 ++ (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail)))) fragment0086467Acc00100
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail)))) fragment0086467Acc00300 := array_fragment0086467_chunk_002 fuel (fragment0086467Chunk003Chars00 ++ (fragment0086467Chunk004Chars00 ++ (tail))) fragment0086467Acc00200
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0086467Chunk004Chars00 ++ (tail))) fragment0086467Acc00400 := array_fragment0086467_chunk_003 fuel (fragment0086467Chunk004Chars00 ++ (tail)) fragment0086467Acc00300
    _ = .ok (fragment0086467Value, tail) := array_fragment0086467_chunk_004 fuel (tail) fragment0086467Acc00400

noncomputable def fragment0086158Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0086158Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0086158Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]
noncomputable def fragment0086158Acc00100 : List (String × SourceJson) := (fragment0086158Field000Key00, fragment0086158Field000Value00) :: fragment0086158Acc00000
noncomputable def fragment0086158Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0086158_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0086158Field000Chars00 ++ tail)) fragment0086158Acc00000 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0086158Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086158_object_field_000"
  err.flush

noncomputable def fragment0086158Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0086158Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0086158Acc00200 : List (String × SourceJson) := (fragment0086158Field001Key00, fragment0086158Field001Value00) :: fragment0086158Acc00100
noncomputable def fragment0086158Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0086158_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0086158Field001Chars00 ++ tail)) fragment0086158Acc00100 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0086158Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086158_object_field_001"
  err.flush

noncomputable def fragment0086158Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0086158Field002Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0086158Acc00300 : List (String × SourceJson) := (fragment0086158Field002Key00, fragment0086158Field002Value00) :: fragment0086158Acc00200
noncomputable def fragment0086158Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0086158_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0086158Field002Chars00 ++ tail)) fragment0086158Acc00200 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0086158Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086158_object_field_002"
  err.flush

noncomputable def fragment0086158Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0086158Field003Value00 : SourceJson := fragment0086467Value
noncomputable def fragment0086158Acc00400 : List (String × SourceJson) := (fragment0086158Field003Key00, fragment0086158Field003Value00) :: fragment0086158Acc00300
noncomputable def fragment0086158Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0086158Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0086158Field003Chars00 : List Char := fragment0086158Field003HeaderChars00 ++ fragment0086467Chars ++ fragment0086158Field003SuffixChars00

noncomputable def fragment0086158Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0086158Field003Key00, result.1) :: fragment0086158Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0086158Field003Key00, result.1) :: fragment0086158Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0086158_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0086158Field003HeaderChars00 ++ rest)) fragment0086158Acc00300 =
      (SourceJson.value (fuel + 24) rest).bind (fragment0086158Field003AfterValue00 (fuel + 24)) := by rfl

theorem object_fragment0086158_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0086158Field003Chars00 ++ tail)) fragment0086158Acc00300 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0086158Acc00400 := by
  have hinput : fragment0086158Field003Chars00 ++ tail = fragment0086158Field003HeaderChars00 ++ (fragment0086467Chars ++ (fragment0086158Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0086158Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0086158Field003Chars00 ++ tail)) fragment0086158Acc00300 =
        SourceJson.object (fuel + 25)
          (SourceJson.white (fragment0086158Field003HeaderChars00 ++ (fragment0086467Chars ++ (fragment0086158Field003SuffixChars00 ++ tail)))) fragment0086158Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 25) (SourceJson.white s) fragment0086158Acc00300) hinput
    _ = (SourceJson.value (fuel + 24) (fragment0086467Chars ++ (fragment0086158Field003SuffixChars00 ++ tail))).bind
        (fragment0086158Field003AfterValue00 (fuel + 24)) := object_fragment0086158_field_003_header fuel (fragment0086467Chars ++ (fragment0086158Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0086467Value, fragment0086158Field003SuffixChars00 ++ tail)).bind (fragment0086158Field003AfterValue00 (fuel + 24)) :=
      congrArg (fun result => result.bind (fragment0086158Field003AfterValue00 (fuel + 24)))
        (value_fragment0086467 (fuel + 0) (fragment0086158Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0086158Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086158_object_field_003"
  err.flush

noncomputable def fragment0086158Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0086158Field004Value00 : SourceJson := .number (String.ofList ['1', '7'])
noncomputable def fragment0086158Acc00500 : List (String × SourceJson) := (fragment0086158Field004Key00, fragment0086158Field004Value00) :: fragment0086158Acc00400
noncomputable def fragment0086158Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0086158_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0086158Field004Chars00 ++ tail)) fragment0086158Acc00400 =
      .ok (.obj (fragment0086158Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0086158_object_field_004"
  err.flush

noncomputable def fragment0086158Chars : List Char := '{' :: (fragment0086158Field000Chars00 ++ fragment0086158Field001Chars00 ++ fragment0086158Field002Chars00 ++ fragment0086158Field003Chars00 ++ fragment0086158Field004Chars00)
noncomputable def fragment0086158Value : SourceJson := .obj (fragment0086158Acc00500.reverse)

theorem value_fragment0086158 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (fragment0086158Chars ++ tail) =
      .ok (fragment0086158Value, tail) := by
  have hinput : fragment0086158Chars ++ tail = '{' :: (fragment0086158Field000Chars00 ++ (fragment0086158Field001Chars00 ++ (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0086158Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 29) (fragment0086158Chars ++ tail) =
        SourceJson.value (fuel + 29) ('{' :: (fragment0086158Field000Chars00 ++ (fragment0086158Field001Chars00 ++ (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 29)) hinput
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0086158Field000Chars00 ++ (fragment0086158Field001Chars00 ++ (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail))))))) fragment0086158Acc00000 := by rfl
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0086158Field001Chars00 ++ (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail)))))) fragment0086158Acc00100 := object_fragment0086158_field_000 fuel (fragment0086158Field001Chars00 ++ (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail))))) fragment0086158Acc00200 := object_fragment0086158_field_001 fuel (fragment0086158Field002Chars00 ++ (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail)))) fragment0086158Acc00300 := object_fragment0086158_field_002 fuel (fragment0086158Field003Chars00 ++ (fragment0086158Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0086158Field004Chars00 ++ (tail))) fragment0086158Acc00400 := object_fragment0086158_field_003 fuel (fragment0086158Field004Chars00 ++ (tail))
    _ = .ok (fragment0086158Value, tail) := object_fragment0086158_field_004 fuel (tail)

noncomputable def fragment0088581Acc00000 : List SourceJson := []

noncomputable def fragment0088581Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0088581Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: (acc))

theorem array_fragment0088581_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (fragment0088581Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (fragment0088581Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0088581Acc00100 : List SourceJson := fragment0088581Chunk000Push00 fragment0088581Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088581_array_chunk_000"
  err.flush

noncomputable def fragment0088581Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0088581Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0088581_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (fragment0088581Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 23) (SourceJson.white tail) (fragment0088581Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0088581Acc00200 : List SourceJson := fragment0088581Chunk001Push00 fragment0088581Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088581_array_chunk_001"
  err.flush

noncomputable def fragment0088581Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0088581Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6'])]) :: (acc))

theorem array_fragment0088581_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0088581Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0088581Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0088581Acc00300 : List SourceJson := fragment0088581Chunk002Push00 fragment0088581Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088581_array_chunk_002"
  err.flush

noncomputable def fragment0088581Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0088581Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]) :: (acc))

theorem array_fragment0088581_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0088581Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0088581Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0088581Acc00400 : List SourceJson := fragment0088581Chunk003Push00 fragment0088581Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088581_array_chunk_003"
  err.flush

noncomputable def fragment0088581Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0088581Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]) :: (acc)

theorem array_fragment0088581_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0088581Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0088581Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0088581Acc00500 : List SourceJson := fragment0088581Chunk004Push00 fragment0088581Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088581_array_chunk_004"
  err.flush

noncomputable def fragment0088581Chars : List Char := '[' :: (fragment0088581Chunk000Chars00 ++ fragment0088581Chunk001Chars00 ++ fragment0088581Chunk002Chars00 ++ fragment0088581Chunk003Chars00 ++ fragment0088581Chunk004Chars00)
noncomputable def fragment0088581Value : SourceJson := .arr (fragment0088581Acc00500.reverse)

theorem value_fragment0088581 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 28) (fragment0088581Chars ++ tail) =
      .ok (fragment0088581Value, tail) := by
  have hinput : fragment0088581Chars ++ tail = '[' :: (fragment0088581Chunk000Chars00 ++ (fragment0088581Chunk001Chars00 ++ (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0088581Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 28) (fragment0088581Chars ++ tail) =
        SourceJson.value (fuel + 28) ('[' :: (fragment0088581Chunk000Chars00 ++ (fragment0088581Chunk001Chars00 ++ (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 28)) hinput
    _ = SourceJson.array (fuel + 27) (SourceJson.white (fragment0088581Chunk000Chars00 ++ (fragment0088581Chunk001Chars00 ++ (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail))))))) fragment0088581Acc00000 := by rfl
    _ = SourceJson.array (fuel + 25) (SourceJson.white (fragment0088581Chunk001Chars00 ++ (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail)))))) fragment0088581Acc00100 := array_fragment0088581_chunk_000 fuel (fragment0088581Chunk001Chars00 ++ (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail))))) fragment0088581Acc00000
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail))))) fragment0088581Acc00200 := array_fragment0088581_chunk_001 fuel (fragment0088581Chunk002Chars00 ++ (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail)))) fragment0088581Acc00100
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail)))) fragment0088581Acc00300 := array_fragment0088581_chunk_002 fuel (fragment0088581Chunk003Chars00 ++ (fragment0088581Chunk004Chars00 ++ (tail))) fragment0088581Acc00200
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0088581Chunk004Chars00 ++ (tail))) fragment0088581Acc00400 := array_fragment0088581_chunk_003 fuel (fragment0088581Chunk004Chars00 ++ (tail)) fragment0088581Acc00300
    _ = .ok (fragment0088581Value, tail) := array_fragment0088581_chunk_004 fuel (tail) fragment0088581Acc00400

noncomputable def fragment0088194Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0088194Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0088194Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8'])]
noncomputable def fragment0088194Acc00100 : List (String × SourceJson) := (fragment0088194Field000Key00, fragment0088194Field000Value00) :: fragment0088194Acc00000
noncomputable def fragment0088194Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0088194_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 32) (SourceJson.white (fragment0088194Field000Chars00 ++ tail)) fragment0088194Acc00000 =
      SourceJson.object (fuel + 31) (SourceJson.white tail) fragment0088194Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088194_object_field_000"
  err.flush

noncomputable def fragment0088194Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0088194Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0088194Acc00200 : List (String × SourceJson) := (fragment0088194Field001Key00, fragment0088194Field001Value00) :: fragment0088194Acc00100
noncomputable def fragment0088194Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0088194_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 31) (SourceJson.white (fragment0088194Field001Chars00 ++ tail)) fragment0088194Acc00100 =
      SourceJson.object (fuel + 30) (SourceJson.white tail) fragment0088194Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088194_object_field_001"
  err.flush

noncomputable def fragment0088194Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0088194Field002Value00 : SourceJson := .number (String.ofList ['2', '8'])
noncomputable def fragment0088194Acc00300 : List (String × SourceJson) := (fragment0088194Field002Key00, fragment0088194Field002Value00) :: fragment0088194Acc00200
noncomputable def fragment0088194Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '8', ',']

theorem object_fragment0088194_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 30) (SourceJson.white (fragment0088194Field002Chars00 ++ tail)) fragment0088194Acc00200 =
      SourceJson.object (fuel + 29) (SourceJson.white tail) fragment0088194Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088194_object_field_002"
  err.flush

noncomputable def fragment0088194Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0088194Field003Value00 : SourceJson := fragment0088581Value
noncomputable def fragment0088194Acc00400 : List (String × SourceJson) := (fragment0088194Field003Key00, fragment0088194Field003Value00) :: fragment0088194Acc00300
noncomputable def fragment0088194Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0088194Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0088194Field003Chars00 : List Char := fragment0088194Field003HeaderChars00 ++ fragment0088581Chars ++ fragment0088194Field003SuffixChars00

noncomputable def fragment0088194Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0088194Field003Key00, result.1) :: fragment0088194Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0088194Field003Key00, result.1) :: fragment0088194Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0088194_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0088194Field003HeaderChars00 ++ rest)) fragment0088194Acc00300 =
      (SourceJson.value (fuel + 28) rest).bind (fragment0088194Field003AfterValue00 (fuel + 28)) := by rfl

theorem object_fragment0088194_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0088194Field003Chars00 ++ tail)) fragment0088194Acc00300 =
      SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0088194Acc00400 := by
  have hinput : fragment0088194Field003Chars00 ++ tail = fragment0088194Field003HeaderChars00 ++ (fragment0088581Chars ++ (fragment0088194Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0088194Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0088194Field003Chars00 ++ tail)) fragment0088194Acc00300 =
        SourceJson.object (fuel + 29)
          (SourceJson.white (fragment0088194Field003HeaderChars00 ++ (fragment0088581Chars ++ (fragment0088194Field003SuffixChars00 ++ tail)))) fragment0088194Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 29) (SourceJson.white s) fragment0088194Acc00300) hinput
    _ = (SourceJson.value (fuel + 28) (fragment0088581Chars ++ (fragment0088194Field003SuffixChars00 ++ tail))).bind
        (fragment0088194Field003AfterValue00 (fuel + 28)) := object_fragment0088194_field_003_header fuel (fragment0088581Chars ++ (fragment0088194Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0088581Value, fragment0088194Field003SuffixChars00 ++ tail)).bind (fragment0088194Field003AfterValue00 (fuel + 28)) :=
      congrArg (fun result => result.bind (fragment0088194Field003AfterValue00 (fuel + 28)))
        (value_fragment0088581 (fuel + 0) (fragment0088194Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0088194Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088194_object_field_003"
  err.flush

noncomputable def fragment0088194Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0088194Field004Value00 : SourceJson := .number (String.ofList ['5', '5'])
noncomputable def fragment0088194Acc00500 : List (String × SourceJson) := (fragment0088194Field004Key00, fragment0088194Field004Value00) :: fragment0088194Acc00400
noncomputable def fragment0088194Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0088194_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0088194Field004Chars00 ++ tail)) fragment0088194Acc00400 =
      .ok (.obj (fragment0088194Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0088194_object_field_004"
  err.flush

noncomputable def fragment0088194Chars : List Char := '{' :: (fragment0088194Field000Chars00 ++ fragment0088194Field001Chars00 ++ fragment0088194Field002Chars00 ++ fragment0088194Field003Chars00 ++ fragment0088194Field004Chars00)
noncomputable def fragment0088194Value : SourceJson := .obj (fragment0088194Acc00500.reverse)

theorem value_fragment0088194 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 33) (fragment0088194Chars ++ tail) =
      .ok (fragment0088194Value, tail) := by
  have hinput : fragment0088194Chars ++ tail = '{' :: (fragment0088194Field000Chars00 ++ (fragment0088194Field001Chars00 ++ (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0088194Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 33) (fragment0088194Chars ++ tail) =
        SourceJson.value (fuel + 33) ('{' :: (fragment0088194Field000Chars00 ++ (fragment0088194Field001Chars00 ++ (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 33)) hinput
    _ = SourceJson.object (fuel + 32) (SourceJson.white (fragment0088194Field000Chars00 ++ (fragment0088194Field001Chars00 ++ (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail))))))) fragment0088194Acc00000 := by rfl
    _ = SourceJson.object (fuel + 31) (SourceJson.white (fragment0088194Field001Chars00 ++ (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail)))))) fragment0088194Acc00100 := object_fragment0088194_field_000 fuel (fragment0088194Field001Chars00 ++ (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 30) (SourceJson.white (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail))))) fragment0088194Acc00200 := object_fragment0088194_field_001 fuel (fragment0088194Field002Chars00 ++ (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 29) (SourceJson.white (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail)))) fragment0088194Acc00300 := object_fragment0088194_field_002 fuel (fragment0088194Field003Chars00 ++ (fragment0088194Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0088194Field004Chars00 ++ (tail))) fragment0088194Acc00400 := object_fragment0088194_field_003 fuel (fragment0088194Field004Chars00 ++ (tail))
    _ = .ok (fragment0088194Value, tail) := object_fragment0088194_field_004 fuel (tail)

noncomputable def fragment0091119Acc00000 : List SourceJson := []

noncomputable def fragment0091119Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0091119Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4'])]) :: (acc))

theorem array_fragment0091119_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0091119Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0091119Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0091119Acc00100 : List SourceJson := fragment0091119Chunk000Push00 fragment0091119Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0091119_array_chunk_000"
  err.flush

noncomputable def fragment0091119Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0091119Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])]) :: (acc))

theorem array_fragment0091119_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0091119Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0091119Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0091119Acc00200 : List SourceJson := fragment0091119Chunk001Push00 fragment0091119Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0091119_array_chunk_001"
  err.flush

noncomputable def fragment0091119Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0091119Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: (acc))

theorem array_fragment0091119_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0091119Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0091119Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0091119Acc00300 : List SourceJson := fragment0091119Chunk002Push00 fragment0091119Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0091119_array_chunk_002"
  err.flush

noncomputable def fragment0091119Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0091119Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])]) :: (acc))

theorem array_fragment0091119_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0091119Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0091119Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0091119Acc00400 : List SourceJson := fragment0091119Chunk003Push00 fragment0091119Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0091119_array_chunk_003"
  err.flush

noncomputable def fragment0091119Chars : List Char := '[' :: (fragment0091119Chunk000Chars00 ++ fragment0091119Chunk001Chars00 ++ fragment0091119Chunk002Chars00 ++ fragment0091119Chunk003Chars00)
noncomputable def fragment0091119Value : SourceJson := .arr (fragment0091119Acc00400.reverse)

theorem value_fragment0091119 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0091119Chars ++ tail) =
      .ok (fragment0091119Value, tail) := by
  have hinput : fragment0091119Chars ++ tail = '[' :: (fragment0091119Chunk000Chars00 ++ (fragment0091119Chunk001Chars00 ++ (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0091119Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0091119Chars ++ tail) =
        SourceJson.value (fuel + 20) ('[' :: (fragment0091119Chunk000Chars00 ++ (fragment0091119Chunk001Chars00 ++ (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0091119Chunk000Chars00 ++ (fragment0091119Chunk001Chars00 ++ (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail)))))) fragment0091119Acc00000 := by rfl
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0091119Chunk001Chars00 ++ (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail))))) fragment0091119Acc00100 := array_fragment0091119_chunk_000 fuel (fragment0091119Chunk001Chars00 ++ (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail)))) fragment0091119Acc00000
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail)))) fragment0091119Acc00200 := array_fragment0091119_chunk_001 fuel (fragment0091119Chunk002Chars00 ++ (fragment0091119Chunk003Chars00 ++ (tail))) fragment0091119Acc00100
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0091119Chunk003Chars00 ++ (tail))) fragment0091119Acc00300 := array_fragment0091119_chunk_002 fuel (fragment0091119Chunk003Chars00 ++ (tail)) fragment0091119Acc00200
    _ = .ok (fragment0091119Value, tail) := array_fragment0091119_chunk_003 fuel (tail) fragment0091119Acc00300

noncomputable def fragment0090848Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0090848Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0090848Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]
noncomputable def fragment0090848Acc00100 : List (String × SourceJson) := (fragment0090848Field000Key00, fragment0090848Field000Value00) :: fragment0090848Acc00000
noncomputable def fragment0090848Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0090848_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0090848Field000Chars00 ++ tail)) fragment0090848Acc00000 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0090848Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090848_object_field_000"
  err.flush

noncomputable def fragment0090848Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0090848Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0090848Acc00200 : List (String × SourceJson) := (fragment0090848Field001Key00, fragment0090848Field001Value00) :: fragment0090848Acc00100
noncomputable def fragment0090848Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0090848_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0090848Field001Chars00 ++ tail)) fragment0090848Acc00100 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0090848Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090848_object_field_001"
  err.flush

noncomputable def fragment0090848Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0090848Field002Value00 : SourceJson := .number (String.ofList ['1', '6'])
noncomputable def fragment0090848Acc00300 : List (String × SourceJson) := (fragment0090848Field002Key00, fragment0090848Field002Value00) :: fragment0090848Acc00200
noncomputable def fragment0090848Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '6', ',']

theorem object_fragment0090848_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0090848Field002Chars00 ++ tail)) fragment0090848Acc00200 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0090848Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090848_object_field_002"
  err.flush

noncomputable def fragment0090848Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0090848Field003Value00 : SourceJson := fragment0091119Value
noncomputable def fragment0090848Acc00400 : List (String × SourceJson) := (fragment0090848Field003Key00, fragment0090848Field003Value00) :: fragment0090848Acc00300
noncomputable def fragment0090848Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0090848Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0090848Field003Chars00 : List Char := fragment0090848Field003HeaderChars00 ++ fragment0091119Chars ++ fragment0090848Field003SuffixChars00

noncomputable def fragment0090848Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0090848Field003Key00, result.1) :: fragment0090848Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0090848Field003Key00, result.1) :: fragment0090848Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0090848_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0090848Field003HeaderChars00 ++ rest)) fragment0090848Acc00300 =
      (SourceJson.value (fuel + 20) rest).bind (fragment0090848Field003AfterValue00 (fuel + 20)) := by rfl

theorem object_fragment0090848_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0090848Field003Chars00 ++ tail)) fragment0090848Acc00300 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0090848Acc00400 := by
  have hinput : fragment0090848Field003Chars00 ++ tail = fragment0090848Field003HeaderChars00 ++ (fragment0091119Chars ++ (fragment0090848Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0090848Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0090848Field003Chars00 ++ tail)) fragment0090848Acc00300 =
        SourceJson.object (fuel + 21)
          (SourceJson.white (fragment0090848Field003HeaderChars00 ++ (fragment0091119Chars ++ (fragment0090848Field003SuffixChars00 ++ tail)))) fragment0090848Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 21) (SourceJson.white s) fragment0090848Acc00300) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0091119Chars ++ (fragment0090848Field003SuffixChars00 ++ tail))).bind
        (fragment0090848Field003AfterValue00 (fuel + 20)) := object_fragment0090848_field_003_header fuel (fragment0091119Chars ++ (fragment0090848Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0091119Value, fragment0090848Field003SuffixChars00 ++ tail)).bind (fragment0090848Field003AfterValue00 (fuel + 20)) :=
      congrArg (fun result => result.bind (fragment0090848Field003AfterValue00 (fuel + 20)))
        (value_fragment0091119 (fuel + 0) (fragment0090848Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0090848Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090848_object_field_003"
  err.flush

noncomputable def fragment0090848Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0090848Field004Value00 : SourceJson := .number (String.ofList ['1', '5'])
noncomputable def fragment0090848Acc00500 : List (String × SourceJson) := (fragment0090848Field004Key00, fragment0090848Field004Value00) :: fragment0090848Acc00400
noncomputable def fragment0090848Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0090848_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0090848Field004Chars00 ++ tail)) fragment0090848Acc00400 =
      .ok (.obj (fragment0090848Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0090848_object_field_004"
  err.flush

noncomputable def fragment0090848Chars : List Char := '{' :: (fragment0090848Field000Chars00 ++ fragment0090848Field001Chars00 ++ fragment0090848Field002Chars00 ++ fragment0090848Field003Chars00 ++ fragment0090848Field004Chars00)
noncomputable def fragment0090848Value : SourceJson := .obj (fragment0090848Acc00500.reverse)

theorem value_fragment0090848 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 25) (fragment0090848Chars ++ tail) =
      .ok (fragment0090848Value, tail) := by
  have hinput : fragment0090848Chars ++ tail = '{' :: (fragment0090848Field000Chars00 ++ (fragment0090848Field001Chars00 ++ (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0090848Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 25) (fragment0090848Chars ++ tail) =
        SourceJson.value (fuel + 25) ('{' :: (fragment0090848Field000Chars00 ++ (fragment0090848Field001Chars00 ++ (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 25)) hinput
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0090848Field000Chars00 ++ (fragment0090848Field001Chars00 ++ (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail))))))) fragment0090848Acc00000 := by rfl
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0090848Field001Chars00 ++ (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail)))))) fragment0090848Acc00100 := object_fragment0090848_field_000 fuel (fragment0090848Field001Chars00 ++ (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail))))) fragment0090848Acc00200 := object_fragment0090848_field_001 fuel (fragment0090848Field002Chars00 ++ (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail)))) fragment0090848Acc00300 := object_fragment0090848_field_002 fuel (fragment0090848Field003Chars00 ++ (fragment0090848Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0090848Field004Chars00 ++ (tail))) fragment0090848Acc00400 := object_fragment0090848_field_003 fuel (fragment0090848Field004Chars00 ++ (tail))
    _ = .ok (fragment0090848Value, tail) := object_fragment0090848_field_004 fuel (tail)

noncomputable def fragment0093613Acc00000 : List SourceJson := []

noncomputable def fragment0093613Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0093613Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])]) :: (acc))

theorem array_fragment0093613_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0093613Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0093613Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0093613Acc00100 : List SourceJson := fragment0093613Chunk000Push00 fragment0093613Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093613_array_chunk_000"
  err.flush

noncomputable def fragment0093613Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0093613Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0093613_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0093613Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0093613Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0093613Acc00200 : List SourceJson := fragment0093613Chunk001Push00 fragment0093613Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093613_array_chunk_001"
  err.flush

noncomputable def fragment0093613Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0093613Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0093613_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0093613Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0093613Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0093613Acc00300 : List SourceJson := fragment0093613Chunk002Push00 fragment0093613Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093613_array_chunk_002"
  err.flush

noncomputable def fragment0093613Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0093613Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]) :: (acc)

theorem array_fragment0093613_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0093613Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0093613Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0093613Acc00400 : List SourceJson := fragment0093613Chunk003Push00 fragment0093613Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093613_array_chunk_003"
  err.flush

noncomputable def fragment0093613Chars : List Char := '[' :: (fragment0093613Chunk000Chars00 ++ fragment0093613Chunk001Chars00 ++ fragment0093613Chunk002Chars00 ++ fragment0093613Chunk003Chars00)
noncomputable def fragment0093613Value : SourceJson := .arr (fragment0093613Acc00400.reverse)

theorem value_fragment0093613 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0093613Chars ++ tail) =
      .ok (fragment0093613Value, tail) := by
  have hinput : fragment0093613Chars ++ tail = '[' :: (fragment0093613Chunk000Chars00 ++ (fragment0093613Chunk001Chars00 ++ (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0093613Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0093613Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0093613Chunk000Chars00 ++ (fragment0093613Chunk001Chars00 ++ (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0093613Chunk000Chars00 ++ (fragment0093613Chunk001Chars00 ++ (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail)))))) fragment0093613Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0093613Chunk001Chars00 ++ (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail))))) fragment0093613Acc00100 := array_fragment0093613_chunk_000 fuel (fragment0093613Chunk001Chars00 ++ (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail)))) fragment0093613Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail)))) fragment0093613Acc00200 := array_fragment0093613_chunk_001 fuel (fragment0093613Chunk002Chars00 ++ (fragment0093613Chunk003Chars00 ++ (tail))) fragment0093613Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0093613Chunk003Chars00 ++ (tail))) fragment0093613Acc00300 := array_fragment0093613_chunk_002 fuel (fragment0093613Chunk003Chars00 ++ (tail)) fragment0093613Acc00200
    _ = .ok (fragment0093613Value, tail) := array_fragment0093613_chunk_003 fuel (tail) fragment0093613Acc00300

noncomputable def fragment0093393Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0093393Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0093393Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['2', '0'])]
noncomputable def fragment0093393Acc00100 : List (String × SourceJson) := (fragment0093393Field000Key00, fragment0093393Field000Value00) :: fragment0093393Acc00000
noncomputable def fragment0093393Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0093393_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0093393Field000Chars00 ++ tail)) fragment0093393Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0093393Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093393_object_field_000"
  err.flush

noncomputable def fragment0093393Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0093393Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0093393Acc00200 : List (String × SourceJson) := (fragment0093393Field001Key00, fragment0093393Field001Value00) :: fragment0093393Acc00100
noncomputable def fragment0093393Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0093393_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0093393Field001Chars00 ++ tail)) fragment0093393Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0093393Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093393_object_field_001"
  err.flush

noncomputable def fragment0093393Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0093393Field002Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0093393Acc00300 : List (String × SourceJson) := (fragment0093393Field002Key00, fragment0093393Field002Value00) :: fragment0093393Acc00200
noncomputable def fragment0093393Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0093393_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0093393Field002Chars00 ++ tail)) fragment0093393Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0093393Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093393_object_field_002"
  err.flush

noncomputable def fragment0093393Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0093393Field003Value00 : SourceJson := fragment0093613Value
noncomputable def fragment0093393Acc00400 : List (String × SourceJson) := (fragment0093393Field003Key00, fragment0093393Field003Value00) :: fragment0093393Acc00300
noncomputable def fragment0093393Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0093393Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0093393Field003Chars00 : List Char := fragment0093393Field003HeaderChars00 ++ fragment0093613Chars ++ fragment0093393Field003SuffixChars00

noncomputable def fragment0093393Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0093393Field003Key00, result.1) :: fragment0093393Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0093393Field003Key00, result.1) :: fragment0093393Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0093393_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0093393Field003HeaderChars00 ++ rest)) fragment0093393Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0093393Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0093393_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0093393Field003Chars00 ++ tail)) fragment0093393Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0093393Acc00400 := by
  have hinput : fragment0093393Field003Chars00 ++ tail = fragment0093393Field003HeaderChars00 ++ (fragment0093613Chars ++ (fragment0093393Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0093393Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0093393Field003Chars00 ++ tail)) fragment0093393Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0093393Field003HeaderChars00 ++ (fragment0093613Chars ++ (fragment0093393Field003SuffixChars00 ++ tail)))) fragment0093393Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0093393Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0093613Chars ++ (fragment0093393Field003SuffixChars00 ++ tail))).bind
        (fragment0093393Field003AfterValue00 (fuel + 17)) := object_fragment0093393_field_003_header fuel (fragment0093613Chars ++ (fragment0093393Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0093613Value, fragment0093393Field003SuffixChars00 ++ tail)).bind (fragment0093393Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0093393Field003AfterValue00 (fuel + 17)))
        (value_fragment0093613 (fuel + 0) (fragment0093393Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0093393Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093393_object_field_003"
  err.flush

noncomputable def fragment0093393Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0093393Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0093393Acc00500 : List (String × SourceJson) := (fragment0093393Field004Key00, fragment0093393Field004Value00) :: fragment0093393Acc00400
noncomputable def fragment0093393Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0093393_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0093393Field004Chars00 ++ tail)) fragment0093393Acc00400 =
      .ok (.obj (fragment0093393Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0093393_object_field_004"
  err.flush

noncomputable def fragment0093393Chars : List Char := '{' :: (fragment0093393Field000Chars00 ++ fragment0093393Field001Chars00 ++ fragment0093393Field002Chars00 ++ fragment0093393Field003Chars00 ++ fragment0093393Field004Chars00)
noncomputable def fragment0093393Value : SourceJson := .obj (fragment0093393Acc00500.reverse)

theorem value_fragment0093393 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0093393Chars ++ tail) =
      .ok (fragment0093393Value, tail) := by
  have hinput : fragment0093393Chars ++ tail = '{' :: (fragment0093393Field000Chars00 ++ (fragment0093393Field001Chars00 ++ (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0093393Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0093393Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0093393Field000Chars00 ++ (fragment0093393Field001Chars00 ++ (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0093393Field000Chars00 ++ (fragment0093393Field001Chars00 ++ (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail))))))) fragment0093393Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0093393Field001Chars00 ++ (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail)))))) fragment0093393Acc00100 := object_fragment0093393_field_000 fuel (fragment0093393Field001Chars00 ++ (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail))))) fragment0093393Acc00200 := object_fragment0093393_field_001 fuel (fragment0093393Field002Chars00 ++ (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail)))) fragment0093393Acc00300 := object_fragment0093393_field_002 fuel (fragment0093393Field003Chars00 ++ (fragment0093393Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0093393Field004Chars00 ++ (tail))) fragment0093393Acc00400 := object_fragment0093393_field_003 fuel (fragment0093393Field004Chars00 ++ (tail))
    _ = .ok (fragment0093393Value, tail) := object_fragment0093393_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_before_reader"
  err.flush

noncomputable def chunk0008Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0008Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['5'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 71) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 70) (SourceJson.white tail) (chunk0008Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0009_before_reader"
  err.flush

noncomputable def chunk0009LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0009SuffixChars00 : List Char := [',']
noncomputable def chunk0009Chars00 : List Char := chunk0009LeadChars00 ++ fragment0082563Chars ++ chunk0009SuffixChars00
noncomputable def chunk0009Push00 (acc : List SourceJson) : List SourceJson := fragment0082563Value :: acc

noncomputable def chunk0009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 70)
      (SourceJson.white (chunk0009LeadChars00 ++ (fragment0082563Chars ++ rest))) acc =
      (SourceJson.value (fuel + 69) (fragment0082563Chars ++ rest)).bind
        (chunk0009AfterValue00 (fuel + 69) acc) := by rfl

theorem array_chunk0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 70) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 69) (SourceJson.white tail) (chunk0009Push00 acc) := by
  have hinput : chunk0009Chars00 ++ tail = chunk0009LeadChars00 ++ (fragment0082563Chars ++ (chunk0009SuffixChars00 ++ tail)) := by
    simp only [chunk0009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 70) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 70)
          (SourceJson.white (chunk0009LeadChars00 ++ (fragment0082563Chars ++ (chunk0009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 70) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 69) (fragment0082563Chars ++ (chunk0009SuffixChars00 ++ tail))).bind
        (chunk0009AfterValue00 (fuel + 69) acc) := array_chunk0009_head fuel (chunk0009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0082563Value, chunk0009SuffixChars00 ++ tail)).bind
        (chunk0009AfterValue00 (fuel + 69) acc) :=
      congrArg (fun result => result.bind (chunk0009AfterValue00 (fuel + 69) acc))
        (value_fragment0082563 (fuel + 30) (chunk0009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 69) (SourceJson.white tail) (chunk0009Push00 acc) := by rfl

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
noncomputable def chunk0010Chars00 : List Char := chunk0010LeadChars00 ++ fragment0086158Chars ++ chunk0010SuffixChars00
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson := fragment0086158Value :: acc

noncomputable def chunk0010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 69)
      (SourceJson.white (chunk0010LeadChars00 ++ (fragment0086158Chars ++ rest))) acc =
      (SourceJson.value (fuel + 68) (fragment0086158Chars ++ rest)).bind
        (chunk0010AfterValue00 (fuel + 68) acc) := by rfl

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 69) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 68) (SourceJson.white tail) (chunk0010Push00 acc) := by
  have hinput : chunk0010Chars00 ++ tail = chunk0010LeadChars00 ++ (fragment0086158Chars ++ (chunk0010SuffixChars00 ++ tail)) := by
    simp only [chunk0010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 69) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 69)
          (SourceJson.white (chunk0010LeadChars00 ++ (fragment0086158Chars ++ (chunk0010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 69) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 68) (fragment0086158Chars ++ (chunk0010SuffixChars00 ++ tail))).bind
        (chunk0010AfterValue00 (fuel + 68) acc) := array_chunk0010_head fuel (chunk0010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0086158Value, chunk0010SuffixChars00 ++ tail)).bind
        (chunk0010AfterValue00 (fuel + 68) acc) :=
      congrArg (fun result => result.bind (chunk0010AfterValue00 (fuel + 68) acc))
        (value_fragment0086158 (fuel + 39) (chunk0010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 68) (SourceJson.white tail) (chunk0010Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_before_reader"
  err.flush

noncomputable def chunk0011LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0011SuffixChars00 : List Char := [',']
noncomputable def chunk0011Chars00 : List Char := chunk0011LeadChars00 ++ fragment0088194Chars ++ chunk0011SuffixChars00
noncomputable def chunk0011Push00 (acc : List SourceJson) : List SourceJson := fragment0088194Value :: acc

noncomputable def chunk0011AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0011_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 68)
      (SourceJson.white (chunk0011LeadChars00 ++ (fragment0088194Chars ++ rest))) acc =
      (SourceJson.value (fuel + 67) (fragment0088194Chars ++ rest)).bind
        (chunk0011AfterValue00 (fuel + 67) acc) := by rfl

theorem array_chunk0011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 68) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 67) (SourceJson.white tail) (chunk0011Push00 acc) := by
  have hinput : chunk0011Chars00 ++ tail = chunk0011LeadChars00 ++ (fragment0088194Chars ++ (chunk0011SuffixChars00 ++ tail)) := by
    simp only [chunk0011Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 68) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 68)
          (SourceJson.white (chunk0011LeadChars00 ++ (fragment0088194Chars ++ (chunk0011SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 68) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 67) (fragment0088194Chars ++ (chunk0011SuffixChars00 ++ tail))).bind
        (chunk0011AfterValue00 (fuel + 67) acc) := array_chunk0011_head fuel (chunk0011SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0088194Value, chunk0011SuffixChars00 ++ tail)).bind
        (chunk0011AfterValue00 (fuel + 67) acc) :=
      congrArg (fun result => result.bind (chunk0011AfterValue00 (fuel + 67) acc))
        (value_fragment0088194 (fuel + 34) (chunk0011SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 67) (SourceJson.white tail) (chunk0011Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0012SuffixChars00 : List Char := [',']
noncomputable def chunk0012Chars00 : List Char := chunk0012LeadChars00 ++ fragment0090848Chars ++ chunk0012SuffixChars00
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson := fragment0090848Value :: acc

noncomputable def chunk0012AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0012_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 67)
      (SourceJson.white (chunk0012LeadChars00 ++ (fragment0090848Chars ++ rest))) acc =
      (SourceJson.value (fuel + 66) (fragment0090848Chars ++ rest)).bind
        (chunk0012AfterValue00 (fuel + 66) acc) := by rfl

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 67) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 66) (SourceJson.white tail) (chunk0012Push00 acc) := by
  have hinput : chunk0012Chars00 ++ tail = chunk0012LeadChars00 ++ (fragment0090848Chars ++ (chunk0012SuffixChars00 ++ tail)) := by
    simp only [chunk0012Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 67) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 67)
          (SourceJson.white (chunk0012LeadChars00 ++ (fragment0090848Chars ++ (chunk0012SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 67) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 66) (fragment0090848Chars ++ (chunk0012SuffixChars00 ++ tail))).bind
        (chunk0012AfterValue00 (fuel + 66) acc) := array_chunk0012_head fuel (chunk0012SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0090848Value, chunk0012SuffixChars00 ++ tail)).bind
        (chunk0012AfterValue00 (fuel + 66) acc) :=
      congrArg (fun result => result.bind (chunk0012AfterValue00 (fuel + 66) acc))
        (value_fragment0090848 (fuel + 41) (chunk0012SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 66) (SourceJson.white tail) (chunk0012Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 66) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 65) (SourceJson.white tail) (chunk0013Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 65) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 64) (SourceJson.white tail) (chunk0014Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0015SuffixChars00 : List Char := [',']
noncomputable def chunk0015Chars00 : List Char := chunk0015LeadChars00 ++ fragment0093393Chars ++ chunk0015SuffixChars00
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson := fragment0093393Value :: acc

noncomputable def chunk0015AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0015_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 64)
      (SourceJson.white (chunk0015LeadChars00 ++ (fragment0093393Chars ++ rest))) acc =
      (SourceJson.value (fuel + 63) (fragment0093393Chars ++ rest)).bind
        (chunk0015AfterValue00 (fuel + 63) acc) := by rfl

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 64) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 63) (SourceJson.white tail) (chunk0015Push00 acc) := by
  have hinput : chunk0015Chars00 ++ tail = chunk0015LeadChars00 ++ (fragment0093393Chars ++ (chunk0015SuffixChars00 ++ tail)) := by
    simp only [chunk0015Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 64) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 64)
          (SourceJson.white (chunk0015LeadChars00 ++ (fragment0093393Chars ++ (chunk0015SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 64) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 63) (fragment0093393Chars ++ (chunk0015SuffixChars00 ++ tail))).bind
        (chunk0015AfterValue00 (fuel + 63) acc) := array_chunk0015_head fuel (chunk0015SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0093393Value, chunk0015SuffixChars00 ++ tail)).bind
        (chunk0015AfterValue00 (fuel + 63) acc) :=
      congrArg (fun result => result.bind (chunk0015AfterValue00 (fuel + 63) acc))
        (value_fragment0093393 (fuel + 41) (chunk0015SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 63) (SourceJson.white tail) (chunk0015Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0008Chars00 ++ chunk0009Chars00 ++ chunk0010Chars00 ++ chunk0011Chars00 ++ chunk0012Chars00 ++ chunk0013Chars00 ++ chunk0014Chars00 ++ chunk0015Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 71) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 63) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 71) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 71) (SourceJson.white (chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 71) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 70) (SourceJson.white (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))))) (chunk0008Push00 (acc)) := array_chunk0008 fuel (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 69) (SourceJson.white (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (chunk0009Push00 (chunk0008Push00 (acc))) := array_chunk0009 fuel (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0008Push00 (acc))
    _ = SourceJson.array (fuel + 68) (SourceJson.white (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))) := array_chunk0010 fuel (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0009Push00 (chunk0008Push00 (acc)))
    _ = SourceJson.array (fuel + 67) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))) := array_chunk0011 fuel (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))
    _ = SourceJson.array (fuel + 66) (SourceJson.white (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))) := array_chunk0012 fuel (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))
    _ = SourceJson.array (fuel + 65) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))) := array_chunk0013 fuel (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))
    _ = SourceJson.array (fuel + 64) (SourceJson.white (chunk0015Chars00 ++ (tail))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))) := array_chunk0014 fuel (chunk0015Chars00 ++ (tail)) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))
    _ = SourceJson.array (fuel + 63) (SourceJson.white tail) (blockPush acc) := array_chunk0015 fuel (tail) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 81792).take 12735 = blockChars := by rfl

theorem block_original_split : sourceRest 81792 = blockChars ++ sourceRest 94527 := by
  calc
    sourceRest 81792 = (sourceRest 81792).take 12735 ++ (sourceRest 81792).drop 12735 :=
      (List.take_append_drop 12735 (sourceRest 81792)).symm
    _ = blockChars ++ (sourceRest 81792).drop 12735 :=
      congrArg (fun part => part ++ (sourceRest 81792).drop 12735) block_original_prefix
    _ = blockChars ++ sourceRest 94527 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 81792 12735)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 71) (SourceJson.white (sourceRest 81792)) acc =
      SourceJson.array (fuel + 63) (SourceJson.white (sourceRest 94527)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 71) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 94527) acc)

#print axioms array_fragment0083014_chunk_000
#print axioms array_fragment0083014_chunk_001
#print axioms array_fragment0083014_chunk_002
#print axioms array_fragment0083014_chunk_003
#print axioms array_fragment0083014_chunk_004
#print axioms value_fragment0083014
#print axioms object_fragment0082563_field_000
#print axioms object_fragment0082563_field_001
#print axioms object_fragment0082563_field_002
#print axioms object_fragment0082563_field_003_header
#print axioms object_fragment0082563_field_003
#print axioms object_fragment0082563_field_004
#print axioms value_fragment0082563
#print axioms array_fragment0086467_chunk_000
#print axioms array_fragment0086467_chunk_001
#print axioms array_fragment0086467_chunk_002
#print axioms array_fragment0086467_chunk_003
#print axioms array_fragment0086467_chunk_004
#print axioms value_fragment0086467
#print axioms object_fragment0086158_field_000
#print axioms object_fragment0086158_field_001
#print axioms object_fragment0086158_field_002
#print axioms object_fragment0086158_field_003_header
#print axioms object_fragment0086158_field_003
#print axioms object_fragment0086158_field_004
#print axioms value_fragment0086158
#print axioms array_fragment0088581_chunk_000
#print axioms array_fragment0088581_chunk_001
#print axioms array_fragment0088581_chunk_002
#print axioms array_fragment0088581_chunk_003
#print axioms array_fragment0088581_chunk_004
#print axioms value_fragment0088581
#print axioms object_fragment0088194_field_000
#print axioms object_fragment0088194_field_001
#print axioms object_fragment0088194_field_002
#print axioms object_fragment0088194_field_003_header
#print axioms object_fragment0088194_field_003
#print axioms object_fragment0088194_field_004
#print axioms value_fragment0088194
#print axioms array_fragment0091119_chunk_000
#print axioms array_fragment0091119_chunk_001
#print axioms array_fragment0091119_chunk_002
#print axioms array_fragment0091119_chunk_003
#print axioms value_fragment0091119
#print axioms object_fragment0090848_field_000
#print axioms object_fragment0090848_field_001
#print axioms object_fragment0090848_field_002
#print axioms object_fragment0090848_field_003_header
#print axioms object_fragment0090848_field_003
#print axioms object_fragment0090848_field_004
#print axioms value_fragment0090848
#print axioms array_fragment0093613_chunk_000
#print axioms array_fragment0093613_chunk_001
#print axioms array_fragment0093613_chunk_002
#print axioms array_fragment0093613_chunk_003
#print axioms value_fragment0093613
#print axioms object_fragment0093393_field_000
#print axioms object_fragment0093393_field_001
#print axioms object_fragment0093393_field_002
#print axioms object_fragment0093393_field_003_header
#print axioms object_fragment0093393_field_003
#print axioms object_fragment0093393_field_004
#print axioms value_fragment0093393
#print axioms array_chunk0008
#print axioms array_chunk0009_head
#print axioms array_chunk0009
#print axioms array_chunk0010_head
#print axioms array_chunk0010
#print axioms array_chunk0011_head
#print axioms array_chunk0011
#print axioms array_chunk0012_head
#print axioms array_chunk0012
#print axioms array_chunk0013
#print axioms array_chunk0014
#print axioms array_chunk0015_head
#print axioms array_chunk0015
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock001

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
