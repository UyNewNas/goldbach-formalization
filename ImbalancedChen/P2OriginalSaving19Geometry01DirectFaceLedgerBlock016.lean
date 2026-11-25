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

namespace FaceLedgerBlock016

noncomputable def fragment0212080Acc00000 : List SourceJson := []

noncomputable def fragment0212080Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0212080Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0212080_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0212080Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0212080Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0212080Acc00100 : List SourceJson := fragment0212080Chunk000Push00 fragment0212080Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212080_array_chunk_000"
  err.flush

noncomputable def fragment0212080Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0212080Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0212080_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0212080Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0212080Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0212080Acc00200 : List SourceJson := fragment0212080Chunk001Push00 fragment0212080Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212080_array_chunk_001"
  err.flush

noncomputable def fragment0212080Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0212080Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0212080_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0212080Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0212080Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0212080Acc00300 : List SourceJson := fragment0212080Chunk002Push00 fragment0212080Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212080_array_chunk_002"
  err.flush

noncomputable def fragment0212080Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0212080Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])]) :: ((.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0212080_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0212080Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0212080Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0212080Acc00400 : List SourceJson := fragment0212080Chunk003Push00 fragment0212080Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0212080_array_chunk_003"
  err.flush

noncomputable def fragment0212080Chars : List Char := '[' :: (fragment0212080Chunk000Chars00 ++ fragment0212080Chunk001Chars00 ++ fragment0212080Chunk002Chars00 ++ fragment0212080Chunk003Chars00)
noncomputable def fragment0212080Value : SourceJson := .arr (fragment0212080Acc00400.reverse)

theorem value_fragment0212080 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0212080Chars ++ tail) =
      .ok (fragment0212080Value, tail) := by
  have hinput : fragment0212080Chars ++ tail = '[' :: (fragment0212080Chunk000Chars00 ++ (fragment0212080Chunk001Chars00 ++ (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0212080Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0212080Chars ++ tail) =
        SourceJson.value (fuel + 20) ('[' :: (fragment0212080Chunk000Chars00 ++ (fragment0212080Chunk001Chars00 ++ (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0212080Chunk000Chars00 ++ (fragment0212080Chunk001Chars00 ++ (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail)))))) fragment0212080Acc00000 := by rfl
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0212080Chunk001Chars00 ++ (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail))))) fragment0212080Acc00100 := array_fragment0212080_chunk_000 fuel (fragment0212080Chunk001Chars00 ++ (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail)))) fragment0212080Acc00000
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail)))) fragment0212080Acc00200 := array_fragment0212080_chunk_001 fuel (fragment0212080Chunk002Chars00 ++ (fragment0212080Chunk003Chars00 ++ (tail))) fragment0212080Acc00100
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0212080Chunk003Chars00 ++ (tail))) fragment0212080Acc00300 := array_fragment0212080_chunk_002 fuel (fragment0212080Chunk003Chars00 ++ (tail)) fragment0212080Acc00200
    _ = .ok (fragment0212080Value, tail) := array_fragment0212080_chunk_003 fuel (tail) fragment0212080Acc00300

noncomputable def fragment0211828Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0211828Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0211828Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]
noncomputable def fragment0211828Acc00100 : List (String × SourceJson) := (fragment0211828Field000Key00, fragment0211828Field000Value00) :: fragment0211828Acc00000
noncomputable def fragment0211828Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0211828_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0211828Field000Chars00 ++ tail)) fragment0211828Acc00000 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0211828Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0211828_object_field_000"
  err.flush

noncomputable def fragment0211828Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0211828Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0211828Acc00200 : List (String × SourceJson) := (fragment0211828Field001Key00, fragment0211828Field001Value00) :: fragment0211828Acc00100
noncomputable def fragment0211828Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0211828_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0211828Field001Chars00 ++ tail)) fragment0211828Acc00100 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0211828Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0211828_object_field_001"
  err.flush

noncomputable def fragment0211828Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0211828Field002Value00 : SourceJson := .number (String.ofList ['3', '1'])
noncomputable def fragment0211828Acc00300 : List (String × SourceJson) := (fragment0211828Field002Key00, fragment0211828Field002Value00) :: fragment0211828Acc00200
noncomputable def fragment0211828Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '1', ',']

theorem object_fragment0211828_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0211828Field002Chars00 ++ tail)) fragment0211828Acc00200 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0211828Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0211828_object_field_002"
  err.flush

noncomputable def fragment0211828Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0211828Field003Value00 : SourceJson := fragment0212080Value
noncomputable def fragment0211828Acc00400 : List (String × SourceJson) := (fragment0211828Field003Key00, fragment0211828Field003Value00) :: fragment0211828Acc00300
noncomputable def fragment0211828Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0211828Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0211828Field003Chars00 : List Char := fragment0211828Field003HeaderChars00 ++ fragment0212080Chars ++ fragment0211828Field003SuffixChars00

noncomputable def fragment0211828Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0211828Field003Key00, result.1) :: fragment0211828Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0211828Field003Key00, result.1) :: fragment0211828Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0211828_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0211828Field003HeaderChars00 ++ rest)) fragment0211828Acc00300 =
      (SourceJson.value (fuel + 20) rest).bind (fragment0211828Field003AfterValue00 (fuel + 20)) := by rfl

theorem object_fragment0211828_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0211828Field003Chars00 ++ tail)) fragment0211828Acc00300 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0211828Acc00400 := by
  have hinput : fragment0211828Field003Chars00 ++ tail = fragment0211828Field003HeaderChars00 ++ (fragment0212080Chars ++ (fragment0211828Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0211828Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0211828Field003Chars00 ++ tail)) fragment0211828Acc00300 =
        SourceJson.object (fuel + 21)
          (SourceJson.white (fragment0211828Field003HeaderChars00 ++ (fragment0212080Chars ++ (fragment0211828Field003SuffixChars00 ++ tail)))) fragment0211828Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 21) (SourceJson.white s) fragment0211828Acc00300) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0212080Chars ++ (fragment0211828Field003SuffixChars00 ++ tail))).bind
        (fragment0211828Field003AfterValue00 (fuel + 20)) := object_fragment0211828_field_003_header fuel (fragment0212080Chars ++ (fragment0211828Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0212080Value, fragment0211828Field003SuffixChars00 ++ tail)).bind (fragment0211828Field003AfterValue00 (fuel + 20)) :=
      congrArg (fun result => result.bind (fragment0211828Field003AfterValue00 (fuel + 20)))
        (value_fragment0212080 (fuel + 0) (fragment0211828Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0211828Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0211828_object_field_003"
  err.flush

noncomputable def fragment0211828Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0211828Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0211828Acc00500 : List (String × SourceJson) := (fragment0211828Field004Key00, fragment0211828Field004Value00) :: fragment0211828Acc00400
noncomputable def fragment0211828Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0211828_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0211828Field004Chars00 ++ tail)) fragment0211828Acc00400 =
      .ok (.obj (fragment0211828Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0211828_object_field_004"
  err.flush

noncomputable def fragment0211828Chars : List Char := '{' :: (fragment0211828Field000Chars00 ++ fragment0211828Field001Chars00 ++ fragment0211828Field002Chars00 ++ fragment0211828Field003Chars00 ++ fragment0211828Field004Chars00)
noncomputable def fragment0211828Value : SourceJson := .obj (fragment0211828Acc00500.reverse)

theorem value_fragment0211828 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 25) (fragment0211828Chars ++ tail) =
      .ok (fragment0211828Value, tail) := by
  have hinput : fragment0211828Chars ++ tail = '{' :: (fragment0211828Field000Chars00 ++ (fragment0211828Field001Chars00 ++ (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0211828Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 25) (fragment0211828Chars ++ tail) =
        SourceJson.value (fuel + 25) ('{' :: (fragment0211828Field000Chars00 ++ (fragment0211828Field001Chars00 ++ (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 25)) hinput
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0211828Field000Chars00 ++ (fragment0211828Field001Chars00 ++ (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail))))))) fragment0211828Acc00000 := by rfl
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0211828Field001Chars00 ++ (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail)))))) fragment0211828Acc00100 := object_fragment0211828_field_000 fuel (fragment0211828Field001Chars00 ++ (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail))))) fragment0211828Acc00200 := object_fragment0211828_field_001 fuel (fragment0211828Field002Chars00 ++ (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail)))) fragment0211828Acc00300 := object_fragment0211828_field_002 fuel (fragment0211828Field003Chars00 ++ (fragment0211828Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0211828Field004Chars00 ++ (tail))) fragment0211828Acc00400 := object_fragment0211828_field_003 fuel (fragment0211828Field004Chars00 ++ (tail))
    _ = .ok (fragment0211828Value, tail) := object_fragment0211828_field_004 fuel (tail)

noncomputable def fragment0213660Acc00000 : List SourceJson := []

noncomputable def fragment0213660Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0213660Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: (acc))

theorem array_fragment0213660_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (fragment0213660Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (fragment0213660Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0213660Acc00100 : List SourceJson := fragment0213660Chunk000Push00 fragment0213660Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213660_array_chunk_000"
  err.flush

noncomputable def fragment0213660Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0213660Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: (acc))

theorem array_fragment0213660_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0213660Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0213660Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0213660Acc00200 : List SourceJson := fragment0213660Chunk001Push00 fragment0213660Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213660_array_chunk_001"
  err.flush

noncomputable def fragment0213660Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0213660Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: (acc))

theorem array_fragment0213660_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0213660Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 16) (SourceJson.white tail) (fragment0213660Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0213660Acc00300 : List SourceJson := fragment0213660Chunk002Push00 fragment0213660Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213660_array_chunk_002"
  err.flush

noncomputable def fragment0213660Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0213660Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: (acc))

theorem array_fragment0213660_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0213660Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0213660Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0213660Acc00400 : List SourceJson := fragment0213660Chunk003Push00 fragment0213660Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213660_array_chunk_003"
  err.flush

noncomputable def fragment0213660Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0213660Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0213660_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0213660Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0213660Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0213660Acc00500 : List SourceJson := fragment0213660Chunk004Push00 fragment0213660Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213660_array_chunk_004"
  err.flush

noncomputable def fragment0213660Chars : List Char := '[' :: (fragment0213660Chunk000Chars00 ++ fragment0213660Chunk001Chars00 ++ fragment0213660Chunk002Chars00 ++ fragment0213660Chunk003Chars00 ++ fragment0213660Chunk004Chars00)
noncomputable def fragment0213660Value : SourceJson := .arr (fragment0213660Acc00500.reverse)

theorem value_fragment0213660 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0213660Chars ++ tail) =
      .ok (fragment0213660Value, tail) := by
  have hinput : fragment0213660Chars ++ tail = '[' :: (fragment0213660Chunk000Chars00 ++ (fragment0213660Chunk001Chars00 ++ (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0213660Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0213660Chars ++ tail) =
        SourceJson.value (fuel + 23) ('[' :: (fragment0213660Chunk000Chars00 ++ (fragment0213660Chunk001Chars00 ++ (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.array (fuel + 22) (SourceJson.white (fragment0213660Chunk000Chars00 ++ (fragment0213660Chunk001Chars00 ++ (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail))))))) fragment0213660Acc00000 := by rfl
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0213660Chunk001Chars00 ++ (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail)))))) fragment0213660Acc00100 := array_fragment0213660_chunk_000 fuel (fragment0213660Chunk001Chars00 ++ (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail))))) fragment0213660Acc00000
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail))))) fragment0213660Acc00200 := array_fragment0213660_chunk_001 fuel (fragment0213660Chunk002Chars00 ++ (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail)))) fragment0213660Acc00100
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail)))) fragment0213660Acc00300 := array_fragment0213660_chunk_002 fuel (fragment0213660Chunk003Chars00 ++ (fragment0213660Chunk004Chars00 ++ (tail))) fragment0213660Acc00200
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0213660Chunk004Chars00 ++ (tail))) fragment0213660Acc00400 := array_fragment0213660_chunk_003 fuel (fragment0213660Chunk004Chars00 ++ (tail)) fragment0213660Acc00300
    _ = .ok (fragment0213660Value, tail) := array_fragment0213660_chunk_004 fuel (tail) fragment0213660Acc00400

noncomputable def fragment0213382Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0213382Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0213382Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]
noncomputable def fragment0213382Acc00100 : List (String × SourceJson) := (fragment0213382Field000Key00, fragment0213382Field000Value00) :: fragment0213382Acc00000
noncomputable def fragment0213382Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0213382_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0213382Field000Chars00 ++ tail)) fragment0213382Acc00000 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0213382Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213382_object_field_000"
  err.flush

noncomputable def fragment0213382Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0213382Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0213382Acc00200 : List (String × SourceJson) := (fragment0213382Field001Key00, fragment0213382Field001Value00) :: fragment0213382Acc00100
noncomputable def fragment0213382Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0213382_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0213382Field001Chars00 ++ tail)) fragment0213382Acc00100 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0213382Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213382_object_field_001"
  err.flush

noncomputable def fragment0213382Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0213382Field002Value00 : SourceJson := .number (String.ofList ['3', '3'])
noncomputable def fragment0213382Acc00300 : List (String × SourceJson) := (fragment0213382Field002Key00, fragment0213382Field002Value00) :: fragment0213382Acc00200
noncomputable def fragment0213382Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '3', ',']

theorem object_fragment0213382_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0213382Field002Chars00 ++ tail)) fragment0213382Acc00200 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0213382Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213382_object_field_002"
  err.flush

noncomputable def fragment0213382Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0213382Field003Value00 : SourceJson := fragment0213660Value
noncomputable def fragment0213382Acc00400 : List (String × SourceJson) := (fragment0213382Field003Key00, fragment0213382Field003Value00) :: fragment0213382Acc00300
noncomputable def fragment0213382Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0213382Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0213382Field003Chars00 : List Char := fragment0213382Field003HeaderChars00 ++ fragment0213660Chars ++ fragment0213382Field003SuffixChars00

noncomputable def fragment0213382Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0213382Field003Key00, result.1) :: fragment0213382Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0213382Field003Key00, result.1) :: fragment0213382Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0213382_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0213382Field003HeaderChars00 ++ rest)) fragment0213382Acc00300 =
      (SourceJson.value (fuel + 23) rest).bind (fragment0213382Field003AfterValue00 (fuel + 23)) := by rfl

theorem object_fragment0213382_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0213382Field003Chars00 ++ tail)) fragment0213382Acc00300 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0213382Acc00400 := by
  have hinput : fragment0213382Field003Chars00 ++ tail = fragment0213382Field003HeaderChars00 ++ (fragment0213660Chars ++ (fragment0213382Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0213382Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0213382Field003Chars00 ++ tail)) fragment0213382Acc00300 =
        SourceJson.object (fuel + 24)
          (SourceJson.white (fragment0213382Field003HeaderChars00 ++ (fragment0213660Chars ++ (fragment0213382Field003SuffixChars00 ++ tail)))) fragment0213382Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 24) (SourceJson.white s) fragment0213382Acc00300) hinput
    _ = (SourceJson.value (fuel + 23) (fragment0213660Chars ++ (fragment0213382Field003SuffixChars00 ++ tail))).bind
        (fragment0213382Field003AfterValue00 (fuel + 23)) := object_fragment0213382_field_003_header fuel (fragment0213660Chars ++ (fragment0213382Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0213660Value, fragment0213382Field003SuffixChars00 ++ tail)).bind (fragment0213382Field003AfterValue00 (fuel + 23)) :=
      congrArg (fun result => result.bind (fragment0213382Field003AfterValue00 (fuel + 23)))
        (value_fragment0213660 (fuel + 0) (fragment0213382Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0213382Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213382_object_field_003"
  err.flush

noncomputable def fragment0213382Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0213382Field004Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0213382Acc00500 : List (String × SourceJson) := (fragment0213382Field004Key00, fragment0213382Field004Value00) :: fragment0213382Acc00400
noncomputable def fragment0213382Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0213382_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0213382Field004Chars00 ++ tail)) fragment0213382Acc00400 =
      .ok (.obj (fragment0213382Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0213382_object_field_004"
  err.flush

noncomputable def fragment0213382Chars : List Char := '{' :: (fragment0213382Field000Chars00 ++ fragment0213382Field001Chars00 ++ fragment0213382Field002Chars00 ++ fragment0213382Field003Chars00 ++ fragment0213382Field004Chars00)
noncomputable def fragment0213382Value : SourceJson := .obj (fragment0213382Acc00500.reverse)

theorem value_fragment0213382 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 28) (fragment0213382Chars ++ tail) =
      .ok (fragment0213382Value, tail) := by
  have hinput : fragment0213382Chars ++ tail = '{' :: (fragment0213382Field000Chars00 ++ (fragment0213382Field001Chars00 ++ (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0213382Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 28) (fragment0213382Chars ++ tail) =
        SourceJson.value (fuel + 28) ('{' :: (fragment0213382Field000Chars00 ++ (fragment0213382Field001Chars00 ++ (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 28)) hinput
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0213382Field000Chars00 ++ (fragment0213382Field001Chars00 ++ (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail))))))) fragment0213382Acc00000 := by rfl
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0213382Field001Chars00 ++ (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail)))))) fragment0213382Acc00100 := object_fragment0213382_field_000 fuel (fragment0213382Field001Chars00 ++ (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail))))) fragment0213382Acc00200 := object_fragment0213382_field_001 fuel (fragment0213382Field002Chars00 ++ (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail)))) fragment0213382Acc00300 := object_fragment0213382_field_002 fuel (fragment0213382Field003Chars00 ++ (fragment0213382Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0213382Field004Chars00 ++ (tail))) fragment0213382Acc00400 := object_fragment0213382_field_003 fuel (fragment0213382Field004Chars00 ++ (tail))
    _ = .ok (fragment0213382Value, tail) := object_fragment0213382_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_before_reader"
  err.flush

noncomputable def chunk0048LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0048SuffixChars00 : List Char := [',']
noncomputable def chunk0048Chars00 : List Char := chunk0048LeadChars00 ++ fragment0211828Chars ++ chunk0048SuffixChars00
noncomputable def chunk0048Push00 (acc : List SourceJson) : List SourceJson := fragment0211828Value :: acc

noncomputable def chunk0048AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0048_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40)
      (SourceJson.white (chunk0048LeadChars00 ++ (fragment0211828Chars ++ rest))) acc =
      (SourceJson.value (fuel + 39) (fragment0211828Chars ++ rest)).bind
        (chunk0048AfterValue00 (fuel + 39) acc) := by rfl

theorem array_chunk0048 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 39) (SourceJson.white tail) (chunk0048Push00 acc) := by
  have hinput : chunk0048Chars00 ++ tail = chunk0048LeadChars00 ++ (fragment0211828Chars ++ (chunk0048SuffixChars00 ++ tail)) := by
    simp only [chunk0048Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 40) (SourceJson.white (chunk0048Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 40)
          (SourceJson.white (chunk0048LeadChars00 ++ (fragment0211828Chars ++ (chunk0048SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 40) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 39) (fragment0211828Chars ++ (chunk0048SuffixChars00 ++ tail))).bind
        (chunk0048AfterValue00 (fuel + 39) acc) := array_chunk0048_head fuel (chunk0048SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0211828Value, chunk0048SuffixChars00 ++ tail)).bind
        (chunk0048AfterValue00 (fuel + 39) acc) :=
      congrArg (fun result => result.bind (chunk0048AfterValue00 (fuel + 39) acc))
        (value_fragment0211828 (fuel + 14) (chunk0048SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 39) (SourceJson.white tail) (chunk0048Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0048_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_before_reader"
  err.flush

noncomputable def chunk0049LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0049SuffixChars00 : List Char := [',']
noncomputable def chunk0049Chars00 : List Char := chunk0049LeadChars00 ++ fragment0213382Chars ++ chunk0049SuffixChars00
noncomputable def chunk0049Push00 (acc : List SourceJson) : List SourceJson := fragment0213382Value :: acc

noncomputable def chunk0049AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0049_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39)
      (SourceJson.white (chunk0049LeadChars00 ++ (fragment0213382Chars ++ rest))) acc =
      (SourceJson.value (fuel + 38) (fragment0213382Chars ++ rest)).bind
        (chunk0049AfterValue00 (fuel + 38) acc) := by rfl

theorem array_chunk0049 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (chunk0049Push00 acc) := by
  have hinput : chunk0049Chars00 ++ tail = chunk0049LeadChars00 ++ (fragment0213382Chars ++ (chunk0049SuffixChars00 ++ tail)) := by
    simp only [chunk0049Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 39) (SourceJson.white (chunk0049Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 39)
          (SourceJson.white (chunk0049LeadChars00 ++ (fragment0213382Chars ++ (chunk0049SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 39) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 38) (fragment0213382Chars ++ (chunk0049SuffixChars00 ++ tail))).bind
        (chunk0049AfterValue00 (fuel + 38) acc) := array_chunk0049_head fuel (chunk0049SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0213382Value, chunk0049SuffixChars00 ++ tail)).bind
        (chunk0049AfterValue00 (fuel + 38) acc) :=
      congrArg (fun result => result.bind (chunk0049AfterValue00 (fuel + 38) acc))
        (value_fragment0213382 (fuel + 10) (chunk0049SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 38) (SourceJson.white tail) (chunk0049Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0049_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0048Chars00 ++ chunk0049Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0049Push00 (chunk0048Push00 (acc))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 40) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0048Chars00 ++ (chunk0049Chars00 ++ (tail)) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 40) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 40) (SourceJson.white (chunk0048Chars00 ++ (chunk0049Chars00 ++ (tail)))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 40) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 39) (SourceJson.white (chunk0049Chars00 ++ (tail))) (chunk0048Push00 (acc)) := array_chunk0048 fuel (chunk0049Chars00 ++ (tail)) (acc)
    _ = SourceJson.array (fuel + 38) (SourceJson.white tail) (blockPush acc) := array_chunk0049 fuel (tail) (chunk0048Push00 (acc))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 211822).take 3546 = blockChars := by rfl

theorem block_original_split : sourceRest 211822 = blockChars ++ sourceRest 215368 := by
  calc
    sourceRest 211822 = (sourceRest 211822).take 3546 ++ (sourceRest 211822).drop 3546 :=
      (List.take_append_drop 3546 (sourceRest 211822)).symm
    _ = blockChars ++ (sourceRest 211822).drop 3546 :=
      congrArg (fun part => part ++ (sourceRest 211822).drop 3546) block_original_prefix
    _ = blockChars ++ sourceRest 215368 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 211822 3546)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 40) (SourceJson.white (sourceRest 211822)) acc =
      SourceJson.array (fuel + 38) (SourceJson.white (sourceRest 215368)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 40) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 215368) acc)

#print axioms array_fragment0212080_chunk_000
#print axioms array_fragment0212080_chunk_001
#print axioms array_fragment0212080_chunk_002
#print axioms array_fragment0212080_chunk_003
#print axioms value_fragment0212080
#print axioms object_fragment0211828_field_000
#print axioms object_fragment0211828_field_001
#print axioms object_fragment0211828_field_002
#print axioms object_fragment0211828_field_003_header
#print axioms object_fragment0211828_field_003
#print axioms object_fragment0211828_field_004
#print axioms value_fragment0211828
#print axioms array_fragment0213660_chunk_000
#print axioms array_fragment0213660_chunk_001
#print axioms array_fragment0213660_chunk_002
#print axioms array_fragment0213660_chunk_003
#print axioms array_fragment0213660_chunk_004
#print axioms value_fragment0213660
#print axioms object_fragment0213382_field_000
#print axioms object_fragment0213382_field_001
#print axioms object_fragment0213382_field_002
#print axioms object_fragment0213382_field_003_header
#print axioms object_fragment0213382_field_003
#print axioms object_fragment0213382_field_004
#print axioms value_fragment0213382
#print axioms array_chunk0048_head
#print axioms array_chunk0048
#print axioms array_chunk0049_head
#print axioms array_chunk0049
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock016

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
