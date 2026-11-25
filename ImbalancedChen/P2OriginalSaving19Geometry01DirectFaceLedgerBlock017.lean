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

namespace FaceLedgerBlock017

noncomputable def fragment0215626Acc00000 : List SourceJson := []

noncomputable def fragment0215626Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0215626Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0215626_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0215626Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0215626Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0215626Acc00100 : List SourceJson := fragment0215626Chunk000Push00 fragment0215626Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215626_array_chunk_000"
  err.flush

noncomputable def fragment0215626Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0215626Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: (acc))

theorem array_fragment0215626_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0215626Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0215626Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0215626Acc00200 : List SourceJson := fragment0215626Chunk001Push00 fragment0215626Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215626_array_chunk_001"
  err.flush

noncomputable def fragment0215626Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0215626Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: ((.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['3', '3'])]) :: (acc))

theorem array_fragment0215626_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0215626Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0215626Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0215626Acc00300 : List SourceJson := fragment0215626Chunk002Push00 fragment0215626Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215626_array_chunk_002"
  err.flush

noncomputable def fragment0215626Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0215626Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]) :: (acc))

theorem array_fragment0215626_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0215626Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0215626Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0215626Acc00400 : List SourceJson := fragment0215626Chunk003Push00 fragment0215626Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215626_array_chunk_003"
  err.flush

noncomputable def fragment0215626Chars : List Char := '[' :: (fragment0215626Chunk000Chars00 ++ fragment0215626Chunk001Chars00 ++ fragment0215626Chunk002Chars00 ++ fragment0215626Chunk003Chars00)
noncomputable def fragment0215626Value : SourceJson := .arr (fragment0215626Acc00400.reverse)

theorem value_fragment0215626 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0215626Chars ++ tail) =
      .ok (fragment0215626Value, tail) := by
  have hinput : fragment0215626Chars ++ tail = '[' :: (fragment0215626Chunk000Chars00 ++ (fragment0215626Chunk001Chars00 ++ (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0215626Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0215626Chars ++ tail) =
        SourceJson.value (fuel + 20) ('[' :: (fragment0215626Chunk000Chars00 ++ (fragment0215626Chunk001Chars00 ++ (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0215626Chunk000Chars00 ++ (fragment0215626Chunk001Chars00 ++ (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail)))))) fragment0215626Acc00000 := by rfl
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0215626Chunk001Chars00 ++ (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail))))) fragment0215626Acc00100 := array_fragment0215626_chunk_000 fuel (fragment0215626Chunk001Chars00 ++ (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail)))) fragment0215626Acc00000
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail)))) fragment0215626Acc00200 := array_fragment0215626_chunk_001 fuel (fragment0215626Chunk002Chars00 ++ (fragment0215626Chunk003Chars00 ++ (tail))) fragment0215626Acc00100
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0215626Chunk003Chars00 ++ (tail))) fragment0215626Acc00300 := array_fragment0215626_chunk_002 fuel (fragment0215626Chunk003Chars00 ++ (tail)) fragment0215626Acc00200
    _ = .ok (fragment0215626Value, tail) := array_fragment0215626_chunk_003 fuel (tail) fragment0215626Acc00300

noncomputable def fragment0215374Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0215374Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0215374Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3'])]
noncomputable def fragment0215374Acc00100 : List (String × SourceJson) := (fragment0215374Field000Key00, fragment0215374Field000Value00) :: fragment0215374Acc00000
noncomputable def fragment0215374Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0215374_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0215374Field000Chars00 ++ tail)) fragment0215374Acc00000 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0215374Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215374_object_field_000"
  err.flush

noncomputable def fragment0215374Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0215374Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0215374Acc00200 : List (String × SourceJson) := (fragment0215374Field001Key00, fragment0215374Field001Value00) :: fragment0215374Acc00100
noncomputable def fragment0215374Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0215374_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0215374Field001Chars00 ++ tail)) fragment0215374Acc00100 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0215374Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215374_object_field_001"
  err.flush

noncomputable def fragment0215374Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0215374Field002Value00 : SourceJson := .number (String.ofList ['3', '3'])
noncomputable def fragment0215374Acc00300 : List (String × SourceJson) := (fragment0215374Field002Key00, fragment0215374Field002Value00) :: fragment0215374Acc00200
noncomputable def fragment0215374Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '3', ',']

theorem object_fragment0215374_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0215374Field002Chars00 ++ tail)) fragment0215374Acc00200 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0215374Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215374_object_field_002"
  err.flush

noncomputable def fragment0215374Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0215374Field003Value00 : SourceJson := fragment0215626Value
noncomputable def fragment0215374Acc00400 : List (String × SourceJson) := (fragment0215374Field003Key00, fragment0215374Field003Value00) :: fragment0215374Acc00300
noncomputable def fragment0215374Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0215374Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0215374Field003Chars00 : List Char := fragment0215374Field003HeaderChars00 ++ fragment0215626Chars ++ fragment0215374Field003SuffixChars00

noncomputable def fragment0215374Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0215374Field003Key00, result.1) :: fragment0215374Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0215374Field003Key00, result.1) :: fragment0215374Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0215374_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0215374Field003HeaderChars00 ++ rest)) fragment0215374Acc00300 =
      (SourceJson.value (fuel + 20) rest).bind (fragment0215374Field003AfterValue00 (fuel + 20)) := by rfl

theorem object_fragment0215374_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0215374Field003Chars00 ++ tail)) fragment0215374Acc00300 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0215374Acc00400 := by
  have hinput : fragment0215374Field003Chars00 ++ tail = fragment0215374Field003HeaderChars00 ++ (fragment0215626Chars ++ (fragment0215374Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0215374Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0215374Field003Chars00 ++ tail)) fragment0215374Acc00300 =
        SourceJson.object (fuel + 21)
          (SourceJson.white (fragment0215374Field003HeaderChars00 ++ (fragment0215626Chars ++ (fragment0215374Field003SuffixChars00 ++ tail)))) fragment0215374Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 21) (SourceJson.white s) fragment0215374Acc00300) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0215626Chars ++ (fragment0215374Field003SuffixChars00 ++ tail))).bind
        (fragment0215374Field003AfterValue00 (fuel + 20)) := object_fragment0215374_field_003_header fuel (fragment0215626Chars ++ (fragment0215374Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0215626Value, fragment0215374Field003SuffixChars00 ++ tail)).bind (fragment0215374Field003AfterValue00 (fuel + 20)) :=
      congrArg (fun result => result.bind (fragment0215374Field003AfterValue00 (fuel + 20)))
        (value_fragment0215626 (fuel + 0) (fragment0215374Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0215374Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215374_object_field_003"
  err.flush

noncomputable def fragment0215374Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0215374Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0215374Acc00500 : List (String × SourceJson) := (fragment0215374Field004Key00, fragment0215374Field004Value00) :: fragment0215374Acc00400
noncomputable def fragment0215374Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0215374_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0215374Field004Chars00 ++ tail)) fragment0215374Acc00400 =
      .ok (.obj (fragment0215374Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0215374_object_field_004"
  err.flush

noncomputable def fragment0215374Chars : List Char := '{' :: (fragment0215374Field000Chars00 ++ fragment0215374Field001Chars00 ++ fragment0215374Field002Chars00 ++ fragment0215374Field003Chars00 ++ fragment0215374Field004Chars00)
noncomputable def fragment0215374Value : SourceJson := .obj (fragment0215374Acc00500.reverse)

theorem value_fragment0215374 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 25) (fragment0215374Chars ++ tail) =
      .ok (fragment0215374Value, tail) := by
  have hinput : fragment0215374Chars ++ tail = '{' :: (fragment0215374Field000Chars00 ++ (fragment0215374Field001Chars00 ++ (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0215374Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 25) (fragment0215374Chars ++ tail) =
        SourceJson.value (fuel + 25) ('{' :: (fragment0215374Field000Chars00 ++ (fragment0215374Field001Chars00 ++ (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 25)) hinput
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0215374Field000Chars00 ++ (fragment0215374Field001Chars00 ++ (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail))))))) fragment0215374Acc00000 := by rfl
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0215374Field001Chars00 ++ (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail)))))) fragment0215374Acc00100 := object_fragment0215374_field_000 fuel (fragment0215374Field001Chars00 ++ (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail))))) fragment0215374Acc00200 := object_fragment0215374_field_001 fuel (fragment0215374Field002Chars00 ++ (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail)))) fragment0215374Acc00300 := object_fragment0215374_field_002 fuel (fragment0215374Field003Chars00 ++ (fragment0215374Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0215374Field004Chars00 ++ (tail))) fragment0215374Acc00400 := object_fragment0215374_field_003 fuel (fragment0215374Field004Chars00 ++ (tail))
    _ = .ok (fragment0215374Value, tail) := object_fragment0215374_field_004 fuel (tail)

noncomputable def fragment0216928Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0216928Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0216928Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]
noncomputable def fragment0216928Acc00100 : List (String × SourceJson) := (fragment0216928Field000Key00, fragment0216928Field000Value00) :: fragment0216928Acc00000
noncomputable def fragment0216928Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0216928_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0216928Field000Chars00 ++ tail)) fragment0216928Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0216928Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216928_object_field_000"
  err.flush

noncomputable def fragment0216928Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0216928Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0216928Acc00200 : List (String × SourceJson) := (fragment0216928Field001Key00, fragment0216928Field001Value00) :: fragment0216928Acc00100
noncomputable def fragment0216928Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0216928_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0216928Field001Chars00 ++ tail)) fragment0216928Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0216928Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216928_object_field_001"
  err.flush

noncomputable def fragment0216928Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0216928Field002Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0216928Acc00300 : List (String × SourceJson) := (fragment0216928Field002Key00, fragment0216928Field002Value00) :: fragment0216928Acc00200
noncomputable def fragment0216928Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0216928_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0216928Field002Chars00 ++ tail)) fragment0216928Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0216928Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216928_object_field_002"
  err.flush

noncomputable def fragment0216928Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0216928Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]]
noncomputable def fragment0216928Acc00400 : List (String × SourceJson) := (fragment0216928Field003Key00, fragment0216928Field003Value00) :: fragment0216928Acc00300
noncomputable def fragment0216928Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0216928_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0216928Field003Chars00 ++ tail)) fragment0216928Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0216928Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216928_object_field_003"
  err.flush

noncomputable def fragment0216928Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0216928Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0216928Acc00500 : List (String × SourceJson) := (fragment0216928Field004Key00, fragment0216928Field004Value00) :: fragment0216928Acc00400
noncomputable def fragment0216928Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0216928_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0216928Field004Chars00 ++ tail)) fragment0216928Acc00400 =
      .ok (.obj (fragment0216928Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0216928_object_field_004"
  err.flush

noncomputable def fragment0216928Chars : List Char := '{' :: (fragment0216928Field000Chars00 ++ fragment0216928Field001Chars00 ++ fragment0216928Field002Chars00 ++ fragment0216928Field003Chars00 ++ fragment0216928Field004Chars00)
noncomputable def fragment0216928Value : SourceJson := .obj (fragment0216928Acc00500.reverse)

theorem value_fragment0216928 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0216928Chars ++ tail) =
      .ok (fragment0216928Value, tail) := by
  have hinput : fragment0216928Chars ++ tail = '{' :: (fragment0216928Field000Chars00 ++ (fragment0216928Field001Chars00 ++ (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0216928Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0216928Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0216928Field000Chars00 ++ (fragment0216928Field001Chars00 ++ (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0216928Field000Chars00 ++ (fragment0216928Field001Chars00 ++ (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail))))))) fragment0216928Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0216928Field001Chars00 ++ (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail)))))) fragment0216928Acc00100 := object_fragment0216928_field_000 fuel (fragment0216928Field001Chars00 ++ (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail))))) fragment0216928Acc00200 := object_fragment0216928_field_001 fuel (fragment0216928Field002Chars00 ++ (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail)))) fragment0216928Acc00300 := object_fragment0216928_field_002 fuel (fragment0216928Field003Chars00 ++ (fragment0216928Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0216928Field004Chars00 ++ (tail))) fragment0216928Acc00400 := object_fragment0216928_field_003 fuel (fragment0216928Field004Chars00 ++ (tail))
    _ = .ok (fragment0216928Value, tail) := object_fragment0216928_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_before_reader"
  err.flush

noncomputable def chunk0050LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0050SuffixChars00 : List Char := [',']
noncomputable def chunk0050Chars00 : List Char := chunk0050LeadChars00 ++ fragment0215374Chars ++ chunk0050SuffixChars00
noncomputable def chunk0050Push00 (acc : List SourceJson) : List SourceJson := fragment0215374Value :: acc

noncomputable def chunk0050AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0050_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38)
      (SourceJson.white (chunk0050LeadChars00 ++ (fragment0215374Chars ++ rest))) acc =
      (SourceJson.value (fuel + 37) (fragment0215374Chars ++ rest)).bind
        (chunk0050AfterValue00 (fuel + 37) acc) := by rfl

theorem array_chunk0050 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 37) (SourceJson.white tail) (chunk0050Push00 acc) := by
  have hinput : chunk0050Chars00 ++ tail = chunk0050LeadChars00 ++ (fragment0215374Chars ++ (chunk0050SuffixChars00 ++ tail)) := by
    simp only [chunk0050Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 38) (SourceJson.white (chunk0050Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 38)
          (SourceJson.white (chunk0050LeadChars00 ++ (fragment0215374Chars ++ (chunk0050SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 38) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 37) (fragment0215374Chars ++ (chunk0050SuffixChars00 ++ tail))).bind
        (chunk0050AfterValue00 (fuel + 37) acc) := array_chunk0050_head fuel (chunk0050SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0215374Value, chunk0050SuffixChars00 ++ tail)).bind
        (chunk0050AfterValue00 (fuel + 37) acc) :=
      congrArg (fun result => result.bind (chunk0050AfterValue00 (fuel + 37) acc))
        (value_fragment0215374 (fuel + 12) (chunk0050SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 37) (SourceJson.white tail) (chunk0050Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0050_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_before_reader"
  err.flush

noncomputable def chunk0051LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0051SuffixChars00 : List Char := [',']
noncomputable def chunk0051Chars00 : List Char := chunk0051LeadChars00 ++ fragment0216928Chars ++ chunk0051SuffixChars00
noncomputable def chunk0051Push00 (acc : List SourceJson) : List SourceJson := fragment0216928Value :: acc

noncomputable def chunk0051AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0051_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37)
      (SourceJson.white (chunk0051LeadChars00 ++ (fragment0216928Chars ++ rest))) acc =
      (SourceJson.value (fuel + 36) (fragment0216928Chars ++ rest)).bind
        (chunk0051AfterValue00 (fuel + 36) acc) := by rfl

theorem array_chunk0051 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail) (chunk0051Push00 acc) := by
  have hinput : chunk0051Chars00 ++ tail = chunk0051LeadChars00 ++ (fragment0216928Chars ++ (chunk0051SuffixChars00 ++ tail)) := by
    simp only [chunk0051Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 37) (SourceJson.white (chunk0051Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 37)
          (SourceJson.white (chunk0051LeadChars00 ++ (fragment0216928Chars ++ (chunk0051SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 37) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 36) (fragment0216928Chars ++ (chunk0051SuffixChars00 ++ tail))).bind
        (chunk0051AfterValue00 (fuel + 36) acc) := array_chunk0051_head fuel (chunk0051SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0216928Value, chunk0051SuffixChars00 ++ tail)).bind
        (chunk0051AfterValue00 (fuel + 36) acc) :=
      congrArg (fun result => result.bind (chunk0051AfterValue00 (fuel + 36) acc))
        (value_fragment0216928 (fuel + 17) (chunk0051SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 36) (SourceJson.white tail) (chunk0051Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0051_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_before_reader"
  err.flush

noncomputable def chunk0052Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0052Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '8'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '8'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0052 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (chunk0052Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 35) (SourceJson.white tail) (chunk0052Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0052_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_before_reader"
  err.flush

noncomputable def chunk0053Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0053Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '9'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0053 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 35) (SourceJson.white (chunk0053Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 34) (SourceJson.white tail) (chunk0053Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0053_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_before_reader"
  err.flush

noncomputable def chunk0054Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0054Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2', '2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '2'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0054 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 34) (SourceJson.white (chunk0054Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 33) (SourceJson.white tail) (chunk0054Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0054_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_before_reader"
  err.flush

noncomputable def chunk0055Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0055Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1', '6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0055 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (chunk0055Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (chunk0055Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0055_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0050Chars00 ++ chunk0051Chars00 ++ chunk0052Chars00 ++ chunk0053Chars00 ++ chunk0054Chars00 ++ chunk0055Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0055Push00 (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 38) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 38) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 38) (SourceJson.white (chunk0050Chars00 ++ (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 38) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 37) (SourceJson.white (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))))) (chunk0050Push00 (acc)) := array_chunk0050 fuel (chunk0051Chars00 ++ (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) (acc)
    _ = SourceJson.array (fuel + 36) (SourceJson.white (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))))) (chunk0051Push00 (chunk0050Push00 (acc))) := array_chunk0051 fuel (chunk0052Chars00 ++ (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))) (chunk0050Push00 (acc))
    _ = SourceJson.array (fuel + 35) (SourceJson.white (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))))) (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc)))) := array_chunk0052 fuel (chunk0053Chars00 ++ (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))) (chunk0051Push00 (chunk0050Push00 (acc)))
    _ = SourceJson.array (fuel + 34) (SourceJson.white (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail)))) (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc))))) := array_chunk0053 fuel (chunk0054Chars00 ++ (chunk0055Chars00 ++ (tail))) (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc))))
    _ = SourceJson.array (fuel + 33) (SourceJson.white (chunk0055Chars00 ++ (tail))) (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc)))))) := array_chunk0054 fuel (chunk0055Chars00 ++ (tail)) (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc)))))
    _ = SourceJson.array (fuel + 32) (SourceJson.white tail) (blockPush acc) := array_chunk0055 fuel (tail) (chunk0054Push00 (chunk0053Push00 (chunk0052Push00 (chunk0051Push00 (chunk0050Push00 (acc))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 215368).take 4070 = blockChars := by rfl

theorem block_original_split : sourceRest 215368 = blockChars ++ sourceRest 219438 := by
  calc
    sourceRest 215368 = (sourceRest 215368).take 4070 ++ (sourceRest 215368).drop 4070 :=
      (List.take_append_drop 4070 (sourceRest 215368)).symm
    _ = blockChars ++ (sourceRest 215368).drop 4070 :=
      congrArg (fun part => part ++ (sourceRest 215368).drop 4070) block_original_prefix
    _ = blockChars ++ sourceRest 219438 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 215368 4070)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 38) (SourceJson.white (sourceRest 215368)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white (sourceRest 219438)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 38) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 219438) acc)

#print axioms array_fragment0215626_chunk_000
#print axioms array_fragment0215626_chunk_001
#print axioms array_fragment0215626_chunk_002
#print axioms array_fragment0215626_chunk_003
#print axioms value_fragment0215626
#print axioms object_fragment0215374_field_000
#print axioms object_fragment0215374_field_001
#print axioms object_fragment0215374_field_002
#print axioms object_fragment0215374_field_003_header
#print axioms object_fragment0215374_field_003
#print axioms object_fragment0215374_field_004
#print axioms value_fragment0215374
#print axioms object_fragment0216928_field_000
#print axioms object_fragment0216928_field_001
#print axioms object_fragment0216928_field_002
#print axioms object_fragment0216928_field_003
#print axioms object_fragment0216928_field_004
#print axioms value_fragment0216928
#print axioms array_chunk0050_head
#print axioms array_chunk0050
#print axioms array_chunk0051_head
#print axioms array_chunk0051
#print axioms array_chunk0052
#print axioms array_chunk0053
#print axioms array_chunk0054
#print axioms array_chunk0055
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock017

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
