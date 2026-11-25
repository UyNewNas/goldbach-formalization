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

namespace FaceLedgerBlock009

noncomputable def fragment0189806Acc00000 : List SourceJson := []

noncomputable def fragment0189806Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0189806Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment0189806_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0189806Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0189806Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0189806Acc00100 : List SourceJson := fragment0189806Chunk000Push00 fragment0189806Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189806_array_chunk_000"
  err.flush

noncomputable def fragment0189806Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0189806Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]) :: (acc))

theorem array_fragment0189806_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0189806Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0189806Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0189806Acc00200 : List SourceJson := fragment0189806Chunk001Push00 fragment0189806Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189806_array_chunk_001"
  err.flush

noncomputable def fragment0189806Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0189806Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '2'])]) :: (acc))

theorem array_fragment0189806_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0189806Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0189806Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0189806Acc00300 : List SourceJson := fragment0189806Chunk002Push00 fragment0189806Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189806_array_chunk_002"
  err.flush

noncomputable def fragment0189806Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0189806Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]) :: (acc)

theorem array_fragment0189806_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0189806Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0189806Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0189806Acc00400 : List SourceJson := fragment0189806Chunk003Push00 fragment0189806Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189806_array_chunk_003"
  err.flush

noncomputable def fragment0189806Chars : List Char := '[' :: (fragment0189806Chunk000Chars00 ++ fragment0189806Chunk001Chars00 ++ fragment0189806Chunk002Chars00 ++ fragment0189806Chunk003Chars00)
noncomputable def fragment0189806Value : SourceJson := .arr (fragment0189806Acc00400.reverse)

theorem value_fragment0189806 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0189806Chars ++ tail) =
      .ok (fragment0189806Value, tail) := by
  have hinput : fragment0189806Chars ++ tail = '[' :: (fragment0189806Chunk000Chars00 ++ (fragment0189806Chunk001Chars00 ++ (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0189806Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0189806Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0189806Chunk000Chars00 ++ (fragment0189806Chunk001Chars00 ++ (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0189806Chunk000Chars00 ++ (fragment0189806Chunk001Chars00 ++ (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail)))))) fragment0189806Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0189806Chunk001Chars00 ++ (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail))))) fragment0189806Acc00100 := array_fragment0189806_chunk_000 fuel (fragment0189806Chunk001Chars00 ++ (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail)))) fragment0189806Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail)))) fragment0189806Acc00200 := array_fragment0189806_chunk_001 fuel (fragment0189806Chunk002Chars00 ++ (fragment0189806Chunk003Chars00 ++ (tail))) fragment0189806Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0189806Chunk003Chars00 ++ (tail))) fragment0189806Acc00300 := array_fragment0189806_chunk_002 fuel (fragment0189806Chunk003Chars00 ++ (tail)) fragment0189806Acc00200
    _ = .ok (fragment0189806Value, tail) := array_fragment0189806_chunk_003 fuel (tail) fragment0189806Acc00300

noncomputable def fragment0189585Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0189585Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0189585Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2'])]
noncomputable def fragment0189585Acc00100 : List (String × SourceJson) := (fragment0189585Field000Key00, fragment0189585Field000Value00) :: fragment0189585Acc00000
noncomputable def fragment0189585Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0189585_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0189585Field000Chars00 ++ tail)) fragment0189585Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0189585Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189585_object_field_000"
  err.flush

noncomputable def fragment0189585Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0189585Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0189585Acc00200 : List (String × SourceJson) := (fragment0189585Field001Key00, fragment0189585Field001Value00) :: fragment0189585Acc00100
noncomputable def fragment0189585Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0189585_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0189585Field001Chars00 ++ tail)) fragment0189585Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0189585Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189585_object_field_001"
  err.flush

noncomputable def fragment0189585Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0189585Field002Value00 : SourceJson := .number (String.ofList ['2', '2'])
noncomputable def fragment0189585Acc00300 : List (String × SourceJson) := (fragment0189585Field002Key00, fragment0189585Field002Value00) :: fragment0189585Acc00200
noncomputable def fragment0189585Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '2', ',']

theorem object_fragment0189585_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0189585Field002Chars00 ++ tail)) fragment0189585Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0189585Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189585_object_field_002"
  err.flush

noncomputable def fragment0189585Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0189585Field003Value00 : SourceJson := fragment0189806Value
noncomputable def fragment0189585Acc00400 : List (String × SourceJson) := (fragment0189585Field003Key00, fragment0189585Field003Value00) :: fragment0189585Acc00300
noncomputable def fragment0189585Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0189585Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0189585Field003Chars00 : List Char := fragment0189585Field003HeaderChars00 ++ fragment0189806Chars ++ fragment0189585Field003SuffixChars00

noncomputable def fragment0189585Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0189585Field003Key00, result.1) :: fragment0189585Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0189585Field003Key00, result.1) :: fragment0189585Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0189585_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0189585Field003HeaderChars00 ++ rest)) fragment0189585Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0189585Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0189585_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0189585Field003Chars00 ++ tail)) fragment0189585Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0189585Acc00400 := by
  have hinput : fragment0189585Field003Chars00 ++ tail = fragment0189585Field003HeaderChars00 ++ (fragment0189806Chars ++ (fragment0189585Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0189585Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0189585Field003Chars00 ++ tail)) fragment0189585Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0189585Field003HeaderChars00 ++ (fragment0189806Chars ++ (fragment0189585Field003SuffixChars00 ++ tail)))) fragment0189585Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0189585Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0189806Chars ++ (fragment0189585Field003SuffixChars00 ++ tail))).bind
        (fragment0189585Field003AfterValue00 (fuel + 17)) := object_fragment0189585_field_003_header fuel (fragment0189806Chars ++ (fragment0189585Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0189806Value, fragment0189585Field003SuffixChars00 ++ tail)).bind (fragment0189585Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0189585Field003AfterValue00 (fuel + 17)))
        (value_fragment0189806 (fuel + 0) (fragment0189585Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0189585Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189585_object_field_003"
  err.flush

noncomputable def fragment0189585Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0189585Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0189585Acc00500 : List (String × SourceJson) := (fragment0189585Field004Key00, fragment0189585Field004Value00) :: fragment0189585Acc00400
noncomputable def fragment0189585Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0189585_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0189585Field004Chars00 ++ tail)) fragment0189585Acc00400 =
      .ok (.obj (fragment0189585Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0189585_object_field_004"
  err.flush

noncomputable def fragment0189585Chars : List Char := '{' :: (fragment0189585Field000Chars00 ++ fragment0189585Field001Chars00 ++ fragment0189585Field002Chars00 ++ fragment0189585Field003Chars00 ++ fragment0189585Field004Chars00)
noncomputable def fragment0189585Value : SourceJson := .obj (fragment0189585Acc00500.reverse)

theorem value_fragment0189585 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0189585Chars ++ tail) =
      .ok (fragment0189585Value, tail) := by
  have hinput : fragment0189585Chars ++ tail = '{' :: (fragment0189585Field000Chars00 ++ (fragment0189585Field001Chars00 ++ (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0189585Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0189585Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0189585Field000Chars00 ++ (fragment0189585Field001Chars00 ++ (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0189585Field000Chars00 ++ (fragment0189585Field001Chars00 ++ (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail))))))) fragment0189585Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0189585Field001Chars00 ++ (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail)))))) fragment0189585Acc00100 := object_fragment0189585_field_000 fuel (fragment0189585Field001Chars00 ++ (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail))))) fragment0189585Acc00200 := object_fragment0189585_field_001 fuel (fragment0189585Field002Chars00 ++ (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail)))) fragment0189585Acc00300 := object_fragment0189585_field_002 fuel (fragment0189585Field003Chars00 ++ (fragment0189585Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0189585Field004Chars00 ++ (tail))) fragment0189585Acc00400 := object_fragment0189585_field_003 fuel (fragment0189585Field004Chars00 ++ (tail))
    _ = .ok (fragment0189585Value, tail) := object_fragment0189585_field_004 fuel (tail)

noncomputable def fragment0190731Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0190731Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0190731Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]
noncomputable def fragment0190731Acc00100 : List (String × SourceJson) := (fragment0190731Field000Key00, fragment0190731Field000Value00) :: fragment0190731Acc00000
noncomputable def fragment0190731Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190731_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0190731Field000Chars00 ++ tail)) fragment0190731Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0190731Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190731_object_field_000"
  err.flush

noncomputable def fragment0190731Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0190731Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0190731Acc00200 : List (String × SourceJson) := (fragment0190731Field001Key00, fragment0190731Field001Value00) :: fragment0190731Acc00100
noncomputable def fragment0190731Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0190731_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0190731Field001Chars00 ++ tail)) fragment0190731Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0190731Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190731_object_field_001"
  err.flush

noncomputable def fragment0190731Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0190731Field002Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0190731Acc00300 : List (String × SourceJson) := (fragment0190731Field002Key00, fragment0190731Field002Value00) :: fragment0190731Acc00200
noncomputable def fragment0190731Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0190731_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0190731Field002Chars00 ++ tail)) fragment0190731Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0190731Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190731_object_field_002"
  err.flush

noncomputable def fragment0190731Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0190731Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]]
noncomputable def fragment0190731Acc00400 : List (String × SourceJson) := (fragment0190731Field003Key00, fragment0190731Field003Value00) :: fragment0190731Acc00300
noncomputable def fragment0190731Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0190731_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0190731Field003Chars00 ++ tail)) fragment0190731Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0190731Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190731_object_field_003"
  err.flush

noncomputable def fragment0190731Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0190731Field004Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0190731Acc00500 : List (String × SourceJson) := (fragment0190731Field004Key00, fragment0190731Field004Value00) :: fragment0190731Acc00400
noncomputable def fragment0190731Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0190731_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0190731Field004Chars00 ++ tail)) fragment0190731Acc00400 =
      .ok (.obj (fragment0190731Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0190731_object_field_004"
  err.flush

noncomputable def fragment0190731Chars : List Char := '{' :: (fragment0190731Field000Chars00 ++ fragment0190731Field001Chars00 ++ fragment0190731Field002Chars00 ++ fragment0190731Field003Chars00 ++ fragment0190731Field004Chars00)
noncomputable def fragment0190731Value : SourceJson := .obj (fragment0190731Acc00500.reverse)

theorem value_fragment0190731 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0190731Chars ++ tail) =
      .ok (fragment0190731Value, tail) := by
  have hinput : fragment0190731Chars ++ tail = '{' :: (fragment0190731Field000Chars00 ++ (fragment0190731Field001Chars00 ++ (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0190731Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0190731Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0190731Field000Chars00 ++ (fragment0190731Field001Chars00 ++ (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0190731Field000Chars00 ++ (fragment0190731Field001Chars00 ++ (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail))))))) fragment0190731Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0190731Field001Chars00 ++ (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail)))))) fragment0190731Acc00100 := object_fragment0190731_field_000 fuel (fragment0190731Field001Chars00 ++ (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail))))) fragment0190731Acc00200 := object_fragment0190731_field_001 fuel (fragment0190731Field002Chars00 ++ (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail)))) fragment0190731Acc00300 := object_fragment0190731_field_002 fuel (fragment0190731Field003Chars00 ++ (fragment0190731Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0190731Field004Chars00 ++ (tail))) fragment0190731Acc00400 := object_fragment0190731_field_003 fuel (fragment0190731Field004Chars00 ++ (tail))
    _ = .ok (fragment0190731Value, tail) := object_fragment0190731_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_before_reader"
  err.flush

noncomputable def chunk0019Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0019Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['6'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['6'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['1', '2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0019 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 78) (SourceJson.white (chunk0019Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 76) (SourceJson.white tail) (chunk0019Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0019_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_before_reader"
  err.flush

noncomputable def chunk0020Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0020Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0020 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 76) (SourceJson.white (chunk0020Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 75) (SourceJson.white tail) (chunk0020Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0020_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_before_reader"
  err.flush

noncomputable def chunk0021Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0021Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['9'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['7']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0021 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 75) (SourceJson.white (chunk0021Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 74) (SourceJson.white tail) (chunk0021Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0021_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_before_reader"
  err.flush

noncomputable def chunk0022LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0022SuffixChars00 : List Char := [',']
noncomputable def chunk0022Chars00 : List Char := chunk0022LeadChars00 ++ fragment0189585Chars ++ chunk0022SuffixChars00
noncomputable def chunk0022Push00 (acc : List SourceJson) : List SourceJson := fragment0189585Value :: acc

noncomputable def chunk0022AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0022_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 74)
      (SourceJson.white (chunk0022LeadChars00 ++ (fragment0189585Chars ++ rest))) acc =
      (SourceJson.value (fuel + 73) (fragment0189585Chars ++ rest)).bind
        (chunk0022AfterValue00 (fuel + 73) acc) := by rfl

theorem array_chunk0022 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 74) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 73) (SourceJson.white tail) (chunk0022Push00 acc) := by
  have hinput : chunk0022Chars00 ++ tail = chunk0022LeadChars00 ++ (fragment0189585Chars ++ (chunk0022SuffixChars00 ++ tail)) := by
    simp only [chunk0022Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 74) (SourceJson.white (chunk0022Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 74)
          (SourceJson.white (chunk0022LeadChars00 ++ (fragment0189585Chars ++ (chunk0022SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 74) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 73) (fragment0189585Chars ++ (chunk0022SuffixChars00 ++ tail))).bind
        (chunk0022AfterValue00 (fuel + 73) acc) := array_chunk0022_head fuel (chunk0022SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0189585Value, chunk0022SuffixChars00 ++ tail)).bind
        (chunk0022AfterValue00 (fuel + 73) acc) :=
      congrArg (fun result => result.bind (chunk0022AfterValue00 (fuel + 73) acc))
        (value_fragment0189585 (fuel + 51) (chunk0022SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 73) (SourceJson.white tail) (chunk0022Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0022_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_before_reader"
  err.flush

noncomputable def chunk0023LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0023SuffixChars00 : List Char := [',']
noncomputable def chunk0023Chars00 : List Char := chunk0023LeadChars00 ++ fragment0190731Chars ++ chunk0023SuffixChars00
noncomputable def chunk0023Push00 (acc : List SourceJson) : List SourceJson := fragment0190731Value :: acc

noncomputable def chunk0023AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0023_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 73)
      (SourceJson.white (chunk0023LeadChars00 ++ (fragment0190731Chars ++ rest))) acc =
      (SourceJson.value (fuel + 72) (fragment0190731Chars ++ rest)).bind
        (chunk0023AfterValue00 (fuel + 72) acc) := by rfl

theorem array_chunk0023 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 73) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 72) (SourceJson.white tail) (chunk0023Push00 acc) := by
  have hinput : chunk0023Chars00 ++ tail = chunk0023LeadChars00 ++ (fragment0190731Chars ++ (chunk0023SuffixChars00 ++ tail)) := by
    simp only [chunk0023Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 73) (SourceJson.white (chunk0023Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 73)
          (SourceJson.white (chunk0023LeadChars00 ++ (fragment0190731Chars ++ (chunk0023SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 73) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 72) (fragment0190731Chars ++ (chunk0023SuffixChars00 ++ tail))).bind
        (chunk0023AfterValue00 (fuel + 72) acc) := array_chunk0023_head fuel (chunk0023SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0190731Value, chunk0023SuffixChars00 ++ tail)).bind
        (chunk0023AfterValue00 (fuel + 72) acc) :=
      congrArg (fun result => result.bind (chunk0023AfterValue00 (fuel + 72) acc))
        (value_fragment0190731 (fuel + 53) (chunk0023SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 72) (SourceJson.white tail) (chunk0023Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0023_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0019Chars00 ++ chunk0020Chars00 ++ chunk0021Chars00 ++ chunk0022Chars00 ++ chunk0023Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0023Push00 (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (acc)))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 78) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 72) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 78) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 78) (SourceJson.white (chunk0019Chars00 ++ (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 78) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 76) (SourceJson.white (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))))) (chunk0019Push00 (acc)) := array_chunk0019 fuel (chunk0020Chars00 ++ (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (acc)
    _ = SourceJson.array (fuel + 75) (SourceJson.white (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))))) (chunk0020Push00 (chunk0019Push00 (acc))) := array_chunk0020 fuel (chunk0021Chars00 ++ (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0019Push00 (acc))
    _ = SourceJson.array (fuel + 74) (SourceJson.white (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail)))) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (acc)))) := array_chunk0021 fuel (chunk0022Chars00 ++ (chunk0023Chars00 ++ (tail))) (chunk0020Push00 (chunk0019Push00 (acc)))
    _ = SourceJson.array (fuel + 73) (SourceJson.white (chunk0023Chars00 ++ (tail))) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (acc))))) := array_chunk0022 fuel (chunk0023Chars00 ++ (tail)) (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (acc))))
    _ = SourceJson.array (fuel + 72) (SourceJson.white tail) (blockPush acc) := array_chunk0023 fuel (tail) (chunk0022Push00 (chunk0021Push00 (chunk0020Push00 (chunk0019Push00 (acc)))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 187823).take 3740 = blockChars := by rfl

theorem block_original_split : sourceRest 187823 = blockChars ++ sourceRest 191563 := by
  calc
    sourceRest 187823 = (sourceRest 187823).take 3740 ++ (sourceRest 187823).drop 3740 :=
      (List.take_append_drop 3740 (sourceRest 187823)).symm
    _ = blockChars ++ (sourceRest 187823).drop 3740 :=
      congrArg (fun part => part ++ (sourceRest 187823).drop 3740) block_original_prefix
    _ = blockChars ++ sourceRest 191563 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 187823 3740)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 78) (SourceJson.white (sourceRest 187823)) acc =
      SourceJson.array (fuel + 72) (SourceJson.white (sourceRest 191563)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 78) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 191563) acc)

#print axioms array_fragment0189806_chunk_000
#print axioms array_fragment0189806_chunk_001
#print axioms array_fragment0189806_chunk_002
#print axioms array_fragment0189806_chunk_003
#print axioms value_fragment0189806
#print axioms object_fragment0189585_field_000
#print axioms object_fragment0189585_field_001
#print axioms object_fragment0189585_field_002
#print axioms object_fragment0189585_field_003_header
#print axioms object_fragment0189585_field_003
#print axioms object_fragment0189585_field_004
#print axioms value_fragment0189585
#print axioms object_fragment0190731_field_000
#print axioms object_fragment0190731_field_001
#print axioms object_fragment0190731_field_002
#print axioms object_fragment0190731_field_003
#print axioms object_fragment0190731_field_004
#print axioms value_fragment0190731
#print axioms array_chunk0019
#print axioms array_chunk0020
#print axioms array_chunk0021
#print axioms array_chunk0022_head
#print axioms array_chunk0022
#print axioms array_chunk0023_head
#print axioms array_chunk0023
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock009

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
