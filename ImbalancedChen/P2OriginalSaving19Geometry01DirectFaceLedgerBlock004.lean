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

namespace FaceLedgerBlock004

noncomputable def fragment0171484Acc00000 : List SourceJson := []

noncomputable def fragment0171484Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0171484Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]) :: (acc))

theorem array_fragment0171484_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0171484Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0171484Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0171484Acc00100 : List SourceJson := fragment0171484Chunk000Push00 fragment0171484Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171484_array_chunk_000"
  err.flush

noncomputable def fragment0171484Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0171484Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0171484_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0171484Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0171484Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0171484Acc00200 : List SourceJson := fragment0171484Chunk001Push00 fragment0171484Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171484_array_chunk_001"
  err.flush

noncomputable def fragment0171484Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0171484Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0171484_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0171484Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0171484Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0171484Acc00300 : List SourceJson := fragment0171484Chunk002Push00 fragment0171484Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171484_array_chunk_002"
  err.flush

noncomputable def fragment0171484Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0171484Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5'])]) :: (acc)

theorem array_fragment0171484_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0171484Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0171484Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0171484Acc00400 : List SourceJson := fragment0171484Chunk003Push00 fragment0171484Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171484_array_chunk_003"
  err.flush

noncomputable def fragment0171484Chars : List Char := '[' :: (fragment0171484Chunk000Chars00 ++ fragment0171484Chunk001Chars00 ++ fragment0171484Chunk002Chars00 ++ fragment0171484Chunk003Chars00)
noncomputable def fragment0171484Value : SourceJson := .arr (fragment0171484Acc00400.reverse)

theorem value_fragment0171484 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0171484Chars ++ tail) =
      .ok (fragment0171484Value, tail) := by
  have hinput : fragment0171484Chars ++ tail = '[' :: (fragment0171484Chunk000Chars00 ++ (fragment0171484Chunk001Chars00 ++ (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0171484Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0171484Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0171484Chunk000Chars00 ++ (fragment0171484Chunk001Chars00 ++ (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0171484Chunk000Chars00 ++ (fragment0171484Chunk001Chars00 ++ (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail)))))) fragment0171484Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0171484Chunk001Chars00 ++ (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail))))) fragment0171484Acc00100 := array_fragment0171484_chunk_000 fuel (fragment0171484Chunk001Chars00 ++ (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail)))) fragment0171484Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail)))) fragment0171484Acc00200 := array_fragment0171484_chunk_001 fuel (fragment0171484Chunk002Chars00 ++ (fragment0171484Chunk003Chars00 ++ (tail))) fragment0171484Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0171484Chunk003Chars00 ++ (tail))) fragment0171484Acc00300 := array_fragment0171484_chunk_002 fuel (fragment0171484Chunk003Chars00 ++ (tail)) fragment0171484Acc00200
    _ = .ok (fragment0171484Value, tail) := array_fragment0171484_chunk_003 fuel (tail) fragment0171484Acc00300

noncomputable def fragment0171240Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0171240Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0171240Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '5'])]
noncomputable def fragment0171240Acc00100 : List (String × SourceJson) := (fragment0171240Field000Key00, fragment0171240Field000Value00) :: fragment0171240Acc00000
noncomputable def fragment0171240Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0171240_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0171240Field000Chars00 ++ tail)) fragment0171240Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0171240Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171240_object_field_000"
  err.flush

noncomputable def fragment0171240Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0171240Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0171240Acc00200 : List (String × SourceJson) := (fragment0171240Field001Key00, fragment0171240Field001Value00) :: fragment0171240Acc00100
noncomputable def fragment0171240Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0171240_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0171240Field001Chars00 ++ tail)) fragment0171240Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0171240Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171240_object_field_001"
  err.flush

noncomputable def fragment0171240Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0171240Field002Value00 : SourceJson := .number (String.ofList ['2', '5'])
noncomputable def fragment0171240Acc00300 : List (String × SourceJson) := (fragment0171240Field002Key00, fragment0171240Field002Value00) :: fragment0171240Acc00200
noncomputable def fragment0171240Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '5', ',']

theorem object_fragment0171240_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0171240Field002Chars00 ++ tail)) fragment0171240Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0171240Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171240_object_field_002"
  err.flush

noncomputable def fragment0171240Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0171240Field003Value00 : SourceJson := fragment0171484Value
noncomputable def fragment0171240Acc00400 : List (String × SourceJson) := (fragment0171240Field003Key00, fragment0171240Field003Value00) :: fragment0171240Acc00300
noncomputable def fragment0171240Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0171240Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0171240Field003Chars00 : List Char := fragment0171240Field003HeaderChars00 ++ fragment0171484Chars ++ fragment0171240Field003SuffixChars00

noncomputable def fragment0171240Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0171240Field003Key00, result.1) :: fragment0171240Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0171240Field003Key00, result.1) :: fragment0171240Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0171240_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0171240Field003HeaderChars00 ++ rest)) fragment0171240Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0171240Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0171240_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0171240Field003Chars00 ++ tail)) fragment0171240Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0171240Acc00400 := by
  have hinput : fragment0171240Field003Chars00 ++ tail = fragment0171240Field003HeaderChars00 ++ (fragment0171484Chars ++ (fragment0171240Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0171240Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0171240Field003Chars00 ++ tail)) fragment0171240Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0171240Field003HeaderChars00 ++ (fragment0171484Chars ++ (fragment0171240Field003SuffixChars00 ++ tail)))) fragment0171240Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0171240Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0171484Chars ++ (fragment0171240Field003SuffixChars00 ++ tail))).bind
        (fragment0171240Field003AfterValue00 (fuel + 17)) := object_fragment0171240_field_003_header fuel (fragment0171484Chars ++ (fragment0171240Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0171484Value, fragment0171240Field003SuffixChars00 ++ tail)).bind (fragment0171240Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0171240Field003AfterValue00 (fuel + 17)))
        (value_fragment0171484 (fuel + 0) (fragment0171240Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0171240Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171240_object_field_003"
  err.flush

noncomputable def fragment0171240Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0171240Field004Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment0171240Acc00500 : List (String × SourceJson) := (fragment0171240Field004Key00, fragment0171240Field004Value00) :: fragment0171240Acc00400
noncomputable def fragment0171240Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0171240_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0171240Field004Chars00 ++ tail)) fragment0171240Acc00400 =
      .ok (.obj (fragment0171240Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0171240_object_field_004"
  err.flush

noncomputable def fragment0171240Chars : List Char := '{' :: (fragment0171240Field000Chars00 ++ fragment0171240Field001Chars00 ++ fragment0171240Field002Chars00 ++ fragment0171240Field003Chars00 ++ fragment0171240Field004Chars00)
noncomputable def fragment0171240Value : SourceJson := .obj (fragment0171240Acc00500.reverse)

theorem value_fragment0171240 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0171240Chars ++ tail) =
      .ok (fragment0171240Value, tail) := by
  have hinput : fragment0171240Chars ++ tail = '{' :: (fragment0171240Field000Chars00 ++ (fragment0171240Field001Chars00 ++ (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0171240Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0171240Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0171240Field000Chars00 ++ (fragment0171240Field001Chars00 ++ (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0171240Field000Chars00 ++ (fragment0171240Field001Chars00 ++ (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail))))))) fragment0171240Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0171240Field001Chars00 ++ (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail)))))) fragment0171240Acc00100 := object_fragment0171240_field_000 fuel (fragment0171240Field001Chars00 ++ (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail))))) fragment0171240Acc00200 := object_fragment0171240_field_001 fuel (fragment0171240Field002Chars00 ++ (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail)))) fragment0171240Acc00300 := object_fragment0171240_field_002 fuel (fragment0171240Field003Chars00 ++ (fragment0171240Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0171240Field004Chars00 ++ (tail))) fragment0171240Acc00400 := object_fragment0171240_field_003 fuel (fragment0171240Field004Chars00 ++ (tail))
    _ = .ok (fragment0171240Value, tail) := object_fragment0171240_field_004 fuel (tail)

noncomputable def fragment0173305Acc00000 : List SourceJson := []

noncomputable def fragment0173305Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0173305Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]) :: (acc))

theorem array_fragment0173305_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0173305Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0173305Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0173305Acc00100 : List SourceJson := fragment0173305Chunk000Push00 fragment0173305Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173305_array_chunk_000"
  err.flush

noncomputable def fragment0173305Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0173305Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0173305_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0173305Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0173305Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0173305Acc00200 : List SourceJson := fragment0173305Chunk001Push00 fragment0173305Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173305_array_chunk_001"
  err.flush

noncomputable def fragment0173305Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0173305Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9'])]) :: (acc))

theorem array_fragment0173305_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0173305Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0173305Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0173305Acc00300 : List SourceJson := fragment0173305Chunk002Push00 fragment0173305Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173305_array_chunk_002"
  err.flush

noncomputable def fragment0173305Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0173305Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc)

theorem array_fragment0173305_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0173305Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0173305Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0173305Acc00400 : List SourceJson := fragment0173305Chunk003Push00 fragment0173305Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173305_array_chunk_003"
  err.flush

noncomputable def fragment0173305Chars : List Char := '[' :: (fragment0173305Chunk000Chars00 ++ fragment0173305Chunk001Chars00 ++ fragment0173305Chunk002Chars00 ++ fragment0173305Chunk003Chars00)
noncomputable def fragment0173305Value : SourceJson := .arr (fragment0173305Acc00400.reverse)

theorem value_fragment0173305 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment0173305Chars ++ tail) =
      .ok (fragment0173305Value, tail) := by
  have hinput : fragment0173305Chars ++ tail = '[' :: (fragment0173305Chunk000Chars00 ++ (fragment0173305Chunk001Chars00 ++ (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0173305Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment0173305Chars ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment0173305Chunk000Chars00 ++ (fragment0173305Chunk001Chars00 ++ (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0173305Chunk000Chars00 ++ (fragment0173305Chunk001Chars00 ++ (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail)))))) fragment0173305Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0173305Chunk001Chars00 ++ (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail))))) fragment0173305Acc00100 := array_fragment0173305_chunk_000 fuel (fragment0173305Chunk001Chars00 ++ (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail)))) fragment0173305Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail)))) fragment0173305Acc00200 := array_fragment0173305_chunk_001 fuel (fragment0173305Chunk002Chars00 ++ (fragment0173305Chunk003Chars00 ++ (tail))) fragment0173305Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0173305Chunk003Chars00 ++ (tail))) fragment0173305Acc00300 := array_fragment0173305_chunk_002 fuel (fragment0173305Chunk003Chars00 ++ (tail)) fragment0173305Acc00200
    _ = .ok (fragment0173305Value, tail) := array_fragment0173305_chunk_003 fuel (tail) fragment0173305Acc00300

noncomputable def fragment0173087Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0173087Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0173087Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]
noncomputable def fragment0173087Acc00100 : List (String × SourceJson) := (fragment0173087Field000Key00, fragment0173087Field000Value00) :: fragment0173087Acc00000
noncomputable def fragment0173087Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0173087_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0173087Field000Chars00 ++ tail)) fragment0173087Acc00000 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0173087Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173087_object_field_000"
  err.flush

noncomputable def fragment0173087Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0173087Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0173087Acc00200 : List (String × SourceJson) := (fragment0173087Field001Key00, fragment0173087Field001Value00) :: fragment0173087Acc00100
noncomputable def fragment0173087Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0173087_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0173087Field001Chars00 ++ tail)) fragment0173087Acc00100 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0173087Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173087_object_field_001"
  err.flush

noncomputable def fragment0173087Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0173087Field002Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0173087Acc00300 : List (String × SourceJson) := (fragment0173087Field002Key00, fragment0173087Field002Value00) :: fragment0173087Acc00200
noncomputable def fragment0173087Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',']

theorem object_fragment0173087_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0173087Field002Chars00 ++ tail)) fragment0173087Acc00200 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0173087Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173087_object_field_002"
  err.flush

noncomputable def fragment0173087Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0173087Field003Value00 : SourceJson := fragment0173305Value
noncomputable def fragment0173087Acc00400 : List (String × SourceJson) := (fragment0173087Field003Key00, fragment0173087Field003Value00) :: fragment0173087Acc00300
noncomputable def fragment0173087Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0173087Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0173087Field003Chars00 : List Char := fragment0173087Field003HeaderChars00 ++ fragment0173305Chars ++ fragment0173087Field003SuffixChars00

noncomputable def fragment0173087Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0173087Field003Key00, result.1) :: fragment0173087Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0173087Field003Key00, result.1) :: fragment0173087Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0173087_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0173087Field003HeaderChars00 ++ rest)) fragment0173087Acc00300 =
      (SourceJson.value (fuel + 18) rest).bind (fragment0173087Field003AfterValue00 (fuel + 18)) := by rfl

theorem object_fragment0173087_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0173087Field003Chars00 ++ tail)) fragment0173087Acc00300 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0173087Acc00400 := by
  have hinput : fragment0173087Field003Chars00 ++ tail = fragment0173087Field003HeaderChars00 ++ (fragment0173305Chars ++ (fragment0173087Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0173087Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0173087Field003Chars00 ++ tail)) fragment0173087Acc00300 =
        SourceJson.object (fuel + 19)
          (SourceJson.white (fragment0173087Field003HeaderChars00 ++ (fragment0173305Chars ++ (fragment0173087Field003SuffixChars00 ++ tail)))) fragment0173087Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 19) (SourceJson.white s) fragment0173087Acc00300) hinput
    _ = (SourceJson.value (fuel + 18) (fragment0173305Chars ++ (fragment0173087Field003SuffixChars00 ++ tail))).bind
        (fragment0173087Field003AfterValue00 (fuel + 18)) := object_fragment0173087_field_003_header fuel (fragment0173305Chars ++ (fragment0173087Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0173305Value, fragment0173087Field003SuffixChars00 ++ tail)).bind (fragment0173087Field003AfterValue00 (fuel + 18)) :=
      congrArg (fun result => result.bind (fragment0173087Field003AfterValue00 (fuel + 18)))
        (value_fragment0173305 (fuel + 0) (fragment0173087Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0173087Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173087_object_field_003"
  err.flush

noncomputable def fragment0173087Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0173087Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0173087Acc00500 : List (String × SourceJson) := (fragment0173087Field004Key00, fragment0173087Field004Value00) :: fragment0173087Acc00400
noncomputable def fragment0173087Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0173087_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0173087Field004Chars00 ++ tail)) fragment0173087Acc00400 =
      .ok (.obj (fragment0173087Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0173087_object_field_004"
  err.flush

noncomputable def fragment0173087Chars : List Char := '{' :: (fragment0173087Field000Chars00 ++ fragment0173087Field001Chars00 ++ fragment0173087Field002Chars00 ++ fragment0173087Field003Chars00 ++ fragment0173087Field004Chars00)
noncomputable def fragment0173087Value : SourceJson := .obj (fragment0173087Acc00500.reverse)

theorem value_fragment0173087 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0173087Chars ++ tail) =
      .ok (fragment0173087Value, tail) := by
  have hinput : fragment0173087Chars ++ tail = '{' :: (fragment0173087Field000Chars00 ++ (fragment0173087Field001Chars00 ++ (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0173087Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0173087Chars ++ tail) =
        SourceJson.value (fuel + 23) ('{' :: (fragment0173087Field000Chars00 ++ (fragment0173087Field001Chars00 ++ (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0173087Field000Chars00 ++ (fragment0173087Field001Chars00 ++ (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail))))))) fragment0173087Acc00000 := by rfl
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0173087Field001Chars00 ++ (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail)))))) fragment0173087Acc00100 := object_fragment0173087_field_000 fuel (fragment0173087Field001Chars00 ++ (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail))))) fragment0173087Acc00200 := object_fragment0173087_field_001 fuel (fragment0173087Field002Chars00 ++ (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail)))) fragment0173087Acc00300 := object_fragment0173087_field_002 fuel (fragment0173087Field003Chars00 ++ (fragment0173087Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0173087Field004Chars00 ++ (tail))) fragment0173087Acc00400 := object_fragment0173087_field_003 fuel (fragment0173087Field004Chars00 ++ (tail))
    _ = .ok (fragment0173087Value, tail) := object_fragment0173087_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0005SuffixChars00 : List Char := [',']
noncomputable def chunk0005Chars00 : List Char := chunk0005LeadChars00 ++ fragment0171240Chars ++ chunk0005SuffixChars00
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson := fragment0171240Value :: acc

noncomputable def chunk0005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93)
      (SourceJson.white (chunk0005LeadChars00 ++ (fragment0171240Chars ++ rest))) acc =
      (SourceJson.value (fuel + 92) (fragment0171240Chars ++ rest)).bind
        (chunk0005AfterValue00 (fuel + 92) acc) := by rfl

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 92) (SourceJson.white tail) (chunk0005Push00 acc) := by
  have hinput : chunk0005Chars00 ++ tail = chunk0005LeadChars00 ++ (fragment0171240Chars ++ (chunk0005SuffixChars00 ++ tail)) := by
    simp only [chunk0005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 93) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 93)
          (SourceJson.white (chunk0005LeadChars00 ++ (fragment0171240Chars ++ (chunk0005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 93) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 92) (fragment0171240Chars ++ (chunk0005SuffixChars00 ++ tail))).bind
        (chunk0005AfterValue00 (fuel + 92) acc) := array_chunk0005_head fuel (chunk0005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0171240Value, chunk0005SuffixChars00 ++ tail)).bind
        (chunk0005AfterValue00 (fuel + 92) acc) :=
      congrArg (fun result => result.bind (chunk0005AfterValue00 (fuel + 92) acc))
        (value_fragment0171240 (fuel + 70) (chunk0005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 92) (SourceJson.white tail) (chunk0005Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['1', '2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['6']))]) :: (acc)

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 92) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 91) (SourceJson.white tail) (chunk0006Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_before_reader"
  err.flush

noncomputable def chunk0007LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0007SuffixChars00 : List Char := [',']
noncomputable def chunk0007Chars00 : List Char := chunk0007LeadChars00 ++ fragment0173087Chars ++ chunk0007SuffixChars00
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson := fragment0173087Value :: acc

noncomputable def chunk0007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 91)
      (SourceJson.white (chunk0007LeadChars00 ++ (fragment0173087Chars ++ rest))) acc =
      (SourceJson.value (fuel + 90) (fragment0173087Chars ++ rest)).bind
        (chunk0007AfterValue00 (fuel + 90) acc) := by rfl

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 91) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 90) (SourceJson.white tail) (chunk0007Push00 acc) := by
  have hinput : chunk0007Chars00 ++ tail = chunk0007LeadChars00 ++ (fragment0173087Chars ++ (chunk0007SuffixChars00 ++ tail)) := by
    simp only [chunk0007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 91) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 91)
          (SourceJson.white (chunk0007LeadChars00 ++ (fragment0173087Chars ++ (chunk0007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 91) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 90) (fragment0173087Chars ++ (chunk0007SuffixChars00 ++ tail))).bind
        (chunk0007AfterValue00 (fuel + 90) acc) := array_chunk0007_head fuel (chunk0007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0173087Value, chunk0007SuffixChars00 ++ tail)).bind
        (chunk0007AfterValue00 (fuel + 90) acc) :=
      congrArg (fun result => result.bind (chunk0007AfterValue00 (fuel + 90) acc))
        (value_fragment0173087 (fuel + 67) (chunk0007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 90) (SourceJson.white tail) (chunk0007Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (acc)))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 93) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 90) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 93) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 93) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 93) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 92) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (acc)) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (acc)
    _ = SourceJson.array (fuel + 91) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (acc))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (acc))
    _ = SourceJson.array (fuel + 90) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (acc)))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 171234).take 2975 = blockChars := by rfl

theorem block_original_split : sourceRest 171234 = blockChars ++ sourceRest 174209 := by
  calc
    sourceRest 171234 = (sourceRest 171234).take 2975 ++ (sourceRest 171234).drop 2975 :=
      (List.take_append_drop 2975 (sourceRest 171234)).symm
    _ = blockChars ++ (sourceRest 171234).drop 2975 :=
      congrArg (fun part => part ++ (sourceRest 171234).drop 2975) block_original_prefix
    _ = blockChars ++ sourceRest 174209 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 171234 2975)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 93) (SourceJson.white (sourceRest 171234)) acc =
      SourceJson.array (fuel + 90) (SourceJson.white (sourceRest 174209)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 93) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 174209) acc)

#print axioms array_fragment0171484_chunk_000
#print axioms array_fragment0171484_chunk_001
#print axioms array_fragment0171484_chunk_002
#print axioms array_fragment0171484_chunk_003
#print axioms value_fragment0171484
#print axioms object_fragment0171240_field_000
#print axioms object_fragment0171240_field_001
#print axioms object_fragment0171240_field_002
#print axioms object_fragment0171240_field_003_header
#print axioms object_fragment0171240_field_003
#print axioms object_fragment0171240_field_004
#print axioms value_fragment0171240
#print axioms array_fragment0173305_chunk_000
#print axioms array_fragment0173305_chunk_001
#print axioms array_fragment0173305_chunk_002
#print axioms array_fragment0173305_chunk_003
#print axioms value_fragment0173305
#print axioms object_fragment0173087_field_000
#print axioms object_fragment0173087_field_001
#print axioms object_fragment0173087_field_002
#print axioms object_fragment0173087_field_003_header
#print axioms object_fragment0173087_field_003
#print axioms object_fragment0173087_field_004
#print axioms value_fragment0173087
#print axioms array_chunk0005_head
#print axioms array_chunk0005
#print axioms array_chunk0006
#print axioms array_chunk0007_head
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock004

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
