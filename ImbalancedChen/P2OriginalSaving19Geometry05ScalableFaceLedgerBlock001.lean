import ImbalancedChen.P2OriginalSaving19Geometry05ScalableInput

/-! Original face_ledger grouped chunk transitions, including exact compact-input binding.
The original packed input, original parser and original decoder are unchanged.
This is a source-only candidate until normal, kernel and full-owned checks pass. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock001

noncomputable def fragment0079500Acc00000 : List SourceJson := []

noncomputable def fragment0079500Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0079500Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]) :: (acc))

theorem array_fragment0079500_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0079500Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0079500Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0079500Acc00100 : List SourceJson := fragment0079500Chunk000Push00 fragment0079500Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079500_array_chunk_000"
  err.flush

noncomputable def fragment0079500Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0079500Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0079500_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0079500Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0079500Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0079500Acc00200 : List SourceJson := fragment0079500Chunk001Push00 fragment0079500Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079500_array_chunk_001"
  err.flush

noncomputable def fragment0079500Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0079500Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0079500_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0079500Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0079500Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0079500Acc00300 : List SourceJson := fragment0079500Chunk002Push00 fragment0079500Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079500_array_chunk_002"
  err.flush

noncomputable def fragment0079500Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0079500Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc)

theorem array_fragment0079500_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0079500Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0079500Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0079500Acc00400 : List SourceJson := fragment0079500Chunk003Push00 fragment0079500Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079500_array_chunk_003"
  err.flush

noncomputable def fragment0079500Chars : List Char := '[' :: (fragment0079500Chunk000Chars00 ++ fragment0079500Chunk001Chars00 ++ fragment0079500Chunk002Chars00 ++ fragment0079500Chunk003Chars00)
noncomputable def fragment0079500Value : SourceJson := .arr (fragment0079500Acc00400.reverse)

theorem value_fragment0079500 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment0079500Chars ++ tail) =
      .ok (fragment0079500Value, tail) := by
  have hinput : fragment0079500Chars ++ tail = '[' :: (fragment0079500Chunk000Chars00 ++ (fragment0079500Chunk001Chars00 ++ (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0079500Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment0079500Chars ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment0079500Chunk000Chars00 ++ (fragment0079500Chunk001Chars00 ++ (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0079500Chunk000Chars00 ++ (fragment0079500Chunk001Chars00 ++ (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail)))))) fragment0079500Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0079500Chunk001Chars00 ++ (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail))))) fragment0079500Acc00100 := array_fragment0079500_chunk_000 fuel (fragment0079500Chunk001Chars00 ++ (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail)))) fragment0079500Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail)))) fragment0079500Acc00200 := array_fragment0079500_chunk_001 fuel (fragment0079500Chunk002Chars00 ++ (fragment0079500Chunk003Chars00 ++ (tail))) fragment0079500Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0079500Chunk003Chars00 ++ (tail))) fragment0079500Acc00300 := array_fragment0079500_chunk_002 fuel (fragment0079500Chunk003Chars00 ++ (tail)) fragment0079500Acc00200
    _ = .ok (fragment0079500Value, tail) := array_fragment0079500_chunk_003 fuel (tail) fragment0079500Acc00300

noncomputable def fragment0079282Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0079282Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0079282Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]
noncomputable def fragment0079282Acc00100 : List (String × SourceJson) := (fragment0079282Field000Key00, fragment0079282Field000Value00) :: fragment0079282Acc00000
noncomputable def fragment0079282Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0079282_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0079282Field000Chars00 ++ tail)) fragment0079282Acc00000 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0079282Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079282_object_field_000"
  err.flush

noncomputable def fragment0079282Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0079282Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0079282Acc00200 : List (String × SourceJson) := (fragment0079282Field001Key00, fragment0079282Field001Value00) :: fragment0079282Acc00100
noncomputable def fragment0079282Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0079282_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0079282Field001Chars00 ++ tail)) fragment0079282Acc00100 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0079282Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079282_object_field_001"
  err.flush

noncomputable def fragment0079282Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0079282Field002Value00 : SourceJson := .number (String.ofList ['1', '1'])
noncomputable def fragment0079282Acc00300 : List (String × SourceJson) := (fragment0079282Field002Key00, fragment0079282Field002Value00) :: fragment0079282Acc00200
noncomputable def fragment0079282Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',']

theorem object_fragment0079282_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0079282Field002Chars00 ++ tail)) fragment0079282Acc00200 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0079282Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079282_object_field_002"
  err.flush

noncomputable def fragment0079282Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0079282Field003Value00 : SourceJson := fragment0079500Value
noncomputable def fragment0079282Acc00400 : List (String × SourceJson) := (fragment0079282Field003Key00, fragment0079282Field003Value00) :: fragment0079282Acc00300
noncomputable def fragment0079282Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0079282Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0079282Field003Chars00 : List Char := fragment0079282Field003HeaderChars00 ++ fragment0079500Chars ++ fragment0079282Field003SuffixChars00

noncomputable def fragment0079282Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0079282Field003Key00, result.1) :: fragment0079282Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0079282Field003Key00, result.1) :: fragment0079282Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0079282_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0079282Field003HeaderChars00 ++ rest)) fragment0079282Acc00300 =
      (SourceJson.value (fuel + 18) rest).bind (fragment0079282Field003AfterValue00 (fuel + 18)) := by rfl

theorem object_fragment0079282_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0079282Field003Chars00 ++ tail)) fragment0079282Acc00300 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0079282Acc00400 := by
  have hinput : fragment0079282Field003Chars00 ++ tail = fragment0079282Field003HeaderChars00 ++ (fragment0079500Chars ++ (fragment0079282Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0079282Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0079282Field003Chars00 ++ tail)) fragment0079282Acc00300 =
        SourceJson.object (fuel + 19)
          (SourceJson.white (fragment0079282Field003HeaderChars00 ++ (fragment0079500Chars ++ (fragment0079282Field003SuffixChars00 ++ tail)))) fragment0079282Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 19) (SourceJson.white s) fragment0079282Acc00300) hinput
    _ = (SourceJson.value (fuel + 18) (fragment0079500Chars ++ (fragment0079282Field003SuffixChars00 ++ tail))).bind
        (fragment0079282Field003AfterValue00 (fuel + 18)) := object_fragment0079282_field_003_header fuel (fragment0079500Chars ++ (fragment0079282Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0079500Value, fragment0079282Field003SuffixChars00 ++ tail)).bind (fragment0079282Field003AfterValue00 (fuel + 18)) :=
      congrArg (fun result => result.bind (fragment0079282Field003AfterValue00 (fuel + 18)))
        (value_fragment0079500 (fuel + 0) (fragment0079282Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0079282Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079282_object_field_003"
  err.flush

noncomputable def fragment0079282Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0079282Field004Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0079282Acc00500 : List (String × SourceJson) := (fragment0079282Field004Key00, fragment0079282Field004Value00) :: fragment0079282Acc00400
noncomputable def fragment0079282Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0079282_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0079282Field004Chars00 ++ tail)) fragment0079282Acc00400 =
      .ok (.obj (fragment0079282Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079282_object_field_004"
  err.flush

noncomputable def fragment0079282Chars : List Char := '{' :: (fragment0079282Field000Chars00 ++ fragment0079282Field001Chars00 ++ fragment0079282Field002Chars00 ++ fragment0079282Field003Chars00 ++ fragment0079282Field004Chars00)
noncomputable def fragment0079282Value : SourceJson := .obj (fragment0079282Acc00500.reverse)

theorem value_fragment0079282 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0079282Chars ++ tail) =
      .ok (fragment0079282Value, tail) := by
  have hinput : fragment0079282Chars ++ tail = '{' :: (fragment0079282Field000Chars00 ++ (fragment0079282Field001Chars00 ++ (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0079282Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0079282Chars ++ tail) =
        SourceJson.value (fuel + 23) ('{' :: (fragment0079282Field000Chars00 ++ (fragment0079282Field001Chars00 ++ (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0079282Field000Chars00 ++ (fragment0079282Field001Chars00 ++ (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail))))))) fragment0079282Acc00000 := by rfl
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0079282Field001Chars00 ++ (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail)))))) fragment0079282Acc00100 := object_fragment0079282_field_000 fuel (fragment0079282Field001Chars00 ++ (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail))))) fragment0079282Acc00200 := object_fragment0079282_field_001 fuel (fragment0079282Field002Chars00 ++ (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail)))) fragment0079282Acc00300 := object_fragment0079282_field_002 fuel (fragment0079282Field003Chars00 ++ (fragment0079282Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0079282Field004Chars00 ++ (tail))) fragment0079282Acc00400 := object_fragment0079282_field_003 fuel (fragment0079282Field004Chars00 ++ (tail))
    _ = .ok (fragment0079282Value, tail) := object_fragment0079282_field_004 fuel (tail)

noncomputable def fragment0080758Acc00000 : List SourceJson := []

noncomputable def fragment0080758Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080758Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1'])]) :: (acc))

theorem array_fragment0080758_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 26) (SourceJson.white (fragment0080758Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 24) (SourceJson.white tail) (fragment0080758Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0080758Acc00100 : List SourceJson := fragment0080758Chunk000Push00 fragment0080758Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080758_array_chunk_000"
  err.flush

noncomputable def fragment0080758Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080758Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0080758_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 24) (SourceJson.white (fragment0080758Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (fragment0080758Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0080758Acc00200 : List SourceJson := fragment0080758Chunk001Push00 fragment0080758Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080758_array_chunk_001"
  err.flush

noncomputable def fragment0080758Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080758Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0080758_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (fragment0080758Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 20) (SourceJson.white tail) (fragment0080758Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0080758Acc00300 : List SourceJson := fragment0080758Chunk002Push00 fragment0080758Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080758_array_chunk_002"
  err.flush

noncomputable def fragment0080758Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080758Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])]) :: (acc))

theorem array_fragment0080758_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 20) (SourceJson.white (fragment0080758Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 18) (SourceJson.white tail) (fragment0080758Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0080758Acc00400 : List SourceJson := fragment0080758Chunk003Push00 fragment0080758Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080758_array_chunk_003"
  err.flush

noncomputable def fragment0080758Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0080758Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]) :: (acc)

theorem array_fragment0080758_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 18) (SourceJson.white (fragment0080758Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0080758Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0080758Acc00500 : List SourceJson := fragment0080758Chunk004Push00 fragment0080758Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080758_array_chunk_004"
  err.flush

noncomputable def fragment0080758Chars : List Char := '[' :: (fragment0080758Chunk000Chars00 ++ fragment0080758Chunk001Chars00 ++ fragment0080758Chunk002Chars00 ++ fragment0080758Chunk003Chars00 ++ fragment0080758Chunk004Chars00)
noncomputable def fragment0080758Value : SourceJson := .arr (fragment0080758Acc00500.reverse)

theorem value_fragment0080758 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment0080758Chars ++ tail) =
      .ok (fragment0080758Value, tail) := by
  have hinput : fragment0080758Chars ++ tail = '[' :: (fragment0080758Chunk000Chars00 ++ (fragment0080758Chunk001Chars00 ++ (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0080758Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment0080758Chars ++ tail) =
        SourceJson.value (fuel + 27) ('[' :: (fragment0080758Chunk000Chars00 ++ (fragment0080758Chunk001Chars00 ++ (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.array (fuel + 26) (SourceJson.white (fragment0080758Chunk000Chars00 ++ (fragment0080758Chunk001Chars00 ++ (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail))))))) fragment0080758Acc00000 := by rfl
    _ = SourceJson.array (fuel + 24) (SourceJson.white (fragment0080758Chunk001Chars00 ++ (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail)))))) fragment0080758Acc00100 := array_fragment0080758_chunk_000 fuel (fragment0080758Chunk001Chars00 ++ (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail))))) fragment0080758Acc00000
    _ = SourceJson.array (fuel + 22) (SourceJson.white (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail))))) fragment0080758Acc00200 := array_fragment0080758_chunk_001 fuel (fragment0080758Chunk002Chars00 ++ (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail)))) fragment0080758Acc00100
    _ = SourceJson.array (fuel + 20) (SourceJson.white (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail)))) fragment0080758Acc00300 := array_fragment0080758_chunk_002 fuel (fragment0080758Chunk003Chars00 ++ (fragment0080758Chunk004Chars00 ++ (tail))) fragment0080758Acc00200
    _ = SourceJson.array (fuel + 18) (SourceJson.white (fragment0080758Chunk004Chars00 ++ (tail))) fragment0080758Acc00400 := array_fragment0080758_chunk_003 fuel (fragment0080758Chunk004Chars00 ++ (tail)) fragment0080758Acc00300
    _ = .ok (fragment0080758Value, tail) := array_fragment0080758_chunk_004 fuel (tail) fragment0080758Acc00400

noncomputable def fragment0080410Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0080410Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0080410Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]
noncomputable def fragment0080410Acc00100 : List (String × SourceJson) := (fragment0080410Field000Key00, fragment0080410Field000Value00) :: fragment0080410Acc00000
noncomputable def fragment0080410Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0080410_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 31) (SourceJson.white (fragment0080410Field000Chars00 ++ tail)) fragment0080410Acc00000 =
      SourceJson.object (fuel + 30) (SourceJson.white tail) fragment0080410Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080410_object_field_000"
  err.flush

noncomputable def fragment0080410Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0080410Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0080410Acc00200 : List (String × SourceJson) := (fragment0080410Field001Key00, fragment0080410Field001Value00) :: fragment0080410Acc00100
noncomputable def fragment0080410Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0080410_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 30) (SourceJson.white (fragment0080410Field001Chars00 ++ tail)) fragment0080410Acc00100 =
      SourceJson.object (fuel + 29) (SourceJson.white tail) fragment0080410Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080410_object_field_001"
  err.flush

noncomputable def fragment0080410Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0080410Field002Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0080410Acc00300 : List (String × SourceJson) := (fragment0080410Field002Key00, fragment0080410Field002Value00) :: fragment0080410Acc00200
noncomputable def fragment0080410Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0080410_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0080410Field002Chars00 ++ tail)) fragment0080410Acc00200 =
      SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0080410Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080410_object_field_002"
  err.flush

noncomputable def fragment0080410Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0080410Field003Value00 : SourceJson := fragment0080758Value
noncomputable def fragment0080410Acc00400 : List (String × SourceJson) := (fragment0080410Field003Key00, fragment0080410Field003Value00) :: fragment0080410Acc00300
noncomputable def fragment0080410Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0080410Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0080410Field003Chars00 : List Char := fragment0080410Field003HeaderChars00 ++ fragment0080758Chars ++ fragment0080410Field003SuffixChars00

noncomputable def fragment0080410Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0080410Field003Key00, result.1) :: fragment0080410Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0080410Field003Key00, result.1) :: fragment0080410Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0080410_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0080410Field003HeaderChars00 ++ rest)) fragment0080410Acc00300 =
      (SourceJson.value (fuel + 27) rest).bind (fragment0080410Field003AfterValue00 (fuel + 27)) := by rfl

theorem object_fragment0080410_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0080410Field003Chars00 ++ tail)) fragment0080410Acc00300 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0080410Acc00400 := by
  have hinput : fragment0080410Field003Chars00 ++ tail = fragment0080410Field003HeaderChars00 ++ (fragment0080758Chars ++ (fragment0080410Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0080410Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0080410Field003Chars00 ++ tail)) fragment0080410Acc00300 =
        SourceJson.object (fuel + 28)
          (SourceJson.white (fragment0080410Field003HeaderChars00 ++ (fragment0080758Chars ++ (fragment0080410Field003SuffixChars00 ++ tail)))) fragment0080410Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 28) (SourceJson.white s) fragment0080410Acc00300) hinput
    _ = (SourceJson.value (fuel + 27) (fragment0080758Chars ++ (fragment0080410Field003SuffixChars00 ++ tail))).bind
        (fragment0080410Field003AfterValue00 (fuel + 27)) := object_fragment0080410_field_003_header fuel (fragment0080758Chars ++ (fragment0080410Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0080758Value, fragment0080410Field003SuffixChars00 ++ tail)).bind (fragment0080410Field003AfterValue00 (fuel + 27)) :=
      congrArg (fun result => result.bind (fragment0080410Field003AfterValue00 (fuel + 27)))
        (value_fragment0080758 (fuel + 0) (fragment0080410Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0080410Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080410_object_field_003"
  err.flush

noncomputable def fragment0080410Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0080410Field004Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0080410Acc00500 : List (String × SourceJson) := (fragment0080410Field004Key00, fragment0080410Field004Value00) :: fragment0080410Acc00400
noncomputable def fragment0080410Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0080410_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0080410Field004Chars00 ++ tail)) fragment0080410Acc00400 =
      .ok (.obj (fragment0080410Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080410_object_field_004"
  err.flush

noncomputable def fragment0080410Chars : List Char := '{' :: (fragment0080410Field000Chars00 ++ fragment0080410Field001Chars00 ++ fragment0080410Field002Chars00 ++ fragment0080410Field003Chars00 ++ fragment0080410Field004Chars00)
noncomputable def fragment0080410Value : SourceJson := .obj (fragment0080410Acc00500.reverse)

theorem value_fragment0080410 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 32) (fragment0080410Chars ++ tail) =
      .ok (fragment0080410Value, tail) := by
  have hinput : fragment0080410Chars ++ tail = '{' :: (fragment0080410Field000Chars00 ++ (fragment0080410Field001Chars00 ++ (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0080410Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 32) (fragment0080410Chars ++ tail) =
        SourceJson.value (fuel + 32) ('{' :: (fragment0080410Field000Chars00 ++ (fragment0080410Field001Chars00 ++ (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 32)) hinput
    _ = SourceJson.object (fuel + 31) (SourceJson.white (fragment0080410Field000Chars00 ++ (fragment0080410Field001Chars00 ++ (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail))))))) fragment0080410Acc00000 := by rfl
    _ = SourceJson.object (fuel + 30) (SourceJson.white (fragment0080410Field001Chars00 ++ (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail)))))) fragment0080410Acc00100 := object_fragment0080410_field_000 fuel (fragment0080410Field001Chars00 ++ (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 29) (SourceJson.white (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail))))) fragment0080410Acc00200 := object_fragment0080410_field_001 fuel (fragment0080410Field002Chars00 ++ (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail)))) fragment0080410Acc00300 := object_fragment0080410_field_002 fuel (fragment0080410Field003Chars00 ++ (fragment0080410Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0080410Field004Chars00 ++ (tail))) fragment0080410Acc00400 := object_fragment0080410_field_003 fuel (fragment0080410Field004Chars00 ++ (tail))
    _ = .ok (fragment0080410Value, tail) := object_fragment0080410_field_004 fuel (tail)

noncomputable def fragment0083051Acc00000 : List SourceJson := []

noncomputable def fragment0083051Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083051Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]) :: (acc))

theorem array_fragment0083051_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0083051Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0083051Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0083051Acc00100 : List SourceJson := fragment0083051Chunk000Push00 fragment0083051Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083051_array_chunk_000"
  err.flush

noncomputable def fragment0083051Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083051Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]) :: (acc))

theorem array_fragment0083051_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0083051Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0083051Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0083051Acc00200 : List SourceJson := fragment0083051Chunk001Push00 fragment0083051Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083051_array_chunk_001"
  err.flush

noncomputable def fragment0083051Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0083051Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '1'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0083051_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0083051Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0083051Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0083051Acc00300 : List SourceJson := fragment0083051Chunk002Push00 fragment0083051Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083051_array_chunk_002"
  err.flush

noncomputable def fragment0083051Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0083051Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]) :: ((.arr [.number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]) :: (acc))

theorem array_fragment0083051_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0083051Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0083051Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0083051Acc00400 : List SourceJson := fragment0083051Chunk003Push00 fragment0083051Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0083051_array_chunk_003"
  err.flush

noncomputable def fragment0083051Chars : List Char := '[' :: (fragment0083051Chunk000Chars00 ++ fragment0083051Chunk001Chars00 ++ fragment0083051Chunk002Chars00 ++ fragment0083051Chunk003Chars00)
noncomputable def fragment0083051Value : SourceJson := .arr (fragment0083051Acc00400.reverse)

theorem value_fragment0083051 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0083051Chars ++ tail) =
      .ok (fragment0083051Value, tail) := by
  have hinput : fragment0083051Chars ++ tail = '[' :: (fragment0083051Chunk000Chars00 ++ (fragment0083051Chunk001Chars00 ++ (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0083051Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0083051Chars ++ tail) =
        SourceJson.value (fuel + 22) ('[' :: (fragment0083051Chunk000Chars00 ++ (fragment0083051Chunk001Chars00 ++ (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0083051Chunk000Chars00 ++ (fragment0083051Chunk001Chars00 ++ (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail)))))) fragment0083051Acc00000 := by rfl
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0083051Chunk001Chars00 ++ (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail))))) fragment0083051Acc00100 := array_fragment0083051_chunk_000 fuel (fragment0083051Chunk001Chars00 ++ (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail)))) fragment0083051Acc00000
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail)))) fragment0083051Acc00200 := array_fragment0083051_chunk_001 fuel (fragment0083051Chunk002Chars00 ++ (fragment0083051Chunk003Chars00 ++ (tail))) fragment0083051Acc00100
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0083051Chunk003Chars00 ++ (tail))) fragment0083051Acc00300 := array_fragment0083051_chunk_002 fuel (fragment0083051Chunk003Chars00 ++ (tail)) fragment0083051Acc00200
    _ = .ok (fragment0083051Value, tail) := array_fragment0083051_chunk_003 fuel (tail) fragment0083051Acc00300

noncomputable def fragment0082755Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0082755Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0082755Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1'])]
noncomputable def fragment0082755Acc00100 : List (String × SourceJson) := (fragment0082755Field000Key00, fragment0082755Field000Value00) :: fragment0082755Acc00000
noncomputable def fragment0082755Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0082755_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0082755Field000Chars00 ++ tail)) fragment0082755Acc00000 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0082755Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082755_object_field_000"
  err.flush

noncomputable def fragment0082755Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0082755Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0082755Acc00200 : List (String × SourceJson) := (fragment0082755Field001Key00, fragment0082755Field001Value00) :: fragment0082755Acc00100
noncomputable def fragment0082755Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0082755_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0082755Field001Chars00 ++ tail)) fragment0082755Acc00100 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0082755Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082755_object_field_001"
  err.flush

noncomputable def fragment0082755Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0082755Field002Value00 : SourceJson := .number (String.ofList ['2', '1'])
noncomputable def fragment0082755Acc00300 : List (String × SourceJson) := (fragment0082755Field002Key00, fragment0082755Field002Value00) :: fragment0082755Acc00200
noncomputable def fragment0082755Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '1', ',']

theorem object_fragment0082755_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0082755Field002Chars00 ++ tail)) fragment0082755Acc00200 =
      SourceJson.object (fuel + 23) (SourceJson.white tail) fragment0082755Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082755_object_field_002"
  err.flush

noncomputable def fragment0082755Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0082755Field003Value00 : SourceJson := fragment0083051Value
noncomputable def fragment0082755Acc00400 : List (String × SourceJson) := (fragment0082755Field003Key00, fragment0082755Field003Value00) :: fragment0082755Acc00300
noncomputable def fragment0082755Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0082755Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0082755Field003Chars00 : List Char := fragment0082755Field003HeaderChars00 ++ fragment0083051Chars ++ fragment0082755Field003SuffixChars00

noncomputable def fragment0082755Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0082755Field003Key00, result.1) :: fragment0082755Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0082755Field003Key00, result.1) :: fragment0082755Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0082755_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0082755Field003HeaderChars00 ++ rest)) fragment0082755Acc00300 =
      (SourceJson.value (fuel + 22) rest).bind (fragment0082755Field003AfterValue00 (fuel + 22)) := by rfl

theorem object_fragment0082755_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0082755Field003Chars00 ++ tail)) fragment0082755Acc00300 =
      SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0082755Acc00400 := by
  have hinput : fragment0082755Field003Chars00 ++ tail = fragment0082755Field003HeaderChars00 ++ (fragment0083051Chars ++ (fragment0082755Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0082755Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 23) (SourceJson.white (fragment0082755Field003Chars00 ++ tail)) fragment0082755Acc00300 =
        SourceJson.object (fuel + 23)
          (SourceJson.white (fragment0082755Field003HeaderChars00 ++ (fragment0083051Chars ++ (fragment0082755Field003SuffixChars00 ++ tail)))) fragment0082755Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 23) (SourceJson.white s) fragment0082755Acc00300) hinput
    _ = (SourceJson.value (fuel + 22) (fragment0083051Chars ++ (fragment0082755Field003SuffixChars00 ++ tail))).bind
        (fragment0082755Field003AfterValue00 (fuel + 22)) := object_fragment0082755_field_003_header fuel (fragment0083051Chars ++ (fragment0082755Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0083051Value, fragment0082755Field003SuffixChars00 ++ tail)).bind (fragment0082755Field003AfterValue00 (fuel + 22)) :=
      congrArg (fun result => result.bind (fragment0082755Field003AfterValue00 (fuel + 22)))
        (value_fragment0083051 (fuel + 0) (fragment0082755Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 22) (SourceJson.white tail) fragment0082755Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082755_object_field_003"
  err.flush

noncomputable def fragment0082755Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0082755Field004Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0082755Acc00500 : List (String × SourceJson) := (fragment0082755Field004Key00, fragment0082755Field004Value00) :: fragment0082755Acc00400
noncomputable def fragment0082755Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0082755_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0082755Field004Chars00 ++ tail)) fragment0082755Acc00400 =
      .ok (.obj (fragment0082755Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0082755_object_field_004"
  err.flush

noncomputable def fragment0082755Chars : List Char := '{' :: (fragment0082755Field000Chars00 ++ fragment0082755Field001Chars00 ++ fragment0082755Field002Chars00 ++ fragment0082755Field003Chars00 ++ fragment0082755Field004Chars00)
noncomputable def fragment0082755Value : SourceJson := .obj (fragment0082755Acc00500.reverse)

theorem value_fragment0082755 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 27) (fragment0082755Chars ++ tail) =
      .ok (fragment0082755Value, tail) := by
  have hinput : fragment0082755Chars ++ tail = '{' :: (fragment0082755Field000Chars00 ++ (fragment0082755Field001Chars00 ++ (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0082755Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 27) (fragment0082755Chars ++ tail) =
        SourceJson.value (fuel + 27) ('{' :: (fragment0082755Field000Chars00 ++ (fragment0082755Field001Chars00 ++ (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 27)) hinput
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0082755Field000Chars00 ++ (fragment0082755Field001Chars00 ++ (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail))))))) fragment0082755Acc00000 := by rfl
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0082755Field001Chars00 ++ (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail)))))) fragment0082755Acc00100 := object_fragment0082755_field_000 fuel (fragment0082755Field001Chars00 ++ (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail))))) fragment0082755Acc00200 := object_fragment0082755_field_001 fuel (fragment0082755Field002Chars00 ++ (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 23) (SourceJson.white (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail)))) fragment0082755Acc00300 := object_fragment0082755_field_002 fuel (fragment0082755Field003Chars00 ++ (fragment0082755Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0082755Field004Chars00 ++ (tail))) fragment0082755Acc00400 := object_fragment0082755_field_003 fuel (fragment0082755Field004Chars00 ++ (tail))
    _ = .ok (fragment0082755Value, tail) := object_fragment0082755_field_004 fuel (tail)

noncomputable def fragment0085644Acc00000 : List SourceJson := []

noncomputable def fragment0085644Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0085644Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]) :: (acc))

theorem array_fragment0085644_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 16) (SourceJson.white (fragment0085644Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 14) (SourceJson.white tail) (fragment0085644Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0085644Acc00100 : List SourceJson := fragment0085644Chunk000Push00 fragment0085644Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085644_array_chunk_000"
  err.flush

noncomputable def fragment0085644Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0085644Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]) :: (acc))

theorem array_fragment0085644_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 14) (SourceJson.white (fragment0085644Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 12) (SourceJson.white tail) (fragment0085644Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0085644Acc00200 : List SourceJson := fragment0085644Chunk001Push00 fragment0085644Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085644_array_chunk_001"
  err.flush

noncomputable def fragment0085644Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0085644Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: (acc))

theorem array_fragment0085644_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 12) (SourceJson.white (fragment0085644Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 10) (SourceJson.white tail) (fragment0085644Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0085644Acc00300 : List SourceJson := fragment0085644Chunk002Push00 fragment0085644Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085644_array_chunk_002"
  err.flush

noncomputable def fragment0085644Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0085644Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]) :: (acc)

theorem array_fragment0085644_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 10) (SourceJson.white (fragment0085644Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0085644Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0085644Acc00400 : List SourceJson := fragment0085644Chunk003Push00 fragment0085644Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085644_array_chunk_003"
  err.flush

noncomputable def fragment0085644Chars : List Char := '[' :: (fragment0085644Chunk000Chars00 ++ fragment0085644Chunk001Chars00 ++ fragment0085644Chunk002Chars00 ++ fragment0085644Chunk003Chars00)
noncomputable def fragment0085644Value : SourceJson := .arr (fragment0085644Acc00400.reverse)

theorem value_fragment0085644 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 17) (fragment0085644Chars ++ tail) =
      .ok (fragment0085644Value, tail) := by
  have hinput : fragment0085644Chars ++ tail = '[' :: (fragment0085644Chunk000Chars00 ++ (fragment0085644Chunk001Chars00 ++ (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0085644Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 17) (fragment0085644Chars ++ tail) =
        SourceJson.value (fuel + 17) ('[' :: (fragment0085644Chunk000Chars00 ++ (fragment0085644Chunk001Chars00 ++ (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 17)) hinput
    _ = SourceJson.array (fuel + 16) (SourceJson.white (fragment0085644Chunk000Chars00 ++ (fragment0085644Chunk001Chars00 ++ (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail)))))) fragment0085644Acc00000 := by rfl
    _ = SourceJson.array (fuel + 14) (SourceJson.white (fragment0085644Chunk001Chars00 ++ (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail))))) fragment0085644Acc00100 := array_fragment0085644_chunk_000 fuel (fragment0085644Chunk001Chars00 ++ (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail)))) fragment0085644Acc00000
    _ = SourceJson.array (fuel + 12) (SourceJson.white (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail)))) fragment0085644Acc00200 := array_fragment0085644_chunk_001 fuel (fragment0085644Chunk002Chars00 ++ (fragment0085644Chunk003Chars00 ++ (tail))) fragment0085644Acc00100
    _ = SourceJson.array (fuel + 10) (SourceJson.white (fragment0085644Chunk003Chars00 ++ (tail))) fragment0085644Acc00300 := array_fragment0085644_chunk_002 fuel (fragment0085644Chunk003Chars00 ++ (tail)) fragment0085644Acc00200
    _ = .ok (fragment0085644Value, tail) := array_fragment0085644_chunk_003 fuel (tail) fragment0085644Acc00300

noncomputable def fragment0085398Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0085398Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0085398Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9'])]
noncomputable def fragment0085398Acc00100 : List (String × SourceJson) := (fragment0085398Field000Key00, fragment0085398Field000Value00) :: fragment0085398Acc00000
noncomputable def fragment0085398Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0085398_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0085398Field000Chars00 ++ tail)) fragment0085398Acc00000 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0085398Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085398_object_field_000"
  err.flush

noncomputable def fragment0085398Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0085398Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0085398Acc00200 : List (String × SourceJson) := (fragment0085398Field001Key00, fragment0085398Field001Value00) :: fragment0085398Acc00100
noncomputable def fragment0085398Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0085398_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0085398Field001Chars00 ++ tail)) fragment0085398Acc00100 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0085398Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085398_object_field_001"
  err.flush

noncomputable def fragment0085398Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0085398Field002Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0085398Acc00300 : List (String × SourceJson) := (fragment0085398Field002Key00, fragment0085398Field002Value00) :: fragment0085398Acc00200
noncomputable def fragment0085398Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '9', ',']

theorem object_fragment0085398_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0085398Field002Chars00 ++ tail)) fragment0085398Acc00200 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0085398Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085398_object_field_002"
  err.flush

noncomputable def fragment0085398Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0085398Field003Value00 : SourceJson := fragment0085644Value
noncomputable def fragment0085398Acc00400 : List (String × SourceJson) := (fragment0085398Field003Key00, fragment0085398Field003Value00) :: fragment0085398Acc00300
noncomputable def fragment0085398Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0085398Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0085398Field003Chars00 : List Char := fragment0085398Field003HeaderChars00 ++ fragment0085644Chars ++ fragment0085398Field003SuffixChars00

noncomputable def fragment0085398Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0085398Field003Key00, result.1) :: fragment0085398Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0085398Field003Key00, result.1) :: fragment0085398Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0085398_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0085398Field003HeaderChars00 ++ rest)) fragment0085398Acc00300 =
      (SourceJson.value (fuel + 17) rest).bind (fragment0085398Field003AfterValue00 (fuel + 17)) := by rfl

theorem object_fragment0085398_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0085398Field003Chars00 ++ tail)) fragment0085398Acc00300 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0085398Acc00400 := by
  have hinput : fragment0085398Field003Chars00 ++ tail = fragment0085398Field003HeaderChars00 ++ (fragment0085644Chars ++ (fragment0085398Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0085398Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0085398Field003Chars00 ++ tail)) fragment0085398Acc00300 =
        SourceJson.object (fuel + 18)
          (SourceJson.white (fragment0085398Field003HeaderChars00 ++ (fragment0085644Chars ++ (fragment0085398Field003SuffixChars00 ++ tail)))) fragment0085398Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 18) (SourceJson.white s) fragment0085398Acc00300) hinput
    _ = (SourceJson.value (fuel + 17) (fragment0085644Chars ++ (fragment0085398Field003SuffixChars00 ++ tail))).bind
        (fragment0085398Field003AfterValue00 (fuel + 17)) := object_fragment0085398_field_003_header fuel (fragment0085644Chars ++ (fragment0085398Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0085644Value, fragment0085398Field003SuffixChars00 ++ tail)).bind (fragment0085398Field003AfterValue00 (fuel + 17)) :=
      congrArg (fun result => result.bind (fragment0085398Field003AfterValue00 (fuel + 17)))
        (value_fragment0085644 (fuel + 0) (fragment0085398Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0085398Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085398_object_field_003"
  err.flush

noncomputable def fragment0085398Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0085398Field004Value00 : SourceJson := .number (String.ofList ['1', '2'])
noncomputable def fragment0085398Acc00500 : List (String × SourceJson) := (fragment0085398Field004Key00, fragment0085398Field004Value00) :: fragment0085398Acc00400
noncomputable def fragment0085398Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0085398_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0085398Field004Chars00 ++ tail)) fragment0085398Acc00400 =
      .ok (.obj (fragment0085398Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0085398_object_field_004"
  err.flush

noncomputable def fragment0085398Chars : List Char := '{' :: (fragment0085398Field000Chars00 ++ fragment0085398Field001Chars00 ++ fragment0085398Field002Chars00 ++ fragment0085398Field003Chars00 ++ fragment0085398Field004Chars00)
noncomputable def fragment0085398Value : SourceJson := .obj (fragment0085398Acc00500.reverse)

theorem value_fragment0085398 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 22) (fragment0085398Chars ++ tail) =
      .ok (fragment0085398Value, tail) := by
  have hinput : fragment0085398Chars ++ tail = '{' :: (fragment0085398Field000Chars00 ++ (fragment0085398Field001Chars00 ++ (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0085398Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 22) (fragment0085398Chars ++ tail) =
        SourceJson.value (fuel + 22) ('{' :: (fragment0085398Field000Chars00 ++ (fragment0085398Field001Chars00 ++ (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 22)) hinput
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0085398Field000Chars00 ++ (fragment0085398Field001Chars00 ++ (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail))))))) fragment0085398Acc00000 := by rfl
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0085398Field001Chars00 ++ (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail)))))) fragment0085398Acc00100 := object_fragment0085398_field_000 fuel (fragment0085398Field001Chars00 ++ (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail))))) fragment0085398Acc00200 := object_fragment0085398_field_001 fuel (fragment0085398Field002Chars00 ++ (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail)))) fragment0085398Acc00300 := object_fragment0085398_field_002 fuel (fragment0085398Field003Chars00 ++ (fragment0085398Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0085398Field004Chars00 ++ (tail))) fragment0085398Acc00400 := object_fragment0085398_field_003 fuel (fragment0085398Field004Chars00 ++ (tail))
    _ = .ok (fragment0085398Value, tail) := object_fragment0085398_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0008_before_reader"
  err.flush

noncomputable def chunk0008LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0008SuffixChars00 : List Char := [',']
noncomputable def chunk0008Chars00 : List Char := chunk0008LeadChars00 ++ fragment0079282Chars ++ chunk0008SuffixChars00
noncomputable def chunk0008Push00 (acc : List SourceJson) : List SourceJson := fragment0079282Value :: acc

noncomputable def chunk0008AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0008_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52)
      (SourceJson.white (chunk0008LeadChars00 ++ (fragment0079282Chars ++ rest))) acc =
      (SourceJson.value (fuel + 51) (fragment0079282Chars ++ rest)).bind
        (chunk0008AfterValue00 (fuel + 51) acc) := by rfl

theorem array_chunk0008 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 51) (SourceJson.white tail) (chunk0008Push00 acc) := by
  have hinput : chunk0008Chars00 ++ tail = chunk0008LeadChars00 ++ (fragment0079282Chars ++ (chunk0008SuffixChars00 ++ tail)) := by
    simp only [chunk0008Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 52) (SourceJson.white (chunk0008Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 52)
          (SourceJson.white (chunk0008LeadChars00 ++ (fragment0079282Chars ++ (chunk0008SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 52) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 51) (fragment0079282Chars ++ (chunk0008SuffixChars00 ++ tail))).bind
        (chunk0008AfterValue00 (fuel + 51) acc) := array_chunk0008_head fuel (chunk0008SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0079282Value, chunk0008SuffixChars00 ++ tail)).bind
        (chunk0008AfterValue00 (fuel + 51) acc) :=
      congrArg (fun result => result.bind (chunk0008AfterValue00 (fuel + 51) acc))
        (value_fragment0079282 (fuel + 28) (chunk0008SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 51) (SourceJson.white tail) (chunk0008Push00 acc) := by rfl

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
noncomputable def chunk0009Chars00 : List Char := chunk0009LeadChars00 ++ fragment0080410Chars ++ chunk0009SuffixChars00
noncomputable def chunk0009Push00 (acc : List SourceJson) : List SourceJson := fragment0080410Value :: acc

noncomputable def chunk0009AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0009_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51)
      (SourceJson.white (chunk0009LeadChars00 ++ (fragment0080410Chars ++ rest))) acc =
      (SourceJson.value (fuel + 50) (fragment0080410Chars ++ rest)).bind
        (chunk0009AfterValue00 (fuel + 50) acc) := by rfl

theorem array_chunk0009 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 51) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (chunk0009Push00 acc) := by
  have hinput : chunk0009Chars00 ++ tail = chunk0009LeadChars00 ++ (fragment0080410Chars ++ (chunk0009SuffixChars00 ++ tail)) := by
    simp only [chunk0009Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 51) (SourceJson.white (chunk0009Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 51)
          (SourceJson.white (chunk0009LeadChars00 ++ (fragment0080410Chars ++ (chunk0009SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 51) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 50) (fragment0080410Chars ++ (chunk0009SuffixChars00 ++ tail))).bind
        (chunk0009AfterValue00 (fuel + 50) acc) := array_chunk0009_head fuel (chunk0009SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0080410Value, chunk0009SuffixChars00 ++ tail)).bind
        (chunk0009AfterValue00 (fuel + 50) acc) :=
      congrArg (fun result => result.bind (chunk0009AfterValue00 (fuel + 50) acc))
        (value_fragment0080410 (fuel + 18) (chunk0009SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 50) (SourceJson.white tail) (chunk0009Push00 acc) := by rfl

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
noncomputable def chunk0010Chars00 : List Char := chunk0010LeadChars00 ++ fragment0082755Chars ++ chunk0010SuffixChars00
noncomputable def chunk0010Push00 (acc : List SourceJson) : List SourceJson := fragment0082755Value :: acc

noncomputable def chunk0010AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0010_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50)
      (SourceJson.white (chunk0010LeadChars00 ++ (fragment0082755Chars ++ rest))) acc =
      (SourceJson.value (fuel + 49) (fragment0082755Chars ++ rest)).bind
        (chunk0010AfterValue00 (fuel + 49) acc) := by rfl

theorem array_chunk0010 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (chunk0010Push00 acc) := by
  have hinput : chunk0010Chars00 ++ tail = chunk0010LeadChars00 ++ (fragment0082755Chars ++ (chunk0010SuffixChars00 ++ tail)) := by
    simp only [chunk0010Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 50) (SourceJson.white (chunk0010Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 50)
          (SourceJson.white (chunk0010LeadChars00 ++ (fragment0082755Chars ++ (chunk0010SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 50) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 49) (fragment0082755Chars ++ (chunk0010SuffixChars00 ++ tail))).bind
        (chunk0010AfterValue00 (fuel + 49) acc) := array_chunk0010_head fuel (chunk0010SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0082755Value, chunk0010SuffixChars00 ++ tail)).bind
        (chunk0010AfterValue00 (fuel + 49) acc) :=
      congrArg (fun result => result.bind (chunk0010AfterValue00 (fuel + 49) acc))
        (value_fragment0082755 (fuel + 22) (chunk0010SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 49) (SourceJson.white tail) (chunk0010Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0010_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_before_reader"
  err.flush

noncomputable def chunk0011Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0011Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc)

theorem array_chunk0011 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49) (SourceJson.white (chunk0011Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (chunk0011Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0011_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_before_reader"
  err.flush

noncomputable def chunk0012Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0012Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['6']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0012 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48) (SourceJson.white (chunk0012Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (chunk0012Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0012_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_before_reader"
  err.flush

noncomputable def chunk0013LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0013SuffixChars00 : List Char := [',']
noncomputable def chunk0013Chars00 : List Char := chunk0013LeadChars00 ++ fragment0085398Chars ++ chunk0013SuffixChars00
noncomputable def chunk0013Push00 (acc : List SourceJson) : List SourceJson := fragment0085398Value :: acc

noncomputable def chunk0013AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0013_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47)
      (SourceJson.white (chunk0013LeadChars00 ++ (fragment0085398Chars ++ rest))) acc =
      (SourceJson.value (fuel + 46) (fragment0085398Chars ++ rest)).bind
        (chunk0013AfterValue00 (fuel + 46) acc) := by rfl

theorem array_chunk0013 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 46) (SourceJson.white tail) (chunk0013Push00 acc) := by
  have hinput : chunk0013Chars00 ++ tail = chunk0013LeadChars00 ++ (fragment0085398Chars ++ (chunk0013SuffixChars00 ++ tail)) := by
    simp only [chunk0013Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 47) (SourceJson.white (chunk0013Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 47)
          (SourceJson.white (chunk0013LeadChars00 ++ (fragment0085398Chars ++ (chunk0013SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 47) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 46) (fragment0085398Chars ++ (chunk0013SuffixChars00 ++ tail))).bind
        (chunk0013AfterValue00 (fuel + 46) acc) := array_chunk0013_head fuel (chunk0013SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0085398Value, chunk0013SuffixChars00 ++ tail)).bind
        (chunk0013AfterValue00 (fuel + 46) acc) :=
      congrArg (fun result => result.bind (chunk0013AfterValue00 (fuel + 46) acc))
        (value_fragment0085398 (fuel + 24) (chunk0013SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 46) (SourceJson.white tail) (chunk0013Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0013_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_before_reader"
  err.flush

noncomputable def chunk0014Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0014Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '7'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['5']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '7'])], .arr [.number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5'])], .arr [.number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['6']))]) :: (acc)

theorem array_chunk0014 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 46) (SourceJson.white (chunk0014Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (chunk0014Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0014_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_before_reader"
  err.flush

noncomputable def chunk0015Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0015Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['2']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0015 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 45) (SourceJson.white (chunk0015Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (chunk0015Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0015_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0008Chars00 ++ chunk0009Chars00 ++ chunk0010Chars00 ++ chunk0011Chars00 ++ chunk0012Chars00 ++ chunk0013Chars00 ++ chunk0014Chars00 ++ chunk0015Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0015Push00 (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 52) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 52) (SourceJson.white (chunk0008Chars00 ++ (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 52) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 51) (SourceJson.white (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))))) (chunk0008Push00 (acc)) := array_chunk0008 fuel (chunk0009Chars00 ++ (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 50) (SourceJson.white (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))))) (chunk0009Push00 (chunk0008Push00 (acc))) := array_chunk0009 fuel (chunk0010Chars00 ++ (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0008Push00 (acc))
    _ = SourceJson.array (fuel + 49) (SourceJson.white (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))) := array_chunk0010 fuel (chunk0011Chars00 ++ (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0009Push00 (chunk0008Push00 (acc)))
    _ = SourceJson.array (fuel + 48) (SourceJson.white (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))) := array_chunk0011 fuel (chunk0012Chars00 ++ (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))
    _ = SourceJson.array (fuel + 47) (SourceJson.white (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))) := array_chunk0012 fuel (chunk0013Chars00 ++ (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))
    _ = SourceJson.array (fuel + 46) (SourceJson.white (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail)))) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))) := array_chunk0013 fuel (chunk0014Chars00 ++ (chunk0015Chars00 ++ (tail))) (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))
    _ = SourceJson.array (fuel + 45) (SourceJson.white (chunk0015Chars00 ++ (tail))) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))) := array_chunk0014 fuel (chunk0015Chars00 ++ (tail)) (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc)))))))
    _ = SourceJson.array (fuel + 43) (SourceJson.white tail) (blockPush acc) := array_chunk0015 fuel (tail) (chunk0014Push00 (chunk0013Push00 (chunk0012Push00 (chunk0011Push00 (chunk0010Push00 (chunk0009Push00 (chunk0008Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 79276).take 8545 = blockChars := by rfl

theorem block_original_split : sourceRest 79276 = blockChars ++ sourceRest 87821 := by
  calc
    sourceRest 79276 = (sourceRest 79276).take 8545 ++ (sourceRest 79276).drop 8545 :=
      (List.take_append_drop 8545 (sourceRest 79276)).symm
    _ = blockChars ++ (sourceRest 79276).drop 8545 :=
      congrArg (fun part => part ++ (sourceRest 79276).drop 8545) block_original_prefix
    _ = blockChars ++ sourceRest 87821 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 79276 8545)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (sourceRest 79276)) acc =
      SourceJson.array (fuel + 43) (SourceJson.white (sourceRest 87821)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 52) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 87821) acc)

#print axioms array_fragment0079500_chunk_000
#print axioms array_fragment0079500_chunk_001
#print axioms array_fragment0079500_chunk_002
#print axioms array_fragment0079500_chunk_003
#print axioms value_fragment0079500
#print axioms object_fragment0079282_field_000
#print axioms object_fragment0079282_field_001
#print axioms object_fragment0079282_field_002
#print axioms object_fragment0079282_field_003_header
#print axioms object_fragment0079282_field_003
#print axioms object_fragment0079282_field_004
#print axioms value_fragment0079282
#print axioms array_fragment0080758_chunk_000
#print axioms array_fragment0080758_chunk_001
#print axioms array_fragment0080758_chunk_002
#print axioms array_fragment0080758_chunk_003
#print axioms array_fragment0080758_chunk_004
#print axioms value_fragment0080758
#print axioms object_fragment0080410_field_000
#print axioms object_fragment0080410_field_001
#print axioms object_fragment0080410_field_002
#print axioms object_fragment0080410_field_003_header
#print axioms object_fragment0080410_field_003
#print axioms object_fragment0080410_field_004
#print axioms value_fragment0080410
#print axioms array_fragment0083051_chunk_000
#print axioms array_fragment0083051_chunk_001
#print axioms array_fragment0083051_chunk_002
#print axioms array_fragment0083051_chunk_003
#print axioms value_fragment0083051
#print axioms object_fragment0082755_field_000
#print axioms object_fragment0082755_field_001
#print axioms object_fragment0082755_field_002
#print axioms object_fragment0082755_field_003_header
#print axioms object_fragment0082755_field_003
#print axioms object_fragment0082755_field_004
#print axioms value_fragment0082755
#print axioms array_fragment0085644_chunk_000
#print axioms array_fragment0085644_chunk_001
#print axioms array_fragment0085644_chunk_002
#print axioms array_fragment0085644_chunk_003
#print axioms value_fragment0085644
#print axioms object_fragment0085398_field_000
#print axioms object_fragment0085398_field_001
#print axioms object_fragment0085398_field_002
#print axioms object_fragment0085398_field_003_header
#print axioms object_fragment0085398_field_003
#print axioms object_fragment0085398_field_004
#print axioms value_fragment0085398
#print axioms array_chunk0008_head
#print axioms array_chunk0008
#print axioms array_chunk0009_head
#print axioms array_chunk0009
#print axioms array_chunk0010_head
#print axioms array_chunk0010
#print axioms array_chunk0011
#print axioms array_chunk0012
#print axioms array_chunk0013_head
#print axioms array_chunk0013
#print axioms array_chunk0014
#print axioms array_chunk0015
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock001

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
