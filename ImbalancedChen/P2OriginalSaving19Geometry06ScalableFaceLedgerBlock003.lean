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

namespace FaceLedgerBlock003

noncomputable def fragment0103843Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0103843Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0103843Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]
noncomputable def fragment0103843Acc00100 : List (String × SourceJson) := (fragment0103843Field000Key00, fragment0103843Field000Value00) :: fragment0103843Acc00000
noncomputable def fragment0103843Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0103843_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0103843Field000Chars00 ++ tail)) fragment0103843Acc00000 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0103843Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0103843_object_field_000"
  err.flush

noncomputable def fragment0103843Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0103843Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0103843Acc00200 : List (String × SourceJson) := (fragment0103843Field001Key00, fragment0103843Field001Value00) :: fragment0103843Acc00100
noncomputable def fragment0103843Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0103843_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0103843Field001Chars00 ++ tail)) fragment0103843Acc00100 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0103843Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0103843_object_field_001"
  err.flush

noncomputable def fragment0103843Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0103843Field002Value00 : SourceJson := .number (String.ofList ['2', '3'])
noncomputable def fragment0103843Acc00300 : List (String × SourceJson) := (fragment0103843Field002Key00, fragment0103843Field002Value00) :: fragment0103843Acc00200
noncomputable def fragment0103843Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '3', ',']

theorem object_fragment0103843_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0103843Field002Chars00 ++ tail)) fragment0103843Acc00200 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0103843Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0103843_object_field_002"
  err.flush

noncomputable def fragment0103843Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0103843Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3'])]]
noncomputable def fragment0103843Acc00400 : List (String × SourceJson) := (fragment0103843Field003Key00, fragment0103843Field003Value00) :: fragment0103843Acc00300
noncomputable def fragment0103843Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0103843_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0103843Field003Chars00 ++ tail)) fragment0103843Acc00300 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0103843Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0103843_object_field_003"
  err.flush

noncomputable def fragment0103843Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0103843Field004Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0103843Acc00500 : List (String × SourceJson) := (fragment0103843Field004Key00, fragment0103843Field004Value00) :: fragment0103843Acc00400
noncomputable def fragment0103843Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0103843_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0103843Field004Chars00 ++ tail)) fragment0103843Acc00400 =
      .ok (.obj (fragment0103843Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0103843_object_field_004"
  err.flush

noncomputable def fragment0103843Chars : List Char := '{' :: (fragment0103843Field000Chars00 ++ fragment0103843Field001Chars00 ++ fragment0103843Field002Chars00 ++ fragment0103843Field003Chars00 ++ fragment0103843Field004Chars00)
noncomputable def fragment0103843Value : SourceJson := .obj (fragment0103843Acc00500.reverse)

theorem value_fragment0103843 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 20) (fragment0103843Chars ++ tail) =
      .ok (fragment0103843Value, tail) := by
  have hinput : fragment0103843Chars ++ tail = '{' :: (fragment0103843Field000Chars00 ++ (fragment0103843Field001Chars00 ++ (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0103843Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 20) (fragment0103843Chars ++ tail) =
        SourceJson.value (fuel + 20) ('{' :: (fragment0103843Field000Chars00 ++ (fragment0103843Field001Chars00 ++ (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 20)) hinput
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0103843Field000Chars00 ++ (fragment0103843Field001Chars00 ++ (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail))))))) fragment0103843Acc00000 := by rfl
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0103843Field001Chars00 ++ (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail)))))) fragment0103843Acc00100 := object_fragment0103843_field_000 fuel (fragment0103843Field001Chars00 ++ (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail))))) fragment0103843Acc00200 := object_fragment0103843_field_001 fuel (fragment0103843Field002Chars00 ++ (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail)))) fragment0103843Acc00300 := object_fragment0103843_field_002 fuel (fragment0103843Field003Chars00 ++ (fragment0103843Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0103843Field004Chars00 ++ (tail))) fragment0103843Acc00400 := object_fragment0103843_field_003 fuel (fragment0103843Field004Chars00 ++ (tail))
    _ = .ok (fragment0103843Value, tail) := object_fragment0103843_field_004 fuel (tail)

noncomputable def fragment0105970Acc00000 : List SourceJson := []

noncomputable def fragment0105970Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0105970Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]) :: (acc))

theorem array_fragment0105970_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0105970Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0105970Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0105970Acc00100 : List SourceJson := fragment0105970Chunk000Push00 fragment0105970Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105970_array_chunk_000"
  err.flush

noncomputable def fragment0105970Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0105970Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '5'])]) :: (acc))

theorem array_fragment0105970_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0105970Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0105970Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0105970Acc00200 : List SourceJson := fragment0105970Chunk001Push00 fragment0105970Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105970_array_chunk_001"
  err.flush

noncomputable def fragment0105970Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0105970Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: ((.arr [.number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4'])]) :: (acc))

theorem array_fragment0105970_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0105970Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0105970Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0105970Acc00300 : List SourceJson := fragment0105970Chunk002Push00 fragment0105970Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105970_array_chunk_002"
  err.flush

noncomputable def fragment0105970Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0105970Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]) :: (acc)

theorem array_fragment0105970_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0105970Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0105970Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0105970Acc00400 : List SourceJson := fragment0105970Chunk003Push00 fragment0105970Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105970_array_chunk_003"
  err.flush

noncomputable def fragment0105970Chars : List Char := '[' :: (fragment0105970Chunk000Chars00 ++ fragment0105970Chunk001Chars00 ++ fragment0105970Chunk002Chars00 ++ fragment0105970Chunk003Chars00)
noncomputable def fragment0105970Value : SourceJson := .arr (fragment0105970Acc00400.reverse)

theorem value_fragment0105970 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 18) (fragment0105970Chars ++ tail) =
      .ok (fragment0105970Value, tail) := by
  have hinput : fragment0105970Chars ++ tail = '[' :: (fragment0105970Chunk000Chars00 ++ (fragment0105970Chunk001Chars00 ++ (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0105970Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 18) (fragment0105970Chars ++ tail) =
        SourceJson.value (fuel + 18) ('[' :: (fragment0105970Chunk000Chars00 ++ (fragment0105970Chunk001Chars00 ++ (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 18)) hinput
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0105970Chunk000Chars00 ++ (fragment0105970Chunk001Chars00 ++ (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail)))))) fragment0105970Acc00000 := by rfl
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0105970Chunk001Chars00 ++ (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail))))) fragment0105970Acc00100 := array_fragment0105970_chunk_000 fuel (fragment0105970Chunk001Chars00 ++ (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail)))) fragment0105970Acc00000
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail)))) fragment0105970Acc00200 := array_fragment0105970_chunk_001 fuel (fragment0105970Chunk002Chars00 ++ (fragment0105970Chunk003Chars00 ++ (tail))) fragment0105970Acc00100
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0105970Chunk003Chars00 ++ (tail))) fragment0105970Acc00300 := array_fragment0105970_chunk_002 fuel (fragment0105970Chunk003Chars00 ++ (tail)) fragment0105970Acc00200
    _ = .ok (fragment0105970Value, tail) := array_fragment0105970_chunk_003 fuel (tail) fragment0105970Acc00300

noncomputable def fragment0105711Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0105711Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0105711Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5'])]
noncomputable def fragment0105711Acc00100 : List (String × SourceJson) := (fragment0105711Field000Key00, fragment0105711Field000Value00) :: fragment0105711Acc00000
noncomputable def fragment0105711Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0105711_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 22) (SourceJson.white (fragment0105711Field000Chars00 ++ tail)) fragment0105711Acc00000 =
      SourceJson.object (fuel + 21) (SourceJson.white tail) fragment0105711Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105711_object_field_000"
  err.flush

noncomputable def fragment0105711Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0105711Field001Value00 : SourceJson := .number (String.ofList ['4'])
noncomputable def fragment0105711Acc00200 : List (String × SourceJson) := (fragment0105711Field001Key00, fragment0105711Field001Value00) :: fragment0105711Acc00100
noncomputable def fragment0105711Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',']

theorem object_fragment0105711_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 21) (SourceJson.white (fragment0105711Field001Chars00 ++ tail)) fragment0105711Acc00100 =
      SourceJson.object (fuel + 20) (SourceJson.white tail) fragment0105711Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105711_object_field_001"
  err.flush

noncomputable def fragment0105711Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0105711Field002Value00 : SourceJson := .number (String.ofList ['2', '5'])
noncomputable def fragment0105711Acc00300 : List (String × SourceJson) := (fragment0105711Field002Key00, fragment0105711Field002Value00) :: fragment0105711Acc00200
noncomputable def fragment0105711Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '5', ',']

theorem object_fragment0105711_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0105711Field002Chars00 ++ tail)) fragment0105711Acc00200 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0105711Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105711_object_field_002"
  err.flush

noncomputable def fragment0105711Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0105711Field003Value00 : SourceJson := fragment0105970Value
noncomputable def fragment0105711Acc00400 : List (String × SourceJson) := (fragment0105711Field003Key00, fragment0105711Field003Value00) :: fragment0105711Acc00300
noncomputable def fragment0105711Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0105711Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0105711Field003Chars00 : List Char := fragment0105711Field003HeaderChars00 ++ fragment0105970Chars ++ fragment0105711Field003SuffixChars00

noncomputable def fragment0105711Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0105711Field003Key00, result.1) :: fragment0105711Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0105711Field003Key00, result.1) :: fragment0105711Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0105711_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0105711Field003HeaderChars00 ++ rest)) fragment0105711Acc00300 =
      (SourceJson.value (fuel + 18) rest).bind (fragment0105711Field003AfterValue00 (fuel + 18)) := by rfl

theorem object_fragment0105711_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0105711Field003Chars00 ++ tail)) fragment0105711Acc00300 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0105711Acc00400 := by
  have hinput : fragment0105711Field003Chars00 ++ tail = fragment0105711Field003HeaderChars00 ++ (fragment0105970Chars ++ (fragment0105711Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0105711Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0105711Field003Chars00 ++ tail)) fragment0105711Acc00300 =
        SourceJson.object (fuel + 19)
          (SourceJson.white (fragment0105711Field003HeaderChars00 ++ (fragment0105970Chars ++ (fragment0105711Field003SuffixChars00 ++ tail)))) fragment0105711Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 19) (SourceJson.white s) fragment0105711Acc00300) hinput
    _ = (SourceJson.value (fuel + 18) (fragment0105970Chars ++ (fragment0105711Field003SuffixChars00 ++ tail))).bind
        (fragment0105711Field003AfterValue00 (fuel + 18)) := object_fragment0105711_field_003_header fuel (fragment0105970Chars ++ (fragment0105711Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0105970Value, fragment0105711Field003SuffixChars00 ++ tail)).bind (fragment0105711Field003AfterValue00 (fuel + 18)) :=
      congrArg (fun result => result.bind (fragment0105711Field003AfterValue00 (fuel + 18)))
        (value_fragment0105970 (fuel + 0) (fragment0105711Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0105711Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105711_object_field_003"
  err.flush

noncomputable def fragment0105711Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0105711Field004Value00 : SourceJson := .number (String.ofList ['1', '4'])
noncomputable def fragment0105711Acc00500 : List (String × SourceJson) := (fragment0105711Field004Key00, fragment0105711Field004Value00) :: fragment0105711Acc00400
noncomputable def fragment0105711Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0105711_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0105711Field004Chars00 ++ tail)) fragment0105711Acc00400 =
      .ok (.obj (fragment0105711Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0105711_object_field_004"
  err.flush

noncomputable def fragment0105711Chars : List Char := '{' :: (fragment0105711Field000Chars00 ++ fragment0105711Field001Chars00 ++ fragment0105711Field002Chars00 ++ fragment0105711Field003Chars00 ++ fragment0105711Field004Chars00)
noncomputable def fragment0105711Value : SourceJson := .obj (fragment0105711Acc00500.reverse)

theorem value_fragment0105711 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 23) (fragment0105711Chars ++ tail) =
      .ok (fragment0105711Value, tail) := by
  have hinput : fragment0105711Chars ++ tail = '{' :: (fragment0105711Field000Chars00 ++ (fragment0105711Field001Chars00 ++ (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0105711Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 23) (fragment0105711Chars ++ tail) =
        SourceJson.value (fuel + 23) ('{' :: (fragment0105711Field000Chars00 ++ (fragment0105711Field001Chars00 ++ (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 23)) hinput
    _ = SourceJson.object (fuel + 22) (SourceJson.white (fragment0105711Field000Chars00 ++ (fragment0105711Field001Chars00 ++ (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail))))))) fragment0105711Acc00000 := by rfl
    _ = SourceJson.object (fuel + 21) (SourceJson.white (fragment0105711Field001Chars00 ++ (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail)))))) fragment0105711Acc00100 := object_fragment0105711_field_000 fuel (fragment0105711Field001Chars00 ++ (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail))))) fragment0105711Acc00200 := object_fragment0105711_field_001 fuel (fragment0105711Field002Chars00 ++ (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail)))) fragment0105711Acc00300 := object_fragment0105711_field_002 fuel (fragment0105711Field003Chars00 ++ (fragment0105711Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0105711Field004Chars00 ++ (tail))) fragment0105711Acc00400 := object_fragment0105711_field_003 fuel (fragment0105711Field004Chars00 ++ (tail))
    _ = .ok (fragment0105711Value, tail) := object_fragment0105711_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_before_reader"
  err.flush

noncomputable def chunk0024Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0024Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0024 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55) (SourceJson.white (chunk0024Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 54) (SourceJson.white tail) (chunk0024Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0024_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_before_reader"
  err.flush

noncomputable def chunk0025Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0025Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['4']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc)

theorem array_chunk0025 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 54) (SourceJson.white (chunk0025Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 53) (SourceJson.white tail) (chunk0025Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0025_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_before_reader"
  err.flush

noncomputable def chunk0026LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0026SuffixChars00 : List Char := [',']
noncomputable def chunk0026Chars00 : List Char := chunk0026LeadChars00 ++ fragment0103843Chars ++ chunk0026SuffixChars00
noncomputable def chunk0026Push00 (acc : List SourceJson) : List SourceJson := fragment0103843Value :: acc

noncomputable def chunk0026AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0026_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53)
      (SourceJson.white (chunk0026LeadChars00 ++ (fragment0103843Chars ++ rest))) acc =
      (SourceJson.value (fuel + 52) (fragment0103843Chars ++ rest)).bind
        (chunk0026AfterValue00 (fuel + 52) acc) := by rfl

theorem array_chunk0026 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 53) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0026Push00 acc) := by
  have hinput : chunk0026Chars00 ++ tail = chunk0026LeadChars00 ++ (fragment0103843Chars ++ (chunk0026SuffixChars00 ++ tail)) := by
    simp only [chunk0026Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 53) (SourceJson.white (chunk0026Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 53)
          (SourceJson.white (chunk0026LeadChars00 ++ (fragment0103843Chars ++ (chunk0026SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 53) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 52) (fragment0103843Chars ++ (chunk0026SuffixChars00 ++ tail))).bind
        (chunk0026AfterValue00 (fuel + 52) acc) := array_chunk0026_head fuel (chunk0026SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0103843Value, chunk0026SuffixChars00 ++ tail)).bind
        (chunk0026AfterValue00 (fuel + 52) acc) :=
      congrArg (fun result => result.bind (chunk0026AfterValue00 (fuel + 52) acc))
        (value_fragment0103843 (fuel + 32) (chunk0026SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 52) (SourceJson.white tail) (chunk0026Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0026_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_before_reader"
  err.flush

noncomputable def chunk0027Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0027Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['8']), .number (String.ofList ['1', '0'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '0'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['1', '0'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['2']))]) :: (acc))

theorem array_chunk0027 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 52) (SourceJson.white (chunk0027Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 50) (SourceJson.white tail) (chunk0027Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0027_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_before_reader"
  err.flush

noncomputable def chunk0028Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0028Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0028 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 50) (SourceJson.white (chunk0028Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 49) (SourceJson.white tail) (chunk0028Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0028_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_before_reader"
  err.flush

noncomputable def chunk0029LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0029SuffixChars00 : List Char := [',']
noncomputable def chunk0029Chars00 : List Char := chunk0029LeadChars00 ++ fragment0105711Chars ++ chunk0029SuffixChars00
noncomputable def chunk0029Push00 (acc : List SourceJson) : List SourceJson := fragment0105711Value :: acc

noncomputable def chunk0029AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0029_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49)
      (SourceJson.white (chunk0029LeadChars00 ++ (fragment0105711Chars ++ rest))) acc =
      (SourceJson.value (fuel + 48) (fragment0105711Chars ++ rest)).bind
        (chunk0029AfterValue00 (fuel + 48) acc) := by rfl

theorem array_chunk0029 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 49) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 48) (SourceJson.white tail) (chunk0029Push00 acc) := by
  have hinput : chunk0029Chars00 ++ tail = chunk0029LeadChars00 ++ (fragment0105711Chars ++ (chunk0029SuffixChars00 ++ tail)) := by
    simp only [chunk0029Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 49) (SourceJson.white (chunk0029Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 49)
          (SourceJson.white (chunk0029LeadChars00 ++ (fragment0105711Chars ++ (chunk0029SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 49) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 48) (fragment0105711Chars ++ (chunk0029SuffixChars00 ++ tail))).bind
        (chunk0029AfterValue00 (fuel + 48) acc) := array_chunk0029_head fuel (chunk0029SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0105711Value, chunk0029SuffixChars00 ++ tail)).bind
        (chunk0029AfterValue00 (fuel + 48) acc) :=
      congrArg (fun result => result.bind (chunk0029AfterValue00 (fuel + 48) acc))
        (value_fragment0105711 (fuel + 25) (chunk0029SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 48) (SourceJson.white tail) (chunk0029Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0029_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_before_reader"
  err.flush

noncomputable def chunk0030Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0030Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['4']), .number (String.ofList ['8']), .number (String.ofList ['1', '3'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '4'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['6']))]) :: (acc)

theorem array_chunk0030 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 48) (SourceJson.white (chunk0030Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 47) (SourceJson.white tail) (chunk0030Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0030_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_before_reader"
  err.flush

noncomputable def chunk0031Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0031Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['3']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1', '1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['8'])], .arr [.number (String.ofList ['3']), .number (String.ofList ['7'])], .arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1'])], .arr [.number (String.ofList ['8']), .number (String.ofList ['1', '1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['3']))]) :: (acc))

theorem array_chunk0031 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 47) (SourceJson.white (chunk0031Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (chunk0031Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0031_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0024Chars00 ++ chunk0025Chars00 ++ chunk0026Chars00 ++ chunk0027Chars00 ++ chunk0028Chars00 ++ chunk0029Chars00 ++ chunk0030Chars00 ++ chunk0031Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0031Push00 (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 55) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 55) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 55) (SourceJson.white (chunk0024Chars00 ++ (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 55) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 54) (SourceJson.white (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))))) (chunk0024Push00 (acc)) := array_chunk0024 fuel (chunk0025Chars00 ++ (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 53) (SourceJson.white (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))))) (chunk0025Push00 (chunk0024Push00 (acc))) := array_chunk0025 fuel (chunk0026Chars00 ++ (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0024Push00 (acc))
    _ = SourceJson.array (fuel + 52) (SourceJson.white (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))) := array_chunk0026 fuel (chunk0027Chars00 ++ (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0025Push00 (chunk0024Push00 (acc)))
    _ = SourceJson.array (fuel + 50) (SourceJson.white (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))) := array_chunk0027 fuel (chunk0028Chars00 ++ (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))
    _ = SourceJson.array (fuel + 49) (SourceJson.white (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))) := array_chunk0028 fuel (chunk0029Chars00 ++ (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))
    _ = SourceJson.array (fuel + 48) (SourceJson.white (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail)))) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))) := array_chunk0029 fuel (chunk0030Chars00 ++ (chunk0031Chars00 ++ (tail))) (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))
    _ = SourceJson.array (fuel + 47) (SourceJson.white (chunk0031Chars00 ++ (tail))) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))) := array_chunk0030 fuel (chunk0031Chars00 ++ (tail)) (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc)))))))
    _ = SourceJson.array (fuel + 45) (SourceJson.white tail) (blockPush acc) := array_chunk0031 fuel (tail) (chunk0030Push00 (chunk0029Push00 (chunk0028Push00 (chunk0027Push00 (chunk0026Push00 (chunk0025Push00 (chunk0024Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 102926).take 5405 = blockChars := by rfl

theorem block_original_split : sourceRest 102926 = blockChars ++ sourceRest 108331 := by
  calc
    sourceRest 102926 = (sourceRest 102926).take 5405 ++ (sourceRest 102926).drop 5405 :=
      (List.take_append_drop 5405 (sourceRest 102926)).symm
    _ = blockChars ++ (sourceRest 102926).drop 5405 :=
      congrArg (fun part => part ++ (sourceRest 102926).drop 5405) block_original_prefix
    _ = blockChars ++ sourceRest 108331 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 102926 5405)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 55) (SourceJson.white (sourceRest 102926)) acc =
      SourceJson.array (fuel + 45) (SourceJson.white (sourceRest 108331)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 55) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 108331) acc)

#print axioms object_fragment0103843_field_000
#print axioms object_fragment0103843_field_001
#print axioms object_fragment0103843_field_002
#print axioms object_fragment0103843_field_003
#print axioms object_fragment0103843_field_004
#print axioms value_fragment0103843
#print axioms array_fragment0105970_chunk_000
#print axioms array_fragment0105970_chunk_001
#print axioms array_fragment0105970_chunk_002
#print axioms array_fragment0105970_chunk_003
#print axioms value_fragment0105970
#print axioms object_fragment0105711_field_000
#print axioms object_fragment0105711_field_001
#print axioms object_fragment0105711_field_002
#print axioms object_fragment0105711_field_003_header
#print axioms object_fragment0105711_field_003
#print axioms object_fragment0105711_field_004
#print axioms value_fragment0105711
#print axioms array_chunk0024
#print axioms array_chunk0025
#print axioms array_chunk0026_head
#print axioms array_chunk0026
#print axioms array_chunk0027
#print axioms array_chunk0028
#print axioms array_chunk0029_head
#print axioms array_chunk0029
#print axioms array_chunk0030
#print axioms array_chunk0031
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock003

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
