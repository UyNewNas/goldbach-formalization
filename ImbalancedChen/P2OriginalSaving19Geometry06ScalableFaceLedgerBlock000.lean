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

namespace FaceLedgerBlock000

noncomputable def fragment0071459Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0071459Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0071459Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6'])]
noncomputable def fragment0071459Acc00100 : List (String × SourceJson) := (fragment0071459Field000Key00, fragment0071459Field000Value00) :: fragment0071459Acc00000
noncomputable def fragment0071459Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0071459_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0071459Field000Chars00 ++ tail)) fragment0071459Acc00000 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0071459Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0071459_object_field_000"
  err.flush

noncomputable def fragment0071459Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0071459Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0071459Acc00200 : List (String × SourceJson) := (fragment0071459Field001Key00, fragment0071459Field001Value00) :: fragment0071459Acc00100
noncomputable def fragment0071459Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0071459_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0071459Field001Chars00 ++ tail)) fragment0071459Acc00100 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0071459Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0071459_object_field_001"
  err.flush

noncomputable def fragment0071459Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0071459Field002Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0071459Acc00300 : List (String × SourceJson) := (fragment0071459Field002Key00, fragment0071459Field002Value00) :: fragment0071459Acc00200
noncomputable def fragment0071459Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '6', ',']

theorem object_fragment0071459_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0071459Field002Chars00 ++ tail)) fragment0071459Acc00200 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0071459Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0071459_object_field_002"
  err.flush

noncomputable def fragment0071459Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0071459Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6'])]]
noncomputable def fragment0071459Acc00400 : List (String × SourceJson) := (fragment0071459Field003Key00, fragment0071459Field003Value00) :: fragment0071459Acc00300
noncomputable def fragment0071459Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0071459_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0071459Field003Chars00 ++ tail)) fragment0071459Acc00300 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0071459Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0071459_object_field_003"
  err.flush

noncomputable def fragment0071459Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0071459Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0071459Acc00500 : List (String × SourceJson) := (fragment0071459Field004Key00, fragment0071459Field004Value00) :: fragment0071459Acc00400
noncomputable def fragment0071459Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0071459_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0071459Field004Chars00 ++ tail)) fragment0071459Acc00400 =
      .ok (.obj (fragment0071459Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0071459_object_field_004"
  err.flush

noncomputable def fragment0071459Chars : List Char := '{' :: (fragment0071459Field000Chars00 ++ fragment0071459Field001Chars00 ++ fragment0071459Field002Chars00 ++ fragment0071459Field003Chars00 ++ fragment0071459Field004Chars00)
noncomputable def fragment0071459Value : SourceJson := .obj (fragment0071459Acc00500.reverse)

theorem value_fragment0071459 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0071459Chars ++ tail) =
      .ok (fragment0071459Value, tail) := by
  have hinput : fragment0071459Chars ++ tail = '{' :: (fragment0071459Field000Chars00 ++ (fragment0071459Field001Chars00 ++ (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0071459Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0071459Chars ++ tail) =
        SourceJson.value (fuel + 21) ('{' :: (fragment0071459Field000Chars00 ++ (fragment0071459Field001Chars00 ++ (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0071459Field000Chars00 ++ (fragment0071459Field001Chars00 ++ (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail))))))) fragment0071459Acc00000 := by rfl
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0071459Field001Chars00 ++ (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail)))))) fragment0071459Acc00100 := object_fragment0071459_field_000 fuel (fragment0071459Field001Chars00 ++ (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail))))) fragment0071459Acc00200 := object_fragment0071459_field_001 fuel (fragment0071459Field002Chars00 ++ (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail)))) fragment0071459Acc00300 := object_fragment0071459_field_002 fuel (fragment0071459Field003Chars00 ++ (fragment0071459Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0071459Field004Chars00 ++ (tail))) fragment0071459Acc00400 := object_fragment0071459_field_003 fuel (fragment0071459Field004Chars00 ++ (tail))
    _ = .ok (fragment0071459Value, tail) := object_fragment0071459_field_004 fuel (tail)

noncomputable def fragment0072941Acc00000 : List SourceJson := []

noncomputable def fragment0072941Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['9']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0072941_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 39) (SourceJson.white (fragment0072941Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 37) (SourceJson.white tail) (fragment0072941Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00100 : List SourceJson := fragment0072941Chunk000Push00 fragment0072941Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_000"
  err.flush

noncomputable def fragment0072941Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0072941_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 37) (SourceJson.white (fragment0072941Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 36) (SourceJson.white tail) (fragment0072941Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00200 : List SourceJson := fragment0072941Chunk001Push00 fragment0072941Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_001"
  err.flush

noncomputable def fragment0072941Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0'])]) :: (acc)

theorem array_fragment0072941_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 36) (SourceJson.white (fragment0072941Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 35) (SourceJson.white tail) (fragment0072941Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00300 : List SourceJson := fragment0072941Chunk002Push00 fragment0072941Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_002"
  err.flush

noncomputable def fragment0072941Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: (acc))

theorem array_fragment0072941_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 35) (SourceJson.white (fragment0072941Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 33) (SourceJson.white tail) (fragment0072941Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00400 : List SourceJson := fragment0072941Chunk003Push00 fragment0072941Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_003"
  err.flush

noncomputable def fragment0072941Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0072941_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 33) (SourceJson.white (fragment0072941Chunk004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 32) (SourceJson.white tail) (fragment0072941Chunk004Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00500 : List SourceJson := fragment0072941Chunk004Push00 fragment0072941Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_004"
  err.flush

noncomputable def fragment0072941Chunk005Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk005Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0072941_chunk_005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 32) (SourceJson.white (fragment0072941Chunk005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 31) (SourceJson.white tail) (fragment0072941Chunk005Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00600 : List SourceJson := fragment0072941Chunk005Push00 fragment0072941Acc00500

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_005"
  err.flush

noncomputable def fragment0072941Chunk006Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0072941Chunk006Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '8']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: (acc))

theorem array_fragment0072941_chunk_006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 31) (SourceJson.white (fragment0072941Chunk006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 29) (SourceJson.white tail) (fragment0072941Chunk006Push00 acc) := by
  rfl

noncomputable def fragment0072941Acc00700 : List SourceJson := fragment0072941Chunk006Push00 fragment0072941Acc00600

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_006"
  err.flush

noncomputable def fragment0072941Chunk007Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0072941Chunk007Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0072941_chunk_007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 29) (SourceJson.white (fragment0072941Chunk007Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0072941Chunk007Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0072941Acc00800 : List SourceJson := fragment0072941Chunk007Push00 fragment0072941Acc00700

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072941_array_chunk_007"
  err.flush

noncomputable def fragment0072941Chars : List Char := '[' :: (fragment0072941Chunk000Chars00 ++ fragment0072941Chunk001Chars00 ++ fragment0072941Chunk002Chars00 ++ fragment0072941Chunk003Chars00 ++ fragment0072941Chunk004Chars00 ++ fragment0072941Chunk005Chars00 ++ fragment0072941Chunk006Chars00 ++ fragment0072941Chunk007Chars00)
noncomputable def fragment0072941Value : SourceJson := .arr (fragment0072941Acc00800.reverse)

theorem value_fragment0072941 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 40) (fragment0072941Chars ++ tail) =
      .ok (fragment0072941Value, tail) := by
  have hinput : fragment0072941Chars ++ tail = '[' :: (fragment0072941Chunk000Chars00 ++ (fragment0072941Chunk001Chars00 ++ (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))))))))) := by
    simp only [fragment0072941Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 40) (fragment0072941Chars ++ tail) =
        SourceJson.value (fuel + 40) ('[' :: (fragment0072941Chunk000Chars00 ++ (fragment0072941Chunk001Chars00 ++ (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))))))))) :=
      congrArg (SourceJson.value (fuel + 40)) hinput
    _ = SourceJson.array (fuel + 39) (SourceJson.white (fragment0072941Chunk000Chars00 ++ (fragment0072941Chunk001Chars00 ++ (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))))))))) fragment0072941Acc00000 := by rfl
    _ = SourceJson.array (fuel + 37) (SourceJson.white (fragment0072941Chunk001Chars00 ++ (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))))))))) fragment0072941Acc00100 := array_fragment0072941_chunk_000 fuel (fragment0072941Chunk001Chars00 ++ (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))))))) fragment0072941Acc00000
    _ = SourceJson.array (fuel + 36) (SourceJson.white (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))))))) fragment0072941Acc00200 := array_fragment0072941_chunk_001 fuel (fragment0072941Chunk002Chars00 ++ (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))))))) fragment0072941Acc00100
    _ = SourceJson.array (fuel + 35) (SourceJson.white (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))))))) fragment0072941Acc00300 := array_fragment0072941_chunk_002 fuel (fragment0072941Chunk003Chars00 ++ (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))))) fragment0072941Acc00200
    _ = SourceJson.array (fuel + 33) (SourceJson.white (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))))) fragment0072941Acc00400 := array_fragment0072941_chunk_003 fuel (fragment0072941Chunk004Chars00 ++ (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))))) fragment0072941Acc00300
    _ = SourceJson.array (fuel + 32) (SourceJson.white (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))))) fragment0072941Acc00500 := array_fragment0072941_chunk_004 fuel (fragment0072941Chunk005Chars00 ++ (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))) fragment0072941Acc00400
    _ = SourceJson.array (fuel + 31) (SourceJson.white (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail)))) fragment0072941Acc00600 := array_fragment0072941_chunk_005 fuel (fragment0072941Chunk006Chars00 ++ (fragment0072941Chunk007Chars00 ++ (tail))) fragment0072941Acc00500
    _ = SourceJson.array (fuel + 29) (SourceJson.white (fragment0072941Chunk007Chars00 ++ (tail))) fragment0072941Acc00700 := array_fragment0072941_chunk_006 fuel (fragment0072941Chunk007Chars00 ++ (tail)) fragment0072941Acc00600
    _ = .ok (fragment0072941Value, tail) := array_fragment0072941_chunk_007 fuel (tail) fragment0072941Acc00700

noncomputable def fragment0072426Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0072426Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0072426Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2'])]
noncomputable def fragment0072426Acc00100 : List (String × SourceJson) := (fragment0072426Field000Key00, fragment0072426Field000Value00) :: fragment0072426Acc00000
noncomputable def fragment0072426Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0072426_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 44) (SourceJson.white (fragment0072426Field000Chars00 ++ tail)) fragment0072426Acc00000 =
      SourceJson.object (fuel + 43) (SourceJson.white tail) fragment0072426Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072426_object_field_000"
  err.flush

noncomputable def fragment0072426Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0072426Field001Value00 : SourceJson := .number (String.ofList ['8'])
noncomputable def fragment0072426Acc00200 : List (String × SourceJson) := (fragment0072426Field001Key00, fragment0072426Field001Value00) :: fragment0072426Acc00100
noncomputable def fragment0072426Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',']

theorem object_fragment0072426_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 43) (SourceJson.white (fragment0072426Field001Chars00 ++ tail)) fragment0072426Acc00100 =
      SourceJson.object (fuel + 42) (SourceJson.white tail) fragment0072426Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072426_object_field_001"
  err.flush

noncomputable def fragment0072426Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0072426Field002Value00 : SourceJson := .number (String.ofList ['3', '2'])
noncomputable def fragment0072426Acc00300 : List (String × SourceJson) := (fragment0072426Field002Key00, fragment0072426Field002Value00) :: fragment0072426Acc00200
noncomputable def fragment0072426Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '2', ',']

theorem object_fragment0072426_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 42) (SourceJson.white (fragment0072426Field002Chars00 ++ tail)) fragment0072426Acc00200 =
      SourceJson.object (fuel + 41) (SourceJson.white tail) fragment0072426Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072426_object_field_002"
  err.flush

noncomputable def fragment0072426Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0072426Field003Value00 : SourceJson := fragment0072941Value
noncomputable def fragment0072426Acc00400 : List (String × SourceJson) := (fragment0072426Field003Key00, fragment0072426Field003Value00) :: fragment0072426Acc00300
noncomputable def fragment0072426Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0072426Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0072426Field003Chars00 : List Char := fragment0072426Field003HeaderChars00 ++ fragment0072941Chars ++ fragment0072426Field003SuffixChars00

noncomputable def fragment0072426Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0072426Field003Key00, result.1) :: fragment0072426Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0072426Field003Key00, result.1) :: fragment0072426Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0072426_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0072426Field003HeaderChars00 ++ rest)) fragment0072426Acc00300 =
      (SourceJson.value (fuel + 40) rest).bind (fragment0072426Field003AfterValue00 (fuel + 40)) := by rfl

theorem object_fragment0072426_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0072426Field003Chars00 ++ tail)) fragment0072426Acc00300 =
      SourceJson.object (fuel + 40) (SourceJson.white tail) fragment0072426Acc00400 := by
  have hinput : fragment0072426Field003Chars00 ++ tail = fragment0072426Field003HeaderChars00 ++ (fragment0072941Chars ++ (fragment0072426Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0072426Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 41) (SourceJson.white (fragment0072426Field003Chars00 ++ tail)) fragment0072426Acc00300 =
        SourceJson.object (fuel + 41)
          (SourceJson.white (fragment0072426Field003HeaderChars00 ++ (fragment0072941Chars ++ (fragment0072426Field003SuffixChars00 ++ tail)))) fragment0072426Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 41) (SourceJson.white s) fragment0072426Acc00300) hinput
    _ = (SourceJson.value (fuel + 40) (fragment0072941Chars ++ (fragment0072426Field003SuffixChars00 ++ tail))).bind
        (fragment0072426Field003AfterValue00 (fuel + 40)) := object_fragment0072426_field_003_header fuel (fragment0072941Chars ++ (fragment0072426Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0072941Value, fragment0072426Field003SuffixChars00 ++ tail)).bind (fragment0072426Field003AfterValue00 (fuel + 40)) :=
      congrArg (fun result => result.bind (fragment0072426Field003AfterValue00 (fuel + 40)))
        (value_fragment0072941 (fuel + 0) (fragment0072426Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 40) (SourceJson.white tail) fragment0072426Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072426_object_field_003"
  err.flush

noncomputable def fragment0072426Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0072426Field004Value00 : SourceJson := .number (String.ofList ['1', '1', '3'])
noncomputable def fragment0072426Acc00500 : List (String × SourceJson) := (fragment0072426Field004Key00, fragment0072426Field004Value00) :: fragment0072426Acc00400
noncomputable def fragment0072426Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '1', '3', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0072426_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 40) (SourceJson.white (fragment0072426Field004Chars00 ++ tail)) fragment0072426Acc00400 =
      .ok (.obj (fragment0072426Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0072426_object_field_004"
  err.flush

noncomputable def fragment0072426Chars : List Char := '{' :: (fragment0072426Field000Chars00 ++ fragment0072426Field001Chars00 ++ fragment0072426Field002Chars00 ++ fragment0072426Field003Chars00 ++ fragment0072426Field004Chars00)
noncomputable def fragment0072426Value : SourceJson := .obj (fragment0072426Acc00500.reverse)

theorem value_fragment0072426 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 45) (fragment0072426Chars ++ tail) =
      .ok (fragment0072426Value, tail) := by
  have hinput : fragment0072426Chars ++ tail = '{' :: (fragment0072426Field000Chars00 ++ (fragment0072426Field001Chars00 ++ (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0072426Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 45) (fragment0072426Chars ++ tail) =
        SourceJson.value (fuel + 45) ('{' :: (fragment0072426Field000Chars00 ++ (fragment0072426Field001Chars00 ++ (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 45)) hinput
    _ = SourceJson.object (fuel + 44) (SourceJson.white (fragment0072426Field000Chars00 ++ (fragment0072426Field001Chars00 ++ (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail))))))) fragment0072426Acc00000 := by rfl
    _ = SourceJson.object (fuel + 43) (SourceJson.white (fragment0072426Field001Chars00 ++ (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail)))))) fragment0072426Acc00100 := object_fragment0072426_field_000 fuel (fragment0072426Field001Chars00 ++ (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 42) (SourceJson.white (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail))))) fragment0072426Acc00200 := object_fragment0072426_field_001 fuel (fragment0072426Field002Chars00 ++ (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 41) (SourceJson.white (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail)))) fragment0072426Acc00300 := object_fragment0072426_field_002 fuel (fragment0072426Field003Chars00 ++ (fragment0072426Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 40) (SourceJson.white (fragment0072426Field004Chars00 ++ (tail))) fragment0072426Acc00400 := object_fragment0072426_field_003 fuel (fragment0072426Field004Chars00 ++ (tail))
    _ = .ok (fragment0072426Value, tail) := object_fragment0072426_field_004 fuel (tail)

noncomputable def fragment0077458Acc00000 : List SourceJson := []

noncomputable def fragment0077458Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0077458Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6'])]) :: (acc))

theorem array_fragment0077458_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 27) (SourceJson.white (fragment0077458Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 25) (SourceJson.white tail) (fragment0077458Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0077458Acc00100 : List SourceJson := fragment0077458Chunk000Push00 fragment0077458Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077458_array_chunk_000"
  err.flush

noncomputable def fragment0077458Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0077458Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0077458_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 25) (SourceJson.white (fragment0077458Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 23) (SourceJson.white tail) (fragment0077458Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0077458Acc00200 : List SourceJson := fragment0077458Chunk001Push00 fragment0077458Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077458_array_chunk_001"
  err.flush

noncomputable def fragment0077458Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0077458Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0077458_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0077458Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0077458Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0077458Acc00300 : List SourceJson := fragment0077458Chunk002Push00 fragment0077458Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077458_array_chunk_002"
  err.flush

noncomputable def fragment0077458Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0077458Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: (acc))

theorem array_fragment0077458_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0077458Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0077458Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0077458Acc00400 : List SourceJson := fragment0077458Chunk003Push00 fragment0077458Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077458_array_chunk_003"
  err.flush

noncomputable def fragment0077458Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0077458Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]) :: ((.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '9'])]) :: (acc))

theorem array_fragment0077458_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0077458Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0077458Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0077458Acc00500 : List SourceJson := fragment0077458Chunk004Push00 fragment0077458Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077458_array_chunk_004"
  err.flush

noncomputable def fragment0077458Chars : List Char := '[' :: (fragment0077458Chunk000Chars00 ++ fragment0077458Chunk001Chars00 ++ fragment0077458Chunk002Chars00 ++ fragment0077458Chunk003Chars00 ++ fragment0077458Chunk004Chars00)
noncomputable def fragment0077458Value : SourceJson := .arr (fragment0077458Acc00500.reverse)

theorem value_fragment0077458 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 28) (fragment0077458Chars ++ tail) =
      .ok (fragment0077458Value, tail) := by
  have hinput : fragment0077458Chars ++ tail = '[' :: (fragment0077458Chunk000Chars00 ++ (fragment0077458Chunk001Chars00 ++ (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0077458Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 28) (fragment0077458Chars ++ tail) =
        SourceJson.value (fuel + 28) ('[' :: (fragment0077458Chunk000Chars00 ++ (fragment0077458Chunk001Chars00 ++ (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 28)) hinput
    _ = SourceJson.array (fuel + 27) (SourceJson.white (fragment0077458Chunk000Chars00 ++ (fragment0077458Chunk001Chars00 ++ (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail))))))) fragment0077458Acc00000 := by rfl
    _ = SourceJson.array (fuel + 25) (SourceJson.white (fragment0077458Chunk001Chars00 ++ (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail)))))) fragment0077458Acc00100 := array_fragment0077458_chunk_000 fuel (fragment0077458Chunk001Chars00 ++ (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail))))) fragment0077458Acc00000
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail))))) fragment0077458Acc00200 := array_fragment0077458_chunk_001 fuel (fragment0077458Chunk002Chars00 ++ (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail)))) fragment0077458Acc00100
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail)))) fragment0077458Acc00300 := array_fragment0077458_chunk_002 fuel (fragment0077458Chunk003Chars00 ++ (fragment0077458Chunk004Chars00 ++ (tail))) fragment0077458Acc00200
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0077458Chunk004Chars00 ++ (tail))) fragment0077458Acc00400 := array_fragment0077458_chunk_003 fuel (fragment0077458Chunk004Chars00 ++ (tail)) fragment0077458Acc00300
    _ = .ok (fragment0077458Value, tail) := array_fragment0077458_chunk_004 fuel (tail) fragment0077458Acc00400

noncomputable def fragment0077111Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0077111Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0077111Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0'])]
noncomputable def fragment0077111Acc00100 : List (String × SourceJson) := (fragment0077111Field000Key00, fragment0077111Field000Value00) :: fragment0077111Acc00000
noncomputable def fragment0077111Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0077111_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 32) (SourceJson.white (fragment0077111Field000Chars00 ++ tail)) fragment0077111Acc00000 =
      SourceJson.object (fuel + 31) (SourceJson.white tail) fragment0077111Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077111_object_field_000"
  err.flush

noncomputable def fragment0077111Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0077111Field001Value00 : SourceJson := .number (String.ofList ['7'])
noncomputable def fragment0077111Acc00200 : List (String × SourceJson) := (fragment0077111Field001Key00, fragment0077111Field001Value00) :: fragment0077111Acc00100
noncomputable def fragment0077111Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '7', ',']

theorem object_fragment0077111_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 31) (SourceJson.white (fragment0077111Field001Chars00 ++ tail)) fragment0077111Acc00100 =
      SourceJson.object (fuel + 30) (SourceJson.white tail) fragment0077111Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077111_object_field_001"
  err.flush

noncomputable def fragment0077111Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0077111Field002Value00 : SourceJson := .number (String.ofList ['2', '0'])
noncomputable def fragment0077111Acc00300 : List (String × SourceJson) := (fragment0077111Field002Key00, fragment0077111Field002Value00) :: fragment0077111Acc00200
noncomputable def fragment0077111Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', '0', ',']

theorem object_fragment0077111_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 30) (SourceJson.white (fragment0077111Field002Chars00 ++ tail)) fragment0077111Acc00200 =
      SourceJson.object (fuel + 29) (SourceJson.white tail) fragment0077111Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077111_object_field_002"
  err.flush

noncomputable def fragment0077111Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0077111Field003Value00 : SourceJson := fragment0077458Value
noncomputable def fragment0077111Acc00400 : List (String × SourceJson) := (fragment0077111Field003Key00, fragment0077111Field003Value00) :: fragment0077111Acc00300
noncomputable def fragment0077111Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0077111Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0077111Field003Chars00 : List Char := fragment0077111Field003HeaderChars00 ++ fragment0077458Chars ++ fragment0077111Field003SuffixChars00

noncomputable def fragment0077111Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0077111Field003Key00, result.1) :: fragment0077111Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0077111Field003Key00, result.1) :: fragment0077111Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0077111_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0077111Field003HeaderChars00 ++ rest)) fragment0077111Acc00300 =
      (SourceJson.value (fuel + 28) rest).bind (fragment0077111Field003AfterValue00 (fuel + 28)) := by rfl

theorem object_fragment0077111_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0077111Field003Chars00 ++ tail)) fragment0077111Acc00300 =
      SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0077111Acc00400 := by
  have hinput : fragment0077111Field003Chars00 ++ tail = fragment0077111Field003HeaderChars00 ++ (fragment0077458Chars ++ (fragment0077111Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0077111Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 29) (SourceJson.white (fragment0077111Field003Chars00 ++ tail)) fragment0077111Acc00300 =
        SourceJson.object (fuel + 29)
          (SourceJson.white (fragment0077111Field003HeaderChars00 ++ (fragment0077458Chars ++ (fragment0077111Field003SuffixChars00 ++ tail)))) fragment0077111Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 29) (SourceJson.white s) fragment0077111Acc00300) hinput
    _ = (SourceJson.value (fuel + 28) (fragment0077458Chars ++ (fragment0077111Field003SuffixChars00 ++ tail))).bind
        (fragment0077111Field003AfterValue00 (fuel + 28)) := object_fragment0077111_field_003_header fuel (fragment0077458Chars ++ (fragment0077111Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0077458Value, fragment0077111Field003SuffixChars00 ++ tail)).bind (fragment0077111Field003AfterValue00 (fuel + 28)) :=
      congrArg (fun result => result.bind (fragment0077111Field003AfterValue00 (fuel + 28)))
        (value_fragment0077458 (fuel + 0) (fragment0077111Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 28) (SourceJson.white tail) fragment0077111Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077111_object_field_003"
  err.flush

noncomputable def fragment0077111Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0077111Field004Value00 : SourceJson := .number (String.ofList ['1', '9'])
noncomputable def fragment0077111Acc00500 : List (String × SourceJson) := (fragment0077111Field004Key00, fragment0077111Field004Value00) :: fragment0077111Acc00400
noncomputable def fragment0077111Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '9', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0077111_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0077111Field004Chars00 ++ tail)) fragment0077111Acc00400 =
      .ok (.obj (fragment0077111Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0077111_object_field_004"
  err.flush

noncomputable def fragment0077111Chars : List Char := '{' :: (fragment0077111Field000Chars00 ++ fragment0077111Field001Chars00 ++ fragment0077111Field002Chars00 ++ fragment0077111Field003Chars00 ++ fragment0077111Field004Chars00)
noncomputable def fragment0077111Value : SourceJson := .obj (fragment0077111Acc00500.reverse)

theorem value_fragment0077111 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 33) (fragment0077111Chars ++ tail) =
      .ok (fragment0077111Value, tail) := by
  have hinput : fragment0077111Chars ++ tail = '{' :: (fragment0077111Field000Chars00 ++ (fragment0077111Field001Chars00 ++ (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0077111Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 33) (fragment0077111Chars ++ tail) =
        SourceJson.value (fuel + 33) ('{' :: (fragment0077111Field000Chars00 ++ (fragment0077111Field001Chars00 ++ (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 33)) hinput
    _ = SourceJson.object (fuel + 32) (SourceJson.white (fragment0077111Field000Chars00 ++ (fragment0077111Field001Chars00 ++ (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail))))))) fragment0077111Acc00000 := by rfl
    _ = SourceJson.object (fuel + 31) (SourceJson.white (fragment0077111Field001Chars00 ++ (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail)))))) fragment0077111Acc00100 := object_fragment0077111_field_000 fuel (fragment0077111Field001Chars00 ++ (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 30) (SourceJson.white (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail))))) fragment0077111Acc00200 := object_fragment0077111_field_001 fuel (fragment0077111Field002Chars00 ++ (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 29) (SourceJson.white (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail)))) fragment0077111Acc00300 := object_fragment0077111_field_002 fuel (fragment0077111Field003Chars00 ++ (fragment0077111Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0077111Field004Chars00 ++ (tail))) fragment0077111Acc00400 := object_fragment0077111_field_003 fuel (fragment0077111Field004Chars00 ++ (tail))
    _ = .ok (fragment0077111Value, tail) := object_fragment0077111_field_004 fuel (tail)

noncomputable def fragment0080071Acc00000 : List SourceJson := []

noncomputable def fragment0080071Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080071Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]) :: (acc))

theorem array_fragment0080071_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (fragment0080071Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (fragment0080071Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0080071Acc00100 : List SourceJson := fragment0080071Chunk000Push00 fragment0080071Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080071_array_chunk_000"
  err.flush

noncomputable def fragment0080071Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080071Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]) :: (acc))

theorem array_fragment0080071_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (fragment0080071Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 19) (SourceJson.white tail) (fragment0080071Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0080071Acc00200 : List SourceJson := fragment0080071Chunk001Push00 fragment0080071Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080071_array_chunk_001"
  err.flush

noncomputable def fragment0080071Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080071Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]) :: ((.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]) :: (acc))

theorem array_fragment0080071_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 19) (SourceJson.white (fragment0080071Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 17) (SourceJson.white tail) (fragment0080071Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0080071Acc00300 : List SourceJson := fragment0080071Chunk002Push00 fragment0080071Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080071_array_chunk_002"
  err.flush

noncomputable def fragment0080071Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0080071Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['7']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7'])]) :: ((.arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]) :: (acc))

theorem array_fragment0080071_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 17) (SourceJson.white (fragment0080071Chunk003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 15) (SourceJson.white tail) (fragment0080071Chunk003Push00 acc) := by
  rfl

noncomputable def fragment0080071Acc00400 : List SourceJson := fragment0080071Chunk003Push00 fragment0080071Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080071_array_chunk_003"
  err.flush

noncomputable def fragment0080071Chunk004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0080071Chunk004Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]) :: (acc)

theorem array_fragment0080071_chunk_004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0080071Chunk004Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0080071Chunk004Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0080071Acc00500 : List SourceJson := fragment0080071Chunk004Push00 fragment0080071Acc00400

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0080071_array_chunk_004"
  err.flush

noncomputable def fragment0080071Chars : List Char := '[' :: (fragment0080071Chunk000Chars00 ++ fragment0080071Chunk001Chars00 ++ fragment0080071Chunk002Chars00 ++ fragment0080071Chunk003Chars00 ++ fragment0080071Chunk004Chars00)
noncomputable def fragment0080071Value : SourceJson := .arr (fragment0080071Acc00500.reverse)

theorem value_fragment0080071 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 24) (fragment0080071Chars ++ tail) =
      .ok (fragment0080071Value, tail) := by
  have hinput : fragment0080071Chars ++ tail = '[' :: (fragment0080071Chunk000Chars00 ++ (fragment0080071Chunk001Chars00 ++ (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail)))))) := by
    simp only [fragment0080071Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 24) (fragment0080071Chars ++ tail) =
        SourceJson.value (fuel + 24) ('[' :: (fragment0080071Chunk000Chars00 ++ (fragment0080071Chunk001Chars00 ++ (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 24)) hinput
    _ = SourceJson.array (fuel + 23) (SourceJson.white (fragment0080071Chunk000Chars00 ++ (fragment0080071Chunk001Chars00 ++ (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail))))))) fragment0080071Acc00000 := by rfl
    _ = SourceJson.array (fuel + 21) (SourceJson.white (fragment0080071Chunk001Chars00 ++ (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail)))))) fragment0080071Acc00100 := array_fragment0080071_chunk_000 fuel (fragment0080071Chunk001Chars00 ++ (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail))))) fragment0080071Acc00000
    _ = SourceJson.array (fuel + 19) (SourceJson.white (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail))))) fragment0080071Acc00200 := array_fragment0080071_chunk_001 fuel (fragment0080071Chunk002Chars00 ++ (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail)))) fragment0080071Acc00100
    _ = SourceJson.array (fuel + 17) (SourceJson.white (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail)))) fragment0080071Acc00300 := array_fragment0080071_chunk_002 fuel (fragment0080071Chunk003Chars00 ++ (fragment0080071Chunk004Chars00 ++ (tail))) fragment0080071Acc00200
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0080071Chunk004Chars00 ++ (tail))) fragment0080071Acc00400 := array_fragment0080071_chunk_003 fuel (fragment0080071Chunk004Chars00 ++ (tail)) fragment0080071Acc00300
    _ = .ok (fragment0080071Value, tail) := array_fragment0080071_chunk_004 fuel (tail) fragment0080071Acc00400

noncomputable def fragment0079762Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0079762Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0079762Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8'])]
noncomputable def fragment0079762Acc00100 : List (String × SourceJson) := (fragment0079762Field000Key00, fragment0079762Field000Value00) :: fragment0079762Acc00000
noncomputable def fragment0079762Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0079762_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 28) (SourceJson.white (fragment0079762Field000Chars00 ++ tail)) fragment0079762Acc00000 =
      SourceJson.object (fuel + 27) (SourceJson.white tail) fragment0079762Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079762_object_field_000"
  err.flush

noncomputable def fragment0079762Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0079762Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0079762Acc00200 : List (String × SourceJson) := (fragment0079762Field001Key00, fragment0079762Field001Value00) :: fragment0079762Acc00100
noncomputable def fragment0079762Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0079762_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 27) (SourceJson.white (fragment0079762Field001Chars00 ++ tail)) fragment0079762Acc00100 =
      SourceJson.object (fuel + 26) (SourceJson.white tail) fragment0079762Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079762_object_field_001"
  err.flush

noncomputable def fragment0079762Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0079762Field002Value00 : SourceJson := .number (String.ofList ['1', '8'])
noncomputable def fragment0079762Acc00300 : List (String × SourceJson) := (fragment0079762Field002Key00, fragment0079762Field002Value00) :: fragment0079762Acc00200
noncomputable def fragment0079762Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', '8', ',']

theorem object_fragment0079762_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 26) (SourceJson.white (fragment0079762Field002Chars00 ++ tail)) fragment0079762Acc00200 =
      SourceJson.object (fuel + 25) (SourceJson.white tail) fragment0079762Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079762_object_field_002"
  err.flush

noncomputable def fragment0079762Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0079762Field003Value00 : SourceJson := fragment0080071Value
noncomputable def fragment0079762Acc00400 : List (String × SourceJson) := (fragment0079762Field003Key00, fragment0079762Field003Value00) :: fragment0079762Acc00300
noncomputable def fragment0079762Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0079762Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0079762Field003Chars00 : List Char := fragment0079762Field003HeaderChars00 ++ fragment0080071Chars ++ fragment0079762Field003SuffixChars00

noncomputable def fragment0079762Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0079762Field003Key00, result.1) :: fragment0079762Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0079762Field003Key00, result.1) :: fragment0079762Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0079762_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0079762Field003HeaderChars00 ++ rest)) fragment0079762Acc00300 =
      (SourceJson.value (fuel + 24) rest).bind (fragment0079762Field003AfterValue00 (fuel + 24)) := by rfl

theorem object_fragment0079762_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0079762Field003Chars00 ++ tail)) fragment0079762Acc00300 =
      SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0079762Acc00400 := by
  have hinput : fragment0079762Field003Chars00 ++ tail = fragment0079762Field003HeaderChars00 ++ (fragment0080071Chars ++ (fragment0079762Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0079762Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 25) (SourceJson.white (fragment0079762Field003Chars00 ++ tail)) fragment0079762Acc00300 =
        SourceJson.object (fuel + 25)
          (SourceJson.white (fragment0079762Field003HeaderChars00 ++ (fragment0080071Chars ++ (fragment0079762Field003SuffixChars00 ++ tail)))) fragment0079762Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 25) (SourceJson.white s) fragment0079762Acc00300) hinput
    _ = (SourceJson.value (fuel + 24) (fragment0080071Chars ++ (fragment0079762Field003SuffixChars00 ++ tail))).bind
        (fragment0079762Field003AfterValue00 (fuel + 24)) := object_fragment0079762_field_003_header fuel (fragment0080071Chars ++ (fragment0079762Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0080071Value, fragment0079762Field003SuffixChars00 ++ tail)).bind (fragment0079762Field003AfterValue00 (fuel + 24)) :=
      congrArg (fun result => result.bind (fragment0079762Field003AfterValue00 (fuel + 24)))
        (value_fragment0080071 (fuel + 0) (fragment0079762Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 24) (SourceJson.white tail) fragment0079762Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079762_object_field_003"
  err.flush

noncomputable def fragment0079762Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0079762Field004Value00 : SourceJson := .number (String.ofList ['1', '7'])
noncomputable def fragment0079762Acc00500 : List (String × SourceJson) := (fragment0079762Field004Key00, fragment0079762Field004Value00) :: fragment0079762Acc00400
noncomputable def fragment0079762Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '7', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0079762_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 24) (SourceJson.white (fragment0079762Field004Chars00 ++ tail)) fragment0079762Acc00400 =
      .ok (.obj (fragment0079762Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0079762_object_field_004"
  err.flush

noncomputable def fragment0079762Chars : List Char := '{' :: (fragment0079762Field000Chars00 ++ fragment0079762Field001Chars00 ++ fragment0079762Field002Chars00 ++ fragment0079762Field003Chars00 ++ fragment0079762Field004Chars00)
noncomputable def fragment0079762Value : SourceJson := .obj (fragment0079762Acc00500.reverse)

theorem value_fragment0079762 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 29) (fragment0079762Chars ++ tail) =
      .ok (fragment0079762Value, tail) := by
  have hinput : fragment0079762Chars ++ tail = '{' :: (fragment0079762Field000Chars00 ++ (fragment0079762Field001Chars00 ++ (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0079762Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 29) (fragment0079762Chars ++ tail) =
        SourceJson.value (fuel + 29) ('{' :: (fragment0079762Field000Chars00 ++ (fragment0079762Field001Chars00 ++ (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 29)) hinput
    _ = SourceJson.object (fuel + 28) (SourceJson.white (fragment0079762Field000Chars00 ++ (fragment0079762Field001Chars00 ++ (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail))))))) fragment0079762Acc00000 := by rfl
    _ = SourceJson.object (fuel + 27) (SourceJson.white (fragment0079762Field001Chars00 ++ (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail)))))) fragment0079762Acc00100 := object_fragment0079762_field_000 fuel (fragment0079762Field001Chars00 ++ (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 26) (SourceJson.white (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail))))) fragment0079762Acc00200 := object_fragment0079762_field_001 fuel (fragment0079762Field002Chars00 ++ (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 25) (SourceJson.white (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail)))) fragment0079762Acc00300 := object_fragment0079762_field_002 fuel (fragment0079762Field003Chars00 ++ (fragment0079762Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 24) (SourceJson.white (fragment0079762Field004Chars00 ++ (tail))) fragment0079762Acc00400 := object_fragment0079762_field_003 fuel (fragment0079762Field004Chars00 ++ (tail))
    _ = .ok (fragment0079762Value, tail) := object_fragment0079762_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_before_reader"
  err.flush

noncomputable def chunk0000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',', '\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0000Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['2'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['2'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: ((.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['1'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['1'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0'])], .arr [.number (String.ofList ['1'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc))

theorem array_chunk0000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 80) (SourceJson.white (chunk0000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 78) (SourceJson.white tail) (chunk0000Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0000_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_before_reader"
  err.flush

noncomputable def chunk0001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0001Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['3'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['3'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 78) (SourceJson.white (chunk0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 77) (SourceJson.white tail) (chunk0001Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0001_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_before_reader"
  err.flush

noncomputable def chunk0002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0002Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['4'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['4'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 77) (SourceJson.white (chunk0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 76) (SourceJson.white tail) (chunk0002Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0002_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_before_reader"
  err.flush

noncomputable def chunk0003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', '{', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}', ',']
noncomputable def chunk0003Push00 (acc : List SourceJson) : List SourceJson :=
  (.obj [(String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's'], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]), (String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n'], .number (String.ofList ['5'])), (String.ofList ['p', 'i', 'v', 'o', 't'], .number (String.ofList ['5'])), (String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's'], .arr [.arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['0']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])], .arr [.number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5'])]]), (String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's'], .number (String.ofList ['1']))]) :: (acc)

theorem array_chunk0003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 76) (SourceJson.white (chunk0003Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 75) (SourceJson.white tail) (chunk0003Push00 acc) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0003_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_before_reader"
  err.flush

noncomputable def chunk0004LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0004SuffixChars00 : List Char := [',']
noncomputable def chunk0004Chars00 : List Char := chunk0004LeadChars00 ++ fragment0071459Chars ++ chunk0004SuffixChars00
noncomputable def chunk0004Push00 (acc : List SourceJson) : List SourceJson := fragment0071459Value :: acc

noncomputable def chunk0004AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0004_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 75)
      (SourceJson.white (chunk0004LeadChars00 ++ (fragment0071459Chars ++ rest))) acc =
      (SourceJson.value (fuel + 74) (fragment0071459Chars ++ rest)).bind
        (chunk0004AfterValue00 (fuel + 74) acc) := by rfl

theorem array_chunk0004 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 75) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 74) (SourceJson.white tail) (chunk0004Push00 acc) := by
  have hinput : chunk0004Chars00 ++ tail = chunk0004LeadChars00 ++ (fragment0071459Chars ++ (chunk0004SuffixChars00 ++ tail)) := by
    simp only [chunk0004Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 75) (SourceJson.white (chunk0004Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 75)
          (SourceJson.white (chunk0004LeadChars00 ++ (fragment0071459Chars ++ (chunk0004SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 75) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 74) (fragment0071459Chars ++ (chunk0004SuffixChars00 ++ tail))).bind
        (chunk0004AfterValue00 (fuel + 74) acc) := array_chunk0004_head fuel (chunk0004SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0071459Value, chunk0004SuffixChars00 ++ tail)).bind
        (chunk0004AfterValue00 (fuel + 74) acc) :=
      congrArg (fun result => result.bind (chunk0004AfterValue00 (fuel + 74) acc))
        (value_fragment0071459 (fuel + 53) (chunk0004SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 74) (SourceJson.white tail) (chunk0004Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0004_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_before_reader"
  err.flush

noncomputable def chunk0005LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0005SuffixChars00 : List Char := [',']
noncomputable def chunk0005Chars00 : List Char := chunk0005LeadChars00 ++ fragment0072426Chars ++ chunk0005SuffixChars00
noncomputable def chunk0005Push00 (acc : List SourceJson) : List SourceJson := fragment0072426Value :: acc

noncomputable def chunk0005AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0005_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 74)
      (SourceJson.white (chunk0005LeadChars00 ++ (fragment0072426Chars ++ rest))) acc =
      (SourceJson.value (fuel + 73) (fragment0072426Chars ++ rest)).bind
        (chunk0005AfterValue00 (fuel + 73) acc) := by rfl

theorem array_chunk0005 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 74) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 73) (SourceJson.white tail) (chunk0005Push00 acc) := by
  have hinput : chunk0005Chars00 ++ tail = chunk0005LeadChars00 ++ (fragment0072426Chars ++ (chunk0005SuffixChars00 ++ tail)) := by
    simp only [chunk0005Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 74) (SourceJson.white (chunk0005Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 74)
          (SourceJson.white (chunk0005LeadChars00 ++ (fragment0072426Chars ++ (chunk0005SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 74) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 73) (fragment0072426Chars ++ (chunk0005SuffixChars00 ++ tail))).bind
        (chunk0005AfterValue00 (fuel + 73) acc) := array_chunk0005_head fuel (chunk0005SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0072426Value, chunk0005SuffixChars00 ++ tail)).bind
        (chunk0005AfterValue00 (fuel + 73) acc) :=
      congrArg (fun result => result.bind (chunk0005AfterValue00 (fuel + 73) acc))
        (value_fragment0072426 (fuel + 28) (chunk0005SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 73) (SourceJson.white tail) (chunk0005Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0005_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0006_before_reader"
  err.flush

noncomputable def chunk0006LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0006SuffixChars00 : List Char := [',']
noncomputable def chunk0006Chars00 : List Char := chunk0006LeadChars00 ++ fragment0077111Chars ++ chunk0006SuffixChars00
noncomputable def chunk0006Push00 (acc : List SourceJson) : List SourceJson := fragment0077111Value :: acc

noncomputable def chunk0006AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0006_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 73)
      (SourceJson.white (chunk0006LeadChars00 ++ (fragment0077111Chars ++ rest))) acc =
      (SourceJson.value (fuel + 72) (fragment0077111Chars ++ rest)).bind
        (chunk0006AfterValue00 (fuel + 72) acc) := by rfl

theorem array_chunk0006 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 73) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 72) (SourceJson.white tail) (chunk0006Push00 acc) := by
  have hinput : chunk0006Chars00 ++ tail = chunk0006LeadChars00 ++ (fragment0077111Chars ++ (chunk0006SuffixChars00 ++ tail)) := by
    simp only [chunk0006Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 73) (SourceJson.white (chunk0006Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 73)
          (SourceJson.white (chunk0006LeadChars00 ++ (fragment0077111Chars ++ (chunk0006SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 73) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 72) (fragment0077111Chars ++ (chunk0006SuffixChars00 ++ tail))).bind
        (chunk0006AfterValue00 (fuel + 72) acc) := array_chunk0006_head fuel (chunk0006SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0077111Value, chunk0006SuffixChars00 ++ tail)).bind
        (chunk0006AfterValue00 (fuel + 72) acc) :=
      congrArg (fun result => result.bind (chunk0006AfterValue00 (fuel + 72) acc))
        (value_fragment0077111 (fuel + 39) (chunk0006SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 72) (SourceJson.white tail) (chunk0006Push00 acc) := by rfl

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
noncomputable def chunk0007Chars00 : List Char := chunk0007LeadChars00 ++ fragment0079762Chars ++ chunk0007SuffixChars00
noncomputable def chunk0007Push00 (acc : List SourceJson) : List SourceJson := fragment0079762Value :: acc

noncomputable def chunk0007AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0007_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 72)
      (SourceJson.white (chunk0007LeadChars00 ++ (fragment0079762Chars ++ rest))) acc =
      (SourceJson.value (fuel + 71) (fragment0079762Chars ++ rest)).bind
        (chunk0007AfterValue00 (fuel + 71) acc) := by rfl

theorem array_chunk0007 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 72) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 71) (SourceJson.white tail) (chunk0007Push00 acc) := by
  have hinput : chunk0007Chars00 ++ tail = chunk0007LeadChars00 ++ (fragment0079762Chars ++ (chunk0007SuffixChars00 ++ tail)) := by
    simp only [chunk0007Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 72) (SourceJson.white (chunk0007Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 72)
          (SourceJson.white (chunk0007LeadChars00 ++ (fragment0079762Chars ++ (chunk0007SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 72) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 71) (fragment0079762Chars ++ (chunk0007SuffixChars00 ++ tail))).bind
        (chunk0007AfterValue00 (fuel + 71) acc) := array_chunk0007_head fuel (chunk0007SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0079762Value, chunk0007SuffixChars00 ++ tail)).bind
        (chunk0007AfterValue00 (fuel + 71) acc) :=
      congrArg (fun result => result.bind (chunk0007AfterValue00 (fuel + 71) acc))
        (value_fragment0079762 (fuel + 42) (chunk0007SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 71) (SourceJson.white tail) (chunk0007Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0007_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0000Chars00 ++ chunk0001Chars00 ++ chunk0002Chars00 ++ chunk0003Chars00 ++ chunk0004Chars00 ++ chunk0005Chars00 ++ chunk0006Chars00 ++ chunk0007Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0007Push00 (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 80) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 71) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 80) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 80) (SourceJson.white (chunk0000Chars00 ++ (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 80) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 78) (SourceJson.white (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))))) (chunk0000Push00 (acc)) := array_chunk0000 fuel (chunk0001Chars00 ++ (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (acc)
    _ = SourceJson.array (fuel + 77) (SourceJson.white (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))))) (chunk0001Push00 (chunk0000Push00 (acc))) := array_chunk0001 fuel (chunk0002Chars00 ++ (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0000Push00 (acc))
    _ = SourceJson.array (fuel + 76) (SourceJson.white (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))) := array_chunk0002 fuel (chunk0003Chars00 ++ (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0001Push00 (chunk0000Push00 (acc)))
    _ = SourceJson.array (fuel + 75) (SourceJson.white (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))) := array_chunk0003 fuel (chunk0004Chars00 ++ (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))
    _ = SourceJson.array (fuel + 74) (SourceJson.white (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))) := array_chunk0004 fuel (chunk0005Chars00 ++ (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))
    _ = SourceJson.array (fuel + 73) (SourceJson.white (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail)))) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))) := array_chunk0005 fuel (chunk0006Chars00 ++ (chunk0007Chars00 ++ (tail))) (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))
    _ = SourceJson.array (fuel + 72) (SourceJson.white (chunk0007Chars00 ++ (tail))) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))) := array_chunk0006 fuel (chunk0007Chars00 ++ (tail)) (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc)))))))
    _ = SourceJson.array (fuel + 71) (SourceJson.white tail) (blockPush acc) := array_chunk0007 fuel (tail) (chunk0006Push00 (chunk0005Push00 (chunk0004Push00 (chunk0003Push00 (chunk0002Push00 (chunk0001Push00 (chunk0000Push00 (acc))))))))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 69088).take 12704 = blockChars := by rfl

theorem block_original_split : sourceRest 69088 = blockChars ++ sourceRest 81792 := by
  calc
    sourceRest 69088 = (sourceRest 69088).take 12704 ++ (sourceRest 69088).drop 12704 :=
      (List.take_append_drop 12704 (sourceRest 69088)).symm
    _ = blockChars ++ (sourceRest 69088).drop 12704 :=
      congrArg (fun part => part ++ (sourceRest 69088).drop 12704) block_original_prefix
    _ = blockChars ++ sourceRest 81792 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 69088 12704)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 80) (SourceJson.white (sourceRest 69088)) acc =
      SourceJson.array (fuel + 71) (SourceJson.white (sourceRest 81792)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 80) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 81792) acc)

#print axioms object_fragment0071459_field_000
#print axioms object_fragment0071459_field_001
#print axioms object_fragment0071459_field_002
#print axioms object_fragment0071459_field_003
#print axioms object_fragment0071459_field_004
#print axioms value_fragment0071459
#print axioms array_fragment0072941_chunk_000
#print axioms array_fragment0072941_chunk_001
#print axioms array_fragment0072941_chunk_002
#print axioms array_fragment0072941_chunk_003
#print axioms array_fragment0072941_chunk_004
#print axioms array_fragment0072941_chunk_005
#print axioms array_fragment0072941_chunk_006
#print axioms array_fragment0072941_chunk_007
#print axioms value_fragment0072941
#print axioms object_fragment0072426_field_000
#print axioms object_fragment0072426_field_001
#print axioms object_fragment0072426_field_002
#print axioms object_fragment0072426_field_003_header
#print axioms object_fragment0072426_field_003
#print axioms object_fragment0072426_field_004
#print axioms value_fragment0072426
#print axioms array_fragment0077458_chunk_000
#print axioms array_fragment0077458_chunk_001
#print axioms array_fragment0077458_chunk_002
#print axioms array_fragment0077458_chunk_003
#print axioms array_fragment0077458_chunk_004
#print axioms value_fragment0077458
#print axioms object_fragment0077111_field_000
#print axioms object_fragment0077111_field_001
#print axioms object_fragment0077111_field_002
#print axioms object_fragment0077111_field_003_header
#print axioms object_fragment0077111_field_003
#print axioms object_fragment0077111_field_004
#print axioms value_fragment0077111
#print axioms array_fragment0080071_chunk_000
#print axioms array_fragment0080071_chunk_001
#print axioms array_fragment0080071_chunk_002
#print axioms array_fragment0080071_chunk_003
#print axioms array_fragment0080071_chunk_004
#print axioms value_fragment0080071
#print axioms object_fragment0079762_field_000
#print axioms object_fragment0079762_field_001
#print axioms object_fragment0079762_field_002
#print axioms object_fragment0079762_field_003_header
#print axioms object_fragment0079762_field_003
#print axioms object_fragment0079762_field_004
#print axioms value_fragment0079762
#print axioms array_chunk0000
#print axioms array_chunk0001
#print axioms array_chunk0002
#print axioms array_chunk0003
#print axioms array_chunk0004_head
#print axioms array_chunk0004
#print axioms array_chunk0005_head
#print axioms array_chunk0005
#print axioms array_chunk0006_head
#print axioms array_chunk0006
#print axioms array_chunk0007_head
#print axioms array_chunk0007
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock000

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
