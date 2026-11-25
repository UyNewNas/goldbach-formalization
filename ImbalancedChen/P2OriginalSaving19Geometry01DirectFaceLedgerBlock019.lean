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

namespace FaceLedgerBlock019

noncomputable def fragment0222925Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0222925Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0222925Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])]
noncomputable def fragment0222925Acc00100 : List (String × SourceJson) := (fragment0222925Field000Key00, fragment0222925Field000Value00) :: fragment0222925Acc00000
noncomputable def fragment0222925Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0222925_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0222925Field000Chars00 ++ tail)) fragment0222925Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0222925Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222925_object_field_000"
  err.flush

noncomputable def fragment0222925Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0222925Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0222925Acc00200 : List (String × SourceJson) := (fragment0222925Field001Key00, fragment0222925Field001Value00) :: fragment0222925Acc00100
noncomputable def fragment0222925Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0222925_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0222925Field001Chars00 ++ tail)) fragment0222925Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0222925Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222925_object_field_001"
  err.flush

noncomputable def fragment0222925Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0222925Field002Value00 : SourceJson := .number (String.ofList ['3', '0'])
noncomputable def fragment0222925Acc00300 : List (String × SourceJson) := (fragment0222925Field002Key00, fragment0222925Field002Value00) :: fragment0222925Acc00200
noncomputable def fragment0222925Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '0', ',']

theorem object_fragment0222925_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0222925Field002Chars00 ++ tail)) fragment0222925Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0222925Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222925_object_field_002"
  err.flush

noncomputable def fragment0222925Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0222925Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '0'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])], .arr [.number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])]]
noncomputable def fragment0222925Acc00400 : List (String × SourceJson) := (fragment0222925Field003Key00, fragment0222925Field003Value00) :: fragment0222925Acc00300
noncomputable def fragment0222925Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0222925_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0222925Field003Chars00 ++ tail)) fragment0222925Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0222925Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222925_object_field_003"
  err.flush

noncomputable def fragment0222925Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0222925Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0222925Acc00500 : List (String × SourceJson) := (fragment0222925Field004Key00, fragment0222925Field004Value00) :: fragment0222925Acc00400
noncomputable def fragment0222925Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0222925_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0222925Field004Chars00 ++ tail)) fragment0222925Acc00400 =
      .ok (.obj (fragment0222925Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0222925_object_field_004"
  err.flush

noncomputable def fragment0222925Chars : List Char := '{' :: (fragment0222925Field000Chars00 ++ fragment0222925Field001Chars00 ++ fragment0222925Field002Chars00 ++ fragment0222925Field003Chars00 ++ fragment0222925Field004Chars00)
noncomputable def fragment0222925Value : SourceJson := .obj (fragment0222925Acc00500.reverse)

theorem value_fragment0222925 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0222925Chars ++ tail) =
      .ok (fragment0222925Value, tail) := by
  have hinput : fragment0222925Chars ++ tail = '{' :: (fragment0222925Field000Chars00 ++ (fragment0222925Field001Chars00 ++ (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0222925Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0222925Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0222925Field000Chars00 ++ (fragment0222925Field001Chars00 ++ (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0222925Field000Chars00 ++ (fragment0222925Field001Chars00 ++ (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail))))))) fragment0222925Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0222925Field001Chars00 ++ (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail)))))) fragment0222925Acc00100 := object_fragment0222925_field_000 fuel (fragment0222925Field001Chars00 ++ (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail))))) fragment0222925Acc00200 := object_fragment0222925_field_001 fuel (fragment0222925Field002Chars00 ++ (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail)))) fragment0222925Acc00300 := object_fragment0222925_field_002 fuel (fragment0222925Field003Chars00 ++ (fragment0222925Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0222925Field004Chars00 ++ (tail))) fragment0222925Acc00400 := object_fragment0222925_field_003 fuel (fragment0222925Field004Chars00 ++ (tail))
    _ = .ok (fragment0222925Value, tail) := object_fragment0222925_field_004 fuel (tail)

noncomputable def fragment0223914Acc00000 : List SourceJson := []

noncomputable def fragment0223914Chunk000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0223914Chunk000Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0'])]) :: (acc))

theorem array_fragment0223914_chunk_000 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 15) (SourceJson.white (fragment0223914Chunk000Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 13) (SourceJson.white tail) (fragment0223914Chunk000Push00 acc) := by
  rfl

noncomputable def fragment0223914Acc00100 : List SourceJson := fragment0223914Chunk000Push00 fragment0223914Acc00000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223914_array_chunk_000"
  err.flush

noncomputable def fragment0223914Chunk001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0223914Chunk001Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: (acc))

theorem array_fragment0223914_chunk_001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 13) (SourceJson.white (fragment0223914Chunk001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 11) (SourceJson.white tail) (fragment0223914Chunk001Push00 acc) := by
  rfl

noncomputable def fragment0223914Acc00200 : List SourceJson := fragment0223914Chunk001Push00 fragment0223914Acc00100

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223914_array_chunk_001"
  err.flush

noncomputable def fragment0223914Chunk002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']
noncomputable def fragment0223914Chunk002Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: ((.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: (acc))

theorem array_fragment0223914_chunk_002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 11) (SourceJson.white (fragment0223914Chunk002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 9) (SourceJson.white tail) (fragment0223914Chunk002Push00 acc) := by
  rfl

noncomputable def fragment0223914Acc00300 : List SourceJson := fragment0223914Chunk002Push00 fragment0223914Acc00200

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223914_array_chunk_002"
  err.flush

noncomputable def fragment0223914Chunk003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']']
noncomputable def fragment0223914Chunk003Push00 (acc : List SourceJson) : List SourceJson :=
  (.arr [.number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]) :: (acc)

theorem array_fragment0223914_chunk_003 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 9) (SourceJson.white (fragment0223914Chunk003Chars00 ++ tail)) acc =
      .ok (.arr ((fragment0223914Chunk003Push00 acc).reverse), tail) := by
  rfl

noncomputable def fragment0223914Acc00400 : List SourceJson := fragment0223914Chunk003Push00 fragment0223914Acc00300

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223914_array_chunk_003"
  err.flush

noncomputable def fragment0223914Chars : List Char := '[' :: (fragment0223914Chunk000Chars00 ++ fragment0223914Chunk001Chars00 ++ fragment0223914Chunk002Chars00 ++ fragment0223914Chunk003Chars00)
noncomputable def fragment0223914Value : SourceJson := .arr (fragment0223914Acc00400.reverse)

theorem value_fragment0223914 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 16) (fragment0223914Chars ++ tail) =
      .ok (fragment0223914Value, tail) := by
  have hinput : fragment0223914Chars ++ tail = '[' :: (fragment0223914Chunk000Chars00 ++ (fragment0223914Chunk001Chars00 ++ (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail))))) := by
    simp only [fragment0223914Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 16) (fragment0223914Chars ++ tail) =
        SourceJson.value (fuel + 16) ('[' :: (fragment0223914Chunk000Chars00 ++ (fragment0223914Chunk001Chars00 ++ (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail)))))) :=
      congrArg (SourceJson.value (fuel + 16)) hinput
    _ = SourceJson.array (fuel + 15) (SourceJson.white (fragment0223914Chunk000Chars00 ++ (fragment0223914Chunk001Chars00 ++ (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail)))))) fragment0223914Acc00000 := by rfl
    _ = SourceJson.array (fuel + 13) (SourceJson.white (fragment0223914Chunk001Chars00 ++ (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail))))) fragment0223914Acc00100 := array_fragment0223914_chunk_000 fuel (fragment0223914Chunk001Chars00 ++ (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail)))) fragment0223914Acc00000
    _ = SourceJson.array (fuel + 11) (SourceJson.white (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail)))) fragment0223914Acc00200 := array_fragment0223914_chunk_001 fuel (fragment0223914Chunk002Chars00 ++ (fragment0223914Chunk003Chars00 ++ (tail))) fragment0223914Acc00100
    _ = SourceJson.array (fuel + 9) (SourceJson.white (fragment0223914Chunk003Chars00 ++ (tail))) fragment0223914Acc00300 := array_fragment0223914_chunk_002 fuel (fragment0223914Chunk003Chars00 ++ (tail)) fragment0223914Acc00200
    _ = .ok (fragment0223914Value, tail) := array_fragment0223914_chunk_003 fuel (tail) fragment0223914Acc00300

noncomputable def fragment0223727Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0223727Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0223727Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '2'])]
noncomputable def fragment0223727Acc00100 : List (String × SourceJson) := (fragment0223727Field000Key00, fragment0223727Field000Value00) :: fragment0223727Acc00000
noncomputable def fragment0223727Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0223727_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 20) (SourceJson.white (fragment0223727Field000Chars00 ++ tail)) fragment0223727Acc00000 =
      SourceJson.object (fuel + 19) (SourceJson.white tail) fragment0223727Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223727_object_field_000"
  err.flush

noncomputable def fragment0223727Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0223727Field001Value00 : SourceJson := .number (String.ofList ['6'])
noncomputable def fragment0223727Acc00200 : List (String × SourceJson) := (fragment0223727Field001Key00, fragment0223727Field001Value00) :: fragment0223727Acc00100
noncomputable def fragment0223727Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '6', ',']

theorem object_fragment0223727_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 19) (SourceJson.white (fragment0223727Field001Chars00 ++ tail)) fragment0223727Acc00100 =
      SourceJson.object (fuel + 18) (SourceJson.white tail) fragment0223727Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223727_object_field_001"
  err.flush

noncomputable def fragment0223727Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0223727Field002Value00 : SourceJson := .number (String.ofList ['3', '2'])
noncomputable def fragment0223727Acc00300 : List (String × SourceJson) := (fragment0223727Field002Key00, fragment0223727Field002Value00) :: fragment0223727Acc00200
noncomputable def fragment0223727Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '2', ',']

theorem object_fragment0223727_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0223727Field002Chars00 ++ tail)) fragment0223727Acc00200 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0223727Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223727_object_field_002"
  err.flush

noncomputable def fragment0223727Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0223727Field003Value00 : SourceJson := fragment0223914Value
noncomputable def fragment0223727Acc00400 : List (String × SourceJson) := (fragment0223727Field003Key00, fragment0223727Field003Value00) :: fragment0223727Acc00300
noncomputable def fragment0223727Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0223727Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0223727Field003Chars00 : List Char := fragment0223727Field003HeaderChars00 ++ fragment0223914Chars ++ fragment0223727Field003SuffixChars00

noncomputable def fragment0223727Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0223727Field003Key00, result.1) :: fragment0223727Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0223727Field003Key00, result.1) :: fragment0223727Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0223727_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0223727Field003HeaderChars00 ++ rest)) fragment0223727Acc00300 =
      (SourceJson.value (fuel + 16) rest).bind (fragment0223727Field003AfterValue00 (fuel + 16)) := by rfl

theorem object_fragment0223727_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0223727Field003Chars00 ++ tail)) fragment0223727Acc00300 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0223727Acc00400 := by
  have hinput : fragment0223727Field003Chars00 ++ tail = fragment0223727Field003HeaderChars00 ++ (fragment0223914Chars ++ (fragment0223727Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0223727Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0223727Field003Chars00 ++ tail)) fragment0223727Acc00300 =
        SourceJson.object (fuel + 17)
          (SourceJson.white (fragment0223727Field003HeaderChars00 ++ (fragment0223914Chars ++ (fragment0223727Field003SuffixChars00 ++ tail)))) fragment0223727Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 17) (SourceJson.white s) fragment0223727Acc00300) hinput
    _ = (SourceJson.value (fuel + 16) (fragment0223914Chars ++ (fragment0223727Field003SuffixChars00 ++ tail))).bind
        (fragment0223727Field003AfterValue00 (fuel + 16)) := object_fragment0223727_field_003_header fuel (fragment0223914Chars ++ (fragment0223727Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0223914Value, fragment0223727Field003SuffixChars00 ++ tail)).bind (fragment0223727Field003AfterValue00 (fuel + 16)) :=
      congrArg (fun result => result.bind (fragment0223727Field003AfterValue00 (fuel + 16)))
        (value_fragment0223914 (fuel + 0) (fragment0223727Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0223727Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223727_object_field_003"
  err.flush

noncomputable def fragment0223727Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0223727Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0223727Acc00500 : List (String × SourceJson) := (fragment0223727Field004Key00, fragment0223727Field004Value00) :: fragment0223727Acc00400
noncomputable def fragment0223727Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0223727_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0223727Field004Chars00 ++ tail)) fragment0223727Acc00400 =
      .ok (.obj (fragment0223727Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0223727_object_field_004"
  err.flush

noncomputable def fragment0223727Chars : List Char := '{' :: (fragment0223727Field000Chars00 ++ fragment0223727Field001Chars00 ++ fragment0223727Field002Chars00 ++ fragment0223727Field003Chars00 ++ fragment0223727Field004Chars00)
noncomputable def fragment0223727Value : SourceJson := .obj (fragment0223727Acc00500.reverse)

theorem value_fragment0223727 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 21) (fragment0223727Chars ++ tail) =
      .ok (fragment0223727Value, tail) := by
  have hinput : fragment0223727Chars ++ tail = '{' :: (fragment0223727Field000Chars00 ++ (fragment0223727Field001Chars00 ++ (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0223727Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 21) (fragment0223727Chars ++ tail) =
        SourceJson.value (fuel + 21) ('{' :: (fragment0223727Field000Chars00 ++ (fragment0223727Field001Chars00 ++ (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 21)) hinput
    _ = SourceJson.object (fuel + 20) (SourceJson.white (fragment0223727Field000Chars00 ++ (fragment0223727Field001Chars00 ++ (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail))))))) fragment0223727Acc00000 := by rfl
    _ = SourceJson.object (fuel + 19) (SourceJson.white (fragment0223727Field001Chars00 ++ (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail)))))) fragment0223727Acc00100 := object_fragment0223727_field_000 fuel (fragment0223727Field001Chars00 ++ (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail))))) fragment0223727Acc00200 := object_fragment0223727_field_001 fuel (fragment0223727Field002Chars00 ++ (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail)))) fragment0223727Acc00300 := object_fragment0223727_field_002 fuel (fragment0223727Field003Chars00 ++ (fragment0223727Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0223727Field004Chars00 ++ (tail))) fragment0223727Acc00400 := object_fragment0223727_field_003 fuel (fragment0223727Field004Chars00 ++ (tail))
    _ = .ok (fragment0223727Value, tail) := object_fragment0223727_field_004 fuel (tail)

noncomputable def fragment0224744Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0224744Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0224744Field000Value00 : SourceJson := .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])]
noncomputable def fragment0224744Acc00100 : List (String × SourceJson) := (fragment0224744Field000Key00, fragment0224744Field000Value00) :: fragment0224744Acc00000
noncomputable def fragment0224744Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0224744_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 18) (SourceJson.white (fragment0224744Field000Chars00 ++ tail)) fragment0224744Acc00000 =
      SourceJson.object (fuel + 17) (SourceJson.white tail) fragment0224744Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224744_object_field_000"
  err.flush

noncomputable def fragment0224744Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0224744Field001Value00 : SourceJson := .number (String.ofList ['5'])
noncomputable def fragment0224744Acc00200 : List (String × SourceJson) := (fragment0224744Field001Key00, fragment0224744Field001Value00) :: fragment0224744Acc00100
noncomputable def fragment0224744Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '5', ',']

theorem object_fragment0224744_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 17) (SourceJson.white (fragment0224744Field001Chars00 ++ tail)) fragment0224744Acc00100 =
      SourceJson.object (fuel + 16) (SourceJson.white tail) fragment0224744Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224744_object_field_001"
  err.flush

noncomputable def fragment0224744Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0224744Field002Value00 : SourceJson := .number (String.ofList ['3', '2'])
noncomputable def fragment0224744Acc00300 : List (String × SourceJson) := (fragment0224744Field002Key00, fragment0224744Field002Value00) :: fragment0224744Acc00200
noncomputable def fragment0224744Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '2', ',']

theorem object_fragment0224744_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 16) (SourceJson.white (fragment0224744Field002Chars00 ++ tail)) fragment0224744Acc00200 =
      SourceJson.object (fuel + 15) (SourceJson.white tail) fragment0224744Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224744_object_field_002"
  err.flush

noncomputable def fragment0224744Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0224744Field003Value00 : SourceJson := .arr [.arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['3', '2'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])], .arr [.number (String.ofList ['1', '6']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])], .arr [.number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['3', '2'])]]
noncomputable def fragment0224744Acc00400 : List (String × SourceJson) := (fragment0224744Field003Key00, fragment0224744Field003Value00) :: fragment0224744Acc00300
noncomputable def fragment0224744Field003Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ']', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0224744_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 15) (SourceJson.white (fragment0224744Field003Chars00 ++ tail)) fragment0224744Acc00300 =
      SourceJson.object (fuel + 14) (SourceJson.white tail) fragment0224744Acc00400 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224744_object_field_003"
  err.flush

noncomputable def fragment0224744Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0224744Field004Value00 : SourceJson := .number (String.ofList ['1'])
noncomputable def fragment0224744Acc00500 : List (String × SourceJson) := (fragment0224744Field004Key00, fragment0224744Field004Value00) :: fragment0224744Acc00400
noncomputable def fragment0224744Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0224744_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 14) (SourceJson.white (fragment0224744Field004Chars00 ++ tail)) fragment0224744Acc00400 =
      .ok (.obj (fragment0224744Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0224744_object_field_004"
  err.flush

noncomputable def fragment0224744Chars : List Char := '{' :: (fragment0224744Field000Chars00 ++ fragment0224744Field001Chars00 ++ fragment0224744Field002Chars00 ++ fragment0224744Field003Chars00 ++ fragment0224744Field004Chars00)
noncomputable def fragment0224744Value : SourceJson := .obj (fragment0224744Acc00500.reverse)

theorem value_fragment0224744 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 19) (fragment0224744Chars ++ tail) =
      .ok (fragment0224744Value, tail) := by
  have hinput : fragment0224744Chars ++ tail = '{' :: (fragment0224744Field000Chars00 ++ (fragment0224744Field001Chars00 ++ (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0224744Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 19) (fragment0224744Chars ++ tail) =
        SourceJson.value (fuel + 19) ('{' :: (fragment0224744Field000Chars00 ++ (fragment0224744Field001Chars00 ++ (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 19)) hinput
    _ = SourceJson.object (fuel + 18) (SourceJson.white (fragment0224744Field000Chars00 ++ (fragment0224744Field001Chars00 ++ (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail))))))) fragment0224744Acc00000 := by rfl
    _ = SourceJson.object (fuel + 17) (SourceJson.white (fragment0224744Field001Chars00 ++ (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail)))))) fragment0224744Acc00100 := object_fragment0224744_field_000 fuel (fragment0224744Field001Chars00 ++ (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 16) (SourceJson.white (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail))))) fragment0224744Acc00200 := object_fragment0224744_field_001 fuel (fragment0224744Field002Chars00 ++ (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 15) (SourceJson.white (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail)))) fragment0224744Acc00300 := object_fragment0224744_field_002 fuel (fragment0224744Field003Chars00 ++ (fragment0224744Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 14) (SourceJson.white (fragment0224744Field004Chars00 ++ (tail))) fragment0224744Acc00400 := object_fragment0224744_field_003 fuel (fragment0224744Field004Chars00 ++ (tail))
    _ = .ok (fragment0224744Value, tail) := object_fragment0224744_field_004 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0062_before_reader"
  err.flush

noncomputable def chunk0062LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0062SuffixChars00 : List Char := [',']
noncomputable def chunk0062Chars00 : List Char := chunk0062LeadChars00 ++ fragment0222925Chars ++ chunk0062SuffixChars00
noncomputable def chunk0062Push00 (acc : List SourceJson) : List SourceJson := fragment0222925Value :: acc

noncomputable def chunk0062AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0062_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23)
      (SourceJson.white (chunk0062LeadChars00 ++ (fragment0222925Chars ++ rest))) acc =
      (SourceJson.value (fuel + 22) (fragment0222925Chars ++ rest)).bind
        (chunk0062AfterValue00 (fuel + 22) acc) := by rfl

theorem array_chunk0062 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (chunk0062Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 22) (SourceJson.white tail) (chunk0062Push00 acc) := by
  have hinput : chunk0062Chars00 ++ tail = chunk0062LeadChars00 ++ (fragment0222925Chars ++ (chunk0062SuffixChars00 ++ tail)) := by
    simp only [chunk0062Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 23) (SourceJson.white (chunk0062Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 23)
          (SourceJson.white (chunk0062LeadChars00 ++ (fragment0222925Chars ++ (chunk0062SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 23) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 22) (fragment0222925Chars ++ (chunk0062SuffixChars00 ++ tail))).bind
        (chunk0062AfterValue00 (fuel + 22) acc) := array_chunk0062_head fuel (chunk0062SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0222925Value, chunk0062SuffixChars00 ++ tail)).bind
        (chunk0062AfterValue00 (fuel + 22) acc) :=
      congrArg (fun result => result.bind (chunk0062AfterValue00 (fuel + 22) acc))
        (value_fragment0222925 (fuel + 3) (chunk0062SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 22) (SourceJson.white tail) (chunk0062Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0062_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0063_before_reader"
  err.flush

noncomputable def chunk0063LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0063SuffixChars00 : List Char := [',']
noncomputable def chunk0063Chars00 : List Char := chunk0063LeadChars00 ++ fragment0223727Chars ++ chunk0063SuffixChars00
noncomputable def chunk0063Push00 (acc : List SourceJson) : List SourceJson := fragment0223727Value :: acc

noncomputable def chunk0063AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0063_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22)
      (SourceJson.white (chunk0063LeadChars00 ++ (fragment0223727Chars ++ rest))) acc =
      (SourceJson.value (fuel + 21) (fragment0223727Chars ++ rest)).bind
        (chunk0063AfterValue00 (fuel + 21) acc) := by rfl

theorem array_chunk0063 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 22) (SourceJson.white (chunk0063Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 21) (SourceJson.white tail) (chunk0063Push00 acc) := by
  have hinput : chunk0063Chars00 ++ tail = chunk0063LeadChars00 ++ (fragment0223727Chars ++ (chunk0063SuffixChars00 ++ tail)) := by
    simp only [chunk0063Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 22) (SourceJson.white (chunk0063Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 22)
          (SourceJson.white (chunk0063LeadChars00 ++ (fragment0223727Chars ++ (chunk0063SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 22) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 21) (fragment0223727Chars ++ (chunk0063SuffixChars00 ++ tail))).bind
        (chunk0063AfterValue00 (fuel + 21) acc) := array_chunk0063_head fuel (chunk0063SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0223727Value, chunk0063SuffixChars00 ++ tail)).bind
        (chunk0063AfterValue00 (fuel + 21) acc) :=
      congrArg (fun result => result.bind (chunk0063AfterValue00 (fuel + 21) acc))
        (value_fragment0223727 (fuel + 0) (chunk0063SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 21) (SourceJson.white tail) (chunk0063Push00 acc) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0063_reader_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0064_before_reader"
  err.flush

noncomputable def chunk0064LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def chunk0064SuffixChars00 : List Char := ['\r', '\n', ' ', ' ', ']']
noncomputable def chunk0064Chars00 : List Char := chunk0064LeadChars00 ++ fragment0224744Chars ++ chunk0064SuffixChars00
noncomputable def chunk0064Push00 (acc : List SourceJson) : List SourceJson := fragment0224744Value :: acc

noncomputable def chunk0064AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_chunk0064_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21)
      (SourceJson.white (chunk0064LeadChars00 ++ (fragment0224744Chars ++ rest))) acc =
      (SourceJson.value (fuel + 20) (fragment0224744Chars ++ rest)).bind
        (chunk0064AfterValue00 (fuel + 20) acc) := by rfl

theorem array_chunk0064 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 21) (SourceJson.white (chunk0064Chars00 ++ tail)) acc =
      .ok (.arr ((chunk0064Push00 acc).reverse), tail) := by
  have hinput : chunk0064Chars00 ++ tail = chunk0064LeadChars00 ++ (fragment0224744Chars ++ (chunk0064SuffixChars00 ++ tail)) := by
    simp only [chunk0064Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 21) (SourceJson.white (chunk0064Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 21)
          (SourceJson.white (chunk0064LeadChars00 ++ (fragment0224744Chars ++ (chunk0064SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 21) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 20) (fragment0224744Chars ++ (chunk0064SuffixChars00 ++ tail))).bind
        (chunk0064AfterValue00 (fuel + 20) acc) := array_chunk0064_head fuel (chunk0064SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0224744Value, chunk0064SuffixChars00 ++ tail)).bind
        (chunk0064AfterValue00 (fuel + 20) acc) :=
      congrArg (fun result => result.bind (chunk0064AfterValue00 (fuel + 20) acc))
        (value_fragment0224744 (fuel + 1) (chunk0064SuffixChars00 ++ tail))
    _ = .ok (.arr ((chunk0064Push00 acc).reverse), tail) := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED chunk0064_reader_complete"
  err.flush

noncomputable def blockChars : List Char := chunk0062Chars00 ++ chunk0063Chars00 ++ chunk0064Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := chunk0064Push00 (chunk0063Push00 (chunk0062Push00 (acc)))

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (blockChars ++ tail)) acc =
      .ok (.arr ((blockPush acc).reverse), tail) := by
  have hinput : blockChars ++ tail = chunk0062Chars00 ++ (chunk0063Chars00 ++ (chunk0064Chars00 ++ (tail))) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 23) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 23) (SourceJson.white (chunk0062Chars00 ++ (chunk0063Chars00 ++ (chunk0064Chars00 ++ (tail))))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 23) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 22) (SourceJson.white (chunk0063Chars00 ++ (chunk0064Chars00 ++ (tail)))) (chunk0062Push00 (acc)) := array_chunk0062 fuel (chunk0063Chars00 ++ (chunk0064Chars00 ++ (tail))) (acc)
    _ = SourceJson.array (fuel + 21) (SourceJson.white (chunk0064Chars00 ++ (tail))) (chunk0063Push00 (chunk0062Push00 (acc))) := array_chunk0063 fuel (chunk0064Chars00 ++ (tail)) (chunk0062Push00 (acc))
    _ = .ok (.arr ((blockPush acc).reverse), tail) := array_chunk0064 fuel (tail) (chunk0063Push00 (chunk0062Push00 (acc)))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED block_before_packed_binding"
  err.flush

theorem block_original_prefix :
    (sourceRest 222919).take 2625 = blockChars := by rfl

theorem block_original_split : sourceRest 222919 = blockChars ++ sourceRest 225544 := by
  calc
    sourceRest 222919 = (sourceRest 222919).take 2625 ++ (sourceRest 222919).drop 2625 :=
      (List.take_append_drop 2625 (sourceRest 222919)).symm
    _ = blockChars ++ (sourceRest 222919).drop 2625 :=
      congrArg (fun part => part ++ (sourceRest 222919).drop 2625) block_original_prefix
    _ = blockChars ++ sourceRest 225544 :=
      congrArg (fun tail => blockChars ++ tail) (sourceRest_drop 222919 2625)

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 23) (SourceJson.white (sourceRest 222919)) acc =
      .ok (.arr ((blockPush acc).reverse), sourceRest 225544) :=
  (congrArg (fun chars => SourceJson.array (fuel + 23) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 225544) acc)

#print axioms object_fragment0222925_field_000
#print axioms object_fragment0222925_field_001
#print axioms object_fragment0222925_field_002
#print axioms object_fragment0222925_field_003
#print axioms object_fragment0222925_field_004
#print axioms value_fragment0222925
#print axioms array_fragment0223914_chunk_000
#print axioms array_fragment0223914_chunk_001
#print axioms array_fragment0223914_chunk_002
#print axioms array_fragment0223914_chunk_003
#print axioms value_fragment0223914
#print axioms object_fragment0223727_field_000
#print axioms object_fragment0223727_field_001
#print axioms object_fragment0223727_field_002
#print axioms object_fragment0223727_field_003_header
#print axioms object_fragment0223727_field_003
#print axioms object_fragment0223727_field_004
#print axioms value_fragment0223727
#print axioms object_fragment0224744_field_000
#print axioms object_fragment0224744_field_001
#print axioms object_fragment0224744_field_002
#print axioms object_fragment0224744_field_003
#print axioms object_fragment0224744_field_004
#print axioms value_fragment0224744
#print axioms array_chunk0062_head
#print axioms array_chunk0062
#print axioms array_chunk0063_head
#print axioms array_chunk0063
#print axioms array_chunk0064_head
#print axioms array_chunk0064
#print axioms array_block
#print axioms block_original_prefix
#print axioms block_original_split
#print axioms array_block_original

end FaceLedgerBlock019

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
