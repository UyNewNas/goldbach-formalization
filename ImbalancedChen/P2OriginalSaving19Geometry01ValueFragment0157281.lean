import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput
import ImbalancedChen.P2OriginalSaving19Geometry01ValueFragment0157887

/-! Original self-delimiting child; structured readers use separately checked child certificates.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

noncomputable def fragment0157281Acc00000 : List (String × SourceJson) := []

noncomputable def fragment0157281Field000Key00 : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's']
noncomputable def fragment0157281Field000Value00 : SourceJson := .arr [.number (String.ofList ['0']), .number (String.ofList ['1']), .number (String.ofList ['2']), .number (String.ofList ['3']), .number (String.ofList ['4']), .number (String.ofList ['5']), .number (String.ofList ['6']), .number (String.ofList ['7']), .number (String.ofList ['8']), .number (String.ofList ['9']), .number (String.ofList ['1', '0']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '9']), .number (String.ofList ['2', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '8']), .number (String.ofList ['2', '9']), .number (String.ofList ['3', '0']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '4']), .number (String.ofList ['3', '5']), .number (String.ofList ['3', '6']), .number (String.ofList ['3', '7']), .number (String.ofList ['3', '8']), .number (String.ofList ['3', '9'])]
noncomputable def fragment0157281Acc00100 : List (String × SourceJson) := (fragment0157281Field000Key00, fragment0157281Field000Value00) :: fragment0157281Acc00000
noncomputable def fragment0157281Field000Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '"', ':', ' ', '[', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '1', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '2', '9', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '0', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '1', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '2', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '3', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '4', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '5', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '6', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '7', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '8', ',', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ' ', ' ', '3', '9', '\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', ']', ',']

theorem object_fragment0157281_field_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 51) (SourceJson.white (fragment0157281Field000Chars00 ++ tail)) fragment0157281Acc00000 =
      SourceJson.object (fuel + 50) (SourceJson.white tail) fragment0157281Acc00100 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157281_object_field_000"
  err.flush

noncomputable def fragment0157281Field001Key00 : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def fragment0157281Field001Value00 : SourceJson := .number (String.ofList ['8'])
noncomputable def fragment0157281Acc00200 : List (String × SourceJson) := (fragment0157281Field001Key00, fragment0157281Field001Value00) :: fragment0157281Acc00100
noncomputable def fragment0157281Field001Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',']

theorem object_fragment0157281_field_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 50) (SourceJson.white (fragment0157281Field001Chars00 ++ tail)) fragment0157281Acc00100 =
      SourceJson.object (fuel + 49) (SourceJson.white tail) fragment0157281Acc00200 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157281_object_field_001"
  err.flush

noncomputable def fragment0157281Field002Key00 : String := String.ofList ['p', 'i', 'v', 'o', 't']
noncomputable def fragment0157281Field002Value00 : SourceJson := .number (String.ofList ['3', '9'])
noncomputable def fragment0157281Acc00300 : List (String × SourceJson) := (fragment0157281Field002Key00, fragment0157281Field002Value00) :: fragment0157281Acc00200
noncomputable def fragment0157281Field002Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'p', 'i', 'v', 'o', 't', '"', ':', ' ', '3', '9', ',']

theorem object_fragment0157281_field_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 49) (SourceJson.white (fragment0157281Field002Chars00 ++ tail)) fragment0157281Acc00200 =
      SourceJson.object (fuel + 48) (SourceJson.white tail) fragment0157281Acc00300 := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157281_object_field_002"
  err.flush

noncomputable def fragment0157281Field003Key00 : String := String.ofList ['f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's']
noncomputable def fragment0157281Field003Value00 : SourceJson := fragment0157887Value
noncomputable def fragment0157281Acc00400 : List (String × SourceJson) := (fragment0157281Field003Key00, fragment0157281Field003Value00) :: fragment0157281Acc00300
noncomputable def fragment0157281Field003HeaderChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 'f', 'a', 'c', 'e', 't', '_', 's', 'e', 't', 's', '"', ':', ' ']
noncomputable def fragment0157281Field003SuffixChars00 : List Char := [',']
noncomputable def fragment0157281Field003Chars00 : List Char := fragment0157281Field003HeaderChars00 ++ fragment0157887Chars ++ fragment0157281Field003SuffixChars00

noncomputable def fragment0157281Field003AfterValue00 (fuel : Nat) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | '}' :: ending => .ok (.obj (((fragment0157281Field003Key00, result.1) :: fragment0157281Acc00300).reverse), ending)
  | ',' :: ending => SourceJson.object fuel (SourceJson.white ending) ((fragment0157281Field003Key00, result.1) :: fragment0157281Acc00300)
  | _ => .error "object separator missing"

theorem object_fragment0157281_field_003_header (fuel : Nat) (rest : List Char) :
    SourceJson.object (fuel + 48) (SourceJson.white (fragment0157281Field003HeaderChars00 ++ rest)) fragment0157281Acc00300 =
      (SourceJson.value (fuel + 47) rest).bind (fragment0157281Field003AfterValue00 (fuel + 47)) := by rfl

theorem object_fragment0157281_field_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 48) (SourceJson.white (fragment0157281Field003Chars00 ++ tail)) fragment0157281Acc00300 =
      SourceJson.object (fuel + 47) (SourceJson.white tail) fragment0157281Acc00400 := by
  have hinput : fragment0157281Field003Chars00 ++ tail = fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ tail)) := by
    simp only [fragment0157281Field003Chars00, List.append_assoc]
  calc
    SourceJson.object (fuel + 48) (SourceJson.white (fragment0157281Field003Chars00 ++ tail)) fragment0157281Acc00300 =
        SourceJson.object (fuel + 48)
          (SourceJson.white (fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ tail)))) fragment0157281Acc00300 :=
      congrArg (fun s => SourceJson.object (fuel + 48) (SourceJson.white s) fragment0157281Acc00300) hinput
    _ = (SourceJson.value (fuel + 47) (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ tail))).bind
        (fragment0157281Field003AfterValue00 (fuel + 47)) := object_fragment0157281_field_003_header fuel (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ tail))
    _ = (Except.ok (fragment0157887Value, fragment0157281Field003SuffixChars00 ++ tail)).bind (fragment0157281Field003AfterValue00 (fuel + 47)) :=
      congrArg (fun result => result.bind (fragment0157281Field003AfterValue00 (fuel + 47)))
        (value_fragment0157887 (fuel + 0) (fragment0157281Field003SuffixChars00 ++ tail))
    _ = SourceJson.object (fuel + 47) (SourceJson.white tail) fragment0157281Acc00400 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157281_object_field_003"
  err.flush

noncomputable def fragment0157281Field004Key00 : String := String.ofList ['s', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's']
noncomputable def fragment0157281Field004Value00 : SourceJson := .number (String.ofList ['1', '4', '4'])
noncomputable def fragment0157281Acc00500 : List (String × SourceJson) := (fragment0157281Field004Key00, fragment0157281Field004Value00) :: fragment0157281Acc00400
noncomputable def fragment0157281Field004Chars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ', ' ', ' ', '"', 's', 'i', 'm', 'p', 'l', 'i', 'c', 'e', 's', '"', ':', ' ', '1', '4', '4', '\r', '\n', ' ', ' ', ' ', ' ', '}']

theorem object_fragment0157281_field_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 47) (SourceJson.white (fragment0157281Field004Chars00 ++ tail)) fragment0157281Acc00400 =
      .ok (.obj (fragment0157281Acc00500.reverse), tail) := by
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED fragment0157281_object_field_004"
  err.flush

noncomputable def fragment0157281Chars : List Char := '{' :: (fragment0157281Field000Chars00 ++ fragment0157281Field001Chars00 ++ fragment0157281Field002Chars00 ++ fragment0157281Field003Chars00 ++ fragment0157281Field004Chars00)
noncomputable def fragment0157281Value : SourceJson := .obj (fragment0157281Acc00500.reverse)

theorem value_fragment0157281 (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 52) (fragment0157281Chars ++ tail) =
      .ok (fragment0157281Value, tail) := by
  have hinput : fragment0157281Chars ++ tail = '{' :: (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail)))))) := by
    simp only [fragment0157281Chars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 52) (fragment0157281Chars ++ tail) =
        SourceJson.value (fuel + 52) ('{' :: (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail))))))) :=
      congrArg (SourceJson.value (fuel + 52)) hinput
    _ = SourceJson.object (fuel + 51) (SourceJson.white (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail))))))) fragment0157281Acc00000 := by rfl
    _ = SourceJson.object (fuel + 50) (SourceJson.white (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail)))))) fragment0157281Acc00100 := object_fragment0157281_field_000 fuel (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail)))))
    _ = SourceJson.object (fuel + 49) (SourceJson.white (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail))))) fragment0157281Acc00200 := object_fragment0157281_field_001 fuel (fragment0157281Field002Chars00 ++ (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail))))
    _ = SourceJson.object (fuel + 48) (SourceJson.white (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail)))) fragment0157281Acc00300 := object_fragment0157281_field_002 fuel (fragment0157281Field003Chars00 ++ (fragment0157281Field004Chars00 ++ (tail)))
    _ = SourceJson.object (fuel + 47) (SourceJson.white (fragment0157281Field004Chars00 ++ (tail))) fragment0157281Acc00400 := object_fragment0157281_field_003 fuel (fragment0157281Field004Chars00 ++ (tail))
    _ = .ok (fragment0157281Value, tail) := object_fragment0157281_field_004 fuel (tail)

noncomputable def fragment0157281OpenChars : List Char := ['{']

theorem fragment0157281_open_prefix :
    (sourceRest 157281).take 1 = fragment0157281OpenChars := by rfl

theorem fragment0157281_open_split : sourceRest 157281 = fragment0157281OpenChars ++ sourceRest 157282 := by
  calc
    sourceRest 157281 = (sourceRest 157281).take 1 ++ (sourceRest 157281).drop 1 :=
      (List.take_append_drop 1 (sourceRest 157281)).symm
    _ = fragment0157281OpenChars ++ (sourceRest 157281).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 157281).drop 1) fragment0157281_open_prefix
    _ = fragment0157281OpenChars ++ sourceRest 157282 :=
      congrArg (fun tail => fragment0157281OpenChars ++ tail) (sourceRest_drop 157281 1)

theorem fragment0157281Field000_original_prefix :
    (sourceRest 157282).take 540 = fragment0157281Field000Chars00 := by rfl

theorem fragment0157281Field000_original_split : sourceRest 157282 = fragment0157281Field000Chars00 ++ sourceRest 157822 := by
  calc
    sourceRest 157282 = (sourceRest 157282).take 540 ++ (sourceRest 157282).drop 540 :=
      (List.take_append_drop 540 (sourceRest 157282)).symm
    _ = fragment0157281Field000Chars00 ++ (sourceRest 157282).drop 540 :=
      congrArg (fun part => part ++ (sourceRest 157282).drop 540) fragment0157281Field000_original_prefix
    _ = fragment0157281Field000Chars00 ++ sourceRest 157822 :=
      congrArg (fun tail => fragment0157281Field000Chars00 ++ tail) (sourceRest_drop 157282 540)

theorem fragment0157281Field001_original_prefix :
    (sourceRest 157822).take 23 = fragment0157281Field001Chars00 := by rfl

theorem fragment0157281Field001_original_split : sourceRest 157822 = fragment0157281Field001Chars00 ++ sourceRest 157845 := by
  calc
    sourceRest 157822 = (sourceRest 157822).take 23 ++ (sourceRest 157822).drop 23 :=
      (List.take_append_drop 23 (sourceRest 157822)).symm
    _ = fragment0157281Field001Chars00 ++ (sourceRest 157822).drop 23 :=
      congrArg (fun part => part ++ (sourceRest 157822).drop 23) fragment0157281Field001_original_prefix
    _ = fragment0157281Field001Chars00 ++ sourceRest 157845 :=
      congrArg (fun tail => fragment0157281Field001Chars00 ++ tail) (sourceRest_drop 157822 23)

theorem fragment0157281Field002_original_prefix :
    (sourceRest 157845).take 20 = fragment0157281Field002Chars00 := by rfl

theorem fragment0157281Field002_original_split : sourceRest 157845 = fragment0157281Field002Chars00 ++ sourceRest 157865 := by
  calc
    sourceRest 157845 = (sourceRest 157845).take 20 ++ (sourceRest 157845).drop 20 :=
      (List.take_append_drop 20 (sourceRest 157845)).symm
    _ = fragment0157281Field002Chars00 ++ (sourceRest 157845).drop 20 :=
      congrArg (fun part => part ++ (sourceRest 157845).drop 20) fragment0157281Field002_original_prefix
    _ = fragment0157281Field002Chars00 ++ sourceRest 157865 :=
      congrArg (fun tail => fragment0157281Field002Chars00 ++ tail) (sourceRest_drop 157845 20)

theorem fragment0157281Field003_header_prefix :
    (sourceRest 157865).take 22 = fragment0157281Field003HeaderChars00 := by rfl

theorem fragment0157281Field003_header_split : sourceRest 157865 = fragment0157281Field003HeaderChars00 ++ sourceRest 157887 := by
  calc
    sourceRest 157865 = (sourceRest 157865).take 22 ++ (sourceRest 157865).drop 22 :=
      (List.take_append_drop 22 (sourceRest 157865)).symm
    _ = fragment0157281Field003HeaderChars00 ++ (sourceRest 157865).drop 22 :=
      congrArg (fun part => part ++ (sourceRest 157865).drop 22) fragment0157281Field003_header_prefix
    _ = fragment0157281Field003HeaderChars00 ++ sourceRest 157887 :=
      congrArg (fun tail => fragment0157281Field003HeaderChars00 ++ tail) (sourceRest_drop 157865 22)

theorem fragment0157281Field003_suffix_prefix :
    (sourceRest 162880).take 1 = fragment0157281Field003SuffixChars00 := by rfl

theorem fragment0157281Field003_suffix_split : sourceRest 162880 = fragment0157281Field003SuffixChars00 ++ sourceRest 162881 := by
  calc
    sourceRest 162880 = (sourceRest 162880).take 1 ++ (sourceRest 162880).drop 1 :=
      (List.take_append_drop 1 (sourceRest 162880)).symm
    _ = fragment0157281Field003SuffixChars00 ++ (sourceRest 162880).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 162880).drop 1) fragment0157281Field003_suffix_prefix
    _ = fragment0157281Field003SuffixChars00 ++ sourceRest 162881 :=
      congrArg (fun tail => fragment0157281Field003SuffixChars00 ++ tail) (sourceRest_drop 162880 1)

theorem fragment0157281Field004_original_prefix :
    (sourceRest 162881).take 31 = fragment0157281Field004Chars00 := by rfl

theorem fragment0157281Field004_original_split : sourceRest 162881 = fragment0157281Field004Chars00 ++ sourceRest 162912 := by
  calc
    sourceRest 162881 = (sourceRest 162881).take 31 ++ (sourceRest 162881).drop 31 :=
      (List.take_append_drop 31 (sourceRest 162881)).symm
    _ = fragment0157281Field004Chars00 ++ (sourceRest 162881).drop 31 :=
      congrArg (fun part => part ++ (sourceRest 162881).drop 31) fragment0157281Field004_original_prefix
    _ = fragment0157281Field004Chars00 ++ sourceRest 162912 :=
      congrArg (fun tail => fragment0157281Field004Chars00 ++ tail) (sourceRest_drop 162881 31)

theorem fragment0157281_original_split : sourceRest 157281 = fragment0157281Chars ++ sourceRest 162912 := by
  calc
    sourceRest 157281 = fragment0157281OpenChars ++ (sourceRest 157282) := fragment0157281_open_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (sourceRest 157822)) := congrArg (fun rest => fragment0157281OpenChars ++ (rest)) fragment0157281Field000_original_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (sourceRest 157845))) := congrArg (fun rest => fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (rest))) fragment0157281Field001_original_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (sourceRest 157865)))) := congrArg (fun rest => fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (rest)))) fragment0157281Field002_original_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (sourceRest 157887))))) := congrArg (fun rest => fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (rest))))) fragment0157281Field003_header_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (sourceRest 162880)))))) := congrArg (fun rest => fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (rest)))))) fragment0157887_original_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ (sourceRest 162881))))))) := congrArg (fun rest => fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (rest))))))) fragment0157281Field003_suffix_split
    _ = fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ (fragment0157281Field004Chars00 ++ (sourceRest 162912)))))))) := congrArg (fun rest => fragment0157281OpenChars ++ (fragment0157281Field000Chars00 ++ (fragment0157281Field001Chars00 ++ (fragment0157281Field002Chars00 ++ (fragment0157281Field003HeaderChars00 ++ (fragment0157887Chars ++ (fragment0157281Field003SuffixChars00 ++ (rest)))))))) fragment0157281Field004_original_split
    _ = fragment0157281Chars ++ sourceRest 162912 := by simp only [fragment0157281Chars, fragment0157281OpenChars, fragment0157281Field003Chars00, List.cons_append, List.nil_append, List.append_assoc]

theorem value_fragment0157281_original (fuel : Nat) :
    SourceJson.value (fuel + 52) (sourceRest 157281) =
      .ok (fragment0157281Value, sourceRest 162912) :=
  (congrArg (SourceJson.value (fuel + 52)) fragment0157281_original_split).trans
    (value_fragment0157281 fuel (sourceRest 162912))

#print axioms object_fragment0157281_field_000
#print axioms object_fragment0157281_field_001
#print axioms object_fragment0157281_field_002
#print axioms object_fragment0157281_field_003_header
#print axioms object_fragment0157281_field_003
#print axioms object_fragment0157281_field_004
#print axioms value_fragment0157281
#print axioms fragment0157281_open_prefix
#print axioms fragment0157281_open_split
#print axioms fragment0157281Field000_original_prefix
#print axioms fragment0157281Field000_original_split
#print axioms fragment0157281Field001_original_prefix
#print axioms fragment0157281Field001_original_split
#print axioms fragment0157281Field002_original_prefix
#print axioms fragment0157281Field002_original_split
#print axioms fragment0157281Field003_header_prefix
#print axioms fragment0157281Field003_header_split
#print axioms fragment0157281Field003_suffix_prefix
#print axioms fragment0157281Field003_suffix_split
#print axioms fragment0157281Field004_original_prefix
#print axioms fragment0157281Field004_original_split
#print axioms fragment0157281_original_split
#print axioms value_fragment0157281_original

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
