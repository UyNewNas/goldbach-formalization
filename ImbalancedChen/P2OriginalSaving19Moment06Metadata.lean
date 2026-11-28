/- SOURCE_CANDIDATE: original Cell06 source only. No Lean compilation,
independent kernel replay, full-owned audit or formal acceptance is claimed. -/

import ImbalancedChen.P2OriginalSaving19Moment06Input

/-! The first nine original metadata fields, including root opening and original duplicate-key checks.
Candidate quotations preserve exact original raw bytes. The Lean equations bind
them to the production-compatible packed input and run the unchanged reader.
This local input resolves inside this private project, not the P1 filesystem. -/
namespace ImbalancedChen.P2OriginalSaving19Moment06Parsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive

noncomputable def momentMetadataAcc000 : List (String × SourceJson) := []

noncomputable def momentMetadataField000Key : String := String.ofList ['c', 'e', 'l', 'l', '_', 'i', 'd']
noncomputable def momentMetadataField000Value : SourceJson := .number (String.ofList ['6'])
noncomputable def momentMetadataField000Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'c', 'e', 'l', 'l', '_', 'i', 'd', '"', ':', ' ', '6', ',']
noncomputable def momentMetadataAcc001 : List (String × SourceJson) := (momentMetadataField000Key, momentMetadataField000Value) :: momentMetadataAcc000

theorem object_moment_metadata_000 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 161) (SourceJson.white (momentMetadataField000Chars ++ tail)) momentMetadataAcc000 =
      SourceJson.object (fuel + 160) (SourceJson.white tail) momentMetadataAcc001 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_000_generic_complete"
  err.flush

noncomputable def momentMetadataField001Key : String := String.ofList ['s', 'o', 'u', 'r', 'c', 'e', '_', 'w', 'i', 't', 'n', 'e', 's', 's']
noncomputable def momentMetadataField001Value : SourceJson := .str (String.ofList ['e', 'i', 'g', 'h', 't', 'h', '-', 't', 'h', 'i', 'r', 'd', '-', 'm', 'i', 'n', 'o', 'r', 'a', 'n', 't', '-', 'e', 'x', 't', 'e', 'n', 's', 'i', 'o', 'n', '-', '2', '0', '2', '6', '1', '0', '0', '9', '-', 'a', '2', '3', '-', 's', '2', '3', '_', 'l', 'o', 'w', '-', '0', '6', '-', 'c', 'e', 'l', 'l', '.', 'w', 'i', 't', 'n', 'e', 's', 's', '.', 'j', 's', 'o', 'n'])
noncomputable def momentMetadataField001Chars : List Char := ['\r', '\n', ' ', ' ', '"', 's', 'o', 'u', 'r', 'c', 'e', '_', 'w', 'i', 't', 'n', 'e', 's', 's', '"', ':', ' ', '"', 'e', 'i', 'g', 'h', 't', 'h', '-', 't', 'h', 'i', 'r', 'd', '-', 'm', 'i', 'n', 'o', 'r', 'a', 'n', 't', '-', 'e', 'x', 't', 'e', 'n', 's', 'i', 'o', 'n', '-', '2', '0', '2', '6', '1', '0', '0', '9', '-', 'a', '2', '3', '-', 's', '2', '3', '_', 'l', 'o', 'w', '-', '0', '6', '-', 'c', 'e', 'l', 'l', '.', 'w', 'i', 't', 'n', 'e', 's', 's', '.', 'j', 's', 'o', 'n', '"', ',']
noncomputable def momentMetadataAcc002 : List (String × SourceJson) := (momentMetadataField001Key, momentMetadataField001Value) :: momentMetadataAcc001

theorem object_moment_metadata_001 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 160) (SourceJson.white (momentMetadataField001Chars ++ tail)) momentMetadataAcc001 =
      SourceJson.object (fuel + 159) (SourceJson.white tail) momentMetadataAcc002 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_001_generic_complete"
  err.flush

noncomputable def momentMetadataField002Key : String := String.ofList ['d', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n']
noncomputable def momentMetadataField002Value : SourceJson := .number (String.ofList ['8'])
noncomputable def momentMetadataField002Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'd', 'i', 'm', 'e', 'n', 's', 'i', 'o', 'n', '"', ':', ' ', '8', ',']
noncomputable def momentMetadataAcc003 : List (String × SourceJson) := (momentMetadataField002Key, momentMetadataField002Value) :: momentMetadataAcc002

theorem object_moment_metadata_002 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 159) (SourceJson.white (momentMetadataField002Chars ++ tail)) momentMetadataAcc002 =
      SourceJson.object (fuel + 158) (SourceJson.white tail) momentMetadataAcc003 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_002_generic_complete"
  err.flush

noncomputable def momentMetadataField003Key : String := String.ofList ['v', 'e', 'r', 't', 'i', 'c', 'e', 's', '_', 'p', 'e', 'r', '_', 's', 'i', 'm', 'p', 'l', 'e', 'x']
noncomputable def momentMetadataField003Value : SourceJson := .number (String.ofList ['9'])
noncomputable def momentMetadataField003Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'v', 'e', 'r', 't', 'i', 'c', 'e', 's', '_', 'p', 'e', 'r', '_', 's', 'i', 'm', 'p', 'l', 'e', 'x', '"', ':', ' ', '9', ',']
noncomputable def momentMetadataAcc004 : List (String × SourceJson) := (momentMetadataField003Key, momentMetadataField003Value) :: momentMetadataAcc003

theorem object_moment_metadata_003 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 158) (SourceJson.white (momentMetadataField003Chars ++ tail)) momentMetadataAcc003 =
      SourceJson.object (fuel + 157) (SourceJson.white tail) momentMetadataAcc004 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_003_generic_complete"
  err.flush

noncomputable def momentMetadataField004Key : String := String.ofList ['f', 'a', 'c', 't', 'o', 'r', '_', 'c', 'o', 'u', 'n', 't']
noncomputable def momentMetadataField004Value : SourceJson := .number (String.ofList ['1', '0'])
noncomputable def momentMetadataField004Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'a', 'c', 't', 'o', 'r', '_', 'c', 'o', 'u', 'n', 't', '"', ':', ' ', '1', '0', ',']
noncomputable def momentMetadataAcc005 : List (String × SourceJson) := (momentMetadataField004Key, momentMetadataField004Value) :: momentMetadataAcc004

theorem object_moment_metadata_004 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 157) (SourceJson.white (momentMetadataField004Chars ++ tail)) momentMetadataAcc004 =
      SourceJson.object (fuel + 156) (SourceJson.white tail) momentMetadataAcc005 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_004_generic_complete"
  err.flush

noncomputable def momentMetadataField005Key : String := String.ofList ['l', 'o', 'g', '_', 'd', 'e', 'g', 'r', 'e', 'e']
noncomputable def momentMetadataField005Value : SourceJson := .number (String.ofList ['6'])
noncomputable def momentMetadataField005Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'l', 'o', 'g', '_', 'd', 'e', 'g', 'r', 'e', 'e', '"', ':', ' ', '6', ',']
noncomputable def momentMetadataAcc006 : List (String × SourceJson) := (momentMetadataField005Key, momentMetadataField005Value) :: momentMetadataAcc005

theorem object_moment_metadata_005 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 156) (SourceJson.white (momentMetadataField005Chars ++ tail)) momentMetadataAcc005 =
      SourceJson.object (fuel + 155) (SourceJson.white tail) momentMetadataAcc006 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_005_generic_complete"
  err.flush

noncomputable def momentMetadataField006Key : String := String.ofList ['e', 'x', 'p', '_', 'd', 'e', 'g', 'r', 'e', 'e']
noncomputable def momentMetadataField006Value : SourceJson := .number (String.ofList ['3'])
noncomputable def momentMetadataField006Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'e', 'x', 'p', '_', 'd', 'e', 'g', 'r', 'e', 'e', '"', ':', ' ', '3', ',']
noncomputable def momentMetadataAcc007 : List (String × SourceJson) := (momentMetadataField006Key, momentMetadataField006Value) :: momentMetadataAcc006

theorem object_moment_metadata_006 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 155) (SourceJson.white (momentMetadataField006Chars ++ tail)) momentMetadataAcc006 =
      SourceJson.object (fuel + 154) (SourceJson.white tail) momentMetadataAcc007 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_006_generic_complete"
  err.flush

noncomputable def momentMetadataField007Key : String := String.ofList ['l', 'o', 'g', '_', 'f', 'l', 'o', 'o', 'r', '_', 'd', 'e', 'n', 'o', 'm', 'i', 'n', 'a', 't', 'o', 'r']
noncomputable def momentMetadataField007Value : SourceJson := .str (String.ofList ['1', '2', '0', '8', '9', '2', '5', '8', '1', '9', '6', '1', '4', '6', '2', '9', '1', '7', '4', '7', '0', '6', '1', '7', '6'])
noncomputable def momentMetadataField007Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'l', 'o', 'g', '_', 'f', 'l', 'o', 'o', 'r', '_', 'd', 'e', 'n', 'o', 'm', 'i', 'n', 'a', 't', 'o', 'r', '"', ':', ' ', '"', '1', '2', '0', '8', '9', '2', '5', '8', '1', '9', '6', '1', '4', '6', '2', '9', '1', '7', '4', '7', '0', '6', '1', '7', '6', '"', ',']
noncomputable def momentMetadataAcc008 : List (String × SourceJson) := (momentMetadataField007Key, momentMetadataField007Value) :: momentMetadataAcc007

theorem object_moment_metadata_007 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 154) (SourceJson.white (momentMetadataField007Chars ++ tail)) momentMetadataAcc007 =
      SourceJson.object (fuel + 153) (SourceJson.white tail) momentMetadataAcc008 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_007_generic_complete"
  err.flush

noncomputable def momentMetadataField008Key : String := String.ofList ['f', 'i', 'n', 'a', 'l', '_', 'f', 'l', 'o', 'o', 'r', '_', 'd', 'e', 'n', 'o', 'm', 'i', 'n', 'a', 't', 'o', 'r']
noncomputable def momentMetadataField008Value : SourceJson := .str (String.ofList ['7', '9', '2', '2', '8', '1', '6', '2', '5', '1', '4', '2', '6', '4', '3', '3', '7', '5', '9', '3', '5', '4', '3', '9', '5', '0', '3', '3', '6'])
noncomputable def momentMetadataField008Chars : List Char := ['\r', '\n', ' ', ' ', '"', 'f', 'i', 'n', 'a', 'l', '_', 'f', 'l', 'o', 'o', 'r', '_', 'd', 'e', 'n', 'o', 'm', 'i', 'n', 'a', 't', 'o', 'r', '"', ':', ' ', '"', '7', '9', '2', '2', '8', '1', '6', '2', '5', '1', '4', '2', '6', '4', '3', '3', '7', '5', '9', '3', '5', '4', '3', '9', '5', '0', '3', '3', '6', '"', ',']
noncomputable def momentMetadataAcc009 : List (String × SourceJson) := (momentMetadataField008Key, momentMetadataField008Value) :: momentMetadataAcc008

theorem object_moment_metadata_008 (fuel : Nat) (tail : List Char) :
    SourceJson.object (fuel + 153) (SourceJson.white (momentMetadataField008Chars ++ tail)) momentMetadataAcc008 =
      SourceJson.object (fuel + 152) (SourceJson.white tail) momentMetadataAcc009 := by rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_008_generic_complete"
  err.flush

noncomputable def momentMetadataChars : List Char := '{' :: (momentMetadataField000Chars ++ momentMetadataField001Chars ++ momentMetadataField002Chars ++ momentMetadataField003Chars ++ momentMetadataField004Chars ++ momentMetadataField005Chars ++ momentMetadataField006Chars ++ momentMetadataField007Chars ++ momentMetadataField008Chars)

theorem value_moment_metadata (fuel : Nat) (tail : List Char) :
    SourceJson.value (fuel + 162) (momentMetadataChars ++ tail) =
      SourceJson.object (fuel + 152) (SourceJson.white tail) momentMetadataAcc009 := by
  have hinput : momentMetadataChars ++ tail = '{' :: (momentMetadataField000Chars ++ (momentMetadataField001Chars ++ (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))))))) := by
    simp only [momentMetadataChars, List.cons_append, List.append_assoc]
  calc
    SourceJson.value (fuel + 162) (momentMetadataChars ++ tail) =
        SourceJson.value (fuel + 162) ('{' :: (momentMetadataField000Chars ++ (momentMetadataField001Chars ++ (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))))))))) :=
      congrArg (SourceJson.value (fuel + 162)) hinput
    _ = SourceJson.object (fuel + 161) (SourceJson.white (momentMetadataField000Chars ++ (momentMetadataField001Chars ++ (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))))))))) momentMetadataAcc000 := by rfl
    _ = SourceJson.object (fuel + 160) (SourceJson.white (momentMetadataField001Chars ++ (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))))))) momentMetadataAcc001 :=
      object_moment_metadata_000 fuel (momentMetadataField001Chars ++ (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))))))
    _ = SourceJson.object (fuel + 159) (SourceJson.white (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))))))) momentMetadataAcc002 :=
      object_moment_metadata_001 fuel (momentMetadataField002Chars ++ (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))))))
    _ = SourceJson.object (fuel + 158) (SourceJson.white (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))))) momentMetadataAcc003 :=
      object_moment_metadata_002 fuel (momentMetadataField003Chars ++ (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))))
    _ = SourceJson.object (fuel + 157) (SourceJson.white (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))))) momentMetadataAcc004 :=
      object_moment_metadata_003 fuel (momentMetadataField004Chars ++ (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))))
    _ = SourceJson.object (fuel + 156) (SourceJson.white (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))) momentMetadataAcc005 :=
      object_moment_metadata_004 fuel (momentMetadataField005Chars ++ (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))))
    _ = SourceJson.object (fuel + 155) (SourceJson.white (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))) momentMetadataAcc006 :=
      object_moment_metadata_005 fuel (momentMetadataField006Chars ++ (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail))))
    _ = SourceJson.object (fuel + 154) (SourceJson.white (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))) momentMetadataAcc007 :=
      object_moment_metadata_006 fuel (momentMetadataField007Chars ++ (momentMetadataField008Chars ++ (tail)))
    _ = SourceJson.object (fuel + 153) (SourceJson.white (momentMetadataField008Chars ++ (tail))) momentMetadataAcc008 :=
      object_moment_metadata_007 fuel (momentMetadataField008Chars ++ (tail))
    _ = SourceJson.object (fuel + 152) (SourceJson.white (tail)) momentMetadataAcc009 :=
      object_moment_metadata_008 fuel (tail)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_before_raw_binding"
  err.flush

theorem moment_metadata_prefix :
    (momentRest06 0).take 348 = momentMetadataChars := by rfl

theorem moment_metadata_split :
    momentRest06 0 = momentMetadataChars ++ momentRest06 348 := by
  calc
    momentRest06 0 =
        (momentRest06 0).take 348 ++ (momentRest06 0).drop 348 :=
      (List.take_append_drop 348 (momentRest06 0)).symm
    _ = momentMetadataChars ++ (momentRest06 0).drop 348 :=
      congrArg (fun p => p ++ (momentRest06 0).drop 348) moment_metadata_prefix
    _ = momentMetadataChars ++ momentRest06 348 :=
      congrArg (fun rest => momentMetadataChars ++ rest) (momentRest06_drop 0 348)

theorem momentChars06_through_metadata (fuel : Nat) :
    SourceJson.value (fuel + 162) momentChars06 =
      SourceJson.object (fuel + 152) (SourceJson.white (momentRest06 348)) momentMetadataAcc009 := by
  exact (congrArg (SourceJson.value (fuel + 162))
    (momentRest06_zero.symm.trans moment_metadata_split)).trans
    (value_moment_metadata fuel (momentRest06 348))

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_MOMENT06 metadata_complete"
  err.flush

#print axioms object_moment_metadata_000
#print axioms object_moment_metadata_001
#print axioms object_moment_metadata_002
#print axioms object_moment_metadata_003
#print axioms object_moment_metadata_004
#print axioms object_moment_metadata_005
#print axioms object_moment_metadata_006
#print axioms object_moment_metadata_007
#print axioms object_moment_metadata_008
#print axioms value_moment_metadata
#print axioms moment_metadata_prefix
#print axioms moment_metadata_split
#print axioms momentChars06_through_metadata

end ImbalancedChen.P2OriginalSaving19Moment06Parsing
