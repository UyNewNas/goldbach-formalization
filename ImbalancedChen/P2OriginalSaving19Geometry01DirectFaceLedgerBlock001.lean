import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput
import ImbalancedChen.P2OriginalSaving19Geometry01ValueFragment0157281

/-! Grouped external original-reader transitions; child certificates remain opaque.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock001

noncomputable def piece0001LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def piece0001SuffixChars00 : List Char := [',']
noncomputable def piece0001Chars00 : List Char := piece0001LeadChars00 ++ fragment0157281Chars ++ piece0001SuffixChars00
noncomputable def piece0001Push00 (acc : List SourceJson) : List SourceJson := fragment0157281Value :: acc

noncomputable def piece0001AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_piece0001_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 97)
      (SourceJson.white (piece0001LeadChars00 ++ (fragment0157281Chars ++ rest))) acc =
      (SourceJson.value (fuel + 96) (fragment0157281Chars ++ rest)).bind
        (piece0001AfterValue00 (fuel + 96) acc) := by rfl

theorem array_piece0001 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 97) (SourceJson.white (piece0001Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 96) (SourceJson.white tail) (piece0001Push00 acc) := by
  have hinput : piece0001Chars00 ++ tail = piece0001LeadChars00 ++ (fragment0157281Chars ++ (piece0001SuffixChars00 ++ tail)) := by
    simp only [piece0001Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 97) (SourceJson.white (piece0001Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 97)
          (SourceJson.white (piece0001LeadChars00 ++ (fragment0157281Chars ++ (piece0001SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 97) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 96) (fragment0157281Chars ++ (piece0001SuffixChars00 ++ tail))).bind
        (piece0001AfterValue00 (fuel + 96) acc) := array_piece0001_head fuel (piece0001SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0157281Value, piece0001SuffixChars00 ++ tail)).bind
        (piece0001AfterValue00 (fuel + 96) acc) :=
      congrArg (fun result => result.bind (piece0001AfterValue00 (fuel + 96) acc))
        (value_fragment0157281 (fuel + 44) (piece0001SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 96) (SourceJson.white tail) (piece0001Push00 acc) := by rfl

noncomputable def blockChars : List Char := piece0001Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := piece0001Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 97) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 96) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = piece0001Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 97) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 97) (SourceJson.white (piece0001Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 97) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 96) (SourceJson.white tail) (blockPush acc) := array_piece0001 fuel (tail) (acc)

theorem block_lead_prefix :
    (sourceRest 157275).take 6 = piece0001LeadChars00 := by rfl

theorem block_lead_split : sourceRest 157275 = piece0001LeadChars00 ++ sourceRest 157281 := by
  calc
    sourceRest 157275 = (sourceRest 157275).take 6 ++ (sourceRest 157275).drop 6 :=
      (List.take_append_drop 6 (sourceRest 157275)).symm
    _ = piece0001LeadChars00 ++ (sourceRest 157275).drop 6 :=
      congrArg (fun part => part ++ (sourceRest 157275).drop 6) block_lead_prefix
    _ = piece0001LeadChars00 ++ sourceRest 157281 :=
      congrArg (fun tail => piece0001LeadChars00 ++ tail) (sourceRest_drop 157275 6)

theorem block_suffix_prefix :
    (sourceRest 162912).take 1 = piece0001SuffixChars00 := by rfl

theorem block_suffix_split : sourceRest 162912 = piece0001SuffixChars00 ++ sourceRest 162913 := by
  calc
    sourceRest 162912 = (sourceRest 162912).take 1 ++ (sourceRest 162912).drop 1 :=
      (List.take_append_drop 1 (sourceRest 162912)).symm
    _ = piece0001SuffixChars00 ++ (sourceRest 162912).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 162912).drop 1) block_suffix_prefix
    _ = piece0001SuffixChars00 ++ sourceRest 162913 :=
      congrArg (fun tail => piece0001SuffixChars00 ++ tail) (sourceRest_drop 162912 1)

theorem block_original_split : sourceRest 157275 = blockChars ++ sourceRest 162913 := by
  calc
    sourceRest 157275 = piece0001LeadChars00 ++ (sourceRest 157281) := block_lead_split
    _ = piece0001LeadChars00 ++ (fragment0157281Chars ++ (sourceRest 162912)) := congrArg (fun rest => piece0001LeadChars00 ++ (rest)) fragment0157281_original_split
    _ = piece0001LeadChars00 ++ (fragment0157281Chars ++ (piece0001SuffixChars00 ++ (sourceRest 162913))) := congrArg (fun rest => piece0001LeadChars00 ++ (fragment0157281Chars ++ (rest))) block_suffix_split
    _ = blockChars ++ sourceRest 162913 := by simp only [blockChars, piece0001Chars00, List.cons_append, List.nil_append, List.append_assoc]

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 97) (SourceJson.white (sourceRest 157275)) acc =
      SourceJson.array (fuel + 96) (SourceJson.white (sourceRest 162913)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 97) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 162913) acc)

#print axioms array_piece0001_head
#print axioms array_piece0001
#print axioms block_lead_prefix
#print axioms block_lead_split
#print axioms block_suffix_prefix
#print axioms block_suffix_split
#print axioms block_original_split
#print axioms array_block
#print axioms array_block_original

end FaceLedgerBlock001

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
