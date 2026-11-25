import ImbalancedChen.P2OriginalSaving19Geometry01DirectInput
import ImbalancedChen.P2OriginalSaving19Geometry01ValueFragment0162919

/-! Grouped external original-reader transitions; child certificates remain opaque.
Original-reader equations and exact production packed-input slices are checked
in Lean. No whole-cell parse or typed decoding claim is made by this pilot. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19PackedChars

namespace FaceLedgerBlock002

noncomputable def piece0002LeadChars00 : List Char := ['\r', '\n', ' ', ' ', ' ', ' ']
noncomputable def piece0002SuffixChars00 : List Char := [',']
noncomputable def piece0002Chars00 : List Char := piece0002LeadChars00 ++ fragment0162919Chars ++ piece0002SuffixChars00
noncomputable def piece0002Push00 (acc : List SourceJson) : List SourceJson := fragment0162919Value :: acc

noncomputable def piece0002AfterValue00 (fuel : Nat) (acc : List SourceJson) (result : SourceJson × List Char) :
    Except String (SourceJson × List Char) :=
  match SourceJson.white result.2 with
  | ']' :: tail => .ok (.arr ((result.1 :: acc).reverse), tail)
  | ',' :: tail => SourceJson.array fuel (SourceJson.white tail) (result.1 :: acc)
  | _ => .error "array separator missing"

theorem array_piece0002_head (fuel : Nat) (rest : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 96)
      (SourceJson.white (piece0002LeadChars00 ++ (fragment0162919Chars ++ rest))) acc =
      (SourceJson.value (fuel + 95) (fragment0162919Chars ++ rest)).bind
        (piece0002AfterValue00 (fuel + 95) acc) := by rfl

theorem array_piece0002 (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 96) (SourceJson.white (piece0002Chars00 ++ tail)) acc =
      SourceJson.array (fuel + 95) (SourceJson.white tail) (piece0002Push00 acc) := by
  have hinput : piece0002Chars00 ++ tail = piece0002LeadChars00 ++ (fragment0162919Chars ++ (piece0002SuffixChars00 ++ tail)) := by
    simp only [piece0002Chars00, List.append_assoc]
  calc
    SourceJson.array (fuel + 96) (SourceJson.white (piece0002Chars00 ++ tail)) acc =
        SourceJson.array (fuel + 96)
          (SourceJson.white (piece0002LeadChars00 ++ (fragment0162919Chars ++ (piece0002SuffixChars00 ++ tail)))) acc :=
      congrArg (fun s => SourceJson.array (fuel + 96) (SourceJson.white s) acc) hinput
    _ = (SourceJson.value (fuel + 95) (fragment0162919Chars ++ (piece0002SuffixChars00 ++ tail))).bind
        (piece0002AfterValue00 (fuel + 95) acc) := array_piece0002_head fuel (piece0002SuffixChars00 ++ tail) acc
    _ = (Except.ok (fragment0162919Value, piece0002SuffixChars00 ++ tail)).bind
        (piece0002AfterValue00 (fuel + 95) acc) :=
      congrArg (fun result => result.bind (piece0002AfterValue00 (fuel + 95) acc))
        (value_fragment0162919 (fuel + 50) (piece0002SuffixChars00 ++ tail))
    _ = SourceJson.array (fuel + 95) (SourceJson.white tail) (piece0002Push00 acc) := by rfl

noncomputable def blockChars : List Char := piece0002Chars00
noncomputable def blockPush (acc : List SourceJson) : List SourceJson := piece0002Push00 (acc)

theorem array_block (fuel : Nat) (tail : List Char) (acc : List SourceJson) :
    SourceJson.array (fuel + 96) (SourceJson.white (blockChars ++ tail)) acc =
      SourceJson.array (fuel + 95) (SourceJson.white tail) (blockPush acc) := by
  have hinput : blockChars ++ tail = piece0002Chars00 ++ (tail) := by simp only [blockChars, List.append_assoc]
  calc
    SourceJson.array (fuel + 96) (SourceJson.white (blockChars ++ tail)) acc =
        SourceJson.array (fuel + 96) (SourceJson.white (piece0002Chars00 ++ (tail))) acc :=
      congrArg (fun chars => SourceJson.array (fuel + 96) (SourceJson.white chars) acc) hinput
    _ = SourceJson.array (fuel + 95) (SourceJson.white tail) (blockPush acc) := array_piece0002 fuel (tail) (acc)

theorem block_lead_prefix :
    (sourceRest 162913).take 6 = piece0002LeadChars00 := by rfl

theorem block_lead_split : sourceRest 162913 = piece0002LeadChars00 ++ sourceRest 162919 := by
  calc
    sourceRest 162913 = (sourceRest 162913).take 6 ++ (sourceRest 162913).drop 6 :=
      (List.take_append_drop 6 (sourceRest 162913)).symm
    _ = piece0002LeadChars00 ++ (sourceRest 162913).drop 6 :=
      congrArg (fun part => part ++ (sourceRest 162913).drop 6) block_lead_prefix
    _ = piece0002LeadChars00 ++ sourceRest 162919 :=
      congrArg (fun tail => piece0002LeadChars00 ++ tail) (sourceRest_drop 162913 6)

theorem block_suffix_prefix :
    (sourceRest 167229).take 1 = piece0002SuffixChars00 := by rfl

theorem block_suffix_split : sourceRest 167229 = piece0002SuffixChars00 ++ sourceRest 167230 := by
  calc
    sourceRest 167229 = (sourceRest 167229).take 1 ++ (sourceRest 167229).drop 1 :=
      (List.take_append_drop 1 (sourceRest 167229)).symm
    _ = piece0002SuffixChars00 ++ (sourceRest 167229).drop 1 :=
      congrArg (fun part => part ++ (sourceRest 167229).drop 1) block_suffix_prefix
    _ = piece0002SuffixChars00 ++ sourceRest 167230 :=
      congrArg (fun tail => piece0002SuffixChars00 ++ tail) (sourceRest_drop 167229 1)

theorem block_original_split : sourceRest 162913 = blockChars ++ sourceRest 167230 := by
  calc
    sourceRest 162913 = piece0002LeadChars00 ++ (sourceRest 162919) := block_lead_split
    _ = piece0002LeadChars00 ++ (fragment0162919Chars ++ (sourceRest 167229)) := congrArg (fun rest => piece0002LeadChars00 ++ (rest)) fragment0162919_original_split
    _ = piece0002LeadChars00 ++ (fragment0162919Chars ++ (piece0002SuffixChars00 ++ (sourceRest 167230))) := congrArg (fun rest => piece0002LeadChars00 ++ (fragment0162919Chars ++ (rest))) block_suffix_split
    _ = blockChars ++ sourceRest 167230 := by simp only [blockChars, piece0002Chars00, List.cons_append, List.nil_append, List.append_assoc]

theorem array_block_original (fuel : Nat) (acc : List SourceJson) :
    SourceJson.array (fuel + 96) (SourceJson.white (sourceRest 162913)) acc =
      SourceJson.array (fuel + 95) (SourceJson.white (sourceRest 167230)) (blockPush acc) :=
  (congrArg (fun chars => SourceJson.array (fuel + 96) (SourceJson.white chars) acc)
    block_original_split).trans (array_block fuel (sourceRest 167230) acc)

#print axioms array_piece0002_head
#print axioms array_piece0002
#print axioms block_lead_prefix
#print axioms block_lead_split
#print axioms block_suffix_prefix
#print axioms block_suffix_split
#print axioms block_original_split
#print axioms array_block
#print axioms array_block_original

end FaceLedgerBlock002

end ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
