import ImbalancedChen.P2Saving16Cell03FieldSimp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell03 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell03FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell03TypedPayload
open P2Saving16Cell03ScalarDecode
open scoped ImbalancedChen.P2Saving16Cell03FieldDecode

theorem simplex09_lookup_simplex_id :
    rawSimplex09.getObjVal? "simplex_id" = .ok (.number (String.ofList ['9'])) := by
  rfl

attribute [local simp] simplex09_lookup_simplex_id

theorem simplex09_lookup_vertex_ids :
    rawSimplex09.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['6']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex09_lookup_vertex_ids

theorem simplex09_lookup_physical_volume :
    rawSimplex09.getObjVal? "physical_volume" = .ok (.str (String.ofList ['3', '6', '2', '1', '0', '6', '5', '4', '9', '7', '3', '4', '4', '5', '6', '2', '0', '2', '1', '4', '7', '3', '8', '1', '9', '7', '1', '8', '4', '2', '9', '3', '6', '9', '5', '5', '5', '2', '8', '1', '1', '7', '/', '1', '7', '4', '7', '8', '2', '7', '8', '4', '6', '1', '1', '6', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex09_lookup_physical_volume

theorem simplex09_lookup_mean_gap :
    rawSimplex09.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '1', '6', '7', '/', '1', '9', '3', '9', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex09_lookup_mean_gap

theorem simplex09_lookup_factor_maxima :
    rawSimplex09.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '9', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '9', '1', '/', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '4', '3', '4', '7', '/', '1', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '4', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '1', '7', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '8', '0', '7', '3', '/', '2', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex09_lookup_factor_maxima

theorem simplex09_lookup_gap_weighted_means :
    rawSimplex09.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '2', '2', '2', '2', '2', '1', '4', '7', '0', '5', '9', '3', '8', '1', '/', '4', '1', '2', '9', '4', '1', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '3', '1', '1', '9', '5', '6', '8', '6', '7', '0', '1', '8', '1', '/', '4', '1', '2', '9', '4', '1', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '3', '0', '9', '7', '4', '1', '3', '6', '9', '8', '2', '9', '6', '1', '/', '1', '8', '5', '8', '2', '3', '4', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '2', '5', '6', '2', '3', '3', '8', '5', '1', '3', '7', '9', '/', '1', '8', '5', '8', '2', '3', '4', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '1', '1', '7', '9', '7', '6', '4', '7', '4', '7', '3', '7', '/', '3', '7', '1', '6', '4', '6', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '9', '5', '3', '3', '7', '5', '8', '5', '8', '0', '5', '9', '9', '/', '1', '4', '8', '6', '5', '8', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '3', '2', '8', '8', '0', '1', '3', '5', '7', '4', '7', '4', '3', '/', '4', '9', '5', '5', '2', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '4', '9', '6', '1', '5', '4', '7', '6', '2', '5', '6', '1', '/', '3', '7', '1', '6', '4', '6', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '6', '6', '7', '8', '9', '4', '3', '0', '9', '8', '9', '8', '3', '/', '1', '8', '5', '8', '2', '3', '4', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '7', '5', '7', '1', '8', '5', '3', '2', '1', '2', '9', '0', '7', '/', '9', '2', '9', '1', '1', '7', '4', '7', '5', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex09_lookup_gap_weighted_means

theorem simplex09_lookup_max_bound :
    rawSimplex09.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '7', '0', '7', '2', '6', '4', '3', '2', '2', '1', '8', '8', '9', '8', '4', '3', '4', '3', '4', '6', '2', '5', '4', '0', '1', '4', '5', '6', '3', '1', '4', '5', '3', '6', '1', '1', '7', '3', '1', '0', '0', '7', '9', '7', '6', '6', '6', '3', '6', '4', '1', '6', '0', '0', '0', '0', '/', '9', '7', '7', '6', '6', '9', '8', '8', '3', '4', '8', '1', '3', '3', '1', '7', '9', '0', '4', '6', '0', '9', '5', '5', '6', '6', '2', '5', '9', '2', '5', '4', '6', '4', '6', '5', '3', '5', '1', '1', '0', '9', '2', '6', '0', '6', '2', '1', '5', '2', '6', '2', '7', '0', '1', '8', '1', '6', '2', '1', '6', '7', '1', '1', '0', '0', '8', '0', '3', '6', '6', '3'])) := by
  rfl

attribute [local simp] simplex09_lookup_max_bound

theorem simplex09_lookup_jensen_bound :
    rawSimplex09.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '9', '0', '9', '3', '9', '2', '0', '4', '4', '4', '3', '9', '0', '6', '3', '3', '8', '5', '9', '4', '0', '6', '6', '3', '1', '2', '3', '5', '0', '0', '1', '0', '9', '5', '2', '9', '5', '9', '3', '4', '1', '0', '0', '7', '4', '7', '6', '0', '8', '3', '4', '3', '6', '3', '4', '6', '2', '1', '1', '3', '5', '5', '4', '1', '6', '5', '9', '1', '6', '5', '0', '4', '8', '5', '8', '7', '8', '1', '2', '2', '1', '1', '6', '6', '3', '1', '9', '1', '5', '0', '8', '2', '6', '9', '2', '7', '5', '7', '3', '6', '3', '9', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '1', '0', '5', '6', '0', '3', '4', '4', '1', '4', '7', '8', '3', '6', '0', '7', '0', '3', '8', '7', '1', '8', '7', '4', '2', '6', '6', '0', '1', '5', '0', '8', '3', '7', '2', '9', '3', '9', '7', '4', '9', '2', '0', '6', '0', '6', '7', '6', '6', '3', '6', '2', '7', '1', '1', '1', '9', '1', '6', '9', '0', '8', '6', '9', '1', '7', '1', '0', '2', '6', '0', '5', '8', '4', '4', '0', '7', '2', '4', '3', '9', '3', '5', '8', '5', '5', '7', '7', '9', '6', '9', '3', '2', '2', '6', '2', '6', '5', '2', '6', '9', '0', '8', '3', '9', '5', '5', '7', '5', '5', '6', '2', '7', '3', '8', '4', '0', '4', '7', '8', '1', '5', '1', '0', '3', '4', '0', '9', '8', '2', '7', '6', '7', '6', '7', '9', '7', '6', '8', '8', '3', '5', '3'])) := by
  rfl

attribute [local simp] simplex09_lookup_jensen_bound

theorem simplex09_lookup_max_floor_Q96 :
    rawSimplex09.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '3', '8', '3', '5', '2', '8', '5', '0', '4', '4', '4', '3', '0'])) := by
  rfl

attribute [local simp] simplex09_lookup_max_floor_Q96

theorem simplex09_lookup_jensen_floor_Q96 :
    rawSimplex09.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '7', '7', '5', '3', '1', '5', '3', '7', '9', '1', '2', '5', '1'])) := by
  rfl

attribute [local simp] simplex09_lookup_jensen_floor_Q96

theorem simplex09_decoded : decodeSimplex rawSimplex09 = .ok simplex09 := by
  unfold decodeSimplex simplex09
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
