import ImbalancedChen.P2Saving16Cell01FieldSimp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell01 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell01FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell01TypedPayload
open P2Saving16Cell01ScalarDecode
open scoped ImbalancedChen.P2Saving16Cell01FieldDecode

theorem simplex09_lookup_simplex_id :
    rawSimplex09.getObjVal? "simplex_id" = .ok (.number (String.ofList ['9'])) := by
  rfl

attribute [local simp] simplex09_lookup_simplex_id

theorem simplex09_lookup_vertex_ids :
    rawSimplex09.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex09_lookup_vertex_ids

theorem simplex09_lookup_physical_volume :
    rawSimplex09.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '8', '5', '2', '0', '0', '0', '9', '7', '4', '7', '9', '5', '5', '8', '1', '3', '6', '6', '2', '0', '9', '7', '8', '7', '1', '8', '5', '2', '7', '6', '1', '1', '9', '1', '2', '9', '6', '5', '8', '1', '/', '1', '0', '5', '7', '2', '3', '7', '0', '5', '9', '2', '0', '7', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex09_lookup_physical_volume

theorem simplex09_lookup_mean_gap :
    rawSimplex09.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex09_lookup_mean_gap

theorem simplex09_lookup_factor_maxima :
    rawSimplex09.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex09_lookup_factor_maxima

theorem simplex09_lookup_gap_weighted_means :
    rawSimplex09.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '5', '5', '5', '9', '4', '2', '0', '0', '0', '8', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '8', '1', '4', '3', '6', '8', '3', '5', '3', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '8', '0', '3', '4', '5', '4', '8', '2', '1', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '4', '1', '6', '9', '0', '9', '6', '1', '4', '3', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '2', '6', '0', '6', '2', '5', '2', '7', '4', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '1', '4', '2', '3', '2', '8', '7', '9', '/', '1', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '1', '3', '3', '8', '6', '0', '7', '2', '1', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '5', '7', '6', '2', '8', '0', '7', '3', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '5', '9', '1', '3', '6', '3', '4', '3', '9', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '9', '1', '1', '4', '2', '2', '3', '1', '3', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex09_lookup_gap_weighted_means

theorem simplex09_lookup_max_bound :
    rawSimplex09.getObjVal? "max_bound" = .ok (.str (String.ofList ['6', '3', '5', '8', '6', '1', '5', '9', '0', '7', '7', '4', '6', '5', '5', '5', '5', '0', '2', '1', '2', '8', '0', '4', '0', '2', '5', '7', '8', '9', '9', '4', '0', '9', '0', '1', '1', '8', '9', '1', '4', '7', '1', '3', '9', '8', '1', '2', '5', '0', '0', '0', '0', '0', '/', '8', '1', '9', '6', '0', '0', '1', '8', '9', '3', '2', '6', '0', '9', '6', '1', '3', '9', '3', '2', '9', '4', '3', '6', '6', '8', '2', '7', '9', '7', '8', '0', '3', '3', '2', '0', '2', '1', '1', '2', '3', '7', '5', '5', '1', '3', '7', '7', '2', '2', '8', '4', '6', '0', '7', '9', '3', '1', '6', '9', '1', '4', '2', '9', '7', '8', '2', '2', '7'])) := by
  rfl

attribute [local simp] simplex09_lookup_max_bound

theorem simplex09_lookup_jensen_bound :
    rawSimplex09.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '3', '3', '1', '0', '1', '1', '0', '0', '5', '9', '4', '2', '3', '7', '0', '6', '1', '5', '0', '6', '3', '5', '5', '5', '6', '1', '6', '0', '2', '1', '4', '2', '5', '9', '2', '7', '6', '0', '2', '3', '8', '8', '9', '9', '3', '5', '2', '8', '4', '9', '9', '3', '7', '3', '4', '5', '2', '1', '2', '7', '4', '1', '1', '2', '7', '0', '2', '4', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '6', '3', '5', '5', '6', '9', '6', '3', '2', '1', '0', '0', '5', '1', '5', '9', '1', '5', '6', '5', '4', '8', '5', '9', '0', '1', '7', '0', '7', '3', '6', '1', '3', '6', '7', '6', '1', '7', '6', '2', '3', '2', '3', '4', '4', '8', '2', '2', '4', '4', '1', '1', '8', '6', '8', '6', '6', '4', '3', '5', '5', '6', '2', '0', '5', '3', '2', '6', '3', '8', '4', '9', '6', '5', '8', '2', '3', '4', '4', '4', '6', '8', '6', '5', '7', '6', '0', '9', '8', '7', '6', '7', '3', '6', '4', '3', '3', '3', '7', '4', '9', '4', '7', '6', '8', '0', '4', '2', '5', '3'])) := by
  rfl

attribute [local simp] simplex09_lookup_jensen_bound

theorem simplex09_lookup_max_floor_Q96 :
    rawSimplex09.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '1', '4', '6', '6', '7', '3', '2', '3', '2', '4', '5', '6', '8'])) := by
  rfl

attribute [local simp] simplex09_lookup_max_floor_Q96

theorem simplex09_lookup_jensen_floor_Q96 :
    rawSimplex09.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['5', '1', '1', '0', '2', '8', '0', '8', '4', '8', '4', '1', '5', '9', '2'])) := by
  rfl

attribute [local simp] simplex09_lookup_jensen_floor_Q96

theorem simplex09_decoded : decodeSimplex rawSimplex09 = .ok simplex09 := by
  unfold decodeSimplex simplex09
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
