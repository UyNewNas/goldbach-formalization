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

theorem simplex67_lookup_simplex_id :
    rawSimplex67.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '7'])) := by
  rfl

attribute [local simp] simplex67_lookup_simplex_id

theorem simplex67_lookup_vertex_ids :
    rawSimplex67.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['5']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex67_lookup_vertex_ids

theorem simplex67_lookup_physical_volume :
    rawSimplex67.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '6', '2', '6', '0', '2', '8', '7', '6', '8', '8', '9', '3', '5', '3', '4', '0', '2', '1', '5', '7', '2', '1', '5', '0', '6', '5', '7', '9', '0', '9', '1', '4', '1', '5', '1', '0', '7', '1', '8', '3', '6', '9', '4', '7', '/', '5', '2', '2', '1', '0', '6', '9', '8', '2', '4', '3', '6', '6', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex67_lookup_physical_volume

theorem simplex67_lookup_mean_gap :
    rawSimplex67.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '2', '7', '1', '/', '1', '0', '0', '3', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex67_lookup_mean_gap

theorem simplex67_lookup_factor_maxima :
    rawSimplex67.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['7', '6', '8', '7', '5', '2', '1', '/', '1', '1', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '8', '7', '5', '2', '1', '/', '1', '1', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '3', '1', '1', '9', '/', '5', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex67_lookup_factor_maxima

theorem simplex67_lookup_gap_weighted_means :
    rawSimplex67.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['4', '2', '4', '5', '0', '4', '3', '8', '5', '6', '2', '6', '3', '/', '7', '5', '4', '2', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '7', '6', '7', '4', '0', '7', '2', '2', '5', '6', '3', '/', '7', '5', '4', '2', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '6', '1', '0', '9', '7', '2', '7', '8', '4', '0', '5', '3', '/', '9', '0', '5', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '5', '8', '6', '9', '7', '7', '4', '8', '3', '5', '3', '/', '9', '0', '5', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '8', '1', '1', '3', '9', '2', '5', '5', '8', '7', '7', '/', '9', '0', '5', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '6', '3', '6', '5', '4', '0', '2', '9', '1', '4', '9', '/', '3', '6', '2', '0', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '4', '2', '2', '6', '7', '3', '9', '5', '9', '1', '/', '4', '0', '2', '2', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '4', '3', '8', '9', '6', '2', '3', '1', '1', '9', '/', '2', '2', '6', '2', '8', '9', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '7', '3', '2', '1', '2', '2', '1', '9', '3', '4', '1', '/', '2', '2', '6', '2', '8', '9', '2', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '1', '1', '0', '3', '5', '8', '4', '4', '4', '2', '4', '7', '/', '9', '0', '5', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex67_lookup_gap_weighted_means

theorem simplex67_lookup_max_bound :
    rawSimplex67.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '7', '6', '1', '6', '4', '2', '3', '2', '1', '4', '6', '8', '2', '1', '3', '8', '5', '9', '5', '9', '6', '6', '1', '6', '3', '3', '4', '7', '3', '7', '9', '0', '6', '1', '3', '5', '7', '1', '8', '7', '8', '9', '1', '7', '6', '3', '2', '9', '6', '2', '5', '0', '0', '0', '0', '0', '/', '1', '3', '8', '7', '9', '8', '9', '8', '7', '6', '8', '5', '3', '4', '3', '0', '3', '6', '8', '2', '8', '1', '6', '0', '6', '6', '3', '6', '6', '0', '8', '0', '3', '8', '5', '6', '4', '0', '0', '6', '2', '6', '0', '8', '7', '8', '0', '3', '5', '8', '8', '7', '8', '2', '0', '9', '2', '0', '6', '1', '6', '4', '1', '3', '6', '6', '7', '8', '7', '7', '9', '7'])) := by
  rfl

attribute [local simp] simplex67_lookup_max_bound

theorem simplex67_lookup_jensen_bound :
    rawSimplex67.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['5', '7', '9', '9', '1', '1', '9', '4', '1', '5', '9', '2', '8', '1', '9', '7', '1', '2', '9', '6', '3', '6', '1', '1', '0', '3', '8', '5', '1', '7', '5', '7', '6', '3', '7', '7', '3', '0', '4', '4', '5', '9', '3', '2', '2', '0', '2', '2', '9', '5', '8', '5', '9', '4', '9', '2', '9', '3', '6', '8', '0', '5', '1', '9', '5', '8', '6', '2', '1', '4', '4', '8', '6', '3', '6', '4', '4', '6', '5', '7', '2', '4', '7', '7', '7', '0', '1', '7', '4', '0', '1', '3', '6', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '8', '0', '4', '7', '0', '2', '1', '2', '8', '3', '1', '0', '9', '4', '6', '3', '3', '9', '5', '6', '6', '0', '8', '8', '7', '8', '7', '2', '7', '1', '6', '5', '3', '5', '8', '5', '7', '9', '8', '5', '0', '5', '4', '5', '4', '5', '5', '4', '4', '6', '6', '5', '9', '1', '7', '0', '5', '5', '8', '1', '4', '3', '1', '0', '6', '9', '5', '3', '6', '0', '8', '1', '5', '1', '3', '1', '2', '5', '1', '3', '1', '8', '6', '0', '4', '3', '6', '7', '6', '2', '2', '0', '1', '0', '7', '4', '6', '0', '0', '5', '8', '2', '3', '9', '0', '9', '7', '2', '4', '0', '7', '1', '9', '6', '2', '2', '5', '9', '0', '0', '5', '4', '5', '7', '6', '5', '7', '3'])) := by
  rfl

attribute [local simp] simplex67_lookup_jensen_bound

theorem simplex67_lookup_max_floor_Q96 :
    rawSimplex67.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '7', '1', '8', '0', '0', '3', '7', '6', '9', '1', '2', '9', '2', '1'])) := by
  rfl

attribute [local simp] simplex67_lookup_max_floor_Q96

theorem simplex67_lookup_jensen_floor_Q96 :
    rawSimplex67.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '0', '7', '3', '3', '7', '1', '7', '3', '8', '8', '0', '4', '6', '0', '9'])) := by
  rfl

attribute [local simp] simplex67_lookup_jensen_floor_Q96

theorem simplex67_decoded : decodeSimplex rawSimplex67 = .ok simplex67 := by
  unfold decodeSimplex simplex67
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
