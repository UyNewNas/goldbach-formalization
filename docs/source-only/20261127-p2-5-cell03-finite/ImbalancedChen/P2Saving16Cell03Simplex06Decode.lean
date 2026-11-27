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

theorem simplex06_lookup_simplex_id :
    rawSimplex06.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6'])) := by
  rfl

attribute [local simp] simplex06_lookup_simplex_id

theorem simplex06_lookup_vertex_ids :
    rawSimplex06.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_vertex_ids

theorem simplex06_lookup_physical_volume :
    rawSimplex06.getObjVal? "physical_volume" = .ok (.str (String.ofList ['3', '1', '6', '3', '9', '2', '9', '3', '3', '1', '4', '3', '9', '9', '5', '4', '1', '8', '4', '3', '0', '5', '9', '7', '0', '4', '0', '0', '6', '4', '1', '1', '7', '9', '6', '6', '6', '6', '4', '8', '8', '6', '4', '2', '4', '9', '/', '6', '3', '3', '0', '0', '9', '4', '9', '7', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_physical_volume

theorem simplex06_lookup_mean_gap :
    rawSimplex06.getObjVal? "mean_gap" = .ok (.str (String.ofList ['4', '4', '2', '6', '1', '9', '/', '8', '6', '4', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_mean_gap

theorem simplex06_lookup_factor_maxima :
    rawSimplex06.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '2', '0', '0', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '2', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '2', '0', '0', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_factor_maxima

theorem simplex06_lookup_gap_weighted_means :
    rawSimplex06.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['9', '1', '3', '6', '5', '4', '0', '2', '8', '9', '/', '1', '3', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '9', '9', '7', '6', '0', '1', '7', '9', '/', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '5', '5', '4', '5', '1', '2', '3', '4', '8', '1', '/', '1', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '0', '2', '9', '1', '2', '0', '2', '3', '/', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '6', '0', '8', '7', '1', '7', '4', '9', '/', '1', '6', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '8', '2', '9', '2', '4', '6', '0', '3', '/', '4', '0', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '2', '7', '5', '2', '3', '4', '7', '7', '/', '1', '6', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '9', '9', '8', '6', '4', '9', '1', '9', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '0', '1', '4', '6', '3', '4', '4', '2', '3', '/', '1', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '3', '8', '8', '1', '9', '9', '7', '3', '/', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_gap_weighted_means

theorem simplex06_lookup_max_bound :
    rawSimplex06.getObjVal? "max_bound" = .ok (.str (String.ofList ['8', '7', '5', '2', '5', '9', '5', '2', '2', '9', '7', '0', '3', '8', '8', '1', '7', '5', '6', '8', '9', '5', '7', '7', '6', '9', '5', '4', '7', '5', '8', '7', '3', '9', '3', '9', '2', '9', '5', '2', '8', '3', '5', '2', '8', '1', '4', '2', '5', '8', '1', '8', '7', '5', '/', '2', '1', '6', '8', '1', '0', '5', '7', '5', '5', '2', '8', '8', '8', '1', '7', '1', '5', '3', '3', '6', '2', '0', '8', '5', '7', '2', '3', '9', '8', '7', '1', '0', '9', '7', '0', '6', '0', '6', '8', '5', '4', '9', '3', '6', '4', '0', '9', '9', '5', '2', '0', '5', '5', '5', '8', '1', '6', '5', '3', '4', '8', '9', '3', '4', '4'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_bound

theorem simplex06_lookup_jensen_bound :
    rawSimplex06.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '6', '9', '2', '4', '0', '5', '4', '3', '9', '9', '5', '0', '8', '9', '3', '5', '8', '3', '0', '1', '4', '7', '0', '5', '6', '0', '4', '2', '3', '9', '2', '2', '2', '2', '6', '5', '5', '1', '0', '6', '7', '4', '4', '7', '1', '1', '4', '8', '4', '0', '0', '1', '8', '6', '9', '0', '5', '7', '0', '0', '9', '2', '4', '4', '5', '8', '0', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '4', '2', '2', '8', '0', '9', '9', '4', '7', '3', '6', '0', '1', '4', '3', '1', '5', '8', '8', '0', '4', '1', '0', '4', '8', '6', '1', '8', '2', '7', '0', '3', '5', '9', '0', '0', '9', '9', '8', '8', '0', '9', '6', '1', '4', '6', '3', '9', '5', '5', '7', '3', '1', '8', '1', '9', '7', '3', '4', '1', '9', '0', '9', '9', '1', '0', '3', '3', '8', '2', '4', '7', '6', '4', '0', '5', '6', '4', '1', '0', '2', '4', '2', '5', '8', '3', '6', '7', '1', '9', '0', '8', '6', '0', '6', '1', '7'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_bound

theorem simplex06_lookup_max_floor_Q96 :
    rawSimplex06.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '1', '9', '8', '4', '2', '3', '4', '8', '8', '2', '8', '6', '7', '9', '7', '0', '9'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_floor_Q96

theorem simplex06_lookup_jensen_floor_Q96 :
    rawSimplex06.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '3', '1', '7', '0', '9', '1', '8', '4', '5', '1', '9', '9', '9', '1', '7', '3', '5', '3'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_floor_Q96

theorem simplex06_decoded : decodeSimplex rawSimplex06 = .ok simplex06 := by
  unfold decodeSimplex simplex06
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
