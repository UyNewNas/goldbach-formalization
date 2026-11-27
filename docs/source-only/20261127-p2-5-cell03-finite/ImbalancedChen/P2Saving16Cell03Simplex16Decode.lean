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

theorem simplex16_lookup_simplex_id :
    rawSimplex16.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1', '6'])) := by
  rfl

attribute [local simp] simplex16_lookup_simplex_id

theorem simplex16_lookup_vertex_ids :
    rawSimplex16.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex16_lookup_vertex_ids

theorem simplex16_lookup_physical_volume :
    rawSimplex16.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '5', '1', '6', '0', '2', '3', '9', '1', '8', '6', '3', '2', '9', '4', '9', '8', '2', '9', '3', '7', '1', '4', '7', '1', '3', '2', '5', '7', '2', '0', '0', '4', '7', '5', '0', '4', '3', '7', '5', '3', '5', '1', '7', '/', '1', '4', '5', '2', '3', '2', '9', '5', '1', '5', '8', '1', '6', '0', '5', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex16_lookup_physical_volume

theorem simplex16_lookup_mean_gap :
    rawSimplex16.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '6', '1', '1', '/', '7', '4', '1', '6', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex16_lookup_mean_gap

theorem simplex16_lookup_factor_maxima :
    rawSimplex16.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '2', '5', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '2', '9', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '2', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex16_lookup_factor_maxima

theorem simplex16_lookup_gap_weighted_means :
    rawSimplex16.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '2', '6', '0', '2', '7', '1', '1', '9', '6', '1', '7', '2', '7', '/', '1', '8', '5', '5', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '9', '1', '0', '7', '6', '8', '5', '9', '6', '1', '1', '/', '9', '2', '7', '9', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '4', '1', '1', '2', '0', '0', '2', '1', '4', '8', '2', '9', '/', '5', '5', '6', '7', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '7', '5', '2', '4', '0', '5', '0', '0', '2', '2', '9', '/', '2', '7', '8', '3', '7', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '2', '7', '7', '6', '5', '6', '6', '8', '2', '5', '1', '/', '2', '7', '8', '3', '7', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '7', '6', '1', '8', '3', '1', '0', '2', '6', '3', '3', '1', '/', '5', '5', '6', '7', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '1', '8', '0', '3', '6', '6', '3', '3', '6', '1', '1', '/', '9', '2', '7', '9', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '9', '0', '9', '1', '5', '6', '4', '8', '9', '8', '3', '/', '2', '7', '8', '3', '7', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '8', '0', '2', '1', '6', '7', '3', '7', '4', '8', '3', '/', '2', '7', '8', '3', '7', '8', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '1', '4', '3', '0', '8', '0', '8', '1', '6', '6', '1', '/', '5', '5', '6', '7', '5', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex16_lookup_gap_weighted_means

theorem simplex16_lookup_max_bound :
    rawSimplex16.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '7', '1', '8', '1', '6', '3', '7', '1', '7', '6', '0', '1', '0', '3', '4', '2', '9', '9', '0', '0', '9', '6', '2', '2', '0', '7', '7', '5', '9', '6', '0', '6', '5', '7', '4', '9', '1', '8', '1', '4', '0', '5', '5', '9', '4', '5', '2', '2', '4', '2', '1', '8', '7', '5', '/', '6', '3', '8', '3', '6', '2', '1', '1', '9', '9', '9', '6', '7', '7', '3', '3', '5', '1', '2', '2', '3', '4', '3', '7', '8', '1', '8', '6', '2', '9', '9', '9', '8', '0', '6', '4', '2', '9', '9', '7', '3', '4', '1', '1', '7', '2', '5', '8', '0', '5', '6', '4', '7', '7', '5', '1', '4', '6', '9', '2', '0', '4', '0', '5', '2', '2', '1', '8', '0', '8'])) := by
  rfl

attribute [local simp] simplex16_lookup_max_bound

theorem simplex16_lookup_jensen_bound :
    rawSimplex16.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '7', '1', '4', '6', '2', '4', '8', '9', '2', '4', '4', '1', '1', '9', '8', '9', '5', '0', '0', '8', '5', '7', '5', '8', '3', '0', '4', '3', '0', '9', '7', '4', '8', '9', '7', '4', '1', '9', '5', '0', '6', '7', '6', '7', '0', '7', '7', '9', '7', '0', '8', '4', '9', '4', '9', '4', '3', '0', '4', '2', '1', '6', '3', '3', '6', '9', '6', '0', '0', '7', '3', '6', '0', '1', '9', '1', '4', '6', '6', '9', '2', '7', '0', '9', '7', '4', '0', '3', '3', '9', '9', '9', '9', '0', '9', '7', '8', '6', '9', '8', '7', '3', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '9', '6', '6', '1', '6', '6', '8', '2', '6', '2', '7', '9', '2', '6', '0', '1', '7', '2', '2', '1', '2', '5', '0', '7', '9', '7', '8', '0', '0', '4', '6', '2', '3', '4', '5', '1', '3', '5', '8', '7', '4', '7', '5', '4', '7', '5', '0', '0', '0', '9', '4', '9', '0', '4', '1', '7', '9', '3', '7', '6', '3', '2', '0', '7', '9', '7', '0', '2', '1', '5', '7', '0', '4', '1', '8', '7', '3', '6', '4', '8', '1', '5', '8', '5', '3', '3', '7', '8', '5', '4', '1', '2', '4', '6', '5', '5', '7', '2', '6', '8', '3', '8', '7', '1', '5', '1', '1', '3', '2', '9', '2', '9', '3', '4', '5', '3', '4', '8', '3', '0', '1', '8', '9', '5', '7', '3', '4', '5', '3', '0', '3'])) := by
  rfl

attribute [local simp] simplex16_lookup_jensen_bound

theorem simplex16_lookup_max_floor_Q96 :
    rawSimplex16.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['5', '8', '5', '5', '7', '8', '9', '8', '4', '2', '1', '1', '7', '9'])) := by
  rfl

attribute [local simp] simplex16_lookup_max_floor_Q96

theorem simplex16_lookup_jensen_floor_Q96 :
    rawSimplex16.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '4', '2', '0', '3', '3', '5', '9', '9', '5', '6', '4', '8', '3', '3'])) := by
  rfl

attribute [local simp] simplex16_lookup_jensen_floor_Q96

theorem simplex16_decoded : decodeSimplex rawSimplex16 = .ok simplex16 := by
  unfold decodeSimplex simplex16
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
