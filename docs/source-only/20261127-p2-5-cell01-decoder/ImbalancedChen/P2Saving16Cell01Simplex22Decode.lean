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

theorem simplex22_lookup_simplex_id :
    rawSimplex22.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2', '2'])) := by
  rfl

attribute [local simp] simplex22_lookup_simplex_id

theorem simplex22_lookup_vertex_ids :
    rawSimplex22.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex22_lookup_vertex_ids

theorem simplex22_lookup_physical_volume :
    rawSimplex22.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '3', '1', '2', '5', '4', '0', '9', '8', '8', '5', '8', '2', '6', '9', '3', '4', '4', '6', '8', '8', '5', '7', '5', '4', '5', '9', '9', '9', '4', '1', '6', '8', '5', '4', '1', '4', '5', '5', '3', '/', '1', '2', '7', '4', '2', '5', '9', '3', '5', '5', '7', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex22_lookup_physical_volume

theorem simplex22_lookup_mean_gap :
    rawSimplex22.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex22_lookup_mean_gap

theorem simplex22_lookup_factor_maxima :
    rawSimplex22.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex22_lookup_factor_maxima

theorem simplex22_lookup_gap_weighted_means :
    rawSimplex22.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '0', '4', '2', '6', '6', '7', '4', '2', '0', '5', '1', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '1', '7', '6', '7', '7', '5', '9', '7', '/', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '9', '7', '2', '5', '6', '6', '0', '0', '3', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '4', '2', '4', '3', '0', '7', '0', '2', '7', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '0', '3', '7', '0', '7', '4', '7', '9', '/', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '1', '4', '3', '3', '3', '6', '6', '1', '/', '1', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '6', '6', '6', '9', '6', '4', '3', '8', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '2', '0', '4', '9', '4', '8', '2', '2', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '5', '8', '4', '6', '2', '0', '4', '6', '9', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '8', '6', '7', '5', '0', '9', '5', '9', '7', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex22_lookup_gap_weighted_means

theorem simplex22_lookup_max_bound :
    rawSimplex22.getObjVal? "max_bound" = .ok (.str (String.ofList ['3', '0', '5', '0', '5', '7', '3', '7', '2', '7', '4', '2', '4', '9', '5', '2', '0', '2', '8', '5', '8', '6', '1', '9', '2', '4', '9', '3', '4', '4', '1', '6', '6', '8', '8', '8', '8', '8', '1', '4', '3', '1', '6', '6', '5', '8', '2', '0', '3', '1', '2', '5', '/', '5', '7', '8', '4', '0', '0', '4', '1', '0', '1', '3', '9', '4', '4', '6', '7', '4', '2', '0', '2', '2', '3', '7', '6', '4', '2', '4', '9', '5', '8', '4', '5', '8', '8', '6', '7', '6', '3', '3', '0', '2', '2', '7', '7', '2', '4', '0', '5', '4', '6', '1', '5', '7', '0', '0', '8', '2', '2', '6', '3', '3', '6', '0', '3', '9', '6', '8'])) := by
  rfl

attribute [local simp] simplex22_lookup_max_bound

theorem simplex22_lookup_jensen_bound :
    rawSimplex22.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '0', '7', '5', '1', '8', '6', '9', '7', '7', '6', '5', '5', '5', '4', '7', '6', '3', '9', '7', '0', '3', '8', '6', '6', '6', '0', '3', '6', '8', '7', '8', '8', '4', '7', '6', '5', '9', '0', '3', '8', '0', '6', '1', '4', '3', '6', '2', '5', '0', '7', '1', '0', '3', '6', '5', '6', '0', '0', '4', '8', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '7', '4', '8', '0', '8', '7', '2', '9', '9', '9', '6', '3', '7', '3', '6', '0', '5', '8', '6', '5', '5', '7', '8', '9', '8', '4', '8', '2', '4', '8', '9', '6', '0', '6', '8', '3', '3', '7', '1', '3', '0', '7', '4', '8', '1', '5', '4', '6', '9', '2', '3', '2', '0', '2', '5', '3', '7', '8', '3', '6', '5', '9', '6', '7', '1', '3', '9', '6', '1', '2', '8', '9', '3', '2', '7', '0', '2', '8', '4', '4', '1', '5', '7', '3', '6', '2', '3', '2', '8', '7', '3', '5', '2', '9', '1', '7', '6', '6', '5', '8', '9', '4', '5', '9', '9'])) := by
  rfl

attribute [local simp] simplex22_lookup_jensen_bound

theorem simplex22_lookup_max_floor_Q96 :
    rawSimplex22.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '1', '7', '8', '6', '1', '6', '5', '2', '2', '4', '1', '7', '3'])) := by
  rfl

attribute [local simp] simplex22_lookup_max_floor_Q96

theorem simplex22_lookup_jensen_floor_Q96 :
    rawSimplex22.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '5', '8', '7', '0', '2', '9', '4', '5', '3', '0', '6', '4', '3', '9'])) := by
  rfl

attribute [local simp] simplex22_lookup_jensen_floor_Q96

theorem simplex22_decoded : decodeSimplex rawSimplex22 = .ok simplex22 := by
  unfold decodeSimplex simplex22
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
