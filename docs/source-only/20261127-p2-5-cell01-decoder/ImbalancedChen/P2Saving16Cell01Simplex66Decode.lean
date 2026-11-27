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

theorem simplex66_lookup_simplex_id :
    rawSimplex66.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '6'])) := by
  rfl

attribute [local simp] simplex66_lookup_simplex_id

theorem simplex66_lookup_vertex_ids :
    rawSimplex66.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex66_lookup_vertex_ids

theorem simplex66_lookup_physical_volume :
    rawSimplex66.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '2', '4', '6', '0', '8', '7', '1', '3', '6', '8', '9', '3', '4', '3', '8', '9', '9', '7', '7', '7', '0', '9', '0', '8', '5', '1', '5', '6', '6', '8', '8', '8', '0', '0', '6', '1', '2', '6', '6', '8', '8', '7', '/', '2', '6', '5', '9', '0', '7', '5', '0', '6', '7', '6', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex66_lookup_physical_volume

theorem simplex66_lookup_mean_gap :
    rawSimplex66.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '4', '4', '3', '9', '9', '3', '9', '/', '1', '5', '5', '7', '6', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex66_lookup_mean_gap

theorem simplex66_lookup_factor_maxima :
    rawSimplex66.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['6', '4', '0', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '4', '6', '8', '3', '9', '/', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '1', '/', '1', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex66_lookup_factor_maxima

theorem simplex66_lookup_gap_weighted_means :
    rawSimplex66.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '5', '9', '9', '2', '9', '4', '0', '2', '5', '4', '5', '0', '0', '7', '4', '3', '3', '/', '8', '6', '5', '1', '7', '3', '8', '4', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '6', '3', '3', '8', '1', '6', '8', '0', '4', '6', '0', '1', '1', '4', '6', '1', '3', '/', '9', '5', '1', '6', '9', '1', '2', '2', '4', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '0', '9', '0', '0', '2', '0', '3', '4', '7', '7', '3', '5', '4', '4', '4', '1', '3', '7', '/', '2', '8', '5', '5', '0', '7', '3', '6', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '7', '3', '3', '2', '5', '0', '0', '2', '9', '4', '7', '2', '3', '5', '3', '5', '7', '/', '5', '7', '1', '0', '1', '4', '7', '3', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '8', '6', '8', '4', '4', '2', '0', '4', '0', '6', '7', '3', '5', '7', '0', '7', '7', '3', '/', '5', '7', '1', '0', '1', '4', '7', '3', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '1', '5', '2', '3', '8', '8', '5', '4', '0', '7', '4', '0', '0', '8', '0', '7', '/', '2', '8', '5', '5', '0', '7', '3', '6', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '4', '7', '2', '2', '0', '7', '0', '8', '3', '1', '8', '6', '9', '5', '1', '/', '1', '4', '2', '7', '5', '3', '6', '8', '3', '6', '9', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '7', '3', '0', '9', '3', '5', '7', '0', '9', '1', '7', '2', '0', '8', '9', '9', '/', '5', '7', '1', '0', '1', '4', '7', '3', '4', '7', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '4', '7', '3', '6', '5', '3', '2', '3', '5', '0', '1', '6', '7', '5', '3', '5', '1', '/', '2', '8', '5', '5', '0', '7', '3', '6', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '5', '6', '1', '6', '2', '5', '3', '0', '7', '1', '6', '4', '9', '5', '7', '0', '1', '3', '/', '2', '8', '5', '5', '0', '7', '3', '6', '7', '3', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex66_lookup_gap_weighted_means

theorem simplex66_lookup_max_bound :
    rawSimplex66.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '4', '3', '3', '1', '4', '3', '2', '2', '8', '9', '1', '1', '0', '7', '2', '8', '7', '5', '5', '6', '4', '3', '3', '6', '0', '0', '4', '5', '8', '9', '5', '5', '1', '6', '6', '5', '6', '7', '9', '0', '1', '0', '8', '7', '0', '5', '8', '3', '2', '0', '0', '0', '0', '0', '/', '5', '3', '3', '9', '3', '9', '4', '5', '6', '9', '2', '7', '4', '1', '0', '2', '1', '1', '0', '5', '3', '9', '7', '5', '7', '9', '0', '9', '4', '6', '5', '2', '9', '8', '7', '3', '5', '0', '1', '9', '8', '3', '6', '7', '9', '2', '5', '6', '2', '1', '5', '9', '3', '1', '6', '2', '6', '5', '5', '3', '7', '4', '6', '6', '1', '6', '6', '7'])) := by
  rfl

attribute [local simp] simplex66_lookup_max_bound

theorem simplex66_lookup_jensen_bound :
    rawSimplex66.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '0', '8', '6', '3', '5', '7', '8', '7', '6', '6', '7', '6', '7', '8', '2', '6', '1', '3', '0', '6', '4', '3', '0', '4', '9', '4', '5', '7', '4', '7', '7', '2', '2', '5', '2', '0', '8', '7', '2', '2', '3', '5', '2', '9', '3', '1', '0', '8', '3', '2', '7', '2', '7', '5', '2', '9', '5', '6', '8', '0', '6', '2', '0', '6', '3', '5', '1', '1', '9', '1', '0', '8', '3', '8', '4', '1', '1', '9', '8', '8', '8', '4', '6', '2', '0', '0', '5', '0', '2', '3', '9', '7', '5', '7', '6', '0', '2', '3', '3', '6', '6', '8', '5', '9', '7', '3', '1', '4', '3', '8', '6', '5', '5', '1', '1', '8', '0', '8', '7', '9', '7', '8', '7', '7', '8', '3', '0', '1', '2', '9', '9', '1', '0', '2', '9', '0', '5', '7', '3', '5', '7', '5', '3', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '7', '4', '7', '9', '5', '0', '9', '0', '7', '5', '0', '3', '6', '0', '9', '9', '7', '0', '0', '9', '0', '0', '0', '3', '2', '2', '3', '4', '1', '6', '2', '9', '5', '7', '9', '9', '6', '5', '5', '2', '3', '0', '7', '6', '1', '3', '9', '6', '1', '4', '6', '9', '9', '3', '6', '0', '0', '3', '8', '8', '9', '5', '5', '6', '9', '0', '0', '2', '6', '5', '7', '3', '0', '9', '2', '2', '0', '0', '9', '8', '1', '6', '4', '7', '4', '4', '5', '3', '0', '4', '1', '7', '3', '0', '5', '4', '5', '2', '9', '6', '6', '2', '5', '1', '5', '7', '7', '1', '2', '8', '5', '5', '0', '0', '3', '4', '8', '6', '9', '2', '6', '5', '5', '7', '8', '9', '5', '8', '9', '6', '4', '0', '4', '7', '9', '9', '7', '4', '2', '8', '7', '3', '0', '5', '3', '3', '0', '2', '7', '8', '6', '6', '1', '3', '3', '7', '7', '4', '7', '6', '9', '7', '4', '9', '2', '0', '1', '7', '1', '0', '8', '2', '8', '9', '4', '9', '1', '4', '6', '3', '7', '8', '7'])) := by
  rfl

attribute [local simp] simplex66_lookup_jensen_bound

theorem simplex66_lookup_max_floor_Q96 :
    rawSimplex66.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '1', '2', '6', '5', '5', '7', '6', '6', '8', '1', '6', '3', '1', '2', '7'])) := by
  rfl

attribute [local simp] simplex66_lookup_max_floor_Q96

theorem simplex66_lookup_jensen_floor_Q96 :
    rawSimplex66.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['9', '8', '8', '0', '6', '7', '5', '1', '4', '5', '3', '6', '6', '7', '7', '0'])) := by
  rfl

attribute [local simp] simplex66_lookup_jensen_floor_Q96

theorem simplex66_decoded : decodeSimplex rawSimplex66 = .ok simplex66 := by
  unfold decodeSimplex simplex66
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
