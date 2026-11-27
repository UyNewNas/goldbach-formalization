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

theorem simplex70_lookup_simplex_id :
    rawSimplex70.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '0'])) := by
  rfl

attribute [local simp] simplex70_lookup_simplex_id

theorem simplex70_lookup_vertex_ids :
    rawSimplex70.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex70_lookup_vertex_ids

theorem simplex70_lookup_physical_volume :
    rawSimplex70.getObjVal? "physical_volume" = .ok (.str (String.ofList ['7', '7', '1', '7', '1', '7', '7', '5', '2', '6', '5', '3', '4', '6', '1', '6', '1', '9', '3', '8', '1', '1', '0', '7', '1', '3', '9', '5', '8', '1', '1', '7', '4', '2', '8', '4', '3', '2', '3', '3', '/', '1', '2', '6', '7', '5', '6', '7', '5', '6', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex70_lookup_physical_volume

theorem simplex70_lookup_mean_gap :
    rawSimplex70.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex70_lookup_mean_gap

theorem simplex70_lookup_factor_maxima :
    rawSimplex70.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['6', '4', '0', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '4', '6', '8', '3', '9', '/', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '1', '/', '1', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex70_lookup_factor_maxima

theorem simplex70_lookup_gap_weighted_means :
    rawSimplex70.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '9', '5', '8', '7', '2', '8', '8', '3', '/', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '2', '9', '5', '9', '2', '1', '1', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '4', '2', '4', '8', '8', '8', '7', '9', '/', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '2', '5', '8', '8', '5', '5', '5', '7', '/', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '4', '3', '6', '6', '7', '5', '9', '3', '/', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '5', '8', '0', '8', '2', '7', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '1', '1', '5', '9', '8', '7', '/', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '8', '5', '0', '6', '9', '3', '9', '/', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '7', '8', '0', '6', '8', '7', '1', '5', '1', '/', '1', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '2', '2', '3', '5', '8', '1', '7', '1', '/', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex70_lookup_gap_weighted_means

theorem simplex70_lookup_max_bound :
    rawSimplex70.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '4', '6', '9', '1', '0', '5', '3', '6', '2', '7', '1', '4', '1', '9', '0', '6', '3', '1', '9', '2', '8', '0', '4', '4', '0', '6', '3', '6', '6', '5', '8', '5', '5', '6', '7', '5', '7', '4', '2', '4', '4', '5', '5', '6', '8', '0', '0', '0', '0', '0', '/', '3', '1', '8', '5', '7', '2', '5', '8', '8', '2', '7', '1', '2', '7', '6', '5', '0', '5', '3', '9', '0', '9', '6', '5', '1', '5', '9', '3', '3', '8', '7', '4', '6', '7', '4', '7', '9', '4', '0', '5', '4', '6', '6', '8', '9', '4', '9', '9', '4', '3', '2', '7', '4', '8', '1', '9', '1', '6', '5', '4', '7', '2', '2', '5', '3'])) := by
  rfl

attribute [local simp] simplex70_lookup_max_bound

theorem simplex70_lookup_jensen_bound :
    rawSimplex70.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '4', '9', '1', '2', '4', '0', '0', '8', '6', '2', '2', '4', '4', '6', '9', '7', '0', '4', '8', '4', '9', '1', '6', '4', '3', '4', '5', '1', '3', '0', '6', '5', '3', '6', '4', '3', '6', '6', '7', '9', '3', '6', '7', '0', '8', '0', '5', '3', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '7', '3', '0', '6', '3', '3', '6', '0', '9', '3', '7', '6', '7', '6', '7', '9', '1', '8', '2', '1', '8', '3', '6', '3', '2', '9', '4', '1', '8', '1', '7', '0', '6', '0', '0', '4', '2', '5', '7', '7', '1', '5', '0', '2', '9', '6', '9', '0', '9', '3', '3', '5', '3', '0', '6', '0', '8', '3', '3', '7', '2', '3', '2', '7', '6', '1', '0', '9', '4', '2', '3', '7', '5', '7', '2', '0', '7', '3', '8', '3', '1', '9', '8', '3', '7', '6', '6', '2', '9', '4', '9', '7'])) := by
  rfl

attribute [local simp] simplex70_lookup_jensen_bound

theorem simplex70_lookup_max_floor_Q96 :
    rawSimplex70.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '1', '1', '1', '4', '5', '4', '7', '1', '7', '0', '9', '2', '5', '4', '0'])) := by
  rfl

attribute [local simp] simplex70_lookup_max_floor_Q96

theorem simplex70_lookup_jensen_floor_Q96 :
    rawSimplex70.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '9', '7', '8', '7', '2', '1', '3', '3', '7', '3', '2', '2', '1', '3', '2'])) := by
  rfl

attribute [local simp] simplex70_lookup_jensen_floor_Q96

theorem simplex70_decoded : decodeSimplex rawSimplex70 = .ok simplex70 := by
  unfold decodeSimplex simplex70
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
