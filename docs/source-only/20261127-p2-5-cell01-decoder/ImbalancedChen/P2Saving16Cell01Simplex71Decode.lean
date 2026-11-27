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

theorem simplex71_lookup_simplex_id :
    rawSimplex71.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '1'])) := by
  rfl

attribute [local simp] simplex71_lookup_simplex_id

theorem simplex71_lookup_vertex_ids :
    rawSimplex71.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex71_lookup_vertex_ids

theorem simplex71_lookup_physical_volume :
    rawSimplex71.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '9', '0', '2', '8', '1', '3', '4', '4', '4', '5', '0', '6', '9', '9', '0', '9', '4', '2', '2', '7', '0', '2', '7', '7', '0', '5', '9', '2', '7', '3', '8', '1', '1', '6', '5', '1', '6', '2', '9', '/', '1', '0', '0', '8', '2', '9', '2', '3', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex71_lookup_physical_volume

theorem simplex71_lookup_mean_gap :
    rawSimplex71.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex71_lookup_mean_gap

theorem simplex71_lookup_factor_maxima :
    rawSimplex71.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '1', '/', '1', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex71_lookup_factor_maxima

theorem simplex71_lookup_gap_weighted_means :
    rawSimplex71.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '1', '9', '7', '2', '7', '7', '2', '1', '9', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '4', '9', '7', '7', '0', '4', '9', '9', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '9', '0', '0', '5', '6', '8', '7', '5', '3', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '1', '0', '5', '3', '8', '3', '4', '4', '9', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '2', '8', '1', '4', '8', '8', '6', '0', '1', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '6', '6', '3', '6', '8', '8', '7', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '4', '3', '5', '9', '8', '1', '3', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '5', '5', '9', '6', '4', '5', '4', '3', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '6', '3', '4', '6', '8', '8', '9', '9', '0', '7', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '5', '3', '3', '6', '0', '5', '9', '7', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex71_lookup_gap_weighted_means

theorem simplex71_lookup_max_bound :
    rawSimplex71.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '7', '3', '0', '0', '9', '2', '8', '2', '8', '2', '6', '8', '7', '0', '6', '7', '7', '8', '1', '4', '1', '1', '1', '3', '1', '1', '4', '5', '3', '4', '3', '2', '3', '5', '1', '2', '4', '3', '3', '2', '1', '6', '7', '1', '6', '8', '0', '0', '0', '0', '0', '/', '1', '6', '0', '7', '0', '4', '6', '8', '8', '0', '5', '4', '5', '0', '7', '6', '0', '0', '8', '5', '4', '8', '7', '3', '8', '4', '4', '2', '1', '2', '3', '1', '9', '1', '7', '3', '8', '9', '5', '7', '0', '5', '7', '1', '2', '1', '0', '1', '1', '6', '4', '1', '0', '3', '8', '6', '0', '9', '8', '1', '6', '6', '8', '1', '6', '3'])) := by
  rfl

attribute [local simp] simplex71_lookup_max_bound

theorem simplex71_lookup_jensen_bound :
    rawSimplex71.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '0', '5', '1', '8', '4', '6', '9', '7', '0', '1', '8', '9', '0', '0', '8', '3', '3', '1', '9', '2', '5', '8', '5', '4', '1', '0', '3', '2', '8', '4', '0', '0', '8', '5', '8', '6', '1', '2', '2', '7', '7', '8', '4', '7', '0', '2', '7', '2', '4', '9', '3', '5', '4', '3', '3', '3', '6', '1', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '9', '8', '1', '5', '1', '0', '0', '0', '7', '2', '6', '9', '1', '0', '8', '3', '1', '3', '1', '4', '5', '8', '2', '5', '0', '2', '9', '1', '4', '5', '1', '2', '0', '2', '0', '3', '8', '2', '3', '3', '8', '9', '3', '1', '3', '3', '6', '6', '2', '2', '9', '3', '9', '9', '7', '7', '9', '7', '0', '0', '2', '7', '7', '3', '5', '1', '0', '8', '2', '0', '1', '3', '7', '0', '3', '7', '1', '6', '5', '8', '5', '5', '4', '6', '6', '2', '4', '0', '7', '1', '5', '9', '8', '0', '6', '2', '2', '8', '0', '9', '9'])) := by
  rfl

attribute [local simp] simplex71_lookup_jensen_bound

theorem simplex71_lookup_max_floor_Q96 :
    rawSimplex71.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '2', '4', '9', '6', '2', '5', '5', '2', '8', '4', '0', '4', '7', '3'])) := by
  rfl

attribute [local simp] simplex71_lookup_max_floor_Q96

theorem simplex71_lookup_jensen_floor_Q96 :
    rawSimplex71.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '4', '8', '0', '3', '4', '3', '4', '6', '0', '0', '6', '0', '8', '4', '6', '6'])) := by
  rfl

attribute [local simp] simplex71_lookup_jensen_floor_Q96

theorem simplex71_decoded : decodeSimplex rawSimplex71 = .ok simplex71 := by
  unfold decodeSimplex simplex71
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
