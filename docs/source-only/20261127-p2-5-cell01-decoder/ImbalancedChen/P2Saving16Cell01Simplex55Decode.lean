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

theorem simplex55_lookup_simplex_id :
    rawSimplex55.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5', '5'])) := by
  rfl

attribute [local simp] simplex55_lookup_simplex_id

theorem simplex55_lookup_vertex_ids :
    rawSimplex55.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex55_lookup_vertex_ids

theorem simplex55_lookup_physical_volume :
    rawSimplex55.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '3', '8', '9', '7', '0', '7', '7', '3', '0', '7', '9', '5', '3', '5', '4', '8', '1', '1', '3', '6', '8', '0', '0', '0', '8', '2', '9', '1', '5', '6', '8', '8', '3', '9', '2', '6', '6', '3', '5', '2', '8', '2', '4', '8', '7', '/', '1', '2', '0', '8', '2', '7', '0', '9', '2', '4', '8', '0', '8', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex55_lookup_physical_volume

theorem simplex55_lookup_mean_gap :
    rawSimplex55.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex55_lookup_mean_gap

theorem simplex55_lookup_factor_maxima :
    rawSimplex55.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex55_lookup_factor_maxima

theorem simplex55_lookup_gap_weighted_means :
    rawSimplex55.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['4', '9', '7', '3', '8', '1', '1', '2', '3', '7', '9', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '9', '9', '3', '0', '6', '0', '7', '2', '4', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '2', '3', '7', '1', '3', '4', '4', '9', '3', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '9', '7', '3', '8', '6', '4', '4', '0', '2', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '7', '0', '3', '6', '7', '0', '4', '8', '6', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '5', '5', '1', '1', '1', '0', '9', '1', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '6', '4', '8', '4', '9', '3', '2', '2', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '7', '9', '7', '0', '3', '0', '0', '7', '8', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '2', '8', '8', '5', '2', '2', '1', '4', '7', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '4', '7', '7', '7', '4', '2', '6', '4', '1', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex55_lookup_gap_weighted_means

theorem simplex55_lookup_max_bound :
    rawSimplex55.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '2', '7', '2', '1', '8', '3', '8', '6', '4', '9', '5', '9', '2', '4', '9', '5', '7', '2', '6', '9', '3', '4', '9', '6', '0', '2', '1', '9', '0', '4', '9', '5', '1', '0', '0', '1', '6', '1', '0', '6', '8', '0', '1', '2', '9', '3', '0', '9', '7', '3', '8', '2', '8', '1', '2', '5', '/', '5', '9', '9', '1', '8', '8', '9', '6', '4', '0', '8', '1', '4', '9', '8', '5', '2', '9', '5', '6', '0', '0', '2', '7', '7', '0', '5', '6', '0', '9', '5', '2', '3', '4', '0', '5', '5', '0', '7', '0', '3', '1', '2', '6', '9', '9', '0', '0', '1', '7', '8', '5', '7', '7', '2', '1', '6', '0', '8', '8', '9', '5', '0', '4', '1', '6', '1', '7'])) := by
  rfl

attribute [local simp] simplex55_lookup_max_bound

theorem simplex55_lookup_jensen_bound :
    rawSimplex55.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '6', '6', '9', '7', '7', '0', '2', '2', '5', '5', '7', '5', '8', '5', '1', '6', '2', '1', '9', '3', '4', '2', '8', '3', '9', '9', '6', '1', '7', '1', '0', '7', '2', '9', '5', '7', '2', '0', '7', '8', '3', '8', '2', '3', '2', '9', '6', '8', '9', '3', '7', '9', '4', '7', '9', '0', '5', '6', '9', '3', '4', '4', '7', '5', '1', '9', '8', '6', '1', '3', '0', '6', '6', '3', '4', '0', '1', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '8', '2', '4', '1', '3', '3', '5', '9', '3', '6', '8', '3', '9', '8', '2', '0', '7', '8', '7', '1', '4', '4', '1', '1', '1', '6', '0', '1', '9', '0', '5', '4', '2', '2', '2', '6', '9', '4', '7', '3', '7', '7', '2', '8', '1', '6', '4', '4', '4', '3', '2', '8', '3', '2', '8', '9', '8', '7', '5', '8', '3', '7', '1', '6', '2', '0', '5', '2', '9', '1', '2', '1', '7', '4', '8', '2', '7', '9', '8', '8', '1', '7', '7', '4', '6', '4', '1', '9', '2', '3', '6', '4', '9', '6', '1', '3', '6', '8', '2', '4', '0', '7', '0', '8', '6', '8', '3', '8', '6', '0', '3', '5', '2', '1', '5', '7'])) := by
  rfl

attribute [local simp] simplex55_lookup_jensen_bound

theorem simplex55_lookup_max_floor_Q96 :
    rawSimplex55.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '6', '8', '2', '1', '5', '3', '6', '4', '5', '0', '6', '1', '2', '4', '3', '7', '5'])) := by
  rfl

attribute [local simp] simplex55_lookup_max_floor_Q96

theorem simplex55_lookup_jensen_floor_Q96 :
    rawSimplex55.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '3', '1', '0', '0', '5', '5', '9', '9', '4', '3', '8', '9', '3', '2', '3', '9', '3', '7'])) := by
  rfl

attribute [local simp] simplex55_lookup_jensen_floor_Q96

theorem simplex55_decoded : decodeSimplex rawSimplex55 = .ok simplex55 := by
  unfold decodeSimplex simplex55
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
