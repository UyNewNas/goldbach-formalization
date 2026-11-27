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

theorem simplex40_lookup_simplex_id :
    rawSimplex40.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '0'])) := by
  rfl

attribute [local simp] simplex40_lookup_simplex_id

theorem simplex40_lookup_vertex_ids :
    rawSimplex40.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex40_lookup_vertex_ids

theorem simplex40_lookup_physical_volume :
    rawSimplex40.getObjVal? "physical_volume" = .ok (.str (String.ofList ['7', '9', '2', '9', '9', '5', '0', '6', '6', '6', '8', '3', '2', '0', '9', '9', '5', '8', '6', '5', '0', '1', '2', '3', '3', '8', '5', '1', '/', '2', '1', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex40_lookup_physical_volume

theorem simplex40_lookup_mean_gap :
    rawSimplex40.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex40_lookup_mean_gap

theorem simplex40_lookup_factor_maxima :
    rawSimplex40.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex40_lookup_factor_maxima

theorem simplex40_lookup_gap_weighted_means :
    rawSimplex40.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '3', '3', '7', '3', '4', '3', '1', '7', '8', '1', '/', '1', '7', '3', '2', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '7', '0', '2', '8', '1', '5', '8', '1', '/', '1', '7', '3', '2', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '4', '8', '4', '0', '2', '2', '9', '3', '1', '3', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '9', '5', '1', '5', '9', '6', '9', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '9', '4', '7', '9', '0', '1', '4', '1', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '2', '2', '7', '3', '1', '9', '3', '9', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '0', '8', '7', '9', '5', '5', '4', '3', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '1', '0', '3', '9', '0', '3', '9', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '0', '3', '5', '7', '4', '8', '3', '7', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '3', '1', '1', '6', '1', '3', '3', '1', '/', '5', '1', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex40_lookup_gap_weighted_means

theorem simplex40_lookup_max_bound :
    rawSimplex40.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '9', '2', '8', '9', '3', '5', '6', '3', '3', '1', '4', '6', '7', '4', '5', '0', '7', '7', '7', '5', '4', '1', '6', '1', '6', '9', '3', '0', '6', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '0', '4', '6', '5', '1', '4', '9', '5', '7', '9', '3', '7', '1', '8', '5', '7', '4', '0', '8', '9', '6', '7', '4', '9', '3', '1', '5', '6', '7', '8', '9', '0', '7', '5', '7', '4', '0', '0', '3', '2', '8', '7', '4', '2', '4', '9', '0', '3', '9', '2', '0', '1', '7', '3', '7', '0', '6', '5', '5', '8', '2', '3'])) := by
  rfl

attribute [local simp] simplex40_lookup_max_bound

theorem simplex40_lookup_jensen_bound :
    rawSimplex40.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '3', '6', '1', '1', '7', '2', '1', '9', '9', '6', '8', '9', '8', '1', '0', '4', '5', '7', '5', '9', '0', '7', '5', '4', '3', '2', '9', '5', '0', '2', '9', '7', '0', '5', '8', '5', '4', '2', '4', '5', '4', '5', '6', '9', '9', '4', '1', '9', '4', '9', '3', '0', '4', '2', '3', '3', '6', '9', '1', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '8', '9', '4', '4', '2', '9', '1', '3', '0', '8', '2', '4', '2', '6', '9', '0', '8', '8', '7', '3', '8', '8', '2', '8', '3', '2', '3', '7', '5', '0', '4', '8', '7', '1', '4', '6', '0', '1', '2', '4', '1', '4', '8', '3', '7', '1', '8', '4', '1', '0', '7', '3', '7', '5', '4', '3', '2', '2', '8', '5', '3', '5', '8', '7', '5', '2', '0', '1', '9', '1', '6', '7', '7', '9', '2', '4', '4', '7', '1', '6', '5', '2', '6', '8', '0', '2', '6', '3', '7', '7', '4', '8', '3', '3', '5', '5', '1', '3', '1', '9'])) := by
  rfl

attribute [local simp] simplex40_lookup_jensen_bound

theorem simplex40_lookup_max_floor_Q96 :
    rawSimplex40.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '1', '7', '5', '0', '1', '9', '9', '4', '7', '5', '7', '0'])) := by
  rfl

attribute [local simp] simplex40_lookup_max_floor_Q96

theorem simplex40_lookup_jensen_floor_Q96 :
    rawSimplex40.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '7', '1', '3', '3', '6', '9', '4', '6', '4', '1', '2', '0', '1'])) := by
  rfl

attribute [local simp] simplex40_lookup_jensen_floor_Q96

theorem simplex40_decoded : decodeSimplex rawSimplex40 = .ok simplex40 := by
  unfold decodeSimplex simplex40
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
