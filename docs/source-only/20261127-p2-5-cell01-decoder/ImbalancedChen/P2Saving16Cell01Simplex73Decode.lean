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

theorem simplex73_lookup_simplex_id :
    rawSimplex73.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '3'])) := by
  rfl

attribute [local simp] simplex73_lookup_simplex_id

theorem simplex73_lookup_vertex_ids :
    rawSimplex73.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex73_lookup_vertex_ids

theorem simplex73_lookup_physical_volume :
    rawSimplex73.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '1', '1', '7', '6', '7', '4', '4', '6', '6', '0', '2', '4', '1', '2', '3', '4', '7', '0', '7', '2', '8', '9', '5', '9', '3', '6', '3', '9', '1', '3', '1', '6', '2', '0', '5', '7', '/', '1', '0', '6', '0', '9', '1', '3', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex73_lookup_physical_volume

theorem simplex73_lookup_mean_gap :
    rawSimplex73.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex73_lookup_mean_gap

theorem simplex73_lookup_factor_maxima :
    rawSimplex73.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '2', '1', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex73_lookup_factor_maxima

theorem simplex73_lookup_gap_weighted_means :
    rawSimplex73.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '1', '4', '7', '2', '4', '0', '5', '5', '4', '7', '/', '1', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '4', '7', '3', '8', '3', '1', '4', '7', '/', '1', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '4', '2', '5', '7', '2', '6', '1', '8', '0', '9', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '8', '0', '0', '3', '3', '4', '1', '9', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '0', '6', '8', '3', '8', '6', '3', '1', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '1', '9', '8', '3', '6', '9', '7', '/', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '3', '4', '3', '9', '5', '0', '4', '3', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '8', '1', '7', '8', '6', '0', '2', '6', '3', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '6', '5', '6', '3', '6', '8', '5', '0', '7', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '9', '0', '4', '5', '2', '6', '2', '4', '1', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex73_lookup_gap_weighted_means

theorem simplex73_lookup_max_bound :
    rawSimplex73.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '7', '2', '1', '7', '6', '0', '7', '8', '6', '9', '0', '5', '4', '5', '8', '6', '0', '0', '5', '7', '4', '4', '9', '5', '0', '1', '2', '4', '2', '6', '6', '5', '5', '6', '0', '1', '9', '5', '4', '3', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '/', '2', '6', '7', '3', '8', '5', '0', '2', '5', '2', '1', '5', '8', '7', '8', '9', '0', '9', '7', '4', '2', '3', '5', '3', '6', '8', '4', '3', '4', '1', '3', '3', '7', '5', '0', '1', '9', '2', '5', '9', '1', '5', '0', '3', '5', '5', '2', '1', '3', '6', '1', '0', '4', '5', '7', '1', '7', '6', '4', '0', '1', '9', '0', '4', '9'])) := by
  rfl

attribute [local simp] simplex73_lookup_max_bound

theorem simplex73_lookup_jensen_bound :
    rawSimplex73.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '1', '3', '1', '2', '9', '3', '9', '9', '2', '9', '4', '9', '3', '5', '8', '7', '9', '1', '7', '2', '1', '7', '8', '3', '2', '6', '5', '2', '2', '8', '0', '5', '6', '6', '8', '8', '9', '5', '9', '0', '8', '0', '3', '9', '2', '1', '6', '9', '5', '4', '4', '0', '1', '0', '4', '8', '4', '9', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '4', '2', '6', '3', '8', '7', '2', '7', '2', '1', '5', '1', '7', '0', '0', '5', '0', '1', '9', '3', '0', '2', '0', '1', '5', '3', '1', '4', '5', '7', '7', '0', '4', '4', '9', '5', '7', '0', '0', '0', '0', '6', '2', '7', '3', '9', '6', '7', '7', '0', '8', '2', '6', '0', '7', '6', '6', '0', '3', '1', '3', '8', '1', '8', '2', '3', '1', '4', '3', '1', '3', '9', '9', '2', '9', '3', '2', '0', '7', '8', '6', '4', '0', '5', '9', '5', '1', '1', '3', '2', '8', '0', '9', '4', '4', '3', '1', '0', '1', '7'])) := by
  rfl

attribute [local simp] simplex73_lookup_jensen_bound

theorem simplex73_lookup_max_floor_Q96 :
    rawSimplex73.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '6', '9', '5', '4', '0', '0', '0', '8', '1', '3', '1', '2', '2', '9', '3', '2'])) := by
  rfl

attribute [local simp] simplex73_lookup_max_floor_Q96

theorem simplex73_lookup_jensen_floor_Q96 :
    rawSimplex73.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '8', '4', '4', '1', '5', '4', '2', '5', '3', '6', '5', '8', '9', '1', '1', '8'])) := by
  rfl

attribute [local simp] simplex73_lookup_jensen_floor_Q96

theorem simplex73_decoded : decodeSimplex rawSimplex73 = .ok simplex73 := by
  unfold decodeSimplex simplex73
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
