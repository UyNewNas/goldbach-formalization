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

theorem simplex57_lookup_simplex_id :
    rawSimplex57.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5', '7'])) := by
  rfl

attribute [local simp] simplex57_lookup_simplex_id

theorem simplex57_lookup_vertex_ids :
    rawSimplex57.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex57_lookup_vertex_ids

theorem simplex57_lookup_physical_volume :
    rawSimplex57.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '9', '3', '2', '0', '4', '3', '6', '3', '1', '8', '7', '3', '6', '3', '2', '6', '4', '2', '0', '6', '1', '0', '0', '9', '0', '4', '6', '2', '6', '4', '7', '9', '7', '9', '9', '9', '8', '2', '9', '2', '3', '3', '/', '2', '1', '1', '4', '4', '7', '4', '1', '1', '8', '4', '1', '4', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex57_lookup_physical_volume

theorem simplex57_lookup_mean_gap :
    rawSimplex57.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex57_lookup_mean_gap

theorem simplex57_lookup_factor_maxima :
    rawSimplex57.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex57_lookup_factor_maxima

theorem simplex57_lookup_gap_weighted_means :
    rawSimplex57.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '2', '5', '5', '8', '7', '5', '8', '1', '8', '3', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '8', '1', '3', '7', '0', '6', '5', '2', '8', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '3', '5', '2', '6', '1', '8', '8', '4', '6', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '5', '0', '0', '9', '7', '1', '8', '3', '8', '3', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '1', '7', '6', '5', '6', '3', '0', '5', '0', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '6', '3', '2', '0', '1', '4', '2', '2', '1', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '3', '4', '1', '7', '5', '2', '4', '5', '2', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '7', '3', '9', '3', '3', '2', '0', '8', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '1', '7', '3', '0', '3', '7', '7', '9', '4', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '3', '6', '2', '2', '5', '8', '2', '8', '8', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex57_lookup_gap_weighted_means

theorem simplex57_lookup_max_bound :
    rawSimplex57.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '3', '4', '3', '8', '4', '7', '7', '8', '3', '2', '3', '7', '2', '6', '2', '6', '0', '0', '9', '2', '1', '6', '9', '1', '9', '0', '8', '4', '7', '2', '1', '8', '3', '3', '2', '6', '9', '7', '2', '4', '5', '9', '4', '7', '9', '5', '6', '2', '5', '0', '0', '0', '0', '/', '6', '8', '6', '8', '1', '7', '3', '1', '9', '3', '8', '3', '6', '0', '3', '6', '1', '8', '2', '7', '0', '5', '3', '2', '9', '4', '4', '7', '0', '1', '5', '5', '7', '4', '7', '4', '4', '4', '3', '6', '9', '7', '5', '6', '4', '6', '9', '5', '2', '1', '0', '4', '9', '2', '3', '6', '4', '0', '1', '4', '6', '5', '6', '1', '9', '3'])) := by
  rfl

attribute [local simp] simplex57_lookup_max_bound

theorem simplex57_lookup_jensen_bound :
    rawSimplex57.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '0', '0', '7', '9', '6', '0', '9', '0', '7', '7', '5', '7', '8', '8', '0', '7', '6', '6', '1', '6', '5', '6', '9', '0', '4', '6', '1', '5', '0', '8', '2', '9', '1', '1', '9', '3', '7', '0', '0', '2', '6', '6', '0', '1', '0', '9', '2', '0', '8', '0', '8', '1', '0', '4', '2', '7', '6', '6', '0', '6', '6', '3', '4', '1', '9', '2', '6', '0', '2', '5', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '1', '8', '3', '3', '2', '1', '1', '8', '5', '9', '6', '6', '0', '7', '8', '4', '8', '1', '9', '8', '1', '1', '3', '4', '2', '6', '3', '3', '9', '1', '3', '6', '5', '3', '2', '7', '9', '2', '1', '4', '3', '8', '8', '3', '2', '3', '2', '8', '8', '7', '4', '2', '4', '2', '7', '4', '8', '8', '6', '6', '9', '1', '0', '1', '1', '0', '8', '6', '3', '7', '3', '1', '1', '0', '0', '8', '2', '4', '9', '3', '5', '1', '4', '3', '8', '4', '9', '2', '0', '6', '3', '4', '4', '5', '8', '4', '3', '7', '5', '8', '4', '7', '7', '5', '8', '6', '5', '0', '4', '5', '1'])) := by
  rfl

attribute [local simp] simplex57_lookup_jensen_bound

theorem simplex57_lookup_max_floor_Q96 :
    rawSimplex57.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '1', '6', '4', '4', '2', '2', '8', '9', '1', '9', '8', '2', '1', '9', '2', '0'])) := by
  rfl

attribute [local simp] simplex57_lookup_max_floor_Q96

theorem simplex57_lookup_jensen_floor_Q96 :
    rawSimplex57.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '8', '5', '4', '1', '6', '2', '0', '0', '2', '4', '0', '8', '7', '6', '2', '5', '9'])) := by
  rfl

attribute [local simp] simplex57_lookup_jensen_floor_Q96

theorem simplex57_decoded : decodeSimplex rawSimplex57 = .ok simplex57 := by
  unfold decodeSimplex simplex57
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
