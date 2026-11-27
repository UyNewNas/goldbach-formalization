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

theorem simplex49_lookup_simplex_id :
    rawSimplex49.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '9'])) := by
  rfl

attribute [local simp] simplex49_lookup_simplex_id

theorem simplex49_lookup_vertex_ids :
    rawSimplex49.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex49_lookup_vertex_ids

theorem simplex49_lookup_physical_volume :
    rawSimplex49.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '3', '6', '3', '3', '0', '7', '5', '2', '8', '5', '8', '9', '8', '1', '8', '6', '8', '8', '7', '6', '7', '3', '2', '2', '7', '5', '3', '2', '7', '7', '3', '3', '5', '5', '4', '6', '8', '7', '0', '7', '9', '4', '9', '0', '1', '1', '/', '3', '6', '2', '4', '8', '1', '2', '7', '7', '4', '4', '2', '4', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex49_lookup_physical_volume

theorem simplex49_lookup_mean_gap :
    rawSimplex49.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex49_lookup_mean_gap

theorem simplex49_lookup_factor_maxima :
    rawSimplex49.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex49_lookup_factor_maxima

theorem simplex49_lookup_gap_weighted_means :
    rawSimplex49.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '1', '0', '9', '3', '2', '2', '7', '3', '2', '9', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '2', '3', '4', '8', '1', '7', '5', '6', '7', '4', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '8', '8', '2', '0', '1', '9', '5', '4', '3', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '7', '0', '2', '8', '4', '1', '4', '1', '2', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '9', '7', '4', '6', '9', '3', '4', '7', '6', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '0', '6', '6', '5', '5', '4', '7', '3', '1', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '7', '6', '4', '8', '4', '6', '9', '9', '/', '2', '4', '7', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '2', '5', '4', '9', '8', '4', '0', '9', '8', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '5', '7', '8', '2', '9', '2', '2', '4', '7', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '8', '3', '2', '8', '5', '7', '5', '9', '1', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex49_lookup_gap_weighted_means

theorem simplex49_lookup_max_bound :
    rawSimplex49.getObjVal? "max_bound" = .ok (.str (String.ofList ['2', '1', '6', '3', '4', '4', '8', '9', '3', '1', '8', '7', '5', '7', '5', '3', '6', '3', '8', '0', '4', '1', '7', '1', '1', '7', '3', '2', '1', '0', '3', '6', '3', '8', '2', '2', '5', '4', '8', '6', '6', '7', '5', '7', '0', '4', '6', '3', '4', '8', '9', '4', '1', '4', '0', '6', '2', '5', '/', '2', '5', '6', '0', '1', '9', '5', '1', '1', '6', '2', '4', '9', '0', '9', '1', '8', '1', '0', '9', '9', '7', '2', '5', '3', '7', '9', '4', '5', '7', '6', '5', '9', '5', '3', '9', '2', '1', '8', '4', '6', '0', '9', '6', '6', '4', '7', '3', '8', '5', '0', '9', '8', '4', '6', '3', '5', '9', '8', '9', '8', '0', '2', '5', '3', '1', '7', '2', '1'])) := by
  rfl

attribute [local simp] simplex49_lookup_max_bound

theorem simplex49_lookup_jensen_bound :
    rawSimplex49.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['7', '3', '5', '3', '0', '6', '6', '9', '6', '7', '7', '0', '9', '2', '2', '5', '7', '0', '1', '7', '6', '1', '7', '3', '6', '1', '5', '9', '7', '2', '0', '4', '1', '2', '5', '6', '2', '6', '4', '9', '6', '7', '0', '6', '9', '2', '4', '4', '6', '5', '7', '1', '8', '2', '1', '5', '1', '9', '8', '5', '8', '2', '8', '7', '0', '4', '7', '7', '3', '5', '7', '9', '3', '6', '2', '1', '7', '1', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '9', '4', '9', '3', '5', '3', '1', '0', '7', '9', '1', '2', '0', '9', '8', '5', '3', '4', '4', '3', '4', '7', '1', '1', '8', '8', '6', '2', '2', '5', '4', '7', '6', '7', '5', '3', '7', '4', '5', '5', '9', '4', '8', '9', '7', '8', '8', '5', '7', '5', '7', '8', '6', '1', '9', '9', '8', '4', '5', '1', '9', '9', '4', '5', '7', '6', '4', '5', '5', '0', '9', '6', '3', '2', '3', '1', '3', '9', '0', '5', '7', '6', '5', '9', '5', '9', '6', '9', '2', '0', '1', '8', '7', '7', '1', '4', '3', '3', '9', '7', '7', '6', '7', '6', '1', '8', '0', '9', '1', '9', '2', '3', '8', '7'])) := by
  rfl

attribute [local simp] simplex49_lookup_jensen_bound

theorem simplex49_lookup_max_floor_Q96 :
    rawSimplex49.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '6', '9', '5', '0', '3', '9', '8', '6', '1', '5', '3', '5', '5', '7', '7', '1', '5'])) := by
  rfl

attribute [local simp] simplex49_lookup_max_floor_Q96

theorem simplex49_lookup_jensen_floor_Q96 :
    rawSimplex49.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '2', '8', '5', '2', '0', '6', '5', '8', '0', '6', '5', '8', '1', '9', '7', '2', '8'])) := by
  rfl

attribute [local simp] simplex49_lookup_jensen_floor_Q96

theorem simplex49_decoded : decodeSimplex rawSimplex49 = .ok simplex49 := by
  unfold decodeSimplex simplex49
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
