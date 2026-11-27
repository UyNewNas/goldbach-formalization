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

theorem simplex08_lookup_simplex_id :
    rawSimplex08.getObjVal? "simplex_id" = .ok (.number (String.ofList ['8'])) := by
  rfl

attribute [local simp] simplex08_lookup_simplex_id

theorem simplex08_lookup_vertex_ids :
    rawSimplex08.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex08_lookup_vertex_ids

theorem simplex08_lookup_physical_volume :
    rawSimplex08.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '3', '1', '2', '6', '2', '7', '5', '8', '7', '8', '9', '9', '7', '6', '4', '6', '5', '0', '8', '3', '8', '4', '6', '1', '9', '1', '9', '5', '5', '0', '7', '8', '7', '8', '9', '0', '6', '3', '3', '/', '1', '1', '7', '4', '7', '0', '7', '8', '4', '3', '5', '6', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex08_lookup_physical_volume

theorem simplex08_lookup_mean_gap :
    rawSimplex08.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex08_lookup_mean_gap

theorem simplex08_lookup_factor_maxima :
    rawSimplex08.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex08_lookup_factor_maxima

theorem simplex08_lookup_gap_weighted_means :
    rawSimplex08.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '7', '7', '2', '0', '5', '3', '1', '4', '9', '1', '/', '2', '3', '2', '3', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '8', '0', '3', '2', '4', '5', '5', '8', '1', '/', '3', '7', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '6', '8', '9', '9', '8', '0', '0', '9', '6', '9', '/', '1', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '3', '8', '8', '1', '4', '1', '8', '3', '0', '1', '/', '5', '5', '7', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '7', '0', '0', '9', '8', '0', '7', '7', '9', '/', '5', '5', '7', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '9', '9', '8', '7', '7', '6', '4', '5', '2', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '8', '4', '4', '6', '6', '5', '7', '7', '7', '/', '1', '4', '8', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '1', '3', '3', '8', '9', '2', '1', '7', '/', '5', '5', '7', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '6', '7', '5', '5', '0', '9', '1', '/', '3', '4', '8', '4', '6', '8', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '5', '4', '5', '7', '5', '6', '5', '8', '1', '/', '1', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex08_lookup_gap_weighted_means

theorem simplex08_lookup_max_bound :
    rawSimplex08.getObjVal? "max_bound" = .ok (.str (String.ofList ['9', '7', '6', '2', '1', '2', '9', '9', '6', '7', '5', '9', '7', '6', '7', '6', '1', '8', '0', '4', '8', '2', '0', '1', '7', '7', '6', '3', '8', '6', '3', '2', '4', '7', '4', '8', '7', '0', '0', '5', '6', '3', '5', '5', '5', '6', '2', '5', '0', '0', '0', '0', '0', '/', '1', '5', '7', '2', '9', '8', '0', '1', '9', '0', '8', '7', '4', '0', '6', '6', '5', '0', '8', '8', '2', '2', '3', '7', '3', '3', '8', '1', '8', '4', '4', '3', '1', '9', '2', '7', '3', '4', '0', '0', '9', '9', '4', '8', '1', '2', '0', '1', '5', '9', '2', '3', '6', '2', '0', '4', '1', '2', '0', '4', '7', '5', '0', '2', '3', '9', '2', '8', '3'])) := by
  rfl

attribute [local simp] simplex08_lookup_max_bound

theorem simplex08_lookup_jensen_bound :
    rawSimplex08.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['5', '9', '2', '2', '9', '3', '9', '4', '9', '9', '3', '6', '6', '2', '5', '5', '6', '9', '3', '3', '9', '4', '0', '1', '1', '5', '4', '9', '0', '0', '0', '2', '6', '2', '4', '2', '8', '0', '8', '4', '0', '4', '5', '3', '5', '4', '5', '6', '1', '7', '1', '7', '7', '7', '0', '6', '0', '3', '3', '4', '1', '1', '8', '8', '4', '0', '8', '5', '7', '5', '9', '2', '4', '0', '3', '8', '8', '8', '7', '0', '2', '3', '9', '2', '5', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '/', '1', '1', '1', '8', '3', '2', '7', '4', '0', '4', '4', '4', '7', '7', '9', '1', '0', '9', '1', '7', '6', '2', '7', '2', '5', '5', '9', '0', '5', '9', '3', '7', '3', '2', '0', '2', '3', '3', '9', '7', '8', '3', '7', '4', '3', '0', '9', '3', '5', '6', '2', '0', '6', '1', '3', '0', '9', '2', '9', '3', '2', '4', '0', '7', '4', '0', '6', '9', '2', '3', '1', '1', '7', '2', '0', '3', '6', '9', '4', '2', '2', '6', '1', '6', '5', '3', '1', '4', '0', '9', '1', '7', '1', '4', '4', '7', '3', '3', '5', '6', '4', '7', '9', '0', '6', '8', '0', '1', '9', '9'])) := by
  rfl

attribute [local simp] simplex08_lookup_jensen_bound

theorem simplex08_lookup_max_floor_Q96 :
    rawSimplex08.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '9', '1', '7', '0', '0', '8', '0', '0', '8', '3', '9', '9', '7'])) := by
  rfl

attribute [local simp] simplex08_lookup_max_floor_Q96

theorem simplex08_lookup_jensen_floor_Q96 :
    rawSimplex08.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '1', '9', '6', '1', '2', '0', '1', '2', '8', '6', '0', '9', '9', '0'])) := by
  rfl

attribute [local simp] simplex08_lookup_jensen_floor_Q96

theorem simplex08_decoded : decodeSimplex rawSimplex08 = .ok simplex08 := by
  unfold decodeSimplex simplex08
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
