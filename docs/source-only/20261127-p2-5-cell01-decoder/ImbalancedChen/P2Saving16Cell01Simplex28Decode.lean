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

theorem simplex28_lookup_simplex_id :
    rawSimplex28.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2', '8'])) := by
  rfl

attribute [local simp] simplex28_lookup_simplex_id

theorem simplex28_lookup_vertex_ids :
    rawSimplex28.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex28_lookup_vertex_ids

theorem simplex28_lookup_physical_volume :
    rawSimplex28.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '5', '1', '6', '6', '8', '8', '9', '1', '2', '5', '5', '3', '2', '6', '0', '2', '9', '5', '9', '6', '4', '2', '9', '2', '6', '1', '2', '4', '2', '1', '1', '/', '1', '7', '6', '3', '5', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex28_lookup_physical_volume

theorem simplex28_lookup_mean_gap :
    rawSimplex28.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex28_lookup_mean_gap

theorem simplex28_lookup_factor_maxima :
    rawSimplex28.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex28_lookup_factor_maxima

theorem simplex28_lookup_gap_weighted_means :
    rawSimplex28.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '2', '8', '6', '2', '1', '0', '5', '7', '4', '9', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '6', '4', '9', '5', '0', '4', '9', '4', '9', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '0', '3', '1', '2', '0', '8', '0', '0', '0', '1', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '4', '7', '7', '9', '4', '3', '8', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '6', '7', '1', '1', '8', '1', '9', '9', '/', '2', '5', '9', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '6', '6', '8', '7', '9', '7', '3', '9', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '0', '0', '3', '8', '1', '9', '6', '3', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '9', '2', '0', '3', '3', '0', '6', '1', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '2', '0', '2', '1', '3', '2', '7', '9', '9', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '0', '9', '3', '0', '2', '3', '9', '4', '9', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex28_lookup_gap_weighted_means

theorem simplex28_lookup_max_bound :
    rawSimplex28.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '2', '1', '3', '1', '9', '5', '8', '2', '1', '0', '9', '7', '9', '6', '2', '7', '8', '2', '9', '1', '7', '1', '2', '7', '3', '4', '6', '3', '7', '3', '3', '6', '8', '0', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '6', '7', '0', '9', '1', '5', '1', '8', '9', '3', '5', '5', '5', '9', '2', '5', '7', '0', '8', '5', '6', '8', '3', '5', '7', '7', '3', '4', '9', '6', '8', '8', '8', '5', '3', '4', '6', '8', '4', '3', '0', '8', '7', '3', '1', '6', '5', '5', '8', '0', '6', '4', '8', '5', '5', '4', '5', '2', '9', '2', '9', '7', '7', '1'])) := by
  rfl

attribute [local simp] simplex28_lookup_max_bound

theorem simplex28_lookup_jensen_bound :
    rawSimplex28.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '1', '9', '7', '8', '7', '7', '0', '7', '4', '0', '6', '4', '9', '4', '1', '4', '2', '8', '6', '3', '1', '1', '7', '1', '6', '6', '9', '9', '1', '1', '4', '3', '6', '2', '1', '7', '2', '7', '9', '6', '4', '6', '1', '6', '5', '1', '2', '7', '3', '7', '6', '7', '7', '3', '1', '6', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '1', '6', '8', '5', '0', '6', '7', '4', '6', '2', '0', '5', '6', '4', '5', '4', '2', '8', '2', '6', '5', '0', '8', '4', '2', '5', '1', '5', '0', '1', '4', '7', '4', '3', '6', '4', '5', '0', '8', '8', '4', '3', '2', '7', '5', '0', '1', '8', '8', '8', '6', '7', '1', '5', '4', '1', '5', '2', '1', '3', '9', '5', '0', '5', '5', '7', '8', '2', '1', '7', '8', '7', '5', '5', '8', '9', '7', '7', '6', '5', '8', '8', '6', '6', '0', '4', '1', '7', '6', '2', '7', '5', '8', '9', '5', '8', '3', '3', '9', '7', '1'])) := by
  rfl

attribute [local simp] simplex28_lookup_jensen_bound

theorem simplex28_lookup_max_floor_Q96 :
    rawSimplex28.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['9', '0', '0', '7', '5', '9', '4', '3', '7', '8', '7', '3', '2'])) := by
  rfl

attribute [local simp] simplex28_lookup_max_floor_Q96

theorem simplex28_lookup_jensen_floor_Q96 :
    rawSimplex28.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '4', '3', '4', '9', '3', '5', '7', '2', '4', '5', '8', '0', '1'])) := by
  rfl

attribute [local simp] simplex28_lookup_jensen_floor_Q96

theorem simplex28_decoded : decodeSimplex rawSimplex28 = .ok simplex28 := by
  unfold decodeSimplex simplex28
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
