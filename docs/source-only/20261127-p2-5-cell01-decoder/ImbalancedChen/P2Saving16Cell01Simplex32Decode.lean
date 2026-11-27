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

theorem simplex32_lookup_simplex_id :
    rawSimplex32.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3', '2'])) := by
  rfl

attribute [local simp] simplex32_lookup_simplex_id

theorem simplex32_lookup_vertex_ids :
    rawSimplex32.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex32_lookup_vertex_ids

theorem simplex32_lookup_physical_volume :
    rawSimplex32.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '3', '1', '2', '4', '9', '7', '6', '8', '9', '5', '7', '6', '2', '6', '6', '1', '0', '1', '1', '1', '5', '2', '5', '5', '3', '6', '8', '3', '5', '1', '4', '3', '2', '7', '7', '7', '3', '1', '3', '/', '1', '2', '7', '4', '2', '5', '9', '3', '5', '5', '7', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex32_lookup_physical_volume

theorem simplex32_lookup_mean_gap :
    rawSimplex32.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex32_lookup_mean_gap

theorem simplex32_lookup_factor_maxima :
    rawSimplex32.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '8', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex32_lookup_factor_maxima

theorem simplex32_lookup_gap_weighted_means :
    rawSimplex32.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '0', '4', '2', '6', '6', '9', '2', '1', '2', '5', '1', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '8', '1', '7', '6', '9', '9', '9', '9', '7', '/', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '9', '7', '2', '5', '4', '3', '6', '0', '3', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '4', '2', '4', '3', '1', '5', '9', '8', '7', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '0', '3', '7', '0', '2', '9', '9', '9', '/', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '3', '5', '9', '9', '9', '5', '3', '4', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '4', '3', '5', '9', '6', '3', '0', '2', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '2', '0', '4', '9', '6', '6', '1', '4', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '5', '8', '4', '5', '4', '2', '0', '6', '9', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '8', '6', '7', '5', '3', '1', '9', '9', '7', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex32_lookup_gap_weighted_means

theorem simplex32_lookup_max_bound :
    rawSimplex32.getObjVal? "max_bound" = .ok (.str (String.ofList ['3', '0', '5', '0', '5', '4', '3', '0', '9', '8', '8', '9', '0', '2', '2', '4', '9', '2', '4', '4', '2', '3', '5', '4', '2', '5', '2', '7', '1', '3', '9', '3', '3', '6', '8', '4', '7', '3', '8', '8', '3', '4', '1', '4', '2', '3', '8', '2', '8', '1', '2', '5', '/', '5', '7', '8', '3', '9', '9', '9', '0', '9', '0', '3', '9', '4', '1', '6', '3', '0', '9', '6', '1', '9', '8', '8', '6', '9', '7', '8', '0', '8', '0', '4', '2', '8', '3', '5', '3', '5', '6', '6', '0', '7', '8', '7', '6', '4', '1', '4', '4', '9', '6', '4', '7', '6', '0', '6', '2', '9', '9', '2', '4', '1', '2', '5', '4', '7', '8', '4'])) := by
  rfl

attribute [local simp] simplex32_lookup_max_bound

theorem simplex32_lookup_jensen_bound :
    rawSimplex32.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['9', '6', '7', '6', '5', '8', '5', '6', '4', '2', '5', '4', '7', '8', '3', '5', '1', '2', '6', '6', '5', '8', '4', '3', '6', '8', '7', '8', '6', '2', '4', '7', '3', '6', '3', '3', '9', '6', '9', '5', '9', '5', '1', '4', '3', '0', '3', '1', '2', '7', '3', '5', '0', '6', '1', '2', '1', '1', '3', '4', '8', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '1', '1', '9', '9', '3', '8', '1', '4', '0', '7', '6', '8', '7', '1', '9', '7', '7', '4', '3', '3', '0', '8', '0', '0', '6', '8', '9', '1', '4', '7', '8', '7', '6', '2', '7', '3', '1', '7', '9', '6', '1', '7', '2', '4', '5', '7', '2', '4', '6', '3', '4', '1', '4', '2', '8', '1', '1', '6', '1', '5', '3', '9', '1', '2', '6', '4', '6', '0', '3', '2', '6', '1', '5', '6', '0', '0', '9', '8', '6', '0', '3', '5', '8', '6', '0', '7', '2', '6', '2', '1', '5', '4', '8', '0', '7', '5', '4', '8', '8', '2', '1', '6', '3', '5', '3', '9', '1'])) := by
  rfl

attribute [local simp] simplex32_lookup_jensen_bound

theorem simplex32_lookup_max_floor_Q96 :
    rawSimplex32.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '1', '7', '8', '5', '7', '8', '1', '8', '8', '1', '7', '8', '3'])) := by
  rfl

attribute [local simp] simplex32_lookup_max_floor_Q96

theorem simplex32_lookup_jensen_floor_Q96 :
    rawSimplex32.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '6', '1', '6', '4', '1', '7', '3', '1', '4', '8', '6', '0', '7', '8'])) := by
  rfl

attribute [local simp] simplex32_lookup_jensen_floor_Q96

theorem simplex32_decoded : decodeSimplex rawSimplex32 = .ok simplex32 := by
  unfold decodeSimplex simplex32
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
