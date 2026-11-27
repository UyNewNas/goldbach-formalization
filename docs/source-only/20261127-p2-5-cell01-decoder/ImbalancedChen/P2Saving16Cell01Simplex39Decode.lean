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

theorem simplex39_lookup_simplex_id :
    rawSimplex39.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3', '9'])) := by
  rfl

attribute [local simp] simplex39_lookup_simplex_id

theorem simplex39_lookup_vertex_ids :
    rawSimplex39.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex39_lookup_vertex_ids

theorem simplex39_lookup_physical_volume :
    rawSimplex39.getObjVal? "physical_volume" = .ok (.str (String.ofList ['5', '9', '4', '7', '6', '5', '3', '3', '4', '9', '3', '9', '5', '9', '6', '2', '1', '6', '2', '2', '6', '1', '5', '8', '3', '1', '2', '3', '1', '/', '1', '6', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex39_lookup_physical_volume

theorem simplex39_lookup_mean_gap :
    rawSimplex39.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex39_lookup_mean_gap

theorem simplex39_lookup_factor_maxima :
    rawSimplex39.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex39_lookup_factor_maxima

theorem simplex39_lookup_gap_weighted_means :
    rawSimplex39.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '6', '7', '4', '6', '8', '4', '6', '2', '3', '7', '/', '3', '4', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '4', '0', '5', '4', '5', '8', '3', '7', '/', '3', '4', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '4', '2', '0', '1', '2', '3', '3', '1', '9', '/', '5', '1', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '5', '9', '5', '1', '5', '9', '6', '9', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '9', '4', '7', '9', '0', '1', '4', '1', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '1', '4', '4', '6', '9', '1', '6', '9', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '9', '9', '9', '4', '3', '5', '3', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '5', '1', '0', '3', '8', '3', '4', '6', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '0', '3', '5', '8', '5', '2', '3', '2', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '6', '2', '3', '0', '5', '3', '3', '7', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex39_lookup_gap_weighted_means

theorem simplex39_lookup_max_bound :
    rawSimplex39.getObjVal? "max_bound" = .ok (.str (String.ofList ['2', '3', '7', '8', '7', '5', '6', '8', '1', '9', '9', '0', '6', '8', '9', '5', '7', '9', '1', '6', '4', '1', '9', '2', '5', '4', '5', '6', '1', '8', '4', '0', '9', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '5', '1', '3', '9', '5', '4', '4', '8', '7', '3', '8', '1', '1', '5', '5', '7', '2', '2', '2', '6', '9', '0', '2', '4', '7', '9', '4', '7', '0', '3', '6', '7', '2', '2', '7', '2', '2', '0', '0', '9', '8', '6', '2', '2', '7', '4', '7', '1', '1', '7', '6', '0', '5', '2', '1', '1', '1', '9', '6', '7', '4', '6', '9'])) := by
  rfl

attribute [local simp] simplex39_lookup_max_bound

theorem simplex39_lookup_jensen_bound :
    rawSimplex39.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '6', '0', '5', '6', '4', '8', '4', '8', '3', '1', '1', '8', '1', '0', '9', '0', '0', '7', '5', '0', '0', '6', '8', '4', '3', '5', '4', '3', '0', '1', '8', '6', '8', '3', '5', '8', '4', '6', '6', '2', '9', '0', '3', '2', '9', '6', '0', '0', '3', '1', '3', '8', '4', '6', '3', '3', '0', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '7', '0', '7', '2', '0', '2', '4', '1', '4', '5', '7', '1', '8', '2', '5', '3', '5', '7', '3', '7', '3', '6', '0', '6', '9', '5', '3', '5', '9', '1', '7', '0', '0', '8', '7', '7', '4', '5', '7', '8', '2', '5', '9', '7', '1', '6', '6', '4', '6', '3', '9', '2', '9', '4', '9', '4', '7', '6', '1', '0', '4', '7', '9', '5', '5', '6', '5', '0', '1', '0', '0', '9', '8', '6', '4', '9', '6', '0', '3', '1', '4', '6', '0', '8', '0', '2', '8', '9', '0', '5', '0', '6', '1', '4', '9', '6', '5', '1', '4', '7', '6', '7'])) := by
  rfl

attribute [local simp] simplex39_lookup_jensen_bound

theorem simplex39_lookup_max_floor_Q96 :
    rawSimplex39.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '1', '7', '5', '1', '5', '3', '5', '6', '9', '5', '8', '8'])) := by
  rfl

attribute [local simp] simplex39_lookup_max_floor_Q96

theorem simplex39_lookup_jensen_floor_Q96 :
    rawSimplex39.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '7', '0', '2', '5', '0', '9', '2', '1', '3', '6', '9', '8', '9'])) := by
  rfl

attribute [local simp] simplex39_lookup_jensen_floor_Q96

theorem simplex39_decoded : decodeSimplex rawSimplex39 = .ok simplex39 := by
  unfold decodeSimplex simplex39
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
