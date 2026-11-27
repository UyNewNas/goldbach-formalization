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

theorem simplex41_lookup_simplex_id :
    rawSimplex41.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '1'])) := by
  rfl

attribute [local simp] simplex41_lookup_simplex_id

theorem simplex41_lookup_vertex_ids :
    rawSimplex41.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex41_lookup_vertex_ids

theorem simplex41_lookup_physical_volume :
    rawSimplex41.getObjVal? "physical_volume" = .ok (.str (String.ofList ['9', '4', '4', '0', '5', '6', '8', '4', '5', '4', '0', '1', '8', '5', '3', '4', '9', '3', '2', '0', '8', '6', '8', '0', '8', '1', '6', '9', '1', '5', '9', '/', '5', '3', '9', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex41_lookup_physical_volume

theorem simplex41_lookup_mean_gap :
    rawSimplex41.getObjVal? "mean_gap" = .ok (.str (String.ofList ['7', '4', '9', '8', '9', '3', '/', '6', '4', '3', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex41_lookup_mean_gap

theorem simplex41_lookup_factor_maxima :
    rawSimplex41.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex41_lookup_factor_maxima

theorem simplex41_lookup_gap_weighted_means :
    rawSimplex41.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['8', '1', '2', '7', '1', '3', '8', '5', '6', '1', '0', '1', '9', '6', '1', '9', '/', '1', '0', '5', '5', '5', '9', '1', '5', '6', '8', '2', '8', '1', '2', '5', '0', '0', '0']), .str (String.ofList ['3', '3', '1', '7', '4', '3', '5', '6', '0', '2', '5', '5', '7', '4', '9', '0', '1', '/', '4', '2', '2', '2', '3', '6', '6', '2', '7', '3', '1', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '0', '3', '6', '3', '6', '9', '2', '3', '1', '4', '4', '3', '1', '8', '0', '6', '7', '/', '1', '0', '1', '3', '3', '6', '7', '9', '0', '5', '5', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '2', '0', '1', '1', '1', '5', '8', '9', '2', '7', '7', '3', '2', '0', '3', '7', '/', '2', '0', '2', '6', '7', '3', '5', '8', '1', '1', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '3', '0', '8', '9', '3', '4', '0', '2', '8', '5', '2', '2', '9', '3', '6', '9', '/', '1', '0', '1', '3', '3', '6', '7', '9', '0', '5', '5', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '3', '0', '8', '6', '4', '4', '2', '0', '9', '9', '6', '0', '1', '7', '1', '/', '1', '3', '5', '1', '1', '5', '7', '2', '0', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '8', '3', '0', '0', '9', '1', '1', '2', '8', '5', '5', '9', '2', '2', '1', '/', '5', '0', '6', '6', '8', '3', '9', '5', '2', '7', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '4', '7', '4', '4', '6', '1', '0', '0', '7', '5', '8', '2', '7', '9', '3', '/', '4', '0', '5', '3', '4', '7', '1', '6', '2', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '3', '1', '1', '7', '7', '6', '8', '0', '9', '6', '2', '4', '7', '8', '5', '7', '/', '2', '0', '2', '6', '7', '3', '5', '8', '1', '1', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '1', '0', '7', '7', '4', '9', '8', '4', '0', '5', '3', '3', '6', '7', '7', '/', '2', '5', '3', '3', '4', '1', '9', '7', '6', '3', '8', '7', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex41_lookup_gap_weighted_means

theorem simplex41_lookup_max_bound :
    rawSimplex41.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '6', '9', '9', '0', '5', '9', '8', '8', '7', '9', '2', '5', '4', '3', '7', '0', '9', '1', '7', '9', '8', '5', '6', '9', '4', '8', '1', '2', '1', '4', '8', '3', '5', '9', '9', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '3', '2', '6', '5', '8', '6', '1', '1', '2', '7', '3', '4', '0', '6', '2', '7', '1', '7', '3', '0', '7', '8', '6', '6', '2', '0', '4', '9', '9', '6', '2', '1', '9', '7', '1', '4', '3', '7', '9', '3', '6', '5', '3', '5', '4', '4', '1', '0', '8', '9', '2', '9', '9', '0', '8', '0', '5', '8', '3', '3', '4', '4', '1'])) := by
  rfl

attribute [local simp] simplex41_lookup_max_bound

theorem simplex41_lookup_jensen_bound :
    rawSimplex41.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '0', '7', '8', '8', '6', '7', '8', '8', '8', '0', '7', '3', '9', '6', '1', '7', '9', '0', '3', '8', '0', '8', '3', '8', '8', '9', '8', '3', '8', '0', '6', '8', '5', '2', '3', '6', '5', '3', '2', '2', '4', '1', '5', '4', '2', '4', '2', '1', '9', '5', '1', '7', '8', '3', '3', '6', '4', '4', '9', '4', '8', '2', '8', '7', '7', '5', '4', '9', '8', '0', '2', '0', '8', '7', '5', '5', '1', '3', '2', '0', '8', '6', '6', '5', '5', '8', '8', '8', '7', '1', '2', '9', '0', '7', '5', '3', '4', '5', '6', '2', '2', '5', '0', '1', '9', '1', '7', '7', '0', '6', '4', '0', '7', '0', '3', '2', '0', '4', '0', '5', '4', '3', '4', '5', '0', '1', '3', '5', '4', '2', '9', '9', '0', '6', '8', '4', '5', '0', '9', '2', '7', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '5', '2', '9', '3', '6', '8', '1', '6', '4', '1', '6', '6', '0', '6', '3', '2', '0', '6', '0', '8', '6', '9', '8', '2', '1', '2', '3', '1', '5', '0', '7', '9', '8', '1', '1', '1', '8', '9', '8', '3', '8', '3', '7', '8', '7', '5', '5', '9', '3', '3', '5', '5', '5', '1', '1', '9', '7', '9', '9', '4', '5', '4', '5', '5', '4', '4', '2', '6', '7', '1', '4', '5', '2', '2', '2', '1', '2', '8', '6', '8', '8', '4', '8', '9', '3', '6', '0', '8', '1', '0', '9', '7', '5', '8', '9', '5', '6', '6', '9', '7', '9', '7', '7', '0', '5', '3', '3', '2', '5', '9', '6', '9', '0', '7', '9', '0', '1', '9', '3', '5', '6', '4', '7', '4', '6', '5', '1', '0', '1', '5', '8', '7', '7', '1', '7', '6', '3', '7', '5', '5', '8', '8', '0', '0', '0', '1', '1', '5', '8', '6', '7', '8', '9', '7', '2', '1', '4', '5', '1', '9', '5', '3', '7', '5', '7', '5', '0', '8', '3'])) := by
  rfl

attribute [local simp] simplex41_lookup_jensen_bound

theorem simplex41_lookup_max_floor_Q96 :
    rawSimplex41.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '7', '0', '5', '6', '4', '3', '9', '1', '8', '8', '7', '1', '7', '5', '9', '3'])) := by
  rfl

attribute [local simp] simplex41_lookup_max_floor_Q96

theorem simplex41_lookup_jensen_floor_Q96 :
    rawSimplex41.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '4', '2', '1', '8', '7', '0', '3', '2', '8', '9', '6', '1', '3', '2', '7', '2', '8'])) := by
  rfl

attribute [local simp] simplex41_lookup_jensen_floor_Q96

theorem simplex41_decoded : decodeSimplex rawSimplex41 = .ok simplex41 := by
  unfold decodeSimplex simplex41
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
