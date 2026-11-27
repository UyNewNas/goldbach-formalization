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

theorem simplex24_lookup_simplex_id :
    rawSimplex24.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2', '4'])) := by
  rfl

attribute [local simp] simplex24_lookup_simplex_id

theorem simplex24_lookup_vertex_ids :
    rawSimplex24.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex24_lookup_vertex_ids

theorem simplex24_lookup_physical_volume :
    rawSimplex24.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '5', '5', '7', '0', '9', '3', '6', '0', '7', '1', '6', '4', '4', '7', '2', '2', '1', '1', '3', '3', '0', '9', '8', '9', '4', '9', '7', '3', '5', '1', '2', '9', '/', '2', '1', '3', '9', '8', '3', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex24_lookup_physical_volume

theorem simplex24_lookup_mean_gap :
    rawSimplex24.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '0', '8', '3', '/', '3', '9', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex24_lookup_mean_gap

theorem simplex24_lookup_factor_maxima :
    rawSimplex24.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex24_lookup_factor_maxima

theorem simplex24_lookup_gap_weighted_means :
    rawSimplex24.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['4', '8', '6', '7', '1', '6', '9', '3', '9', '/', '6', '3', '9', '8', '4', '3', '7', '5', '0', '0']), .str (String.ofList ['3', '9', '4', '2', '9', '4', '6', '3', '8', '7', '/', '5', '1', '1', '8', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '7', '1', '6', '1', '0', '0', '1', '8', '2', '9', '/', '1', '2', '2', '8', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '0', '4', '7', '0', '9', '6', '3', '7', '9', '/', '2', '4', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '6', '2', '2', '0', '6', '5', '6', '3', '/', '1', '2', '2', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '2', '9', '1', '2', '8', '7', '4', '7', '/', '2', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '7', '1', '1', '6', '1', '4', '2', '8', '1', '/', '4', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '5', '1', '5', '0', '7', '5', '3', '9', '1', '/', '4', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '2', '0', '8', '4', '2', '4', '3', '5', '9', '/', '2', '4', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '9', '9', '1', '3', '9', '8', '9', '9', '/', '3', '0', '7', '1', '2', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex24_lookup_gap_weighted_means

theorem simplex24_lookup_max_bound :
    rawSimplex24.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '0', '3', '7', '8', '9', '6', '3', '1', '4', '7', '9', '1', '5', '5', '0', '5', '9', '7', '1', '8', '4', '7', '8', '4', '3', '5', '9', '3', '5', '4', '4', '7', '5', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '7', '5', '1', '2', '0', '4', '7', '1', '6', '1', '6', '9', '3', '5', '9', '6', '0', '7', '3', '9', '7', '6', '1', '2', '8', '4', '8', '5', '3', '2', '1', '4', '0', '5', '4', '1', '9', '5', '1', '0', '4', '7', '7', '0', '6', '6', '1', '4', '9', '6', '8', '7', '6', '0', '0', '0', '0', '0', '8', '2', '4', '1', '6', '0', '7'])) := by
  rfl

attribute [local simp] simplex24_lookup_max_bound

theorem simplex24_lookup_jensen_bound :
    rawSimplex24.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['9', '3', '9', '2', '1', '8', '3', '1', '2', '0', '2', '5', '0', '5', '8', '3', '3', '0', '0', '6', '1', '1', '8', '9', '5', '6', '5', '2', '1', '0', '6', '7', '1', '6', '5', '1', '1', '7', '7', '9', '2', '7', '9', '5', '8', '4', '4', '1', '3', '9', '8', '1', '2', '4', '6', '4', '9', '8', '1', '5', '5', '5', '9', '3', '8', '7', '2', '0', '7', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '0', '2', '9', '1', '9', '4', '0', '9', '5', '2', '1', '7', '0', '4', '1', '1', '2', '5', '5', '2', '1', '7', '2', '7', '1', '7', '9', '9', '6', '2', '5', '9', '2', '7', '8', '8', '9', '4', '1', '1', '2', '0', '7', '0', '0', '7', '5', '6', '5', '8', '3', '7', '7', '7', '6', '4', '7', '0', '6', '6', '3', '5', '4', '3', '0', '5', '9', '9', '5', '4', '3', '0', '6', '0', '3', '3', '5', '8', '3', '4', '2', '0', '7', '1', '4', '4', '9', '1', '3', '7', '6', '7', '4', '2', '4', '4', '9', '7', '3'])) := by
  rfl

attribute [local simp] simplex24_lookup_jensen_bound

theorem simplex24_lookup_max_floor_Q96 :
    rawSimplex24.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '4', '4', '8', '8', '5', '0', '8', '9', '1', '4', '7', '5'])) := by
  rfl

attribute [local simp] simplex24_lookup_max_floor_Q96

theorem simplex24_lookup_jensen_floor_Q96 :
    rawSimplex24.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '6', '4', '2', '3', '1', '3', '3', '0', '7', '7', '9', '7', '4'])) := by
  rfl

attribute [local simp] simplex24_lookup_jensen_floor_Q96

theorem simplex24_decoded : decodeSimplex rawSimplex24 = .ok simplex24 := by
  unfold decodeSimplex simplex24
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
