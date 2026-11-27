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

theorem simplex21_lookup_simplex_id :
    rawSimplex21.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2', '1'])) := by
  rfl

attribute [local simp] simplex21_lookup_simplex_id

theorem simplex21_lookup_vertex_ids :
    rawSimplex21.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['6']), .number (String.ofList ['3']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex21_lookup_vertex_ids

theorem simplex21_lookup_physical_volume :
    rawSimplex21.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '2', '9', '6', '8', '6', '5', '1', '5', '3', '8', '9', '9', '3', '4', '3', '3', '7', '4', '9', '1', '2', '7', '7', '4', '9', '9', '4', '3', '9', '3', '3', '3', '8', '6', '6', '2', '5', '4', '5', '0', '7', '9', '/', '1', '0', '9', '2', '2', '2', '2', '3', '0', '4', '9', '1', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex21_lookup_physical_volume

theorem simplex21_lookup_mean_gap :
    rawSimplex21.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex21_lookup_mean_gap

theorem simplex21_lookup_factor_maxima :
    rawSimplex21.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex21_lookup_factor_maxima

theorem simplex21_lookup_gap_weighted_means :
    rawSimplex21.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '8', '8', '9', '6', '8', '4', '7', '7', '7', '3', '1', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '9', '0', '5', '3', '9', '4', '5', '5', '7', '/', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '5', '3', '8', '3', '5', '3', '7', '2', '3', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '7', '0', '6', '7', '6', '2', '0', '9', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '4', '6', '2', '4', '7', '9', '9', '4', '3', '/', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '4', '1', '8', '1', '9', '1', '9', '7', '/', '1', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '8', '1', '4', '3', '3', '4', '2', '1', '3', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '3', '5', '2', '3', '1', '8', '0', '5', '3', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '0', '1', '8', '8', '3', '2', '7', '4', '9', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '3', '0', '1', '7', '2', '1', '8', '7', '7', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex21_lookup_gap_weighted_means

theorem simplex21_lookup_max_bound :
    rawSimplex21.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '0', '3', '6', '4', '1', '4', '7', '7', '6', '9', '6', '7', '2', '9', '1', '9', '9', '7', '0', '4', '1', '1', '1', '5', '0', '7', '3', '4', '2', '8', '5', '1', '0', '1', '1', '2', '8', '9', '2', '6', '3', '9', '6', '6', '0', '0', '9', '1', '4', '0', '6', '2', '5', '/', '2', '8', '4', '5', '1', '1', '7', '3', '4', '3', '2', '7', '2', '2', '7', '8', '4', '2', '1', '9', '0', '9', '0', '6', '8', '4', '4', '9', '8', '4', '7', '0', '3', '1', '9', '5', '4', '2', '1', '3', '4', '7', '1', '2', '4', '0', '7', '6', '4', '7', '7', '8', '8', '1', '8', '6', '2', '0', '9', '7', '7', '8', '0', '3', '4', '4', '8', '3', '2'])) := by
  rfl

attribute [local simp] simplex21_lookup_max_bound

theorem simplex21_lookup_jensen_bound :
    rawSimplex21.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '1', '4', '9', '3', '9', '7', '6', '4', '1', '6', '0', '4', '3', '6', '2', '2', '0', '9', '2', '7', '1', '1', '5', '6', '7', '9', '0', '8', '8', '7', '6', '5', '2', '6', '0', '8', '1', '2', '0', '7', '7', '1', '5', '7', '3', '9', '4', '9', '3', '3', '1', '5', '4', '2', '8', '6', '9', '5', '4', '0', '0', '7', '7', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '7', '2', '3', '3', '8', '3', '5', '0', '2', '5', '5', '4', '3', '0', '0', '6', '1', '4', '9', '4', '6', '9', '7', '0', '2', '8', '1', '6', '2', '5', '0', '2', '6', '9', '8', '3', '5', '7', '4', '0', '9', '9', '6', '9', '7', '7', '5', '8', '3', '4', '8', '7', '1', '8', '3', '9', '7', '0', '8', '3', '6', '8', '5', '8', '1', '8', '9', '4', '5', '3', '6', '4', '8', '7', '7', '3', '9', '2', '2', '9', '1', '6', '1', '4', '2', '0', '4', '1', '7', '0', '7', '5', '2', '0', '5', '9', '2', '4', '4', '6', '8', '7', '3', '5', '3', '3', '3'])) := by
  rfl

attribute [local simp] simplex21_lookup_jensen_bound

theorem simplex21_lookup_max_floor_Q96 :
    rawSimplex21.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '1', '2', '4', '0', '2', '2', '9', '7', '4', '5', '9', '1', '0', '2'])) := by
  rfl

attribute [local simp] simplex21_lookup_max_floor_Q96

theorem simplex21_lookup_jensen_floor_Q96 :
    rawSimplex21.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '2', '0', '7', '1', '3', '4', '9', '8', '6', '2', '2', '9', '4', '3', '4'])) := by
  rfl

attribute [local simp] simplex21_lookup_jensen_floor_Q96

theorem simplex21_decoded : decodeSimplex rawSimplex21 = .ok simplex21 := by
  unfold decodeSimplex simplex21
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
