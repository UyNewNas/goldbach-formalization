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

theorem simplex48_lookup_simplex_id :
    rawSimplex48.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '8'])) := by
  rfl

attribute [local simp] simplex48_lookup_simplex_id

theorem simplex48_lookup_vertex_ids :
    rawSimplex48.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '7']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '2']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex48_lookup_vertex_ids

theorem simplex48_lookup_physical_volume :
    rawSimplex48.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '4', '5', '6', '9', '8', '3', '2', '0', '2', '6', '0', '7', '4', '4', '2', '4', '1', '4', '1', '2', '8', '9', '9', '3', '8', '8', '5', '5', '7', '5', '9', '/', '7', '4', '5', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex48_lookup_physical_volume

theorem simplex48_lookup_mean_gap :
    rawSimplex48.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '0', '8', '3', '/', '3', '9', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex48_lookup_mean_gap

theorem simplex48_lookup_factor_maxima :
    rawSimplex48.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '8', '6', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex48_lookup_factor_maxima

theorem simplex48_lookup_gap_weighted_means :
    rawSimplex48.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '8', '1', '5', '0', '8', '9', '7', '8', '6', '7', '/', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '0', '0', '8', '4', '1', '8', '6', '7', '/', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '6', '8', '1', '0', '0', '0', '7', '3', '3', '/', '1', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '9', '5', '8', '2', '8', '5', '1', '9', '/', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '6', '9', '6', '5', '0', '4', '5', '7', '/', '1', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '0', '7', '2', '6', '8', '0', '7', '/', '1', '3', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '8', '8', '0', '4', '1', '8', '9', '/', '2', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '4', '9', '5', '8', '9', '5', '3', '/', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '2', '2', '1', '2', '6', '6', '1', '1', '9', '/', '1', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '2', '5', '9', '0', '5', '3', '8', '6', '7', '/', '1', '0', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex48_lookup_gap_weighted_means

theorem simplex48_lookup_max_bound :
    rawSimplex48.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '4', '8', '5', '8', '9', '0', '5', '2', '5', '0', '4', '4', '3', '5', '0', '4', '2', '8', '0', '9', '5', '2', '4', '3', '1', '1', '5', '4', '5', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '8', '0', '6', '1', '7', '6', '2', '2', '6', '6', '7', '4', '1', '4', '6', '1', '4', '3', '9', '1', '7', '1', '2', '3', '7', '6', '2', '7', '5', '7', '3', '2', '6', '1', '0', '3', '3', '1', '0', '8', '4', '7', '5', '6', '4', '6', '1', '3', '5', '3', '4', '5', '7', '7', '4', '3'])) := by
  rfl

attribute [local simp] simplex48_lookup_max_bound

theorem simplex48_lookup_jensen_bound :
    rawSimplex48.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '2', '3', '2', '9', '8', '3', '2', '9', '8', '2', '5', '9', '3', '7', '2', '0', '4', '5', '9', '6', '0', '8', '3', '9', '9', '5', '7', '8', '7', '8', '5', '7', '9', '6', '6', '9', '2', '9', '0', '2', '7', '1', '9', '5', '0', '2', '4', '0', '6', '6', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '6', '4', '2', '0', '2', '9', '2', '0', '4', '4', '6', '7', '3', '7', '5', '7', '6', '6', '1', '2', '1', '8', '5', '5', '3', '3', '4', '3', '3', '0', '9', '6', '1', '3', '5', '0', '2', '3', '9', '1', '9', '3', '7', '1', '4', '1', '2', '0', '9', '3', '4', '5', '2', '9', '5', '9', '1', '4', '1', '1', '9', '6', '8', '0', '9', '4', '3', '5', '1', '1', '3', '0', '0', '2', '9', '4', '3', '4', '9', '2', '8', '1', '8', '9', '8', '3', '1', '6', '0', '0', '0', '8', '5', '8', '4', '0', '7'])) := by
  rfl

attribute [local simp] simplex48_lookup_jensen_bound

theorem simplex48_lookup_max_floor_Q96 :
    rawSimplex48.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '5', '5', '2', '9', '1', '8', '7', '8', '1', '4', '7', '6', '6', '4', '8', '7'])) := by
  rfl

attribute [local simp] simplex48_lookup_max_floor_Q96

theorem simplex48_lookup_jensen_floor_Q96 :
    rawSimplex48.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '0', '4', '7', '1', '4', '8', '4', '1', '2', '2', '5', '8', '0', '5', '7', '5', '3'])) := by
  rfl

attribute [local simp] simplex48_lookup_jensen_floor_Q96

theorem simplex48_decoded : decodeSimplex rawSimplex48 = .ok simplex48 := by
  unfold decodeSimplex simplex48
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
