import ImbalancedChen.P2Saving16Cell03FieldSimp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell03 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell03FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell03TypedPayload
open P2Saving16Cell03ScalarDecode
open scoped ImbalancedChen.P2Saving16Cell03FieldDecode

theorem simplex07_lookup_simplex_id :
    rawSimplex07.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7'])) := by
  rfl

attribute [local simp] simplex07_lookup_simplex_id

theorem simplex07_lookup_vertex_ids :
    rawSimplex07.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['2', '0']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '8']), .number (String.ofList ['1', '7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex07_lookup_vertex_ids

theorem simplex07_lookup_physical_volume :
    rawSimplex07.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '7', '7', '5', '6', '7', '9', '9', '4', '8', '7', '3', '2', '0', '1', '7', '3', '1', '8', '8', '6', '7', '2', '6', '5', '6', '1', '3', '9', '6', '9', '7', '5', '0', '3', '3', '9', '8', '1', '7', '8', '3', '4', '5', '9', '4', '1', '/', '3', '4', '0', '7', '4', '8', '1', '6', '9', '0', '4', '4', '3', '5', '5', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_physical_volume

theorem simplex07_lookup_mean_gap :
    rawSimplex07.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '1', '6', '7', '/', '1', '9', '3', '9', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_mean_gap

theorem simplex07_lookup_factor_maxima :
    rawSimplex07.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '5', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '5', '9', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '0', '7', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '4', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '1', '7', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '8', '0', '7', '3', '/', '2', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_factor_maxima

theorem simplex07_lookup_gap_weighted_means :
    rawSimplex07.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '3', '6', '6', '9', '9', '6', '7', '8', '0', '2', '4', '3', '1', '1', '9', '3', '/', '4', '0', '2', '5', '2', '5', '1', '2', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '7', '5', '7', '4', '4', '6', '3', '1', '7', '9', '5', '5', '5', '9', '3', '/', '4', '0', '2', '5', '2', '5', '1', '2', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '3', '2', '5', '6', '0', '9', '0', '5', '9', '3', '9', '4', '1', '0', '1', '/', '6', '0', '3', '7', '8', '7', '6', '8', '4', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '2', '3', '7', '1', '6', '9', '4', '1', '8', '2', '4', '7', '7', '7', '/', '1', '2', '0', '7', '5', '7', '5', '3', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '0', '1', '2', '7', '3', '8', '7', '2', '8', '1', '1', '5', '1', '7', '/', '3', '0', '1', '8', '9', '3', '8', '4', '2', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '7', '1', '2', '3', '0', '0', '2', '7', '8', '8', '9', '4', '5', '1', '1', '/', '4', '8', '3', '0', '3', '0', '1', '4', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '4', '4', '2', '3', '4', '0', '6', '7', '8', '4', '8', '4', '4', '9', '/', '5', '3', '6', '7', '0', '0', '1', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '6', '2', '8', '6', '4', '4', '3', '6', '7', '6', '6', '3', '5', '0', '3', '/', '2', '4', '1', '5', '1', '5', '0', '7', '3', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '7', '6', '6', '1', '8', '9', '4', '3', '6', '4', '0', '7', '3', '5', '1', '/', '1', '2', '0', '7', '5', '7', '5', '3', '6', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '1', '8', '7', '2', '0', '1', '0', '2', '6', '3', '8', '0', '3', '/', '7', '5', '4', '7', '3', '4', '6', '0', '5', '6', '2', '5', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_gap_weighted_means

theorem simplex07_lookup_max_bound :
    rawSimplex07.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '3', '5', '1', '9', '4', '3', '1', '0', '4', '8', '3', '3', '8', '3', '9', '0', '2', '2', '9', '7', '4', '9', '5', '7', '2', '5', '3', '0', '1', '5', '0', '2', '5', '4', '1', '7', '8', '7', '4', '1', '7', '5', '5', '7', '6', '6', '6', '4', '9', '5', '8', '5', '7', '6', '0', '0', '0', '0', '/', '5', '5', '1', '5', '6', '2', '8', '1', '1', '5', '5', '9', '9', '8', '4', '7', '6', '7', '7', '8', '9', '0', '1', '8', '2', '2', '8', '4', '6', '3', '3', '1', '2', '6', '5', '1', '8', '8', '6', '8', '2', '6', '2', '0', '7', '1', '9', '8', '2', '1', '9', '7', '9', '3', '0', '3', '7', '3', '0', '2', '4', '0', '0', '3', '4', '7', '3', '1', '2', '0', '8', '8', '3'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_bound

theorem simplex07_lookup_jensen_bound :
    rawSimplex07.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '6', '6', '8', '7', '5', '0', '3', '7', '1', '3', '9', '4', '5', '9', '5', '5', '7', '3', '6', '1', '0', '9', '9', '3', '3', '3', '6', '2', '6', '6', '1', '3', '8', '3', '0', '7', '5', '8', '9', '4', '8', '8', '2', '2', '6', '5', '0', '5', '8', '9', '9', '1', '8', '7', '9', '9', '5', '1', '0', '8', '4', '7', '6', '5', '3', '9', '0', '9', '8', '1', '6', '6', '3', '3', '4', '5', '6', '1', '4', '1', '1', '9', '3', '2', '7', '1', '5', '0', '8', '2', '6', '3', '1', '9', '8', '8', '8', '9', '4', '5', '7', '1', '2', '6', '7', '7', '2', '5', '4', '6', '0', '0', '2', '2', '7', '6', '4', '2', '9', '9', '4', '0', '4', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '1', '3', '5', '2', '6', '1', '0', '1', '4', '7', '3', '2', '6', '1', '1', '3', '4', '1', '5', '9', '7', '5', '7', '5', '3', '2', '7', '9', '0', '5', '4', '4', '1', '9', '4', '1', '8', '5', '3', '2', '3', '9', '6', '2', '0', '9', '8', '2', '9', '5', '8', '7', '6', '6', '2', '2', '3', '2', '1', '5', '6', '2', '5', '1', '3', '3', '8', '5', '7', '9', '1', '4', '3', '5', '4', '3', '8', '7', '3', '3', '9', '6', '9', '6', '6', '7', '2', '0', '2', '1', '4', '8', '8', '1', '3', '6', '7', '1', '6', '5', '5', '9', '7', '0', '2', '7', '5', '7', '3', '7', '5', '7', '7', '9', '6', '2', '1', '9', '4', '4', '6', '6', '5', '4', '1', '7', '4', '1', '7', '6', '2', '8', '1', '6', '8', '9', '4', '0', '5', '9', '6', '5', '0', '9', '0', '4', '0', '4', '8', '0', '5', '9', '8', '6', '2', '1', '4', '4', '7'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_bound

theorem simplex07_lookup_max_floor_Q96 :
    rawSimplex07.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '9', '4', '1', '9', '7', '2', '2', '6', '0', '9', '0', '8', '4', '1'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_floor_Q96

theorem simplex07_lookup_jensen_floor_Q96 :
    rawSimplex07.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '3', '9', '7', '0', '0', '3', '9', '0', '9', '8', '0', '3', '9', '9', '4'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_floor_Q96

theorem simplex07_decoded : decodeSimplex rawSimplex07 = .ok simplex07 := by
  unfold decodeSimplex simplex07
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
