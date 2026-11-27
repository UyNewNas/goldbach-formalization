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

theorem simplex14_lookup_simplex_id :
    rawSimplex14.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1', '4'])) := by
  rfl

attribute [local simp] simplex14_lookup_simplex_id

theorem simplex14_lookup_vertex_ids :
    rawSimplex14.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex14_lookup_vertex_ids

theorem simplex14_lookup_physical_volume :
    rawSimplex14.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '2', '2', '8', '0', '0', '4', '0', '3', '5', '0', '9', '2', '3', '6', '6', '5', '1', '8', '9', '0', '2', '9', '1', '2', '0', '1', '9', '9', '0', '5', '7', '2', '1', '2', '9', '7', '6', '5', '3', '6', '5', '3', '0', '3', '7', '/', '1', '0', '4', '2', '3', '2', '5', '7', '2', '1', '7', '3', '5', '6', '7', '9', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex14_lookup_physical_volume

theorem simplex14_lookup_mean_gap :
    rawSimplex14.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '6', '1', '1', '/', '7', '4', '1', '6', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex14_lookup_mean_gap

theorem simplex14_lookup_factor_maxima :
    rawSimplex14.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '0', '7', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '2', '5', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '2', '9', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '2', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex14_lookup_factor_maxima

theorem simplex14_lookup_gap_weighted_means :
    rawSimplex14.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '9', '8', '8', '9', '0', '9', '7', '6', '1', '5', '3', '9', '3', '6', '1', '/', '2', '8', '8', '5', '8', '5', '2', '9', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '3', '3', '6', '2', '5', '9', '0', '9', '6', '5', '9', '6', '6', '7', '/', '5', '7', '7', '1', '7', '0', '5', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '4', '5', '4', '3', '4', '2', '8', '4', '8', '3', '8', '6', '9', '7', '/', '8', '6', '5', '7', '5', '5', '8', '9', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '9', '0', '7', '1', '2', '1', '0', '9', '2', '2', '7', '9', '4', '0', '3', '/', '1', '7', '3', '1', '5', '1', '1', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '6', '0', '1', '6', '1', '6', '0', '9', '2', '3', '2', '7', '5', '7', '/', '1', '7', '3', '1', '5', '1', '1', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '2', '5', '3', '5', '0', '2', '6', '1', '9', '5', '8', '5', '1', '7', '/', '3', '4', '6', '3', '0', '2', '3', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '3', '4', '9', '3', '3', '4', '6', '9', '3', '4', '0', '5', '6', '2', '9', '/', '1', '1', '5', '4', '3', '4', '1', '1', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '3', '3', '7', '7', '0', '9', '5', '5', '1', '9', '4', '5', '1', '/', '1', '7', '3', '1', '5', '1', '1', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '3', '3', '5', '4', '0', '0', '8', '6', '9', '5', '6', '9', '1', '/', '1', '7', '3', '1', '5', '1', '1', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '4', '2', '0', '6', '4', '7', '9', '0', '9', '4', '5', '4', '9', '/', '4', '3', '2', '8', '7', '7', '9', '4', '5', '5', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex14_lookup_gap_weighted_means

theorem simplex14_lookup_max_bound :
    rawSimplex14.getObjVal? "max_bound" = .ok (.str (String.ofList ['3', '8', '2', '1', '7', '8', '9', '3', '6', '1', '1', '2', '3', '7', '0', '1', '0', '0', '0', '5', '7', '2', '9', '2', '8', '3', '2', '3', '8', '5', '0', '5', '0', '8', '0', '6', '5', '8', '3', '3', '8', '8', '0', '0', '2', '2', '1', '6', '9', '2', '2', '4', '2', '1', '8', '7', '5', '/', '4', '5', '8', '1', '4', '8', '2', '2', '3', '9', '6', '5', '8', '8', '5', '2', '5', '2', '7', '7', '4', '6', '6', '6', '2', '0', '3', '4', '8', '4', '6', '5', '2', '4', '7', '4', '2', '3', '4', '6', '9', '4', '0', '1', '9', '7', '0', '7', '3', '2', '8', '7', '0', '6', '2', '1', '1', '0', '6', '5', '5', '1', '8', '1', '9', '1', '6', '7', '8', '8', '3', '2'])) := by
  rfl

attribute [local simp] simplex14_lookup_max_bound

theorem simplex14_lookup_jensen_bound :
    rawSimplex14.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '3', '8', '4', '8', '7', '4', '5', '3', '6', '4', '5', '5', '0', '9', '8', '3', '2', '1', '4', '6', '7', '6', '8', '1', '7', '2', '3', '9', '0', '5', '4', '3', '5', '4', '4', '1', '1', '4', '7', '4', '1', '7', '9', '6', '1', '3', '4', '0', '6', '6', '9', '4', '1', '0', '4', '5', '6', '5', '9', '7', '9', '5', '4', '6', '3', '9', '1', '1', '9', '4', '6', '1', '2', '2', '2', '1', '8', '7', '6', '4', '8', '0', '7', '5', '4', '1', '2', '2', '8', '7', '0', '9', '6', '9', '8', '4', '7', '9', '1', '7', '7', '5', '0', '4', '1', '5', '1', '4', '3', '7', '0', '1', '3', '6', '6', '4', '2', '4', '9', '7', '9', '9', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '3', '6', '8', '9', '0', '2', '0', '6', '7', '9', '1', '1', '1', '6', '6', '2', '1', '4', '0', '9', '9', '4', '3', '3', '4', '1', '7', '7', '2', '3', '7', '8', '8', '6', '5', '0', '8', '9', '7', '5', '3', '3', '1', '1', '2', '8', '8', '7', '6', '8', '6', '2', '4', '8', '7', '1', '7', '1', '9', '4', '3', '2', '1', '3', '8', '1', '9', '0', '0', '4', '1', '3', '1', '2', '5', '5', '9', '3', '7', '2', '6', '3', '2', '6', '1', '7', '5', '0', '3', '4', '6', '5', '9', '9', '0', '9', '7', '4', '5', '9', '9', '8', '4', '7', '2', '2', '0', '1', '9', '3', '9', '5', '6', '6', '0', '4', '5', '1', '7', '1', '0', '3', '7', '5', '5', '4', '4', '4', '4', '2', '0', '7', '4', '1', '4', '1', '9', '7', '7', '7', '4', '3', '8', '9', '1', '8', '9', '1', '2', '2', '6', '9', '2', '3', '3'])) := by
  rfl

attribute [local simp] simplex14_lookup_jensen_bound

theorem simplex14_lookup_max_floor_Q96 :
    rawSimplex14.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '6', '0', '9', '0', '6', '9', '5', '7', '0', '9', '1', '9', '9'])) := by
  rfl

attribute [local simp] simplex14_lookup_max_floor_Q96

theorem simplex14_lookup_jensen_floor_Q96 :
    rawSimplex14.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['8', '2', '0', '7', '1', '8', '5', '9', '2', '1', '3', '8', '4', '6', '7'])) := by
  rfl

attribute [local simp] simplex14_lookup_jensen_floor_Q96

theorem simplex14_decoded : decodeSimplex rawSimplex14 = .ok simplex14 := by
  unfold decodeSimplex simplex14
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
