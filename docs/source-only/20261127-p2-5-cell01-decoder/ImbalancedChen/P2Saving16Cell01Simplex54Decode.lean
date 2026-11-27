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

theorem simplex54_lookup_simplex_id :
    rawSimplex54.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5', '4'])) := by
  rfl

attribute [local simp] simplex54_lookup_simplex_id

theorem simplex54_lookup_vertex_ids :
    rawSimplex54.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex54_lookup_vertex_ids

theorem simplex54_lookup_physical_volume :
    rawSimplex54.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '0', '9', '6', '8', '8', '9', '3', '0', '3', '6', '8', '9', '6', '6', '4', '5', '3', '7', '9', '4', '4', '0', '7', '9', '2', '5', '3', '4', '5', '8', '5', '6', '5', '9', '/', '3', '3', '0', '6', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex54_lookup_physical_volume

theorem simplex54_lookup_mean_gap :
    rawSimplex54.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex54_lookup_mean_gap

theorem simplex54_lookup_factor_maxima :
    rawSimplex54.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex54_lookup_factor_maxima

theorem simplex54_lookup_gap_weighted_means :
    rawSimplex54.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '0', '2', '7', '1', '0', '2', '5', '9', '0', '7', '3', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '2', '8', '5', '0', '5', '7', '4', '7', '3', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '3', '1', '3', '1', '7', '6', '2', '7', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '9', '5', '0', '6', '3', '9', '0', '1', '7', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '2', '0', '9', '9', '7', '7', '1', '3', '3', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '4', '4', '1', '8', '3', '5', '6', '9', '3', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '1', '7', '4', '8', '0', '8', '7', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '7', '6', '7', '8', '7', '6', '5', '3', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '7', '5', '4', '0', '5', '8', '4', '2', '7', '1', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '1', '7', '2', '1', '8', '7', '8', '7', '3', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex54_lookup_gap_weighted_means

theorem simplex54_lookup_max_bound :
    rawSimplex54.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '5', '0', '7', '5', '4', '8', '4', '8', '5', '9', '4', '8', '1', '3', '5', '2', '3', '4', '8', '2', '6', '3', '1', '1', '7', '1', '6', '2', '0', '5', '1', '9', '4', '2', '5', '1', '4', '0', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '4', '1', '8', '4', '8', '9', '9', '2', '9', '5', '0', '5', '4', '3', '6', '3', '8', '3', '3', '6', '5', '9', '6', '4', '4', '5', '4', '4', '0', '5', '6', '0', '6', '0', '8', '3', '2', '3', '7', '0', '8', '1', '8', '0', '0', '2', '4', '6', '4', '8', '9', '8', '5', '6', '3', '2', '9', '0', '7', '0', '9', '7', '3'])) := by
  rfl

attribute [local simp] simplex54_lookup_max_bound

theorem simplex54_lookup_jensen_bound :
    rawSimplex54.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '9', '4', '9', '1', '0', '4', '6', '0', '9', '4', '0', '4', '0', '1', '4', '4', '5', '9', '1', '9', '9', '6', '8', '6', '8', '7', '0', '0', '8', '2', '6', '9', '8', '7', '3', '1', '5', '2', '7', '1', '0', '0', '5', '8', '4', '7', '0', '8', '5', '7', '9', '6', '5', '0', '4', '5', '8', '3', '9', '7', '5', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '7', '5', '2', '4', '6', '2', '8', '3', '6', '9', '3', '8', '9', '7', '9', '3', '2', '3', '0', '7', '6', '5', '1', '8', '0', '0', '7', '7', '8', '7', '5', '3', '0', '0', '5', '7', '3', '0', '9', '1', '1', '0', '7', '7', '0', '8', '4', '8', '2', '8', '6', '6', '9', '6', '7', '4', '8', '3', '1', '7', '0', '0', '7', '2', '3', '5', '7', '8', '4', '0', '3', '5', '3', '4', '7', '4', '7', '9', '3', '1', '8', '7', '0', '2', '9', '3', '5', '2', '0', '4', '9', '9', '4', '3', '6', '1', '8', '7', '2', '5', '2', '3', '4', '6', '3'])) := by
  rfl

attribute [local simp] simplex54_lookup_jensen_bound

theorem simplex54_lookup_max_floor_Q96 :
    rawSimplex54.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '0', '8', '3', '3', '7', '1', '7', '3', '2', '5', '0', '3', '8', '2', '2', '4'])) := by
  rfl

attribute [local simp] simplex54_lookup_max_floor_Q96

theorem simplex54_lookup_jensen_floor_Q96 :
    rawSimplex54.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '3', '9', '4', '7', '3', '3', '0', '7', '0', '2', '3', '3', '8', '7', '1', '2', '1'])) := by
  rfl

attribute [local simp] simplex54_lookup_jensen_floor_Q96

theorem simplex54_decoded : decodeSimplex rawSimplex54 = .ok simplex54 := by
  unfold decodeSimplex simplex54
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
