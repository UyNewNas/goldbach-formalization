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

theorem simplex76_lookup_simplex_id :
    rawSimplex76.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '6'])) := by
  rfl

attribute [local simp] simplex76_lookup_simplex_id

theorem simplex76_lookup_vertex_ids :
    rawSimplex76.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex76_lookup_vertex_ids

theorem simplex76_lookup_physical_volume :
    rawSimplex76.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '0', '0', '9', '6', '1', '6', '1', '2', '7', '2', '4', '0', '1', '6', '2', '2', '8', '7', '0', '8', '9', '6', '7', '2', '5', '3', '0', '6', '1', '/', '5', '2', '3', '9', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex76_lookup_physical_volume

theorem simplex76_lookup_mean_gap :
    rawSimplex76.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex76_lookup_mean_gap

theorem simplex76_lookup_factor_maxima :
    rawSimplex76.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '2', '1', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex76_lookup_factor_maxima

theorem simplex76_lookup_gap_weighted_means :
    rawSimplex76.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '8', '0', '7', '6', '1', '1', '8', '7', '8', '3', '/', '2', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '3', '8', '5', '8', '5', '1', '8', '3', '/', '2', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '3', '1', '5', '2', '7', '6', '4', '6', '7', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '7', '3', '3', '8', '0', '0', '9', '/', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '3', '0', '1', '9', '7', '9', '/', '1', '9', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '2', '2', '3', '2', '3', '1', '/', '9', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '8', '7', '8', '0', '6', '9', '/', '3', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '9', '7', '4', '1', '2', '8', '3', '/', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '1', '9', '0', '1', '1', '1', '1', '/', '1', '1', '5', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '1', '9', '7', '5', '8', '1', '8', '3', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex76_lookup_gap_weighted_means

theorem simplex76_lookup_max_bound :
    rawSimplex76.getObjVal? "max_bound" = .ok (.str (String.ofList ['6', '4', '6', '0', '7', '1', '6', '1', '3', '6', '8', '0', '5', '6', '0', '3', '4', '9', '6', '4', '2', '8', '3', '2', '0', '3', '3', '6', '1', '6', '6', '9', '2', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '6', '2', '6', '9', '6', '7', '0', '0', '5', '2', '8', '1', '3', '6', '1', '8', '2', '1', '9', '9', '8', '0', '0', '4', '3', '7', '2', '6', '9', '2', '3', '9', '8', '3', '9', '2', '6', '2', '5', '0', '9', '2', '2', '4', '2', '4', '1', '7', '3', '1', '4', '0', '5', '6', '2', '1', '0', '2', '8', '0', '6', '2', '9', '7'])) := by
  rfl

attribute [local simp] simplex76_lookup_max_bound

theorem simplex76_lookup_jensen_bound :
    rawSimplex76.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '5', '8', '3', '0', '0', '6', '6', '4', '5', '4', '8', '9', '1', '5', '0', '3', '4', '0', '0', '0', '8', '3', '6', '2', '7', '3', '5', '5', '6', '9', '7', '3', '9', '4', '3', '6', '6', '8', '2', '8', '3', '4', '8', '8', '0', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '0', '2', '3', '0', '1', '9', '5', '7', '5', '6', '1', '8', '0', '0', '5', '5', '9', '1', '3', '5', '3', '1', '4', '3', '9', '7', '0', '1', '5', '4', '4', '9', '2', '0', '4', '0', '0', '0', '9', '6', '9', '3', '3', '9', '5', '9', '3', '0', '1', '1', '8', '0', '2', '8', '9', '6', '8', '5', '4', '5', '3', '4', '0', '9', '0', '8', '8', '0', '5', '5', '2', '6', '1', '2', '8', '0', '1', '8', '3', '5', '5', '4', '6', '4', '4', '2', '1', '4', '2', '4', '9'])) := by
  rfl

attribute [local simp] simplex76_lookup_jensen_bound

theorem simplex76_lookup_max_floor_Q96 :
    rawSimplex76.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '1', '4', '6', '1', '6', '5', '0', '1', '9', '8', '4', '2'])) := by
  rfl

attribute [local simp] simplex76_lookup_max_floor_Q96

theorem simplex76_lookup_jensen_floor_Q96 :
    rawSimplex76.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '4', '0', '3', '2', '2', '4', '3', '4', '9', '4', '8', '1', '5'])) := by
  rfl

attribute [local simp] simplex76_lookup_jensen_floor_Q96

theorem simplex76_decoded : decodeSimplex rawSimplex76 = .ok simplex76 := by
  unfold decodeSimplex simplex76
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
