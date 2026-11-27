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

theorem simplex26_lookup_simplex_id :
    rawSimplex26.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2', '6'])) := by
  rfl

attribute [local simp] simplex26_lookup_simplex_id

theorem simplex26_lookup_vertex_ids :
    rawSimplex26.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex26_lookup_vertex_ids

theorem simplex26_lookup_physical_volume :
    rawSimplex26.getObjVal? "physical_volume" = .ok (.str (String.ofList ['8', '5', '3', '1', '9', '2', '1', '2', '3', '7', '2', '3', '4', '7', '9', '4', '1', '1', '1', '7', '8', '6', '4', '6', '8', '6', '4', '7', '8', '0', '9', '7', '1', '/', '1', '2', '6', '9', '7', '8', '9', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex26_lookup_physical_volume

theorem simplex26_lookup_mean_gap :
    rawSimplex26.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex26_lookup_mean_gap

theorem simplex26_lookup_factor_maxima :
    rawSimplex26.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex26_lookup_factor_maxima

theorem simplex26_lookup_gap_weighted_means :
    rawSimplex26.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '0', '5', '4', '5', '3', '4', '3', '4', '1', '2', '3', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '7', '0', '2', '8', '2', '3', '2', '5', '2', '3', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '9', '2', '7', '0', '9', '2', '6', '5', '2', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '7', '6', '6', '1', '8', '6', '9', '7', '6', '7', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '5', '5', '8', '5', '3', '5', '7', '5', '2', '3', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '1', '9', '9', '0', '6', '3', '9', '6', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '3', '8', '7', '6', '9', '8', '5', '1', '/', '3', '4', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '1', '4', '7', '0', '4', '6', '3', '2', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '2', '7', '0', '3', '6', '5', '6', '0', '2', '1', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '9', '9', '1', '5', '2', '7', '0', '5', '2', '3', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex26_lookup_gap_weighted_means

theorem simplex26_lookup_max_bound :
    rawSimplex26.getObjVal? "max_bound" = .ok (.str (String.ofList ['8', '5', '3', '0', '8', '2', '9', '1', '5', '1', '3', '1', '6', '4', '2', '8', '0', '5', '8', '1', '4', '0', '1', '5', '9', '9', '7', '9', '8', '2', '2', '7', '9', '0', '3', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '9', '6', '0', '3', '7', '6', '1', '8', '1', '8', '3', '8', '3', '6', '8', '3', '0', '1', '3', '9', '1', '9', '2', '2', '0', '1', '6', '9', '2', '7', '4', '1', '5', '2', '4', '5', '0', '3', '6', '2', '3', '1', '8', '8', '0', '4', '0', '3', '8', '2', '4', '1', '3', '5', '7', '3', '4', '3', '8', '1', '7', '4', '1', '1', '7', '1'])) := by
  rfl

attribute [local simp] simplex26_lookup_max_bound

theorem simplex26_lookup_jensen_bound :
    rawSimplex26.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '0', '3', '5', '6', '2', '2', '0', '2', '9', '7', '5', '6', '8', '7', '6', '1', '1', '8', '9', '7', '6', '8', '5', '8', '7', '9', '4', '1', '0', '4', '6', '9', '7', '7', '9', '0', '9', '9', '2', '5', '0', '1', '7', '4', '3', '4', '4', '3', '8', '3', '5', '7', '5', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '8', '0', '0', '4', '3', '5', '4', '0', '3', '3', '8', '2', '4', '2', '4', '9', '8', '7', '2', '9', '1', '4', '1', '4', '0', '2', '9', '3', '1', '0', '2', '5', '7', '0', '6', '6', '3', '8', '3', '3', '2', '7', '4', '3', '7', '1', '3', '0', '7', '4', '7', '6', '9', '1', '0', '2', '7', '5', '5', '6', '8', '3', '0', '0', '2', '1', '6', '9', '6', '4', '7', '8', '3', '3', '3', '6', '1', '7', '1', '2', '8', '9', '0', '5', '1', '0', '5', '1', '3', '7', '3', '0', '9', '0', '5', '2', '7', '5', '0', '9', '7'])) := by
  rfl

attribute [local simp] simplex26_lookup_jensen_bound

theorem simplex26_lookup_max_floor_Q96 :
    rawSimplex26.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['7', '0', '3', '7', '6', '7', '8', '8', '9', '2', '5', '3', '7', '0', '5', '8', '7'])) := by
  rfl

attribute [local simp] simplex26_lookup_max_floor_Q96

theorem simplex26_lookup_jensen_floor_Q96 :
    rawSimplex26.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['5', '0', '1', '0', '1', '0', '2', '9', '4', '4', '7', '4', '5', '2', '9', '9', '1', '4'])) := by
  rfl

attribute [local simp] simplex26_lookup_jensen_floor_Q96

theorem simplex26_decoded : decodeSimplex rawSimplex26 = .ok simplex26 := by
  unfold decodeSimplex simplex26
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
