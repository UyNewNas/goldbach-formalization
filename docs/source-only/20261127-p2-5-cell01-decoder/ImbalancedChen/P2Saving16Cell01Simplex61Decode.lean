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

theorem simplex61_lookup_simplex_id :
    rawSimplex61.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '1'])) := by
  rfl

attribute [local simp] simplex61_lookup_simplex_id

theorem simplex61_lookup_vertex_ids :
    rawSimplex61.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex61_lookup_vertex_ids

theorem simplex61_lookup_physical_volume :
    rawSimplex61.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '3', '1', '2', '6', '6', '5', '4', '7', '6', '7', '2', '3', '8', '6', '9', '8', '3', '3', '5', '6', '9', '1', '3', '2', '9', '3', '1', '1', '0', '1', '2', '9', '2', '3', '9', '8', '1', '3', '1', '4', '8', '2', '3', '3', '6', '2', '3', '/', '1', '0', '9', '7', '7', '3', '6', '5', '1', '0', '5', '7', '5', '7', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex61_lookup_physical_volume

theorem simplex61_lookup_mean_gap :
    rawSimplex61.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex61_lookup_mean_gap

theorem simplex61_lookup_factor_maxima :
    rawSimplex61.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex61_lookup_factor_maxima

theorem simplex61_lookup_gap_weighted_means :
    rawSimplex61.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '9', '1', '9', '0', '2', '8', '6', '9', '5', '6', '5', '9', '4', '7', '/', '6', '0', '7', '8', '5', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '2', '1', '6', '4', '1', '6', '3', '8', '6', '6', '8', '9', '7', '/', '6', '0', '7', '8', '5', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '9', '5', '7', '0', '4', '1', '6', '1', '0', '7', '1', '7', '8', '3', '/', '1', '8', '2', '3', '5', '6', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '7', '4', '2', '8', '1', '2', '7', '1', '3', '6', '7', '7', '1', '/', '3', '6', '4', '7', '1', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '5', '6', '7', '7', '9', '8', '4', '4', '0', '1', '5', '9', '/', '3', '6', '4', '7', '1', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '5', '6', '6', '9', '9', '3', '8', '5', '7', '0', '4', '3', '/', '9', '1', '1', '7', '8', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '1', '5', '7', '6', '6', '9', '4', '9', '4', '9', '7', '/', '6', '0', '7', '8', '5', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '7', '0', '7', '9', '1', '4', '8', '3', '1', '3', '8', '7', '/', '3', '6', '4', '7', '1', '2', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '7', '8', '4', '3', '4', '7', '7', '2', '0', '2', '0', '7', '9', '/', '1', '8', '2', '3', '5', '6', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '2', '5', '2', '5', '2', '5', '4', '7', '8', '3', '9', '6', '7', '/', '1', '8', '2', '3', '5', '6', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex61_lookup_gap_weighted_means

theorem simplex61_lookup_max_bound :
    rawSimplex61.getObjVal? "max_bound" = .ok (.str (String.ofList ['9', '3', '9', '6', '1', '3', '2', '6', '4', '3', '3', '2', '1', '6', '2', '5', '8', '1', '5', '3', '3', '5', '0', '8', '4', '7', '4', '8', '2', '1', '2', '7', '8', '8', '0', '5', '9', '7', '1', '5', '5', '9', '8', '6', '9', '8', '3', '4', '8', '2', '1', '5', '3', '4', '6', '0', '9', '3', '7', '5', '/', '1', '1', '7', '9', '4', '6', '8', '9', '7', '2', '6', '5', '7', '7', '2', '8', '0', '0', '2', '0', '6', '8', '6', '0', '8', '8', '6', '7', '8', '3', '0', '4', '8', '4', '6', '3', '6', '3', '5', '3', '3', '0', '7', '6', '4', '2', '0', '3', '9', '9', '8', '7', '6', '0', '1', '5', '1', '6', '3', '1', '7', '7', '3', '4', '7', '9', '1', '6', '0', '7', '5', '9', '3'])) := by
  rfl

attribute [local simp] simplex61_lookup_max_bound

theorem simplex61_lookup_jensen_bound :
    rawSimplex61.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '8', '7', '8', '4', '2', '0', '6', '9', '3', '1', '0', '5', '4', '1', '6', '6', '8', '0', '5', '0', '1', '7', '0', '4', '5', '6', '1', '6', '3', '8', '4', '2', '5', '8', '2', '5', '1', '2', '2', '9', '6', '5', '6', '8', '6', '5', '4', '7', '6', '3', '5', '4', '7', '6', '6', '9', '1', '7', '5', '2', '8', '2', '5', '4', '8', '0', '8', '9', '4', '4', '4', '2', '3', '9', '7', '4', '0', '2', '1', '6', '6', '3', '2', '7', '2', '2', '6', '3', '6', '2', '9', '4', '6', '8', '6', '0', '5', '3', '3', '2', '7', '0', '2', '1', '6', '0', '2', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '8', '0', '8', '9', '2', '9', '6', '7', '7', '0', '5', '7', '6', '0', '4', '9', '0', '0', '9', '8', '3', '4', '8', '2', '7', '4', '3', '8', '7', '8', '8', '4', '4', '6', '7', '7', '2', '9', '9', '9', '5', '0', '2', '7', '9', '4', '9', '3', '1', '2', '5', '7', '3', '7', '4', '9', '7', '5', '4', '8', '7', '6', '3', '9', '5', '3', '3', '9', '9', '9', '7', '5', '6', '1', '9', '4', '5', '5', '4', '3', '7', '1', '4', '9', '3', '1', '6', '6', '5', '3', '0', '5', '1', '9', '8', '9', '9', '4', '6', '9', '2', '5', '2', '2', '0', '8', '8', '4', '5', '6', '5', '6', '8', '0', '2', '2', '4', '0', '7', '4', '5', '1', '2', '4', '6', '2', '0', '9', '6', '9', '0', '4', '5', '5', '0', '2', '7', '6', '0', '4', '9', '1', '3'])) := by
  rfl

attribute [local simp] simplex61_lookup_jensen_bound

theorem simplex61_lookup_max_floor_Q96 :
    rawSimplex61.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '3', '1', '1', '6', '3', '9', '7', '4', '0', '6', '6', '4', '0', '3', '5', '8'])) := by
  rfl

attribute [local simp] simplex61_lookup_max_floor_Q96

theorem simplex61_lookup_jensen_floor_Q96 :
    rawSimplex61.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '7', '4', '9', '9', '7', '8', '3', '7', '7', '1', '2', '1', '4', '8', '8', '9', '2'])) := by
  rfl

attribute [local simp] simplex61_lookup_jensen_floor_Q96

theorem simplex61_decoded : decodeSimplex rawSimplex61 = .ok simplex61 := by
  unfold decodeSimplex simplex61
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
