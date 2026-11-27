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

theorem simplex05_lookup_simplex_id :
    rawSimplex05.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5'])) := by
  rfl

attribute [local simp] simplex05_lookup_simplex_id

theorem simplex05_lookup_vertex_ids :
    rawSimplex05.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_vertex_ids

theorem simplex05_lookup_physical_volume :
    rawSimplex05.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '2', '9', '6', '9', '0', '4', '2', '1', '7', '2', '4', '9', '9', '6', '3', '2', '2', '5', '5', '2', '7', '5', '9', '9', '7', '2', '2', '5', '4', '5', '8', '0', '4', '0', '4', '7', '0', '3', '4', '6', '3', '9', '/', '1', '2', '8', '8', '8', '2', '2', '3', '1', '9', '7', '9', '5', '4', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_physical_volume

theorem simplex05_lookup_mean_gap :
    rawSimplex05.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_mean_gap

theorem simplex05_lookup_factor_maxima :
    rawSimplex05.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_factor_maxima

theorem simplex05_lookup_gap_weighted_means :
    rawSimplex05.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '3', '2', '4', '2', '1', '3', '6', '5', '3', '9', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '4', '9', '7', '0', '8', '4', '8', '8', '4', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '3', '0', '3', '6', '3', '8', '3', '4', '6', '3', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '0', '0', '5', '9', '3', '9', '8', '4', '3', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '1', '8', '0', '5', '0', '1', '1', '1', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '3', '1', '3', '9', '0', '6', '2', '2', '3', '/', '1', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '0', '0', '3', '0', '9', '6', '1', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '5', '7', '4', '9', '7', '4', '1', '0', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '6', '6', '1', '3', '1', '1', '4', '4', '7', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '0', '9', '8', '1', '6', '6', '7', '6', '8', '1', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_gap_weighted_means

theorem simplex05_lookup_max_bound :
    rawSimplex05.getObjVal? "max_bound" = .ok (.str (String.ofList ['6', '3', '0', '7', '1', '5', '1', '3', '8', '6', '8', '0', '1', '5', '3', '2', '2', '7', '7', '6', '6', '4', '3', '2', '2', '2', '3', '3', '1', '9', '4', '2', '7', '3', '8', '3', '8', '6', '6', '7', '3', '1', '1', '3', '9', '4', '4', '7', '8', '7', '5', '9', '7', '6', '5', '6', '2', '5', '/', '4', '8', '3', '5', '8', '4', '1', '5', '7', '3', '3', '9', '3', '6', '8', '4', '0', '8', '8', '5', '7', '4', '4', '3', '1', '9', '9', '3', '9', '8', '8', '4', '2', '9', '9', '2', '9', '3', '5', '6', '3', '2', '0', '7', '8', '8', '4', '8', '6', '1', '4', '1', '4', '1', '4', '3', '1', '0', '1', '9', '8', '0', '4', '1', '2', '4', '2', '9', '3'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_bound

theorem simplex05_lookup_jensen_bound :
    rawSimplex05.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '7', '0', '2', '3', '1', '5', '1', '9', '4', '1', '7', '8', '7', '7', '4', '3', '5', '3', '2', '1', '6', '9', '6', '5', '6', '9', '7', '0', '2', '7', '5', '5', '2', '6', '7', '1', '9', '0', '4', '4', '4', '9', '4', '0', '0', '9', '0', '7', '1', '9', '9', '9', '8', '5', '8', '5', '4', '7', '2', '9', '1', '8', '7', '8', '3', '5', '2', '2', '0', '4', '1', '6', '9', '0', '2', '0', '9', '9', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '3', '1', '1', '8', '5', '6', '1', '2', '4', '3', '0', '6', '1', '1', '6', '8', '3', '5', '6', '9', '4', '5', '9', '8', '6', '6', '9', '1', '7', '7', '4', '7', '1', '8', '2', '3', '5', '3', '9', '3', '2', '5', '8', '2', '8', '2', '8', '7', '8', '8', '3', '3', '6', '2', '0', '6', '4', '3', '0', '0', '1', '1', '4', '7', '2', '6', '8', '1', '4', '4', '9', '5', '3', '1', '3', '6', '4', '7', '6', '9', '9', '8', '9', '0', '0', '0', '9', '7', '8', '9', '9', '6', '8', '2', '3', '5', '1', '2', '4', '5', '0', '2', '0', '4', '6', '4', '7', '8', '7', '8', '6', '7', '5', '3'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_bound

theorem simplex05_lookup_max_floor_Q96 :
    rawSimplex05.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '0', '3', '3', '3', '3', '4', '1', '3', '1', '1', '7', '7', '7', '0', '6', '3', '2', '6'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_floor_Q96

theorem simplex05_lookup_jensen_floor_Q96 :
    rawSimplex05.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '0', '9', '5', '4', '5', '8', '7', '4', '7', '1', '8', '7', '8', '7', '4', '4', '9', '2', '3'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_floor_Q96

theorem simplex05_decoded : decodeSimplex rawSimplex05 = .ok simplex05 := by
  unfold decodeSimplex simplex05
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
