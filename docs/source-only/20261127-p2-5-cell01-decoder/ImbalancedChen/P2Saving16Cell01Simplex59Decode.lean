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

theorem simplex59_lookup_simplex_id :
    rawSimplex59.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5', '9'])) := by
  rfl

attribute [local simp] simplex59_lookup_simplex_id

theorem simplex59_lookup_vertex_ids :
    rawSimplex59.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '5']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex59_lookup_vertex_ids

theorem simplex59_lookup_physical_volume :
    rawSimplex59.getObjVal? "physical_volume" = .ok (.str (String.ofList ['9', '1', '4', '2', '4', '4', '6', '0', '9', '9', '1', '1', '4', '6', '4', '7', '6', '4', '1', '0', '9', '7', '7', '2', '3', '8', '0', '9', '6', '8', '4', '3', '8', '6', '4', '3', '/', '1', '1', '9', '0', '4', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex59_lookup_physical_volume

theorem simplex59_lookup_mean_gap :
    rawSimplex59.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex59_lookup_mean_gap

theorem simplex59_lookup_factor_maxima :
    rawSimplex59.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex59_lookup_factor_maxima

theorem simplex59_lookup_gap_weighted_means :
    rawSimplex59.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['9', '8', '9', '2', '0', '6', '0', '0', '1', '2', '3', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '4', '9', '5', '3', '9', '8', '5', '2', '3', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '7', '1', '0', '2', '8', '3', '5', '2', '2', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '9', '4', '6', '6', '4', '7', '4', '8', '7', '7', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '6', '9', '4', '1', '4', '1', '2', '7', '3', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '5', '2', '1', '0', '1', '5', '1', '5', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '7', '9', '8', '4', '9', '1', '4', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '5', '2', '5', '8', '3', '6', '0', '4', '9', '/', '8', '3', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '3', '3', '0', '3', '8', '1', '8', '2', '1', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '3', '8', '2', '5', '2', '8', '9', '2', '3', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex59_lookup_gap_weighted_means

theorem simplex59_lookup_max_bound :
    rawSimplex59.getObjVal? "max_bound" = .ok (.str (String.ofList ['3', '4', '4', '1', '4', '2', '1', '5', '0', '2', '4', '9', '9', '3', '7', '3', '5', '4', '0', '2', '1', '6', '3', '4', '3', '8', '3', '0', '9', '7', '8', '5', '3', '9', '9', '8', '2', '5', '0', '8', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '4', '1', '4', '3', '5', '8', '8', '6', '6', '9', '2', '1', '8', '2', '3', '0', '9', '0', '9', '8', '1', '3', '3', '2', '0', '5', '4', '2', '4', '4', '4', '5', '9', '2', '4', '4', '5', '8', '0', '9', '0', '3', '2', '8', '7', '8', '6', '4', '1', '7', '0', '0', '4', '8', '5', '6', '2', '9', '4', '2', '4', '6', '7'])) := by
  rfl

attribute [local simp] simplex59_lookup_max_bound

theorem simplex59_lookup_jensen_bound :
    rawSimplex59.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['6', '2', '6', '4', '8', '6', '8', '3', '8', '9', '0', '9', '7', '6', '4', '1', '1', '9', '8', '5', '0', '5', '3', '4', '8', '5', '9', '2', '1', '3', '9', '4', '9', '8', '6', '8', '0', '9', '3', '5', '6', '6', '7', '2', '2', '0', '5', '3', '1', '9', '5', '1', '9', '7', '0', '3', '7', '1', '2', '3', '0', '1', '2', '1', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '3', '9', '9', '7', '9', '5', '4', '9', '2', '4', '5', '4', '0', '2', '9', '3', '5', '1', '2', '0', '4', '1', '5', '0', '9', '5', '7', '0', '7', '9', '2', '4', '5', '6', '5', '9', '8', '5', '9', '4', '1', '7', '1', '1', '9', '1', '3', '6', '7', '8', '6', '1', '1', '2', '6', '7', '0', '9', '5', '6', '5', '0', '0', '6', '5', '2', '5', '7', '5', '3', '5', '8', '0', '3', '0', '7', '6', '0', '1', '7', '3', '4', '4', '3', '4', '1', '6', '4', '2', '4', '5', '4', '0', '8', '6', '2', '4', '1', '6', '6', '3', '2', '3', '6', '3', '6', '3'])) := by
  rfl

attribute [local simp] simplex59_lookup_jensen_bound

theorem simplex59_lookup_max_floor_Q96 :
    rawSimplex59.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '1', '2', '9', '3', '1', '6', '3', '8', '2', '1', '4', '8', '8', '0', '4', '9'])) := by
  rfl

attribute [local simp] simplex59_lookup_max_floor_Q96

theorem simplex59_lookup_jensen_floor_Q96 :
    rawSimplex59.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['5', '9', '0', '9', '1', '2', '0', '1', '8', '4', '0', '3', '0', '7', '4', '0', '0'])) := by
  rfl

attribute [local simp] simplex59_lookup_jensen_floor_Q96

theorem simplex59_decoded : decodeSimplex rawSimplex59 = .ok simplex59 := by
  unfold decodeSimplex simplex59
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
