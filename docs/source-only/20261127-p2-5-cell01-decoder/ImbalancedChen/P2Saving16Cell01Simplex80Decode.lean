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

theorem simplex80_lookup_simplex_id :
    rawSimplex80.getObjVal? "simplex_id" = .ok (.number (String.ofList ['8', '0'])) := by
  rfl

attribute [local simp] simplex80_lookup_simplex_id

theorem simplex80_lookup_vertex_ids :
    rawSimplex80.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '2']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex80_lookup_vertex_ids

theorem simplex80_lookup_physical_volume :
    rawSimplex80.getObjVal? "physical_volume" = .ok (.str (String.ofList ['9', '9', '6', '9', '9', '2', '1', '8', '0', '2', '0', '3', '8', '4', '3', '5', '0', '5', '8', '2', '3', '4', '9', '7', '1', '0', '7', '9', '0', '9', '/', '7', '8', '2', '7', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex80_lookup_physical_volume

theorem simplex80_lookup_mean_gap :
    rawSimplex80.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '0', '8', '3', '/', '3', '9', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex80_lookup_mean_gap

theorem simplex80_lookup_factor_maxima :
    rawSimplex80.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '8', '6', '7', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex80_lookup_factor_maxima

theorem simplex80_lookup_gap_weighted_means :
    rawSimplex80.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '1', '3', '7', '0', '8', '5', '5', '9', '3', '9', '/', '2', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '6', '3', '3', '3', '1', '3', '9', '3', '9', '/', '2', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '5', '0', '3', '0', '6', '8', '0', '1', '1', '/', '8', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '9', '4', '5', '9', '8', '8', '6', '1', '/', '2', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '1', '4', '9', '2', '5', '7', '/', '2', '2', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '7', '3', '6', '3', '6', '2', '9', '/', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '6', '2', '0', '6', '4', '7', '7', '9', '/', '5', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '9', '7', '0', '7', '6', '7', '7', '/', '2', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '6', '9', '9', '4', '9', '9', '/', '1', '1', '3', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '2', '0', '1', '9', '7', '2', '9', '3', '9', '/', '8', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex80_lookup_gap_weighted_means

theorem simplex80_lookup_max_bound :
    rawSimplex80.getObjVal? "max_bound" = .ok (.str (String.ofList ['9', '3', '4', '5', '3', '0', '6', '2', '0', '1', '1', '4', '0', '7', '2', '7', '1', '0', '1', '8', '3', '6', '5', '5', '0', '1', '4', '0', '9', '8', '5', '0', '1', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '2', '0', '8', '0', '6', '9', '9', '5', '4', '1', '8', '9', '8', '7', '3', '2', '8', '9', '8', '9', '9', '1', '0', '3', '1', '6', '4', '8', '0', '2', '9', '5', '7', '8', '5', '2', '3', '8', '3', '5', '0', '6', '2', '7', '9', '0', '6', '2', '9', '2', '2', '8', '5', '5', '1', '8', '0', '9', '8', '5', '8', '9', '9'])) := by
  rfl

attribute [local simp] simplex80_lookup_max_bound

theorem simplex80_lookup_jensen_bound :
    rawSimplex80.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['7', '8', '2', '1', '5', '3', '9', '7', '1', '1', '1', '9', '8', '9', '3', '2', '6', '9', '5', '5', '4', '5', '4', '7', '7', '2', '4', '2', '8', '7', '0', '9', '3', '0', '4', '5', '5', '5', '0', '1', '3', '6', '1', '7', '6', '8', '3', '4', '5', '0', '4', '4', '7', '9', '9', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '7', '9', '2', '1', '7', '2', '5', '0', '0', '2', '6', '7', '3', '4', '7', '5', '8', '8', '0', '0', '9', '1', '0', '5', '7', '2', '2', '5', '8', '1', '6', '8', '8', '2', '3', '3', '1', '2', '5', '2', '5', '4', '3', '3', '2', '4', '5', '8', '6', '7', '8', '2', '6', '0', '4', '2', '3', '6', '2', '2', '3', '3', '2', '2', '6', '1', '8', '4', '9', '0', '2', '1', '1', '6', '2', '6', '8', '9', '8', '6', '3', '6', '4', '6', '0', '0', '0', '7', '8', '1', '0', '8', '2', '5', '4', '9'])) := by
  rfl

attribute [local simp] simplex80_lookup_jensen_bound

theorem simplex80_lookup_max_floor_Q96 :
    rawSimplex80.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '7', '5', '9', '5', '0', '3', '6', '3', '5', '8', '9', '4', '4', '7', '9', '5'])) := by
  rfl

attribute [local simp] simplex80_lookup_max_floor_Q96

theorem simplex80_lookup_jensen_floor_Q96 :
    rawSimplex80.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '8', '2', '2', '6', '1', '7', '1', '5', '9', '0', '3', '4', '2', '4', '3', '2'])) := by
  rfl

attribute [local simp] simplex80_lookup_jensen_floor_Q96

theorem simplex80_decoded : decodeSimplex rawSimplex80 = .ok simplex80 := by
  unfold decodeSimplex simplex80
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
