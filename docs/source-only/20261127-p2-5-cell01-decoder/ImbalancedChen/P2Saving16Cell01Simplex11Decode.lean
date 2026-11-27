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

theorem simplex11_lookup_simplex_id :
    rawSimplex11.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1', '1'])) := by
  rfl

attribute [local simp] simplex11_lookup_simplex_id

theorem simplex11_lookup_vertex_ids :
    rawSimplex11.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex11_lookup_vertex_ids

theorem simplex11_lookup_physical_volume :
    rawSimplex11.getObjVal? "physical_volume" = .ok (.str (String.ofList ['8', '6', '2', '5', '2', '2', '7', '3', '9', '9', '0', '2', '2', '6', '4', '0', '5', '0', '8', '0', '5', '3', '3', '1', '1', '6', '1', '4', '2', '2', '3', '1', '3', '0', '6', '8', '2', '2', '1', '/', '2', '3', '4', '9', '4', '1', '5', '6', '8', '7', '1', '2', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex11_lookup_physical_volume

theorem simplex11_lookup_mean_gap :
    rawSimplex11.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex11_lookup_mean_gap

theorem simplex11_lookup_factor_maxima :
    rawSimplex11.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex11_lookup_factor_maxima

theorem simplex11_lookup_gap_weighted_means :
    rawSimplex11.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '0', '6', '3', '0', '0', '7', '1', '0', '1', '/', '6', '6', '3', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '4', '0', '0', '4', '4', '8', '4', '8', '3', '/', '5', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '8', '1', '2', '8', '5', '5', '8', '1', '6', '7', '/', '1', '5', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '9', '3', '0', '2', '8', '4', '1', '5', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '9', '3', '9', '9', '3', '1', '2', '1', '6', '1', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '8', '5', '5', '3', '8', '8', '8', '6', '3', '/', '6', '3', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '3', '4', '9', '5', '0', '2', '3', '1', '/', '2', '1', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '1', '6', '1', '9', '7', '7', '0', '1', '/', '7', '9', '6', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '7', '6', '5', '0', '0', '0', '1', '/', '9', '9', '5', '6', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '5', '0', '6', '5', '2', '1', '4', '8', '3', '/', '1', '5', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex11_lookup_gap_weighted_means

theorem simplex11_lookup_max_bound :
    rawSimplex11.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '6', '5', '1', '7', '4', '1', '2', '5', '3', '9', '9', '5', '4', '6', '6', '4', '3', '8', '5', '5', '0', '2', '6', '2', '4', '1', '7', '5', '2', '2', '2', '4', '1', '1', '8', '1', '2', '6', '4', '7', '0', '3', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '/', '9', '1', '0', '6', '7', '2', '7', '4', '2', '0', '8', '4', '9', '8', '5', '8', '7', '3', '5', '2', '8', '7', '4', '2', '4', '8', '4', '2', '2', '5', '6', '5', '8', '5', '2', '6', '7', '0', '5', '8', '3', '9', '1', '0', '1', '6', '9', '3', '4', '2', '9', '4', '6', '4', '4', '4', '9', '0', '8', '0', '1', '3', '2', '9', '6', '4', '2', '7'])) := by
  rfl

attribute [local simp] simplex11_lookup_max_bound

theorem simplex11_lookup_jensen_bound :
    rawSimplex11.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '6', '0', '2', '8', '7', '9', '3', '5', '4', '3', '0', '4', '7', '0', '5', '8', '6', '6', '0', '8', '4', '2', '5', '7', '7', '4', '6', '7', '2', '6', '2', '6', '8', '6', '2', '2', '0', '5', '6', '6', '9', '8', '5', '1', '4', '1', '6', '7', '7', '6', '3', '0', '8', '0', '9', '5', '5', '7', '2', '1', '3', '9', '4', '2', '0', '8', '9', '0', '8', '0', '8', '1', '0', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '7', '7', '2', '0', '0', '2', '4', '9', '2', '2', '0', '9', '8', '5', '4', '8', '8', '5', '0', '5', '8', '8', '3', '7', '7', '8', '6', '5', '6', '8', '5', '3', '4', '1', '2', '8', '9', '1', '9', '4', '6', '5', '8', '1', '0', '5', '9', '0', '8', '6', '1', '1', '9', '4', '1', '8', '3', '3', '2', '8', '5', '2', '7', '5', '8', '9', '5', '9', '1', '9', '4', '2', '4', '6', '9', '3', '3', '1', '6', '8', '5', '2', '5', '2', '6', '0', '2', '0', '6', '6', '2', '4', '6', '5', '4', '0', '5', '9', '0', '3', '7', '5', '2', '7'])) := by
  rfl

attribute [local simp] simplex11_lookup_jensen_bound

theorem simplex11_lookup_max_floor_Q96 :
    rawSimplex11.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '9', '1', '6', '9', '9', '2', '1', '7', '3', '6', '6', '4', '2'])) := by
  rfl

attribute [local simp] simplex11_lookup_max_floor_Q96

theorem simplex11_lookup_jensen_floor_Q96 :
    rawSimplex11.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '1', '5', '7', '2', '9', '1', '0', '3', '8', '6', '2', '2', '7', '5'])) := by
  rfl

attribute [local simp] simplex11_lookup_jensen_floor_Q96

theorem simplex11_decoded : decodeSimplex rawSimplex11 = .ok simplex11 := by
  unfold decodeSimplex simplex11
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
