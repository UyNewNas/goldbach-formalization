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

theorem simplex75_lookup_simplex_id :
    rawSimplex75.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '5'])) := by
  rfl

attribute [local simp] simplex75_lookup_simplex_id

theorem simplex75_lookup_vertex_ids :
    rawSimplex75.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex75_lookup_vertex_ids

theorem simplex75_lookup_physical_volume :
    rawSimplex75.getObjVal? "physical_volume" = .ok (.str (String.ofList ['7', '5', '7', '2', '3', '6', '3', '3', '0', '0', '9', '4', '7', '2', '1', '8', '1', '5', '2', '2', '8', '1', '3', '0', '2', '9', '0', '2', '4', '1', '/', '5', '0', '2', '9', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex75_lookup_physical_volume

theorem simplex75_lookup_mean_gap :
    rawSimplex75.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex75_lookup_mean_gap

theorem simplex75_lookup_factor_maxima :
    rawSimplex75.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '2', '1', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex75_lookup_factor_maxima

theorem simplex75_lookup_gap_weighted_means :
    rawSimplex75.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '5', '7', '5', '2', '6', '6', '6', '1', '4', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '2', '7', '7', '5', '9', '8', '9', '4', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '4', '8', '8', '7', '8', '7', '4', '0', '9', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '1', '5', '6', '4', '3', '5', '8', '3', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '4', '3', '1', '2', '4', '0', '9', '/', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '1', '4', '9', '1', '0', '9', '2', '1', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '0', '5', '5', '4', '4', '0', '1', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '9', '8', '3', '7', '6', '1', '4', '1', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '1', '8', '3', '4', '6', '3', '2', '3', '/', '1', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '2', '3', '9', '9', '4', '4', '9', '4', '1', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex75_lookup_gap_weighted_means

theorem simplex75_lookup_max_bound :
    rawSimplex75.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '5', '1', '4', '2', '7', '8', '8', '0', '7', '6', '8', '8', '9', '3', '9', '3', '8', '1', '6', '7', '1', '5', '6', '2', '1', '7', '9', '1', '2', '7', '6', '9', '8', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '8', '8', '0', '8', '6', '9', '5', '8', '1', '1', '0', '7', '5', '2', '4', '8', '5', '6', '0', '4', '5', '7', '0', '3', '8', '8', '1', '2', '6', '5', '0', '0', '3', '7', '0', '0', '3', '6', '0', '9', '9', '4', '0', '3', '4', '4', '2', '2', '8', '2', '4', '5', '6', '2', '2', '4', '6', '9', '4', '4', '8', '6', '9', '9'])) := by
  rfl

attribute [local simp] simplex75_lookup_max_bound

theorem simplex75_lookup_jensen_bound :
    rawSimplex75.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['5', '3', '8', '9', '1', '9', '7', '9', '2', '1', '1', '6', '6', '3', '8', '9', '0', '1', '8', '9', '2', '5', '0', '6', '2', '6', '3', '4', '2', '8', '4', '6', '7', '8', '8', '0', '6', '5', '3', '0', '9', '0', '7', '7', '0', '8', '6', '3', '9', '1', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '8', '8', '6', '4', '9', '2', '6', '4', '4', '1', '6', '3', '6', '2', '9', '9', '0', '5', '2', '7', '0', '5', '6', '7', '7', '5', '1', '5', '8', '1', '7', '6', '0', '6', '2', '2', '0', '0', '5', '9', '1', '5', '2', '3', '3', '4', '3', '2', '9', '4', '1', '1', '3', '3', '6', '9', '2', '2', '5', '3', '7', '4', '8', '5', '4', '6', '6', '8', '6', '1', '7', '4', '6', '2', '5', '4', '5', '1', '1', '9', '8', '7', '9', '0', '5', '1', '8', '5', '9', '3', '8', '8', '2', '2', '8', '4', '7', '9', '4', '9'])) := by
  rfl

attribute [local simp] simplex75_lookup_jensen_bound

theorem simplex75_lookup_max_floor_Q96 :
    rawSimplex75.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '4', '5', '8', '0', '3', '5', '9', '1', '9', '0', '8', '8', '4', '6', '6', '2'])) := by
  rfl

attribute [local simp] simplex75_lookup_max_floor_Q96

theorem simplex75_lookup_jensen_floor_Q96 :
    rawSimplex75.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '0', '9', '8', '6', '1', '5', '8', '6', '7', '3', '4', '4', '8', '1', '3', '0', '0'])) := by
  rfl

attribute [local simp] simplex75_lookup_jensen_floor_Q96

theorem simplex75_decoded : decodeSimplex rawSimplex75 = .ok simplex75 := by
  unfold decodeSimplex simplex75
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
