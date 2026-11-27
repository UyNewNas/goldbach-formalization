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

theorem simplex74_lookup_simplex_id :
    rawSimplex74.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '4'])) := by
  rfl

attribute [local simp] simplex74_lookup_simplex_id

theorem simplex74_lookup_vertex_ids :
    rawSimplex74.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex74_lookup_vertex_ids

theorem simplex74_lookup_physical_volume :
    rawSimplex74.getObjVal? "physical_volume" = .ok (.str (String.ofList ['5', '6', '7', '9', '4', '5', '4', '2', '4', '1', '5', '1', '2', '1', '6', '4', '6', '2', '7', '6', '0', '8', '7', '7', '5', '5', '7', '5', '8', '2', '1', '/', '2', '3', '5', '7', '5', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex74_lookup_physical_volume

theorem simplex74_lookup_mean_gap :
    rawSimplex74.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex74_lookup_mean_gap

theorem simplex74_lookup_factor_maxima :
    rawSimplex74.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '2', '1', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex74_lookup_factor_maxima

theorem simplex74_lookup_gap_weighted_means :
    rawSimplex74.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '5', '4', '3', '9', '8', '7', '2', '8', '9', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '9', '6', '4', '8', '0', '5', '6', '9', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '2', '7', '2', '2', '5', '9', '5', '5', '9', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '4', '9', '1', '5', '8', '4', '9', '3', '3', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '7', '9', '1', '2', '4', '1', '3', '9', '/', '3', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '1', '9', '7', '2', '2', '6', '5', '1', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '7', '5', '3', '6', '6', '1', '3', '1', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '3', '1', '8', '7', '8', '7', '1', '/', '9', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '7', '1', '5', '9', '7', '6', '1', '9', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '8', '8', '9', '5', '2', '8', '4', '9', '1', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex74_lookup_gap_weighted_means

theorem simplex74_lookup_max_bound :
    rawSimplex74.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '2', '6', '8', '7', '7', '0', '9', '0', '7', '3', '5', '2', '6', '4', '1', '3', '7', '0', '2', '8', '6', '6', '4', '5', '3', '1', '5', '2', '6', '0', '5', '3', '7', '4', '8', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '4', '6', '4', '2', '6', '0', '8', '7', '4', '3', '3', '2', '2', '5', '7', '4', '5', '6', '8', '1', '3', '7', '1', '1', '1', '6', '4', '3', '7', '9', '5', '0', '1', '1', '1', '0', '1', '0', '8', '2', '9', '8', '2', '1', '0', '3', '2', '6', '8', '4', '7', '3', '6', '8', '6', '7', '4', '0', '8', '3', '4', '6', '0', '9', '7'])) := by
  rfl

attribute [local simp] simplex74_lookup_max_bound

theorem simplex74_lookup_jensen_bound :
    rawSimplex74.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '5', '8', '6', '8', '9', '7', '7', '9', '3', '4', '8', '6', '5', '4', '8', '1', '1', '3', '8', '4', '0', '9', '2', '1', '8', '5', '6', '1', '0', '5', '3', '7', '2', '2', '3', '6', '0', '2', '6', '7', '2', '6', '7', '1', '7', '4', '5', '1', '9', '4', '5', '9', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '8', '7', '1', '9', '5', '2', '2', '0', '8', '0', '9', '7', '6', '0', '2', '0', '7', '1', '1', '2', '6', '5', '5', '3', '3', '1', '0', '4', '8', '3', '3', '3', '3', '5', '2', '2', '9', '4', '4', '8', '1', '2', '2', '8', '6', '7', '4', '8', '7', '4', '1', '0', '4', '4', '2', '1', '6', '3', '0', '7', '2', '5', '1', '0', '2', '9', '6', '5', '4', '4', '7', '9', '8', '5', '2', '8', '2', '8', '6', '3', '8', '2', '1', '2', '7', '5', '1', '3', '0', '3', '7', '7', '6', '5', '4', '5', '8', '1', '6', '7'])) := by
  rfl

attribute [local simp] simplex74_lookup_jensen_bound

theorem simplex74_lookup_max_floor_Q96 :
    rawSimplex74.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '9', '3', '2', '9', '8', '3', '3', '4', '2', '1', '2', '0'])) := by
  rfl

attribute [local simp] simplex74_lookup_max_floor_Q96

theorem simplex74_lookup_jensen_floor_Q96 :
    rawSimplex74.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '7', '2', '6', '3', '8', '1', '2', '6', '5', '6', '7', '2', '1'])) := by
  rfl

attribute [local simp] simplex74_lookup_jensen_floor_Q96

theorem simplex74_decoded : decodeSimplex rawSimplex74 = .ok simplex74 := by
  unfold decodeSimplex simplex74
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
