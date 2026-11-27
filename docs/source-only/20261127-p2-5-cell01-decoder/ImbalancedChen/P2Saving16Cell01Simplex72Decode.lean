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

theorem simplex72_lookup_simplex_id :
    rawSimplex72.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '2'])) := by
  rfl

attribute [local simp] simplex72_lookup_simplex_id

theorem simplex72_lookup_vertex_ids :
    rawSimplex72.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex72_lookup_vertex_ids

theorem simplex72_lookup_physical_volume :
    rawSimplex72.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '6', '7', '5', '9', '8', '2', '3', '0', '0', '6', '4', '6', '0', '8', '2', '2', '4', '8', '0', '3', '9', '0', '7', '0', '8', '5', '1', '5', '8', '6', '1', '2', '5', '5', '0', '8', '9', '/', '3', '8', '1', '9', '2', '8', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex72_lookup_physical_volume

theorem simplex72_lookup_mean_gap :
    rawSimplex72.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex72_lookup_mean_gap

theorem simplex72_lookup_factor_maxima :
    rawSimplex72.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex72_lookup_factor_maxima

theorem simplex72_lookup_gap_weighted_means :
    rawSimplex72.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '3', '1', '5', '3', '9', '9', '6', '9', '9', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '6', '7', '8', '9', '2', '9', '7', '9', '1', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '5', '0', '6', '8', '2', '7', '1', '5', '3', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '4', '8', '5', '3', '1', '2', '0', '3', '9', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '9', '0', '1', '5', '6', '0', '0', '1', '1', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '7', '8', '8', '1', '5', '6', '0', '9', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '8', '1', '4', '3', '6', '8', '7', '9', '/', '2', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '0', '7', '0', '5', '1', '3', '4', '3', '3', '/', '2', '7', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '9', '1', '9', '6', '3', '4', '3', '5', '7', '/', '1', '3', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '4', '7', '1', '0', '2', '1', '9', '7', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex72_lookup_gap_weighted_means

theorem simplex72_lookup_max_bound :
    rawSimplex72.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '0', '4', '7', '0', '1', '8', '2', '3', '9', '7', '3', '3', '7', '5', '8', '6', '4', '3', '2', '3', '4', '0', '9', '8', '7', '4', '9', '7', '9', '2', '7', '4', '5', '3', '6', '6', '0', '9', '0', '8', '7', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '/', '5', '7', '5', '6', '4', '6', '8', '7', '0', '8', '8', '0', '2', '7', '5', '0', '6', '5', '6', '0', '8', '9', '3', '8', '6', '3', '7', '1', '3', '7', '7', '5', '9', '1', '3', '5', '9', '9', '3', '5', '9', '1', '3', '4', '0', '9', '1', '4', '9', '2', '1', '1', '3', '0', '0', '7', '6', '2', '5', '2', '2', '6', '5', '6', '3'])) := by
  rfl

attribute [local simp] simplex72_lookup_max_bound

theorem simplex72_lookup_jensen_bound :
    rawSimplex72.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '7', '7', '1', '1', '3', '9', '4', '5', '6', '2', '5', '0', '7', '0', '6', '2', '9', '3', '3', '2', '3', '7', '1', '5', '4', '0', '7', '4', '8', '0', '5', '1', '4', '7', '4', '0', '3', '1', '1', '1', '4', '8', '8', '3', '3', '0', '2', '1', '7', '4', '9', '1', '9', '1', '7', '4', '2', '2', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '3', '0', '8', '0', '8', '7', '3', '6', '8', '1', '1', '4', '5', '5', '3', '1', '7', '9', '0', '8', '3', '4', '0', '4', '4', '5', '0', '6', '0', '6', '8', '4', '1', '7', '7', '6', '2', '1', '5', '7', '5', '0', '5', '1', '8', '0', '5', '4', '7', '4', '0', '3', '5', '1', '8', '9', '0', '7', '0', '1', '0', '5', '1', '4', '0', '1', '1', '8', '5', '8', '7', '0', '9', '9', '0', '4', '3', '3', '4', '9', '7', '5', '7', '3', '8', '8', '9', '1', '0', '3', '7', '1', '2', '3', '1', '4', '0', '7', '0', '1', '9'])) := by
  rfl

attribute [local simp] simplex72_lookup_jensen_bound

theorem simplex72_lookup_max_floor_Q96 :
    rawSimplex72.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '9', '4', '6', '3', '7', '6', '3', '5', '5', '6', '7', '4', '6', '2', '3'])) := by
  rfl

attribute [local simp] simplex72_lookup_max_floor_Q96

theorem simplex72_lookup_jensen_floor_Q96 :
    rawSimplex72.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '3', '4', '2', '8', '1', '6', '5', '1', '6', '2', '9', '1', '8', '8', '6', '1'])) := by
  rfl

attribute [local simp] simplex72_lookup_jensen_floor_Q96

theorem simplex72_decoded : decodeSimplex rawSimplex72 = .ok simplex72 := by
  unfold decodeSimplex simplex72
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
