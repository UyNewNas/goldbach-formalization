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

theorem simplex60_lookup_simplex_id :
    rawSimplex60.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '0'])) := by
  rfl

attribute [local simp] simplex60_lookup_simplex_id

theorem simplex60_lookup_vertex_ids :
    rawSimplex60.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex60_lookup_vertex_ids

theorem simplex60_lookup_physical_volume :
    rawSimplex60.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '0', '3', '1', '2', '1', '1', '2', '5', '2', '9', '8', '0', '2', '9', '9', '6', '8', '9', '0', '3', '2', '7', '5', '1', '4', '0', '0', '3', '2', '5', '7', '4', '3', '1', '8', '9', '7', '7', '3', '6', '5', '6', '1', '9', '7', '/', '4', '9', '2', '2', '5', '8', '5', '2', '4', '9', '2', '1', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex60_lookup_physical_volume

theorem simplex60_lookup_mean_gap :
    rawSimplex60.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex60_lookup_mean_gap

theorem simplex60_lookup_factor_maxima :
    rawSimplex60.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex60_lookup_factor_maxima

theorem simplex60_lookup_gap_weighted_means :
    rawSimplex60.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '7', '7', '8', '8', '8', '0', '9', '3', '5', '2', '3', '9', '/', '2', '7', '2', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '2', '4', '8', '9', '5', '7', '0', '7', '8', '8', '9', '/', '2', '7', '2', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '7', '6', '8', '7', '8', '1', '1', '6', '7', '7', '1', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '8', '5', '7', '5', '1', '9', '7', '8', '9', '8', '7', '/', '1', '6', '3', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '2', '9', '0', '9', '0', '9', '6', '6', '9', '4', '3', '/', '1', '6', '3', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '0', '1', '6', '6', '1', '3', '2', '2', '8', '7', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '7', '4', '7', '4', '1', '1', '1', '0', '8', '7', '/', '1', '3', '6', '2', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '4', '3', '6', '7', '8', '6', '7', '2', '7', '9', '/', '1', '6', '3', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '9', '6', '2', '9', '6', '3', '0', '0', '7', '2', '3', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '6', '2', '6', '6', '7', '3', '7', '8', '1', '7', '9', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex60_lookup_gap_weighted_means

theorem simplex60_lookup_max_bound :
    rawSimplex60.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '8', '8', '8', '0', '0', '8', '9', '5', '0', '8', '5', '3', '4', '7', '1', '3', '6', '4', '8', '9', '7', '9', '7', '2', '1', '3', '5', '6', '1', '3', '9', '4', '7', '0', '6', '5', '9', '7', '4', '3', '6', '7', '9', '5', '2', '0', '0', '7', '6', '7', '9', '6', '8', '7', '5', '/', '4', '5', '3', '5', '3', '1', '6', '2', '5', '8', '6', '9', '5', '6', '0', '7', '7', '6', '8', '8', '3', '8', '1', '0', '9', '9', '8', '0', '1', '6', '4', '3', '2', '5', '8', '2', '8', '7', '1', '0', '1', '1', '1', '5', '2', '6', '4', '2', '2', '3', '4', '8', '3', '1', '2', '6', '3', '0', '5', '3', '2', '1', '8', '1', '5', '9', '0', '2'])) := by
  rfl

attribute [local simp] simplex60_lookup_max_bound

theorem simplex60_lookup_jensen_bound :
    rawSimplex60.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['9', '1', '5', '6', '8', '2', '4', '7', '4', '5', '0', '2', '3', '6', '8', '0', '7', '9', '8', '0', '2', '9', '1', '9', '1', '2', '7', '0', '1', '9', '4', '7', '8', '7', '0', '8', '5', '8', '6', '0', '9', '1', '6', '1', '0', '9', '6', '3', '8', '4', '4', '4', '8', '3', '6', '7', '5', '5', '8', '1', '8', '8', '6', '3', '2', '2', '3', '0', '6', '1', '0', '9', '5', '8', '9', '1', '0', '2', '8', '2', '7', '8', '0', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '9', '7', '8', '1', '4', '1', '2', '4', '4', '0', '8', '5', '6', '2', '9', '6', '4', '7', '5', '5', '0', '9', '9', '4', '1', '7', '2', '9', '3', '4', '0', '6', '5', '6', '2', '3', '2', '9', '7', '8', '5', '3', '6', '2', '3', '9', '4', '3', '0', '0', '6', '9', '3', '0', '7', '5', '2', '8', '6', '3', '0', '5', '7', '0', '8', '5', '0', '6', '5', '3', '3', '6', '3', '2', '8', '1', '9', '3', '4', '7', '6', '8', '2', '7', '2', '9', '6', '5', '1', '0', '0', '1', '3', '9', '9', '8', '6', '5', '8', '3', '4', '6', '1', '0', '7', '8', '3', '3', '4', '7', '9', '5', '3', '3', '4', '2', '0', '3', '1'])) := by
  rfl

attribute [local simp] simplex60_lookup_jensen_bound

theorem simplex60_lookup_max_floor_Q96 :
    rawSimplex60.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '2', '9', '8', '1', '9', '2', '9', '2', '5', '3', '5', '1', '2', '7', '2', '2'])) := by
  rfl

attribute [local simp] simplex60_lookup_max_floor_Q96

theorem simplex60_lookup_jensen_floor_Q96 :
    rawSimplex60.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '4', '3', '6', '0', '1', '0', '7', '1', '7', '9', '4', '0', '6', '6', '2', '6', '3'])) := by
  rfl

attribute [local simp] simplex60_lookup_jensen_floor_Q96

theorem simplex60_decoded : decodeSimplex rawSimplex60 = .ok simplex60 := by
  unfold decodeSimplex simplex60
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
