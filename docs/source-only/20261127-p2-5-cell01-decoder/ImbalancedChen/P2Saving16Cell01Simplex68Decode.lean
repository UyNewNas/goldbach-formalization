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

theorem simplex68_lookup_simplex_id :
    rawSimplex68.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '8'])) := by
  rfl

attribute [local simp] simplex68_lookup_simplex_id

theorem simplex68_lookup_vertex_ids :
    rawSimplex68.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '9']), .number (String.ofList ['2', '8']), .number (String.ofList ['1', '8']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex68_lookup_vertex_ids

theorem simplex68_lookup_physical_volume :
    rawSimplex68.getObjVal? "physical_volume" = .ok (.str (String.ofList ['5', '4', '4', '7', '2', '6', '7', '7', '0', '6', '7', '1', '1', '1', '8', '2', '0', '5', '5', '9', '1', '0', '0', '9', '7', '9', '4', '7', '0', '0', '6', '6', '5', '8', '4', '0', '6', '5', '6', '1', '5', '2', '3', '/', '7', '0', '2', '3', '8', '6', '0', '7', '5', '0', '2', '6', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex68_lookup_physical_volume

theorem simplex68_lookup_mean_gap :
    rawSimplex68.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '2', '7', '1', '/', '1', '0', '0', '3', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex68_lookup_mean_gap

theorem simplex68_lookup_factor_maxima :
    rawSimplex68.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['4', '6', '4', '0', '5', '8', '3', '/', '8', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '0', '4', '6', '1', '6', '7', '/', '8', '9', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '3', '1', '1', '9', '/', '5', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex68_lookup_factor_maxima

theorem simplex68_lookup_gap_weighted_means :
    rawSimplex68.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '4', '7', '7', '3', '8', '7', '1', '3', '1', '5', '2', '9', '/', '1', '0', '0', '5', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '1', '9', '6', '4', '9', '6', '1', '9', '9', '2', '9', '/', '1', '0', '0', '5', '7', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '0', '7', '0', '3', '3', '7', '0', '6', '6', '8', '9', '/', '2', '8', '2', '8', '6', '1', '5', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '1', '0', '2', '2', '0', '1', '2', '5', '7', '3', '/', '2', '2', '6', '2', '8', '9', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '4', '8', '7', '9', '7', '4', '4', '4', '2', '4', '3', '/', '9', '0', '5', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '1', '4', '5', '8', '2', '4', '8', '3', '4', '4', '1', '/', '3', '6', '2', '0', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '5', '9', '2', '9', '8', '9', '7', '0', '3', '5', '3', '7', '/', '1', '2', '0', '6', '8', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '5', '2', '9', '0', '6', '0', '6', '0', '4', '9', '/', '9', '0', '5', '1', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '9', '3', '5', '0', '8', '5', '0', '0', '6', '5', '4', '7', '/', '4', '5', '2', '5', '7', '8', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '7', '5', '2', '3', '9', '8', '9', '5', '2', '5', '5', '1', '/', '4', '5', '2', '5', '7', '8', '5', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex68_lookup_gap_weighted_means

theorem simplex68_lookup_max_bound :
    rawSimplex68.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '1', '0', '4', '5', '4', '7', '4', '1', '1', '6', '7', '5', '7', '4', '1', '3', '2', '5', '6', '8', '0', '4', '5', '8', '2', '2', '4', '5', '7', '2', '7', '8', '7', '4', '8', '6', '2', '5', '4', '2', '9', '8', '2', '1', '8', '9', '3', '2', '0', '0', '0', '0', '0', '0', '0', '/', '4', '0', '7', '0', '8', '6', '5', '4', '4', '7', '2', '3', '2', '0', '4', '1', '1', '4', '0', '4', '3', '6', '1', '6', '7', '3', '7', '6', '7', '5', '2', '4', '2', '8', '9', '8', '7', '4', '1', '7', '3', '3', '5', '2', '7', '2', '2', '0', '3', '4', '8', '9', '8', '8', '4', '8', '0', '7', '5', '1', '1', '0', '0', '1', '1', '7', '9', '8', '4', '7', '1'])) := by
  rfl

attribute [local simp] simplex68_lookup_max_bound

theorem simplex68_lookup_jensen_bound :
    rawSimplex68.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '0', '2', '2', '7', '5', '7', '2', '0', '3', '9', '9', '0', '5', '3', '4', '0', '6', '3', '3', '3', '1', '9', '2', '6', '1', '7', '8', '8', '3', '7', '2', '2', '6', '1', '2', '4', '7', '3', '4', '2', '4', '9', '2', '2', '2', '7', '0', '7', '0', '8', '1', '4', '0', '2', '0', '0', '1', '2', '4', '8', '9', '7', '2', '5', '9', '5', '4', '4', '3', '6', '5', '5', '5', '6', '4', '9', '9', '1', '6', '6', '1', '4', '5', '0', '4', '0', '4', '6', '8', '2', '6', '1', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '2', '3', '7', '2', '9', '4', '6', '3', '8', '6', '8', '9', '3', '8', '2', '5', '0', '6', '1', '9', '5', '2', '0', '8', '3', '3', '4', '2', '1', '4', '1', '9', '5', '0', '6', '0', '5', '5', '3', '9', '2', '0', '7', '8', '2', '6', '9', '7', '7', '5', '5', '6', '7', '4', '7', '5', '6', '9', '7', '1', '4', '2', '9', '1', '6', '3', '4', '3', '8', '0', '7', '0', '6', '8', '0', '5', '8', '4', '8', '6', '2', '6', '9', '4', '5', '0', '9', '7', '1', '2', '5', '3', '3', '3', '6', '8', '5', '0', '4', '7', '7', '7', '6', '4', '3', '9', '7', '5', '2', '3', '7', '6', '3', '6', '8', '5', '2', '4', '5', '9', '1', '8', '4', '2', '0', '4', '3', '5', '9'])) := by
  rfl

attribute [local simp] simplex68_lookup_jensen_bound

theorem simplex68_lookup_max_floor_Q96 :
    rawSimplex68.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['9', '9', '3', '4', '5', '9', '2', '9', '5', '4', '1', '5', '9', '1'])) := by
  rfl

attribute [local simp] simplex68_lookup_max_floor_Q96

theorem simplex68_lookup_jensen_floor_Q96 :
    rawSimplex68.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '6', '7', '8', '6', '4', '5', '9', '0', '2', '3', '3', '0', '2', '3'])) := by
  rfl

attribute [local simp] simplex68_lookup_jensen_floor_Q96

theorem simplex68_decoded : decodeSimplex rawSimplex68 = .ok simplex68 := by
  unfold decodeSimplex simplex68
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
