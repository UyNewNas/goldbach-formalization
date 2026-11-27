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

theorem simplex42_lookup_simplex_id :
    rawSimplex42.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '2'])) := by
  rfl

attribute [local simp] simplex42_lookup_simplex_id

theorem simplex42_lookup_vertex_ids :
    rawSimplex42.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex42_lookup_vertex_ids

theorem simplex42_lookup_physical_volume :
    rawSimplex42.getObjVal? "physical_volume" = .ok (.str (String.ofList ['3', '6', '7', '6', '6', '5', '4', '9', '4', '6', '8', '1', '5', '3', '5', '4', '9', '9', '5', '8', '6', '5', '7', '3', '8', '1', '8', '2', '4', '9', '7', '8', '8', '9', '9', '4', '5', '6', '4', '1', '6', '7', '0', '4', '8', '1', '0', '1', '5', '1', '/', '7', '0', '3', '4', '8', '0', '3', '2', '5', '3', '6', '7', '3', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex42_lookup_physical_volume

theorem simplex42_lookup_mean_gap :
    rawSimplex42.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex42_lookup_mean_gap

theorem simplex42_lookup_factor_maxima :
    rawSimplex42.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '0', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '8', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex42_lookup_factor_maxima

theorem simplex42_lookup_gap_weighted_means :
    rawSimplex42.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['7', '5', '3', '5', '4', '7', '7', '4', '4', '4', '1', '4', '1', '3', '/', '1', '0', '6', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '2', '5', '6', '2', '6', '8', '6', '8', '2', '6', '1', '/', '1', '3', '2', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '7', '3', '6', '0', '0', '0', '1', '6', '6', '5', '7', '9', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '7', '9', '3', '8', '0', '1', '0', '7', '6', '7', '7', '3', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '9', '1', '8', '2', '8', '8', '4', '6', '4', '8', '1', '/', '1', '5', '9', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '1', '4', '7', '9', '7', '8', '5', '2', '5', '4', '9', '1', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '5', '8', '1', '5', '8', '0', '5', '5', '5', '3', '7', '/', '1', '0', '6', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '8', '7', '7', '2', '1', '9', '8', '7', '1', '7', '1', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '2', '0', '3', '0', '2', '2', '7', '5', '9', '5', '7', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '0', '5', '7', '5', '5', '1', '3', '7', '4', '2', '1', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex42_lookup_gap_weighted_means

theorem simplex42_lookup_max_bound :
    rawSimplex42.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '8', '5', '0', '1', '5', '0', '0', '0', '0', '8', '5', '7', '4', '1', '2', '5', '7', '1', '5', '1', '5', '1', '3', '4', '0', '7', '0', '6', '7', '2', '5', '2', '9', '1', '1', '5', '0', '4', '2', '7', '1', '2', '6', '0', '9', '6', '7', '7', '8', '6', '2', '8', '7', '7', '1', '7', '7', '9', '6', '8', '7', '5', '/', '1', '2', '3', '6', '9', '7', '0', '7', '0', '9', '2', '0', '3', '4', '4', '7', '6', '4', '4', '3', '1', '3', '1', '1', '5', '6', '3', '2', '2', '8', '3', '3', '6', '3', '3', '3', '6', '0', '6', '5', '9', '8', '9', '4', '6', '1', '6', '0', '1', '2', '4', '1', '7', '6', '0', '2', '3', '1', '9', '1', '8', '5', '0', '6', '7', '7', '2', '1', '8', '1', '8', '1', '1', '2'])) := by
  rfl

attribute [local simp] simplex42_lookup_max_bound

theorem simplex42_lookup_jensen_bound :
    rawSimplex42.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '6', '7', '5', '2', '2', '8', '7', '0', '8', '3', '6', '9', '6', '8', '0', '0', '5', '5', '3', '6', '1', '6', '8', '1', '3', '6', '7', '1', '2', '5', '5', '7', '0', '4', '4', '6', '5', '4', '3', '2', '7', '5', '1', '4', '5', '4', '1', '3', '5', '3', '1', '5', '3', '7', '2', '9', '3', '9', '9', '9', '9', '0', '5', '3', '1', '9', '5', '3', '8', '7', '5', '9', '6', '9', '1', '1', '4', '9', '7', '2', '4', '4', '6', '4', '1', '9', '1', '4', '1', '3', '3', '5', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '2', '4', '9', '4', '1', '8', '0', '8', '4', '8', '9', '4', '0', '1', '4', '2', '9', '4', '6', '3', '7', '5', '0', '4', '3', '9', '1', '0', '7', '4', '2', '1', '8', '8', '0', '5', '1', '4', '1', '7', '1', '7', '0', '2', '6', '1', '7', '5', '5', '0', '1', '7', '4', '0', '1', '7', '4', '1', '5', '0', '5', '4', '6', '8', '7', '2', '4', '9', '3', '2', '6', '0', '0', '9', '2', '0', '7', '3', '9', '9', '2', '2', '3', '6', '1', '6', '9', '3', '9', '0', '5', '4', '4', '1', '5', '9', '2', '7', '7', '5', '4', '5', '0', '8', '2', '7', '4', '3', '1', '0', '7', '9', '2', '5', '7', '9', '8', '8', '4', '8', '8', '7', '2', '8', '9', '4', '6', '4', '1', '9', '1', '9'])) := by
  rfl

attribute [local simp] simplex42_lookup_jensen_bound

theorem simplex42_lookup_max_floor_Q96 :
    rawSimplex42.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['5', '0', '2', '8', '0', '3', '3', '0', '4', '3', '9', '6', '5', '8', '7', '1', '8', '2', '6'])) := by
  rfl

attribute [local simp] simplex42_lookup_max_floor_Q96

theorem simplex42_lookup_jensen_floor_Q96 :
    rawSimplex42.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['5', '5', '0', '1', '1', '4', '0', '3', '9', '6', '9', '9', '8', '7', '2', '5', '5', '0', '6', '8'])) := by
  rfl

attribute [local simp] simplex42_lookup_jensen_floor_Q96

theorem simplex42_decoded : decodeSimplex rawSimplex42 = .ok simplex42 := by
  unfold decodeSimplex simplex42
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
