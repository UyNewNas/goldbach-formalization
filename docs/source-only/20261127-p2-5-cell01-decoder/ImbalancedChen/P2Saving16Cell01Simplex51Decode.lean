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

theorem simplex51_lookup_simplex_id :
    rawSimplex51.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5', '1'])) := by
  rfl

attribute [local simp] simplex51_lookup_simplex_id

theorem simplex51_lookup_vertex_ids :
    rawSimplex51.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex51_lookup_vertex_ids

theorem simplex51_lookup_physical_volume :
    rawSimplex51.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '1', '7', '8', '8', '4', '8', '6', '5', '5', '7', '7', '7', '7', '1', '7', '8', '1', '9', '1', '7', '3', '6', '6', '2', '2', '8', '7', '8', '1', '9', '8', '4', '2', '9', '7', '8', '1', '6', '6', '0', '4', '1', '4', '9', '/', '6', '3', '4', '3', '4', '2', '2', '3', '5', '5', '2', '4', '3', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex51_lookup_physical_volume

theorem simplex51_lookup_mean_gap :
    rawSimplex51.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex51_lookup_mean_gap

theorem simplex51_lookup_factor_maxima :
    rawSimplex51.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '2', '8', '1', '2', '7', '/', '9', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex51_lookup_factor_maxima

theorem simplex51_lookup_gap_weighted_means :
    rawSimplex51.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '3', '9', '1', '3', '8', '7', '3', '1', '3', '3', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '5', '1', '6', '8', '8', '2', '1', '4', '7', '8', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '9', '9', '7', '5', '0', '3', '8', '9', '6', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '2', '2', '9', '9', '4', '8', '8', '4', '8', '3', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '4', '4', '7', '5', '8', '6', '0', '4', '0', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '4', '7', '5', '5', '3', '5', '1', '8', '9', '/', '1', '1', '1', '5', '1', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '5', '6', '9', '0', '5', '1', '4', '7', '/', '4', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '3', '1', '8', '8', '7', '2', '2', '8', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '8', '4', '6', '2', '8', '0', '7', '8', '9', '4', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '6', '7', '1', '7', '3', '7', '3', '2', '3', '8', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex51_lookup_gap_weighted_means

theorem simplex51_lookup_max_bound :
    rawSimplex51.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '5', '4', '4', '8', '9', '7', '8', '3', '7', '9', '0', '0', '7', '1', '1', '8', '4', '7', '3', '7', '7', '8', '1', '6', '1', '6', '0', '9', '1', '1', '0', '5', '4', '3', '0', '6', '1', '9', '1', '8', '8', '0', '6', '4', '2', '3', '1', '0', '8', '1', '2', '5', '0', '0', '0', '0', '/', '4', '9', '8', '8', '8', '3', '8', '1', '9', '4', '3', '2', '8', '7', '0', '5', '9', '3', '6', '5', '0', '4', '8', '2', '5', '4', '5', '4', '1', '0', '0', '1', '4', '6', '4', '9', '4', '1', '6', '9', '7', '2', '4', '4', '4', '9', '5', '4', '2', '1', '2', '4', '6', '0', '5', '4', '0', '1', '9', '4', '3', '8', '9', '4', '3', '7', '5', '3'])) := by
  rfl

attribute [local simp] simplex51_lookup_max_bound

theorem simplex51_lookup_jensen_bound :
    rawSimplex51.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '4', '9', '3', '4', '8', '2', '2', '0', '6', '9', '3', '5', '3', '0', '6', '7', '5', '5', '2', '7', '7', '9', '5', '1', '0', '3', '9', '9', '5', '9', '0', '7', '1', '7', '2', '5', '3', '7', '8', '8', '4', '1', '3', '7', '7', '2', '5', '9', '4', '8', '1', '4', '9', '8', '6', '7', '3', '3', '1', '2', '7', '7', '4', '0', '5', '2', '1', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '1', '0', '8', '5', '8', '1', '2', '1', '9', '9', '6', '7', '1', '7', '2', '3', '5', '4', '7', '6', '1', '5', '2', '9', '0', '6', '2', '5', '0', '7', '7', '3', '3', '1', '6', '7', '4', '9', '3', '9', '6', '0', '6', '7', '5', '4', '3', '5', '2', '1', '1', '7', '1', '4', '7', '1', '1', '3', '4', '9', '1', '3', '5', '6', '2', '6', '6', '0', '5', '0', '0', '9', '5', '1', '0', '3', '3', '2', '8', '9', '5', '8', '2', '5', '1', '7', '9', '6', '1', '8', '6', '4', '5', '9', '8', '9', '9', '0', '2', '5', '7', '0', '0', '3', '5', '0', '8', '9'])) := by
  rfl

attribute [local simp] simplex51_lookup_jensen_bound

theorem simplex51_lookup_max_floor_Q96 :
    rawSimplex51.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '4', '5', '3', '4', '6', '5', '3', '6', '0', '0', '9', '6', '7', '9', '4', '4', '1'])) := by
  rfl

attribute [local simp] simplex51_lookup_max_floor_Q96

theorem simplex51_lookup_jensen_floor_Q96 :
    rawSimplex51.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '1', '6', '4', '7', '2', '7', '0', '6', '0', '3', '0', '8', '8', '4', '8', '2', '1', '8'])) := by
  rfl

attribute [local simp] simplex51_lookup_jensen_floor_Q96

theorem simplex51_decoded : decodeSimplex rawSimplex51 = .ok simplex51 := by
  unfold decodeSimplex simplex51
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
