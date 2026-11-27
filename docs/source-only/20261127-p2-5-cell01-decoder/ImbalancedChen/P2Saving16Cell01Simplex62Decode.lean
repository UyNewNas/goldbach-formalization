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

theorem simplex62_lookup_simplex_id :
    rawSimplex62.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '2'])) := by
  rfl

attribute [local simp] simplex62_lookup_simplex_id

theorem simplex62_lookup_vertex_ids :
    rawSimplex62.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['4'])]) := by
  rfl

attribute [local simp] simplex62_lookup_vertex_ids

theorem simplex62_lookup_physical_volume :
    rawSimplex62.getObjVal? "physical_volume" = .ok (.str (String.ofList ['5', '1', '4', '3', '8', '1', '6', '3', '8', '7', '3', '8', '3', '3', '7', '9', '4', '7', '2', '7', '4', '4', '2', '7', '8', '7', '1', '2', '9', '6', '6', '5', '4', '5', '4', '9', '5', '0', '0', '3', '1', '2', '3', '/', '8', '6', '1', '4', '5', '2', '4', '1', '8', '6', '1', '3', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex62_lookup_physical_volume

theorem simplex62_lookup_mean_gap :
    rawSimplex62.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex62_lookup_mean_gap

theorem simplex62_lookup_factor_maxima :
    rawSimplex62.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '6', '8', '7', '1', '/', '1', '3', '2', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex62_lookup_factor_maxima

theorem simplex62_lookup_gap_weighted_means :
    rawSimplex62.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['6', '2', '7', '4', '3', '4', '8', '7', '1', '5', '7', '3', '/', '9', '0', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '2', '7', '7', '3', '1', '2', '9', '1', '2', '3', '/', '9', '0', '8', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '9', '5', '4', '4', '4', '5', '8', '7', '6', '3', '8', '1', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '8', '4', '1', '2', '5', '8', '4', '9', '8', '1', '/', '1', '6', '3', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '6', '4', '3', '0', '3', '6', '0', '9', '4', '9', '/', '1', '6', '3', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '1', '2', '0', '4', '6', '7', '8', '1', '6', '3', '/', '4', '0', '8', '8', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '6', '2', '6', '3', '0', '1', '8', '7', '/', '2', '7', '2', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '4', '8', '8', '5', '4', '3', '1', '5', '3', '5', '7', '/', '1', '6', '3', '5', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '1', '8', '7', '2', '8', '5', '4', '1', '1', '1', '3', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '8', '5', '0', '9', '9', '6', '1', '8', '5', '6', '9', '/', '8', '1', '7', '7', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex62_lookup_gap_weighted_means

theorem simplex62_lookup_max_bound :
    rawSimplex62.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '5', '8', '6', '1', '2', '8', '0', '3', '1', '4', '3', '4', '1', '3', '7', '0', '4', '6', '0', '0', '4', '0', '8', '0', '0', '9', '7', '0', '7', '0', '1', '4', '9', '9', '6', '0', '5', '1', '9', '2', '8', '2', '2', '6', '9', '0', '7', '5', '0', '0', '0', '0', '/', '1', '0', '7', '3', '4', '5', '8', '5', '1', '4', '1', '5', '6', '3', '9', '4', '4', '9', '9', '6', '7', '4', '1', '3', '2', '3', '7', '5', '9', '2', '5', '1', '7', '8', '0', '7', '8', '8', '8', '6', '8', '6', '0', '0', '0', '5', '2', '7', '5', '4', '7', '5', '2', '2', '2', '3', '0', '4', '5', '8', '8', '2', '2', '5', '9', '1'])) := by
  rfl

attribute [local simp] simplex62_lookup_max_bound

theorem simplex62_lookup_jensen_bound :
    rawSimplex62.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['9', '6', '6', '6', '7', '5', '9', '2', '6', '8', '5', '0', '5', '5', '0', '3', '5', '9', '5', '9', '8', '5', '8', '7', '6', '0', '0', '3', '3', '3', '0', '3', '8', '5', '5', '1', '1', '5', '7', '5', '2', '8', '3', '8', '8', '2', '9', '1', '6', '3', '0', '5', '8', '3', '2', '0', '8', '4', '6', '1', '6', '2', '3', '7', '1', '6', '7', '1', '3', '6', '8', '0', '9', '4', '7', '9', '4', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '2', '4', '4', '7', '5', '8', '8', '9', '2', '7', '9', '7', '1', '6', '2', '1', '4', '0', '2', '6', '2', '0', '5', '8', '6', '5', '6', '5', '9', '1', '3', '6', '3', '1', '3', '3', '8', '8', '5', '4', '4', '6', '3', '2', '4', '6', '2', '4', '8', '7', '1', '2', '4', '9', '7', '3', '2', '6', '2', '6', '0', '6', '8', '6', '4', '5', '2', '6', '7', '1', '3', '0', '9', '1', '2', '7', '7', '3', '4', '6', '2', '5', '5', '7', '3', '5', '9', '6', '3', '8', '9', '3', '6', '4', '2', '1', '2', '5', '2', '0', '0', '5', '5', '3', '8', '2', '7', '4', '2', '1', '6', '3', '6', '4', '6', '9'])) := by
  rfl

attribute [local simp] simplex62_lookup_jensen_bound

theorem simplex62_lookup_max_floor_Q96 :
    rawSimplex62.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '1', '7', '0', '6', '6', '4', '7', '9', '7', '8', '0', '6', '8', '5', '2', '4'])) := by
  rfl

attribute [local simp] simplex62_lookup_max_floor_Q96

theorem simplex62_lookup_jensen_floor_Q96 :
    rawSimplex62.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '1', '4', '1', '4', '1', '7', '2', '7', '9', '6', '7', '3', '3', '6', '1', '8'])) := by
  rfl

attribute [local simp] simplex62_lookup_jensen_floor_Q96

theorem simplex62_decoded : decodeSimplex rawSimplex62 = .ok simplex62 := by
  unfold decodeSimplex simplex62
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
