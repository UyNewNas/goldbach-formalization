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

theorem simplex56_lookup_simplex_id :
    rawSimplex56.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5', '6'])) := by
  rfl

attribute [local simp] simplex56_lookup_simplex_id

theorem simplex56_lookup_vertex_ids :
    rawSimplex56.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex56_lookup_vertex_ids

theorem simplex56_lookup_physical_volume :
    rawSimplex56.getObjVal? "physical_volume" = .ok (.str (String.ofList ['5', '8', '1', '1', '9', '4', '6', '4', '2', '3', '2', '1', '4', '5', '0', '0', '5', '2', '2', '7', '3', '6', '3', '9', '6', '3', '6', '2', '5', '7', '5', '1', '4', '2', '5', '4', '8', '2', '8', '2', '5', '5', '4', '4', '4', '7', '3', '3', '/', '2', '6', '9', '4', '4', '4', '4', '1', '6', '2', '3', '2', '2', '2', '6', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex56_lookup_physical_volume

theorem simplex56_lookup_mean_gap :
    rawSimplex56.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex56_lookup_mean_gap

theorem simplex56_lookup_factor_maxima :
    rawSimplex56.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex56_lookup_factor_maxima

theorem simplex56_lookup_gap_weighted_means :
    rawSimplex56.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '0', '9', '6', '1', '0', '2', '8', '7', '2', '4', '5', '1', '8', '1', '/', '1', '6', '5', '7', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '4', '0', '8', '8', '2', '2', '0', '5', '4', '5', '3', '1', '/', '1', '6', '5', '7', '7', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '1', '5', '5', '5', '2', '6', '6', '5', '6', '5', '1', '0', '9', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '5', '5', '5', '5', '0', '1', '8', '2', '9', '5', '5', '9', '3', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '2', '6', '2', '0', '5', '2', '3', '1', '6', '2', '9', '7', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '0', '3', '5', '7', '7', '4', '2', '1', '4', '9', '0', '1', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '3', '8', '8', '4', '9', '0', '4', '7', '0', '0', '3', '1', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '2', '3', '0', '2', '5', '3', '5', '5', '5', '9', '1', '1', '/', '9', '9', '4', '6', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '5', '9', '7', '7', '8', '6', '7', '9', '1', '8', '6', '7', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '4', '1', '6', '3', '9', '2', '3', '0', '4', '6', '4', '1', '/', '4', '9', '7', '3', '3', '4', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex56_lookup_gap_weighted_means

theorem simplex56_lookup_max_bound :
    rawSimplex56.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '2', '6', '6', '2', '6', '6', '0', '6', '6', '8', '4', '7', '5', '1', '8', '5', '7', '8', '3', '0', '0', '2', '9', '0', '8', '8', '3', '0', '6', '9', '0', '4', '4', '2', '8', '4', '5', '6', '7', '0', '6', '1', '5', '0', '9', '7', '3', '0', '7', '5', '9', '2', '3', '0', '7', '0', '3', '1', '2', '5', '0', '/', '3', '1', '1', '6', '5', '4', '0', '2', '8', '7', '7', '3', '8', '6', '6', '7', '6', '5', '3', '8', '3', '2', '0', '5', '6', '8', '2', '0', '7', '9', '5', '5', '6', '6', '0', '8', '3', '2', '9', '5', '8', '1', '8', '4', '1', '5', '8', '3', '5', '0', '1', '0', '6', '2', '7', '7', '7', '5', '4', '0', '9', '6', '0', '1', '6', '9', '4', '9', '2', '1', '4', '3', '1'])) := by
  rfl

attribute [local simp] simplex56_lookup_max_bound

theorem simplex56_lookup_jensen_bound :
    rawSimplex56.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '9', '4', '4', '0', '9', '2', '1', '2', '3', '6', '2', '7', '0', '3', '3', '6', '4', '2', '5', '1', '3', '2', '1', '8', '5', '0', '8', '7', '3', '2', '2', '6', '8', '2', '6', '3', '4', '8', '2', '3', '6', '7', '5', '4', '4', '8', '2', '6', '1', '5', '7', '3', '7', '0', '7', '3', '0', '8', '4', '2', '4', '8', '3', '9', '9', '4', '5', '0', '2', '8', '8', '0', '2', '0', '7', '4', '8', '5', '3', '3', '9', '2', '8', '5', '2', '7', '6', '2', '5', '3', '8', '3', '2', '7', '2', '4', '9', '0', '2', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '6', '0', '4', '2', '8', '1', '4', '2', '8', '6', '0', '3', '8', '9', '3', '4', '3', '0', '8', '9', '6', '3', '9', '8', '4', '3', '8', '2', '3', '1', '2', '7', '7', '9', '1', '4', '1', '4', '0', '7', '0', '9', '0', '5', '6', '6', '9', '1', '6', '4', '3', '5', '2', '9', '9', '0', '3', '9', '7', '5', '7', '5', '7', '8', '9', '4', '6', '9', '2', '8', '4', '6', '7', '2', '3', '6', '9', '2', '2', '8', '7', '3', '1', '8', '8', '4', '5', '3', '2', '4', '2', '2', '5', '2', '8', '5', '5', '1', '1', '2', '5', '7', '4', '2', '2', '3', '1', '7', '8', '2', '6', '1', '8', '8', '2', '0', '2', '7', '7', '1', '6', '2', '2', '3', '1', '2', '6', '2', '0', '4', '0', '0', '9', '2', '2', '7', '0', '9'])) := by
  rfl

attribute [local simp] simplex56_lookup_jensen_bound

theorem simplex56_lookup_max_floor_Q96 :
    rawSimplex56.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '2', '1', '9', '0', '8', '0', '2', '7', '7', '1', '0', '0', '7', '2', '1', '0', '3'])) := by
  rfl

attribute [local simp] simplex56_lookup_max_floor_Q96

theorem simplex56_lookup_jensen_floor_Q96 :
    rawSimplex56.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '5', '4', '8', '9', '2', '5', '7', '0', '6', '1', '7', '7', '6', '8', '4', '2', '8', '5'])) := by
  rfl

attribute [local simp] simplex56_lookup_jensen_floor_Q96

theorem simplex56_decoded : decodeSimplex rawSimplex56 = .ok simplex56 := by
  unfold decodeSimplex simplex56
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
