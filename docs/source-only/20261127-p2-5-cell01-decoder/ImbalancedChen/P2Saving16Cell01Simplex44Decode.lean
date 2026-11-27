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

theorem simplex44_lookup_simplex_id :
    rawSimplex44.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '4'])) := by
  rfl

attribute [local simp] simplex44_lookup_simplex_id

theorem simplex44_lookup_vertex_ids :
    rawSimplex44.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex44_lookup_vertex_ids

theorem simplex44_lookup_physical_volume :
    rawSimplex44.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '0', '9', '0', '9', '7', '5', '4', '4', '1', '2', '4', '4', '8', '6', '6', '2', '4', '8', '3', '5', '7', '4', '3', '1', '6', '7', '5', '7', '6', '6', '7', '7', '5', '4', '6', '1', '0', '6', '9', '1', '4', '2', '5', '1', '3', '/', '2', '9', '1', '2', '5', '9', '2', '8', '1', '3', '0', '9', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex44_lookup_physical_volume

theorem simplex44_lookup_mean_gap :
    rawSimplex44.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex44_lookup_mean_gap

theorem simplex44_lookup_factor_maxima :
    rawSimplex44.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '8', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex44_lookup_factor_maxima

theorem simplex44_lookup_gap_weighted_means :
    rawSimplex44.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '0', '2', '0', '3', '6', '1', '0', '3', '5', '7', '1', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '3', '8', '8', '4', '7', '7', '8', '7', '/', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '5', '2', '5', '1', '3', '9', '5', '8', '1', '3', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '3', '1', '6', '7', '2', '3', '6', '9', '9', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '6', '5', '7', '4', '9', '9', '1', '4', '3', '/', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '6', '8', '2', '7', '7', '2', '2', '1', '3', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '4', '0', '6', '9', '2', '6', '1', '5', '1', '/', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '9', '8', '9', '7', '8', '1', '5', '7', '3', '/', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '3', '0', '5', '5', '8', '9', '0', '5', '9', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '5', '8', '8', '6', '7', '9', '7', '8', '7', '/', '1', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex44_lookup_gap_weighted_means

theorem simplex44_lookup_max_bound :
    rawSimplex44.getObjVal? "max_bound" = .ok (.str (String.ofList ['3', '8', '4', '1', '3', '2', '1', '5', '0', '8', '7', '4', '1', '8', '2', '6', '9', '4', '3', '1', '0', '4', '5', '1', '3', '0', '9', '0', '9', '8', '2', '0', '7', '0', '4', '7', '3', '7', '5', '5', '7', '2', '1', '4', '4', '9', '2', '1', '8', '7', '5', '/', '3', '4', '3', '3', '4', '6', '0', '2', '0', '1', '9', '5', '7', '9', '6', '6', '5', '9', '2', '8', '0', '0', '5', '3', '0', '5', '4', '0', '5', '7', '1', '8', '9', '6', '3', '0', '0', '9', '9', '5', '5', '4', '0', '4', '5', '2', '7', '6', '4', '6', '5', '2', '4', '0', '9', '4', '1', '3', '2', '2', '2', '4'])) := by
  rfl

attribute [local simp] simplex44_lookup_max_bound

theorem simplex44_lookup_jensen_bound :
    rawSimplex44.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '2', '9', '0', '9', '9', '0', '7', '6', '1', '2', '4', '7', '7', '2', '0', '9', '1', '4', '8', '8', '4', '7', '0', '4', '4', '5', '5', '3', '8', '5', '1', '3', '6', '2', '9', '1', '4', '9', '2', '2', '2', '6', '8', '1', '8', '1', '9', '8', '6', '1', '6', '0', '6', '2', '5', '2', '0', '5', '8', '2', '9', '8', '6', '1', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '4', '1', '3', '8', '9', '5', '8', '6', '3', '3', '3', '8', '8', '1', '1', '5', '4', '4', '1', '8', '6', '8', '8', '3', '5', '1', '3', '8', '3', '4', '6', '5', '5', '3', '2', '8', '7', '6', '1', '0', '4', '2', '0', '3', '4', '2', '4', '3', '9', '8', '0', '3', '9', '8', '9', '4', '4', '2', '5', '4', '0', '9', '8', '2', '7', '2', '3', '1', '7', '2', '1', '8', '4', '5', '8', '9', '2', '9', '7', '5', '3', '5', '7', '8', '8', '3', '3', '2', '2', '5', '8', '5', '2', '3', '4', '5', '5', '2', '4', '6', '6', '1', '9', '3'])) := by
  rfl

attribute [local simp] simplex44_lookup_jensen_bound

theorem simplex44_lookup_max_floor_Q96 :
    rawSimplex44.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['8', '8', '6', '3', '9', '6', '8', '9', '0', '7', '8', '2', '6', '0', '7', '5', '6', '4'])) := by
  rfl

attribute [local simp] simplex44_lookup_max_floor_Q96

theorem simplex44_lookup_jensen_floor_Q96 :
    rawSimplex44.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '6', '2', '5', '1', '3', '9', '3', '9', '8', '6', '2', '1', '3', '1', '5', '9', '6', '9'])) := by
  rfl

attribute [local simp] simplex44_lookup_jensen_floor_Q96

theorem simplex44_decoded : decodeSimplex rawSimplex44 = .ok simplex44 := by
  unfold decodeSimplex simplex44
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
