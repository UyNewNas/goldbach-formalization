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

theorem simplex47_lookup_simplex_id :
    rawSimplex47.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4', '7'])) := by
  rfl

attribute [local simp] simplex47_lookup_simplex_id

theorem simplex47_lookup_vertex_ids :
    rawSimplex47.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '7']), .number (String.ofList ['2', '4']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex47_lookup_vertex_ids

theorem simplex47_lookup_physical_volume :
    rawSimplex47.getObjVal? "physical_volume" = .ok (.str (String.ofList ['3', '9', '4', '7', '3', '7', '8', '3', '2', '2', '7', '0', '3', '8', '9', '7', '2', '1', '8', '2', '2', '1', '4', '8', '1', '9', '0', '5', '0', '0', '8', '2', '6', '8', '9', '/', '6', '0', '3', '8', '3', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex47_lookup_physical_volume

theorem simplex47_lookup_mean_gap :
    rawSimplex47.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '0', '8', '3', '/', '3', '9', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex47_lookup_mean_gap

theorem simplex47_lookup_factor_maxima :
    rawSimplex47.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '1', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex47_lookup_factor_maxima

theorem simplex47_lookup_gap_weighted_means :
    rawSimplex47.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '5', '0', '3', '7', '2', '3', '7', '9', '9', '0', '3', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '3', '5', '2', '1', '8', '7', '5', '9', '0', '3', '/', '3', '2', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '5', '6', '1', '1', '4', '7', '0', '7', '4', '9', '7', '/', '9', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '8', '5', '9', '5', '9', '6', '8', '5', '1', '/', '4', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '4', '4', '8', '3', '4', '2', '2', '1', '5', '9', '/', '4', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '5', '8', '9', '4', '4', '7', '3', '7', '/', '8', '1', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '7', '3', '2', '9', '3', '8', '0', '7', '/', '4', '9', '1', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '9', '4', '7', '2', '4', '4', '9', '1', '/', '2', '4', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '8', '0', '0', '5', '6', '9', '4', '1', '7', '1', '/', '9', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '0', '3', '4', '5', '7', '8', '3', '9', '0', '3', '/', '9', '8', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex47_lookup_gap_weighted_means

theorem simplex47_lookup_max_bound :
    rawSimplex47.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '0', '7', '1', '7', '5', '8', '0', '9', '8', '1', '7', '9', '0', '3', '2', '3', '3', '8', '6', '9', '9', '2', '0', '6', '7', '1', '6', '1', '9', '0', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '8', '7', '7', '9', '7', '2', '0', '5', '8', '8', '2', '2', '1', '0', '2', '4', '7', '4', '7', '7', '2', '0', '3', '0', '2', '6', '3', '6', '7', '9', '9', '0', '3', '5', '3', '6', '7', '2', '1', '4', '8', '8', '8', '0', '5', '0', '2', '4', '4', '8', '4', '2', '0', '9', '3'])) := by
  rfl

attribute [local simp] simplex47_lookup_max_bound

theorem simplex47_lookup_jensen_bound :
    rawSimplex47.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '0', '8', '8', '6', '0', '3', '1', '5', '2', '3', '1', '3', '0', '3', '1', '3', '5', '6', '3', '0', '3', '5', '5', '4', '2', '4', '3', '1', '6', '7', '3', '9', '9', '1', '8', '8', '1', '4', '2', '5', '6', '1', '7', '7', '5', '3', '1', '6', '2', '2', '9', '6', '5', '2', '0', '3', '1', '6', '9', '2', '9', '5', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '9', '2', '4', '0', '4', '3', '6', '7', '8', '1', '5', '3', '5', '8', '7', '7', '3', '9', '2', '0', '7', '0', '4', '1', '9', '4', '7', '0', '1', '1', '5', '5', '8', '7', '0', '9', '7', '0', '8', '3', '6', '9', '6', '3', '6', '6', '0', '0', '8', '6', '4', '4', '4', '2', '0', '4', '4', '0', '2', '8', '7', '4', '4', '2', '2', '5', '1', '8', '3', '6', '2', '3', '9', '2', '9', '0', '9', '1', '0', '7', '7', '0', '8', '3', '9', '7', '1', '1', '7', '6', '7', '0', '2', '3', '9', '1', '8', '0', '5', '5', '7', '2', '0', '3', '6', '3', '9'])) := by
  rfl

attribute [local simp] simplex47_lookup_jensen_bound

theorem simplex47_lookup_max_floor_Q96 :
    rawSimplex47.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '3', '4', '0', '6', '2', '0', '4', '9', '3', '8', '4', '2', '2', '3', '9', '4'])) := by
  rfl

attribute [local simp] simplex47_lookup_max_floor_Q96

theorem simplex47_lookup_jensen_floor_Q96 :
    rawSimplex47.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '1', '3', '0', '6', '9', '7', '9', '7', '9', '0', '8', '3', '7', '0', '0', '6', '6'])) := by
  rfl

attribute [local simp] simplex47_lookup_jensen_floor_Q96

theorem simplex47_decoded : decodeSimplex rawSimplex47 = .ok simplex47 := by
  unfold decodeSimplex simplex47
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
