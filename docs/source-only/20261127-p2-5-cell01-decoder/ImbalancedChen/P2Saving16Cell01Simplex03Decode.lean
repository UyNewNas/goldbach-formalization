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

theorem simplex03_lookup_simplex_id :
    rawSimplex03.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3'])) := by
  rfl

attribute [local simp] simplex03_lookup_simplex_id

theorem simplex03_lookup_vertex_ids :
    rawSimplex03.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['3']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_vertex_ids

theorem simplex03_lookup_physical_volume :
    rawSimplex03.getObjVal? "physical_volume" = .ok (.str (String.ofList ['9', '7', '2', '7', '0', '9', '2', '9', '3', '6', '1', '9', '5', '9', '5', '5', '5', '7', '9', '6', '5', '3', '2', '3', '5', '9', '4', '1', '1', '1', '0', '4', '6', '4', '0', '5', '5', '1', '2', '3', '4', '5', '9', '/', '6', '0', '4', '1', '3', '5', '4', '6', '2', '4', '0', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_physical_volume

theorem simplex03_lookup_mean_gap :
    rawSimplex03.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_mean_gap

theorem simplex03_lookup_factor_maxima :
    rawSimplex03.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_factor_maxima

theorem simplex03_lookup_gap_weighted_means :
    rawSimplex03.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '2', '7', '3', '8', '8', '2', '3', '7', '6', '4', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '9', '3', '7', '7', '2', '1', '0', '9', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '2', '6', '8', '7', '9', '7', '0', '4', '6', '8', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '8', '9', '8', '0', '2', '1', '7', '8', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '7', '8', '7', '7', '3', '2', '7', '1', '0', '9', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '7', '4', '3', '9', '5', '0', '1', '1', '1', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '0', '9', '7', '5', '5', '5', '4', '3', '/', '1', '8', '5', '8', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '8', '0', '7', '2', '4', '9', '4', '3', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '9', '7', '0', '6', '6', '9', '9', '1', '1', '2', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '0', '2', '6', '9', '0', '6', '6', '6', '6', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_gap_weighted_means

theorem simplex03_lookup_max_bound :
    rawSimplex03.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '7', '8', '0', '8', '9', '9', '7', '4', '0', '5', '9', '5', '8', '6', '6', '1', '6', '6', '3', '1', '3', '5', '1', '3', '0', '8', '9', '1', '3', '8', '5', '2', '3', '3', '3', '2', '1', '8', '9', '4', '2', '1', '9', '2', '5', '0', '0', '0', '7', '8', '1', '2', '5', '/', '8', '5', '3', '3', '8', '3', '8', '0', '7', '0', '6', '9', '4', '7', '3', '6', '6', '2', '6', '8', '9', '6', '0', '5', '6', '4', '5', '9', '9', '7', '9', '5', '8', '2', '2', '2', '8', '2', '7', '5', '8', '6', '0', '2', '1', '4', '9', '7', '5', '5', '4', '3', '6', '7', '2', '3', '1', '2', '1', '1', '4', '1', '9', '0', '4', '2', '8', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_bound

theorem simplex03_lookup_jensen_bound :
    rawSimplex03.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '0', '1', '1', '1', '5', '1', '4', '2', '1', '0', '9', '2', '8', '7', '8', '2', '4', '9', '2', '2', '4', '6', '0', '0', '2', '9', '0', '9', '5', '6', '3', '5', '6', '0', '5', '3', '0', '2', '7', '0', '5', '2', '0', '0', '5', '4', '2', '1', '4', '9', '7', '3', '8', '9', '0', '2', '4', '7', '8', '4', '1', '1', '8', '3', '9', '6', '2', '4', '9', '3', '2', '3', '1', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '6', '8', '1', '4', '8', '9', '6', '8', '6', '7', '7', '5', '2', '0', '9', '3', '9', '9', '4', '5', '0', '1', '7', '3', '6', '2', '2', '7', '9', '8', '7', '5', '6', '4', '1', '3', '7', '9', '4', '8', '4', '9', '9', '5', '9', '6', '6', '9', '0', '6', '7', '5', '2', '3', '4', '1', '8', '2', '8', '0', '5', '4', '3', '8', '2', '5', '9', '3', '3', '7', '0', '9', '9', '6', '0', '9', '1', '5', '7', '1', '5', '4', '8', '0', '2', '7', '9', '9', '5', '5', '7', '5', '1', '8', '9', '6', '3', '2', '4', '7', '7', '6', '5', '2', '8', '8', '7', '6', '1', '9', '2', '2', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_bound

theorem simplex03_lookup_max_floor_Q96 :
    rawSimplex03.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '6', '5', '3', '3', '8', '7', '5', '2', '5', '0', '5', '8', '2', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_floor_Q96

theorem simplex03_lookup_jensen_floor_Q96 :
    rawSimplex03.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '7', '2', '4', '0', '5', '4', '2', '8', '4', '3', '2', '0', '6', '9', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_floor_Q96

theorem simplex03_decoded : decodeSimplex rawSimplex03 = .ok simplex03 := by
  unfold decodeSimplex simplex03
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
