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

theorem simplex01_lookup_simplex_id :
    rawSimplex01.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1'])) := by
  rfl

attribute [local simp] simplex01_lookup_simplex_id

theorem simplex01_lookup_vertex_ids :
    rawSimplex01.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_vertex_ids

theorem simplex01_lookup_physical_volume :
    rawSimplex01.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '7', '0', '1', '2', '5', '2', '5', '3', '9', '8', '6', '3', '2', '9', '7', '0', '6', '6', '3', '6', '1', '0', '0', '3', '9', '8', '1', '8', '5', '6', '9', '3', '2', '6', '3', '5', '8', '6', '0', '7', '7', '3', '7', '6', '4', '2', '4', '4', '6', '3', '1', '/', '5', '9', '0', '5', '3', '2', '3', '4', '5', '5', '7', '5', '6', '3', '0', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_physical_volume

theorem simplex01_lookup_mean_gap :
    rawSimplex01.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_mean_gap

theorem simplex01_lookup_factor_maxima :
    rawSimplex01.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '6', '5', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_factor_maxima

theorem simplex01_lookup_gap_weighted_means :
    rawSimplex01.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '0', '5', '6', '3', '8', '4', '2', '8', '5', '3', '3', '5', '8', '4', '0', '3', '/', '4', '3', '5', '9', '9', '6', '6', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '2', '9', '9', '8', '5', '7', '5', '0', '8', '2', '1', '7', '4', '5', '3', '/', '4', '3', '5', '9', '9', '6', '6', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '8', '6', '0', '2', '0', '5', '5', '4', '8', '9', '3', '7', '4', '3', '6', '7', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '0', '2', '5', '2', '8', '5', '5', '7', '1', '1', '6', '3', '8', '4', '4', '9', '/', '2', '6', '1', '5', '9', '7', '9', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '3', '1', '3', '0', '7', '8', '6', '1', '7', '6', '7', '6', '4', '8', '1', '/', '2', '6', '1', '5', '9', '7', '9', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '2', '3', '8', '9', '6', '0', '7', '2', '5', '0', '5', '8', '9', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '9', '9', '8', '1', '8', '5', '1', '8', '8', '1', '2', '3', '9', '/', '2', '1', '7', '9', '9', '8', '3', '3', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '3', '9', '7', '2', '8', '3', '7', '2', '6', '6', '1', '1', '7', '1', '3', '/', '2', '6', '1', '5', '9', '7', '9', '9', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '2', '5', '6', '7', '8', '3', '5', '6', '6', '8', '7', '3', '0', '2', '1', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '1', '9', '4', '8', '1', '9', '4', '1', '7', '5', '5', '1', '9', '8', '3', '/', '1', '3', '0', '7', '9', '8', '9', '9', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_gap_weighted_means

theorem simplex01_lookup_max_bound :
    rawSimplex01.getObjVal? "max_bound" = .ok (.str (String.ofList ['2', '3', '5', '4', '1', '1', '9', '7', '2', '5', '2', '2', '8', '1', '1', '8', '8', '7', '4', '7', '7', '2', '9', '8', '4', '1', '1', '0', '8', '1', '2', '3', '3', '8', '6', '3', '7', '6', '0', '4', '1', '4', '2', '8', '3', '7', '4', '0', '1', '5', '4', '1', '5', '6', '1', '5', '1', '7', '8', '4', '3', '7', '5', '0', '0', '/', '3', '8', '9', '1', '2', '3', '8', '3', '2', '9', '6', '0', '0', '2', '5', '8', '5', '4', '0', '2', '0', '4', '1', '8', '2', '7', '6', '4', '2', '6', '6', '9', '6', '6', '4', '9', '2', '4', '1', '5', '8', '9', '3', '8', '9', '7', '9', '0', '6', '1', '4', '3', '8', '4', '9', '7', '6', '0', '0', '5', '5', '2', '4', '3', '3', '5', '0', '7', '3', '9', '3', '9', '4', '6', '1'])) := by
  rfl

attribute [local simp] simplex01_lookup_max_bound

theorem simplex01_lookup_jensen_bound :
    rawSimplex01.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '6', '6', '5', '3', '1', '3', '4', '9', '2', '1', '7', '1', '1', '7', '8', '2', '1', '5', '4', '4', '1', '8', '3', '4', '5', '4', '3', '1', '1', '2', '0', '4', '1', '7', '3', '1', '4', '1', '0', '9', '2', '2', '1', '2', '5', '4', '2', '4', '7', '5', '9', '1', '2', '4', '2', '1', '1', '9', '3', '6', '1', '9', '3', '6', '0', '3', '9', '2', '0', '0', '3', '4', '2', '5', '8', '3', '4', '5', '6', '6', '9', '3', '7', '1', '6', '5', '2', '9', '5', '2', '9', '1', '0', '8', '1', '2', '6', '5', '9', '1', '5', '4', '3', '8', '1', '0', '7', '7', '0', '0', '9', '8', '7', '8', '1', '1', '6', '6', '5', '1', '6', '2', '0', '4', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '2', '0', '3', '3', '4', '3', '9', '1', '2', '6', '4', '2', '4', '6', '8', '3', '7', '5', '3', '0', '3', '4', '2', '4', '5', '0', '1', '3', '6', '8', '2', '2', '8', '0', '8', '5', '9', '7', '7', '0', '0', '8', '1', '3', '7', '2', '8', '6', '8', '3', '9', '2', '7', '6', '0', '4', '5', '5', '7', '3', '8', '2', '4', '5', '4', '0', '5', '7', '9', '9', '5', '2', '0', '6', '4', '6', '1', '3', '0', '7', '2', '1', '6', '6', '0', '5', '7', '9', '0', '1', '7', '5', '5', '8', '0', '5', '4', '3', '5', '5', '5', '2', '4', '1', '9', '9', '7', '6', '0', '9', '0', '6', '8', '1', '9', '7', '1', '4', '3', '6', '8', '7', '7', '4', '3', '1', '5', '5', '7', '2', '4', '4', '2', '8', '3', '4', '2', '4', '3', '1', '9', '6', '8', '1', '5', '3', '1', '0', '9', '3', '4', '3', '4', '9', '3', '5', '8', '0', '1', '1'])) := by
  rfl

attribute [local simp] simplex01_lookup_jensen_bound

theorem simplex01_lookup_max_floor_Q96 :
    rawSimplex01.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '7', '9', '3', '1', '4', '2', '0', '3', '7', '8', '3', '4', '7', '4', '9', '7', '9', '8'])) := by
  rfl

attribute [local simp] simplex01_lookup_max_floor_Q96

theorem simplex01_lookup_jensen_floor_Q96 :
    rawSimplex01.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['5', '1', '9', '9', '7', '1', '9', '6', '3', '2', '6', '7', '1', '3', '3', '1', '3', '3', '0', '7'])) := by
  rfl

attribute [local simp] simplex01_lookup_jensen_floor_Q96

theorem simplex01_decoded : decodeSimplex rawSimplex01 = .ok simplex01 := by
  unfold decodeSimplex simplex01
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
