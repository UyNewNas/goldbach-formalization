import ImbalancedChen.P2Saving16Cell03FieldSimp

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell03 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2Saving16Cell03FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell03TypedPayload
open P2Saving16Cell03ScalarDecode
open scoped ImbalancedChen.P2Saving16Cell03FieldDecode

theorem simplex19_lookup_simplex_id :
    rawSimplex19.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1', '9'])) := by
  rfl

attribute [local simp] simplex19_lookup_simplex_id

theorem simplex19_lookup_vertex_ids :
    rawSimplex19.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex19_lookup_vertex_ids

theorem simplex19_lookup_physical_volume :
    rawSimplex19.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '0', '7', '9', '5', '3', '1', '2', '0', '8', '8', '6', '3', '4', '1', '5', '1', '6', '0', '5', '8', '1', '6', '6', '6', '8', '4', '7', '4', '3', '6', '6', '3', '2', '3', '4', '7', '6', '0', '1', '3', '/', '2', '0', '8', '8', '9', '3', '1', '3', '4', '2', '4', '1', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex19_lookup_physical_volume

theorem simplex19_lookup_mean_gap :
    rawSimplex19.getObjVal? "mean_gap" = .ok (.str (String.ofList ['4', '4', '2', '6', '1', '9', '/', '8', '6', '4', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex19_lookup_mean_gap

theorem simplex19_lookup_factor_maxima :
    rawSimplex19.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '2', '0', '0', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '4', '3', '2', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '2', '7', '5', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex19_lookup_factor_maxima

theorem simplex19_lookup_gap_weighted_means :
    rawSimplex19.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '6', '1', '8', '6', '5', '5', '7', '9', '2', '7', '7', '/', '2', '4', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '7', '3', '4', '0', '7', '2', '8', '1', '/', '2', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '4', '9', '0', '3', '1', '9', '6', '8', '3', '/', '1', '5', '0', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '3', '4', '4', '6', '1', '2', '3', '8', '8', '3', '/', '1', '2', '0', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '1', '9', '4', '5', '4', '8', '5', '5', '3', '/', '1', '8', '0', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '2', '4', '9', '0', '3', '4', '3', '/', '1', '4', '0', '7', '6', '5', '6', '2', '5', '0', '0']), .str (String.ofList ['7', '1', '7', '5', '2', '8', '3', '9', '6', '1', '9', '/', '1', '8', '0', '1', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '1', '3', '4', '8', '2', '6', '9', '9', '9', '3', '/', '3', '6', '0', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '5', '5', '8', '0', '5', '9', '4', '1', '/', '2', '0', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '0', '0', '4', '3', '2', '0', '2', '3', '/', '1', '0', '0', '1', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex19_lookup_gap_weighted_means

theorem simplex19_lookup_max_bound :
    rawSimplex19.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '1', '9', '0', '9', '3', '7', '6', '8', '8', '5', '6', '1', '8', '4', '3', '3', '9', '8', '1', '3', '6', '6', '9', '3', '7', '3', '7', '0', '7', '4', '6', '4', '6', '6', '6', '4', '5', '5', '4', '2', '1', '7', '2', '2', '4', '2', '1', '8', '7', '5', '/', '1', '0', '6', '9', '7', '1', '5', '2', '2', '9', '2', '5', '8', '7', '3', '2', '4', '1', '6', '8', '2', '6', '3', '0', '5', '0', '3', '5', '5', '5', '6', '4', '0', '9', '4', '9', '7', '1', '4', '5', '3', '5', '0', '0', '1', '0', '1', '9', '3', '8', '0', '3', '6', '0', '5', '3', '0', '2', '8', '9', '6', '6', '6', '1', '2', '4', '8'])) := by
  rfl

attribute [local simp] simplex19_lookup_max_bound

theorem simplex19_lookup_jensen_bound :
    rawSimplex19.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '7', '4', '7', '9', '5', '9', '7', '1', '8', '8', '6', '5', '5', '7', '1', '8', '0', '4', '3', '5', '7', '1', '5', '2', '8', '8', '6', '6', '1', '2', '3', '0', '0', '6', '7', '7', '1', '6', '4', '9', '1', '9', '0', '2', '4', '6', '2', '7', '0', '8', '0', '0', '5', '2', '1', '9', '2', '5', '9', '3', '7', '5', '7', '2', '3', '4', '6', '4', '3', '9', '3', '6', '1', '5', '7', '2', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '/', '5', '4', '2', '3', '4', '5', '0', '9', '7', '6', '2', '2', '5', '5', '8', '7', '9', '8', '8', '9', '0', '2', '4', '4', '0', '2', '8', '3', '2', '7', '8', '6', '8', '4', '0', '0', '3', '1', '5', '1', '7', '7', '8', '7', '7', '7', '6', '4', '4', '6', '4', '3', '7', '6', '2', '5', '8', '0', '8', '7', '7', '3', '4', '4', '5', '1', '1', '1', '9', '1', '9', '6', '5', '5', '8', '6', '9', '2', '7', '2', '5', '8', '5', '2', '6', '0', '5', '1', '6', '6', '4', '0', '7', '1', '9', '8', '2', '3', '6', '0', '0', '9'])) := by
  rfl

attribute [local simp] simplex19_lookup_jensen_bound

theorem simplex19_lookup_max_floor_Q96 :
    rawSimplex19.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['5', '3', '2', '5', '9', '4', '8', '1', '0', '5', '0', '3', '0', '9'])) := by
  rfl

attribute [local simp] simplex19_lookup_max_floor_Q96

theorem simplex19_lookup_jensen_floor_Q96 :
    rawSimplex19.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '9', '3', '6', '0', '2', '8', '8', '4', '7', '0', '6', '5', '5', '0'])) := by
  rfl

attribute [local simp] simplex19_lookup_jensen_floor_Q96

theorem simplex19_decoded : decodeSimplex rawSimplex19 = .ok simplex19 := by
  unfold decodeSimplex simplex19
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
