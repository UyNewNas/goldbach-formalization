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

theorem simplex04_lookup_simplex_id :
    rawSimplex04.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4'])) := by
  rfl

attribute [local simp] simplex04_lookup_simplex_id

theorem simplex04_lookup_vertex_ids :
    rawSimplex04.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['2', '2']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['7']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_vertex_ids

theorem simplex04_lookup_physical_volume :
    rawSimplex04.getObjVal? "physical_volume" = .ok (.str (String.ofList ['7', '5', '5', '1', '0', '6', '5', '8', '9', '1', '5', '4', '8', '9', '4', '2', '7', '9', '6', '0', '4', '3', '1', '8', '3', '9', '0', '2', '2', '0', '3', '6', '8', '6', '6', '4', '0', '2', '3', '1', '1', '/', '3', '0', '5', '6', '2', '4', '8', '9', '8', '1', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_physical_volume

theorem simplex04_lookup_mean_gap :
    rawSimplex04.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '6', '1', '1', '/', '7', '4', '1', '6', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_mean_gap

theorem simplex04_lookup_factor_maxima :
    rawSimplex04.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '2', '6', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '7', '7', '0', '3', '0', '7', '3', '/', '1', '5', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '1', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '2', '5', '1', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '2', '9', '7', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '4', '2', '0', '0', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '7', '9', '9', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '5', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_factor_maxima

theorem simplex04_lookup_gap_weighted_means :
    rawSimplex04.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '6', '5', '3', '0', '1', '5', '3', '9', '2', '2', '8', '7', '/', '8', '4', '3', '5', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '1', '6', '8', '2', '2', '4', '7', '8', '4', '3', '9', '/', '1', '0', '5', '4', '4', '6', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '9', '8', '9', '6', '7', '1', '9', '6', '0', '6', '9', '3', '/', '2', '5', '3', '0', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '4', '6', '7', '6', '7', '2', '4', '1', '0', '4', '1', '/', '5', '0', '6', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '8', '1', '0', '5', '2', '0', '6', '2', '3', '1', '9', '/', '5', '0', '6', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '6', '1', '6', '0', '8', '0', '8', '0', '0', '0', '3', '/', '3', '3', '7', '4', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '3', '8', '0', '6', '0', '2', '7', '1', '1', '4', '9', '/', '1', '0', '1', '2', '2', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '2', '6', '3', '6', '1', '4', '5', '1', '4', '1', '7', '/', '5', '0', '6', '1', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '3', '6', '1', '2', '3', '1', '4', '1', '8', '2', '0', '9', '/', '2', '5', '3', '0', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '2', '9', '4', '6', '4', '9', '9', '9', '2', '2', '5', '7', '/', '2', '5', '3', '0', '7', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_gap_weighted_means

theorem simplex04_lookup_max_bound :
    rawSimplex04.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '5', '2', '0', '1', '2', '7', '2', '8', '6', '8', '2', '4', '7', '9', '3', '8', '9', '0', '1', '7', '2', '0', '9', '5', '9', '6', '6', '9', '6', '0', '3', '8', '2', '5', '8', '5', '1', '4', '4', '4', '1', '3', '1', '2', '5', '5', '2', '5', '0', '0', '0', '/', '3', '5', '9', '3', '9', '9', '0', '2', '2', '0', '9', '1', '5', '7', '0', '4', '8', '6', '5', '6', '0', '6', '3', '9', '3', '3', '6', '1', '0', '4', '3', '9', '3', '1', '4', '2', '1', '2', '8', '9', '4', '1', '1', '4', '8', '7', '4', '7', '1', '3', '7', '7', '1', '7', '9', '0', '6', '1', '2', '4', '1', '7', '5', '8', '4', '4', '5', '9'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_bound

theorem simplex04_lookup_jensen_bound :
    rawSimplex04.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['3', '3', '8', '9', '7', '4', '2', '8', '3', '7', '7', '4', '4', '7', '9', '5', '8', '3', '8', '1', '1', '8', '7', '9', '4', '9', '5', '0', '6', '9', '0', '9', '9', '9', '2', '6', '7', '8', '4', '2', '0', '0', '2', '5', '2', '9', '5', '8', '6', '9', '8', '3', '5', '3', '2', '2', '9', '6', '1', '7', '7', '8', '9', '6', '0', '8', '8', '9', '1', '8', '2', '4', '8', '2', '2', '6', '8', '9', '3', '3', '4', '6', '0', '4', '5', '8', '9', '3', '0', '6', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '5', '1', '0', '1', '1', '3', '7', '9', '3', '7', '4', '3', '7', '7', '0', '8', '2', '9', '0', '0', '1', '5', '1', '6', '7', '9', '7', '0', '4', '8', '5', '3', '3', '9', '2', '1', '9', '7', '7', '1', '9', '0', '7', '8', '1', '5', '8', '2', '7', '4', '4', '7', '7', '8', '4', '1', '1', '4', '8', '7', '2', '5', '0', '8', '1', '1', '1', '9', '7', '4', '7', '4', '2', '4', '7', '3', '6', '4', '6', '8', '1', '6', '5', '8', '7', '7', '3', '6', '8', '8', '1', '4', '2', '2', '3', '8', '6', '0', '6', '1', '0', '1', '6', '0', '7', '2', '0', '9', '0', '0', '1', '8', '5', '2', '3', '6', '9', '8', '1', '3', '2', '8', '4', '7', '7'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_bound

theorem simplex04_lookup_max_floor_Q96 :
    rawSimplex04.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '6', '5', '7', '7', '8', '3', '7', '7', '2', '8', '6', '9', '3'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_floor_Q96

theorem simplex04_lookup_jensen_floor_Q96 :
    rawSimplex04.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '7', '3', '1', '5', '3', '5', '3', '0', '6', '5', '8', '6', '4', '4'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_floor_Q96

theorem simplex04_decoded : decodeSimplex rawSimplex04 = .ok simplex04 := by
  unfold decodeSimplex simplex04
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell03FieldDecode
