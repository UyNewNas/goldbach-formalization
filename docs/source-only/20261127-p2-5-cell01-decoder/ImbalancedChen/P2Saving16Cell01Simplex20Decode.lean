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

theorem simplex20_lookup_simplex_id :
    rawSimplex20.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2', '0'])) := by
  rfl

attribute [local simp] simplex20_lookup_simplex_id

theorem simplex20_lookup_vertex_ids :
    rawSimplex20.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex20_lookup_vertex_ids

theorem simplex20_lookup_physical_volume :
    rawSimplex20.getObjVal? "physical_volume" = .ok (.str (String.ofList ['7', '5', '8', '2', '9', '3', '2', '2', '7', '4', '6', '9', '7', '9', '7', '7', '6', '9', '5', '5', '4', '8', '2', '6', '0', '1', '9', '3', '5', '6', '6', '4', '2', '3', '3', '0', '0', '5', '2', '3', '9', '2', '3', '1', '/', '3', '0', '7', '7', '7', '2', '6', '4', '2', '3', '4', '8', '2', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex20_lookup_physical_volume

theorem simplex20_lookup_mean_gap :
    rawSimplex20.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex20_lookup_mean_gap

theorem simplex20_lookup_factor_maxima :
    rawSimplex20.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '0', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex20_lookup_factor_maxima

theorem simplex20_lookup_gap_weighted_means :
    rawSimplex20.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['7', '5', '9', '4', '1', '4', '3', '2', '3', '6', '1', '6', '5', '3', '/', '1', '0', '6', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '9', '8', '9', '5', '9', '1', '0', '8', '2', '9', '1', '/', '1', '3', '2', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '6', '6', '2', '6', '6', '7', '9', '2', '6', '5', '4', '9', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '5', '5', '9', '0', '9', '5', '4', '9', '2', '0', '3', '7', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '0', '9', '1', '8', '1', '6', '3', '8', '8', '4', '9', '/', '1', '5', '9', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '2', '8', '1', '5', '2', '4', '5', '4', '5', '1', '/', '3', '5', '3', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '0', '9', '1', '8', '2', '1', '0', '6', '7', '7', '7', '9', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '1', '8', '3', '1', '0', '8', '1', '7', '6', '9', '9', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '9', '3', '6', '8', '7', '5', '3', '6', '7', '8', '7', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '7', '9', '0', '8', '7', '3', '7', '7', '4', '5', '1', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex20_lookup_gap_weighted_means

theorem simplex20_lookup_max_bound :
    rawSimplex20.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '1', '5', '6', '4', '6', '9', '6', '0', '6', '6', '6', '7', '1', '6', '2', '4', '8', '3', '0', '8', '1', '4', '8', '7', '3', '8', '9', '3', '4', '4', '9', '6', '2', '9', '4', '1', '3', '4', '3', '7', '2', '2', '8', '8', '6', '8', '1', '8', '5', '4', '9', '7', '6', '5', '6', '2', '5', '/', '3', '8', '6', '5', '5', '5', '0', '8', '5', '2', '5', '3', '6', '8', '3', '0', '3', '9', '9', '1', '3', '3', '4', '6', '7', '7', '7', '7', '3', '7', '5', '0', '1', '5', '9', '3', '1', '1', '0', '8', '5', '3', '3', '3', '6', '8', '0', '9', '3', '4', '8', '9', '6', '6', '9', '2', '4', '7', '1', '9', '6', '2', '8', '3', '9', '3', '9', '4', '5', '0', '8', '8'])) := by
  rfl

attribute [local simp] simplex20_lookup_max_bound

theorem simplex20_lookup_jensen_bound :
    rawSimplex20.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '3', '6', '3', '2', '1', '9', '9', '2', '4', '0', '0', '4', '1', '9', '2', '9', '5', '8', '0', '8', '6', '3', '0', '3', '4', '4', '1', '0', '6', '8', '4', '2', '4', '7', '7', '7', '3', '4', '3', '5', '6', '9', '4', '6', '5', '1', '3', '0', '1', '1', '1', '5', '2', '5', '5', '1', '7', '8', '1', '4', '1', '7', '9', '3', '1', '5', '9', '9', '8', '9', '1', '5', '2', '9', '6', '3', '8', '4', '7', '2', '5', '5', '0', '4', '0', '7', '2', '0', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '1', '8', '3', '0', '5', '4', '7', '3', '5', '8', '8', '9', '9', '0', '9', '6', '3', '7', '7', '7', '6', '9', '0', '9', '4', '1', '7', '3', '6', '5', '7', '0', '1', '6', '6', '8', '1', '8', '9', '5', '3', '8', '3', '8', '1', '3', '1', '3', '5', '9', '5', '0', '1', '1', '8', '1', '9', '5', '5', '8', '1', '4', '4', '4', '0', '7', '3', '4', '7', '2', '6', '2', '5', '6', '0', '7', '8', '5', '3', '0', '1', '3', '6', '4', '0', '2', '7', '6', '8', '0', '1', '7', '3', '0', '9', '6', '1', '7', '3', '1', '9', '3', '1', '6', '3', '6', '0', '4', '8', '6', '4', '4', '5', '3', '1', '9', '5', '5', '6', '7', '3', '8', '6', '8', '9', '6', '4', '3', '4', '7', '7'])) := by
  rfl

attribute [local simp] simplex20_lookup_jensen_bound

theorem simplex20_lookup_max_floor_Q96 :
    rawSimplex20.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '7', '0', '2', '9', '5', '0', '8', '6', '9', '1', '3', '7', '5'])) := by
  rfl

attribute [local simp] simplex20_lookup_max_floor_Q96

theorem simplex20_lookup_jensen_floor_Q96 :
    rawSimplex20.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '5', '8', '1', '9', '7', '4', '5', '7', '3', '6', '2', '9', '6', '2', '3'])) := by
  rfl

attribute [local simp] simplex20_lookup_jensen_floor_Q96

theorem simplex20_decoded : decodeSimplex rawSimplex20 = .ok simplex20 := by
  unfold decodeSimplex simplex20
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
