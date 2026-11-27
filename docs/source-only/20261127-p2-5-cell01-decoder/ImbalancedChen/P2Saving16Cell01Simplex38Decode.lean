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

theorem simplex38_lookup_simplex_id :
    rawSimplex38.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3', '8'])) := by
  rfl

attribute [local simp] simplex38_lookup_simplex_id

theorem simplex38_lookup_vertex_ids :
    rawSimplex38.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex38_lookup_vertex_ids

theorem simplex38_lookup_physical_volume :
    rawSimplex38.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '4', '6', '0', '8', '8', '2', '7', '7', '8', '5', '7', '0', '0', '0', '0', '8', '0', '9', '4', '5', '8', '1', '2', '3', '5', '3', '0', '1', '1', '/', '1', '2', '2', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex38_lookup_physical_volume

theorem simplex38_lookup_mean_gap :
    rawSimplex38.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex38_lookup_mean_gap

theorem simplex38_lookup_factor_maxima :
    rawSimplex38.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex38_lookup_factor_maxima

theorem simplex38_lookup_gap_weighted_means :
    rawSimplex38.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '3', '4', '8', '9', '4', '1', '5', '2', '3', '1', '/', '1', '7', '3', '2', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '8', '6', '2', '6', '5', '0', '3', '1', '/', '1', '7', '3', '2', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '4', '6', '0', '8', '2', '6', '2', '4', '1', '3', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '7', '8', '0', '7', '6', '0', '9', '3', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '0', '1', '9', '8', '9', '5', '2', '1', '/', '1', '0', '3', '9', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '1', '8', '5', '6', '8', '2', '3', '7', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '9', '2', '7', '9', '7', '9', '3', '2', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '0', '3', '1', '7', '7', '1', '5', '7', '/', '4', '1', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '1', '4', '9', '9', '9', '5', '9', '3', '7', '3', '/', '2', '0', '7', '9', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '4', '7', '1', '4', '4', '7', '8', '1', '/', '5', '1', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex38_lookup_gap_weighted_means

theorem simplex38_lookup_max_bound :
    rawSimplex38.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '1', '3', '6', '4', '9', '8', '8', '5', '6', '9', '1', '8', '9', '5', '0', '1', '5', '8', '9', '6', '7', '2', '2', '0', '6', '2', '4', '4', '7', '7', '0', '3', '3', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '5', '4', '1', '8', '6', '3', '4', '6', '2', '1', '4', '3', '4', '6', '7', '1', '6', '6', '8', '0', '7', '0', '7', '4', '3', '8', '4', '1', '1', '1', '0', '1', '6', '8', '1', '6', '6', '0', '2', '9', '5', '8', '6', '8', '2', '4', '1', '3', '5', '2', '8', '1', '5', '6', '3', '3', '5', '9', '0', '2', '4', '0', '7'])) := by
  rfl

attribute [local simp] simplex38_lookup_max_bound

theorem simplex38_lookup_jensen_bound :
    rawSimplex38.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '7', '2', '2', '6', '4', '6', '6', '8', '2', '6', '2', '2', '9', '5', '4', '6', '4', '2', '0', '0', '0', '7', '3', '2', '6', '6', '6', '3', '5', '7', '5', '5', '1', '6', '7', '6', '8', '4', '5', '9', '6', '1', '9', '5', '5', '2', '0', '1', '4', '3', '5', '1', '8', '8', '9', '1', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '9', '1', '2', '6', '1', '7', '1', '0', '6', '8', '1', '5', '1', '1', '5', '1', '5', '4', '4', '4', '6', '9', '6', '1', '3', '3', '9', '1', '4', '0', '1', '1', '6', '4', '7', '3', '0', '3', '5', '4', '3', '4', '5', '5', '0', '4', '1', '1', '2', '1', '5', '5', '3', '9', '8', '7', '6', '7', '9', '1', '2', '5', '7', '7', '0', '5', '4', '8', '6', '1', '5', '1', '4', '4', '6', '0', '6', '4', '4', '2', '8', '5', '1', '5', '9', '3', '7', '6', '8', '8', '1', '3', '2', '6', '9', '8', '4', '2', '2', '3'])) := by
  rfl

attribute [local simp] simplex38_lookup_jensen_bound

theorem simplex38_lookup_max_floor_Q96 :
    rawSimplex38.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['4', '1', '7', '5', '2', '8', '7', '1', '9', '5', '8', '8', '3'])) := by
  rfl

attribute [local simp] simplex38_lookup_max_floor_Q96

theorem simplex38_lookup_jensen_floor_Q96 :
    rawSimplex38.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '6', '8', '9', '4', '0', '4', '9', '9', '1', '1', '3', '5', '8'])) := by
  rfl

attribute [local simp] simplex38_lookup_jensen_floor_Q96

theorem simplex38_decoded : decodeSimplex rawSimplex38 = .ok simplex38 := by
  unfold decodeSimplex simplex38
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
