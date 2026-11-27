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

theorem simplex64_lookup_simplex_id :
    rawSimplex64.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6', '4'])) := by
  rfl

attribute [local simp] simplex64_lookup_simplex_id

theorem simplex64_lookup_vertex_ids :
    rawSimplex64.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['3', '3']), .number (String.ofList ['3', '2']), .number (String.ofList ['3', '1']), .number (String.ofList ['3', '0']), .number (String.ofList ['2', '2']), .number (String.ofList ['7']), .number (String.ofList ['4']), .number (String.ofList ['1'])]) := by
  rfl

attribute [local simp] simplex64_lookup_vertex_ids

theorem simplex64_lookup_physical_volume :
    rawSimplex64.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '0', '6', '3', '8', '8', '3', '9', '1', '2', '7', '5', '0', '8', '9', '1', '2', '2', '1', '8', '6', '6', '0', '5', '9', '0', '8', '0', '0', '0', '9', '3', '3', '1', '9', '8', '4', '5', '4', '5', '6', '4', '4', '9', '/', '1', '9', '3', '3', '8', '7', '2', '7', '7', '6', '4', '7', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex64_lookup_physical_volume

theorem simplex64_lookup_mean_gap :
    rawSimplex64.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex64_lookup_mean_gap

theorem simplex64_lookup_factor_maxima :
    rawSimplex64.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['6', '4', '0', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '4', '0', '6', '1', '9', '/', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '2', '1', '7', '8', '3', '/', '6', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '9', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '2', '8', '7', '/', '7', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex64_lookup_factor_maxima

theorem simplex64_lookup_gap_weighted_means :
    rawSimplex64.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '4', '1', '5', '6', '2', '5', '5', '4', '7', '7', '7', '/', '3', '8', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '1', '3', '6', '0', '9', '3', '7', '2', '7', '/', '3', '8', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '9', '4', '9', '7', '4', '4', '5', '2', '6', '5', '3', '/', '1', '1', '6', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '3', '9', '6', '5', '5', '1', '3', '2', '4', '1', '/', '2', '3', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '5', '2', '9', '7', '7', '6', '4', '7', '4', '9', '/', '2', '3', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '9', '8', '6', '3', '7', '8', '9', '9', '/', '2', '9', '2', '0', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '8', '7', '8', '1', '1', '4', '0', '6', '7', '/', '3', '8', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '5', '0', '8', '4', '7', '5', '0', '0', '7', '/', '2', '3', '3', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '0', '8', '8', '9', '3', '3', '6', '9', '9', '3', '9', '/', '1', '1', '6', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '2', '1', '0', '3', '4', '7', '5', '1', '9', '7', '/', '1', '1', '6', '8', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex64_lookup_gap_weighted_means

theorem simplex64_lookup_max_bound :
    rawSimplex64.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '7', '7', '6', '3', '4', '4', '7', '9', '0', '0', '5', '1', '0', '8', '6', '6', '7', '9', '7', '7', '4', '9', '3', '8', '9', '9', '4', '8', '9', '4', '9', '4', '2', '5', '2', '0', '6', '7', '2', '5', '3', '0', '9', '6', '2', '7', '0', '1', '3', '7', '5', '0', '0', '0', '0', '/', '2', '0', '4', '6', '9', '8', '9', '8', '0', '7', '8', '7', '9', '2', '5', '8', '4', '2', '1', '5', '6', '3', '8', '2', '4', '4', '3', '5', '2', '9', '9', '5', '9', '3', '8', '1', '2', '3', '1', '5', '4', '6', '0', '9', '0', '0', '4', '2', '8', '6', '3', '5', '0', '8', '7', '5', '9', '1', '0', '0', '4', '2', '2', '1', '7', '8', '9', '6', '3'])) := by
  rfl

attribute [local simp] simplex64_lookup_max_bound

theorem simplex64_lookup_jensen_bound :
    rawSimplex64.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '6', '9', '8', '2', '4', '8', '0', '6', '1', '6', '4', '7', '2', '0', '6', '5', '7', '3', '0', '0', '1', '7', '5', '9', '9', '2', '8', '5', '6', '3', '6', '6', '3', '3', '1', '6', '8', '3', '5', '4', '5', '5', '5', '5', '0', '9', '0', '6', '9', '5', '2', '1', '2', '1', '4', '4', '4', '2', '5', '2', '4', '9', '1', '9', '0', '9', '8', '7', '3', '7', '7', '9', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '5', '5', '3', '4', '3', '2', '3', '2', '0', '2', '4', '8', '0', '6', '8', '1', '1', '0', '4', '4', '9', '9', '6', '4', '3', '4', '9', '1', '4', '9', '9', '0', '6', '6', '4', '1', '2', '5', '7', '9', '9', '3', '1', '2', '1', '1', '4', '0', '0', '9', '5', '0', '3', '4', '2', '4', '2', '4', '6', '2', '3', '0', '5', '9', '9', '5', '5', '2', '2', '6', '7', '3', '1', '3', '5', '6', '6', '5', '4', '4', '3', '0', '9', '1', '4', '4', '5', '4', '1', '6', '5', '1', '5', '3', '2', '6', '1', '7', '2', '5', '5', '3', '7', '8', '4', '7', '1', '3', '2', '8', '9'])) := by
  rfl

attribute [local simp] simplex64_lookup_jensen_bound

theorem simplex64_lookup_max_floor_Q96 :
    rawSimplex64.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['6', '8', '7', '5', '2', '9', '2', '3', '5', '2', '0', '0', '9', '3', '8', '5'])) := by
  rfl

attribute [local simp] simplex64_lookup_max_floor_Q96

theorem simplex64_lookup_jensen_floor_Q96 :
    rawSimplex64.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '7', '8', '6', '4', '5', '3', '8', '0', '8', '3', '6', '5', '3', '8', '0', '6'])) := by
  rfl

attribute [local simp] simplex64_lookup_jensen_floor_Q96

theorem simplex64_decoded : decodeSimplex rawSimplex64 = .ok simplex64 := by
  unfold decodeSimplex simplex64
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
