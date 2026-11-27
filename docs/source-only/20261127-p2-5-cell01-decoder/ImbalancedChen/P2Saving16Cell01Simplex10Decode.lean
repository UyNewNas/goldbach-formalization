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

theorem simplex10_lookup_simplex_id :
    rawSimplex10.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1', '0'])) := by
  rfl

attribute [local simp] simplex10_lookup_simplex_id

theorem simplex10_lookup_vertex_ids :
    rawSimplex10.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '5']), .number (String.ofList ['2', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex10_lookup_vertex_ids

theorem simplex10_lookup_physical_volume :
    rawSimplex10.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '4', '6', '9', '1', '2', '7', '5', '8', '7', '8', '5', '0', '7', '3', '0', '3', '2', '4', '4', '0', '3', '1', '1', '5', '0', '9', '1', '1', '6', '6', '9', '6', '9', '3', '0', '6', '2', '0', '1', '/', '2', '2', '5', '5', '4', '3', '9', '0', '5', '9', '6', '4', '1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex10_lookup_physical_volume

theorem simplex10_lookup_mean_gap :
    rawSimplex10.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '6', '3', '/', '4', '2', '4', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex10_lookup_mean_gap

theorem simplex10_lookup_factor_maxima :
    rawSimplex10.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '8', '5', '9', '3', '3', '1', '/', '2', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '9', '1', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex10_lookup_factor_maxima

theorem simplex10_lookup_gap_weighted_means :
    rawSimplex10.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['5', '6', '0', '6', '2', '7', '3', '2', '7', '8', '3', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '7', '3', '1', '7', '6', '8', '1', '1', '2', '8', '7', '/', '7', '4', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '7', '5', '1', '5', '1', '8', '6', '7', '8', '1', '6', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '5', '3', '3', '0', '4', '7', '2', '7', '9', '3', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '1', '9', '0', '9', '4', '2', '6', '7', '5', '7', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '5', '1', '2', '3', '2', '8', '0', '9', '3', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '0', '4', '7', '5', '7', '4', '0', '8', '3', '/', '3', '7', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '3', '4', '4', '0', '0', '5', '4', '0', '1', '/', '4', '4', '6', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '5', '4', '5', '9', '7', '5', '7', '7', '4', '9', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '8', '8', '6', '6', '1', '8', '3', '3', '2', '8', '7', '/', '2', '2', '3', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex10_lookup_gap_weighted_means

theorem simplex10_lookup_max_bound :
    rawSimplex10.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '3', '2', '4', '6', '6', '9', '2', '5', '1', '2', '4', '7', '7', '6', '7', '2', '2', '5', '2', '9', '8', '1', '0', '8', '9', '4', '3', '6', '6', '5', '2', '3', '6', '0', '4', '7', '3', '9', '1', '0', '5', '9', '5', '4', '7', '8', '5', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '/', '2', '7', '3', '2', '0', '0', '0', '6', '3', '1', '0', '8', '6', '9', '8', '7', '1', '3', '1', '0', '9', '8', '1', '2', '2', '2', '7', '5', '9', '9', '2', '6', '7', '7', '7', '3', '4', '0', '3', '7', '4', '5', '8', '5', '0', '4', '5', '9', '0', '7', '6', '1', '5', '3', '5', '9', '7', '7', '2', '3', '0', '4', '7', '6', '5', '9', '4', '0', '9'])) := by
  rfl

attribute [local simp] simplex10_lookup_max_bound

theorem simplex10_lookup_jensen_bound :
    rawSimplex10.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['4', '8', '5', '2', '2', '1', '1', '7', '0', '2', '9', '1', '6', '8', '6', '2', '0', '4', '7', '1', '0', '3', '3', '3', '7', '5', '9', '7', '8', '7', '9', '8', '1', '4', '2', '1', '5', '7', '9', '1', '5', '1', '0', '2', '1', '4', '3', '3', '9', '8', '4', '5', '8', '5', '4', '9', '2', '6', '3', '0', '7', '9', '3', '5', '2', '0', '8', '8', '0', '1', '9', '9', '9', '0', '2', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '1', '8', '1', '4', '3', '8', '5', '2', '5', '2', '8', '9', '6', '5', '4', '4', '6', '3', '7', '1', '0', '6', '9', '5', '8', '9', '5', '3', '3', '6', '4', '2', '6', '8', '6', '9', '5', '6', '5', '6', '5', '5', '9', '3', '9', '7', '6', '4', '8', '6', '9', '8', '0', '7', '9', '6', '3', '9', '6', '5', '6', '5', '1', '1', '5', '2', '2', '3', '2', '0', '1', '3', '2', '4', '4', '4', '1', '0', '8', '2', '9', '9', '1', '2', '8', '5', '5', '1', '4', '2', '5', '7', '8', '1', '0', '2', '0', '7', '9', '3', '7', '1', '0', '4', '6', '4', '3', '1', '3', '3', '3', '8', '0', '0', '9'])) := by
  rfl

attribute [local simp] simplex10_lookup_jensen_bound

theorem simplex10_lookup_max_floor_Q96 :
    rawSimplex10.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '8', '4', '1', '5', '4', '7', '8', '2', '1', '0', '8', '3', '4', '0', '2', '4', '7'])) := by
  rfl

attribute [local simp] simplex10_lookup_max_floor_Q96

theorem simplex10_lookup_jensen_floor_Q96 :
    rawSimplex10.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '2', '5', '3', '9', '2', '9', '9', '2', '6', '2', '9', '9', '4', '7', '3', '9', '6', '7'])) := by
  rfl

attribute [local simp] simplex10_lookup_jensen_floor_Q96

theorem simplex10_decoded : decodeSimplex rawSimplex10 = .ok simplex10 := by
  unfold decodeSimplex simplex10
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
