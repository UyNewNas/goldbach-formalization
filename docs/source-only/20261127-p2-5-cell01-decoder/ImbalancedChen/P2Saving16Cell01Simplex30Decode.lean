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

theorem simplex30_lookup_simplex_id :
    rawSimplex30.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3', '0'])) := by
  rfl

attribute [local simp] simplex30_lookup_simplex_id

theorem simplex30_lookup_vertex_ids :
    rawSimplex30.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '6']), .number (String.ofList ['2', '4']), .number (String.ofList ['2', '3']), .number (String.ofList ['2', '0']), .number (String.ofList ['9']), .number (String.ofList ['6']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex30_lookup_vertex_ids

theorem simplex30_lookup_physical_volume :
    rawSimplex30.getObjVal? "physical_volume" = .ok (.str (String.ofList ['7', '5', '8', '2', '8', '5', '6', '1', '4', '0', '1', '3', '2', '7', '2', '4', '9', '7', '6', '3', '0', '6', '6', '8', '5', '4', '2', '7', '3', '3', '2', '9', '6', '6', '1', '4', '8', '2', '0', '2', '9', '7', '5', '1', '/', '3', '0', '7', '7', '7', '2', '6', '4', '2', '3', '4', '8', '2', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex30_lookup_physical_volume

theorem simplex30_lookup_mean_gap :
    rawSimplex30.getObjVal? "mean_gap" = .ok (.str (String.ofList ['3', '9', '8', '3', '9', '2', '3', '/', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex30_lookup_mean_gap

theorem simplex30_lookup_factor_maxima :
    rawSimplex30.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '3', '1', '0', '9', '/', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '0', '9', '3', '/', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '0', '3', '0', '0', '9', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '2', '3', '4', '0', '8', '3', '/', '2', '1', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '0', '9', '/', '1', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex30_lookup_factor_maxima

theorem simplex30_lookup_gap_weighted_means :
    rawSimplex30.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['7', '5', '9', '4', '1', '4', '7', '9', '4', '9', '1', '2', '5', '3', '/', '1', '0', '6', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '6', '9', '8', '9', '6', '4', '9', '9', '9', '4', '9', '1', '/', '1', '3', '2', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '6', '6', '2', '6', '6', '2', '0', '3', '5', '3', '4', '9', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '5', '5', '9', '0', '9', '7', '8', '4', '8', '5', '1', '7', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '0', '0', '9', '1', '8', '0', '4', '6', '0', '6', '0', '9', '/', '1', '5', '9', '0', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '5', '2', '0', '8', '8', '2', '1', '0', '2', '5', '9', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '0', '5', '0', '6', '7', '7', '1', '0', '0', '9', '9', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '9', '1', '8', '3', '1', '5', '5', '3', '0', '6', '5', '9', '/', '3', '1', '8', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '2', '9', '3', '6', '6', '6', '9', '1', '7', '5', '8', '7', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '7', '9', '0', '9', '3', '2', '6', '8', '6', '5', '1', '/', '3', '9', '7', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex30_lookup_gap_weighted_means

theorem simplex30_lookup_max_bound :
    rawSimplex30.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '1', '5', '6', '4', '5', '7', '9', '9', '5', '4', '1', '8', '6', '9', '7', '9', '0', '4', '8', '4', '6', '3', '6', '7', '4', '1', '9', '7', '3', '2', '9', '0', '2', '3', '3', '7', '7', '3', '9', '3', '0', '8', '4', '5', '1', '0', '1', '2', '9', '2', '7', '8', '9', '0', '6', '2', '5', '/', '3', '8', '6', '5', '5', '4', '7', '5', '0', '3', '5', '9', '7', '9', '0', '1', '7', '8', '1', '8', '3', '4', '4', '6', '2', '0', '5', '3', '0', '7', '1', '2', '1', '3', '9', '6', '5', '0', '9', '7', '2', '1', '1', '9', '6', '4', '7', '9', '9', '2', '2', '4', '4', '5', '7', '0', '1', '1', '6', '4', '9', '3', '3', '3', '2', '3', '5', '7', '7', '3', '4', '4'])) := by
  rfl

attribute [local simp] simplex30_lookup_max_bound

theorem simplex30_lookup_jensen_bound :
    rawSimplex30.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '2', '2', '6', '8', '8', '5', '6', '1', '3', '2', '3', '7', '0', '4', '5', '8', '2', '0', '9', '4', '3', '1', '8', '0', '0', '0', '3', '7', '9', '6', '8', '4', '1', '9', '4', '8', '5', '3', '3', '6', '6', '6', '7', '9', '4', '7', '9', '8', '6', '9', '5', '2', '6', '1', '2', '6', '8', '2', '2', '8', '6', '8', '0', '0', '4', '3', '6', '6', '9', '8', '6', '1', '3', '8', '2', '2', '1', '8', '4', '1', '7', '2', '6', '5', '9', '0', '4', '1', '8', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '3', '7', '3', '6', '1', '6', '8', '0', '4', '5', '9', '1', '9', '0', '3', '6', '9', '0', '7', '4', '9', '9', '5', '6', '7', '5', '5', '1', '7', '3', '9', '4', '8', '7', '8', '8', '8', '7', '8', '0', '2', '5', '9', '2', '8', '1', '5', '0', '2', '9', '5', '3', '9', '3', '3', '6', '5', '8', '3', '5', '9', '7', '2', '6', '6', '1', '7', '5', '5', '8', '3', '2', '1', '7', '1', '4', '7', '9', '5', '9', '5', '1', '5', '5', '6', '6', '3', '7', '2', '3', '2', '2', '8', '4', '1', '0', '4', '0', '0', '0', '4', '2', '5', '2', '2', '2', '6', '3', '2', '9', '5', '2', '9', '6', '7', '5', '9', '0', '6', '5', '2', '3', '3', '7', '9', '6', '3', '3', '6', '5', '6', '9', '3'])) := by
  rfl

attribute [local simp] simplex30_lookup_jensen_bound

theorem simplex30_lookup_max_floor_Q96 :
    rawSimplex30.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '7', '0', '2', '7', '3', '3', '4', '2', '0', '4', '7', '2', '2'])) := by
  rfl

attribute [local simp] simplex30_lookup_max_floor_Q96

theorem simplex30_lookup_jensen_floor_Q96 :
    rawSimplex30.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['2', '6', '0', '1', '7', '0', '0', '2', '3', '2', '8', '9', '3', '2', '1', '6'])) := by
  rfl

attribute [local simp] simplex30_lookup_jensen_floor_Q96

theorem simplex30_decoded : decodeSimplex rawSimplex30 = .ok simplex30 := by
  unfold decodeSimplex simplex30
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
