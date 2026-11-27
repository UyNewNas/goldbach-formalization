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

theorem simplex77_lookup_simplex_id :
    rawSimplex77.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7', '7'])) := by
  rfl

attribute [local simp] simplex77_lookup_simplex_id

theorem simplex77_lookup_vertex_ids :
    rawSimplex77.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['3', '4']), .number (String.ofList ['2', '1']), .number (String.ofList ['1', '9']), .number (String.ofList ['1', '7']), .number (String.ofList ['1', '6']), .number (String.ofList ['1', '4']), .number (String.ofList ['8']), .number (String.ofList ['6']), .number (String.ofList ['3'])]) := by
  rfl

attribute [local simp] simplex77_lookup_vertex_ids

theorem simplex77_lookup_physical_volume :
    rawSimplex77.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '3', '4', '6', '1', '1', '1', '7', '5', '3', '8', '5', '0', '8', '9', '8', '0', '6', '3', '1', '1', '7', '0', '6', '3', '2', '2', '8', '1', '/', '6', '9', '8', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex77_lookup_physical_volume

theorem simplex77_lookup_mean_gap :
    rawSimplex77.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '5', '6', '2', '3', '/', '2', '4', '7', '5', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex77_lookup_mean_gap

theorem simplex77_lookup_factor_maxima :
    rawSimplex77.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '2', '0', '3', '0', '5', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '5', '1', '5', '6', '2', '1', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '2', '1', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '1', '2', '1', '/', '2', '4', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '9', '0', '6', '9', '3', '/', '1', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '9', '0', '6', '1', '3', '/', '1', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex77_lookup_factor_maxima

theorem simplex77_lookup_gap_weighted_means :
    rawSimplex77.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '7', '9', '2', '1', '4', '6', '2', '6', '3', '3', '/', '2', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '1', '8', '3', '9', '2', '9', '0', '3', '3', '/', '2', '3', '1', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '6', '4', '6', '9', '9', '3', '2', '6', '1', '7', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '9', '0', '4', '6', '3', '8', '8', '9', '/', '7', '7', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '0', '2', '0', '5', '0', '9', '/', '1', '9', '2', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '7', '2', '4', '9', '2', '6', '5', '3', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '5', '0', '0', '3', '1', '4', '3', '9', '3', '/', '4', '6', '2', '0', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '5', '1', '7', '1', '6', '1', '/', '5', '7', '7', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '4', '3', '0', '5', '8', '6', '9', '3', '/', '5', '7', '7', '5', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '6', '6', '5', '1', '0', '2', '0', '3', '3', '/', '6', '9', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex77_lookup_gap_weighted_means

theorem simplex77_lookup_max_bound :
    rawSimplex77.getObjVal? "max_bound" = .ok (.str (String.ofList ['2', '1', '5', '3', '5', '0', '3', '1', '2', '2', '4', '7', '4', '2', '4', '8', '2', '3', '7', '0', '6', '3', '9', '7', '4', '7', '9', '0', '4', '1', '0', '8', '8', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '4', '2', '3', '2', '2', '3', '3', '5', '0', '9', '3', '7', '8', '7', '2', '7', '3', '9', '9', '9', '3', '3', '4', '7', '9', '0', '8', '9', '7', '4', '6', '6', '1', '3', '0', '8', '7', '5', '0', '3', '0', '7', '4', '7', '4', '7', '2', '4', '3', '8', '0', '1', '8', '7', '3', '6', '7', '6', '0', '2', '0', '9', '9'])) := by
  rfl

attribute [local simp] simplex77_lookup_max_bound

theorem simplex77_lookup_jensen_bound :
    rawSimplex77.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '4', '6', '1', '8', '1', '9', '9', '2', '5', '6', '3', '6', '2', '3', '7', '2', '4', '5', '3', '5', '6', '6', '2', '1', '8', '9', '7', '7', '9', '5', '9', '9', '3', '5', '8', '4', '7', '5', '5', '0', '1', '8', '6', '1', '8', '2', '0', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '2', '2', '2', '9', '9', '0', '0', '5', '9', '5', '2', '9', '0', '1', '8', '7', '7', '6', '4', '2', '8', '6', '5', '1', '2', '0', '4', '5', '3', '0', '0', '6', '4', '2', '7', '7', '5', '2', '5', '1', '9', '7', '0', '0', '8', '8', '6', '0', '3', '5', '2', '9', '3', '2', '7', '2', '1', '0', '1', '9', '3', '8', '6', '2', '9', '9', '0', '6', '6', '6', '2', '6', '8', '7', '0', '5', '5', '0', '3', '5', '3', '6', '6', '7', '0', '3', '7', '1', '8', '8', '8', '7', '7'])) := by
  rfl

attribute [local simp] simplex77_lookup_jensen_bound

theorem simplex77_lookup_max_floor_Q96 :
    rawSimplex77.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '1', '4', '6', '0', '6', '4', '3', '2', '9', '6', '7', '3'])) := by
  rfl

attribute [local simp] simplex77_lookup_max_floor_Q96

theorem simplex77_lookup_jensen_floor_Q96 :
    rawSimplex77.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['1', '4', '0', '8', '4', '5', '7', '3', '3', '4', '8', '1', '9', '2'])) := by
  rfl

attribute [local simp] simplex77_lookup_jensen_floor_Q96

theorem simplex77_decoded : decodeSimplex rawSimplex77 = .ok simplex77 := by
  unfold decodeSimplex simplex77
  simp [rationalField, rationalArrayField]

end ImbalancedChen.P2Saving16Cell01FieldDecode
