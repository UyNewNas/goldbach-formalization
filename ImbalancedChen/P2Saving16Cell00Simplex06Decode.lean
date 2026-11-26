import ImbalancedChen.P2Saving16Cell00FieldSimp

/-!
SOURCE ONLY / UNCOMPILED / ZERO NEW FORMAL CREDIT.
Mechanical owner split of the frozen cell00 field certificate.
Original theorem commands, statements and proof bodies remain byte-identical.
-/
namespace ImbalancedChen.P2Saving16Cell00FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell00TypedPayload
open P2Saving16Cell00ScalarDecode
open scoped ImbalancedChen.P2Saving16Cell00FieldDecode

theorem simplex06_lookup_simplex_id :
    rawSimplex06.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6'])) := by
  rfl

attribute [local simp] simplex06_lookup_simplex_id

theorem simplex06_lookup_vertex_ids :
    rawSimplex06.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_vertex_ids

theorem simplex06_lookup_physical_volume :
    rawSimplex06.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '2', '9', '1', '5', '1', '4', '4', '8', '8', '8', '1', '9', '4', '1', '8', '7', '3', '8', '0', '6', '4', '3', '0', '5', '0', '6', '8', '2', '0', '5', '2', '3', '/', '2', '4', '4', '2', '6', '0', '9', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_physical_volume

theorem simplex06_lookup_mean_gap :
    rawSimplex06.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_mean_gap

theorem simplex06_lookup_factor_maxima :
    rawSimplex06.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_factor_maxima

theorem simplex06_lookup_gap_weighted_means :
    rawSimplex06.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '4', '9', '1', '7', '1', '0', '0', '7', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '5', '5', '3', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '9', '7', '1', '0', '8', '4', '3', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '0', '1', '9', '7', '3', '0', '9', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '4', '7', '0', '3', '2', '6', '3', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '0', '4', '1', '2', '7', '1', '7', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '0', '3', '8', '9', '3', '5', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '0', '3', '2', '3', '8', '0', '6', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_gap_weighted_means

theorem simplex06_lookup_max_bound :
    rawSimplex06.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '2', '7', '1', '7', '8', '1', '7', '6', '1', '4', '3', '8', '7', '7', '3', '9', '8', '2', '6', '6', '0', '1', '9', '4', '9', '3', '0', '4', '8', '8', '2', '7', '7', '2', '1', '5', '8', '7', '0', '9', '7', '6', '0', '0', '0', '0', '0', '/', '1', '7', '6', '4', '8', '0', '4', '5', '6', '3', '3', '3', '2', '9', '9', '6', '1', '3', '5', '2', '3', '0', '8', '4', '0', '9', '3', '6', '1', '9', '2', '2', '3', '1', '7', '3', '9', '4', '2', '3', '8', '1', '0', '7', '9', '7', '8', '2', '7', '4', '3', '1', '7', '9', '9', '2', '8', '8', '2', '2', '9', '9', '4', '4', '7', '3'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_bound

theorem simplex06_lookup_jensen_bound :
    rawSimplex06.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '3', '6', '7', '1', '6', '7', '0', '0', '8', '5', '1', '9', '9', '6', '0', '9', '7', '6', '3', '7', '2', '4', '7', '0', '1', '5', '8', '8', '7', '7', '3', '9', '2', '3', '7', '1', '0', '1', '7', '4', '5', '4', '1', '7', '5', '7', '9', '1', '5', '8', '7', '4', '4', '8', '8', '9', '7', '6', '5', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '9', '2', '8', '6', '9', '5', '0', '9', '4', '6', '2', '4', '3', '3', '9', '0', '1', '0', '5', '7', '5', '1', '0', '5', '9', '6', '9', '8', '7', '1', '4', '2', '1', '6', '1', '2', '1', '4', '4', '6', '5', '3', '0', '1', '1', '3', '4', '9', '8', '5', '2', '2', '6', '0', '7', '8', '5', '0', '2', '0', '9', '0', '7', '9', '3', '1', '3', '9', '7', '5', '3', '0', '6', '8', '8', '0', '3', '5', '4', '9', '6', '5', '8', '7', '6', '8', '3', '6', '9'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_bound

theorem simplex06_lookup_max_floor_Q96 :
    rawSimplex06.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '6', '6', '6', '8', '4', '6', '2', '2', '2', '6'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_floor_Q96

theorem simplex06_lookup_jensen_floor_Q96 :
    rawSimplex06.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '1', '4', '2', '1', '5', '9', '5', '7', '0', '7', '5'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_floor_Q96

theorem simplex06_decoded : decodeSimplex rawSimplex06 = .ok simplex06 := by
  unfold decodeSimplex simplex06
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex06_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
