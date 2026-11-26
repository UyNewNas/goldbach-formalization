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

theorem simplex07_lookup_simplex_id :
    rawSimplex07.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7'])) := by
  rfl

attribute [local simp] simplex07_lookup_simplex_id

theorem simplex07_lookup_vertex_ids :
    rawSimplex07.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_vertex_ids

theorem simplex07_lookup_physical_volume :
    rawSimplex07.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '4', '0', '1', '4', '5', '4', '6', '3', '7', '6', '1', '6', '3', '8', '8', '5', '2', '8', '9', '8', '5', '6', '3', '6', '5', '6', '9', '8', '4', '7', '0', '8', '3', '1', '0', '7', '/', '1', '7', '4', '9', '9', '2', '8', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_physical_volume

theorem simplex07_lookup_mean_gap :
    rawSimplex07.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_mean_gap

theorem simplex07_lookup_factor_maxima :
    rawSimplex07.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '8', '5', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_factor_maxima

theorem simplex07_lookup_gap_weighted_means :
    rawSimplex07.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['6', '9', '8', '3', '4', '2', '4', '3', '6', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '9', '7', '5', '1', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '3', '8', '8', '4', '2', '5', '2', '9', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '1', '7', '2', '0', '1', '0', '7', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '3', '8', '0', '9', '8', '0', '9', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '4', '9', '2', '7', '3', '3', '/', '2', '8', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '1', '5', '4', '8', '9', '7', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '0', '6', '4', '8', '0', '3', '4', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_gap_weighted_means

theorem simplex07_lookup_max_bound :
    rawSimplex07.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '8', '4', '3', '7', '4', '6', '6', '5', '2', '9', '1', '4', '0', '3', '7', '1', '4', '0', '0', '7', '0', '9', '1', '4', '8', '2', '5', '9', '3', '3', '9', '3', '4', '3', '9', '4', '3', '3', '6', '4', '3', '6', '2', '2', '4', '0', '0', '0', '0', '0', '/', '7', '9', '0', '2', '0', '4', '8', '6', '7', '8', '6', '2', '4', '7', '7', '9', '5', '3', '1', '4', '1', '1', '5', '0', '9', '2', '7', '0', '7', '2', '5', '2', '0', '3', '8', '5', '5', '8', '0', '5', '7', '6', '9', '5', '6', '1', '5', '6', '2', '6', '4', '8', '6', '6', '5', '6', '9', '7', '1', '0', '8', '4', '6', '9'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_bound

theorem simplex07_lookup_jensen_bound :
    rawSimplex07.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['5', '1', '9', '8', '4', '7', '2', '5', '2', '4', '9', '6', '9', '1', '8', '2', '9', '0', '5', '6', '5', '5', '1', '5', '1', '8', '8', '9', '1', '8', '6', '5', '0', '4', '0', '6', '0', '7', '4', '6', '9', '1', '8', '1', '7', '7', '8', '4', '0', '8', '8', '3', '2', '9', '6', '7', '6', '7', '7', '8', '9', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '6', '0', '9', '0', '9', '1', '8', '1', '0', '4', '5', '8', '3', '6', '0', '8', '0', '6', '1', '4', '2', '2', '5', '7', '5', '6', '0', '9', '0', '7', '5', '5', '4', '8', '9', '6', '6', '3', '1', '3', '2', '3', '7', '9', '7', '6', '0', '0', '0', '1', '1', '4', '2', '5', '8', '0', '7', '8', '6', '7', '8', '0', '3', '9', '7', '3', '8', '0', '4', '2', '8', '9', '0', '5', '5', '0', '7', '5', '7', '4', '1', '9', '5', '2', '4', '2', '8', '9'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_bound

theorem simplex07_lookup_max_floor_Q96 :
    rawSimplex07.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '8', '4', '8', '5', '9', '2', '2', '4', '9', '8', '4', '7', '1', '1', '7'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_floor_Q96

theorem simplex07_lookup_jensen_floor_Q96 :
    rawSimplex07.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '7', '8', '4', '0', '7', '5', '1', '9', '7', '5', '0', '0', '6', '3', '1'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_floor_Q96

theorem simplex07_decoded : decodeSimplex rawSimplex07 = .ok simplex07 := by
  unfold decodeSimplex simplex07
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex07_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
