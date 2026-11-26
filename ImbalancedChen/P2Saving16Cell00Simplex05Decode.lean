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

theorem simplex05_lookup_simplex_id :
    rawSimplex05.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5'])) := by
  rfl

attribute [local simp] simplex05_lookup_simplex_id

theorem simplex05_lookup_vertex_ids :
    rawSimplex05.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_vertex_ids

theorem simplex05_lookup_physical_volume :
    rawSimplex05.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '0', '7', '2', '9', '1', '2', '9', '6', '4', '9', '4', '4', '1', '1', '9', '2', '5', '2', '3', '7', '2', '3', '0', '4', '3', '0', '8', '0', '3', '2', '5', '3', '/', '6', '1', '0', '6', '5', '2', '2', '8', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_physical_volume

theorem simplex05_lookup_mean_gap :
    rawSimplex05.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_mean_gap

theorem simplex05_lookup_factor_maxima :
    rawSimplex05.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_factor_maxima

theorem simplex05_lookup_gap_weighted_means :
    rawSimplex05.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '7', '9', '3', '3', '6', '6', '3', '7', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '1', '3', '0', '9', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '1', '9', '4', '2', '2', '1', '0', '8', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '3', '8', '2', '4', '5', '0', '1', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '0', '5', '3', '8', '3', '1', '6', '9', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '2', '0', '8', '2', '4', '0', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '0', '7', '8', '2', '9', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '1', '2', '9', '4', '3', '8', '1', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_gap_weighted_means

theorem simplex05_lookup_max_bound :
    rawSimplex05.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '6', '8', '7', '0', '2', '4', '1', '6', '3', '4', '0', '9', '5', '6', '7', '2', '1', '4', '1', '8', '1', '1', '3', '4', '5', '9', '1', '9', '5', '7', '2', '6', '3', '0', '8', '9', '4', '8', '5', '7', '4', '2', '0', '8', '0', '0', '0', '0', '0', '/', '5', '6', '4', '7', '3', '8', '7', '9', '8', '9', '6', '3', '7', '9', '2', '5', '7', '4', '2', '3', '9', '6', '0', '9', '2', '4', '2', '8', '2', '7', '3', '1', '2', '6', '7', '9', '1', '3', '0', '7', '8', '2', '4', '8', '6', '3', '3', '7', '7', '7', '3', '5', '6', '9', '4', '0', '9', '3', '4', '1', '4', '3', '9', '5', '7', '6', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_bound

theorem simplex05_lookup_jensen_bound :
    rawSimplex05.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '0', '7', '1', '0', '3', '1', '6', '5', '9', '6', '1', '1', '3', '4', '8', '3', '3', '4', '8', '0', '5', '8', '6', '2', '8', '7', '3', '0', '5', '7', '6', '9', '2', '1', '3', '3', '9', '9', '7', '7', '0', '2', '7', '9', '8', '9', '6', '7', '1', '6', '8', '6', '7', '0', '6', '6', '8', '7', '0', '7', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '8', '3', '9', '3', '0', '7', '2', '6', '5', '9', '9', '4', '2', '2', '5', '6', '4', '5', '8', '0', '4', '0', '9', '3', '2', '1', '7', '9', '8', '7', '4', '1', '3', '2', '0', '8', '3', '3', '5', '6', '5', '9', '5', '3', '9', '8', '0', '0', '6', '9', '0', '1', '7', '7', '4', '2', '9', '0', '8', '8', '6', '3', '4', '7', '3', '1', '6', '4', '1', '9', '2', '6', '8', '1', '9', '0', '1', '5', '9', '2', '6', '9', '1', '6', '5', '5', '3', '8', '1', '0', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_bound

theorem simplex05_lookup_max_floor_Q96 :
    rawSimplex05.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '6', '6', '7', '5', '4', '7', '6', '9', '2', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_floor_Q96

theorem simplex05_lookup_jensen_floor_Q96 :
    rawSimplex05.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '1', '3', '1', '5', '1', '1', '4', '0', '8', '3', '8'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_floor_Q96

theorem simplex05_decoded : decodeSimplex rawSimplex05 = .ok simplex05 := by
  unfold decodeSimplex simplex05
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex05_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
