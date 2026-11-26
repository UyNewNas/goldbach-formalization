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

theorem simplex04_lookup_simplex_id :
    rawSimplex04.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4'])) := by
  rfl

attribute [local simp] simplex04_lookup_simplex_id

theorem simplex04_lookup_vertex_ids :
    rawSimplex04.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_vertex_ids

theorem simplex04_lookup_physical_volume :
    rawSimplex04.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '3', '9', '5', '0', '8', '6', '6', '3', '0', '0', '3', '0', '1', '6', '3', '1', '6', '6', '0', '8', '5', '0', '1', '1', '2', '8', '1', '9', '3', '7', '2', '8', '9', '0', '7', '/', '4', '4', '3', '4', '4', '9', '8', '7', '0', '7', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_physical_volume

theorem simplex04_lookup_mean_gap :
    rawSimplex04.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '1', '9', '9', '6', '4', '8', '9', '/', '1', '8', '3', '9', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_mean_gap

theorem simplex04_lookup_factor_maxima :
    rawSimplex04.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_factor_maxima

theorem simplex04_lookup_gap_weighted_means :
    rawSimplex04.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '2', '7', '5', '2', '1', '7', '0', '6', '7', '0', '1', '9', '0', '9', '2', '3', '3', '9', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '8', '8', '2', '7', '0', '7', '2', '9', '8', '9', '7', '1', '5', '7', '3', '7', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '8', '3', '4', '4', '4', '7', '0', '2', '2', '0', '9', '0', '1', '6', '6', '7', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '9', '0', '7', '1', '8', '2', '3', '1', '2', '3', '5', '6', '2', '4', '0', '7', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '9', '8', '8', '1', '6', '0', '7', '3', '6', '6', '4', '8', '1', '4', '0', '1', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '3', '0', '8', '1', '0', '7', '8', '2', '3', '2', '0', '2', '4', '9', '8', '7', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '4', '8', '3', '0', '9', '0', '1', '0', '7', '3', '3', '5', '7', '6', '0', '1', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '6', '7', '6', '4', '5', '3', '1', '2', '3', '5', '0', '5', '9', '7', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '7', '9', '3', '8', '9', '8', '0', '5', '2', '9', '7', '3', '9', '0', '5', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '4', '9', '6', '4', '1', '4', '0', '6', '9', '7', '4', '9', '6', '2', '9', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_gap_weighted_means

theorem simplex04_lookup_max_bound :
    rawSimplex04.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '9', '3', '9', '7', '0', '5', '4', '7', '4', '3', '4', '9', '5', '5', '0', '9', '3', '3', '3', '5', '2', '0', '5', '3', '6', '3', '4', '9', '2', '6', '7', '4', '3', '5', '3', '2', '5', '5', '3', '6', '6', '6', '5', '0', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '/', '4', '1', '2', '4', '2', '1', '3', '4', '8', '3', '8', '5', '6', '5', '6', '1', '0', '9', '9', '7', '7', '9', '9', '5', '8', '7', '2', '9', '3', '8', '0', '1', '9', '5', '8', '3', '9', '2', '5', '7', '8', '2', '1', '4', '5', '3', '1', '8', '8', '7', '8', '0', '7', '6', '8', '7', '4', '4', '1', '1', '8', '6', '3', '2', '4', '2', '0', '2', '9'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_bound

theorem simplex04_lookup_jensen_bound :
    rawSimplex04.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '5', '4', '3', '9', '4', '4', '6', '1', '4', '6', '7', '1', '2', '8', '3', '5', '8', '1', '1', '1', '9', '1', '6', '8', '5', '2', '3', '1', '0', '6', '2', '4', '6', '2', '5', '7', '4', '5', '7', '7', '3', '2', '2', '8', '3', '4', '8', '5', '2', '6', '2', '0', '1', '4', '6', '3', '9', '6', '1', '3', '5', '8', '1', '4', '3', '3', '0', '9', '9', '1', '6', '7', '8', '7', '7', '4', '0', '1', '8', '6', '3', '7', '9', '6', '3', '1', '9', '5', '4', '3', '2', '5', '0', '4', '4', '0', '7', '8', '1', '7', '6', '3', '5', '4', '0', '3', '9', '8', '8', '0', '9', '0', '6', '3', '6', '7', '5', '8', '6', '1', '8', '1', '8', '2', '1', '4', '1', '5', '5', '1', '5', '7', '8', '5', '1', '8', '2', '1', '6', '3', '7', '9', '6', '6', '3', '7', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '6', '3', '2', '6', '2', '2', '2', '5', '9', '3', '6', '6', '2', '0', '2', '0', '6', '2', '9', '9', '2', '6', '3', '1', '7', '7', '3', '2', '4', '0', '6', '6', '4', '9', '8', '9', '4', '6', '1', '2', '1', '7', '2', '1', '4', '8', '9', '1', '7', '8', '8', '9', '9', '9', '0', '1', '5', '4', '2', '3', '1', '5', '9', '1', '1', '1', '4', '2', '7', '3', '9', '4', '9', '4', '3', '8', '6', '0', '5', '2', '7', '6', '7', '0', '9', '4', '8', '7', '7', '5', '3', '6', '8', '2', '9', '1', '2', '7', '1', '4', '2', '2', '4', '0', '8', '9', '1', '0', '0', '8', '0', '2', '1', '8', '3', '7', '1', '6', '7', '8', '2', '1', '1', '2', '7', '0', '7', '3', '2', '5', '6', '6', '5', '9', '4', '1', '5', '2', '3', '3', '2', '5', '5', '5', '4', '5', '7', '8', '6', '1', '7', '1', '1', '3', '9', '3', '4', '4', '0', '5', '5', '6', '2', '4', '6', '4', '2', '2', '4', '6', '6', '9', '3'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_bound

theorem simplex04_lookup_max_floor_Q96 :
    rawSimplex04.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '5', '2', '5', '2', '5', '6', '3', '3', '8', '2', '0', '7', '1', '4', '8'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_floor_Q96

theorem simplex04_lookup_jensen_floor_Q96 :
    rawSimplex04.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '9', '8', '0', '6', '7', '5', '8', '6', '3', '9', '9', '1', '6', '2', '2'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_floor_Q96

theorem simplex04_decoded : decodeSimplex rawSimplex04 = .ok simplex04 := by
  unfold decodeSimplex simplex04
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex04_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
