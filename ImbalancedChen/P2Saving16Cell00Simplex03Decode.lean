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

theorem simplex03_lookup_simplex_id :
    rawSimplex03.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3'])) := by
  rfl

attribute [local simp] simplex03_lookup_simplex_id

theorem simplex03_lookup_vertex_ids :
    rawSimplex03.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_vertex_ids

theorem simplex03_lookup_physical_volume :
    rawSimplex03.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '7', '0', '6', '1', '3', '5', '3', '3', '5', '7', '5', '3', '7', '9', '1', '8', '9', '8', '5', '5', '5', '9', '1', '9', '0', '9', '8', '6', '1', '3', '/', '3', '4', '7', '4', '7', '9', '3', '7', '6', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_physical_volume

theorem simplex03_lookup_mean_gap :
    rawSimplex03.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_mean_gap

theorem simplex03_lookup_factor_maxima :
    rawSimplex03.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_factor_maxima

theorem simplex03_lookup_gap_weighted_means :
    rawSimplex03.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '1', '9', '3', '4', '5', '8', '8', '9', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '8', '5', '3', '8', '6', '6', '9', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '8', '6', '3', '4', '3', '9', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0']), .str (String.ofList ['1', '2', '7', '7', '0', '1', '4', '1', '9', '/', '1', '2', '8', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '0', '4', '2', '5', '8', '7', '/', '4', '2', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '4', '5', '1', '4', '1', '3', '3', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '4', '4', '8', '3', '9', '1', '1', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '1', '5', '4', '3', '/', '2', '4', '0', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '7', '0', '7', '3', '9', '7', '3', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '1', '7', '4', '2', '3', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_gap_weighted_means

theorem simplex03_lookup_max_bound :
    rawSimplex03.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '8', '4', '9', '2', '4', '9', '0', '9', '4', '4', '5', '2', '0', '8', '3', '9', '8', '9', '8', '4', '1', '3', '7', '0', '2', '5', '0', '9', '3', '2', '9', '7', '4', '6', '5', '6', '6', '8', '4', '0', '3', '2', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_bound

theorem simplex03_lookup_jensen_bound :
    rawSimplex03.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '5', '8', '0', '4', '0', '4', '0', '6', '3', '7', '1', '9', '8', '7', '0', '9', '8', '4', '7', '7', '4', '2', '1', '5', '8', '0', '6', '5', '9', '0', '7', '4', '3', '2', '2', '9', '4', '6', '4', '0', '8', '2', '2', '4', '7', '1', '5', '0', '0', '6', '9', '3', '2', '1', '9', '9', '2', '1', '8', '7', '5', '0', '/', '1', '6', '9', '4', '5', '0', '9', '4', '2', '1', '6', '0', '7', '7', '9', '3', '4', '3', '3', '9', '0', '7', '4', '5', '6', '6', '7', '9', '2', '9', '5', '3', '2', '1', '0', '3', '6', '0', '2', '0', '3', '0', '2', '7', '7', '0', '9', '3', '1', '2', '7', '7', '4', '5', '9', '9', '8', '5', '9', '2', '4', '5', '6', '8', '4', '5', '1', '3', '7', '1', '5', '2', '8', '7', '7', '6', '6', '6', '3', '3'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_bound

theorem simplex03_lookup_max_floor_Q96 :
    rawSimplex03.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '5', '2', '8', '5', '5', '1', '3', '1', '1', '2'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_floor_Q96

theorem simplex03_lookup_jensen_floor_Q96 :
    rawSimplex03.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '8', '9', '3', '0', '7', '3', '9', '4', '9', '2'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_floor_Q96

theorem simplex03_decoded : decodeSimplex rawSimplex03 = .ok simplex03 := by
  unfold decodeSimplex simplex03
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex03_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
