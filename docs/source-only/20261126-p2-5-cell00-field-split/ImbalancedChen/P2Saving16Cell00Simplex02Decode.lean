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

theorem simplex02_lookup_simplex_id :
    rawSimplex02.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2'])) := by
  rfl

attribute [local simp] simplex02_lookup_simplex_id

theorem simplex02_lookup_vertex_ids :
    rawSimplex02.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_vertex_ids

theorem simplex02_lookup_physical_volume :
    rawSimplex02.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '6', '7', '6', '5', '8', '7', '4', '9', '9', '6', '2', '1', '7', '1', '8', '6', '9', '6', '7', '1', '7', '5', '3', '1', '1', '8', '7', '2', '4', '3', '/', '8', '6', '8', '6', '9', '8', '4', '4', '0', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex02_lookup_physical_volume

theorem simplex02_lookup_mean_gap :
    rawSimplex02.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex02_lookup_mean_gap

theorem simplex02_lookup_factor_maxima :
    rawSimplex02.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_factor_maxima

theorem simplex02_lookup_gap_weighted_means :
    rawSimplex02.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '5', '6', '4', '1', '2', '7', '/', '4', '2', '8', '9', '0', '6', '2', '5']), .str (String.ofList ['5', '7', '4', '4', '7', '7', '9', '/', '6', '8', '6', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '0', '8', '0', '4', '3', '7', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '4', '6', '5', '0', '1', '9', '/', '1', '0', '6', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '0', '6', '7', '7', '8', '9', '3', '/', '3', '2', '0', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '7', '8', '7', '6', '8', '1', '/', '5', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '4', '2', '3', '8', '7', '/', '1', '0', '9', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '4', '6', '2', '0', '3', '1', '/', '2', '7', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '8', '3', '6', '0', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '5', '0', '8', '1', '4', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_gap_weighted_means

theorem simplex02_lookup_max_bound :
    rawSimplex02.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '8', '4', '9', '8', '8', '4', '4', '6', '6', '9', '6', '5', '0', '0', '3', '7', '8', '6', '3', '8', '6', '1', '0', '9', '6', '8', '0', '8', '4', '4', '6', '5', '7', '1', '9', '2', '3', '3', '7', '4', '0', '8', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7'])) := by
  rfl

attribute [local simp] simplex02_lookup_max_bound

theorem simplex02_lookup_jensen_bound :
    rawSimplex02.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '4', '2', '9', '7', '2', '3', '4', '2', '1', '8', '0', '3', '7', '0', '6', '1', '4', '7', '8', '9', '2', '7', '5', '4', '7', '7', '2', '0', '2', '6', '0', '9', '5', '7', '2', '4', '2', '3', '0', '3', '1', '5', '1', '0', '8', '4', '0', '9', '7', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '5', '3', '3', '2', '8', '2', '9', '8', '9', '5', '1', '1', '3', '9', '3', '6', '9', '9', '9', '6', '7', '2', '3', '2', '5', '5', '4', '9', '4', '5', '0', '1', '2', '7', '3', '4', '1', '8', '0', '8', '6', '6', '9', '9', '3', '4', '6', '1', '5', '7', '1', '3', '6', '6', '5', '3', '2', '7', '8', '3', '4', '2', '1', '5', '9', '9', '8', '9', '2', '5', '0', '8', '9', '8', '3', '5', '4', '7', '9'])) := by
  rfl

attribute [local simp] simplex02_lookup_jensen_bound

theorem simplex02_lookup_max_floor_Q96 :
    rawSimplex02.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '5', '2', '9', '4', '6', '4', '5', '0', '7', '4'])) := by
  rfl

attribute [local simp] simplex02_lookup_max_floor_Q96

theorem simplex02_lookup_jensen_floor_Q96 :
    rawSimplex02.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '8', '7', '7', '0', '0', '7', '9', '5', '4', '8'])) := by
  rfl

attribute [local simp] simplex02_lookup_jensen_floor_Q96

theorem simplex02_decoded : decodeSimplex rawSimplex02 = .ok simplex02 := by
  unfold decodeSimplex simplex02
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex02_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
