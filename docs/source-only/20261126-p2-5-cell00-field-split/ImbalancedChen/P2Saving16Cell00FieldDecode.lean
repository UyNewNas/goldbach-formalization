import ImbalancedChen.P2Saving16Cell00FieldBase
import ImbalancedChen.P2Saving16Cell00Simplex00Decode
import ImbalancedChen.P2Saving16Cell00Simplex01Decode
import ImbalancedChen.P2Saving16Cell00Simplex02Decode
import ImbalancedChen.P2Saving16Cell00Simplex03Decode
import ImbalancedChen.P2Saving16Cell00Simplex04Decode
import ImbalancedChen.P2Saving16Cell00Simplex05Decode
import ImbalancedChen.P2Saving16Cell00Simplex06Decode
import ImbalancedChen.P2Saving16Cell00Simplex07Decode

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

attribute [local simp] lookup_dimension lookup_physical_jacobian lookup_cell_id lookup_left_masks lookup_right_masks lookup_facet_original_indices lookup_positive_normal_balance lookup_normal_rank lookup_active8_enumeration lookup_vertices lookup_vertex_values lookup_all_original_constraint_minima lookup_facet_vertices lookup_face_ledger lookup_simplices lookup_physical_volume lookup_integral_gap cellId_decoded cellId_field dimension_decoded dimension_field physicalJacobian_decoded physicalJacobian_field leftMasks_decoded leftMasks_field rightMasks_decoded rightMasks_field facetOriginalIndices_decoded facetOriginalIndices_field normalRank_decoded normalRank_field facetVertices_decoded facetVertices_field positiveNormalBalance_decoded positiveNormalBalance_field allOriginalMinima_decoded allOriginalMinima_field vertex00_decoded vertex01_decoded vertex02_decoded vertex03_decoded vertex04_decoded vertex05_decoded vertex06_decoded vertex07_decoded vertex08_decoded vertex09_decoded vertex10_decoded vertex11_decoded vertex12_decoded vertex13_decoded vertex14_decoded vertex15_decoded vertices_mapped simplex00_decoded simplex01_decoded simplex02_decoded simplex03_decoded simplex04_decoded simplex05_decoded simplex06_decoded simplex07_decoded

theorem simplices_mapped : rawSimplicesItems.toArray.mapM decodeSimplex = .ok simplices := by
  unfold rawSimplicesItems simplices
  simp

attribute [local simp] simplices_mapped

theorem physicalVolume_field : rationalField rawRoot "physical_volume" = .ok physicalVolume := by
  unfold rationalField physicalVolume
  simp [rawPhysicalVolume]

attribute [local simp] physicalVolume_field

theorem integralGap_field : rationalField rawRoot "integral_gap" = .ok integralGap := by
  unfold rationalField integralGap
  simp [rawIntegralGap]

attribute [local simp] integralGap_field

theorem rawRoot_decoded : decodeCell rawRoot = .ok cell00Payload := by
  unfold decodeCell cell00Payload
  simp [rawActive8, rawVertices, rawVertexValues, rawFaceLedger, rawSimplices]

attribute [local simp] rawRoot_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
