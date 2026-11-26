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

theorem lookup_dimension : rawRoot.getObjVal? "dimension" = .ok rawDimension := by
  rfl

attribute [local simp] lookup_dimension

theorem lookup_physical_jacobian : rawRoot.getObjVal? "physical_jacobian" = .ok rawPhysicalJacobian := by
  rfl

attribute [local simp] lookup_physical_jacobian

theorem lookup_cell_id : rawRoot.getObjVal? "cell_id" = .ok rawCellId := by
  rfl

attribute [local simp] lookup_cell_id

theorem lookup_left_masks : rawRoot.getObjVal? "left_masks" = .ok rawLeftMasks := by
  rfl

attribute [local simp] lookup_left_masks

theorem lookup_right_masks : rawRoot.getObjVal? "right_masks" = .ok rawRightMasks := by
  rfl

attribute [local simp] lookup_right_masks

theorem lookup_facet_original_indices : rawRoot.getObjVal? "facet_original_indices" = .ok rawFacetOriginalIndices := by
  rfl

attribute [local simp] lookup_facet_original_indices

theorem lookup_positive_normal_balance : rawRoot.getObjVal? "positive_normal_balance" = .ok rawPositiveNormalBalance := by
  rfl

attribute [local simp] lookup_positive_normal_balance

theorem lookup_normal_rank : rawRoot.getObjVal? "normal_rank" = .ok rawNormalRank := by
  rfl

attribute [local simp] lookup_normal_rank

theorem lookup_active8_enumeration : rawRoot.getObjVal? "active8_enumeration" = .ok rawActive8 := by
  rfl

attribute [local simp] lookup_active8_enumeration

theorem lookup_vertices : rawRoot.getObjVal? "vertices" = .ok rawVertices := by
  rfl

attribute [local simp] lookup_vertices

theorem lookup_vertex_values : rawRoot.getObjVal? "vertex_values" = .ok rawVertexValues := by
  rfl

attribute [local simp] lookup_vertex_values

theorem lookup_all_original_constraint_minima : rawRoot.getObjVal? "all_original_constraint_minima" = .ok rawAllOriginalMinima := by
  rfl

attribute [local simp] lookup_all_original_constraint_minima

theorem lookup_facet_vertices : rawRoot.getObjVal? "facet_vertices" = .ok rawFacetVertices := by
  rfl

attribute [local simp] lookup_facet_vertices

theorem lookup_face_ledger : rawRoot.getObjVal? "face_ledger" = .ok rawFaceLedger := by
  rfl

attribute [local simp] lookup_face_ledger

theorem lookup_simplices : rawRoot.getObjVal? "simplices" = .ok rawSimplices := by
  rfl

attribute [local simp] lookup_simplices

theorem lookup_physical_volume : rawRoot.getObjVal? "physical_volume" = .ok rawPhysicalVolume := by
  rfl

attribute [local simp] lookup_physical_volume

theorem lookup_integral_gap : rawRoot.getObjVal? "integral_gap" = .ok rawIntegralGap := by
  rfl

attribute [local simp] lookup_integral_gap

theorem cellId_decoded :
    (SourceJson.Decode.read rawCellId : Except String (Nat)) = .ok cellId := by
  unfold rawCellId cellId
  simp

attribute [local simp] cellId_decoded

theorem cellId_field : rawRoot.getObjValAs? (Nat) "cell_id" = .ok cellId := by
  rw [getObjValAs_of_lookup rawRoot "cell_id" rawCellId lookup_cell_id]
  exact cellId_decoded

attribute [local simp] cellId_field

theorem dimension_decoded :
    (SourceJson.Decode.read rawDimension : Except String (Nat)) = .ok dimension := by
  unfold rawDimension dimension
  simp

attribute [local simp] dimension_decoded

theorem dimension_field : rawRoot.getObjValAs? (Nat) "dimension" = .ok dimension := by
  rw [getObjValAs_of_lookup rawRoot "dimension" rawDimension lookup_dimension]
  exact dimension_decoded

attribute [local simp] dimension_field

theorem physicalJacobian_decoded :
    (SourceJson.Decode.read rawPhysicalJacobian : Except String (Nat)) = .ok physicalJacobian := by
  unfold rawPhysicalJacobian physicalJacobian
  simp

attribute [local simp] physicalJacobian_decoded

theorem physicalJacobian_field : rawRoot.getObjValAs? (Nat) "physical_jacobian" = .ok physicalJacobian := by
  rw [getObjValAs_of_lookup rawRoot "physical_jacobian" rawPhysicalJacobian lookup_physical_jacobian]
  exact physicalJacobian_decoded

attribute [local simp] physicalJacobian_field

theorem leftMasks_decoded :
    (SourceJson.Decode.read rawLeftMasks : Except String (Array Nat)) = .ok leftMasks := by
  unfold rawLeftMasks leftMasks
  simp

attribute [local simp] leftMasks_decoded

theorem leftMasks_field : rawRoot.getObjValAs? (Array Nat) "left_masks" = .ok leftMasks := by
  rw [getObjValAs_of_lookup rawRoot "left_masks" rawLeftMasks lookup_left_masks]
  exact leftMasks_decoded

attribute [local simp] leftMasks_field

theorem rightMasks_decoded :
    (SourceJson.Decode.read rawRightMasks : Except String (Array Nat)) = .ok rightMasks := by
  unfold rawRightMasks rightMasks
  simp

attribute [local simp] rightMasks_decoded

theorem rightMasks_field : rawRoot.getObjValAs? (Array Nat) "right_masks" = .ok rightMasks := by
  rw [getObjValAs_of_lookup rawRoot "right_masks" rawRightMasks lookup_right_masks]
  exact rightMasks_decoded

attribute [local simp] rightMasks_field

theorem facetOriginalIndices_decoded :
    (SourceJson.Decode.read rawFacetOriginalIndices : Except String (Array Nat)) = .ok facetOriginalIndices := by
  unfold rawFacetOriginalIndices facetOriginalIndices
  simp

attribute [local simp] facetOriginalIndices_decoded

theorem facetOriginalIndices_field : rawRoot.getObjValAs? (Array Nat) "facet_original_indices" = .ok facetOriginalIndices := by
  rw [getObjValAs_of_lookup rawRoot "facet_original_indices" rawFacetOriginalIndices lookup_facet_original_indices]
  exact facetOriginalIndices_decoded

attribute [local simp] facetOriginalIndices_field

theorem normalRank_decoded :
    (SourceJson.Decode.read rawNormalRank : Except String (Nat)) = .ok normalRank := by
  unfold rawNormalRank normalRank
  simp

attribute [local simp] normalRank_decoded

theorem normalRank_field : rawRoot.getObjValAs? (Nat) "normal_rank" = .ok normalRank := by
  rw [getObjValAs_of_lookup rawRoot "normal_rank" rawNormalRank lookup_normal_rank]
  exact normalRank_decoded

attribute [local simp] normalRank_field

theorem facetVertices_decoded :
    (SourceJson.Decode.read rawFacetVertices : Except String (Array (Array Nat))) = .ok facetVertices := by
  unfold rawFacetVertices facetVertices
  simp

attribute [local simp] facetVertices_decoded

theorem facetVertices_field : rawRoot.getObjValAs? (Array (Array Nat)) "facet_vertices" = .ok facetVertices := by
  rw [getObjValAs_of_lookup rawRoot "facet_vertices" rawFacetVertices lookup_facet_vertices]
  exact facetVertices_decoded

attribute [local simp] facetVertices_field

theorem positiveNormalBalance_decoded : rationalArray rawPositiveNormalBalance = .ok positiveNormalBalance := by
  unfold rawPositiveNormalBalance positiveNormalBalance
  simp

attribute [local simp] positiveNormalBalance_decoded

theorem positiveNormalBalance_field : rationalArrayField rawRoot "positive_normal_balance" = .ok positiveNormalBalance := by
  rw [rationalArrayField_of_lookup rawRoot "positive_normal_balance" rawPositiveNormalBalance lookup_positive_normal_balance]
  exact positiveNormalBalance_decoded

attribute [local simp] positiveNormalBalance_field

theorem allOriginalMinima_decoded : rationalArray rawAllOriginalMinima = .ok allOriginalMinima := by
  unfold rawAllOriginalMinima allOriginalMinima
  simp

attribute [local simp] allOriginalMinima_decoded

theorem allOriginalMinima_field : rationalArrayField rawRoot "all_original_constraint_minima" = .ok allOriginalMinima := by
  rw [rationalArrayField_of_lookup rawRoot "all_original_constraint_minima" rawAllOriginalMinima lookup_all_original_constraint_minima]
  exact allOriginalMinima_decoded

attribute [local simp] allOriginalMinima_field

theorem vertex00_decoded : rationalArray rawVertex00 = .ok vertex00 := by
  unfold rawVertex00 vertex00
  simp

attribute [local simp] vertex00_decoded

theorem vertex01_decoded : rationalArray rawVertex01 = .ok vertex01 := by
  unfold rawVertex01 vertex01
  simp

attribute [local simp] vertex01_decoded

theorem vertex02_decoded : rationalArray rawVertex02 = .ok vertex02 := by
  unfold rawVertex02 vertex02
  simp

attribute [local simp] vertex02_decoded

theorem vertex03_decoded : rationalArray rawVertex03 = .ok vertex03 := by
  unfold rawVertex03 vertex03
  simp

attribute [local simp] vertex03_decoded

theorem vertex04_decoded : rationalArray rawVertex04 = .ok vertex04 := by
  unfold rawVertex04 vertex04
  simp

attribute [local simp] vertex04_decoded

theorem vertex05_decoded : rationalArray rawVertex05 = .ok vertex05 := by
  unfold rawVertex05 vertex05
  simp

attribute [local simp] vertex05_decoded

theorem vertex06_decoded : rationalArray rawVertex06 = .ok vertex06 := by
  unfold rawVertex06 vertex06
  simp

attribute [local simp] vertex06_decoded

theorem vertex07_decoded : rationalArray rawVertex07 = .ok vertex07 := by
  unfold rawVertex07 vertex07
  simp

attribute [local simp] vertex07_decoded

theorem vertex08_decoded : rationalArray rawVertex08 = .ok vertex08 := by
  unfold rawVertex08 vertex08
  simp

attribute [local simp] vertex08_decoded

theorem vertex09_decoded : rationalArray rawVertex09 = .ok vertex09 := by
  unfold rawVertex09 vertex09
  simp

attribute [local simp] vertex09_decoded

theorem vertex10_decoded : rationalArray rawVertex10 = .ok vertex10 := by
  unfold rawVertex10 vertex10
  simp

attribute [local simp] vertex10_decoded

theorem vertex11_decoded : rationalArray rawVertex11 = .ok vertex11 := by
  unfold rawVertex11 vertex11
  simp

attribute [local simp] vertex11_decoded

theorem vertex12_decoded : rationalArray rawVertex12 = .ok vertex12 := by
  unfold rawVertex12 vertex12
  simp

attribute [local simp] vertex12_decoded

theorem vertex13_decoded : rationalArray rawVertex13 = .ok vertex13 := by
  unfold rawVertex13 vertex13
  simp

attribute [local simp] vertex13_decoded

theorem vertex14_decoded : rationalArray rawVertex14 = .ok vertex14 := by
  unfold rawVertex14 vertex14
  simp

attribute [local simp] vertex14_decoded

theorem vertex15_decoded : rationalArray rawVertex15 = .ok vertex15 := by
  unfold rawVertex15 vertex15
  simp

attribute [local simp] vertex15_decoded

theorem vertices_mapped : rawVerticesItems.toArray.mapM rationalArray = .ok vertices := by
  unfold rawVerticesItems vertices
  simp

attribute [local simp] vertices_mapped


end ImbalancedChen.P2Saving16Cell00FieldDecode
