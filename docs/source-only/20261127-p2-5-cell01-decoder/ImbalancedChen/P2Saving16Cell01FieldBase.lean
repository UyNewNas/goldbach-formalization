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

theorem vertex16_decoded : rationalArray rawVertex16 = .ok vertex16 := by
  unfold rawVertex16 vertex16
  simp

attribute [local simp] vertex16_decoded

theorem vertex17_decoded : rationalArray rawVertex17 = .ok vertex17 := by
  unfold rawVertex17 vertex17
  simp

attribute [local simp] vertex17_decoded

theorem vertex18_decoded : rationalArray rawVertex18 = .ok vertex18 := by
  unfold rawVertex18 vertex18
  simp

attribute [local simp] vertex18_decoded

theorem vertex19_decoded : rationalArray rawVertex19 = .ok vertex19 := by
  unfold rawVertex19 vertex19
  simp

attribute [local simp] vertex19_decoded

theorem vertex20_decoded : rationalArray rawVertex20 = .ok vertex20 := by
  unfold rawVertex20 vertex20
  simp

attribute [local simp] vertex20_decoded

theorem vertex21_decoded : rationalArray rawVertex21 = .ok vertex21 := by
  unfold rawVertex21 vertex21
  simp

attribute [local simp] vertex21_decoded

theorem vertex22_decoded : rationalArray rawVertex22 = .ok vertex22 := by
  unfold rawVertex22 vertex22
  simp

attribute [local simp] vertex22_decoded

theorem vertex23_decoded : rationalArray rawVertex23 = .ok vertex23 := by
  unfold rawVertex23 vertex23
  simp

attribute [local simp] vertex23_decoded

theorem vertex24_decoded : rationalArray rawVertex24 = .ok vertex24 := by
  unfold rawVertex24 vertex24
  simp

attribute [local simp] vertex24_decoded

theorem vertex25_decoded : rationalArray rawVertex25 = .ok vertex25 := by
  unfold rawVertex25 vertex25
  simp

attribute [local simp] vertex25_decoded

theorem vertex26_decoded : rationalArray rawVertex26 = .ok vertex26 := by
  unfold rawVertex26 vertex26
  simp

attribute [local simp] vertex26_decoded

theorem vertex27_decoded : rationalArray rawVertex27 = .ok vertex27 := by
  unfold rawVertex27 vertex27
  simp

attribute [local simp] vertex27_decoded

theorem vertex28_decoded : rationalArray rawVertex28 = .ok vertex28 := by
  unfold rawVertex28 vertex28
  simp

attribute [local simp] vertex28_decoded

theorem vertex29_decoded : rationalArray rawVertex29 = .ok vertex29 := by
  unfold rawVertex29 vertex29
  simp

attribute [local simp] vertex29_decoded

theorem vertex30_decoded : rationalArray rawVertex30 = .ok vertex30 := by
  unfold rawVertex30 vertex30
  simp

attribute [local simp] vertex30_decoded

theorem vertex31_decoded : rationalArray rawVertex31 = .ok vertex31 := by
  unfold rawVertex31 vertex31
  simp

attribute [local simp] vertex31_decoded

theorem vertex32_decoded : rationalArray rawVertex32 = .ok vertex32 := by
  unfold rawVertex32 vertex32
  simp

attribute [local simp] vertex32_decoded

theorem vertex33_decoded : rationalArray rawVertex33 = .ok vertex33 := by
  unfold rawVertex33 vertex33
  simp

attribute [local simp] vertex33_decoded

theorem vertex34_decoded : rationalArray rawVertex34 = .ok vertex34 := by
  unfold rawVertex34 vertex34
  simp

attribute [local simp] vertex34_decoded

theorem vertices_mapped : rawVerticesItems.toArray.mapM rationalArray = .ok vertices := by
  unfold rawVerticesItems vertices
  simp

attribute [local simp] vertices_mapped


end ImbalancedChen.P2Saving16Cell01FieldDecode
