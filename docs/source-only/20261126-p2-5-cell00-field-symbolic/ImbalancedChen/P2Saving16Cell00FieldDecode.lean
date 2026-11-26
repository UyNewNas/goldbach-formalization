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
Final-owner retry after attempt005 exhausted kernel memory without unsolved goals.
A single private theorem composes symbolic decoder field successes. The closed
final theorem applies that opaque result to the nineteen existing certificates.
The four public statements, imports, and first three theorem commands are unchanged.
The complete owned audit must include the new private composition declaration.
No decoder, certificate value, array order, or mathematical guard is changed.
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

/- The symbolic root and field values keep closed payloads out of the
intermediate equality motives. Every premise is supplied below by an existing
field or array certificate; this introduces no new mathematical input. -/
private theorem decodeCell_of_field_successes
    (j : SourceJson)
    (cellId dimension physicalJacobian : Nat)
    (leftMasks rightMasks facetOriginalIndices : Array Nat)
    (positiveNormalBalance : Array ℚ) (normalRank : Nat)
    (activeItems vertexItems vertexValueItems faceItems simplexItems : List SourceJson)
    (vertices : Array (Array ℚ)) (allOriginalMinima : Array ℚ)
    (facetVertices : Array (Array Nat)) (simplices : Array SimplexRecord)
    (physicalVolume integralGap : ℚ)
    (hCellId : j.getObjValAs? Nat "cell_id" = .ok cellId)
    (hDimension : j.getObjValAs? Nat "dimension" = .ok dimension)
    (hPhysicalJacobian : j.getObjValAs? Nat "physical_jacobian" = .ok physicalJacobian)
    (hLeftMasks : j.getObjValAs? (Array Nat) "left_masks" = .ok leftMasks)
    (hRightMasks : j.getObjValAs? (Array Nat) "right_masks" = .ok rightMasks)
    (hFacetOriginalIndices : j.getObjValAs? (Array Nat) "facet_original_indices" = .ok facetOriginalIndices)
    (hPositiveNormalBalance : rationalArrayField j "positive_normal_balance" = .ok positiveNormalBalance)
    (hNormalRank : j.getObjValAs? Nat "normal_rank" = .ok normalRank)
    (hActive : j.getObjVal? "active8_enumeration" = .ok (.arr activeItems))
    (hVertices : j.getObjVal? "vertices" = .ok (.arr vertexItems))
    (hVertexValues : j.getObjVal? "vertex_values" = .ok (.arr vertexValueItems))
    (hAllOriginalMinima : rationalArrayField j "all_original_constraint_minima" = .ok allOriginalMinima)
    (hFacetVertices : j.getObjValAs? (Array (Array Nat)) "facet_vertices" = .ok facetVertices)
    (hFaceLedger : j.getObjVal? "face_ledger" = .ok (.arr faceItems))
    (hSimplices : j.getObjVal? "simplices" = .ok (.arr simplexItems))
    (hPhysicalVolume : rationalField j "physical_volume" = .ok physicalVolume)
    (hIntegralGap : rationalField j "integral_gap" = .ok integralGap)
    (hVerticesMapped : vertexItems.toArray.mapM rationalArray = .ok vertices)
    (hSimplicesMapped : simplexItems.toArray.mapM decodeSimplex = .ok simplices) :
    decodeCell j = .ok {
      cellId := cellId
      dimension := dimension
      physicalJacobian := physicalJacobian
      leftMasks := leftMasks
      rightMasks := rightMasks
      facetOriginalIndices := facetOriginalIndices
      positiveNormalBalance := positiveNormalBalance
      normalRank := normalRank
      active8 := activeItems.toArray
      vertices := vertices
      vertexValues := vertexValueItems.toArray
      allOriginalMinima := allOriginalMinima
      facetVertices := facetVertices
      faceLedger := faceItems.toArray
      simplices := simplices
      physicalVolume := physicalVolume
      integralGap := integralGap } := by
  unfold decodeCell
  rewrite [hCellId, hDimension, hPhysicalJacobian, hLeftMasks, hRightMasks,
    hFacetOriginalIndices, hPositiveNormalBalance, hNormalRank, hActive,
    hVertices, hVertexValues, hAllOriginalMinima, hFacetVertices, hFaceLedger,
    hSimplices, hPhysicalVolume, hIntegralGap]
  change
    (do
      let decodedVertices ← vertexItems.toArray.mapM rationalArray
      let decodedSimplices ← simplexItems.toArray.mapM decodeSimplex
      pure ({
        cellId := cellId
        dimension := dimension
        physicalJacobian := physicalJacobian
        leftMasks := leftMasks
        rightMasks := rightMasks
        facetOriginalIndices := facetOriginalIndices
        positiveNormalBalance := positiveNormalBalance
        normalRank := normalRank
        active8 := activeItems.toArray
        vertices := decodedVertices
        vertexValues := vertexValueItems.toArray
        allOriginalMinima := allOriginalMinima
        facetVertices := facetVertices
        faceLedger := faceItems.toArray
        simplices := decodedSimplices
        physicalVolume := physicalVolume
        integralGap := integralGap
      } : CellRecord)) = _
  rewrite [hVerticesMapped, hSimplicesMapped]
  rfl

theorem rawRoot_decoded : decodeCell rawRoot = .ok cell00Payload := by
  exact decodeCell_of_field_successes rawRoot
    cellId dimension physicalJacobian leftMasks rightMasks facetOriginalIndices
    positiveNormalBalance normalRank
    rawActive8Items rawVerticesItems rawVertexValuesItems rawFaceLedgerItems rawSimplicesItems
    vertices allOriginalMinima facetVertices simplices physicalVolume integralGap
    cellId_field dimension_field physicalJacobian_field leftMasks_field rightMasks_field
    facetOriginalIndices_field positiveNormalBalance_field normalRank_field
    lookup_active8_enumeration lookup_vertices lookup_vertex_values
    allOriginalMinima_field facetVertices_field lookup_face_ledger lookup_simplices
    physicalVolume_field integralGap_field vertices_mapped simplices_mapped

attribute [local simp] rawRoot_decoded


end ImbalancedChen.P2Saving16Cell00FieldDecode
