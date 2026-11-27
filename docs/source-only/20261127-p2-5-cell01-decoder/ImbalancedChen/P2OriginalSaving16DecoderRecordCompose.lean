import ImbalancedChen.P2OriginalSaving16DecoderCompose

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.
Cell01 specialization of the existing original-decoder proof decomposition.
All data, field order, scalar spellings and row order come from the unchanged
published typed candidate. These equalities require actual Lean checking.
No geometric validity, integral estimate, Q96 endpoint or P2.5 is asserted.
-/
namespace ImbalancedChen.P2OriginalSaving16OriginalArchive
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive

/- Public extraction of the existing Cell00 symbolic composition proof. -/
theorem decodeCell_of_field_successes
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

end ImbalancedChen.P2OriginalSaving16OriginalArchive
