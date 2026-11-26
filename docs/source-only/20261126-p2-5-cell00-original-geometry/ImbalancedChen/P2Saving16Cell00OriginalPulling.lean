import ImbalancedChen.P2Saving16Cell00OriginalFloors
import ImbalancedChen.P2Saving16Cell00TypedPulling

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Transport the four existing typed Cell00 face-ledger and pulling guards to
the unchanged original archive. The conclusions spell out the original
decoder, face lookup, omitted-pivot child filter, fuel-nine Shape, and
ordered pulling algorithm at archive index zero. No new algorithm or
record is defined, and no finite decision is repeated.

The original payload equality and the typed pulling owner must receive
their actual compilation, kernel replay, and complete owned audits before
this consumer receives proof credit. No Literal96 or global all-fourteen
archive guard is imported. These are finite incidence and row-binding
facts; geometric separation and the integral endpoint remain separate.
-/
namespace ImbalancedChen.P2Saving16Cell00OriginalPulling

open P2OriginalSaving16OriginalArchive (archive)
open P2OriginalSaving16PullingOwnership (FaceRecord decodeFace)
open P2OriginalSaving16PullingFaceInduction (Shape pull)
open P2Saving16Cell00OriginalFloors (cell00_original_payload)

/-- The retained original face ledger reaches the success constructor. -/
theorem cell00_original_faces_parse_tag :
    (match (archive (0 : Fin 14)).faceLedger.mapM decodeFace with
      | .ok _ => true
      | .error _ => false) = true := by
  simpa only [cell00_original_payload,
    P2Saving16Cell00TypedPulling.facesParseSuccess,
    P2Saving16Cell00TypedPulling.parsedFaces] using
    P2Saving16Cell00TypedPulling.cell00_faces_parse_tag

/-- The default face array is not used as evidence of successful parsing. -/
theorem cell00_original_faces_parse :
    (archive (0 : Fin 14)).faceLedger.mapM decodeFace =
      .ok (((archive (0 : Fin 14)).faceLedger.mapM decodeFace).toOption.getD #[]) := by
  simpa only [cell00_original_payload,
    P2Saving16Cell00TypedPulling.parsedFaces,
    P2Saving16Cell00TypedPulling.faces] using
    P2Saving16Cell00TypedPulling.cell00_faces_parse

/-- The complete original finite Shape predicate, without a coverage claim. -/
theorem cell00_original_face_incidence_shape :
    let c := archive (0 : Fin 14)
    let decodedFaces : Array FaceRecord :=
      (c.faceLedger.mapM decodeFace).toOption.getD #[]
    let record := fun (face : List Nat) =>
      (decodedFaces.toList.find? (fun f => f.vertices.toList == face)).getD default
    let pvt := fun (face : List Nat) => (record face).pivot
    let child := fun (face : List Nat) =>
      (((record face).facetSets.toList.map Array.toList).filter
        (fun candidate => !(candidate.contains (pvt face))))
    let facets := fun (f : Fin c.facetOriginalIndices.size) =>
      (c.facetVertices.getD f.val #[]).toList
    Shape facets pvt child 9 (List.range c.vertices.size) := by
  simpa only [cell00_original_payload,
    P2Saving16Cell00TypedPulling.facet,
    P2Saving16Cell00TypedPulling.pivot,
    P2Saving16Cell00TypedPulling.children,
    P2Saving16Cell00TypedPulling.faceRecord,
    P2Saving16Cell00TypedPulling.faces,
    P2Saving16Cell00TypedPulling.parsedFaces,
    P2Saving16Cell00TypedPulling.whole] using
    P2Saving16Cell00TypedPulling.cell00_face_incidence_shape

/-- Exact original saved order and list Nodup, retaining the same fuel nine. -/
theorem cell00_original_pulling_bindings :
    let c := archive (0 : Fin 14)
    let decodedFaces : Array FaceRecord :=
      (c.faceLedger.mapM decodeFace).toOption.getD #[]
    let record := fun (face : List Nat) =>
      (decodedFaces.toList.find? (fun f => f.vertices.toList == face)).getD default
    let pvt := fun (face : List Nat) => (record face).pivot
    let child := fun (face : List Nat) =>
      (((record face).facetSets.toList.map Array.toList).filter
        (fun candidate => !(candidate.contains (pvt face))))
    let saved := c.simplices.toList.map (fun r => r.vertexIds.toList)
    pull pvt child 9 (List.range c.vertices.size) = saved ∧ saved.Nodup := by
  simpa only [cell00_original_payload,
    P2Saving16Cell00TypedPulling.originalPull,
    P2Saving16Cell00TypedPulling.savedRows,
    P2Saving16Cell00TypedPulling.pivot,
    P2Saving16Cell00TypedPulling.children,
    P2Saving16Cell00TypedPulling.faceRecord,
    P2Saving16Cell00TypedPulling.faces,
    P2Saving16Cell00TypedPulling.parsedFaces,
    P2Saving16Cell00TypedPulling.whole] using
    P2Saving16Cell00TypedPulling.cell00_pulling_bindings

#print axioms cell00_original_faces_parse_tag
#print axioms cell00_original_faces_parse
#print axioms cell00_original_face_incidence_shape
#print axioms cell00_original_pulling_bindings

end ImbalancedChen.P2Saving16Cell00OriginalPulling
