import ImbalancedChen.P2OriginalSaving16FaceDecoderCore
import ImbalancedChen.P2OriginalSaving16PullingFaceInduction
import ImbalancedChen.P2Saving16Cell01TypedPayload

/-!
SOURCE ONLY / UNCOMPILED / ZERO FORMAL CREDIT.

Cell01 specializations of the existing retained-face decoder, exact
max-pivot recursion, finite Shape guard, and ordered row/Nodup guard.
All face records and simplex rows come from the unchanged typed payload.
The original algorithms, fuel 9, and saved row order are retained.

The parse-success theorem rejects the default error branch. Shape checks
only finite vertex-ID incidence; Nodup is a list property. Neither is a
geometric disjointness, coverage, integral, or final endpoint premise.
The existing separating-wall induction remains a separate proof supplier.
No correspondence with the parsed original archive is claimed here.
-/
namespace ImbalancedChen.P2Saving16Cell01TypedPulling
noncomputable section

open P2OriginalSaving16PullingOwnership (FaceRecord decodeFace)
open P2OriginalSaving16PullingFaceInduction (Shape pull)
open P2Saving16Cell01TypedPayload (cell01Payload)

set_option Elab.async false

def parsedFaces : Except String (Array FaceRecord) :=
  cell01Payload.faceLedger.mapM decodeFace

def faces : Array FaceRecord := parsedFaces.toOption.getD #[]

def facesParseSuccess : Bool :=
  match parsedFaces with
  | .ok _ => true
  | .error _ => false

/-- Constructor success for the original retained raw face-ledger fields. -/
theorem cell01_faces_parse_tag : facesParseSuccess = true := by
  decide +kernel

/-- A default face array cannot witness this successful decode equality. -/
theorem cell01_faces_parse : parsedFaces = .ok faces := by
  cases h : parsedFaces with
  | error message =>
      have hs := cell01_faces_parse_tag
      simp [facesParseSuccess, h] at hs
  | ok record => simp [faces, h]

def faceRecord (face : List Nat) : FaceRecord :=
  (faces.toList.find? (fun f => f.vertices.toList == face)).getD default

def pivot (face : List Nat) : Nat := (faceRecord face).pivot

def children (face : List Nat) : List (List Nat) :=
  (((faceRecord face).facetSets.toList.map Array.toList).filter
    (fun child => !(child.contains (pivot face))))

def whole : List Nat := List.range cell01Payload.vertices.size

abbrev FacetIndex := Fin cell01Payload.facetOriginalIndices.size

def facet (f : FacetIndex) : List Nat :=
  (cell01Payload.facetVertices.getD f.val #[]).toList

def originalPull : List (List Nat) := pull pivot children 9 whole

def savedRows : List (List Nat) :=
  cell01Payload.simplices.toList.map (fun r => r.vertexIds.toList)

/-- The unchanged finite Shape predicate on the original Cell01 root. -/
theorem cell01_face_incidence_shape : Shape facet pivot children 9 whole := by
  decide +kernel

/-- Exact saved order and list-level Nodup; no geometric overlap guard. -/
theorem cell01_pulling_bindings : originalPull = savedRows ∧ savedRows.Nodup := by
  decide +kernel

#print axioms cell01_faces_parse_tag
#print axioms cell01_faces_parse
#print axioms cell01_face_incidence_shape
#print axioms cell01_pulling_bindings

end

end ImbalancedChen.P2Saving16Cell01TypedPulling
