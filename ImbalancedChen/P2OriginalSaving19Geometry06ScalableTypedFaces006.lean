import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerBlock006

/-! Local original face_ledger decoding, indices 56 through 61.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson056 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped056 : FaceRecord :=
  { vertices := #[7, 11, 12, 14, 16],
    dimension := 4, pivot := 16,
    facetSets := #[#[7, 11, 12, 14], #[7, 11, 12, 16], #[7, 11, 14, 16], #[7, 12, 14, 16], #[11, 12, 14, 16]],
    simplices := 1 }

theorem decode_geometry_Faces_056 : decodeFace geometryFacesJson056 = .ok geometryFacesTyped056 := by decide +kernel

theorem geometryFaces_056_shape : geometryFacesTyped056.vertices.size = 5 ∧ geometryFacesTyped056.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped056.vertices[i.val]! < 33) ∧
    geometryFacesTyped056.pivot < 33 ∧ geometryFacesTyped056.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson057 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped057 : FaceRecord :=
  { vertices := #[7, 11, 12, 14, 16, 17],
    dimension := 5, pivot := 17,
    facetSets := #[#[7, 11, 12, 14, 16], #[7, 11, 12, 14, 17], #[7, 11, 12, 16, 17], #[7, 11, 14, 16, 17], #[7, 12, 14, 16, 17], #[11, 12, 14, 16, 17]],
    simplices := 1 }

theorem decode_geometry_Faces_057 : decodeFace geometryFacesJson057 = .ok geometryFacesTyped057 := by decide +kernel

theorem geometryFaces_057_shape : geometryFacesTyped057.vertices.size = 6 ∧ geometryFacesTyped057.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped057.vertices[i.val]! < 33) ∧
    geometryFacesTyped057.pivot < 33 ∧ geometryFacesTyped057.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson058 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped058 : FaceRecord :=
  { vertices := #[7, 11, 12, 14, 16, 17, 19],
    dimension := 6, pivot := 19,
    facetSets := #[#[7, 11, 12, 14, 16, 17], #[7, 11, 12, 14, 16, 19], #[7, 11, 12, 14, 17, 19], #[7, 11, 12, 16, 17, 19], #[7, 11, 14, 16, 17, 19], #[7, 12, 14, 16, 17, 19], #[11, 12, 14, 16, 17, 19]],
    simplices := 1 }

theorem decode_geometry_Faces_058 : decodeFace geometryFacesJson058 = .ok geometryFacesTyped058 := by decide +kernel

theorem geometryFaces_058_shape : geometryFacesTyped058.vertices.size = 7 ∧ geometryFacesTyped058.vertices.toList.Nodup ∧
    (∀ i : Fin 7, geometryFacesTyped058.vertices[i.val]! < 33) ∧
    geometryFacesTyped058.pivot < 33 ∧ geometryFacesTyped058.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson059 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped059 : FaceRecord :=
  { vertices := #[7, 11, 12, 14, 16, 19],
    dimension := 5, pivot := 19,
    facetSets := #[#[7, 11, 12, 14, 16], #[7, 11, 12, 14, 19], #[7, 11, 12, 16, 19], #[7, 11, 14, 16, 19], #[7, 12, 14, 16, 19], #[11, 12, 14, 16, 19]],
    simplices := 1 }

theorem decode_geometry_Faces_059 : decodeFace geometryFacesJson059 = .ok geometryFacesTyped059 := by decide +kernel

theorem geometryFaces_059_shape : geometryFacesTyped059.vertices.size = 6 ∧ geometryFacesTyped059.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped059.vertices[i.val]! < 33) ∧
    geometryFacesTyped059.pivot < 33 ∧ geometryFacesTyped059.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson060 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped060 : FaceRecord :=
  { vertices := #[7, 11, 14],
    dimension := 2, pivot := 14,
    facetSets := #[#[7, 11], #[7, 14], #[11, 14]],
    simplices := 1 }

theorem decode_geometry_Faces_060 : decodeFace geometryFacesJson060 = .ok geometryFacesTyped060 := by decide +kernel

theorem geometryFaces_060_shape : geometryFacesTyped060.vertices.size = 3 ∧ geometryFacesTyped060.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped060.vertices[i.val]! < 33) ∧
    geometryFacesTyped060.pivot < 33 ∧ geometryFacesTyped060.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson061 : SourceJson :=
  (FaceLedgerBlock006.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped061 : FaceRecord :=
  { vertices := #[7, 14],
    dimension := 1, pivot := 14,
    facetSets := #[#[7], #[14]],
    simplices := 1 }

theorem decode_geometry_Faces_061 : decodeFace geometryFacesJson061 = .ok geometryFacesTyped061 := by decide +kernel

theorem geometryFaces_061_shape : geometryFacesTyped061.vertices.size = 2 ∧ geometryFacesTyped061.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped061.vertices[i.val]! < 33) ∧
    geometryFacesTyped061.pivot < 33 ∧ geometryFacesTyped061.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock006 : List SourceJson := [geometryFacesJson056, geometryFacesJson057, geometryFacesJson058, geometryFacesJson059, geometryFacesJson060, geometryFacesJson061]
noncomputable def geometryFacesTypedBlock006 : List (FaceRecord) := [geometryFacesTyped056, geometryFacesTyped057, geometryFacesTyped058, geometryFacesTyped059, geometryFacesTyped060, geometryFacesTyped061]

theorem geometry_Faces_block_006_push_eq (acc : List SourceJson) :
    FaceLedgerBlock006.blockPush acc = [geometryFacesJson061, geometryFacesJson060, geometryFacesJson059, geometryFacesJson058, geometryFacesJson057, geometryFacesJson056] ++ acc := by rfl

theorem geometry_Faces_block_006_reverse (acc : List SourceJson) :
    (FaceLedgerBlock006.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock006 := by
  rw [geometry_Faces_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_006 : geometryFacesJsonBlock006.mapM decodeFace = .ok geometryFacesTypedBlock006 := by
  simp only [geometryFacesJsonBlock006, geometryFacesTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_056, decode_geometry_Faces_057, decode_geometry_Faces_058, decode_geometry_Faces_059, decode_geometry_Faces_060, decode_geometry_Faces_061]
  rfl

theorem geometry_Faces_block_006_length : geometryFacesTypedBlock006.length = 6 := by rfl

#print axioms decode_geometry_Faces_056
#print axioms geometryFaces_056_shape
#print axioms decode_geometry_Faces_057
#print axioms geometryFaces_057_shape
#print axioms decode_geometry_Faces_058
#print axioms geometryFaces_058_shape
#print axioms decode_geometry_Faces_059
#print axioms geometryFaces_059_shape
#print axioms decode_geometry_Faces_060
#print axioms geometryFaces_060_shape
#print axioms decode_geometry_Faces_061
#print axioms geometryFaces_061_shape
#print axioms geometry_Faces_block_006_push_eq
#print axioms geometry_Faces_block_006_reverse
#print axioms decode_geometry_Faces_block_006
#print axioms geometry_Faces_block_006_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
