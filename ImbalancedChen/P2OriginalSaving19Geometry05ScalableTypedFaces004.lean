import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerBlock004

/-! Local original face_ledger decoding, indices 36 through 44.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson036 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped036 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 15, 17, 19, 21],
    dimension := 4, pivot := 21,
    facetSets := #[#[1, 3, 5, 7], #[1, 3, 5, 15, 17, 21], #[1, 3, 7, 17, 19, 21], #[1, 5, 7, 15, 17, 19], #[3, 5, 7, 15, 19, 21], #[15, 17, 19, 21]],
    simplices := 4 }

theorem decode_geometry_Faces_036 : decodeFace geometryFacesJson036 = .ok geometryFacesTyped036 := by decide +kernel

theorem geometryFaces_036_shape : geometryFacesTyped036.vertices.size = 8 ∧ geometryFacesTyped036.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped036.vertices[i.val]! < 28) ∧
    geometryFacesTyped036.pivot < 28 ∧ geometryFacesTyped036.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson037 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped037 : FaceRecord :=
  { vertices := #[1, 5],
    dimension := 1, pivot := 5,
    facetSets := #[#[1], #[5]],
    simplices := 1 }

theorem decode_geometry_Faces_037 : decodeFace geometryFacesJson037 = .ok geometryFacesTyped037 := by decide +kernel

theorem geometryFaces_037_shape : geometryFacesTyped037.vertices.size = 2 ∧ geometryFacesTyped037.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped037.vertices[i.val]! < 28) ∧
    geometryFacesTyped037.pivot < 28 ∧ geometryFacesTyped037.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson038 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped038 : FaceRecord :=
  { vertices := #[1, 5, 7],
    dimension := 2, pivot := 7,
    facetSets := #[#[1, 5], #[1, 7], #[5, 7]],
    simplices := 1 }

theorem decode_geometry_Faces_038 : decodeFace geometryFacesJson038 = .ok geometryFacesTyped038 := by decide +kernel

theorem geometryFaces_038_shape : geometryFacesTyped038.vertices.size = 3 ∧ geometryFacesTyped038.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped038.vertices[i.val]! < 28) ∧
    geometryFacesTyped038.pivot < 28 ∧ geometryFacesTyped038.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson039 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped039 : FaceRecord :=
  { vertices := #[1, 5, 7, 15, 17, 19],
    dimension := 3, pivot := 19,
    facetSets := #[#[1, 5, 7], #[1, 5, 15, 17], #[1, 7, 17, 19], #[5, 7, 15, 19], #[15, 17, 19]],
    simplices := 3 }

theorem decode_geometry_Faces_039 : decodeFace geometryFacesJson039 = .ok geometryFacesTyped039 := by decide +kernel

theorem geometryFaces_039_shape : geometryFacesTyped039.vertices.size = 6 ∧ geometryFacesTyped039.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped039.vertices[i.val]! < 28) ∧
    geometryFacesTyped039.pivot < 28 ∧ geometryFacesTyped039.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson040 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped040 : FaceRecord :=
  { vertices := #[1, 5, 15, 17],
    dimension := 2, pivot := 17,
    facetSets := #[#[1, 5], #[1, 17], #[5, 15], #[15, 17]],
    simplices := 2 }

theorem decode_geometry_Faces_040 : decodeFace geometryFacesJson040 = .ok geometryFacesTyped040 := by decide +kernel

theorem geometryFaces_040_shape : geometryFacesTyped040.vertices.size = 4 ∧ geometryFacesTyped040.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped040.vertices[i.val]! < 28) ∧
    geometryFacesTyped040.pivot < 28 ∧ geometryFacesTyped040.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson041 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped041 : FaceRecord :=
  { vertices := #[4, 5],
    dimension := 1, pivot := 5,
    facetSets := #[#[4], #[5]],
    simplices := 1 }

theorem decode_geometry_Faces_041 : decodeFace geometryFacesJson041 = .ok geometryFacesTyped041 := by decide +kernel

theorem geometryFaces_041_shape : geometryFacesTyped041.vertices.size = 2 ∧ geometryFacesTyped041.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped041.vertices[i.val]! < 28) ∧
    geometryFacesTyped041.pivot < 28 ∧ geometryFacesTyped041.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson042 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped042 : FaceRecord :=
  { vertices := #[4, 5, 14, 15],
    dimension := 2, pivot := 15,
    facetSets := #[#[4, 5], #[4, 14], #[5, 15], #[14, 15]],
    simplices := 2 }

theorem decode_geometry_Faces_042 : decodeFace geometryFacesJson042 = .ok geometryFacesTyped042 := by decide +kernel

theorem geometryFaces_042_shape : geometryFacesTyped042.vertices.size = 4 ∧ geometryFacesTyped042.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped042.vertices[i.val]! < 28) ∧
    geometryFacesTyped042.pivot < 28 ∧ geometryFacesTyped042.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson043 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped043 : FaceRecord :=
  { vertices := #[4, 14],
    dimension := 1, pivot := 14,
    facetSets := #[#[4], #[14]],
    simplices := 1 }

theorem decode_geometry_Faces_043 : decodeFace geometryFacesJson043 = .ok geometryFacesTyped043 := by decide +kernel

theorem geometryFaces_043_shape : geometryFacesTyped043.vertices.size = 2 ∧ geometryFacesTyped043.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped043.vertices[i.val]! < 28) ∧
    geometryFacesTyped043.pivot < 28 ∧ geometryFacesTyped043.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson044 : SourceJson :=
  (FaceLedgerBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped044 : FaceRecord :=
  { vertices := #[5, 15],
    dimension := 1, pivot := 15,
    facetSets := #[#[5], #[15]],
    simplices := 1 }

theorem decode_geometry_Faces_044 : decodeFace geometryFacesJson044 = .ok geometryFacesTyped044 := by decide +kernel

theorem geometryFaces_044_shape : geometryFacesTyped044.vertices.size = 2 ∧ geometryFacesTyped044.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped044.vertices[i.val]! < 28) ∧
    geometryFacesTyped044.pivot < 28 ∧ geometryFacesTyped044.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock004 : List SourceJson := [geometryFacesJson036, geometryFacesJson037, geometryFacesJson038, geometryFacesJson039, geometryFacesJson040, geometryFacesJson041, geometryFacesJson042, geometryFacesJson043, geometryFacesJson044]
noncomputable def geometryFacesTypedBlock004 : List (FaceRecord) := [geometryFacesTyped036, geometryFacesTyped037, geometryFacesTyped038, geometryFacesTyped039, geometryFacesTyped040, geometryFacesTyped041, geometryFacesTyped042, geometryFacesTyped043, geometryFacesTyped044]

theorem geometry_Faces_block_004_push_eq (acc : List SourceJson) :
    FaceLedgerBlock004.blockPush acc = [geometryFacesJson044, geometryFacesJson043, geometryFacesJson042, geometryFacesJson041, geometryFacesJson040, geometryFacesJson039, geometryFacesJson038, geometryFacesJson037, geometryFacesJson036] ++ acc := by rfl

theorem geometry_Faces_block_004_reverse (acc : List SourceJson) :
    (FaceLedgerBlock004.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock004 := by
  rw [geometry_Faces_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_004 : geometryFacesJsonBlock004.mapM decodeFace = .ok geometryFacesTypedBlock004 := by
  simp only [geometryFacesJsonBlock004, geometryFacesTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_036, decode_geometry_Faces_037, decode_geometry_Faces_038, decode_geometry_Faces_039, decode_geometry_Faces_040, decode_geometry_Faces_041, decode_geometry_Faces_042, decode_geometry_Faces_043, decode_geometry_Faces_044]
  rfl

theorem geometry_Faces_block_004_length : geometryFacesTypedBlock004.length = 9 := by rfl

#print axioms decode_geometry_Faces_036
#print axioms geometryFaces_036_shape
#print axioms decode_geometry_Faces_037
#print axioms geometryFaces_037_shape
#print axioms decode_geometry_Faces_038
#print axioms geometryFaces_038_shape
#print axioms decode_geometry_Faces_039
#print axioms geometryFaces_039_shape
#print axioms decode_geometry_Faces_040
#print axioms geometryFaces_040_shape
#print axioms decode_geometry_Faces_041
#print axioms geometryFaces_041_shape
#print axioms decode_geometry_Faces_042
#print axioms geometryFaces_042_shape
#print axioms decode_geometry_Faces_043
#print axioms geometryFaces_043_shape
#print axioms decode_geometry_Faces_044
#print axioms geometryFaces_044_shape
#print axioms geometry_Faces_block_004_push_eq
#print axioms geometry_Faces_block_004_reverse
#print axioms decode_geometry_Faces_block_004
#print axioms geometry_Faces_block_004_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
