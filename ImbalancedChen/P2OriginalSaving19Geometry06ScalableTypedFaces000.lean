import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerBlock000

/-! Local original face_ledger decoding, indices 0 through 8.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson000 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped000 : FaceRecord :=
  { vertices := #[0, 1],
    dimension := 1, pivot := 1,
    facetSets := #[#[0], #[1]],
    simplices := 1 }

theorem decode_geometry_Faces_000 : decodeFace geometryFacesJson000 = .ok geometryFacesTyped000 := by decide +kernel

theorem geometryFaces_000_shape : geometryFacesTyped000.vertices.size = 2 ∧ geometryFacesTyped000.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped000.vertices[i.val]! < 33) ∧
    geometryFacesTyped000.pivot < 33 ∧ geometryFacesTyped000.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson001 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped001 : FaceRecord :=
  { vertices := #[0, 1, 2],
    dimension := 2, pivot := 2,
    facetSets := #[#[0, 1], #[0, 2], #[1, 2]],
    simplices := 1 }

theorem decode_geometry_Faces_001 : decodeFace geometryFacesJson001 = .ok geometryFacesTyped001 := by decide +kernel

theorem geometryFaces_001_shape : geometryFacesTyped001.vertices.size = 3 ∧ geometryFacesTyped001.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped001.vertices[i.val]! < 33) ∧
    geometryFacesTyped001.pivot < 33 ∧ geometryFacesTyped001.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson002 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped002 : FaceRecord :=
  { vertices := #[0, 1, 2, 3],
    dimension := 3, pivot := 3,
    facetSets := #[#[0, 1, 2], #[0, 1, 3], #[0, 2, 3], #[1, 2, 3]],
    simplices := 1 }

theorem decode_geometry_Faces_002 : decodeFace geometryFacesJson002 = .ok geometryFacesTyped002 := by decide +kernel

theorem geometryFaces_002_shape : geometryFacesTyped002.vertices.size = 4 ∧ geometryFacesTyped002.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped002.vertices[i.val]! < 33) ∧
    geometryFacesTyped002.pivot < 33 ∧ geometryFacesTyped002.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson003 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped003 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4],
    dimension := 4, pivot := 4,
    facetSets := #[#[0, 1, 2, 3], #[0, 1, 2, 4], #[0, 1, 3, 4], #[0, 2, 3, 4], #[1, 2, 3, 4]],
    simplices := 1 }

theorem decode_geometry_Faces_003 : decodeFace geometryFacesJson003 = .ok geometryFacesTyped003 := by decide +kernel

theorem geometryFaces_003_shape : geometryFacesTyped003.vertices.size = 5 ∧ geometryFacesTyped003.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped003.vertices[i.val]! < 33) ∧
    geometryFacesTyped003.pivot < 33 ∧ geometryFacesTyped003.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson004 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped004 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5],
    dimension := 5, pivot := 5,
    facetSets := #[#[0, 1, 2, 3, 4], #[0, 1, 2, 3, 5], #[0, 1, 2, 4, 5], #[0, 1, 3, 4, 5], #[0, 2, 3, 4, 5], #[1, 2, 3, 4, 5]],
    simplices := 1 }

theorem decode_geometry_Faces_004 : decodeFace geometryFacesJson004 = .ok geometryFacesTyped004 := by decide +kernel

theorem geometryFaces_004_shape : geometryFacesTyped004.vertices.size = 6 ∧ geometryFacesTyped004.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped004.vertices[i.val]! < 33) ∧
    geometryFacesTyped004.pivot < 33 ∧ geometryFacesTyped004.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson005 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped005 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6],
    dimension := 6, pivot := 6,
    facetSets := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 6], #[0, 1, 2, 3, 5, 6], #[0, 1, 2, 4, 5, 6], #[0, 1, 3, 4, 5, 6], #[0, 2, 3, 4, 5, 6], #[1, 2, 3, 4, 5, 6]],
    simplices := 1 }

theorem decode_geometry_Faces_005 : decodeFace geometryFacesJson005 = .ok geometryFacesTyped005 := by decide +kernel

theorem geometryFaces_005_shape : geometryFacesTyped005.vertices.size = 7 ∧ geometryFacesTyped005.vertices.toList.Nodup ∧
    (∀ i : Fin 7, geometryFacesTyped005.vertices[i.val]! < 33) ∧
    geometryFacesTyped005.pivot < 33 ∧ geometryFacesTyped005.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson006 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped006 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32],
    dimension := 8, pivot := 32,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20], #[0, 1, 2, 3, 4, 5, 6, 9, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32], #[0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 21, 22, 23, 24, 25, 26, 27, 28, 31, 32], #[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30], #[0, 1, 2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 15, 16, 17, 18, 19, 20, 21, 23, 25, 26, 27, 28, 29, 30, 31, 32], #[0, 1, 2, 4, 5, 6, 8, 10, 13, 15, 18, 20, 21, 22, 23, 27, 29, 32], #[0, 1, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30, 31, 32], #[0, 2, 3, 4, 5, 6, 7, 8, 9, 11, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 24, 25, 27, 28, 29, 30, 31, 32], #[1, 2, 3, 4, 5, 6, 7, 9, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20, 22, 23, 24, 26, 27, 28, 29, 30, 31, 32], #[7, 9, 11, 12, 14, 16, 17, 19, 24, 25, 26, 28, 30, 31], #[8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]],
    simplices := 113 }

theorem decode_geometry_Faces_006 : decodeFace geometryFacesJson006 = .ok geometryFacesTyped006 := by decide +kernel

theorem geometryFaces_006_shape : geometryFacesTyped006.vertices.size = 33 ∧ geometryFacesTyped006.vertices.toList.Nodup ∧
    (∀ i : Fin 33, geometryFacesTyped006.vertices[i.val]! < 33) ∧
    geometryFacesTyped006.pivot < 33 ∧ geometryFacesTyped006.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson007 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped007 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20],
    dimension := 7, pivot := 20,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6], #[0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18], #[0, 1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 19, 20], #[0, 1, 2, 3, 5, 6, 7, 8, 10, 11, 12, 15, 16, 17, 18, 19, 20], #[0, 1, 2, 4, 5, 6, 8, 10, 13, 15, 18, 20], #[0, 1, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13, 14, 17, 18, 19, 20], #[0, 2, 3, 4, 5, 6, 7, 8, 11, 13, 14, 15, 16, 17, 18, 19, 20], #[1, 2, 3, 4, 5, 6, 7, 10, 12, 13, 14, 15, 16, 17, 18, 19, 20], #[7, 11, 12, 14, 16, 17, 19], #[8, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20]],
    simplices := 19 }

theorem decode_geometry_Faces_007 : decodeFace geometryFacesJson007 = .ok geometryFacesTyped007 := by decide +kernel

theorem geometryFaces_007_shape : geometryFacesTyped007.vertices.size = 20 ∧ geometryFacesTyped007.vertices.toList.Nodup ∧
    (∀ i : Fin 20, geometryFacesTyped007.vertices[i.val]! < 33) ∧
    geometryFacesTyped007.pivot < 33 ∧ geometryFacesTyped007.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson008 : SourceJson :=
  (FaceLedgerBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped008 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 15, 16, 17, 18],
    dimension := 6, pivot := 18,
    facetSets := #[#[0, 1, 2, 3, 4, 5], #[0, 1, 2, 3, 4, 7, 8, 10, 11, 12, 13, 14, 15, 16], #[0, 1, 2, 3, 5, 7, 8, 10, 11, 12, 15, 16, 17, 18], #[0, 1, 2, 4, 5, 8, 10, 13, 15, 18], #[0, 1, 3, 4, 5, 7, 8, 10, 11, 12, 13, 14, 17, 18], #[0, 2, 3, 4, 5, 7, 8, 11, 13, 14, 15, 16, 17, 18], #[1, 2, 3, 4, 5, 7, 10, 12, 13, 14, 15, 16, 17, 18], #[7, 11, 12, 14, 16, 17], #[8, 10, 11, 12, 13, 14, 15, 16, 17, 18]],
    simplices := 17 }

theorem decode_geometry_Faces_008 : decodeFace geometryFacesJson008 = .ok geometryFacesTyped008 := by decide +kernel

theorem geometryFaces_008_shape : geometryFacesTyped008.vertices.size = 17 ∧ geometryFacesTyped008.vertices.toList.Nodup ∧
    (∀ i : Fin 17, geometryFacesTyped008.vertices[i.val]! < 33) ∧
    geometryFacesTyped008.pivot < 33 ∧ geometryFacesTyped008.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock000 : List SourceJson := [geometryFacesJson000, geometryFacesJson001, geometryFacesJson002, geometryFacesJson003, geometryFacesJson004, geometryFacesJson005, geometryFacesJson006, geometryFacesJson007, geometryFacesJson008]
noncomputable def geometryFacesTypedBlock000 : List (FaceRecord) := [geometryFacesTyped000, geometryFacesTyped001, geometryFacesTyped002, geometryFacesTyped003, geometryFacesTyped004, geometryFacesTyped005, geometryFacesTyped006, geometryFacesTyped007, geometryFacesTyped008]

theorem geometry_Faces_block_000_push_eq (acc : List SourceJson) :
    FaceLedgerBlock000.blockPush acc = [geometryFacesJson008, geometryFacesJson007, geometryFacesJson006, geometryFacesJson005, geometryFacesJson004, geometryFacesJson003, geometryFacesJson002, geometryFacesJson001, geometryFacesJson000] ++ acc := by rfl

theorem geometry_Faces_block_000_reverse (acc : List SourceJson) :
    (FaceLedgerBlock000.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock000 := by
  rw [geometry_Faces_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_000 : geometryFacesJsonBlock000.mapM decodeFace = .ok geometryFacesTypedBlock000 := by
  simp only [geometryFacesJsonBlock000, geometryFacesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_000, decode_geometry_Faces_001, decode_geometry_Faces_002, decode_geometry_Faces_003, decode_geometry_Faces_004, decode_geometry_Faces_005, decode_geometry_Faces_006, decode_geometry_Faces_007, decode_geometry_Faces_008]
  rfl

theorem geometry_Faces_block_000_length : geometryFacesTypedBlock000.length = 9 := by rfl

#print axioms decode_geometry_Faces_000
#print axioms geometryFaces_000_shape
#print axioms decode_geometry_Faces_001
#print axioms geometryFaces_001_shape
#print axioms decode_geometry_Faces_002
#print axioms geometryFaces_002_shape
#print axioms decode_geometry_Faces_003
#print axioms geometryFaces_003_shape
#print axioms decode_geometry_Faces_004
#print axioms geometryFaces_004_shape
#print axioms decode_geometry_Faces_005
#print axioms geometryFaces_005_shape
#print axioms decode_geometry_Faces_006
#print axioms geometryFaces_006_shape
#print axioms decode_geometry_Faces_007
#print axioms geometryFaces_007_shape
#print axioms decode_geometry_Faces_008
#print axioms geometryFaces_008_shape
#print axioms geometry_Faces_block_000_push_eq
#print axioms geometry_Faces_block_000_reverse
#print axioms decode_geometry_Faces_block_000
#print axioms geometry_Faces_block_000_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
