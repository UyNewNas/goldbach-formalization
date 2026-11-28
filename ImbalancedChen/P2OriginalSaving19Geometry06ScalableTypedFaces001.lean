import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerBlock001

/-! Local original face_ledger decoding, indices 9 through 16.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson009 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped009 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 6],
    dimension := 5, pivot := 6,
    facetSets := #[#[0, 1, 2, 3, 4], #[0, 1, 2, 3, 6], #[0, 1, 2, 4, 6], #[0, 1, 3, 4, 6], #[0, 2, 3, 4, 6], #[1, 2, 3, 4, 6]],
    simplices := 1 }

theorem decode_geometry_Faces_009 : decodeFace geometryFacesJson009 = .ok geometryFacesTyped009 := by decide +kernel

theorem geometryFaces_009_shape : geometryFacesTyped009.vertices.size = 6 ∧ geometryFacesTyped009.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped009.vertices[i.val]! < 33) ∧
    geometryFacesTyped009.pivot < 33 ∧ geometryFacesTyped009.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson010 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped010 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30],
    dimension := 7, pivot := 30,
    facetSets := #[#[0, 1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 19, 20], #[0, 1, 2, 3, 4, 6, 9, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30], #[0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 21, 22, 23, 24, 25, 26, 27, 28], #[0, 1, 2, 3, 6, 7, 8, 9, 10, 11, 12, 15, 16, 19, 20, 21, 23, 25, 26, 27, 28, 29, 30], #[0, 1, 2, 4, 6, 8, 10, 13, 15, 20, 21, 22, 23, 27, 29], #[0, 1, 3, 4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 19, 20, 21, 22, 23, 24, 25, 26, 29, 30], #[0, 2, 3, 4, 6, 7, 8, 9, 11, 13, 14, 15, 16, 19, 20, 21, 22, 24, 25, 27, 28, 29, 30], #[1, 2, 3, 4, 6, 7, 9, 10, 12, 13, 14, 15, 16, 19, 20, 22, 23, 24, 26, 27, 28, 29, 30], #[7, 9, 11, 12, 14, 16, 19, 24, 25, 26, 28, 30], #[8, 10, 11, 12, 13, 14, 15, 16, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30]],
    simplices := 87 }

theorem decode_geometry_Faces_010 : decodeFace geometryFacesJson010 = .ok geometryFacesTyped010 := by decide +kernel

theorem geometryFaces_010_shape : geometryFacesTyped010.vertices.size = 28 ∧ geometryFacesTyped010.vertices.toList.Nodup ∧
    (∀ i : Fin 28, geometryFacesTyped010.vertices[i.val]! < 33) ∧
    geometryFacesTyped010.pivot < 33 ∧ geometryFacesTyped010.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson011 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped011 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 15, 16, 19, 20],
    dimension := 6, pivot := 20,
    facetSets := #[#[0, 1, 2, 3, 4, 6], #[0, 1, 2, 3, 4, 7, 8, 10, 11, 12, 13, 14, 15, 16], #[0, 1, 2, 3, 6, 7, 8, 10, 11, 12, 15, 16, 19, 20], #[0, 1, 2, 4, 6, 8, 10, 13, 15, 20], #[0, 1, 3, 4, 6, 7, 8, 10, 11, 12, 13, 14, 19, 20], #[0, 2, 3, 4, 6, 7, 8, 11, 13, 14, 15, 16, 19, 20], #[1, 2, 3, 4, 6, 7, 10, 12, 13, 14, 15, 16, 19, 20], #[7, 11, 12, 14, 16, 19], #[8, 10, 11, 12, 13, 14, 15, 16, 19, 20]],
    simplices := 17 }

theorem decode_geometry_Faces_011 : decodeFace geometryFacesJson011 = .ok geometryFacesTyped011 := by decide +kernel

theorem geometryFaces_011_shape : geometryFacesTyped011.vertices.size = 17 ∧ geometryFacesTyped011.vertices.toList.Nodup ∧
    (∀ i : Fin 17, geometryFacesTyped011.vertices[i.val]! < 33) ∧
    geometryFacesTyped011.pivot < 33 ∧ geometryFacesTyped011.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson012 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped012 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 21, 22, 23, 24, 25, 26, 27, 28],
    dimension := 6, pivot := 28,
    facetSets := #[#[0, 1, 2, 3, 4, 7, 8, 10, 11, 12, 13, 14, 15, 16], #[0, 1, 2, 3, 4, 9, 21, 22, 23, 24, 25, 26, 27, 28], #[0, 1, 2, 3, 7, 8, 9, 10, 11, 12, 15, 16, 21, 23, 25, 26, 27, 28], #[0, 1, 2, 4, 8, 10, 13, 15, 21, 22, 23, 27], #[0, 1, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 21, 22, 23, 24, 25, 26], #[0, 2, 3, 4, 7, 8, 9, 11, 13, 14, 15, 16, 21, 22, 24, 25, 27, 28], #[1, 2, 3, 4, 7, 9, 10, 12, 13, 14, 15, 16, 22, 23, 24, 26, 27, 28], #[7, 9, 11, 12, 14, 16, 24, 25, 26, 28], #[8, 10, 11, 12, 13, 14, 15, 16, 21, 22, 23, 24, 25, 26, 27, 28]],
    simplices := 55 }

theorem decode_geometry_Faces_012 : decodeFace geometryFacesJson012 = .ok geometryFacesTyped012 := by decide +kernel

theorem geometryFaces_012_shape : geometryFacesTyped012.vertices.size = 23 ∧ geometryFacesTyped012.vertices.toList.Nodup ∧
    (∀ i : Fin 23, geometryFacesTyped012.vertices[i.val]! < 33) ∧
    geometryFacesTyped012.pivot < 33 ∧ geometryFacesTyped012.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson013 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped013 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 7, 8, 10, 11, 12, 13, 14, 15, 16],
    dimension := 5, pivot := 16,
    facetSets := #[#[0, 1, 2, 3, 4], #[0, 1, 2, 3, 7, 8, 10, 11, 12, 15, 16], #[0, 1, 2, 4, 8, 10, 13, 15], #[0, 1, 3, 4, 7, 8, 10, 11, 12, 13, 14], #[0, 2, 3, 4, 7, 8, 11, 13, 14, 15, 16], #[1, 2, 3, 4, 7, 10, 12, 13, 14, 15, 16], #[7, 11, 12, 14, 16], #[8, 10, 11, 12, 13, 14, 15, 16]],
    simplices := 15 }

theorem decode_geometry_Faces_013 : decodeFace geometryFacesJson013 = .ok geometryFacesTyped013 := by decide +kernel

theorem geometryFaces_013_shape : geometryFacesTyped013.vertices.size = 14 ∧ geometryFacesTyped013.vertices.toList.Nodup ∧
    (∀ i : Fin 14, geometryFacesTyped013.vertices[i.val]! < 33) ∧
    geometryFacesTyped013.pivot < 33 ∧ geometryFacesTyped013.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson014 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped014 : FaceRecord :=
  { vertices := #[0, 1, 2, 4],
    dimension := 3, pivot := 4,
    facetSets := #[#[0, 1, 2], #[0, 1, 4], #[0, 2, 4], #[1, 2, 4]],
    simplices := 1 }

theorem decode_geometry_Faces_014 : decodeFace geometryFacesJson014 = .ok geometryFacesTyped014 := by decide +kernel

theorem geometryFaces_014_shape : geometryFacesTyped014.vertices.size = 4 ∧ geometryFacesTyped014.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped014.vertices[i.val]! < 33) ∧
    geometryFacesTyped014.pivot < 33 ∧ geometryFacesTyped014.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson015 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped015 : FaceRecord :=
  { vertices := #[0, 1, 2, 4, 6],
    dimension := 4, pivot := 6,
    facetSets := #[#[0, 1, 2, 4], #[0, 1, 2, 6], #[0, 1, 4, 6], #[0, 2, 4, 6], #[1, 2, 4, 6]],
    simplices := 1 }

theorem decode_geometry_Faces_015 : decodeFace geometryFacesJson015 = .ok geometryFacesTyped015 := by decide +kernel

theorem geometryFaces_015_shape : geometryFacesTyped015.vertices.size = 5 ∧ geometryFacesTyped015.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped015.vertices[i.val]! < 33) ∧
    geometryFacesTyped015.pivot < 33 ∧ geometryFacesTyped015.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson016 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped016 : FaceRecord :=
  { vertices := #[0, 1, 2, 4, 6, 8, 10, 13, 15, 20],
    dimension := 5, pivot := 20,
    facetSets := #[#[0, 1, 2, 4, 6], #[0, 1, 2, 4, 8, 10, 13, 15], #[0, 1, 2, 6, 8, 10, 15, 20], #[0, 1, 4, 6, 8, 10, 13, 20], #[0, 2, 4, 6, 8, 13, 15, 20], #[1, 2, 4, 6, 10, 13, 15, 20], #[8, 10, 13, 15, 20]],
    simplices := 5 }

theorem decode_geometry_Faces_016 : decodeFace geometryFacesJson016 = .ok geometryFacesTyped016 := by decide +kernel

theorem geometryFaces_016_shape : geometryFacesTyped016.vertices.size = 10 ∧ geometryFacesTyped016.vertices.toList.Nodup ∧
    (∀ i : Fin 10, geometryFacesTyped016.vertices[i.val]! < 33) ∧
    geometryFacesTyped016.pivot < 33 ∧ geometryFacesTyped016.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock001 : List SourceJson := [geometryFacesJson009, geometryFacesJson010, geometryFacesJson011, geometryFacesJson012, geometryFacesJson013, geometryFacesJson014, geometryFacesJson015, geometryFacesJson016]
noncomputable def geometryFacesTypedBlock001 : List (FaceRecord) := [geometryFacesTyped009, geometryFacesTyped010, geometryFacesTyped011, geometryFacesTyped012, geometryFacesTyped013, geometryFacesTyped014, geometryFacesTyped015, geometryFacesTyped016]

theorem geometry_Faces_block_001_push_eq (acc : List SourceJson) :
    FaceLedgerBlock001.blockPush acc = [geometryFacesJson016, geometryFacesJson015, geometryFacesJson014, geometryFacesJson013, geometryFacesJson012, geometryFacesJson011, geometryFacesJson010, geometryFacesJson009] ++ acc := by rfl

theorem geometry_Faces_block_001_reverse (acc : List SourceJson) :
    (FaceLedgerBlock001.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock001 := by
  rw [geometry_Faces_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_001 : geometryFacesJsonBlock001.mapM decodeFace = .ok geometryFacesTypedBlock001 := by
  simp only [geometryFacesJsonBlock001, geometryFacesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_009, decode_geometry_Faces_010, decode_geometry_Faces_011, decode_geometry_Faces_012, decode_geometry_Faces_013, decode_geometry_Faces_014, decode_geometry_Faces_015, decode_geometry_Faces_016]
  rfl

theorem geometry_Faces_block_001_length : geometryFacesTypedBlock001.length = 8 := by rfl

#print axioms decode_geometry_Faces_009
#print axioms geometryFaces_009_shape
#print axioms decode_geometry_Faces_010
#print axioms geometryFaces_010_shape
#print axioms decode_geometry_Faces_011
#print axioms geometryFaces_011_shape
#print axioms decode_geometry_Faces_012
#print axioms geometryFaces_012_shape
#print axioms decode_geometry_Faces_013
#print axioms geometryFaces_013_shape
#print axioms decode_geometry_Faces_014
#print axioms geometryFaces_014_shape
#print axioms decode_geometry_Faces_015
#print axioms geometryFaces_015_shape
#print axioms decode_geometry_Faces_016
#print axioms geometryFaces_016_shape
#print axioms geometry_Faces_block_001_push_eq
#print axioms geometry_Faces_block_001_reverse
#print axioms decode_geometry_Faces_block_001
#print axioms geometry_Faces_block_001_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
