import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerBlock001

/-! Local original face_ledger decoding, indices 9 through 17.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson009 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped009 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11],
    dimension := 5, pivot := 11,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 10, 11], #[0, 1, 2, 3, 6, 7, 10, 11], #[0, 1, 4, 5, 6, 7, 10, 11], #[0, 2, 4, 6, 11], #[1, 3, 5, 7, 10], #[2, 3, 4, 5, 6, 7, 10, 11]],
    simplices := 5 }

theorem decode_geometry_Faces_009 : decodeFace geometryFacesJson009 = .ok geometryFacesTyped009 := by decide +kernel

theorem geometryFaces_009_shape : geometryFacesTyped009.vertices.size = 10 ∧ geometryFacesTyped009.vertices.toList.Nodup ∧
    (∀ i : Fin 10, geometryFacesTyped009.vertices[i.val]! < 28) ∧
    geometryFacesTyped009.pivot < 28 ∧ geometryFacesTyped009.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson010 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped010 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 10, 11, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
    dimension := 6, pivot := 23,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7, 10, 11], #[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 16, 17, 18, 19, 20, 21], #[0, 1, 2, 3, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 22, 23], #[0, 1, 2, 3, 6, 7, 10, 11, 16, 17, 18, 19, 20, 21, 22, 23], #[0, 1, 4, 5, 6, 7, 10, 11, 14, 15, 16, 17, 18, 19, 22, 23], #[0, 2, 4, 6, 11, 14, 16, 18, 20, 22], #[1, 3, 5, 7, 10, 15, 17, 19, 21, 23], #[2, 3, 4, 5, 6, 7, 10, 11, 14, 15, 18, 19, 20, 21, 22, 23], #[14, 15, 16, 17, 18, 19, 20, 21, 22, 23]],
    simplices := 30 }

theorem decode_geometry_Faces_010 : decodeFace geometryFacesJson010 = .ok geometryFacesTyped010 := by decide +kernel

theorem geometryFaces_010_shape : geometryFacesTyped010.vertices.size = 20 ∧ geometryFacesTyped010.vertices.toList.Nodup ∧
    (∀ i : Fin 20, geometryFacesTyped010.vertices[i.val]! < 28) ∧
    geometryFacesTyped010.pivot < 28 ∧ geometryFacesTyped010.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson011 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped011 : FaceRecord :=
  { vertices := #[0, 1, 2, 3, 4, 5, 6, 7, 14, 15, 16, 17, 18, 19, 20, 21],
    dimension := 5, pivot := 21,
    facetSets := #[#[0, 1, 2, 3, 4, 5, 6, 7], #[0, 1, 2, 3, 4, 5, 14, 15, 16, 17, 20, 21], #[0, 1, 2, 3, 6, 7, 16, 17, 18, 19, 20, 21], #[0, 1, 4, 5, 6, 7, 14, 15, 16, 17, 18, 19], #[0, 2, 4, 6, 14, 16, 18, 20], #[1, 3, 5, 7, 15, 17, 19, 21], #[2, 3, 4, 5, 6, 7, 14, 15, 18, 19, 20, 21], #[14, 15, 16, 17, 18, 19, 20, 21]],
    simplices := 20 }

theorem decode_geometry_Faces_011 : decodeFace geometryFacesJson011 = .ok geometryFacesTyped011 := by decide +kernel

theorem geometryFaces_011_shape : geometryFacesTyped011.vertices.size = 16 ∧ geometryFacesTyped011.vertices.toList.Nodup ∧
    (∀ i : Fin 16, geometryFacesTyped011.vertices[i.val]! < 28) ∧
    geometryFacesTyped011.pivot < 28 ∧ geometryFacesTyped011.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson012 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped012 : FaceRecord :=
  { vertices := #[0, 1, 4, 5],
    dimension := 2, pivot := 5,
    facetSets := #[#[0, 1], #[0, 4], #[1, 5], #[4, 5]],
    simplices := 2 }

theorem decode_geometry_Faces_012 : decodeFace geometryFacesJson012 = .ok geometryFacesTyped012 := by decide +kernel

theorem geometryFaces_012_shape : geometryFacesTyped012.vertices.size = 4 ∧ geometryFacesTyped012.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped012.vertices[i.val]! < 28) ∧
    geometryFacesTyped012.pivot < 28 ∧ geometryFacesTyped012.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson013 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped013 : FaceRecord :=
  { vertices := #[0, 1, 4, 5, 6, 7],
    dimension := 3, pivot := 7,
    facetSets := #[#[0, 1, 4, 5], #[0, 1, 6, 7], #[0, 4, 6], #[1, 5, 7], #[4, 5, 6, 7]],
    simplices := 3 }

theorem decode_geometry_Faces_013 : decodeFace geometryFacesJson013 = .ok geometryFacesTyped013 := by decide +kernel

theorem geometryFaces_013_shape : geometryFacesTyped013.vertices.size = 6 ∧ geometryFacesTyped013.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped013.vertices[i.val]! < 28) ∧
    geometryFacesTyped013.pivot < 28 ∧ geometryFacesTyped013.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson014 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped014 : FaceRecord :=
  { vertices := #[0, 1, 4, 5, 6, 7, 14, 15, 16, 17, 18, 19],
    dimension := 4, pivot := 19,
    facetSets := #[#[0, 1, 4, 5, 6, 7], #[0, 1, 4, 5, 14, 15, 16, 17], #[0, 1, 6, 7, 16, 17, 18, 19], #[0, 4, 6, 14, 16, 18], #[1, 5, 7, 15, 17, 19], #[4, 5, 6, 7, 14, 15, 18, 19], #[14, 15, 16, 17, 18, 19]],
    simplices := 12 }

theorem decode_geometry_Faces_014 : decodeFace geometryFacesJson014 = .ok geometryFacesTyped014 := by decide +kernel

theorem geometryFaces_014_shape : geometryFacesTyped014.vertices.size = 12 ∧ geometryFacesTyped014.vertices.toList.Nodup ∧
    (∀ i : Fin 12, geometryFacesTyped014.vertices[i.val]! < 28) ∧
    geometryFacesTyped014.pivot < 28 ∧ geometryFacesTyped014.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson015 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped015 : FaceRecord :=
  { vertices := #[0, 1, 4, 5, 14, 15, 16, 17],
    dimension := 3, pivot := 17,
    facetSets := #[#[0, 1, 4, 5], #[0, 1, 16, 17], #[0, 4, 14, 16], #[1, 5, 15, 17], #[4, 5, 14, 15], #[14, 15, 16, 17]],
    simplices := 6 }

theorem decode_geometry_Faces_015 : decodeFace geometryFacesJson015 = .ok geometryFacesTyped015 := by decide +kernel

theorem geometryFaces_015_shape : geometryFacesTyped015.vertices.size = 8 ∧ geometryFacesTyped015.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped015.vertices[i.val]! < 28) ∧
    geometryFacesTyped015.pivot < 28 ∧ geometryFacesTyped015.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson016 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped016 : FaceRecord :=
  { vertices := #[0, 2],
    dimension := 1, pivot := 2,
    facetSets := #[#[0], #[2]],
    simplices := 1 }

theorem decode_geometry_Faces_016 : decodeFace geometryFacesJson016 = .ok geometryFacesTyped016 := by decide +kernel

theorem geometryFaces_016_shape : geometryFacesTyped016.vertices.size = 2 ∧ geometryFacesTyped016.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped016.vertices[i.val]! < 28) ∧
    geometryFacesTyped016.pivot < 28 ∧ geometryFacesTyped016.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson017 : SourceJson :=
  (FaceLedgerBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped017 : FaceRecord :=
  { vertices := #[0, 2, 4],
    dimension := 2, pivot := 4,
    facetSets := #[#[0, 2], #[0, 4], #[2, 4]],
    simplices := 1 }

theorem decode_geometry_Faces_017 : decodeFace geometryFacesJson017 = .ok geometryFacesTyped017 := by decide +kernel

theorem geometryFaces_017_shape : geometryFacesTyped017.vertices.size = 3 ∧ geometryFacesTyped017.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped017.vertices[i.val]! < 28) ∧
    geometryFacesTyped017.pivot < 28 ∧ geometryFacesTyped017.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock001 : List SourceJson := [geometryFacesJson009, geometryFacesJson010, geometryFacesJson011, geometryFacesJson012, geometryFacesJson013, geometryFacesJson014, geometryFacesJson015, geometryFacesJson016, geometryFacesJson017]
noncomputable def geometryFacesTypedBlock001 : List (FaceRecord) := [geometryFacesTyped009, geometryFacesTyped010, geometryFacesTyped011, geometryFacesTyped012, geometryFacesTyped013, geometryFacesTyped014, geometryFacesTyped015, geometryFacesTyped016, geometryFacesTyped017]

theorem geometry_Faces_block_001_push_eq (acc : List SourceJson) :
    FaceLedgerBlock001.blockPush acc = [geometryFacesJson017, geometryFacesJson016, geometryFacesJson015, geometryFacesJson014, geometryFacesJson013, geometryFacesJson012, geometryFacesJson011, geometryFacesJson010, geometryFacesJson009] ++ acc := by rfl

theorem geometry_Faces_block_001_reverse (acc : List SourceJson) :
    (FaceLedgerBlock001.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock001 := by
  rw [geometry_Faces_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_001 : geometryFacesJsonBlock001.mapM decodeFace = .ok geometryFacesTypedBlock001 := by
  simp only [geometryFacesJsonBlock001, geometryFacesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_009, decode_geometry_Faces_010, decode_geometry_Faces_011, decode_geometry_Faces_012, decode_geometry_Faces_013, decode_geometry_Faces_014, decode_geometry_Faces_015, decode_geometry_Faces_016, decode_geometry_Faces_017]
  rfl

theorem geometry_Faces_block_001_length : geometryFacesTypedBlock001.length = 9 := by rfl

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
#print axioms decode_geometry_Faces_017
#print axioms geometryFaces_017_shape
#print axioms geometry_Faces_block_001_push_eq
#print axioms geometry_Faces_block_001_reverse
#print axioms decode_geometry_Faces_block_001
#print axioms geometry_Faces_block_001_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
