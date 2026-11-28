import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerBlock002

/-! Local original face_ledger decoding, indices 17 through 24.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson017 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped017 : FaceRecord :=
  { vertices := #[0, 1, 2, 4, 6, 8, 10, 13, 15, 20, 21, 22, 23, 27, 29],
    dimension := 6, pivot := 29,
    facetSets := #[#[0, 1, 2, 4, 6, 8, 10, 13, 15, 20], #[0, 1, 2, 4, 6, 21, 22, 23, 27, 29], #[0, 1, 2, 4, 8, 10, 13, 15, 21, 22, 23, 27], #[0, 1, 2, 6, 8, 10, 15, 20, 21, 23, 27, 29], #[0, 1, 4, 6, 8, 10, 13, 20, 21, 22, 23, 29], #[0, 2, 4, 6, 8, 13, 15, 20, 21, 22, 27, 29], #[1, 2, 4, 6, 10, 13, 15, 20, 22, 23, 27, 29], #[8, 10, 13, 15, 20, 21, 22, 23, 27, 29]],
    simplices := 15 }

theorem decode_geometry_Faces_017 : decodeFace geometryFacesJson017 = .ok geometryFacesTyped017 := by decide +kernel

theorem geometryFaces_017_shape : geometryFacesTyped017.vertices.size = 15 ∧ geometryFacesTyped017.vertices.toList.Nodup ∧
    (∀ i : Fin 15, geometryFacesTyped017.vertices[i.val]! < 33) ∧
    geometryFacesTyped017.pivot < 33 ∧ geometryFacesTyped017.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson018 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped018 : FaceRecord :=
  { vertices := #[0, 1, 2, 4, 8, 10, 13, 15],
    dimension := 4, pivot := 15,
    facetSets := #[#[0, 1, 2, 4], #[0, 1, 2, 8, 10, 15], #[0, 1, 4, 8, 10, 13], #[0, 2, 4, 8, 13, 15], #[1, 2, 4, 10, 13, 15], #[8, 10, 13, 15]],
    simplices := 4 }

theorem decode_geometry_Faces_018 : decodeFace geometryFacesJson018 = .ok geometryFacesTyped018 := by decide +kernel

theorem geometryFaces_018_shape : geometryFacesTyped018.vertices.size = 8 ∧ geometryFacesTyped018.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped018.vertices[i.val]! < 33) ∧
    geometryFacesTyped018.pivot < 33 ∧ geometryFacesTyped018.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson019 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped019 : FaceRecord :=
  { vertices := #[0, 1, 2, 4, 8, 10, 13, 15, 21, 22, 23, 27],
    dimension := 5, pivot := 27,
    facetSets := #[#[0, 1, 2, 4, 8, 10, 13, 15], #[0, 1, 2, 4, 21, 22, 23, 27], #[0, 1, 2, 8, 10, 15, 21, 23, 27], #[0, 1, 4, 8, 10, 13, 21, 22, 23], #[0, 2, 4, 8, 13, 15, 21, 22, 27], #[1, 2, 4, 10, 13, 15, 22, 23, 27], #[8, 10, 13, 15, 21, 22, 23, 27]],
    simplices := 10 }

theorem decode_geometry_Faces_019 : decodeFace geometryFacesJson019 = .ok geometryFacesTyped019 := by decide +kernel

theorem geometryFaces_019_shape : geometryFacesTyped019.vertices.size = 12 ∧ geometryFacesTyped019.vertices.toList.Nodup ∧
    (∀ i : Fin 12, geometryFacesTyped019.vertices[i.val]! < 33) ∧
    geometryFacesTyped019.pivot < 33 ∧ geometryFacesTyped019.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson020 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped020 : FaceRecord :=
  { vertices := #[0, 1, 3],
    dimension := 2, pivot := 3,
    facetSets := #[#[0, 1], #[0, 3], #[1, 3]],
    simplices := 1 }

theorem decode_geometry_Faces_020 : decodeFace geometryFacesJson020 = .ok geometryFacesTyped020 := by decide +kernel

theorem geometryFaces_020_shape : geometryFacesTyped020.vertices.size = 3 ∧ geometryFacesTyped020.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped020.vertices[i.val]! < 33) ∧
    geometryFacesTyped020.pivot < 33 ∧ geometryFacesTyped020.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson021 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped021 : FaceRecord :=
  { vertices := #[0, 1, 3, 4],
    dimension := 3, pivot := 4,
    facetSets := #[#[0, 1, 3], #[0, 1, 4], #[0, 3, 4], #[1, 3, 4]],
    simplices := 1 }

theorem decode_geometry_Faces_021 : decodeFace geometryFacesJson021 = .ok geometryFacesTyped021 := by decide +kernel

theorem geometryFaces_021_shape : geometryFacesTyped021.vertices.size = 4 ∧ geometryFacesTyped021.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped021.vertices[i.val]! < 33) ∧
    geometryFacesTyped021.pivot < 33 ∧ geometryFacesTyped021.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson022 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped022 : FaceRecord :=
  { vertices := #[0, 1, 3, 4, 7, 8, 9, 10, 11, 12, 13, 14, 21, 22, 23, 24, 25, 26],
    dimension := 5, pivot := 26,
    facetSets := #[#[0, 1, 3, 4, 7, 8, 10, 11, 12, 13, 14], #[0, 1, 3, 4, 9, 21, 22, 23, 24, 25, 26], #[0, 1, 3, 7, 8, 9, 10, 11, 12, 21, 23, 25, 26], #[0, 1, 4, 8, 10, 13, 21, 22, 23], #[0, 3, 4, 7, 8, 9, 11, 13, 14, 21, 22, 24, 25], #[1, 3, 4, 7, 9, 10, 12, 13, 14, 22, 23, 24, 26], #[7, 9, 11, 12, 14, 24, 25, 26], #[8, 10, 11, 12, 13, 14, 21, 22, 23, 24, 25, 26]],
    simplices := 30 }

theorem decode_geometry_Faces_022 : decodeFace geometryFacesJson022 = .ok geometryFacesTyped022 := by decide +kernel

theorem geometryFaces_022_shape : geometryFacesTyped022.vertices.size = 18 ∧ geometryFacesTyped022.vertices.toList.Nodup ∧
    (∀ i : Fin 18, geometryFacesTyped022.vertices[i.val]! < 33) ∧
    geometryFacesTyped022.pivot < 33 ∧ geometryFacesTyped022.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson023 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped023 : FaceRecord :=
  { vertices := #[0, 1, 3, 4, 7, 8, 10, 11, 12, 13, 14],
    dimension := 4, pivot := 14,
    facetSets := #[#[0, 1, 3, 4], #[0, 1, 3, 7, 8, 10, 11, 12], #[0, 1, 4, 8, 10, 13], #[0, 3, 4, 7, 8, 11, 13, 14], #[1, 3, 4, 7, 10, 12, 13, 14], #[7, 11, 12, 14], #[8, 10, 11, 12, 13, 14]],
    simplices := 10 }

theorem decode_geometry_Faces_023 : decodeFace geometryFacesJson023 = .ok geometryFacesTyped023 := by decide +kernel

theorem geometryFaces_023_shape : geometryFacesTyped023.vertices.size = 11 ∧ geometryFacesTyped023.vertices.toList.Nodup ∧
    (∀ i : Fin 11, geometryFacesTyped023.vertices[i.val]! < 33) ∧
    geometryFacesTyped023.pivot < 33 ∧ geometryFacesTyped023.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson024 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped024 : FaceRecord :=
  { vertices := #[0, 1, 3, 7, 8, 10, 11, 12],
    dimension := 3, pivot := 12,
    facetSets := #[#[0, 1, 3], #[0, 1, 8, 10], #[0, 3, 7, 8, 11], #[1, 3, 7, 10, 12], #[7, 11, 12], #[8, 10, 11, 12]],
    simplices := 6 }

theorem decode_geometry_Faces_024 : decodeFace geometryFacesJson024 = .ok geometryFacesTyped024 := by decide +kernel

theorem geometryFaces_024_shape : geometryFacesTyped024.vertices.size = 8 ∧ geometryFacesTyped024.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped024.vertices[i.val]! < 33) ∧
    geometryFacesTyped024.pivot < 33 ∧ geometryFacesTyped024.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock002 : List SourceJson := [geometryFacesJson017, geometryFacesJson018, geometryFacesJson019, geometryFacesJson020, geometryFacesJson021, geometryFacesJson022, geometryFacesJson023, geometryFacesJson024]
noncomputable def geometryFacesTypedBlock002 : List (FaceRecord) := [geometryFacesTyped017, geometryFacesTyped018, geometryFacesTyped019, geometryFacesTyped020, geometryFacesTyped021, geometryFacesTyped022, geometryFacesTyped023, geometryFacesTyped024]

theorem geometry_Faces_block_002_push_eq (acc : List SourceJson) :
    FaceLedgerBlock002.blockPush acc = [geometryFacesJson024, geometryFacesJson023, geometryFacesJson022, geometryFacesJson021, geometryFacesJson020, geometryFacesJson019, geometryFacesJson018, geometryFacesJson017] ++ acc := by rfl

theorem geometry_Faces_block_002_reverse (acc : List SourceJson) :
    (FaceLedgerBlock002.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock002 := by
  rw [geometry_Faces_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_002 : geometryFacesJsonBlock002.mapM decodeFace = .ok geometryFacesTypedBlock002 := by
  simp only [geometryFacesJsonBlock002, geometryFacesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_017, decode_geometry_Faces_018, decode_geometry_Faces_019, decode_geometry_Faces_020, decode_geometry_Faces_021, decode_geometry_Faces_022, decode_geometry_Faces_023, decode_geometry_Faces_024]
  rfl

theorem geometry_Faces_block_002_length : geometryFacesTypedBlock002.length = 8 := by rfl

#print axioms decode_geometry_Faces_017
#print axioms geometryFaces_017_shape
#print axioms decode_geometry_Faces_018
#print axioms geometryFaces_018_shape
#print axioms decode_geometry_Faces_019
#print axioms geometryFaces_019_shape
#print axioms decode_geometry_Faces_020
#print axioms geometryFaces_020_shape
#print axioms decode_geometry_Faces_021
#print axioms geometryFaces_021_shape
#print axioms decode_geometry_Faces_022
#print axioms geometryFaces_022_shape
#print axioms decode_geometry_Faces_023
#print axioms geometryFaces_023_shape
#print axioms decode_geometry_Faces_024
#print axioms geometryFaces_024_shape
#print axioms geometry_Faces_block_002_push_eq
#print axioms geometry_Faces_block_002_reverse
#print axioms decode_geometry_Faces_block_002
#print axioms geometry_Faces_block_002_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
