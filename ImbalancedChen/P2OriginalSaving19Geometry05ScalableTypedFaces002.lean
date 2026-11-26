import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerBlock002

/-! Local original face_ledger decoding, indices 18 through 27.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson018 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryFacesTyped018 : FaceRecord :=
  { vertices := #[0, 2, 4, 6],
    dimension := 3, pivot := 6,
    facetSets := #[#[0, 2, 4], #[0, 2, 6], #[0, 4, 6], #[2, 4, 6]],
    simplices := 1 }

theorem decode_geometry_Faces_018 : decodeFace geometryFacesJson018 = .ok geometryFacesTyped018 := by decide +kernel

theorem geometryFaces_018_shape : geometryFacesTyped018.vertices.size = 4 ∧ geometryFacesTyped018.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped018.vertices[i.val]! < 28) ∧
    geometryFacesTyped018.pivot < 28 ∧ geometryFacesTyped018.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson019 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped019 : FaceRecord :=
  { vertices := #[0, 2, 4, 6, 11],
    dimension := 4, pivot := 11,
    facetSets := #[#[0, 2, 4, 6], #[0, 2, 4, 11], #[0, 2, 6, 11], #[0, 4, 6, 11], #[2, 4, 6, 11]],
    simplices := 1 }

theorem decode_geometry_Faces_019 : decodeFace geometryFacesJson019 = .ok geometryFacesTyped019 := by decide +kernel

theorem geometryFaces_019_shape : geometryFacesTyped019.vertices.size = 5 ∧ geometryFacesTyped019.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped019.vertices[i.val]! < 28) ∧
    geometryFacesTyped019.pivot < 28 ∧ geometryFacesTyped019.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson020 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped020 : FaceRecord :=
  { vertices := #[0, 2, 4, 6, 11, 14, 16, 18, 20, 22],
    dimension := 5, pivot := 22,
    facetSets := #[#[0, 2, 4, 6, 11], #[0, 2, 4, 6, 14, 16, 18, 20], #[0, 2, 4, 11, 14, 16, 20, 22], #[0, 2, 6, 11, 16, 18, 20, 22], #[0, 4, 6, 11, 14, 16, 18, 22], #[2, 4, 6, 11, 14, 18, 20, 22], #[14, 16, 18, 20, 22]],
    simplices := 5 }

theorem decode_geometry_Faces_020 : decodeFace geometryFacesJson020 = .ok geometryFacesTyped020 := by decide +kernel

theorem geometryFaces_020_shape : geometryFacesTyped020.vertices.size = 10 ∧ geometryFacesTyped020.vertices.toList.Nodup ∧
    (∀ i : Fin 10, geometryFacesTyped020.vertices[i.val]! < 28) ∧
    geometryFacesTyped020.pivot < 28 ∧ geometryFacesTyped020.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson021 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped021 : FaceRecord :=
  { vertices := #[0, 2, 4, 6, 14, 16, 18, 20],
    dimension := 4, pivot := 20,
    facetSets := #[#[0, 2, 4, 6], #[0, 2, 4, 14, 16, 20], #[0, 2, 6, 16, 18, 20], #[0, 4, 6, 14, 16, 18], #[2, 4, 6, 14, 18, 20], #[14, 16, 18, 20]],
    simplices := 4 }

theorem decode_geometry_Faces_021 : decodeFace geometryFacesJson021 = .ok geometryFacesTyped021 := by decide +kernel

theorem geometryFaces_021_shape : geometryFacesTyped021.vertices.size = 8 ∧ geometryFacesTyped021.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped021.vertices[i.val]! < 28) ∧
    geometryFacesTyped021.pivot < 28 ∧ geometryFacesTyped021.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson022 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped022 : FaceRecord :=
  { vertices := #[0, 4],
    dimension := 1, pivot := 4,
    facetSets := #[#[0], #[4]],
    simplices := 1 }

theorem decode_geometry_Faces_022 : decodeFace geometryFacesJson022 = .ok geometryFacesTyped022 := by decide +kernel

theorem geometryFaces_022_shape : geometryFacesTyped022.vertices.size = 2 ∧ geometryFacesTyped022.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped022.vertices[i.val]! < 28) ∧
    geometryFacesTyped022.pivot < 28 ∧ geometryFacesTyped022.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson023 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped023 : FaceRecord :=
  { vertices := #[0, 4, 6],
    dimension := 2, pivot := 6,
    facetSets := #[#[0, 4], #[0, 6], #[4, 6]],
    simplices := 1 }

theorem decode_geometry_Faces_023 : decodeFace geometryFacesJson023 = .ok geometryFacesTyped023 := by decide +kernel

theorem geometryFaces_023_shape : geometryFacesTyped023.vertices.size = 3 ∧ geometryFacesTyped023.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped023.vertices[i.val]! < 28) ∧
    geometryFacesTyped023.pivot < 28 ∧ geometryFacesTyped023.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson024 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped024 : FaceRecord :=
  { vertices := #[0, 4, 6, 14, 16, 18],
    dimension := 3, pivot := 18,
    facetSets := #[#[0, 4, 6], #[0, 4, 14, 16], #[0, 6, 16, 18], #[4, 6, 14, 18], #[14, 16, 18]],
    simplices := 3 }

theorem decode_geometry_Faces_024 : decodeFace geometryFacesJson024 = .ok geometryFacesTyped024 := by decide +kernel

theorem geometryFaces_024_shape : geometryFacesTyped024.vertices.size = 6 ∧ geometryFacesTyped024.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped024.vertices[i.val]! < 28) ∧
    geometryFacesTyped024.pivot < 28 ∧ geometryFacesTyped024.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson025 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped025 : FaceRecord :=
  { vertices := #[0, 4, 14, 16],
    dimension := 2, pivot := 16,
    facetSets := #[#[0, 4], #[0, 16], #[4, 14], #[14, 16]],
    simplices := 2 }

theorem decode_geometry_Faces_025 : decodeFace geometryFacesJson025 = .ok geometryFacesTyped025 := by decide +kernel

theorem geometryFaces_025_shape : geometryFacesTyped025.vertices.size = 4 ∧ geometryFacesTyped025.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped025.vertices[i.val]! < 28) ∧
    geometryFacesTyped025.pivot < 28 ∧ geometryFacesTyped025.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson026 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped026 : FaceRecord :=
  { vertices := #[1, 3],
    dimension := 1, pivot := 3,
    facetSets := #[#[1], #[3]],
    simplices := 1 }

theorem decode_geometry_Faces_026 : decodeFace geometryFacesJson026 = .ok geometryFacesTyped026 := by decide +kernel

theorem geometryFaces_026_shape : geometryFacesTyped026.vertices.size = 2 ∧ geometryFacesTyped026.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped026.vertices[i.val]! < 28) ∧
    geometryFacesTyped026.pivot < 28 ∧ geometryFacesTyped026.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson027 : SourceJson :=
  (FaceLedgerBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped027 : FaceRecord :=
  { vertices := #[1, 3, 5],
    dimension := 2, pivot := 5,
    facetSets := #[#[1, 3], #[1, 5], #[3, 5]],
    simplices := 1 }

theorem decode_geometry_Faces_027 : decodeFace geometryFacesJson027 = .ok geometryFacesTyped027 := by decide +kernel

theorem geometryFaces_027_shape : geometryFacesTyped027.vertices.size = 3 ∧ geometryFacesTyped027.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped027.vertices[i.val]! < 28) ∧
    geometryFacesTyped027.pivot < 28 ∧ geometryFacesTyped027.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock002 : List SourceJson := [geometryFacesJson018, geometryFacesJson019, geometryFacesJson020, geometryFacesJson021, geometryFacesJson022, geometryFacesJson023, geometryFacesJson024, geometryFacesJson025, geometryFacesJson026, geometryFacesJson027]
noncomputable def geometryFacesTypedBlock002 : List (FaceRecord) := [geometryFacesTyped018, geometryFacesTyped019, geometryFacesTyped020, geometryFacesTyped021, geometryFacesTyped022, geometryFacesTyped023, geometryFacesTyped024, geometryFacesTyped025, geometryFacesTyped026, geometryFacesTyped027]

theorem geometry_Faces_block_002_push_eq (acc : List SourceJson) :
    FaceLedgerBlock002.blockPush acc = [geometryFacesJson027, geometryFacesJson026, geometryFacesJson025, geometryFacesJson024, geometryFacesJson023, geometryFacesJson022, geometryFacesJson021, geometryFacesJson020, geometryFacesJson019, geometryFacesJson018] ++ acc := by rfl

theorem geometry_Faces_block_002_reverse (acc : List SourceJson) :
    (FaceLedgerBlock002.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock002 := by
  rw [geometry_Faces_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_002 : geometryFacesJsonBlock002.mapM decodeFace = .ok geometryFacesTypedBlock002 := by
  simp only [geometryFacesJsonBlock002, geometryFacesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_018, decode_geometry_Faces_019, decode_geometry_Faces_020, decode_geometry_Faces_021, decode_geometry_Faces_022, decode_geometry_Faces_023, decode_geometry_Faces_024, decode_geometry_Faces_025, decode_geometry_Faces_026, decode_geometry_Faces_027]
  rfl

theorem geometry_Faces_block_002_length : geometryFacesTypedBlock002.length = 10 := by rfl

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
#print axioms decode_geometry_Faces_025
#print axioms geometryFaces_025_shape
#print axioms decode_geometry_Faces_026
#print axioms geometryFaces_026_shape
#print axioms decode_geometry_Faces_027
#print axioms geometryFaces_027_shape
#print axioms geometry_Faces_block_002_push_eq
#print axioms geometry_Faces_block_002_reverse
#print axioms decode_geometry_Faces_block_002
#print axioms geometry_Faces_block_002_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
