import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerBlock003

/-! Local original face_ledger decoding, indices 25 through 34.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson025 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryFacesTyped025 : FaceRecord :=
  { vertices := #[0, 1, 4],
    dimension := 2, pivot := 4,
    facetSets := #[#[0, 1], #[0, 4], #[1, 4]],
    simplices := 1 }

theorem decode_geometry_Faces_025 : decodeFace geometryFacesJson025 = .ok geometryFacesTyped025 := by decide +kernel

theorem geometryFaces_025_shape : geometryFacesTyped025.vertices.size = 3 ∧ geometryFacesTyped025.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped025.vertices[i.val]! < 33) ∧
    geometryFacesTyped025.pivot < 33 ∧ geometryFacesTyped025.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson026 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped026 : FaceRecord :=
  { vertices := #[0, 1, 4, 8, 10, 13],
    dimension := 3, pivot := 13,
    facetSets := #[#[0, 1, 4], #[0, 1, 8, 10], #[0, 4, 8, 13], #[1, 4, 10, 13], #[8, 10, 13]],
    simplices := 3 }

theorem decode_geometry_Faces_026 : decodeFace geometryFacesJson026 = .ok geometryFacesTyped026 := by decide +kernel

theorem geometryFaces_026_shape : geometryFacesTyped026.vertices.size = 6 ∧ geometryFacesTyped026.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped026.vertices[i.val]! < 33) ∧
    geometryFacesTyped026.pivot < 33 ∧ geometryFacesTyped026.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson027 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped027 : FaceRecord :=
  { vertices := #[0, 1, 4, 8, 10, 13, 21, 22, 23],
    dimension := 4, pivot := 23,
    facetSets := #[#[0, 1, 4, 8, 10, 13], #[0, 1, 4, 21, 22, 23], #[0, 1, 8, 10, 21, 23], #[0, 4, 8, 13, 21, 22], #[1, 4, 10, 13, 22, 23], #[8, 10, 13, 21, 22, 23]],
    simplices := 6 }

theorem decode_geometry_Faces_027 : decodeFace geometryFacesJson027 = .ok geometryFacesTyped027 := by decide +kernel

theorem geometryFaces_027_shape : geometryFacesTyped027.vertices.size = 9 ∧ geometryFacesTyped027.vertices.toList.Nodup ∧
    (∀ i : Fin 9, geometryFacesTyped027.vertices[i.val]! < 33) ∧
    geometryFacesTyped027.pivot < 33 ∧ geometryFacesTyped027.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson028 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped028 : FaceRecord :=
  { vertices := #[0, 1, 8, 10],
    dimension := 2, pivot := 10,
    facetSets := #[#[0, 1], #[0, 8], #[1, 10], #[8, 10]],
    simplices := 2 }

theorem decode_geometry_Faces_028 : decodeFace geometryFacesJson028 = .ok geometryFacesTyped028 := by decide +kernel

theorem geometryFaces_028_shape : geometryFacesTyped028.vertices.size = 4 ∧ geometryFacesTyped028.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped028.vertices[i.val]! < 33) ∧
    geometryFacesTyped028.pivot < 33 ∧ geometryFacesTyped028.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson029 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped029 : FaceRecord :=
  { vertices := #[0, 3],
    dimension := 1, pivot := 3,
    facetSets := #[#[0], #[3]],
    simplices := 1 }

theorem decode_geometry_Faces_029 : decodeFace geometryFacesJson029 = .ok geometryFacesTyped029 := by decide +kernel

theorem geometryFaces_029_shape : geometryFacesTyped029.vertices.size = 2 ∧ geometryFacesTyped029.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped029.vertices[i.val]! < 33) ∧
    geometryFacesTyped029.pivot < 33 ∧ geometryFacesTyped029.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson030 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped030 : FaceRecord :=
  { vertices := #[0, 3, 4],
    dimension := 2, pivot := 4,
    facetSets := #[#[0, 3], #[0, 4], #[3, 4]],
    simplices := 1 }

theorem decode_geometry_Faces_030 : decodeFace geometryFacesJson030 = .ok geometryFacesTyped030 := by decide +kernel

theorem geometryFaces_030_shape : geometryFacesTyped030.vertices.size = 3 ∧ geometryFacesTyped030.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped030.vertices[i.val]! < 33) ∧
    geometryFacesTyped030.pivot < 33 ∧ geometryFacesTyped030.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson031 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped031 : FaceRecord :=
  { vertices := #[0, 3, 4, 7, 8, 9, 11, 13, 14, 21, 22, 24, 25],
    dimension := 4, pivot := 25,
    facetSets := #[#[0, 3, 4, 7, 8, 11, 13, 14], #[0, 3, 4, 9, 21, 22, 24, 25], #[0, 3, 7, 8, 9, 11, 21, 25], #[0, 4, 8, 13, 21, 22], #[3, 4, 7, 9, 13, 14, 22, 24], #[7, 9, 11, 14, 24, 25], #[8, 11, 13, 14, 21, 22, 24, 25]],
    simplices := 14 }

theorem decode_geometry_Faces_031 : decodeFace geometryFacesJson031 = .ok geometryFacesTyped031 := by decide +kernel

theorem geometryFaces_031_shape : geometryFacesTyped031.vertices.size = 13 ∧ geometryFacesTyped031.vertices.toList.Nodup ∧
    (∀ i : Fin 13, geometryFacesTyped031.vertices[i.val]! < 33) ∧
    geometryFacesTyped031.pivot < 33 ∧ geometryFacesTyped031.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson032 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped032 : FaceRecord :=
  { vertices := #[0, 3, 4, 7, 8, 11, 13, 14],
    dimension := 3, pivot := 14,
    facetSets := #[#[0, 3, 4], #[0, 3, 7, 8, 11], #[0, 4, 8, 13], #[3, 4, 7, 13, 14], #[7, 11, 14], #[8, 11, 13, 14]],
    simplices := 6 }

theorem decode_geometry_Faces_032 : decodeFace geometryFacesJson032 = .ok geometryFacesTyped032 := by decide +kernel

theorem geometryFaces_032_shape : geometryFacesTyped032.vertices.size = 8 ∧ geometryFacesTyped032.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped032.vertices[i.val]! < 33) ∧
    geometryFacesTyped032.pivot < 33 ∧ geometryFacesTyped032.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson033 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped033 : FaceRecord :=
  { vertices := #[0, 3, 7, 8, 11],
    dimension := 2, pivot := 11,
    facetSets := #[#[0, 3], #[0, 8], #[3, 7], #[7, 11], #[8, 11]],
    simplices := 3 }

theorem decode_geometry_Faces_033 : decodeFace geometryFacesJson033 = .ok geometryFacesTyped033 := by decide +kernel

theorem geometryFaces_033_shape : geometryFacesTyped033.vertices.size = 5 ∧ geometryFacesTyped033.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped033.vertices[i.val]! < 33) ∧
    geometryFacesTyped033.pivot < 33 ∧ geometryFacesTyped033.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson034 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped034 : FaceRecord :=
  { vertices := #[0, 4],
    dimension := 1, pivot := 4,
    facetSets := #[#[0], #[4]],
    simplices := 1 }

theorem decode_geometry_Faces_034 : decodeFace geometryFacesJson034 = .ok geometryFacesTyped034 := by decide +kernel

theorem geometryFaces_034_shape : geometryFacesTyped034.vertices.size = 2 ∧ geometryFacesTyped034.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped034.vertices[i.val]! < 33) ∧
    geometryFacesTyped034.pivot < 33 ∧ geometryFacesTyped034.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock003 : List SourceJson := [geometryFacesJson025, geometryFacesJson026, geometryFacesJson027, geometryFacesJson028, geometryFacesJson029, geometryFacesJson030, geometryFacesJson031, geometryFacesJson032, geometryFacesJson033, geometryFacesJson034]
noncomputable def geometryFacesTypedBlock003 : List (FaceRecord) := [geometryFacesTyped025, geometryFacesTyped026, geometryFacesTyped027, geometryFacesTyped028, geometryFacesTyped029, geometryFacesTyped030, geometryFacesTyped031, geometryFacesTyped032, geometryFacesTyped033, geometryFacesTyped034]

theorem geometry_Faces_block_003_push_eq (acc : List SourceJson) :
    FaceLedgerBlock003.blockPush acc = [geometryFacesJson034, geometryFacesJson033, geometryFacesJson032, geometryFacesJson031, geometryFacesJson030, geometryFacesJson029, geometryFacesJson028, geometryFacesJson027, geometryFacesJson026, geometryFacesJson025] ++ acc := by rfl

theorem geometry_Faces_block_003_reverse (acc : List SourceJson) :
    (FaceLedgerBlock003.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock003 := by
  rw [geometry_Faces_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_003 : geometryFacesJsonBlock003.mapM decodeFace = .ok geometryFacesTypedBlock003 := by
  simp only [geometryFacesJsonBlock003, geometryFacesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_025, decode_geometry_Faces_026, decode_geometry_Faces_027, decode_geometry_Faces_028, decode_geometry_Faces_029, decode_geometry_Faces_030, decode_geometry_Faces_031, decode_geometry_Faces_032, decode_geometry_Faces_033, decode_geometry_Faces_034]
  rfl

theorem geometry_Faces_block_003_length : geometryFacesTypedBlock003.length = 10 := by rfl

#print axioms decode_geometry_Faces_025
#print axioms geometryFaces_025_shape
#print axioms decode_geometry_Faces_026
#print axioms geometryFaces_026_shape
#print axioms decode_geometry_Faces_027
#print axioms geometryFaces_027_shape
#print axioms decode_geometry_Faces_028
#print axioms geometryFaces_028_shape
#print axioms decode_geometry_Faces_029
#print axioms geometryFaces_029_shape
#print axioms decode_geometry_Faces_030
#print axioms geometryFaces_030_shape
#print axioms decode_geometry_Faces_031
#print axioms geometryFaces_031_shape
#print axioms decode_geometry_Faces_032
#print axioms geometryFaces_032_shape
#print axioms decode_geometry_Faces_033
#print axioms geometryFaces_033_shape
#print axioms decode_geometry_Faces_034
#print axioms geometryFaces_034_shape
#print axioms geometry_Faces_block_003_push_eq
#print axioms geometry_Faces_block_003_reverse
#print axioms decode_geometry_Faces_block_003
#print axioms geometry_Faces_block_003_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
