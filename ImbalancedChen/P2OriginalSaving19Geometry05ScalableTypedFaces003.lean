import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableFaceLedgerBlock003

/-! Local original face_ledger decoding, indices 28 through 35.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson028 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped028 : FaceRecord :=
  { vertices := #[1, 3, 5, 7],
    dimension := 3, pivot := 7,
    facetSets := #[#[1, 3, 5], #[1, 3, 7], #[1, 5, 7], #[3, 5, 7]],
    simplices := 1 }

theorem decode_geometry_Faces_028 : decodeFace geometryFacesJson028 = .ok geometryFacesTyped028 := by decide +kernel

theorem geometryFaces_028_shape : geometryFacesTyped028.vertices.size = 4 ∧ geometryFacesTyped028.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped028.vertices[i.val]! < 28) ∧
    geometryFacesTyped028.pivot < 28 ∧ geometryFacesTyped028.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson029 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped029 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 8],
    dimension := 4, pivot := 8,
    facetSets := #[#[1, 3, 5, 7], #[1, 3, 5, 8], #[1, 3, 7, 8], #[1, 5, 7, 8], #[3, 5, 7, 8]],
    simplices := 1 }

theorem decode_geometry_Faces_029 : decodeFace geometryFacesJson029 = .ok geometryFacesTyped029 := by decide +kernel

theorem geometryFaces_029_shape : geometryFacesTyped029.vertices.size = 5 ∧ geometryFacesTyped029.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped029.vertices[i.val]! < 28) ∧
    geometryFacesTyped029.pivot < 28 ∧ geometryFacesTyped029.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson030 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped030 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 8, 10],
    dimension := 5, pivot := 10,
    facetSets := #[#[1, 3, 5, 7, 8], #[1, 3, 5, 7, 10], #[1, 3, 5, 8, 10], #[1, 3, 7, 8, 10], #[1, 5, 7, 8, 10], #[3, 5, 7, 8, 10]],
    simplices := 1 }

theorem decode_geometry_Faces_030 : decodeFace geometryFacesJson030 = .ok geometryFacesTyped030 := by decide +kernel

theorem geometryFaces_030_shape : geometryFacesTyped030.vertices.size = 6 ∧ geometryFacesTyped030.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped030.vertices[i.val]! < 28) ∧
    geometryFacesTyped030.pivot < 28 ∧ geometryFacesTyped030.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson031 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped031 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 8, 10, 12],
    dimension := 6, pivot := 12,
    facetSets := #[#[1, 3, 5, 7, 8, 10], #[1, 3, 5, 7, 8, 12], #[1, 3, 5, 7, 10, 12], #[1, 3, 5, 8, 10, 12], #[1, 3, 7, 8, 10, 12], #[1, 5, 7, 8, 10, 12], #[3, 5, 7, 8, 10, 12]],
    simplices := 1 }

theorem decode_geometry_Faces_031 : decodeFace geometryFacesJson031 = .ok geometryFacesTyped031 := by decide +kernel

theorem geometryFaces_031_shape : geometryFacesTyped031.vertices.size = 7 ∧ geometryFacesTyped031.vertices.toList.Nodup ∧
    (∀ i : Fin 7, geometryFacesTyped031.vertices[i.val]! < 28) ∧
    geometryFacesTyped031.pivot < 28 ∧ geometryFacesTyped031.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson032 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped032 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 8, 10, 12, 15, 17, 19, 21, 23, 24, 26],
    dimension := 7, pivot := 26,
    facetSets := #[#[1, 3, 5, 7, 8, 10, 12], #[1, 3, 5, 7, 8, 10, 15, 17, 19, 21, 23, 24], #[1, 3, 5, 7, 8, 12, 15, 17, 19, 21, 24, 26], #[1, 3, 5, 7, 10, 12, 15, 17, 19, 21, 23, 26], #[1, 3, 5, 8, 10, 12, 15, 17, 21, 23, 24, 26], #[1, 3, 7, 8, 10, 12, 17, 19, 21, 23, 24, 26], #[1, 5, 7, 8, 10, 12, 15, 17, 19, 23, 24, 26], #[3, 5, 7, 8, 10, 12, 15, 19, 21, 23, 24, 26], #[15, 17, 19, 21, 23, 24, 26]],
    simplices := 7 }

theorem decode_geometry_Faces_032 : decodeFace geometryFacesJson032 = .ok geometryFacesTyped032 := by decide +kernel

theorem geometryFaces_032_shape : geometryFacesTyped032.vertices.size = 14 ∧ geometryFacesTyped032.vertices.toList.Nodup ∧
    (∀ i : Fin 14, geometryFacesTyped032.vertices[i.val]! < 28) ∧
    geometryFacesTyped032.pivot < 28 ∧ geometryFacesTyped032.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson033 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped033 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 8, 10, 15, 17, 19, 21, 23, 24],
    dimension := 6, pivot := 24,
    facetSets := #[#[1, 3, 5, 7, 8, 10], #[1, 3, 5, 7, 8, 15, 17, 19, 21, 24], #[1, 3, 5, 7, 10, 15, 17, 19, 21, 23], #[1, 3, 5, 8, 10, 15, 17, 21, 23, 24], #[1, 3, 7, 8, 10, 17, 19, 21, 23, 24], #[1, 5, 7, 8, 10, 15, 17, 19, 23, 24], #[3, 5, 7, 8, 10, 15, 19, 21, 23, 24], #[15, 17, 19, 21, 23, 24]],
    simplices := 6 }

theorem decode_geometry_Faces_033 : decodeFace geometryFacesJson033 = .ok geometryFacesTyped033 := by decide +kernel

theorem geometryFaces_033_shape : geometryFacesTyped033.vertices.size = 12 ∧ geometryFacesTyped033.vertices.toList.Nodup ∧
    (∀ i : Fin 12, geometryFacesTyped033.vertices[i.val]! < 28) ∧
    geometryFacesTyped033.pivot < 28 ∧ geometryFacesTyped033.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson034 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped034 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 10],
    dimension := 4, pivot := 10,
    facetSets := #[#[1, 3, 5, 7], #[1, 3, 5, 10], #[1, 3, 7, 10], #[1, 5, 7, 10], #[3, 5, 7, 10]],
    simplices := 1 }

theorem decode_geometry_Faces_034 : decodeFace geometryFacesJson034 = .ok geometryFacesTyped034 := by decide +kernel

theorem geometryFaces_034_shape : geometryFacesTyped034.vertices.size = 5 ∧ geometryFacesTyped034.vertices.toList.Nodup ∧
    (∀ i : Fin 5, geometryFacesTyped034.vertices[i.val]! < 28) ∧
    geometryFacesTyped034.pivot < 28 ∧ geometryFacesTyped034.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson035 : SourceJson :=
  (FaceLedgerBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped035 : FaceRecord :=
  { vertices := #[1, 3, 5, 7, 10, 15, 17, 19, 21, 23],
    dimension := 5, pivot := 23,
    facetSets := #[#[1, 3, 5, 7, 10], #[1, 3, 5, 7, 15, 17, 19, 21], #[1, 3, 5, 10, 15, 17, 21, 23], #[1, 3, 7, 10, 17, 19, 21, 23], #[1, 5, 7, 10, 15, 17, 19, 23], #[3, 5, 7, 10, 15, 19, 21, 23], #[15, 17, 19, 21, 23]],
    simplices := 5 }

theorem decode_geometry_Faces_035 : decodeFace geometryFacesJson035 = .ok geometryFacesTyped035 := by decide +kernel

theorem geometryFaces_035_shape : geometryFacesTyped035.vertices.size = 10 ∧ geometryFacesTyped035.vertices.toList.Nodup ∧
    (∀ i : Fin 10, geometryFacesTyped035.vertices[i.val]! < 28) ∧
    geometryFacesTyped035.pivot < 28 ∧ geometryFacesTyped035.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock003 : List SourceJson := [geometryFacesJson028, geometryFacesJson029, geometryFacesJson030, geometryFacesJson031, geometryFacesJson032, geometryFacesJson033, geometryFacesJson034, geometryFacesJson035]
noncomputable def geometryFacesTypedBlock003 : List (FaceRecord) := [geometryFacesTyped028, geometryFacesTyped029, geometryFacesTyped030, geometryFacesTyped031, geometryFacesTyped032, geometryFacesTyped033, geometryFacesTyped034, geometryFacesTyped035]

theorem geometry_Faces_block_003_push_eq (acc : List SourceJson) :
    FaceLedgerBlock003.blockPush acc = [geometryFacesJson035, geometryFacesJson034, geometryFacesJson033, geometryFacesJson032, geometryFacesJson031, geometryFacesJson030, geometryFacesJson029, geometryFacesJson028] ++ acc := by rfl

theorem geometry_Faces_block_003_reverse (acc : List SourceJson) :
    (FaceLedgerBlock003.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock003 := by
  rw [geometry_Faces_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_003 : geometryFacesJsonBlock003.mapM decodeFace = .ok geometryFacesTypedBlock003 := by
  simp only [geometryFacesJsonBlock003, geometryFacesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_028, decode_geometry_Faces_029, decode_geometry_Faces_030, decode_geometry_Faces_031, decode_geometry_Faces_032, decode_geometry_Faces_033, decode_geometry_Faces_034, decode_geometry_Faces_035]
  rfl

theorem geometry_Faces_block_003_length : geometryFacesTypedBlock003.length = 8 := by rfl

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
#print axioms decode_geometry_Faces_035
#print axioms geometryFaces_035_shape
#print axioms geometry_Faces_block_003_push_eq
#print axioms geometry_Faces_block_003_reverse
#print axioms decode_geometry_Faces_block_003
#print axioms geometry_Faces_block_003_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
