import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableFaceLedgerBlock005

/-! Local original face_ledger decoding, indices 47 through 55.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryFacesJson047 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryFacesTyped047 : FaceRecord :=
  { vertices := #[7, 9, 11, 12, 14, 16, 17, 19, 24, 25, 26, 28, 30, 31],
    dimension := 7, pivot := 31,
    facetSets := #[#[7, 9, 11, 12, 14, 16, 17, 24, 25, 26, 28, 31], #[7, 9, 11, 12, 14, 16, 19, 24, 25, 26, 28, 30], #[7, 9, 11, 12, 14, 17, 19, 24, 25, 26, 30, 31], #[7, 9, 11, 12, 16, 17, 19, 25, 26, 28, 30, 31], #[7, 9, 11, 14, 16, 17, 19, 24, 25, 28, 30, 31], #[7, 9, 12, 14, 16, 17, 19, 24, 26, 28, 30, 31], #[7, 11, 12, 14, 16, 17, 19], #[9, 24, 25, 26, 28, 30, 31], #[11, 12, 14, 16, 17, 19, 24, 25, 26, 28, 30, 31]],
    simplices := 7 }

theorem decode_geometry_Faces_047 : decodeFace geometryFacesJson047 = .ok geometryFacesTyped047 := by decide +kernel

theorem geometryFaces_047_shape : geometryFacesTyped047.vertices.size = 14 ∧ geometryFacesTyped047.vertices.toList.Nodup ∧
    (∀ i : Fin 14, geometryFacesTyped047.vertices[i.val]! < 33) ∧
    geometryFacesTyped047.pivot < 33 ∧ geometryFacesTyped047.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson048 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryFacesTyped048 : FaceRecord :=
  { vertices := #[7, 9, 11, 12, 14, 16, 19, 24, 25, 26, 28, 30],
    dimension := 6, pivot := 30,
    facetSets := #[#[7, 9, 11, 12, 14, 16, 24, 25, 26, 28], #[7, 9, 11, 12, 14, 19, 24, 25, 26, 30], #[7, 9, 11, 12, 16, 19, 25, 26, 28, 30], #[7, 9, 11, 14, 16, 19, 24, 25, 28, 30], #[7, 9, 12, 14, 16, 19, 24, 26, 28, 30], #[7, 11, 12, 14, 16, 19], #[9, 24, 25, 26, 28, 30], #[11, 12, 14, 16, 19, 24, 25, 26, 28, 30]],
    simplices := 6 }

theorem decode_geometry_Faces_048 : decodeFace geometryFacesJson048 = .ok geometryFacesTyped048 := by decide +kernel

theorem geometryFaces_048_shape : geometryFacesTyped048.vertices.size = 12 ∧ geometryFacesTyped048.vertices.toList.Nodup ∧
    (∀ i : Fin 12, geometryFacesTyped048.vertices[i.val]! < 33) ∧
    geometryFacesTyped048.pivot < 33 ∧ geometryFacesTyped048.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson049 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryFacesTyped049 : FaceRecord :=
  { vertices := #[7, 9, 11, 12, 14, 16, 24, 25, 26, 28],
    dimension := 5, pivot := 28,
    facetSets := #[#[7, 9, 11, 12, 14, 24, 25, 26], #[7, 9, 11, 12, 16, 25, 26, 28], #[7, 9, 11, 14, 16, 24, 25, 28], #[7, 9, 12, 14, 16, 24, 26, 28], #[7, 11, 12, 14, 16], #[9, 24, 25, 26, 28], #[11, 12, 14, 16, 24, 25, 26, 28]],
    simplices := 5 }

theorem decode_geometry_Faces_049 : decodeFace geometryFacesJson049 = .ok geometryFacesTyped049 := by decide +kernel

theorem geometryFaces_049_shape : geometryFacesTyped049.vertices.size = 10 ∧ geometryFacesTyped049.vertices.toList.Nodup ∧
    (∀ i : Fin 10, geometryFacesTyped049.vertices[i.val]! < 33) ∧
    geometryFacesTyped049.pivot < 33 ∧ geometryFacesTyped049.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson050 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryFacesTyped050 : FaceRecord :=
  { vertices := #[7, 9, 11, 12, 14, 24, 25, 26],
    dimension := 4, pivot := 26,
    facetSets := #[#[7, 9, 11, 12, 25, 26], #[7, 9, 11, 14, 24, 25], #[7, 9, 12, 14, 24, 26], #[7, 11, 12, 14], #[9, 24, 25, 26], #[11, 12, 14, 24, 25, 26]],
    simplices := 4 }

theorem decode_geometry_Faces_050 : decodeFace geometryFacesJson050 = .ok geometryFacesTyped050 := by decide +kernel

theorem geometryFaces_050_shape : geometryFacesTyped050.vertices.size = 8 ∧ geometryFacesTyped050.vertices.toList.Nodup ∧
    (∀ i : Fin 8, geometryFacesTyped050.vertices[i.val]! < 33) ∧
    geometryFacesTyped050.pivot < 33 ∧ geometryFacesTyped050.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson051 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryFacesTyped051 : FaceRecord :=
  { vertices := #[7, 9, 11, 14, 24, 25],
    dimension := 3, pivot := 25,
    facetSets := #[#[7, 9, 11, 25], #[7, 9, 14, 24], #[7, 11, 14], #[9, 24, 25], #[11, 14, 24, 25]],
    simplices := 3 }

theorem decode_geometry_Faces_051 : decodeFace geometryFacesJson051 = .ok geometryFacesTyped051 := by decide +kernel

theorem geometryFaces_051_shape : geometryFacesTyped051.vertices.size = 6 ∧ geometryFacesTyped051.vertices.toList.Nodup ∧
    (∀ i : Fin 6, geometryFacesTyped051.vertices[i.val]! < 33) ∧
    geometryFacesTyped051.pivot < 33 ∧ geometryFacesTyped051.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson052 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryFacesTyped052 : FaceRecord :=
  { vertices := #[7, 9, 14, 24],
    dimension := 2, pivot := 24,
    facetSets := #[#[7, 9], #[7, 14], #[9, 24], #[14, 24]],
    simplices := 2 }

theorem decode_geometry_Faces_052 : decodeFace geometryFacesJson052 = .ok geometryFacesTyped052 := by decide +kernel

theorem geometryFaces_052_shape : geometryFacesTyped052.vertices.size = 4 ∧ geometryFacesTyped052.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped052.vertices[i.val]! < 33) ∧
    geometryFacesTyped052.pivot < 33 ∧ geometryFacesTyped052.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson053 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryFacesTyped053 : FaceRecord :=
  { vertices := #[7, 11],
    dimension := 1, pivot := 11,
    facetSets := #[#[7], #[11]],
    simplices := 1 }

theorem decode_geometry_Faces_053 : decodeFace geometryFacesJson053 = .ok geometryFacesTyped053 := by decide +kernel

theorem geometryFaces_053_shape : geometryFacesTyped053.vertices.size = 2 ∧ geometryFacesTyped053.vertices.toList.Nodup ∧
    (∀ i : Fin 2, geometryFacesTyped053.vertices[i.val]! < 33) ∧
    geometryFacesTyped053.pivot < 33 ∧ geometryFacesTyped053.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson054 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryFacesTyped054 : FaceRecord :=
  { vertices := #[7, 11, 12],
    dimension := 2, pivot := 12,
    facetSets := #[#[7, 11], #[7, 12], #[11, 12]],
    simplices := 1 }

theorem decode_geometry_Faces_054 : decodeFace geometryFacesJson054 = .ok geometryFacesTyped054 := by decide +kernel

theorem geometryFaces_054_shape : geometryFacesTyped054.vertices.size = 3 ∧ geometryFacesTyped054.vertices.toList.Nodup ∧
    (∀ i : Fin 3, geometryFacesTyped054.vertices[i.val]! < 33) ∧
    geometryFacesTyped054.pivot < 33 ∧ geometryFacesTyped054.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJson055 : SourceJson :=
  (FaceLedgerBlock005.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryFacesTyped055 : FaceRecord :=
  { vertices := #[7, 11, 12, 14],
    dimension := 3, pivot := 14,
    facetSets := #[#[7, 11, 12], #[7, 11, 14], #[7, 12, 14], #[11, 12, 14]],
    simplices := 1 }

theorem decode_geometry_Faces_055 : decodeFace geometryFacesJson055 = .ok geometryFacesTyped055 := by decide +kernel

theorem geometryFaces_055_shape : geometryFacesTyped055.vertices.size = 4 ∧ geometryFacesTyped055.vertices.toList.Nodup ∧
    (∀ i : Fin 4, geometryFacesTyped055.vertices[i.val]! < 33) ∧
    geometryFacesTyped055.pivot < 33 ∧ geometryFacesTyped055.dimension ≤ 8 := by decide +kernel

noncomputable def geometryFacesJsonBlock005 : List SourceJson := [geometryFacesJson047, geometryFacesJson048, geometryFacesJson049, geometryFacesJson050, geometryFacesJson051, geometryFacesJson052, geometryFacesJson053, geometryFacesJson054, geometryFacesJson055]
noncomputable def geometryFacesTypedBlock005 : List (FaceRecord) := [geometryFacesTyped047, geometryFacesTyped048, geometryFacesTyped049, geometryFacesTyped050, geometryFacesTyped051, geometryFacesTyped052, geometryFacesTyped053, geometryFacesTyped054, geometryFacesTyped055]

theorem geometry_Faces_block_005_push_eq (acc : List SourceJson) :
    FaceLedgerBlock005.blockPush acc = [geometryFacesJson055, geometryFacesJson054, geometryFacesJson053, geometryFacesJson052, geometryFacesJson051, geometryFacesJson050, geometryFacesJson049, geometryFacesJson048, geometryFacesJson047] ++ acc := by rfl

theorem geometry_Faces_block_005_reverse (acc : List SourceJson) :
    (FaceLedgerBlock005.blockPush acc).reverse = acc.reverse ++ geometryFacesJsonBlock005 := by
  rw [geometry_Faces_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Faces_block_005 : geometryFacesJsonBlock005.mapM decodeFace = .ok geometryFacesTypedBlock005 := by
  simp only [geometryFacesJsonBlock005, geometryFacesTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Faces_047, decode_geometry_Faces_048, decode_geometry_Faces_049, decode_geometry_Faces_050, decode_geometry_Faces_051, decode_geometry_Faces_052, decode_geometry_Faces_053, decode_geometry_Faces_054, decode_geometry_Faces_055]
  rfl

theorem geometry_Faces_block_005_length : geometryFacesTypedBlock005.length = 9 := by rfl

#print axioms decode_geometry_Faces_047
#print axioms geometryFaces_047_shape
#print axioms decode_geometry_Faces_048
#print axioms geometryFaces_048_shape
#print axioms decode_geometry_Faces_049
#print axioms geometryFaces_049_shape
#print axioms decode_geometry_Faces_050
#print axioms geometryFaces_050_shape
#print axioms decode_geometry_Faces_051
#print axioms geometryFaces_051_shape
#print axioms decode_geometry_Faces_052
#print axioms geometryFaces_052_shape
#print axioms decode_geometry_Faces_053
#print axioms geometryFaces_053_shape
#print axioms decode_geometry_Faces_054
#print axioms geometryFaces_054_shape
#print axioms decode_geometry_Faces_055
#print axioms geometryFaces_055_shape
#print axioms geometry_Faces_block_005_push_eq
#print axioms geometry_Faces_block_005_reverse
#print axioms decode_geometry_Faces_block_005
#print axioms geometry_Faces_block_005_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
