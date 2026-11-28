import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesBlock004

/-! Local original vertex_values decoding, indices 32 through 32.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson032 : SourceJson :=
  (VertexValuesBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped032 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2765677 : ℚ) / (36000000 : ℚ)), ((2765677 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))] }

theorem decode_geometry_VertexValues_032 : decodeVertexValues geometryVertexValuesJson032 = .ok geometryVertexValuesTyped032 := by decide +kernel

theorem geometryVertexValues_032_shape : geometryVertexValuesTyped032.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock004 : List SourceJson := [geometryVertexValuesJson032]
noncomputable def geometryVertexValuesTypedBlock004 : List (VertexValues) := [geometryVertexValuesTyped032]

theorem geometry_VertexValues_block_004_push_eq (acc : List SourceJson) :
    VertexValuesBlock004.blockPush acc = [geometryVertexValuesJson032] ++ acc := by rfl

theorem geometry_VertexValues_block_004_reverse (acc : List SourceJson) :
    (VertexValuesBlock004.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock004 := by
  rw [geometry_VertexValues_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_004 : geometryVertexValuesJsonBlock004.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock004 := by
  simp only [geometryVertexValuesJsonBlock004, geometryVertexValuesTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_032]
  rfl

theorem geometry_VertexValues_block_004_length : geometryVertexValuesTypedBlock004.length = 1 := by rfl

#print axioms decode_geometry_VertexValues_032
#print axioms geometryVertexValues_032_shape
#print axioms geometry_VertexValues_block_004_push_eq
#print axioms geometry_VertexValues_block_004_reverse
#print axioms decode_geometry_VertexValues_block_004
#print axioms geometry_VertexValues_block_004_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
