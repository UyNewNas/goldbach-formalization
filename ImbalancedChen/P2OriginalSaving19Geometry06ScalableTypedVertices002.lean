import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVerticesBlock002

/-! Local original vertices decoding, indices 32 through 32.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson032 : SourceJson :=
  (VerticesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped032 : Array ℚ :=
  #[((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))]

theorem decode_geometry_Vertices_032 : rationalArray geometryVerticesJson032 = .ok geometryVerticesTyped032 := by decide +kernel

theorem geometryVertices_032_shape : geometryVerticesTyped032.size = 8 := by decide +kernel

noncomputable def geometryVerticesJsonBlock002 : List SourceJson := [geometryVerticesJson032]
noncomputable def geometryVerticesTypedBlock002 : List (Array ℚ) := [geometryVerticesTyped032]

theorem geometry_Vertices_block_002_push_eq (acc : List SourceJson) :
    VerticesBlock002.blockPush acc = [geometryVerticesJson032] ++ acc := by rfl

theorem geometry_Vertices_block_002_reverse (acc : List SourceJson) :
    (VerticesBlock002.blockPush acc).reverse = acc.reverse ++ geometryVerticesJsonBlock002 := by
  rw [geometry_Vertices_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_002 : geometryVerticesJsonBlock002.mapM rationalArray = .ok geometryVerticesTypedBlock002 := by
  simp only [geometryVerticesJsonBlock002, geometryVerticesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_032]
  rfl

theorem geometry_Vertices_block_002_length : geometryVerticesTypedBlock002.length = 1 := by rfl

#print axioms decode_geometry_Vertices_032
#print axioms geometryVertices_032_shape
#print axioms geometry_Vertices_block_002_push_eq
#print axioms geometry_Vertices_block_002_reverse
#print axioms decode_geometry_Vertices_block_002
#print axioms geometry_Vertices_block_002_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
