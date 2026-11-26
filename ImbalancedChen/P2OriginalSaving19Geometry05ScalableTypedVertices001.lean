import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVerticesBlock001

/-! Local original vertices decoding, indices 16 through 27.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson016 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨11, by decide +kernel⟩

noncomputable def geometryVerticesTyped016 : Array ℚ :=
  #[((124999 : ℚ) / (1000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((140623 : ℚ) / (2000000 : ℚ)), ((515597 : ℚ) / (12000000 : ℚ)), ((328141 : ℚ) / (12000000 : ℚ)), ((328141 : ℚ) / (12000000 : ℚ)), ((328133 : ℚ) / (12000000 : ℚ))]

theorem decode_geometry_Vertices_016 : rationalArray geometryVerticesJson016 = .ok geometryVerticesTyped016 := by decide +kernel

theorem geometryVertices_016_shape : geometryVerticesTyped016.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson017 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryVerticesTyped017 : Array ℚ :=
  #[((149999 : ℚ) / (1200000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((105467 : ℚ) / (1500000 : ℚ)), ((515593 : ℚ) / (12000000 : ℚ)), ((109381 : ℚ) / (4000000 : ℚ)), ((65627 : ℚ) / (2400000 : ℚ)), ((65627 : ℚ) / (2400000 : ℚ))]

theorem decode_geometry_Vertices_017 : rationalArray geometryVerticesJson017 = .ok geometryVerticesTyped017 := by decide +kernel

theorem geometryVertices_017_shape : geometryVerticesTyped017.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson018 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryVerticesTyped018 : Array ℚ :=
  #[((4671819 : ℚ) / (37000000 : ℚ)), ((14515649 : ℚ) / (148000000 : ℚ)), ((14015457 : ℚ) / (148000000 : ℚ)), ((984383 : ℚ) / (14800000 : ℚ)), ((5172011 : ℚ) / (148000000 : ℚ)), ((4671819 : ℚ) / (148000000 : ℚ)), ((4671819 : ℚ) / (148000000 : ℚ)), ((4171923 : ℚ) / (148000000 : ℚ))]

theorem decode_geometry_Vertices_018 : rationalArray geometryVerticesJson018 = .ok geometryVerticesTyped018 := by decide +kernel

theorem geometryVertices_018_shape : geometryVerticesTyped018.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson019 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryVerticesTyped019 : Array ℚ :=
  #[((1090611 : ℚ) / (8600000 : ℚ)), ((3371881 : ℚ) / (34400000 : ℚ)), ((3271833 : ℚ) / (34400000 : ℚ)), ((228127 : ℚ) / (3440000 : ℚ)), ((1190659 : ℚ) / (34400000 : ℚ)), ((1090611 : ℚ) / (34400000 : ℚ)), ((4953159 : ℚ) / (172000000 : ℚ)), ((4953159 : ℚ) / (172000000 : ℚ))]

theorem decode_geometry_Vertices_019 : rationalArray geometryVerticesJson019 = .ok geometryVerticesTyped019 := by decide +kernel

theorem geometryVertices_019_shape : geometryVerticesTyped019.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson020 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVerticesTyped020 : Array ℚ :=
  #[((534367 : ℚ) / (4200000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2859371 : ℚ) / (42000000 : ℚ)), ((496927 : ℚ) / (16800000 : ℚ)), ((828137 : ℚ) / (28000000 : ℚ)), ((828137 : ℚ) / (28000000 : ℚ)), ((496871 : ℚ) / (16800000 : ℚ))]

theorem decode_geometry_Vertices_020 : rationalArray geometryVerticesJson020 = .ok geometryVerticesTyped020 := by decide +kernel

theorem geometryVertices_020_shape : geometryVerticesTyped020.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson021 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVerticesTyped021 : Array ℚ :=
  #[((381691 : ℚ) / (3000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((408481 : ℚ) / (6000000 : ℚ)), ((354949 : ℚ) / (12000000 : ℚ)), ((354917 : ℚ) / (12000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ))]

theorem decode_geometry_Vertices_021 : rationalArray geometryVerticesJson021 = .ok geometryVerticesTyped021 := by decide +kernel

theorem geometryVertices_021_shape : geometryVerticesTyped021.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson022 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVerticesTyped022 : Array ℚ :=
  #[((2171839 : ℚ) / (17000000 : ℚ)), ((20671639 : ℚ) / (204000000 : ℚ)), ((19171703 : ℚ) / (204000000 : ℚ)), ((2296879 : ℚ) / (34000000 : ℚ)), ((6890909 : ℚ) / (204000000 : ℚ)), ((1378073 : ℚ) / (40800000 : ℚ)), ((1378073 : ℚ) / (40800000 : ℚ)), ((5390837 : ℚ) / (204000000 : ℚ))]

theorem decode_geometry_Vertices_022 : rationalArray geometryVerticesJson022 = .ok geometryVerticesTyped022 := by decide +kernel

theorem geometryVertices_022_shape : geometryVerticesTyped022.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson023 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVerticesTyped023 : Array ℚ :=
  #[((1771843 : ℚ) / (13800000 : ℚ)), ((27702889 : ℚ) / (276000000 : ℚ)), ((26202809 : ℚ) / (276000000 : ℚ)), ((9234419 : ℚ) / (138000000 : ℚ)), ((9234787 : ℚ) / (276000000 : ℚ)), ((3078017 : ℚ) / (92000000 : ℚ)), ((7734523 : ℚ) / (276000000 : ℚ)), ((7734523 : ℚ) / (276000000 : ℚ))]

theorem decode_geometry_Vertices_023 : rationalArray geometryVerticesJson023 = .ok geometryVerticesTyped023 := by decide +kernel

theorem geometryVertices_023_shape : geometryVerticesTyped023.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson024 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVerticesTyped024 : Array ℚ :=
  #[((1171847 : ℚ) / (9000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((1171943 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (36000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))]

theorem decode_geometry_Vertices_024 : rationalArray geometryVerticesJson024 = .ok geometryVerticesTyped024 := by decide +kernel

theorem geometryVertices_024_shape : geometryVerticesTyped024.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson025 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVerticesTyped025 : Array ℚ :=
  #[((1171847 : ℚ) / (9000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((1171943 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (36000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))]

theorem decode_geometry_Vertices_025 : rationalArray geometryVerticesJson025 = .ok geometryVerticesTyped025 := by decide +kernel

theorem geometryVertices_025_shape : geometryVerticesTyped025.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson026 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped026 : Array ℚ :=
  #[((1171847 : ℚ) / (9000000 : ℚ)), ((18327857 : ℚ) / (180000000 : ℚ)), ((16828033 : ℚ) / (180000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((2203129 : ℚ) / (60000000 : ℚ)), ((5109563 : ℚ) / (180000000 : ℚ)), ((5109443 : ℚ) / (180000000 : ℚ)), ((5109443 : ℚ) / (180000000 : ℚ))]

theorem decode_geometry_Vertices_026 : rationalArray geometryVerticesJson026 = .ok geometryVerticesTyped026 := by decide +kernel

theorem geometryVertices_026_shape : geometryVerticesTyped026.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson027 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped027 : Array ℚ :=
  #[((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828009 : ℚ) / (180000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((5109539 : ℚ) / (180000000 : ℚ)), ((5109539 : ℚ) / (180000000 : ℚ)), ((5109419 : ℚ) / (180000000 : ℚ))]

theorem decode_geometry_Vertices_027 : rationalArray geometryVerticesJson027 = .ok geometryVerticesTyped027 := by decide +kernel

theorem geometryVertices_027_shape : geometryVerticesTyped027.size = 8 := by decide +kernel

noncomputable def geometryVerticesJsonBlock001 : List SourceJson := [geometryVerticesJson016, geometryVerticesJson017, geometryVerticesJson018, geometryVerticesJson019, geometryVerticesJson020, geometryVerticesJson021, geometryVerticesJson022, geometryVerticesJson023, geometryVerticesJson024, geometryVerticesJson025, geometryVerticesJson026, geometryVerticesJson027]
noncomputable def geometryVerticesTypedBlock001 : List (Array ℚ) := [geometryVerticesTyped016, geometryVerticesTyped017, geometryVerticesTyped018, geometryVerticesTyped019, geometryVerticesTyped020, geometryVerticesTyped021, geometryVerticesTyped022, geometryVerticesTyped023, geometryVerticesTyped024, geometryVerticesTyped025, geometryVerticesTyped026, geometryVerticesTyped027]

theorem geometry_Vertices_block_001_push_eq (acc : List SourceJson) :
    VerticesBlock001.blockPush acc = [geometryVerticesJson027, geometryVerticesJson026, geometryVerticesJson025, geometryVerticesJson024, geometryVerticesJson023, geometryVerticesJson022, geometryVerticesJson021, geometryVerticesJson020, geometryVerticesJson019, geometryVerticesJson018, geometryVerticesJson017, geometryVerticesJson016] ++ acc := by rfl

theorem geometry_Vertices_block_001_reverse (acc : List SourceJson) :
    (VerticesBlock001.blockPush acc).reverse = acc.reverse ++ geometryVerticesJsonBlock001 := by
  rw [geometry_Vertices_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_001 : geometryVerticesJsonBlock001.mapM rationalArray = .ok geometryVerticesTypedBlock001 := by
  simp only [geometryVerticesJsonBlock001, geometryVerticesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_016, decode_geometry_Vertices_017, decode_geometry_Vertices_018, decode_geometry_Vertices_019, decode_geometry_Vertices_020, decode_geometry_Vertices_021, decode_geometry_Vertices_022, decode_geometry_Vertices_023, decode_geometry_Vertices_024, decode_geometry_Vertices_025, decode_geometry_Vertices_026, decode_geometry_Vertices_027]
  rfl

theorem geometry_Vertices_block_001_length : geometryVerticesTypedBlock001.length = 12 := by rfl

#print axioms decode_geometry_Vertices_016
#print axioms geometryVertices_016_shape
#print axioms decode_geometry_Vertices_017
#print axioms geometryVertices_017_shape
#print axioms decode_geometry_Vertices_018
#print axioms geometryVertices_018_shape
#print axioms decode_geometry_Vertices_019
#print axioms geometryVertices_019_shape
#print axioms decode_geometry_Vertices_020
#print axioms geometryVertices_020_shape
#print axioms decode_geometry_Vertices_021
#print axioms geometryVertices_021_shape
#print axioms decode_geometry_Vertices_022
#print axioms geometryVertices_022_shape
#print axioms decode_geometry_Vertices_023
#print axioms geometryVertices_023_shape
#print axioms decode_geometry_Vertices_024
#print axioms geometryVertices_024_shape
#print axioms decode_geometry_Vertices_025
#print axioms geometryVertices_025_shape
#print axioms decode_geometry_Vertices_026
#print axioms geometryVertices_026_shape
#print axioms decode_geometry_Vertices_027
#print axioms geometryVertices_027_shape
#print axioms geometry_Vertices_block_001_push_eq
#print axioms geometry_Vertices_block_001_reverse
#print axioms decode_geometry_Vertices_block_001
#print axioms geometry_Vertices_block_001_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
