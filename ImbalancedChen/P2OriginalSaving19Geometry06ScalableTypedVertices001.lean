import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVerticesBlock001

/-! Local original vertices decoding, indices 16 through 31.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson016 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨15, by decide +kernel⟩

noncomputable def geometryVerticesTyped016 : Array ℚ :=
  #[((1838527 : ℚ) / (16000000 : ℚ)), ((3859451 : ℚ) / (48000000 : ℚ)), ((3859451 : ℚ) / (48000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))]

theorem decode_geometry_Vertices_016 : rationalArray geometryVerticesJson016 = .ok geometryVerticesTyped016 := by decide +kernel

theorem geometryVertices_016_shape : geometryVerticesTyped016.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson017 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨14, by decide +kernel⟩

noncomputable def geometryVerticesTyped017 : Array ℚ :=
  #[((1171863 : ℚ) / (10000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))]

theorem decode_geometry_Vertices_017 : rationalArray geometryVerticesJson017 = .ok geometryVerticesTyped017 := by decide +kernel

theorem geometryVertices_017_shape : geometryVerticesTyped017.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson018 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨13, by decide +kernel⟩

noncomputable def geometryVerticesTyped018 : Array ℚ :=
  #[((1171863 : ℚ) / (10000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))]

theorem decode_geometry_Vertices_018 : rationalArray geometryVerticesJson018 = .ok geometryVerticesTyped018 := by decide +kernel

theorem geometryVertices_018_shape : geometryVerticesTyped018.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson019 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨12, by decide +kernel⟩

noncomputable def geometryVerticesTyped019 : Array ℚ :=
  #[((1171863 : ℚ) / (10000000 : ℚ)), ((20390869 : ℚ) / (240000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((7734323 : ℚ) / (240000000 : ℚ)), ((7734323 : ℚ) / (240000000 : ℚ))]

theorem decode_geometry_Vertices_019 : rationalArray geometryVerticesJson019 = .ok geometryVerticesTyped019 := by decide +kernel

theorem geometryVertices_019_shape : geometryVerticesTyped019.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson020 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨11, by decide +kernel⟩

noncomputable def geometryVerticesTyped020 : Array ℚ :=
  #[((1171863 : ℚ) / (10000000 : ℚ)), ((15703297 : ℚ) / (180000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((5390597 : ℚ) / (180000000 : ℚ))]

theorem decode_geometry_Vertices_020 : rationalArray geometryVerticesJson020 = .ok geometryVerticesTyped020 := by decide +kernel

theorem geometryVertices_020_shape : geometryVerticesTyped020.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson021 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryVerticesTyped021 : Array ℚ :=
  #[((609363 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((734379 : ℚ) / (10000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((484387 : ℚ) / (20000000 : ℚ))]

theorem decode_geometry_Vertices_021 : rationalArray geometryVerticesJson021 = .ok geometryVerticesTyped021 := by decide +kernel

theorem geometryVertices_021_shape : geometryVerticesTyped021.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson022 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryVerticesTyped022 : Array ℚ :=
  #[((123577 : ℚ) / (1000000 : ℚ)), ((382099 : ℚ) / (4000000 : ℚ)), ((382099 : ℚ) / (4000000 : ℚ)), ((26989 : ℚ) / (400000 : ℚ)), ((26989 : ℚ) / (800000 : ℚ)), ((26989 : ℚ) / (800000 : ℚ)), ((26989 : ℚ) / (800000 : ℚ)), ((112217 : ℚ) / (4000000 : ℚ))]

theorem decode_geometry_Vertices_022 : rationalArray geometryVerticesJson022 = .ok geometryVerticesTyped022 := by decide +kernel

theorem geometryVertices_022_shape : geometryVerticesTyped022.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson023 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryVerticesTyped023 : Array ℚ :=
  #[((23437 : ℚ) / (187500 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((421879 : ℚ) / (6000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((109379 : ℚ) / (4000000 : ℚ)), ((109379 : ℚ) / (4000000 : ℚ)), ((328129 : ℚ) / (12000000 : ℚ))]

theorem decode_geometry_Vertices_023 : rationalArray geometryVerticesJson023 = .ok geometryVerticesTyped023 := by decide +kernel

theorem geometryVertices_023_shape : geometryVerticesTyped023.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson024 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVerticesTyped024 : Array ℚ :=
  #[((49999 : ℚ) / (400000 : ℚ)), ((1074991 : ℚ) / (11200000 : ℚ)), ((1074991 : ℚ) / (11200000 : ℚ)), ((75001 : ℚ) / (1120000 : ℚ)), ((75001 : ℚ) / (2240000 : ℚ)), ((75001 : ℚ) / (2240000 : ℚ)), ((1625017 : ℚ) / (56000000 : ℚ)), ((1625017 : ℚ) / (56000000 : ℚ))]

theorem decode_geometry_Vertices_024 : rationalArray geometryVerticesJson024 = .ok geometryVerticesTyped024 := by decide +kernel

theorem geometryVertices_024_shape : geometryVerticesTyped024.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson025 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVerticesTyped025 : Array ℚ :=
  #[((49999 : ℚ) / (400000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((70313 : ℚ) / (1000000 : ℚ)), ((70313 : ℚ) / (2000000 : ℚ)), ((70313 : ℚ) / (2000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ))]

theorem decode_geometry_Vertices_025 : rationalArray geometryVerticesJson025 = .ok geometryVerticesTyped025 := by decide +kernel

theorem geometryVertices_025_shape : geometryVerticesTyped025.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson026 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVerticesTyped026 : Array ℚ :=
  #[((49999 : ℚ) / (400000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((70313 : ℚ) / (1000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((328139 : ℚ) / (12000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ))]

theorem decode_geometry_Vertices_026 : rationalArray geometryVerticesJson026 = .ok geometryVerticesTyped026 := by decide +kernel

theorem geometryVertices_026_shape : geometryVerticesTyped026.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson027 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVerticesTyped027 : Array ℚ :=
  #[((178121 : ℚ) / (1400000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((953137 : ℚ) / (14000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))]

theorem decode_geometry_Vertices_027 : rationalArray geometryVerticesJson027 = .ok geometryVerticesTyped027 := by decide +kernel

theorem geometryVertices_027_shape : geometryVerticesTyped027.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson028 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVerticesTyped028 : Array ℚ :=
  #[((2671817 : ℚ) / (21000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2859407 : ℚ) / (42000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))]

theorem decode_geometry_Vertices_028 : rationalArray geometryVerticesJson028 = .ok geometryVerticesTyped028 := by decide +kernel

theorem geometryVertices_028_shape : geometryVerticesTyped028.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson029 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVerticesTyped029 : Array ℚ :=
  #[((6515477 : ℚ) / (51000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((3834347 : ℚ) / (40800000 : ℚ)), ((6890717 : ℚ) / (102000000 : ℚ)), ((6890717 : ℚ) / (204000000 : ℚ)), ((6890717 : ℚ) / (204000000 : ℚ)), ((6890717 : ℚ) / (204000000 : ℚ)), ((1796903 : ℚ) / (68000000 : ℚ))]

theorem decode_geometry_Vertices_029 : rationalArray geometryVerticesJson029 = .ok geometryVerticesTyped029 := by decide +kernel

theorem geometryVertices_029_shape : geometryVerticesTyped029.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson030 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped030 : Array ℚ :=
  #[((354367 : ℚ) / (2760000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((26202937 : ℚ) / (276000000 : ℚ)), ((9234499 : ℚ) / (138000000 : ℚ)), ((9234499 : ℚ) / (276000000 : ℚ)), ((9234499 : ℚ) / (276000000 : ℚ)), ((7734491 : ℚ) / (276000000 : ℚ)), ((7734491 : ℚ) / (276000000 : ℚ))]

theorem decode_geometry_Vertices_030 : rationalArray geometryVerticesJson030 = .ok geometryVerticesTyped030 := by decide +kernel

theorem geometryVertices_030_shape : geometryVerticesTyped030.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson031 : SourceJson :=
  (VerticesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped031 : Array ℚ :=
  #[((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))]

theorem decode_geometry_Vertices_031 : rationalArray geometryVerticesJson031 = .ok geometryVerticesTyped031 := by decide +kernel

theorem geometryVertices_031_shape : geometryVerticesTyped031.size = 8 := by decide +kernel

noncomputable def geometryVerticesJsonBlock001 : List SourceJson := [geometryVerticesJson016, geometryVerticesJson017, geometryVerticesJson018, geometryVerticesJson019, geometryVerticesJson020, geometryVerticesJson021, geometryVerticesJson022, geometryVerticesJson023, geometryVerticesJson024, geometryVerticesJson025, geometryVerticesJson026, geometryVerticesJson027, geometryVerticesJson028, geometryVerticesJson029, geometryVerticesJson030, geometryVerticesJson031]
noncomputable def geometryVerticesTypedBlock001 : List (Array ℚ) := [geometryVerticesTyped016, geometryVerticesTyped017, geometryVerticesTyped018, geometryVerticesTyped019, geometryVerticesTyped020, geometryVerticesTyped021, geometryVerticesTyped022, geometryVerticesTyped023, geometryVerticesTyped024, geometryVerticesTyped025, geometryVerticesTyped026, geometryVerticesTyped027, geometryVerticesTyped028, geometryVerticesTyped029, geometryVerticesTyped030, geometryVerticesTyped031]

theorem geometry_Vertices_block_001_push_eq (acc : List SourceJson) :
    VerticesBlock001.blockPush acc = [geometryVerticesJson031, geometryVerticesJson030, geometryVerticesJson029, geometryVerticesJson028, geometryVerticesJson027, geometryVerticesJson026, geometryVerticesJson025, geometryVerticesJson024, geometryVerticesJson023, geometryVerticesJson022, geometryVerticesJson021, geometryVerticesJson020, geometryVerticesJson019, geometryVerticesJson018, geometryVerticesJson017, geometryVerticesJson016] ++ acc := by rfl

theorem geometry_Vertices_block_001_reverse (acc : List SourceJson) :
    (VerticesBlock001.blockPush acc).reverse = acc.reverse ++ geometryVerticesJsonBlock001 := by
  rw [geometry_Vertices_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_001 : geometryVerticesJsonBlock001.mapM rationalArray = .ok geometryVerticesTypedBlock001 := by
  simp only [geometryVerticesJsonBlock001, geometryVerticesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_016, decode_geometry_Vertices_017, decode_geometry_Vertices_018, decode_geometry_Vertices_019, decode_geometry_Vertices_020, decode_geometry_Vertices_021, decode_geometry_Vertices_022, decode_geometry_Vertices_023, decode_geometry_Vertices_024, decode_geometry_Vertices_025, decode_geometry_Vertices_026, decode_geometry_Vertices_027, decode_geometry_Vertices_028, decode_geometry_Vertices_029, decode_geometry_Vertices_030, decode_geometry_Vertices_031]
  rfl

theorem geometry_Vertices_block_001_length : geometryVerticesTypedBlock001.length = 16 := by rfl

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
#print axioms decode_geometry_Vertices_028
#print axioms geometryVertices_028_shape
#print axioms decode_geometry_Vertices_029
#print axioms geometryVertices_029_shape
#print axioms decode_geometry_Vertices_030
#print axioms geometryVertices_030_shape
#print axioms decode_geometry_Vertices_031
#print axioms geometryVertices_031_shape
#print axioms geometry_Vertices_block_001_push_eq
#print axioms geometry_Vertices_block_001_reverse
#print axioms decode_geometry_Vertices_block_001
#print axioms geometry_Vertices_block_001_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
