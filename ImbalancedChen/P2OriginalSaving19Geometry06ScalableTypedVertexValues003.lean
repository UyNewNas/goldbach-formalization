import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesBlock003

/-! Local original vertex_values decoding, indices 24 through 31.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson024 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped024 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((4875051 : ℚ) / (56000000 : ℚ)), ((4875051 : ℚ) / (56000000 : ℚ)), ((49999 : ℚ) / (400000 : ℚ)), ((1074991 : ℚ) / (11200000 : ℚ)), ((1074991 : ℚ) / (11200000 : ℚ)), ((75001 : ℚ) / (1120000 : ℚ)), ((75001 : ℚ) / (2240000 : ℚ)), ((75001 : ℚ) / (2240000 : ℚ)), ((1625017 : ℚ) / (56000000 : ℚ)), ((1625017 : ℚ) / (56000000 : ℚ))] }

theorem decode_geometry_VertexValues_024 : decodeVertexValues geometryVertexValuesJson024 = .ok geometryVertexValuesTyped024 := by decide +kernel

theorem geometryVertexValues_024_shape : geometryVertexValuesTyped024.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson025 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped025 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((328131 : ℚ) / (4000000 : ℚ)), ((328131 : ℚ) / (4000000 : ℚ)), ((49999 : ℚ) / (400000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((70313 : ℚ) / (1000000 : ℚ)), ((70313 : ℚ) / (2000000 : ℚ)), ((70313 : ℚ) / (2000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ))] }

theorem decode_geometry_VertexValues_025 : decodeVertexValues geometryVertexValuesJson025 = .ok geometryVertexValuesTyped025 := by decide +kernel

theorem geometryVertexValues_025_shape : geometryVertexValuesTyped025.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson026 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped026 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((328131 : ℚ) / (4000000 : ℚ)), ((328131 : ℚ) / (4000000 : ℚ)), ((49999 : ℚ) / (400000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((70313 : ℚ) / (1000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((328139 : ℚ) / (12000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ)), ((109377 : ℚ) / (4000000 : ℚ))] }

theorem decode_geometry_VertexValues_026 : decodeVertexValues geometryVertexValuesJson026 = .ok geometryVertexValuesTyped026 := by decide +kernel

theorem geometryVertexValues_026_shape : geometryVertexValuesTyped026.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson027 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped027 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((178121 : ℚ) / (1400000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((953137 : ℚ) / (14000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))] }

theorem decode_geometry_VertexValues_027 : decodeVertexValues geometryVertexValuesJson027 = .ok geometryVertexValuesTyped027 := by decide +kernel

theorem geometryVertexValues_027_shape : geometryVertexValuesTyped027.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson028 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped028 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((2671817 : ℚ) / (21000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2859407 : ℚ) / (42000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))] }

theorem decode_geometry_VertexValues_028 : decodeVertexValues geometryVertexValuesJson028 = .ok geometryVertexValuesTyped028 := by decide +kernel

theorem geometryVertexValues_028_shape : geometryVertexValuesTyped028.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson029 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped029 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5390709 : ℚ) / (68000000 : ℚ)), ((5390709 : ℚ) / (68000000 : ℚ)), ((6515477 : ℚ) / (51000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((3834347 : ℚ) / (40800000 : ℚ)), ((6890717 : ℚ) / (102000000 : ℚ)), ((6890717 : ℚ) / (204000000 : ℚ)), ((6890717 : ℚ) / (204000000 : ℚ)), ((6890717 : ℚ) / (204000000 : ℚ)), ((1796903 : ℚ) / (68000000 : ℚ))] }

theorem decode_geometry_VertexValues_029 : decodeVertexValues geometryVertexValuesJson029 = .ok geometryVertexValuesTyped029 := by decide +kernel

theorem geometryVertexValues_029_shape : geometryVertexValuesTyped029.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson030 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped030 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((7734491 : ℚ) / (92000000 : ℚ)), ((7734491 : ℚ) / (92000000 : ℚ)), ((354367 : ℚ) / (2760000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((26202937 : ℚ) / (276000000 : ℚ)), ((9234499 : ℚ) / (138000000 : ℚ)), ((9234499 : ℚ) / (276000000 : ℚ)), ((9234499 : ℚ) / (276000000 : ℚ)), ((7734491 : ℚ) / (276000000 : ℚ)), ((7734491 : ℚ) / (276000000 : ℚ))] }

theorem decode_geometry_VertexValues_030 : decodeVertexValues geometryVertexValuesJson030 = .ok geometryVertexValuesTyped030 := by decide +kernel

theorem geometryVertexValues_030_shape : geometryVertexValuesTyped030.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson031 : SourceJson :=
  (VertexValuesBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped031 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2765701 : ℚ) / (36000000 : ℚ)), ((2765701 : ℚ) / (36000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((234379 : ℚ) / (3600000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))] }

theorem decode_geometry_VertexValues_031 : decodeVertexValues geometryVertexValuesJson031 = .ok geometryVertexValuesTyped031 := by decide +kernel

theorem geometryVertexValues_031_shape : geometryVertexValuesTyped031.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock003 : List SourceJson := [geometryVertexValuesJson024, geometryVertexValuesJson025, geometryVertexValuesJson026, geometryVertexValuesJson027, geometryVertexValuesJson028, geometryVertexValuesJson029, geometryVertexValuesJson030, geometryVertexValuesJson031]
noncomputable def geometryVertexValuesTypedBlock003 : List (VertexValues) := [geometryVertexValuesTyped024, geometryVertexValuesTyped025, geometryVertexValuesTyped026, geometryVertexValuesTyped027, geometryVertexValuesTyped028, geometryVertexValuesTyped029, geometryVertexValuesTyped030, geometryVertexValuesTyped031]

theorem geometry_VertexValues_block_003_push_eq (acc : List SourceJson) :
    VertexValuesBlock003.blockPush acc = [geometryVertexValuesJson031, geometryVertexValuesJson030, geometryVertexValuesJson029, geometryVertexValuesJson028, geometryVertexValuesJson027, geometryVertexValuesJson026, geometryVertexValuesJson025, geometryVertexValuesJson024] ++ acc := by rfl

theorem geometry_VertexValues_block_003_reverse (acc : List SourceJson) :
    (VertexValuesBlock003.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock003 := by
  rw [geometry_VertexValues_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_003 : geometryVertexValuesJsonBlock003.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock003 := by
  simp only [geometryVertexValuesJsonBlock003, geometryVertexValuesTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_024, decode_geometry_VertexValues_025, decode_geometry_VertexValues_026, decode_geometry_VertexValues_027, decode_geometry_VertexValues_028, decode_geometry_VertexValues_029, decode_geometry_VertexValues_030, decode_geometry_VertexValues_031]
  rfl

theorem geometry_VertexValues_block_003_length : geometryVertexValuesTypedBlock003.length = 8 := by rfl

#print axioms decode_geometry_VertexValues_024
#print axioms geometryVertexValues_024_shape
#print axioms decode_geometry_VertexValues_025
#print axioms geometryVertexValues_025_shape
#print axioms decode_geometry_VertexValues_026
#print axioms geometryVertexValues_026_shape
#print axioms decode_geometry_VertexValues_027
#print axioms geometryVertexValues_027_shape
#print axioms decode_geometry_VertexValues_028
#print axioms geometryVertexValues_028_shape
#print axioms decode_geometry_VertexValues_029
#print axioms geometryVertexValues_029_shape
#print axioms decode_geometry_VertexValues_030
#print axioms geometryVertexValues_030_shape
#print axioms decode_geometry_VertexValues_031
#print axioms geometryVertexValues_031_shape
#print axioms geometry_VertexValues_block_003_push_eq
#print axioms geometry_VertexValues_block_003_reverse
#print axioms decode_geometry_VertexValues_block_003
#print axioms geometry_VertexValues_block_003_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
