import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesBlock002

/-! Local original vertex_values decoding, indices 16 through 23.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson016 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped016 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((328133 : ℚ) / (4000000 : ℚ)), ((328133 : ℚ) / (4000000 : ℚ)), ((124999 : ℚ) / (1000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((140623 : ℚ) / (2000000 : ℚ)), ((515597 : ℚ) / (12000000 : ℚ)), ((328141 : ℚ) / (12000000 : ℚ)), ((328141 : ℚ) / (12000000 : ℚ)), ((328133 : ℚ) / (12000000 : ℚ))] }

theorem decode_geometry_VertexValues_016 : decodeVertexValues geometryVertexValuesJson016 = .ok geometryVertexValuesTyped016 := by decide +kernel

theorem geometryVertexValues_016_shape : geometryVertexValuesTyped016.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson017 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped017 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((65627 : ℚ) / (800000 : ℚ)), ((65627 : ℚ) / (800000 : ℚ)), ((149999 : ℚ) / (1200000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((105467 : ℚ) / (1500000 : ℚ)), ((515593 : ℚ) / (12000000 : ℚ)), ((109381 : ℚ) / (4000000 : ℚ)), ((65627 : ℚ) / (2400000 : ℚ)), ((65627 : ℚ) / (2400000 : ℚ))] }

theorem decode_geometry_VertexValues_017 : decodeVertexValues geometryVertexValuesJson017 = .ok geometryVertexValuesTyped017 := by decide +kernel

theorem geometryVertexValues_017_shape : geometryVertexValuesTyped017.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson018 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped018 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((12515769 : ℚ) / (148000000 : ℚ)), ((12515769 : ℚ) / (148000000 : ℚ)), ((4671819 : ℚ) / (37000000 : ℚ)), ((14515649 : ℚ) / (148000000 : ℚ)), ((14015457 : ℚ) / (148000000 : ℚ)), ((984383 : ℚ) / (14800000 : ℚ)), ((5172011 : ℚ) / (148000000 : ℚ)), ((4671819 : ℚ) / (148000000 : ℚ)), ((4671819 : ℚ) / (148000000 : ℚ)), ((4171923 : ℚ) / (148000000 : ℚ))] }

theorem decode_geometry_VertexValues_018 : decodeVertexValues geometryVertexValuesJson018 = .ok geometryVertexValuesTyped018 := by decide +kernel

theorem geometryVertexValues_018_shape : geometryVertexValuesTyped018.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson019 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped019 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((14859477 : ℚ) / (172000000 : ℚ)), ((14859477 : ℚ) / (172000000 : ℚ)), ((1090611 : ℚ) / (8600000 : ℚ)), ((3371881 : ℚ) / (34400000 : ℚ)), ((3271833 : ℚ) / (34400000 : ℚ)), ((228127 : ℚ) / (3440000 : ℚ)), ((1190659 : ℚ) / (34400000 : ℚ)), ((1090611 : ℚ) / (34400000 : ℚ)), ((4953159 : ℚ) / (172000000 : ℚ)), ((4953159 : ℚ) / (172000000 : ℚ))] }

theorem decode_geometry_VertexValues_019 : decodeVertexValues geometryVertexValuesJson019 = .ok geometryVertexValuesTyped019 := by decide +kernel

theorem geometryVertexValues_019_shape : geometryVertexValuesTyped019.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson020 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped020 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((496871 : ℚ) / (5600000 : ℚ)), ((496871 : ℚ) / (5600000 : ℚ)), ((534367 : ℚ) / (4200000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2859371 : ℚ) / (42000000 : ℚ)), ((496927 : ℚ) / (16800000 : ℚ)), ((828137 : ℚ) / (28000000 : ℚ)), ((828137 : ℚ) / (28000000 : ℚ)), ((496871 : ℚ) / (16800000 : ℚ))] }

theorem decode_geometry_VertexValues_020 : decodeVertexValues geometryVertexValuesJson020 = .ok geometryVertexValuesTyped020 := by decide +kernel

theorem geometryVertexValues_020_shape : geometryVertexValuesTyped020.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson021 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped021 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((354909 : ℚ) / (4000000 : ℚ)), ((354909 : ℚ) / (4000000 : ℚ)), ((381691 : ℚ) / (3000000 : ℚ)), ((1171879 : ℚ) / (12000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((408481 : ℚ) / (6000000 : ℚ)), ((354949 : ℚ) / (12000000 : ℚ)), ((354917 : ℚ) / (12000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ))] }

theorem decode_geometry_VertexValues_021 : decodeVertexValues geometryVertexValuesJson021 = .ok geometryVertexValuesTyped021 := by decide +kernel

theorem geometryVertexValues_021_shape : geometryVertexValuesTyped021.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson022 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped022 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5390837 : ℚ) / (68000000 : ℚ)), ((5390837 : ℚ) / (68000000 : ℚ)), ((2171839 : ℚ) / (17000000 : ℚ)), ((20671639 : ℚ) / (204000000 : ℚ)), ((19171703 : ℚ) / (204000000 : ℚ)), ((2296879 : ℚ) / (34000000 : ℚ)), ((6890909 : ℚ) / (204000000 : ℚ)), ((1378073 : ℚ) / (40800000 : ℚ)), ((1378073 : ℚ) / (40800000 : ℚ)), ((5390837 : ℚ) / (204000000 : ℚ))] }

theorem decode_geometry_VertexValues_022 : decodeVertexValues geometryVertexValuesJson022 = .ok geometryVertexValuesTyped022 := by decide +kernel

theorem geometryVertexValues_022_shape : geometryVertexValuesTyped022.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson023 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped023 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((7734523 : ℚ) / (92000000 : ℚ)), ((7734523 : ℚ) / (92000000 : ℚ)), ((1771843 : ℚ) / (13800000 : ℚ)), ((27702889 : ℚ) / (276000000 : ℚ)), ((26202809 : ℚ) / (276000000 : ℚ)), ((9234419 : ℚ) / (138000000 : ℚ)), ((9234787 : ℚ) / (276000000 : ℚ)), ((3078017 : ℚ) / (92000000 : ℚ)), ((7734523 : ℚ) / (276000000 : ℚ)), ((7734523 : ℚ) / (276000000 : ℚ))] }

theorem decode_geometry_VertexValues_023 : decodeVertexValues geometryVertexValuesJson023 = .ok geometryVertexValuesTyped023 := by decide +kernel

theorem geometryVertexValues_023_shape : geometryVertexValuesTyped023.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock002 : List SourceJson := [geometryVertexValuesJson016, geometryVertexValuesJson017, geometryVertexValuesJson018, geometryVertexValuesJson019, geometryVertexValuesJson020, geometryVertexValuesJson021, geometryVertexValuesJson022, geometryVertexValuesJson023]
noncomputable def geometryVertexValuesTypedBlock002 : List (VertexValues) := [geometryVertexValuesTyped016, geometryVertexValuesTyped017, geometryVertexValuesTyped018, geometryVertexValuesTyped019, geometryVertexValuesTyped020, geometryVertexValuesTyped021, geometryVertexValuesTyped022, geometryVertexValuesTyped023]

theorem geometry_VertexValues_block_002_push_eq (acc : List SourceJson) :
    VertexValuesBlock002.blockPush acc = [geometryVertexValuesJson023, geometryVertexValuesJson022, geometryVertexValuesJson021, geometryVertexValuesJson020, geometryVertexValuesJson019, geometryVertexValuesJson018, geometryVertexValuesJson017, geometryVertexValuesJson016] ++ acc := by rfl

theorem geometry_VertexValues_block_002_reverse (acc : List SourceJson) :
    (VertexValuesBlock002.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock002 := by
  rw [geometry_VertexValues_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_002 : geometryVertexValuesJsonBlock002.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock002 := by
  simp only [geometryVertexValuesJsonBlock002, geometryVertexValuesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_016, decode_geometry_VertexValues_017, decode_geometry_VertexValues_018, decode_geometry_VertexValues_019, decode_geometry_VertexValues_020, decode_geometry_VertexValues_021, decode_geometry_VertexValues_022, decode_geometry_VertexValues_023]
  rfl

theorem geometry_VertexValues_block_002_length : geometryVertexValuesTypedBlock002.length = 8 := by rfl

#print axioms decode_geometry_VertexValues_016
#print axioms geometryVertexValues_016_shape
#print axioms decode_geometry_VertexValues_017
#print axioms geometryVertexValues_017_shape
#print axioms decode_geometry_VertexValues_018
#print axioms geometryVertexValues_018_shape
#print axioms decode_geometry_VertexValues_019
#print axioms geometryVertexValues_019_shape
#print axioms decode_geometry_VertexValues_020
#print axioms geometryVertexValues_020_shape
#print axioms decode_geometry_VertexValues_021
#print axioms geometryVertexValues_021_shape
#print axioms decode_geometry_VertexValues_022
#print axioms geometryVertexValues_022_shape
#print axioms decode_geometry_VertexValues_023
#print axioms geometryVertexValues_023_shape
#print axioms geometry_VertexValues_block_002_push_eq
#print axioms geometry_VertexValues_block_002_reverse
#print axioms decode_geometry_VertexValues_block_002
#print axioms geometry_VertexValues_block_002_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
