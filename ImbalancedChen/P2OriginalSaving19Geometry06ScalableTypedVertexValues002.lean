import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesBlock002

/-! Local original vertex_values decoding, indices 16 through 23.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson016 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped016 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1838527 : ℚ) / (16000000 : ℚ)), ((3859451 : ℚ) / (48000000 : ℚ)), ((3859451 : ℚ) / (48000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))] }

theorem decode_geometry_VertexValues_016 : decodeVertexValues geometryVertexValuesJson016 = .ok geometryVertexValuesTyped016 := by decide +kernel

theorem geometryVertexValues_016_shape : geometryVertexValuesTyped016.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson017 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped017 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1796879 : ℚ) / (20000000 : ℚ)), ((1796879 : ℚ) / (20000000 : ℚ)), ((1171863 : ℚ) / (10000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))] }

theorem decode_geometry_VertexValues_017 : decodeVertexValues geometryVertexValuesJson017 = .ok geometryVertexValuesTyped017 := by decide +kernel

theorem geometryVertexValues_017_shape : geometryVertexValuesTyped017.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson018 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped018 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5390597 : ℚ) / (60000000 : ℚ)), ((5390597 : ℚ) / (60000000 : ℚ)), ((1171863 : ℚ) / (10000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))] }

theorem decode_geometry_VertexValues_018 : decodeVertexValues geometryVertexValuesJson018 = .ok geometryVertexValuesTyped018 := by decide +kernel

theorem geometryVertexValues_018_shape : geometryVertexValuesTyped018.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson019 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped019 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((7734323 : ℚ) / (80000000 : ℚ)), ((7734323 : ℚ) / (80000000 : ℚ)), ((1171863 : ℚ) / (10000000 : ℚ)), ((20390869 : ℚ) / (240000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((7734323 : ℚ) / (240000000 : ℚ)), ((7734323 : ℚ) / (240000000 : ℚ))] }

theorem decode_geometry_VertexValues_019 : decodeVertexValues geometryVertexValuesJson019 = .ok geometryVertexValuesTyped019 := by decide +kernel

theorem geometryVertexValues_019_shape : geometryVertexValuesTyped019.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson020 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped020 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5390597 : ℚ) / (60000000 : ℚ)), ((5390597 : ℚ) / (60000000 : ℚ)), ((1171863 : ℚ) / (10000000 : ℚ)), ((15703297 : ℚ) / (180000000 : ℚ)), ((1171903 : ℚ) / (15000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((5390597 : ℚ) / (180000000 : ℚ))] }

theorem decode_geometry_VertexValues_020 : decodeVertexValues geometryVertexValuesJson020 = .ok geometryVertexValuesTyped020 := by decide +kernel

theorem geometryVertexValues_020_shape : geometryVertexValuesTyped020.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson021 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped021 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1453161 : ℚ) / (20000000 : ℚ)), ((1453161 : ℚ) / (20000000 : ℚ)), ((609363 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((734379 : ℚ) / (10000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((484387 : ℚ) / (20000000 : ℚ))] }

theorem decode_geometry_VertexValues_021 : decodeVertexValues geometryVertexValuesJson021 = .ok geometryVertexValuesTyped021 := by decide +kernel

theorem geometryVertexValues_021_shape : geometryVertexValuesTyped021.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson022 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped022 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((336651 : ℚ) / (4000000 : ℚ)), ((336651 : ℚ) / (4000000 : ℚ)), ((123577 : ℚ) / (1000000 : ℚ)), ((382099 : ℚ) / (4000000 : ℚ)), ((382099 : ℚ) / (4000000 : ℚ)), ((26989 : ℚ) / (400000 : ℚ)), ((26989 : ℚ) / (800000 : ℚ)), ((26989 : ℚ) / (800000 : ℚ)), ((26989 : ℚ) / (800000 : ℚ)), ((112217 : ℚ) / (4000000 : ℚ))] }

theorem decode_geometry_VertexValues_022 : decodeVertexValues geometryVertexValuesJson022 = .ok geometryVertexValuesTyped022 := by decide +kernel

theorem geometryVertexValues_022_shape : geometryVertexValuesTyped022.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson023 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped023 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((328129 : ℚ) / (4000000 : ℚ)), ((328129 : ℚ) / (4000000 : ℚ)), ((23437 : ℚ) / (187500 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((421879 : ℚ) / (6000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((109379 : ℚ) / (4000000 : ℚ)), ((109379 : ℚ) / (4000000 : ℚ)), ((328129 : ℚ) / (12000000 : ℚ))] }

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
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
