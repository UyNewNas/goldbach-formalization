import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVertexValuesBlock001

/-! Local original vertex_values decoding, indices 8 through 15.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson008 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped008 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1453133 : ℚ) / (18000000 : ℚ)), ((1453133 : ℚ) / (18000000 : ℚ)), ((187499 : ℚ) / (1687500 : ℚ)), ((4546943 : ℚ) / (54000000 : ℚ)), ((4546943 : ℚ) / (54000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1453133 : ℚ) / (54000000 : ℚ))] }

theorem decode_geometry_VertexValues_008 : decodeVertexValues geometryVertexValuesJson008 = .ok geometryVertexValuesTyped008 := by decide +kernel

theorem geometryVertexValues_008_shape : geometryVertexValuesTyped008.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson009 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped009 : VertexValues :=
  { gap := ((93739 : ℚ) / (15500000 : ℚ)),
    factors := #[((11109451 : ℚ) / (124000000 : ℚ)), ((11859363 : ℚ) / (124000000 : ℚ)), ((3453097 : ℚ) / (31000000 : ℚ)), ((11359339 : ℚ) / (124000000 : ℚ)), ((11359339 : ℚ) / (124000000 : ℚ)), ((890629 : ℚ) / (12400000 : ℚ)), ((890629 : ℚ) / (24800000 : ℚ)), ((890629 : ℚ) / (24800000 : ℚ)), ((3953121 : ℚ) / (124000000 : ℚ)), ((3953121 : ℚ) / (124000000 : ℚ))] }

theorem decode_geometry_VertexValues_009 : decodeVertexValues geometryVertexValuesJson009 = .ok geometryVertexValuesTyped009 := by decide +kernel

theorem geometryVertexValues_009_shape : geometryVertexValuesTyped009.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson010 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped010 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((9515557 : ℚ) / (84000000 : ℚ)), ((6890749 : ℚ) / (84000000 : ℚ)), ((6890749 : ℚ) / (84000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((328129 : ℚ) / (10500000 : ℚ)), ((328129 : ℚ) / (10500000 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))] }

theorem decode_geometry_VertexValues_010 : decodeVertexValues geometryVertexValuesJson010 = .ok geometryVertexValuesTyped010 := by decide +kernel

theorem geometryVertexValues_010_shape : geometryVertexValuesTyped010.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson011 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped011 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((82031 : ℚ) / (875000 : ℚ)), ((82031 : ℚ) / (875000 : ℚ)), ((634371 : ℚ) / (5600000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ))] }

theorem decode_geometry_VertexValues_011 : decodeVertexValues geometryVertexValuesJson011 = .ok geometryVertexValuesTyped011 := by decide +kernel

theorem geometryVertexValues_011_shape : geometryVertexValuesTyped011.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson012 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped012 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((82031 : ℚ) / (875000 : ℚ)), ((82031 : ℚ) / (875000 : ℚ)), ((634371 : ℚ) / (5600000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((109377 : ℚ) / (3500000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ))] }

theorem decode_geometry_VertexValues_012 : decodeVertexValues geometryVertexValuesJson012 = .ok geometryVertexValuesTyped012 := by decide +kernel

theorem geometryVertexValues_012_shape : geometryVertexValuesTyped012.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson013 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped013 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((2296857 : ℚ) / (20125000 : ℚ)), ((953141 : ℚ) / (11500000 : ℚ)), ((953141 : ℚ) / (11500000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))] }

theorem decode_geometry_VertexValues_013 : decodeVertexValues geometryVertexValuesJson013 = .ok geometryVertexValuesTyped013 := by decide +kernel

theorem geometryVertexValues_013_shape : geometryVertexValuesTyped013.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson014 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped014 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((96093 : ℚ) / (837500 : ℚ)), ((1646903 : ℚ) / (20100000 : ℚ)), ((1646903 : ℚ) / (20100000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))] }

theorem decode_geometry_VertexValues_014 : decodeVertexValues geometryVertexValuesJson014 = .ok geometryVertexValuesTyped014 := by decide +kernel

theorem geometryVertexValues_014_shape : geometryVertexValuesTyped014.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson015 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped015 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((3309347 : ℚ) / (28800000 : ℚ)), ((11578361 : ℚ) / (144000000 : ℚ)), ((11578361 : ℚ) / (144000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))] }

theorem decode_geometry_VertexValues_015 : decodeVertexValues geometryVertexValuesJson015 = .ok geometryVertexValuesTyped015 := by decide +kernel

theorem geometryVertexValues_015_shape : geometryVertexValuesTyped015.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock001 : List SourceJson := [geometryVertexValuesJson008, geometryVertexValuesJson009, geometryVertexValuesJson010, geometryVertexValuesJson011, geometryVertexValuesJson012, geometryVertexValuesJson013, geometryVertexValuesJson014, geometryVertexValuesJson015]
noncomputable def geometryVertexValuesTypedBlock001 : List (VertexValues) := [geometryVertexValuesTyped008, geometryVertexValuesTyped009, geometryVertexValuesTyped010, geometryVertexValuesTyped011, geometryVertexValuesTyped012, geometryVertexValuesTyped013, geometryVertexValuesTyped014, geometryVertexValuesTyped015]

theorem geometry_VertexValues_block_001_push_eq (acc : List SourceJson) :
    VertexValuesBlock001.blockPush acc = [geometryVertexValuesJson015, geometryVertexValuesJson014, geometryVertexValuesJson013, geometryVertexValuesJson012, geometryVertexValuesJson011, geometryVertexValuesJson010, geometryVertexValuesJson009, geometryVertexValuesJson008] ++ acc := by rfl

theorem geometry_VertexValues_block_001_reverse (acc : List SourceJson) :
    (VertexValuesBlock001.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock001 := by
  rw [geometry_VertexValues_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_001 : geometryVertexValuesJsonBlock001.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock001 := by
  simp only [geometryVertexValuesJsonBlock001, geometryVertexValuesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_008, decode_geometry_VertexValues_009, decode_geometry_VertexValues_010, decode_geometry_VertexValues_011, decode_geometry_VertexValues_012, decode_geometry_VertexValues_013, decode_geometry_VertexValues_014, decode_geometry_VertexValues_015]
  rfl

theorem geometry_VertexValues_block_001_length : geometryVertexValuesTypedBlock001.length = 8 := by rfl

#print axioms decode_geometry_VertexValues_008
#print axioms geometryVertexValues_008_shape
#print axioms decode_geometry_VertexValues_009
#print axioms geometryVertexValues_009_shape
#print axioms decode_geometry_VertexValues_010
#print axioms geometryVertexValues_010_shape
#print axioms decode_geometry_VertexValues_011
#print axioms geometryVertexValues_011_shape
#print axioms decode_geometry_VertexValues_012
#print axioms geometryVertexValues_012_shape
#print axioms decode_geometry_VertexValues_013
#print axioms geometryVertexValues_013_shape
#print axioms decode_geometry_VertexValues_014
#print axioms geometryVertexValues_014_shape
#print axioms decode_geometry_VertexValues_015
#print axioms geometryVertexValues_015_shape
#print axioms geometry_VertexValues_block_001_push_eq
#print axioms geometry_VertexValues_block_001_reverse
#print axioms decode_geometry_VertexValues_block_001
#print axioms geometry_VertexValues_block_001_length
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
