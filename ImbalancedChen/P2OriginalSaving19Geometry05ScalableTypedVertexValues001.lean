import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesBlock001

/-! Local original vertex_values decoding, indices 8 through 15.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson008 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped008 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1078153 : ℚ) / (12000000 : ℚ)), ((1078153 : ℚ) / (12000000 : ℚ)), ((703121 : ℚ) / (6000000 : ℚ)), ((78129 : ℚ) / (1000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))] }

theorem decode_geometry_VertexValues_008 : decodeVertexValues geometryVertexValuesJson008 = .ok geometryVertexValuesTyped008 := by decide +kernel

theorem geometryVertexValues_008_shape : geometryVertexValuesTyped008.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson009 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped009 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((215629 : ℚ) / (2400000 : ℚ)), ((215629 : ℚ) / (2400000 : ℚ)), ((703121 : ℚ) / (6000000 : ℚ)), ((78129 : ℚ) / (1000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))] }

theorem decode_geometry_VertexValues_009 : decodeVertexValues geometryVertexValuesJson009 = .ok geometryVertexValuesTyped009 := by decide +kernel

theorem geometryVertexValues_009_shape : geometryVertexValuesTyped009.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson010 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped010 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1546871 : ℚ) / (16000000 : ℚ)), ((1546871 : ℚ) / (16000000 : ℚ)), ((703121 : ℚ) / (6000000 : ℚ)), ((4078193 : ℚ) / (48000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((1546871 : ℚ) / (48000000 : ℚ)), ((1546871 : ℚ) / (48000000 : ℚ))] }

theorem decode_geometry_VertexValues_010 : decodeVertexValues geometryVertexValuesJson010 = .ok geometryVertexValuesTyped010 := by decide +kernel

theorem geometryVertexValues_010_shape : geometryVertexValuesTyped010.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson011 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped011 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((215629 : ℚ) / (2400000 : ℚ)), ((215629 : ℚ) / (2400000 : ℚ)), ((703121 : ℚ) / (6000000 : ℚ)), ((3140653 : ℚ) / (36000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((215629 : ℚ) / (7200000 : ℚ))] }

theorem decode_geometry_VertexValues_011 : decodeVertexValues geometryVertexValuesJson011 = .ok geometryVertexValuesTyped011 := by decide +kernel

theorem geometryVertexValues_011_shape : geometryVertexValuesTyped011.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson012 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped012 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109331 : ℚ) / (52000000 : ℚ)), ((5109331 : ℚ) / (52000000 : ℚ)), ((6203049 : ℚ) / (52000000 : ℚ)), ((421879 : ℚ) / (4875000 : ℚ)), ((11859707 : ℚ) / (156000000 : ℚ)), ((3953097 : ℚ) / (52000000 : ℚ)), ((70311 : ℚ) / (1625000 : ℚ)), ((340629 : ℚ) / (10400000 : ℚ)), ((5109331 : ℚ) / (156000000 : ℚ)), ((5109331 : ℚ) / (156000000 : ℚ))] }

theorem decode_geometry_VertexValues_012 : decodeVertexValues geometryVertexValuesJson012 = .ok geometryVertexValuesTyped012 := by decide +kernel

theorem geometryVertexValues_012_shape : geometryVertexValuesTyped012.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson013 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped013 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((5109307 : ℚ) / (52000000 : ℚ)), ((5109307 : ℚ) / (52000000 : ℚ)), ((3721831 : ℚ) / (31200000 : ℚ)), ((10547 : ℚ) / (121875 : ℚ)), ((3953233 : ℚ) / (52000000 : ℚ)), ((11859283 : ℚ) / (156000000 : ℚ)), ((421867 : ℚ) / (9750000 : ℚ)), ((1703137 : ℚ) / (52000000 : ℚ)), ((1703137 : ℚ) / (52000000 : ℚ)), ((5109307 : ℚ) / (156000000 : ℚ))] }

theorem decode_geometry_VertexValues_013 : decodeVertexValues geometryVertexValuesJson013 = .ok geometryVertexValuesTyped013 := by decide +kernel

theorem geometryVertexValues_013_shape : geometryVertexValuesTyped013.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson014 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped014 : VertexValues :=
  { gap := ((5857 : ℚ) / (2656250 : ℚ)),
    factors := #[((29203273 : ℚ) / (340000000 : ℚ)), ((29952969 : ℚ) / (340000000 : ℚ)), ((10484347 : ℚ) / (85000000 : ℚ)), ((33453137 : ℚ) / (340000000 : ℚ)), ((31453041 : ℚ) / (340000000 : ℚ)), ((2296879 : ℚ) / (34000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((10484347 : ℚ) / (340000000 : ℚ)), ((10484347 : ℚ) / (340000000 : ℚ)), ((9984323 : ℚ) / (340000000 : ℚ))] }

theorem decode_geometry_VertexValues_014 : decodeVertexValues geometryVertexValuesJson014 = .ok geometryVertexValuesTyped014 := by decide +kernel

theorem geometryVertexValues_014_shape : geometryVertexValuesTyped014.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson015 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped015 : VertexValues :=
  { gap := ((13387 : ℚ) / (6500000 : ℚ)),
    factors := #[((4506721 : ℚ) / (52000000 : ℚ)), ((354909 : ℚ) / (4000000 : ℚ)), ((1609371 : ℚ) / (13000000 : ℚ)), ((5113841 : ℚ) / (52000000 : ℚ)), ((4828113 : ℚ) / (52000000 : ℚ)), ((350447 : ℚ) / (5200000 : ℚ)), ((1895099 : ℚ) / (52000000 : ℚ)), ((1609371 : ℚ) / (52000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ))] }

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
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
