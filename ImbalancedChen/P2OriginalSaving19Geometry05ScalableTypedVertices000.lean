import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVerticesBlock000

/-! Local original vertices decoding, indices 0 through 15.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson000 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨15, by decide +kernel⟩

noncomputable def geometryVerticesTyped000 : Array ℚ :=
  #[((634379 : ℚ) / (5600000 : ℚ)), ((1378169 : ℚ) / (16800000 : ℚ)), ((6890621 : ℚ) / (84000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((328133 : ℚ) / (10500000 : ℚ)), ((328133 : ℚ) / (10500000 : ℚ)), ((164063 : ℚ) / (5250000 : ℚ))]

theorem decode_geometry_Vertices_000 : rationalArray geometryVerticesJson000 = .ok geometryVerticesTyped000 := by decide +kernel

theorem geometryVertices_000_shape : geometryVerticesTyped000.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson001 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨14, by decide +kernel⟩

noncomputable def geometryVerticesTyped001 : Array ℚ :=
  #[((9515693 : ℚ) / (84000000 : ℚ)), ((6890837 : ℚ) / (84000000 : ℚ)), ((2296871 : ℚ) / (28000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((65627 : ℚ) / (2100000 : ℚ)), ((3418 : ℚ) / (109375 : ℚ)), ((3418 : ℚ) / (109375 : ℚ))]

theorem decode_geometry_Vertices_001 : rationalArray geometryVerticesJson001 = .ok geometryVerticesTyped001 := by decide +kernel

theorem geometryVertices_001_shape : geometryVerticesTyped001.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson002 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨13, by decide +kernel⟩

noncomputable def geometryVerticesTyped002 : Array ℚ :=
  #[((3309379 : ℚ) / (28800000 : ℚ)), ((2315717 : ℚ) / (28800000 : ℚ)), ((11578201 : ℚ) / (144000000 : ℚ)), ((11577817 : ℚ) / (144000000 : ℚ)), ((2484539 : ℚ) / (72000000 : ℚ)), ((2484347 : ℚ) / (72000000 : ℚ)), ((2484347 : ℚ) / (72000000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))]

theorem decode_geometry_Vertices_002 : rationalArray geometryVerticesJson002 = .ok geometryVerticesTyped002 := by decide +kernel

theorem geometryVertices_002_shape : geometryVerticesTyped002.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson003 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨12, by decide +kernel⟩

noncomputable def geometryVerticesTyped003 : Array ℚ :=
  #[((16546903 : ℚ) / (144000000 : ℚ)), ((11578577 : ℚ) / (144000000 : ℚ)), ((11578193 : ℚ) / (144000000 : ℚ)), ((11577809 : ℚ) / (144000000 : ℚ)), ((2484547 : ℚ) / (72000000 : ℚ)), ((496871 : ℚ) / (14400000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))]

theorem decode_geometry_Vertices_003 : rationalArray geometryVerticesJson003 = .ok geometryVerticesTyped003 := by decide +kernel

theorem geometryVertices_003_shape : geometryVerticesTyped003.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson004 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨11, by decide +kernel⟩

noncomputable def geometryVerticesTyped004 : Array ℚ :=
  #[((7390621 : ℚ) / (64000000 : ℚ)), ((2828137 : ℚ) / (32000000 : ℚ)), ((2609379 : ℚ) / (32000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((2609379 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((515621 : ℚ) / (16000000 : ℚ))]

theorem decode_geometry_Vertices_004 : rationalArray geometryVerticesJson004 = .ok geometryVerticesTyped004 := by decide +kernel

theorem geometryVertices_004_shape : geometryVerticesTyped004.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson005 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryVerticesTyped005 : Array ℚ :=
  #[((7859371 : ℚ) / (68000000 : ℚ)), ((2984387 : ℚ) / (34000000 : ℚ)), ((2765629 : ℚ) / (34000000 : ℚ)), ((2546871 : ℚ) / (34000000 : ℚ)), ((2765629 : ℚ) / (68000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))]

theorem decode_geometry_Vertices_005 : rationalArray geometryVerticesJson005 = .ok geometryVerticesTyped005 := by decide +kernel

theorem geometryVertices_005_shape : geometryVerticesTyped005.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson006 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryVerticesTyped006 : Array ℚ :=
  #[((3078117 : ℚ) / (26500000 : ℚ)), ((2234423 : ℚ) / (26500000 : ℚ)), ((265627 : ℚ) / (3312500 : ℚ)), ((2015609 : ℚ) / (26500000 : ℚ)), ((265627 : ℚ) / (6625000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((843747 : ℚ) / (26500000 : ℚ))]

theorem decode_geometry_Vertices_006 : rationalArray geometryVerticesJson006 = .ok geometryVerticesTyped006 := by decide +kernel

theorem geometryVertices_006_shape : geometryVerticesTyped006.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson007 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryVerticesTyped007 : Array ℚ :=
  #[((709373 : ℚ) / (6100000 : ℚ)), ((509387 : ℚ) / (6100000 : ℚ)), ((30469 : ℚ) / (381250 : ℚ)), ((465621 : ℚ) / (6100000 : ℚ)), ((30469 : ℚ) / (762500 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))]

theorem decode_geometry_Vertices_007 : rationalArray geometryVerticesJson007 = .ok geometryVerticesTyped007 := by decide +kernel

theorem geometryVertices_007_shape : geometryVerticesTyped007.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson008 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVerticesTyped008 : Array ℚ :=
  #[((703121 : ℚ) / (6000000 : ℚ)), ((78129 : ℚ) / (1000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))]

theorem decode_geometry_Vertices_008 : rationalArray geometryVerticesJson008 = .ok geometryVerticesTyped008 := by decide +kernel

theorem geometryVertices_008_shape : geometryVerticesTyped008.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson009 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVerticesTyped009 : Array ℚ :=
  #[((703121 : ℚ) / (6000000 : ℚ)), ((78129 : ℚ) / (1000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))]

theorem decode_geometry_Vertices_009 : rationalArray geometryVerticesJson009 = .ok geometryVerticesTyped009 := by decide +kernel

theorem geometryVertices_009_shape : geometryVerticesTyped009.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson010 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVerticesTyped010 : Array ℚ :=
  #[((703121 : ℚ) / (6000000 : ℚ)), ((4078193 : ℚ) / (48000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((1546871 : ℚ) / (48000000 : ℚ)), ((1546871 : ℚ) / (48000000 : ℚ))]

theorem decode_geometry_Vertices_010 : rationalArray geometryVerticesJson010 = .ok geometryVerticesTyped010 := by decide +kernel

theorem geometryVertices_010_shape : geometryVerticesTyped010.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson011 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVerticesTyped011 : Array ℚ :=
  #[((703121 : ℚ) / (6000000 : ℚ)), ((3140653 : ℚ) / (36000000 : ℚ)), ((234379 : ℚ) / (3000000 : ℚ)), ((234371 : ℚ) / (3000000 : ℚ)), ((234379 : ℚ) / (6000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((215629 : ℚ) / (7200000 : ℚ))]

theorem decode_geometry_Vertices_011 : rationalArray geometryVerticesJson011 = .ok geometryVerticesTyped011 := by decide +kernel

theorem geometryVertices_011_shape : geometryVerticesTyped011.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson012 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVerticesTyped012 : Array ℚ :=
  #[((6203049 : ℚ) / (52000000 : ℚ)), ((421879 : ℚ) / (4875000 : ℚ)), ((11859707 : ℚ) / (156000000 : ℚ)), ((3953097 : ℚ) / (52000000 : ℚ)), ((70311 : ℚ) / (1625000 : ℚ)), ((340629 : ℚ) / (10400000 : ℚ)), ((5109331 : ℚ) / (156000000 : ℚ)), ((5109331 : ℚ) / (156000000 : ℚ))]

theorem decode_geometry_Vertices_012 : rationalArray geometryVerticesJson012 = .ok geometryVerticesTyped012 := by decide +kernel

theorem geometryVertices_012_shape : geometryVerticesTyped012.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson013 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVerticesTyped013 : Array ℚ :=
  #[((3721831 : ℚ) / (31200000 : ℚ)), ((10547 : ℚ) / (121875 : ℚ)), ((3953233 : ℚ) / (52000000 : ℚ)), ((11859283 : ℚ) / (156000000 : ℚ)), ((421867 : ℚ) / (9750000 : ℚ)), ((1703137 : ℚ) / (52000000 : ℚ)), ((1703137 : ℚ) / (52000000 : ℚ)), ((5109307 : ℚ) / (156000000 : ℚ))]

theorem decode_geometry_Vertices_013 : rationalArray geometryVerticesJson013 = .ok geometryVerticesTyped013 := by decide +kernel

theorem geometryVertices_013_shape : geometryVerticesTyped013.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson014 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped014 : Array ℚ :=
  #[((10484347 : ℚ) / (85000000 : ℚ)), ((33453137 : ℚ) / (340000000 : ℚ)), ((31453041 : ℚ) / (340000000 : ℚ)), ((2296879 : ℚ) / (34000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((10484347 : ℚ) / (340000000 : ℚ)), ((10484347 : ℚ) / (340000000 : ℚ)), ((9984323 : ℚ) / (340000000 : ℚ))]

theorem decode_geometry_Vertices_014 : rationalArray geometryVerticesJson014 = .ok geometryVerticesTyped014 := by decide +kernel

theorem geometryVertices_014_shape : geometryVerticesTyped014.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson015 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped015 : Array ℚ :=
  #[((1609371 : ℚ) / (13000000 : ℚ)), ((5113841 : ℚ) / (52000000 : ℚ)), ((4828113 : ℚ) / (52000000 : ℚ)), ((350447 : ℚ) / (5200000 : ℚ)), ((1895099 : ℚ) / (52000000 : ℚ)), ((1609371 : ℚ) / (52000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ)), ((118303 : ℚ) / (4000000 : ℚ))]

theorem decode_geometry_Vertices_015 : rationalArray geometryVerticesJson015 = .ok geometryVerticesTyped015 := by decide +kernel

theorem geometryVertices_015_shape : geometryVerticesTyped015.size = 8 := by decide +kernel

noncomputable def geometryVerticesJsonBlock000 : List SourceJson := [geometryVerticesJson000, geometryVerticesJson001, geometryVerticesJson002, geometryVerticesJson003, geometryVerticesJson004, geometryVerticesJson005, geometryVerticesJson006, geometryVerticesJson007, geometryVerticesJson008, geometryVerticesJson009, geometryVerticesJson010, geometryVerticesJson011, geometryVerticesJson012, geometryVerticesJson013, geometryVerticesJson014, geometryVerticesJson015]
noncomputable def geometryVerticesTypedBlock000 : List (Array ℚ) := [geometryVerticesTyped000, geometryVerticesTyped001, geometryVerticesTyped002, geometryVerticesTyped003, geometryVerticesTyped004, geometryVerticesTyped005, geometryVerticesTyped006, geometryVerticesTyped007, geometryVerticesTyped008, geometryVerticesTyped009, geometryVerticesTyped010, geometryVerticesTyped011, geometryVerticesTyped012, geometryVerticesTyped013, geometryVerticesTyped014, geometryVerticesTyped015]

theorem geometry_Vertices_block_000_push_eq (acc : List SourceJson) :
    VerticesBlock000.blockPush acc = [geometryVerticesJson015, geometryVerticesJson014, geometryVerticesJson013, geometryVerticesJson012, geometryVerticesJson011, geometryVerticesJson010, geometryVerticesJson009, geometryVerticesJson008, geometryVerticesJson007, geometryVerticesJson006, geometryVerticesJson005, geometryVerticesJson004, geometryVerticesJson003, geometryVerticesJson002, geometryVerticesJson001, geometryVerticesJson000] ++ acc := by rfl

theorem geometry_Vertices_block_000_reverse (acc : List SourceJson) :
    (VerticesBlock000.blockPush acc).reverse = acc.reverse ++ geometryVerticesJsonBlock000 := by
  rw [geometry_Vertices_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_000 : geometryVerticesJsonBlock000.mapM rationalArray = .ok geometryVerticesTypedBlock000 := by
  simp only [geometryVerticesJsonBlock000, geometryVerticesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_000, decode_geometry_Vertices_001, decode_geometry_Vertices_002, decode_geometry_Vertices_003, decode_geometry_Vertices_004, decode_geometry_Vertices_005, decode_geometry_Vertices_006, decode_geometry_Vertices_007, decode_geometry_Vertices_008, decode_geometry_Vertices_009, decode_geometry_Vertices_010, decode_geometry_Vertices_011, decode_geometry_Vertices_012, decode_geometry_Vertices_013, decode_geometry_Vertices_014, decode_geometry_Vertices_015]
  rfl

theorem geometry_Vertices_block_000_length : geometryVerticesTypedBlock000.length = 16 := by rfl

#print axioms decode_geometry_Vertices_000
#print axioms geometryVertices_000_shape
#print axioms decode_geometry_Vertices_001
#print axioms geometryVertices_001_shape
#print axioms decode_geometry_Vertices_002
#print axioms geometryVertices_002_shape
#print axioms decode_geometry_Vertices_003
#print axioms geometryVertices_003_shape
#print axioms decode_geometry_Vertices_004
#print axioms geometryVertices_004_shape
#print axioms decode_geometry_Vertices_005
#print axioms geometryVertices_005_shape
#print axioms decode_geometry_Vertices_006
#print axioms geometryVertices_006_shape
#print axioms decode_geometry_Vertices_007
#print axioms geometryVertices_007_shape
#print axioms decode_geometry_Vertices_008
#print axioms geometryVertices_008_shape
#print axioms decode_geometry_Vertices_009
#print axioms geometryVertices_009_shape
#print axioms decode_geometry_Vertices_010
#print axioms geometryVertices_010_shape
#print axioms decode_geometry_Vertices_011
#print axioms geometryVertices_011_shape
#print axioms decode_geometry_Vertices_012
#print axioms geometryVertices_012_shape
#print axioms decode_geometry_Vertices_013
#print axioms geometryVertices_013_shape
#print axioms decode_geometry_Vertices_014
#print axioms geometryVertices_014_shape
#print axioms decode_geometry_Vertices_015
#print axioms geometryVertices_015_shape
#print axioms geometry_Vertices_block_000_push_eq
#print axioms geometry_Vertices_block_000_reverse
#print axioms decode_geometry_Vertices_block_000
#print axioms geometry_Vertices_block_000_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
