import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableVerticesBlock000

/-! Local original vertices decoding, indices 0 through 15.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson000 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨15, by decide +kernel⟩

noncomputable def geometryVerticesTyped000 : Array ℚ :=
  #[((2390621 : ℚ) / (22000000 : ℚ)), ((10015637 : ℚ) / (110000000 : ℚ)), ((10015637 : ℚ) / (110000000 : ℚ)), ((734379 : ℚ) / (10000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((3390569 : ℚ) / (110000000 : ℚ))]

theorem decode_geometry_Vertices_000 : rationalArray geometryVerticesJson000 = .ok geometryVerticesTyped000 := by decide +kernel

theorem geometryVertices_000_shape : geometryVerticesTyped000.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson001 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨14, by decide +kernel⟩

noncomputable def geometryVerticesTyped001 : Array ℚ :=
  #[((4265621 : ℚ) / (39200000 : ℚ)), ((17828137 : ℚ) / (196000000 : ℚ)), ((17828137 : ℚ) / (196000000 : ℚ)), ((14328169 : ℚ) / (196000000 : ℚ)), ((7328233 : ℚ) / (196000000 : ℚ)), ((54687 : ℚ) / (1531250 : ℚ)), ((54687 : ℚ) / (1531250 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))]

theorem decode_geometry_Vertices_001 : rationalArray geometryVerticesJson001 = .ok geometryVerticesTyped001 := by decide +kernel

theorem geometryVertices_001_shape : geometryVerticesTyped001.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson002 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨13, by decide +kernel⟩

noncomputable def geometryVerticesTyped002 : Array ℚ :=
  #[((8015621 : ℚ) / (73600000 : ℚ)), ((33453137 : ℚ) / (368000000 : ℚ)), ((33453137 : ℚ) / (368000000 : ℚ)), ((26828169 : ℚ) / (368000000 : ℚ)), ((828121 : ℚ) / (23000000 : ℚ)), ((828121 : ℚ) / (23000000 : ℚ)), ((828121 : ℚ) / (23000000 : ℚ)), ((5796847 : ℚ) / (184000000 : ℚ))]

theorem decode_geometry_Vertices_002 : rationalArray geometryVerticesJson002 = .ok geometryVerticesTyped002 := by decide +kernel

theorem geometryVertices_002_shape : geometryVerticesTyped002.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson003 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨12, by decide +kernel⟩

noncomputable def geometryVerticesTyped003 : Array ℚ :=
  #[((75 : ℚ) / (688 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((25 : ℚ) / (344 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((5921703 : ℚ) / (172000000 : ℚ)), ((175 : ℚ) / (5504 : ℚ))]

theorem decode_geometry_Vertices_003 : rationalArray geometryVerticesJson003 = .ok geometryVerticesTyped003 := by decide +kernel

theorem geometryVertices_003_shape : geometryVerticesTyped003.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson004 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨11, by decide +kernel⟩

noncomputable def geometryVerticesTyped004 : Array ℚ :=
  #[((75 : ℚ) / (688 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((25 : ℚ) / (344 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))]

theorem decode_geometry_Vertices_004 : rationalArray geometryVerticesJson004 = .ok geometryVerticesTyped004 := by decide +kernel

theorem geometryVertices_004_shape : geometryVerticesTyped004.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson005 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryVerticesTyped005 : Array ℚ :=
  #[((75 : ℚ) / (688 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((125 : ℚ) / (1376 : ℚ)), ((25 : ℚ) / (344 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((175 : ℚ) / (5504 : ℚ))]

theorem decode_geometry_Vertices_005 : rationalArray geometryVerticesJson005 = .ok geometryVerticesTyped005 := by decide +kernel

theorem geometryVertices_005_shape : geometryVerticesTyped005.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson006 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryVerticesTyped006 : Array ℚ :=
  #[((44109411 : ℚ) / (404000000 : ℚ)), ((36921991 : ℚ) / (404000000 : ℚ)), ((18296847 : ℚ) / (202000000 : ℚ)), ((14703137 : ℚ) / (202000000 : ℚ)), ((14703137 : ℚ) / (404000000 : ℚ)), ((14703137 : ℚ) / (404000000 : ℚ)), ((14703137 : ℚ) / (404000000 : ℚ)), ((2515597 : ℚ) / (80800000 : ℚ))]

theorem decode_geometry_Vertices_006 : rationalArray geometryVerticesJson006 = .ok geometryVerticesTyped006 := by decide +kernel

theorem geometryVertices_006_shape : geometryVerticesTyped006.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson007 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryVerticesTyped007 : Array ℚ :=
  #[((4828113 : ℚ) / (44000000 : ℚ)), ((5921903 : ℚ) / (66000000 : ℚ)), ((5921903 : ℚ) / (66000000 : ℚ)), ((1609371 : ℚ) / (22000000 : ℚ)), ((1609371 : ℚ) / (44000000 : ℚ)), ((1609371 : ℚ) / (44000000 : ℚ)), ((2140609 : ℚ) / (66000000 : ℚ)), ((2140609 : ℚ) / (66000000 : ℚ))]

theorem decode_geometry_Vertices_007 : rationalArray geometryVerticesJson007 = .ok geometryVerticesTyped007 := by decide +kernel

theorem geometryVertices_007_shape : geometryVerticesTyped007.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson008 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVerticesTyped008 : Array ℚ :=
  #[((187499 : ℚ) / (1687500 : ℚ)), ((4546943 : ℚ) / (54000000 : ℚ)), ((4546943 : ℚ) / (54000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1453133 : ℚ) / (54000000 : ℚ))]

theorem decode_geometry_Vertices_008 : rationalArray geometryVerticesJson008 = .ok geometryVerticesTyped008 := by decide +kernel

theorem geometryVertices_008_shape : geometryVerticesTyped008.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson009 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVerticesTyped009 : Array ℚ :=
  #[((3453097 : ℚ) / (31000000 : ℚ)), ((11359339 : ℚ) / (124000000 : ℚ)), ((11359339 : ℚ) / (124000000 : ℚ)), ((890629 : ℚ) / (12400000 : ℚ)), ((890629 : ℚ) / (24800000 : ℚ)), ((890629 : ℚ) / (24800000 : ℚ)), ((3953121 : ℚ) / (124000000 : ℚ)), ((3953121 : ℚ) / (124000000 : ℚ))]

theorem decode_geometry_Vertices_009 : rationalArray geometryVerticesJson009 = .ok geometryVerticesTyped009 := by decide +kernel

theorem geometryVertices_009_shape : geometryVerticesTyped009.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson010 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVerticesTyped010 : Array ℚ :=
  #[((9515557 : ℚ) / (84000000 : ℚ)), ((6890749 : ℚ) / (84000000 : ℚ)), ((6890749 : ℚ) / (84000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((328129 : ℚ) / (10500000 : ℚ)), ((328129 : ℚ) / (10500000 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))]

theorem decode_geometry_Vertices_010 : rationalArray geometryVerticesJson010 = .ok geometryVerticesTyped010 := by decide +kernel

theorem geometryVertices_010_shape : geometryVerticesTyped010.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson011 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVerticesTyped011 : Array ℚ :=
  #[((634371 : ℚ) / (5600000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ))]

theorem decode_geometry_Vertices_011 : rationalArray geometryVerticesJson011 = .ok geometryVerticesTyped011 := by decide +kernel

theorem geometryVertices_011_shape : geometryVerticesTyped011.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson012 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVerticesTyped012 : Array ℚ :=
  #[((634371 : ℚ) / (5600000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((6890741 : ℚ) / (84000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((109377 : ℚ) / (3500000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ)), ((82031 : ℚ) / (2625000 : ℚ))]

theorem decode_geometry_Vertices_012 : rationalArray geometryVerticesJson012 = .ok geometryVerticesTyped012 := by decide +kernel

theorem geometryVertices_012_shape : geometryVerticesTyped012.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson013 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVerticesTyped013 : Array ℚ :=
  #[((2296857 : ℚ) / (20125000 : ℚ)), ((953141 : ℚ) / (11500000 : ℚ)), ((953141 : ℚ) / (11500000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((54687 : ℚ) / (1750000 : ℚ))]

theorem decode_geometry_Vertices_013 : rationalArray geometryVerticesJson013 = .ok geometryVerticesTyped013 := by decide +kernel

theorem geometryVertices_013_shape : geometryVerticesTyped013.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson014 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped014 : Array ℚ :=
  #[((96093 : ℚ) / (837500 : ℚ)), ((1646903 : ℚ) / (20100000 : ℚ)), ((1646903 : ℚ) / (20100000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))]

theorem decode_geometry_Vertices_014 : rationalArray geometryVerticesJson014 = .ok geometryVerticesTyped014 := by decide +kernel

theorem geometryVertices_014_shape : geometryVerticesTyped014.size = 8 := by decide +kernel

noncomputable def geometryVerticesJson015 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped015 : Array ℚ :=
  #[((3309347 : ℚ) / (28800000 : ℚ)), ((11578361 : ℚ) / (144000000 : ℚ)), ((11578361 : ℚ) / (144000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))]

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
end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
