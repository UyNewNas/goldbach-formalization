import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableVertexValuesBlock000

/-! Local original vertex_values decoding, indices 0 through 7.
Only the matching parser leaf is imported. Literal finite shape facts do not
claim a completed geometry or identify geometric meanings. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson000 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped000 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((164063 : ℚ) / (1750000 : ℚ)), ((164063 : ℚ) / (1750000 : ℚ)), ((634379 : ℚ) / (5600000 : ℚ)), ((1378169 : ℚ) / (16800000 : ℚ)), ((6890621 : ℚ) / (84000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((328133 : ℚ) / (10500000 : ℚ)), ((328133 : ℚ) / (10500000 : ℚ)), ((164063 : ℚ) / (5250000 : ℚ))] }

theorem decode_geometry_VertexValues_000 : decodeVertexValues geometryVertexValuesJson000 = .ok geometryVertexValuesTyped000 := by decide +kernel

theorem geometryVertexValues_000_shape : geometryVertexValuesTyped000.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson001 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped001 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((10254 : ℚ) / (109375 : ℚ)), ((10254 : ℚ) / (109375 : ℚ)), ((9515693 : ℚ) / (84000000 : ℚ)), ((6890837 : ℚ) / (84000000 : ℚ)), ((2296871 : ℚ) / (28000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((65627 : ℚ) / (2100000 : ℚ)), ((3418 : ℚ) / (109375 : ℚ)), ((3418 : ℚ) / (109375 : ℚ))] }

theorem decode_geometry_VertexValues_001 : decodeVertexValues geometryVertexValuesJson001 = .ok geometryVertexValuesTyped001 := by decide +kernel

theorem geometryVertexValues_001_shape : geometryVertexValuesTyped001.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson002 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped002 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((3309379 : ℚ) / (28800000 : ℚ)), ((2315717 : ℚ) / (28800000 : ℚ)), ((11578201 : ℚ) / (144000000 : ℚ)), ((11577817 : ℚ) / (144000000 : ℚ)), ((2484539 : ℚ) / (72000000 : ℚ)), ((2484347 : ℚ) / (72000000 : ℚ)), ((2484347 : ℚ) / (72000000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))] }

theorem decode_geometry_VertexValues_002 : decodeVertexValues geometryVertexValuesJson002 = .ok geometryVertexValuesTyped002 := by decide +kernel

theorem geometryVertexValues_002_shape : geometryVertexValuesTyped002.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson003 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped003 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((16546903 : ℚ) / (144000000 : ℚ)), ((11578577 : ℚ) / (144000000 : ℚ)), ((11578193 : ℚ) / (144000000 : ℚ)), ((11577809 : ℚ) / (144000000 : ℚ)), ((2484547 : ℚ) / (72000000 : ℚ)), ((496871 : ℚ) / (14400000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))] }

theorem decode_geometry_VertexValues_003 : decodeVertexValues geometryVertexValuesJson003 = .ok geometryVertexValuesTyped003 := by decide +kernel

theorem geometryVertexValues_003_shape : geometryVertexValuesTyped003.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson004 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped004 : VertexValues :=
  { gap := ((328009 : ℚ) / (128000000 : ℚ)),
    factors := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((7390621 : ℚ) / (64000000 : ℚ)), ((2828137 : ℚ) / (32000000 : ℚ)), ((2609379 : ℚ) / (32000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((2609379 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((515621 : ℚ) / (16000000 : ℚ))] }

theorem decode_geometry_VertexValues_004 : decodeVertexValues geometryVertexValuesJson004 = .ok geometryVertexValuesTyped004 := by decide +kernel

theorem geometryVertexValues_004_shape : geometryVertexValuesTyped004.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson005 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped005 : VertexValues :=
  { gap := ((328001 : ℚ) / (136000000 : ℚ)),
    factors := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((7859371 : ℚ) / (68000000 : ℚ)), ((2984387 : ℚ) / (34000000 : ℚ)), ((2765629 : ℚ) / (34000000 : ℚ)), ((2546871 : ℚ) / (34000000 : ℚ)), ((2765629 : ℚ) / (68000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))] }

theorem decode_geometry_VertexValues_005 : decodeVertexValues geometryVertexValuesJson005 = .ok geometryVertexValuesTyped005 := by decide +kernel

theorem geometryVertexValues_005_shape : geometryVertexValuesTyped005.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson006 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped006 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2531241 : ℚ) / (26500000 : ℚ)), ((2531241 : ℚ) / (26500000 : ℚ)), ((3078117 : ℚ) / (26500000 : ℚ)), ((2234423 : ℚ) / (26500000 : ℚ)), ((265627 : ℚ) / (3312500 : ℚ)), ((2015609 : ℚ) / (26500000 : ℚ)), ((265627 : ℚ) / (6625000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((843747 : ℚ) / (26500000 : ℚ))] }

theorem decode_geometry_VertexValues_006 : decodeVertexValues geometryVertexValuesJson006 = .ok geometryVertexValuesTyped006 := by decide +kernel

theorem geometryVertexValues_006_shape : geometryVertexValuesTyped006.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJson007 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped007 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2999973 : ℚ) / (30500000 : ℚ)), ((2999973 : ℚ) / (30500000 : ℚ)), ((709373 : ℚ) / (6100000 : ℚ)), ((509387 : ℚ) / (6100000 : ℚ)), ((30469 : ℚ) / (381250 : ℚ)), ((465621 : ℚ) / (6100000 : ℚ)), ((30469 : ℚ) / (762500 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))] }

theorem decode_geometry_VertexValues_007 : decodeVertexValues geometryVertexValuesJson007 = .ok geometryVertexValuesTyped007 := by decide +kernel

theorem geometryVertexValues_007_shape : geometryVertexValuesTyped007.factors.size = 10 := by decide +kernel

noncomputable def geometryVertexValuesJsonBlock000 : List SourceJson := [geometryVertexValuesJson000, geometryVertexValuesJson001, geometryVertexValuesJson002, geometryVertexValuesJson003, geometryVertexValuesJson004, geometryVertexValuesJson005, geometryVertexValuesJson006, geometryVertexValuesJson007]
noncomputable def geometryVertexValuesTypedBlock000 : List (VertexValues) := [geometryVertexValuesTyped000, geometryVertexValuesTyped001, geometryVertexValuesTyped002, geometryVertexValuesTyped003, geometryVertexValuesTyped004, geometryVertexValuesTyped005, geometryVertexValuesTyped006, geometryVertexValuesTyped007]

theorem geometry_VertexValues_block_000_push_eq (acc : List SourceJson) :
    VertexValuesBlock000.blockPush acc = [geometryVertexValuesJson007, geometryVertexValuesJson006, geometryVertexValuesJson005, geometryVertexValuesJson004, geometryVertexValuesJson003, geometryVertexValuesJson002, geometryVertexValuesJson001, geometryVertexValuesJson000] ++ acc := by rfl

theorem geometry_VertexValues_block_000_reverse (acc : List SourceJson) :
    (VertexValuesBlock000.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock000 := by
  rw [geometry_VertexValues_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_000 : geometryVertexValuesJsonBlock000.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock000 := by
  simp only [geometryVertexValuesJsonBlock000, geometryVertexValuesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_000, decode_geometry_VertexValues_001, decode_geometry_VertexValues_002, decode_geometry_VertexValues_003, decode_geometry_VertexValues_004, decode_geometry_VertexValues_005, decode_geometry_VertexValues_006, decode_geometry_VertexValues_007]
  rfl

theorem geometry_VertexValues_block_000_length : geometryVertexValuesTypedBlock000.length = 8 := by rfl

#print axioms decode_geometry_VertexValues_000
#print axioms geometryVertexValues_000_shape
#print axioms decode_geometry_VertexValues_001
#print axioms geometryVertexValues_001_shape
#print axioms decode_geometry_VertexValues_002
#print axioms geometryVertexValues_002_shape
#print axioms decode_geometry_VertexValues_003
#print axioms geometryVertexValues_003_shape
#print axioms decode_geometry_VertexValues_004
#print axioms geometryVertexValues_004_shape
#print axioms decode_geometry_VertexValues_005
#print axioms geometryVertexValues_005_shape
#print axioms decode_geometry_VertexValues_006
#print axioms geometryVertexValues_006_shape
#print axioms decode_geometry_VertexValues_007
#print axioms geometryVertexValues_007_shape
#print axioms geometry_VertexValues_block_000_push_eq
#print axioms geometry_VertexValues_block_000_reverse
#print axioms decode_geometry_VertexValues_block_000
#print axioms geometry_VertexValues_block_000_length
end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
