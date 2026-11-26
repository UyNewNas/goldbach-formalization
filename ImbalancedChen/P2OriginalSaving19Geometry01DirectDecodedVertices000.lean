import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVerticesValue

/-! Original vertices typed block 0, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVerticesJson000 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨15, by decide +kernel⟩

noncomputable def geometryVerticesTyped000 : Array ℚ :=
  #[((9515653 : ℚ) / (72000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_000_before_decode"
  err.flush

theorem decode_geometry_Vertices_000 :
    rationalArray geometryVerticesJson000 = .ok geometryVerticesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_000_decoded"
  err.flush

noncomputable def geometryVerticesJson001 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨14, by decide +kernel⟩

noncomputable def geometryVerticesTyped001 : Array ℚ :=
  #[((3171887 : ℚ) / (24000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_001_before_decode"
  err.flush

theorem decode_geometry_Vertices_001 :
    rationalArray geometryVerticesJson001 = .ok geometryVerticesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_001_decoded"
  err.flush

noncomputable def geometryVerticesJson002 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨13, by decide +kernel⟩

noncomputable def geometryVerticesTyped002 : Array ℚ :=
  #[((52953073 : ℚ) / (392000000 : ℚ)), ((22234411 : ℚ) / (196000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((19484379 : ℚ) / (392000000 : ℚ)), ((2796863 : ℚ) / (78400000 : ℚ)), ((2796863 : ℚ) / (78400000 : ℚ)), ((2796863 : ℚ) / (78400000 : ℚ)), ((12609299 : ℚ) / (392000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_002_before_decode"
  err.flush

theorem decode_geometry_Vertices_002 :
    rationalArray geometryVerticesJson002 = .ok geometryVerticesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_002_decoded"
  err.flush

noncomputable def geometryVerticesJson003 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨12, by decide +kernel⟩

noncomputable def geometryVerticesTyped003 : Array ℚ :=
  #[((55296823 : ℚ) / (408000000 : ℚ)), ((7671887 : ℚ) / (68000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((20265629 : ℚ) / (408000000 : ℚ)), ((984371 : ℚ) / (27200000 : ℚ)), ((984371 : ℚ) / (27200000 : ℚ)), ((13390549 : ℚ) / (408000000 : ℚ)), ((13390549 : ℚ) / (408000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_003_before_decode"
  err.flush

theorem decode_geometry_Vertices_003 :
    rationalArray geometryVerticesJson003 = .ok geometryVerticesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_003_decoded"
  err.flush

noncomputable def geometryVerticesJson004 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨11, by decide +kernel⟩

noncomputable def geometryVerticesTyped004 : Array ℚ :=
  #[((4536449 : ℚ) / (33000000 : ℚ)), ((15380207 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (66000000 : ℚ)), ((6307309 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (132000000 : ℚ)), ((682289 : ℚ) / (22000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_004_before_decode"
  err.flush

theorem decode_geometry_Vertices_004 :
    rationalArray geometryVerticesJson004 = .ok geometryVerticesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_004_decoded"
  err.flush

noncomputable def geometryVerticesJson005 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨10, by decide +kernel⟩

noncomputable def geometryVerticesTyped005 : Array ℚ :=
  #[((1106969 : ℚ) / (8000000 : ℚ)), ((3729567 : ℚ) / (32000000 : ℚ)), ((1106969 : ℚ) / (16000000 : ℚ)), ((1515629 : ℚ) / (32000000 : ℚ)), ((1106969 : ℚ) / (32000000 : ℚ)), ((1106969 : ℚ) / (32000000 : ℚ)), ((251201 : ℚ) / (8000000 : ℚ)), ((251201 : ℚ) / (8000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_005_before_decode"
  err.flush

theorem decode_geometry_Vertices_005 :
    rationalArray geometryVerticesJson005 = .ok geometryVerticesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_005_decoded"
  err.flush

noncomputable def geometryVerticesJson006 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨9, by decide +kernel⟩

noncomputable def geometryVerticesTyped006 : Array ℚ :=
  #[((19390521 : ℚ) / (140000000 : ℚ)), ((7609447 : ℚ) / (70000000 : ℚ)), ((8297011 : ℚ) / (140000000 : ℚ)), ((6921883 : ℚ) / (140000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((4171907 : ℚ) / (140000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_006_before_decode"
  err.flush

theorem decode_geometry_Vertices_006 :
    rationalArray geometryVerticesJson006 = .ok geometryVerticesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_006_decoded"
  err.flush

noncomputable def geometryVerticesJson007 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨8, by decide +kernel⟩

noncomputable def geometryVerticesTyped007 : Array ℚ :=
  #[((5015593 : ℚ) / (36000000 : ℚ)), ((2015633 : ℚ) / (18000000 : ℚ)), ((2015681 : ℚ) / (36000000 : ℚ)), ((403117 : ℚ) / (7200000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((328133 : ℚ) / (12000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_007_before_decode"
  err.flush

theorem decode_geometry_Vertices_007 :
    rationalArray geometryVerticesJson007 = .ok geometryVerticesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_007_decoded"
  err.flush

noncomputable def geometryVerticesJson008 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVerticesTyped008 : Array ℚ :=
  #[((334373 : ℚ) / (2400000 : ℚ)), ((559381 : ℚ) / (5200000 : ℚ)), ((1815659 : ℚ) / (31200000 : ℚ)), ((1540627 : ℚ) / (31200000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((4953127 : ℚ) / (156000000 : ℚ)), ((4953127 : ℚ) / (156000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_008_before_decode"
  err.flush

theorem decode_geometry_Vertices_008 :
    rationalArray geometryVerticesJson008 = .ok geometryVerticesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_008_decoded"
  err.flush

noncomputable def geometryVerticesJson009 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVerticesTyped009 : Array ℚ :=
  #[((1571863 : ℚ) / (11200000 : ℚ)), ((9234443 : ℚ) / (84000000 : ℚ)), ((9234667 : ℚ) / (168000000 : ℚ)), ((3078073 : ℚ) / (56000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((1703169 : ℚ) / (56000000 : ℚ)), ((1703169 : ℚ) / (56000000 : ℚ)), ((1021879 : ℚ) / (33600000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_009_before_decode"
  err.flush

theorem decode_geometry_Vertices_009 :
    rationalArray geometryVerticesJson009 = .ok geometryVerticesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_009_decoded"
  err.flush

noncomputable def geometryVerticesJson010 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVerticesTyped010 : Array ℚ :=
  #[((3368279 : ℚ) / (24000000 : ℚ)), ((87947 : ℚ) / (800000 : ℚ)), ((1319237 : ℚ) / (24000000 : ℚ)), ((1319173 : ℚ) / (24000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_010_before_decode"
  err.flush

theorem decode_geometry_Vertices_010 :
    rationalArray geometryVerticesJson010 = .ok geometryVerticesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_010_decoded"
  err.flush

noncomputable def geometryVerticesJson011 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVerticesTyped011 : Array ℚ :=
  #[((3368279 : ℚ) / (24000000 : ℚ)), ((87947 : ℚ) / (800000 : ℚ)), ((1319237 : ℚ) / (24000000 : ℚ)), ((1319173 : ℚ) / (24000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((243311 : ℚ) / (8000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_011_before_decode"
  err.flush

theorem decode_geometry_Vertices_011 :
    rationalArray geometryVerticesJson011 = .ok geometryVerticesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_011_decoded"
  err.flush

noncomputable def geometryVerticesJson012 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVerticesTyped012 : Array ℚ :=
  #[((23859187 : ℚ) / (168000000 : ℚ)), ((18890749 : ℚ) / (168000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((8952977 : ℚ) / (168000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_012_before_decode"
  err.flush

theorem decode_geometry_Vertices_012 :
    rationalArray geometryVerticesJson012 = .ok geometryVerticesTyped012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_012_decoded"
  err.flush

noncomputable def geometryVerticesJson013 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVerticesTyped013 : Array ℚ :=
  #[((23859211 : ℚ) / (168000000 : ℚ)), ((6296919 : ℚ) / (56000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((8952953 : ℚ) / (168000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_013_before_decode"
  err.flush

theorem decode_geometry_Vertices_013 :
    rationalArray geometryVerticesJson013 = .ok geometryVerticesTyped013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_013_decoded"
  err.flush

noncomputable def geometryVerticesJson014 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVerticesTyped014 : Array ℚ :=
  #[((125001 : ℚ) / (875000 : ℚ)), ((2203049 : ℚ) / (21000000 : ℚ)), ((440621 : ℚ) / (8400000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((3796943 : ℚ) / (84000000 : ℚ)), ((3796943 : ℚ) / (84000000 : ℚ)), ((3796943 : ℚ) / (84000000 : ℚ)), ((797017 : ℚ) / (21000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_014_before_decode"
  err.flush

theorem decode_geometry_Vertices_014 :
    rationalArray geometryVerticesJson014 = .ok geometryVerticesTyped014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_014_decoded"
  err.flush

noncomputable def geometryVerticesJson015 : SourceJson :=
  (VerticesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVerticesTyped015 : Array ℚ :=
  #[((15515669 : ℚ) / (108000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((5578153 : ℚ) / (108000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))]

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_015_before_decode"
  err.flush

theorem decode_geometry_Vertices_015 :
    rationalArray geometryVerticesJson015 = .ok geometryVerticesTyped015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_015_decoded"
  err.flush

noncomputable def geometryVerticesJsonBlock000 : List SourceJson := [geometryVerticesJson000, geometryVerticesJson001, geometryVerticesJson002, geometryVerticesJson003, geometryVerticesJson004, geometryVerticesJson005, geometryVerticesJson006, geometryVerticesJson007, geometryVerticesJson008, geometryVerticesJson009, geometryVerticesJson010, geometryVerticesJson011, geometryVerticesJson012, geometryVerticesJson013, geometryVerticesJson014, geometryVerticesJson015]
noncomputable def geometryVerticesTypedBlock000 : List (Array ℚ) := [geometryVerticesTyped000, geometryVerticesTyped001, geometryVerticesTyped002, geometryVerticesTyped003, geometryVerticesTyped004, geometryVerticesTyped005, geometryVerticesTyped006, geometryVerticesTyped007, geometryVerticesTyped008, geometryVerticesTyped009, geometryVerticesTyped010, geometryVerticesTyped011, geometryVerticesTyped012, geometryVerticesTyped013, geometryVerticesTyped014, geometryVerticesTyped015]
noncomputable def geometryVerticesTypedThroughBlock000 : List (Array ℚ) := geometryVerticesTypedBlock000

theorem geometry_Vertices_block_000_push_eq (acc : List SourceJson) :
    VerticesBlock000.blockPush acc = [geometryVerticesJson015, geometryVerticesJson014, geometryVerticesJson013, geometryVerticesJson012, geometryVerticesJson011, geometryVerticesJson010, geometryVerticesJson009, geometryVerticesJson008, geometryVerticesJson007, geometryVerticesJson006, geometryVerticesJson005, geometryVerticesJson004, geometryVerticesJson003, geometryVerticesJson002, geometryVerticesJson001, geometryVerticesJson000] ++ acc := by rfl

theorem geometry_Vertices_block_000_reverse (acc : List SourceJson) :
    (VerticesBlock000.blockPush acc).reverse = acc.reverse ++ geometryVerticesJsonBlock000 := by
  rw [geometry_Vertices_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Vertices_block_000 :
    geometryVerticesJsonBlock000.mapM rationalArray = .ok geometryVerticesTypedBlock000 := by
  simp only [geometryVerticesJsonBlock000, geometryVerticesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Vertices_000, decode_geometry_Vertices_001, decode_geometry_Vertices_002, decode_geometry_Vertices_003, decode_geometry_Vertices_004, decode_geometry_Vertices_005, decode_geometry_Vertices_006, decode_geometry_Vertices_007, decode_geometry_Vertices_008, decode_geometry_Vertices_009, decode_geometry_Vertices_010, decode_geometry_Vertices_011, decode_geometry_Vertices_012, decode_geometry_Vertices_013, decode_geometry_Vertices_014, decode_geometry_Vertices_015]
  rfl

theorem decode_geometry_Vertices_through_block_000 :
    VerticesValue.arrayAcc001.reverse.mapM rationalArray = .ok geometryVerticesTypedThroughBlock000 := by
  change (VerticesBlock000.blockPush VerticesValue.arrayAcc000).reverse.mapM rationalArray = _
  rw [geometry_Vertices_block_000_reverse]
  exact decode_geometry_Vertices_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Vertices_block_000_complete"
  err.flush

#print axioms decode_geometry_Vertices_000
#print axioms decode_geometry_Vertices_001
#print axioms decode_geometry_Vertices_002
#print axioms decode_geometry_Vertices_003
#print axioms decode_geometry_Vertices_004
#print axioms decode_geometry_Vertices_005
#print axioms decode_geometry_Vertices_006
#print axioms decode_geometry_Vertices_007
#print axioms decode_geometry_Vertices_008
#print axioms decode_geometry_Vertices_009
#print axioms decode_geometry_Vertices_010
#print axioms decode_geometry_Vertices_011
#print axioms decode_geometry_Vertices_012
#print axioms decode_geometry_Vertices_013
#print axioms decode_geometry_Vertices_014
#print axioms decode_geometry_Vertices_015
#print axioms geometry_Vertices_block_000_push_eq
#print axioms geometry_Vertices_block_000_reverse
#print axioms decode_geometry_Vertices_block_000
#print axioms decode_geometry_Vertices_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
