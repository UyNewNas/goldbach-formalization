import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertexValues000

/-! Original vertex_values typed block 1, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson008 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped008 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((4953127 : ℚ) / (52000000 : ℚ)), ((4953127 : ℚ) / (52000000 : ℚ)), ((334373 : ℚ) / (2400000 : ℚ)), ((559381 : ℚ) / (5200000 : ℚ)), ((1815659 : ℚ) / (31200000 : ℚ)), ((1540627 : ℚ) / (31200000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((4953127 : ℚ) / (156000000 : ℚ)), ((4953127 : ℚ) / (156000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_008_before_decode"
  err.flush

theorem decode_geometry_VertexValues_008 :
    decodeVertexValues geometryVertexValuesJson008 = .ok geometryVertexValuesTyped008 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_008_decoded"
  err.flush

noncomputable def geometryVertexValuesJson009 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped009 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1021879 : ℚ) / (11200000 : ℚ)), ((1021879 : ℚ) / (11200000 : ℚ)), ((1571863 : ℚ) / (11200000 : ℚ)), ((9234443 : ℚ) / (84000000 : ℚ)), ((9234667 : ℚ) / (168000000 : ℚ)), ((3078073 : ℚ) / (56000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((1703169 : ℚ) / (56000000 : ℚ)), ((1703169 : ℚ) / (56000000 : ℚ)), ((1021879 : ℚ) / (33600000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_009_before_decode"
  err.flush

theorem decode_geometry_VertexValues_009 :
    decodeVertexValues geometryVertexValuesJson009 = .ok geometryVertexValuesTyped009 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_009_decoded"
  err.flush

noncomputable def geometryVertexValuesJson010 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped010 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((729917 : ℚ) / (8000000 : ℚ)), ((729917 : ℚ) / (8000000 : ℚ)), ((3368279 : ℚ) / (24000000 : ℚ)), ((87947 : ℚ) / (800000 : ℚ)), ((1319237 : ℚ) / (24000000 : ℚ)), ((1319173 : ℚ) / (24000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_010_before_decode"
  err.flush

theorem decode_geometry_VertexValues_010 :
    decodeVertexValues geometryVertexValuesJson010 = .ok geometryVertexValuesTyped010 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_010_decoded"
  err.flush

noncomputable def geometryVertexValuesJson011 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped011 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((729917 : ℚ) / (8000000 : ℚ)), ((729917 : ℚ) / (8000000 : ℚ)), ((3368279 : ℚ) / (24000000 : ℚ)), ((87947 : ℚ) / (800000 : ℚ)), ((1319237 : ℚ) / (24000000 : ℚ)), ((1319173 : ℚ) / (24000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((243311 : ℚ) / (8000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ)), ((729917 : ℚ) / (24000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_011_before_decode"
  err.flush

theorem decode_geometry_VertexValues_011 :
    decodeVertexValues geometryVertexValuesJson011 = .ok geometryVertexValuesTyped011 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_011_decoded"
  err.flush

noncomputable def geometryVertexValuesJson012 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped012 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((23859187 : ℚ) / (168000000 : ℚ)), ((18890749 : ℚ) / (168000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((8952977 : ℚ) / (168000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((2484443 : ℚ) / (84000000 : ℚ)), ((828129 : ℚ) / (28000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_012_before_decode"
  err.flush

theorem decode_geometry_VertexValues_012 :
    decodeVertexValues geometryVertexValuesJson012 = .ok geometryVertexValuesTyped012 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_012_decoded"
  err.flush

noncomputable def geometryVertexValuesJson013 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped013 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((496879 : ℚ) / (5600000 : ℚ)), ((496879 : ℚ) / (5600000 : ℚ)), ((23859211 : ℚ) / (168000000 : ℚ)), ((6296919 : ℚ) / (56000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((8952953 : ℚ) / (168000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((2484451 : ℚ) / (84000000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ)), ((496879 : ℚ) / (16800000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_013_before_decode"
  err.flush

theorem decode_geometry_VertexValues_013 :
    decodeVertexValues geometryVertexValuesJson013 = .ok geometryVertexValuesTyped013 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_013_decoded"
  err.flush

noncomputable def geometryVertexValuesJson014 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped014 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((749957 : ℚ) / (10500000 : ℚ)), ((749957 : ℚ) / (10500000 : ℚ)), ((125001 : ℚ) / (875000 : ℚ)), ((2203049 : ℚ) / (21000000 : ℚ)), ((440621 : ℚ) / (8400000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((3796943 : ℚ) / (84000000 : ℚ)), ((3796943 : ℚ) / (84000000 : ℚ)), ((3796943 : ℚ) / (84000000 : ℚ)), ((797017 : ℚ) / (21000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_014_before_decode"
  err.flush

theorem decode_geometry_VertexValues_014 :
    decodeVertexValues geometryVertexValuesJson014 = .ok geometryVertexValuesTyped014 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_014_decoded"
  err.flush

noncomputable def geometryVertexValuesJson015 : SourceJson :=
  (VertexValuesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped015 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484307 : ℚ) / (36000000 : ℚ)), ((2484307 : ℚ) / (36000000 : ℚ)), ((15515669 : ℚ) / (108000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((5578153 : ℚ) / (108000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_015_before_decode"
  err.flush

theorem decode_geometry_VertexValues_015 :
    decodeVertexValues geometryVertexValuesJson015 = .ok geometryVertexValuesTyped015 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_015_decoded"
  err.flush

noncomputable def geometryVertexValuesJsonBlock001 : List SourceJson := [geometryVertexValuesJson008, geometryVertexValuesJson009, geometryVertexValuesJson010, geometryVertexValuesJson011, geometryVertexValuesJson012, geometryVertexValuesJson013, geometryVertexValuesJson014, geometryVertexValuesJson015]
noncomputable def geometryVertexValuesTypedBlock001 : List (VertexValues) := [geometryVertexValuesTyped008, geometryVertexValuesTyped009, geometryVertexValuesTyped010, geometryVertexValuesTyped011, geometryVertexValuesTyped012, geometryVertexValuesTyped013, geometryVertexValuesTyped014, geometryVertexValuesTyped015]
noncomputable def geometryVertexValuesTypedThroughBlock001 : List (VertexValues) := geometryVertexValuesTypedThroughBlock000 ++ geometryVertexValuesTypedBlock001

theorem geometry_VertexValues_block_001_push_eq (acc : List SourceJson) :
    VertexValuesBlock001.blockPush acc = [geometryVertexValuesJson015, geometryVertexValuesJson014, geometryVertexValuesJson013, geometryVertexValuesJson012, geometryVertexValuesJson011, geometryVertexValuesJson010, geometryVertexValuesJson009, geometryVertexValuesJson008] ++ acc := by rfl

theorem geometry_VertexValues_block_001_reverse (acc : List SourceJson) :
    (VertexValuesBlock001.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock001 := by
  rw [geometry_VertexValues_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_001 :
    geometryVertexValuesJsonBlock001.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock001 := by
  simp only [geometryVertexValuesJsonBlock001, geometryVertexValuesTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_008, decode_geometry_VertexValues_009, decode_geometry_VertexValues_010, decode_geometry_VertexValues_011, decode_geometry_VertexValues_012, decode_geometry_VertexValues_013, decode_geometry_VertexValues_014, decode_geometry_VertexValues_015]
  rfl

theorem decode_geometry_VertexValues_through_block_001 :
    VertexValuesValue.arrayAcc002.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock001 := by
  change (VertexValuesBlock001.blockPush VertexValuesValue.arrayAcc001).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_001_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_000, decode_geometry_VertexValues_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_block_001_complete"
  err.flush

#print axioms decode_geometry_VertexValues_008
#print axioms decode_geometry_VertexValues_009
#print axioms decode_geometry_VertexValues_010
#print axioms decode_geometry_VertexValues_011
#print axioms decode_geometry_VertexValues_012
#print axioms decode_geometry_VertexValues_013
#print axioms decode_geometry_VertexValues_014
#print axioms decode_geometry_VertexValues_015
#print axioms geometry_VertexValues_block_001_push_eq
#print axioms geometry_VertexValues_block_001_reverse
#print axioms decode_geometry_VertexValues_block_001
#print axioms decode_geometry_VertexValues_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
