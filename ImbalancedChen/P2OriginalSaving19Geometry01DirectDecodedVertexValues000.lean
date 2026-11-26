import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesValue

/-! Original vertex_values typed block 0, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson000 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped000 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((9515653 : ℚ) / (72000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484379 : ℚ) / (72000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_000_before_decode"
  err.flush

theorem decode_geometry_VertexValues_000 :
    decodeVertexValues geometryVertexValuesJson000 = .ok geometryVertexValuesTyped000 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_000_decoded"
  err.flush

noncomputable def geometryVertexValuesJson001 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped001 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((3171887 : ℚ) / (24000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((276043 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_001_before_decode"
  err.flush

theorem decode_geometry_VertexValues_001 :
    decodeVertexValues geometryVertexValuesJson001 = .ok geometryVertexValuesTyped001 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_001_decoded"
  err.flush

noncomputable def geometryVertexValuesJson002 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped002 : VertexValues :=
  { gap := ((515533 : ℚ) / (98000000 : ℚ)),
    factors := #[((1021879 : ℚ) / (11200000 : ℚ)), ((37827897 : ℚ) / (392000000 : ℚ)), ((52953073 : ℚ) / (392000000 : ℚ)), ((22234411 : ℚ) / (196000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((19484379 : ℚ) / (392000000 : ℚ)), ((2796863 : ℚ) / (78400000 : ℚ)), ((2796863 : ℚ) / (78400000 : ℚ)), ((2796863 : ℚ) / (78400000 : ℚ)), ((12609299 : ℚ) / (392000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_002_before_decode"
  err.flush

theorem decode_geometry_VertexValues_002 :
    decodeVertexValues geometryVertexValuesJson002 = .ok geometryVertexValuesTyped002 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_002_decoded"
  err.flush

noncomputable def geometryVertexValuesJson003 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped003 : VertexValues :=
  { gap := ((171843 : ℚ) / (34000000 : ℚ)),
    factors := #[((12703177 : ℚ) / (136000000 : ℚ)), ((13390549 : ℚ) / (136000000 : ℚ)), ((55296823 : ℚ) / (408000000 : ℚ)), ((7671887 : ℚ) / (68000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((20265629 : ℚ) / (408000000 : ℚ)), ((984371 : ℚ) / (27200000 : ℚ)), ((984371 : ℚ) / (27200000 : ℚ)), ((13390549 : ℚ) / (408000000 : ℚ)), ((13390549 : ℚ) / (408000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_003_before_decode"
  err.flush

theorem decode_geometry_VertexValues_003 :
    decodeVertexValues geometryVertexValuesJson003 = .ok geometryVertexValuesTyped003 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_003_decoded"
  err.flush

noncomputable def geometryVertexValuesJson004 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped004 : VertexValues :=
  { gap := ((442627 : ℚ) / (88000000 : ℚ)),
    factors := #[((7744841 : ℚ) / (88000000 : ℚ)), ((2046867 : ℚ) / (22000000 : ℚ)), ((4536449 : ℚ) / (33000000 : ℚ)), ((15380207 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (66000000 : ℚ)), ((6307309 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (132000000 : ℚ)), ((4536449 : ℚ) / (132000000 : ℚ)), ((682289 : ℚ) / (22000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_004_before_decode"
  err.flush

theorem decode_geometry_VertexValues_004 :
    decodeVertexValues geometryVertexValuesJson004 = .ok geometryVertexValuesTyped004 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_004_decoded"
  err.flush

noncomputable def geometryVertexValuesJson005 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped005 : VertexValues :=
  { gap := ((306431 : ℚ) / (64000000 : ℚ)),
    factors := #[((5722393 : ℚ) / (64000000 : ℚ)), ((753603 : ℚ) / (8000000 : ℚ)), ((1106969 : ℚ) / (8000000 : ℚ)), ((3729567 : ℚ) / (32000000 : ℚ)), ((1106969 : ℚ) / (16000000 : ℚ)), ((1515629 : ℚ) / (32000000 : ℚ)), ((1106969 : ℚ) / (32000000 : ℚ)), ((1106969 : ℚ) / (32000000 : ℚ)), ((251201 : ℚ) / (8000000 : ℚ)), ((251201 : ℚ) / (8000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_005_before_decode"
  err.flush

theorem decode_geometry_VertexValues_005 :
    decodeVertexValues geometryVertexValuesJson005 = .ok geometryVertexValuesTyped005 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_005_decoded"
  err.flush

noncomputable def geometryVertexValuesJson006 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped006 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((12515721 : ℚ) / (140000000 : ℚ)), ((12515721 : ℚ) / (140000000 : ℚ)), ((19390521 : ℚ) / (140000000 : ℚ)), ((7609447 : ℚ) / (70000000 : ℚ)), ((8297011 : ℚ) / (140000000 : ℚ)), ((6921883 : ℚ) / (140000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((4171907 : ℚ) / (140000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_006_before_decode"
  err.flush

theorem decode_geometry_VertexValues_006 :
    decodeVertexValues geometryVertexValuesJson006 = .ok geometryVertexValuesTyped006 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_006_decoded"
  err.flush

noncomputable def geometryVertexValuesJson007 : SourceJson :=
  (VertexValuesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped007 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((328133 : ℚ) / (4000000 : ℚ)), ((328133 : ℚ) / (4000000 : ℚ)), ((5015593 : ℚ) / (36000000 : ℚ)), ((2015633 : ℚ) / (18000000 : ℚ)), ((2015681 : ℚ) / (36000000 : ℚ)), ((403117 : ℚ) / (7200000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((328133 : ℚ) / (12000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_007_before_decode"
  err.flush

theorem decode_geometry_VertexValues_007 :
    decodeVertexValues geometryVertexValuesJson007 = .ok geometryVertexValuesTyped007 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_007_decoded"
  err.flush

noncomputable def geometryVertexValuesJsonBlock000 : List SourceJson := [geometryVertexValuesJson000, geometryVertexValuesJson001, geometryVertexValuesJson002, geometryVertexValuesJson003, geometryVertexValuesJson004, geometryVertexValuesJson005, geometryVertexValuesJson006, geometryVertexValuesJson007]
noncomputable def geometryVertexValuesTypedBlock000 : List (VertexValues) := [geometryVertexValuesTyped000, geometryVertexValuesTyped001, geometryVertexValuesTyped002, geometryVertexValuesTyped003, geometryVertexValuesTyped004, geometryVertexValuesTyped005, geometryVertexValuesTyped006, geometryVertexValuesTyped007]
noncomputable def geometryVertexValuesTypedThroughBlock000 : List (VertexValues) := geometryVertexValuesTypedBlock000

theorem geometry_VertexValues_block_000_push_eq (acc : List SourceJson) :
    VertexValuesBlock000.blockPush acc = [geometryVertexValuesJson007, geometryVertexValuesJson006, geometryVertexValuesJson005, geometryVertexValuesJson004, geometryVertexValuesJson003, geometryVertexValuesJson002, geometryVertexValuesJson001, geometryVertexValuesJson000] ++ acc := by rfl

theorem geometry_VertexValues_block_000_reverse (acc : List SourceJson) :
    (VertexValuesBlock000.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock000 := by
  rw [geometry_VertexValues_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_000 :
    geometryVertexValuesJsonBlock000.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock000 := by
  simp only [geometryVertexValuesJsonBlock000, geometryVertexValuesTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_000, decode_geometry_VertexValues_001, decode_geometry_VertexValues_002, decode_geometry_VertexValues_003, decode_geometry_VertexValues_004, decode_geometry_VertexValues_005, decode_geometry_VertexValues_006, decode_geometry_VertexValues_007]
  rfl

theorem decode_geometry_VertexValues_through_block_000 :
    VertexValuesValue.arrayAcc001.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock000 := by
  change (VertexValuesBlock000.blockPush VertexValuesValue.arrayAcc000).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_000_reverse]
  exact decode_geometry_VertexValues_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_block_000_complete"
  err.flush

#print axioms decode_geometry_VertexValues_000
#print axioms decode_geometry_VertexValues_001
#print axioms decode_geometry_VertexValues_002
#print axioms decode_geometry_VertexValues_003
#print axioms decode_geometry_VertexValues_004
#print axioms decode_geometry_VertexValues_005
#print axioms decode_geometry_VertexValues_006
#print axioms decode_geometry_VertexValues_007
#print axioms geometry_VertexValues_block_000_push_eq
#print axioms geometry_VertexValues_block_000_reverse
#print axioms decode_geometry_VertexValues_block_000
#print axioms decode_geometry_VertexValues_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
