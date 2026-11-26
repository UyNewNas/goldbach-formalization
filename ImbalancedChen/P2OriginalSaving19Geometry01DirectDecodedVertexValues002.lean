import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectVertexValuesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedVertexValues001

/-! Original vertex_values typed block 2, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryVertexValuesJson016 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped016 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((2484283 : ℚ) / (36000000 : ℚ)), ((2484283 : ℚ) / (36000000 : ℚ)), ((15515717 : ℚ) / (108000000 : ℚ)), ((390637 : ℚ) / (4000000 : ℚ)), ((1115621 : ℚ) / (21600000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2484403 : ℚ) / (54000000 : ℚ)), ((2484403 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_016_before_decode"
  err.flush

theorem decode_geometry_VertexValues_016 :
    decodeVertexValues geometryVertexValuesJson016 = .ok geometryVertexValuesTyped016 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_016_decoded"
  err.flush

noncomputable def geometryVertexValuesJson017 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped017 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((4125087 : ℚ) / (50500000 : ℚ)), ((4125087 : ℚ) / (50500000 : ℚ)), ((5453069 : ℚ) / (37875000 : ℚ)), ((4421873 : ℚ) / (37875000 : ℚ)), ((5453069 : ℚ) / (75750000 : ℚ)), ((3390677 : ℚ) / (75750000 : ℚ)), ((5453069 : ℚ) / (151500000 : ℚ)), ((5453069 : ℚ) / (151500000 : ℚ)), ((5453069 : ℚ) / (151500000 : ℚ)), ((1375029 : ℚ) / (50500000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_017_before_decode"
  err.flush

theorem decode_geometry_VertexValues_017 :
    decodeVertexValues geometryVertexValuesJson017 = .ok geometryVertexValuesTyped017 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_017_decoded"
  err.flush

noncomputable def geometryVertexValuesJson018 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped018 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((9609097 : ℚ) / (139000000 : ℚ)), ((9609097 : ℚ) / (139000000 : ℚ)), ((641 : ℚ) / (4448 : ℚ)), ((449 : ℚ) / (4448 : ℚ)), ((231 : ℚ) / (4448 : ℚ)), ((109 : ℚ) / (2224 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((3000139 : ℚ) / (69500000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_018_before_decode"
  err.flush

theorem decode_geometry_VertexValues_018 :
    decodeVertexValues geometryVertexValuesJson018 = .ok geometryVertexValuesTyped018 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_018_decoded"
  err.flush

noncomputable def geometryVertexValuesJson019 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped019 : VertexValues :=
  { gap := ((608819 : ℚ) / (556000000 : ℚ)),
    factors := #[((1191 : ℚ) / (17792 : ℚ)), ((37827569 : ℚ) / (556000000 : ℚ)), ((641 : ℚ) / (4448 : ℚ)), ((449 : ℚ) / (4448 : ℚ)), ((231 : ℚ) / (4448 : ℚ)), ((109 : ℚ) / (2224 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_019_before_decode"
  err.flush

theorem decode_geometry_VertexValues_019 :
    decodeVertexValues geometryVertexValuesJson019 = .ok geometryVertexValuesTyped019 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_019_decoded"
  err.flush

noncomputable def geometryVertexValuesJson020 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped020 : VertexValues :=
  { gap := ((608723 : ℚ) / (652000000 : ℚ)),
    factors := #[((695 : ℚ) / (10432 : ℚ)), ((44046223 : ℚ) / (652000000 : ℚ)), ((1507 : ℚ) / (10432 : ℚ)), ((131 : ℚ) / (1304 : ℚ)), ((537 : ℚ) / (10432 : ℚ)), ((511 : ℚ) / (10432 : ℚ)), ((485 : ℚ) / (10432 : ℚ)), ((485 : ℚ) / (10432 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_020_before_decode"
  err.flush

theorem decode_geometry_VertexValues_020 :
    decodeVertexValues geometryVertexValuesJson020 = .ok geometryVertexValuesTyped020 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_020_decoded"
  err.flush

noncomputable def geometryVertexValuesJson021 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped021 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((15827941 : ℚ) / (235000000 : ℚ)), ((15827941 : ℚ) / (235000000 : ℚ)), ((17046797 : ℚ) / (117500000 : ℚ)), ((11703233 : ℚ) / (117500000 : ℚ)), ((5953227 : ℚ) / (117500000 : ℚ)), ((2875003 : ℚ) / (58750000 : ℚ)), ((1109357 : ℚ) / (23500000 : ℚ)), ((1109357 : ℚ) / (23500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_021_before_decode"
  err.flush

theorem decode_geometry_VertexValues_021 :
    decodeVertexValues geometryVertexValuesJson021 = .ok geometryVertexValuesTyped021 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_021_decoded"
  err.flush

noncomputable def geometryVertexValuesJson022 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped022 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((1021871 : ℚ) / (15200000 : ℚ)), ((1021871 : ℚ) / (15200000 : ℚ)), ((5515589 : ℚ) / (38000000 : ℚ)), ((2859391 : ℚ) / (28500000 : ℚ)), ((2859467 : ℚ) / (57000000 : ℚ)), ((190621 : ℚ) / (3800000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((1703169 : ℚ) / (38000000 : ℚ)), ((1703169 : ℚ) / (38000000 : ℚ)), ((5109431 : ℚ) / (114000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_022_before_decode"
  err.flush

theorem decode_geometry_VertexValues_022 :
    decodeVertexValues geometryVertexValuesJson022 = .ok geometryVertexValuesTyped022 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_022_decoded"
  err.flush

noncomputable def geometryVertexValuesJson023 : SourceJson :=
  (VertexValuesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryVertexValuesTyped023 : VertexValues :=
  { gap := ((0 : ℚ)),
    factors := #[((15327977 : ℚ) / (228000000 : ℚ)), ((15327977 : ℚ) / (228000000 : ℚ)), ((5515597 : ℚ) / (38000000 : ℚ)), ((2859379 : ℚ) / (28500000 : ℚ)), ((571891 : ℚ) / (11400000 : ℚ)), ((953101 : ℚ) / (19000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))] }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_023_before_decode"
  err.flush

theorem decode_geometry_VertexValues_023 :
    decodeVertexValues geometryVertexValuesJson023 = .ok geometryVertexValuesTyped023 := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_023_decoded"
  err.flush

noncomputable def geometryVertexValuesJsonBlock002 : List SourceJson := [geometryVertexValuesJson016, geometryVertexValuesJson017, geometryVertexValuesJson018, geometryVertexValuesJson019, geometryVertexValuesJson020, geometryVertexValuesJson021, geometryVertexValuesJson022, geometryVertexValuesJson023]
noncomputable def geometryVertexValuesTypedBlock002 : List (VertexValues) := [geometryVertexValuesTyped016, geometryVertexValuesTyped017, geometryVertexValuesTyped018, geometryVertexValuesTyped019, geometryVertexValuesTyped020, geometryVertexValuesTyped021, geometryVertexValuesTyped022, geometryVertexValuesTyped023]
noncomputable def geometryVertexValuesTypedThroughBlock002 : List (VertexValues) := geometryVertexValuesTypedThroughBlock001 ++ geometryVertexValuesTypedBlock002

theorem geometry_VertexValues_block_002_push_eq (acc : List SourceJson) :
    VertexValuesBlock002.blockPush acc = [geometryVertexValuesJson023, geometryVertexValuesJson022, geometryVertexValuesJson021, geometryVertexValuesJson020, geometryVertexValuesJson019, geometryVertexValuesJson018, geometryVertexValuesJson017, geometryVertexValuesJson016] ++ acc := by rfl

theorem geometry_VertexValues_block_002_reverse (acc : List SourceJson) :
    (VertexValuesBlock002.blockPush acc).reverse = acc.reverse ++ geometryVertexValuesJsonBlock002 := by
  rw [geometry_VertexValues_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_VertexValues_block_002 :
    geometryVertexValuesJsonBlock002.mapM decodeVertexValues = .ok geometryVertexValuesTypedBlock002 := by
  simp only [geometryVertexValuesJsonBlock002, geometryVertexValuesTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_VertexValues_016, decode_geometry_VertexValues_017, decode_geometry_VertexValues_018, decode_geometry_VertexValues_019, decode_geometry_VertexValues_020, decode_geometry_VertexValues_021, decode_geometry_VertexValues_022, decode_geometry_VertexValues_023]
  rfl

theorem decode_geometry_VertexValues_through_block_002 :
    VertexValuesValue.arrayAcc003.reverse.mapM decodeVertexValues = .ok geometryVertexValuesTypedThroughBlock002 := by
  change (VertexValuesBlock002.blockPush VertexValuesValue.arrayAcc002).reverse.mapM decodeVertexValues = _
  rw [geometry_VertexValues_block_002_reverse]
  rw [List.mapM_append, decode_geometry_VertexValues_through_block_001, decode_geometry_VertexValues_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED VertexValues_block_002_complete"
  err.flush

#print axioms decode_geometry_VertexValues_016
#print axioms decode_geometry_VertexValues_017
#print axioms decode_geometry_VertexValues_018
#print axioms decode_geometry_VertexValues_019
#print axioms decode_geometry_VertexValues_020
#print axioms decode_geometry_VertexValues_021
#print axioms decode_geometry_VertexValues_022
#print axioms decode_geometry_VertexValues_023
#print axioms geometry_VertexValues_block_002_push_eq
#print axioms geometry_VertexValues_block_002_reverse
#print axioms decode_geometry_VertexValues_block_002
#print axioms decode_geometry_VertexValues_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
