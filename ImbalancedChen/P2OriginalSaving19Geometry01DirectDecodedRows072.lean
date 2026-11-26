import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows071

/-! Original simplices typed block 72, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson142 : SourceJson :=
  (SimplicesBlock072.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped142 : GeometryRow :=
  { simplexId := 142,
    vertexIds := #[39, 33, 31, 30, 24, 23, 21, 20, 16],
    physicalVolume := ((126414302657771067273910173770285216311027 : ℚ) / (147493796051331072000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((13985280263319 : ℚ) / (203782600000000 : ℚ)), ((14023331538049 : ℚ) / (203782600000000 : ℚ)), ((102053818824179 : ℚ) / (687766275000000 : ℚ)), ((115478160562109 : ℚ) / (1100426040000000 : ℚ)), ((57313387837837 : ℚ) / (1100426040000000 : ℚ)), ((25542586967873 : ℚ) / (550213020000000 : ℚ)), ((2167992971579 : ℚ) / (48264300000000 : ℚ)), ((20351103317593 : ℚ) / (458510850000000 : ℚ)), ((80368873768249 : ℚ) / (1834043400000000 : ℚ)), ((80368506959569 : ℚ) / (1834043400000000 : ℚ))],
    jensenBound := ((8838116104750980513532304751079225487206651896100495149337332751228703665302856689256439589487190625000000000000000 : ℚ) / (16916760907952634619849218463431356351057320111097898580741000566417882224687782540744155978118318715863700206062920686200274065730391 : ℚ)),
    jensenFloorQ96 := (41392539793 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_simplexId_before"
  err.flush

theorem geometryRow142_simplexId_read :
    geometryRowsJson142.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped142.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_vertexIds_before"
  err.flush

theorem geometryRow142_vertexIds_read :
    geometryRowsJson142.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped142.vertexIds := by decide +kernel

noncomputable def geometryRow142_physicalVolumeNumeratorChars : List Char := ['1', '2', '6', '4', '1', '4', '3', '0', '2', '6', '5', '7', '7', '7', '1', '0', '6', '7', '2', '7', '3', '9', '1', '0', '1', '7', '3', '7', '7', '0', '2', '8', '5', '2', '1', '6', '3', '1', '1', '0', '2', '7']
noncomputable def geometryRow142_physicalVolumeDenominatorChars : List Char := ['1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow142_physicalVolumeText : String := String.ofList (geometryRow142_physicalVolumeNumeratorChars ++ '/' :: geometryRow142_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_physicalVolume_before_field"
  err.flush

theorem geometryRow142_physicalVolume_field :
    geometryRowsJson142.getObjVal? "physical_volume" = .ok (.str geometryRow142_physicalVolumeText) := by rfl

theorem geometryRow142_physicalVolume_numerator_no_slash :
    geometryRow142_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow142_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow142_physicalVolumeNumeratorChars = some (126414302657771067273910173770285216311027 : Int) := by decide +kernel

theorem geometryRow142_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow142_physicalVolumeDenominatorChars = some (147493796051331072000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow142_physicalVolume_denominator_nonzero : (147493796051331072000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow142_physicalVolume_parse :
    parseRational geometryRow142_physicalVolumeText = .ok geometryRowsTyped142.physicalVolume :=
  original_rational_fraction_of_chars geometryRow142_physicalVolumeNumeratorChars geometryRow142_physicalVolumeDenominatorChars
    (126414302657771067273910173770285216311027 : Int) (147493796051331072000000000000000000000000000000000000000000000000000 : Int)
    geometryRow142_physicalVolume_numerator_no_slash geometryRow142_physicalVolume_numerator_parse
    geometryRow142_physicalVolume_denominator_parse geometryRow142_physicalVolume_denominator_nonzero

theorem geometryRow142_physicalVolume_read :
    rationalField geometryRowsJson142 "physical_volume" = .ok geometryRowsTyped142.physicalVolume :=
  original_rationalField_of_string geometryRowsJson142 "physical_volume" geometryRow142_physicalVolumeText
    geometryRowsTyped142.physicalVolume geometryRow142_physicalVolume_field geometryRow142_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_physicalVolume_complete"
  err.flush

noncomputable def geometryRow142_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow142_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow142_meanGapText : String := String.ofList (geometryRow142_meanGapNumeratorChars ++ '/' :: geometryRow142_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_meanGap_before_field"
  err.flush

theorem geometryRow142_meanGap_field :
    geometryRowsJson142.getObjVal? "mean_gap" = .ok (.str geometryRow142_meanGapText) := by rfl

theorem geometryRow142_meanGap_numerator_no_slash :
    geometryRow142_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow142_meanGap_numerator_parse :
    SourceJson.intChars geometryRow142_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow142_meanGap_denominator_parse :
    SourceJson.intChars geometryRow142_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow142_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow142_meanGap_parse :
    parseRational geometryRow142_meanGapText = .ok geometryRowsTyped142.meanGap :=
  original_rational_fraction_of_chars geometryRow142_meanGapNumeratorChars geometryRow142_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow142_meanGap_numerator_no_slash geometryRow142_meanGap_numerator_parse
    geometryRow142_meanGap_denominator_parse geometryRow142_meanGap_denominator_nonzero

theorem geometryRow142_meanGap_read :
    rationalField geometryRowsJson142 "mean_gap" = .ok geometryRowsTyped142.meanGap :=
  original_rationalField_of_string geometryRowsJson142 "mean_gap" geometryRow142_meanGapText
    geometryRowsTyped142.meanGap geometryRow142_meanGap_field geometryRow142_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_meanGap_complete"
  err.flush

noncomputable def geometryRow142_jensenBoundNumeratorChars : List Char := ['8', '8', '3', '8', '1', '1', '6', '1', '0', '4', '7', '5', '0', '9', '8', '0', '5', '1', '3', '5', '3', '2', '3', '0', '4', '7', '5', '1', '0', '7', '9', '2', '2', '5', '4', '8', '7', '2', '0', '6', '6', '5', '1', '8', '9', '6', '1', '0', '0', '4', '9', '5', '1', '4', '9', '3', '3', '7', '3', '3', '2', '7', '5', '1', '2', '2', '8', '7', '0', '3', '6', '6', '5', '3', '0', '2', '8', '5', '6', '6', '8', '9', '2', '5', '6', '4', '3', '9', '5', '8', '9', '4', '8', '7', '1', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow142_jensenBoundDenominatorChars : List Char := ['1', '6', '9', '1', '6', '7', '6', '0', '9', '0', '7', '9', '5', '2', '6', '3', '4', '6', '1', '9', '8', '4', '9', '2', '1', '8', '4', '6', '3', '4', '3', '1', '3', '5', '6', '3', '5', '1', '0', '5', '7', '3', '2', '0', '1', '1', '1', '0', '9', '7', '8', '9', '8', '5', '8', '0', '7', '4', '1', '0', '0', '0', '5', '6', '6', '4', '1', '7', '8', '8', '2', '2', '2', '4', '6', '8', '7', '7', '8', '2', '5', '4', '0', '7', '4', '4', '1', '5', '5', '9', '7', '8', '1', '1', '8', '3', '1', '8', '7', '1', '5', '8', '6', '3', '7', '0', '0', '2', '0', '6', '0', '6', '2', '9', '2', '0', '6', '8', '6', '2', '0', '0', '2', '7', '4', '0', '6', '5', '7', '3', '0', '3', '9', '1']
noncomputable def geometryRow142_jensenBoundText : String := String.ofList (geometryRow142_jensenBoundNumeratorChars ++ '/' :: geometryRow142_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_jensenBound_before_field"
  err.flush

theorem geometryRow142_jensenBound_field :
    geometryRowsJson142.getObjVal? "jensen_bound" = .ok (.str geometryRow142_jensenBoundText) := by rfl

theorem geometryRow142_jensenBound_numerator_no_slash :
    geometryRow142_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow142_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow142_jensenBoundNumeratorChars = some (8838116104750980513532304751079225487206651896100495149337332751228703665302856689256439589487190625000000000000000 : Int) := by decide +kernel

theorem geometryRow142_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow142_jensenBoundDenominatorChars = some (16916760907952634619849218463431356351057320111097898580741000566417882224687782540744155978118318715863700206062920686200274065730391 : Int) := by decide +kernel

theorem geometryRow142_jensenBound_denominator_nonzero : (16916760907952634619849218463431356351057320111097898580741000566417882224687782540744155978118318715863700206062920686200274065730391 : Int) ≠ 0 := by decide +kernel

theorem geometryRow142_jensenBound_parse :
    parseRational geometryRow142_jensenBoundText = .ok geometryRowsTyped142.jensenBound :=
  original_rational_fraction_of_chars geometryRow142_jensenBoundNumeratorChars geometryRow142_jensenBoundDenominatorChars
    (8838116104750980513532304751079225487206651896100495149337332751228703665302856689256439589487190625000000000000000 : Int) (16916760907952634619849218463431356351057320111097898580741000566417882224687782540744155978118318715863700206062920686200274065730391 : Int)
    geometryRow142_jensenBound_numerator_no_slash geometryRow142_jensenBound_numerator_parse
    geometryRow142_jensenBound_denominator_parse geometryRow142_jensenBound_denominator_nonzero

theorem geometryRow142_jensenBound_read :
    rationalField geometryRowsJson142 "jensen_bound" = .ok geometryRowsTyped142.jensenBound :=
  original_rationalField_of_string geometryRowsJson142 "jensen_bound" geometryRow142_jensenBoundText
    geometryRowsTyped142.jensenBound geometryRow142_jensenBound_field geometryRow142_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_factorMaxima_before"
  err.flush

theorem geometryRow142_factorMaxima_read :
    rationalArrayField geometryRowsJson142 "factor_maxima" = .ok geometryRowsTyped142.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_gapWeightedMeans_before"
  err.flush

theorem geometryRow142_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson142 "gap_weighted_means" = .ok geometryRowsTyped142.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow142_floorChars : List Char := ['4', '1', '3', '9', '2', '5', '3', '9', '7', '9', '3']
noncomputable def geometryRow142_floorText : String := String.ofList geometryRow142_floorChars

theorem geometryRow142_floor_text_read :
    geometryRowsJson142.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow142_floorText := by rfl

theorem geometryRow142_floor_chars_parse :
    SourceJson.intChars geometryRow142_floorChars = some (41392539793 : Int) := by decide +kernel

theorem geometryRow142_floor_parse :
    parseInteger geometryRow142_floorText = .ok geometryRowsTyped142.jensenFloorQ96 := by
  simp only [geometryRow142_floorText, parseInteger, String.toList_ofList, geometryRow142_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_142 :
    decodeGeometryRow geometryRowsJson142 = .ok geometryRowsTyped142 :=
  original_geometryRow_of_fields geometryRowsJson142 geometryRowsTyped142 geometryRow142_floorText
    geometryRow142_simplexId_read geometryRow142_vertexIds_read
    geometryRow142_physicalVolume_read geometryRow142_meanGap_read
    geometryRow142_factorMaxima_read geometryRow142_gapWeightedMeans_read
    geometryRow142_jensenBound_read geometryRow142_floor_text_read geometryRow142_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_142_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson143 : SourceJson :=
  (SimplicesBlock072.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped143 : GeometryRow :=
  { simplexId := 143,
    vertexIds := #[39, 33, 32, 30, 24, 23, 21, 20, 16],
    physicalVolume := ((126394369355664618522379266593140699827859 : ℚ) / (147493796051331072000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((24677291397583 : ℚ) / (366808680000000 : ℚ)), ((24745783692097 : ℚ) / (366808680000000 : ℚ)), ((9085230862339 : ℚ) / (61134780000000 : ℚ)), ((579871256844701 : ℚ) / (5502130200000000 : ℚ)), ((10981146525107 : ℚ) / (203782600000000 : ℚ)), ((7060712296157 : ℚ) / (152836950000000 : ℚ)), ((808917670207 : ℚ) / (18099112500000 : ℚ)), ((121486506397019 : ℚ) / (2751065100000000 : ℚ)), ((239866027478989 : ℚ) / (5502130200000000 : ℚ)), ((239865293861629 : ℚ) / (5502130200000000 : ℚ))],
    jensenBound := ((755539772894019913968483407871218780408102411659004459620266313912491660899593961710850312355208448437500000000000000 : ℚ) / (1410363227653368379151089996042370496717523696646602087979975739555868522941618499781892258549802257484967811338810972017309425617155603 : ℚ)),
    jensenFloorQ96 := (42442986841 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_simplexId_before"
  err.flush

theorem geometryRow143_simplexId_read :
    geometryRowsJson143.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped143.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_vertexIds_before"
  err.flush

theorem geometryRow143_vertexIds_read :
    geometryRowsJson143.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped143.vertexIds := by decide +kernel

noncomputable def geometryRow143_physicalVolumeNumeratorChars : List Char := ['1', '2', '6', '3', '9', '4', '3', '6', '9', '3', '5', '5', '6', '6', '4', '6', '1', '8', '5', '2', '2', '3', '7', '9', '2', '6', '6', '5', '9', '3', '1', '4', '0', '6', '9', '9', '8', '2', '7', '8', '5', '9']
noncomputable def geometryRow143_physicalVolumeDenominatorChars : List Char := ['1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow143_physicalVolumeText : String := String.ofList (geometryRow143_physicalVolumeNumeratorChars ++ '/' :: geometryRow143_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_physicalVolume_before_field"
  err.flush

theorem geometryRow143_physicalVolume_field :
    geometryRowsJson143.getObjVal? "physical_volume" = .ok (.str geometryRow143_physicalVolumeText) := by rfl

theorem geometryRow143_physicalVolume_numerator_no_slash :
    geometryRow143_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow143_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow143_physicalVolumeNumeratorChars = some (126394369355664618522379266593140699827859 : Int) := by decide +kernel

theorem geometryRow143_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow143_physicalVolumeDenominatorChars = some (147493796051331072000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow143_physicalVolume_denominator_nonzero : (147493796051331072000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow143_physicalVolume_parse :
    parseRational geometryRow143_physicalVolumeText = .ok geometryRowsTyped143.physicalVolume :=
  original_rational_fraction_of_chars geometryRow143_physicalVolumeNumeratorChars geometryRow143_physicalVolumeDenominatorChars
    (126394369355664618522379266593140699827859 : Int) (147493796051331072000000000000000000000000000000000000000000000000000 : Int)
    geometryRow143_physicalVolume_numerator_no_slash geometryRow143_physicalVolume_numerator_parse
    geometryRow143_physicalVolume_denominator_parse geometryRow143_physicalVolume_denominator_nonzero

theorem geometryRow143_physicalVolume_read :
    rationalField geometryRowsJson143 "physical_volume" = .ok geometryRowsTyped143.physicalVolume :=
  original_rationalField_of_string geometryRowsJson143 "physical_volume" geometryRow143_physicalVolumeText
    geometryRowsTyped143.physicalVolume geometryRow143_physicalVolume_field geometryRow143_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_physicalVolume_complete"
  err.flush

noncomputable def geometryRow143_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow143_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow143_meanGapText : String := String.ofList (geometryRow143_meanGapNumeratorChars ++ '/' :: geometryRow143_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_meanGap_before_field"
  err.flush

theorem geometryRow143_meanGap_field :
    geometryRowsJson143.getObjVal? "mean_gap" = .ok (.str geometryRow143_meanGapText) := by rfl

theorem geometryRow143_meanGap_numerator_no_slash :
    geometryRow143_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow143_meanGap_numerator_parse :
    SourceJson.intChars geometryRow143_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow143_meanGap_denominator_parse :
    SourceJson.intChars geometryRow143_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow143_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow143_meanGap_parse :
    parseRational geometryRow143_meanGapText = .ok geometryRowsTyped143.meanGap :=
  original_rational_fraction_of_chars geometryRow143_meanGapNumeratorChars geometryRow143_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow143_meanGap_numerator_no_slash geometryRow143_meanGap_numerator_parse
    geometryRow143_meanGap_denominator_parse geometryRow143_meanGap_denominator_nonzero

theorem geometryRow143_meanGap_read :
    rationalField geometryRowsJson143 "mean_gap" = .ok geometryRowsTyped143.meanGap :=
  original_rationalField_of_string geometryRowsJson143 "mean_gap" geometryRow143_meanGapText
    geometryRowsTyped143.meanGap geometryRow143_meanGap_field geometryRow143_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_meanGap_complete"
  err.flush

noncomputable def geometryRow143_jensenBoundNumeratorChars : List Char := ['7', '5', '5', '5', '3', '9', '7', '7', '2', '8', '9', '4', '0', '1', '9', '9', '1', '3', '9', '6', '8', '4', '8', '3', '4', '0', '7', '8', '7', '1', '2', '1', '8', '7', '8', '0', '4', '0', '8', '1', '0', '2', '4', '1', '1', '6', '5', '9', '0', '0', '4', '4', '5', '9', '6', '2', '0', '2', '6', '6', '3', '1', '3', '9', '1', '2', '4', '9', '1', '6', '6', '0', '8', '9', '9', '5', '9', '3', '9', '6', '1', '7', '1', '0', '8', '5', '0', '3', '1', '2', '3', '5', '5', '2', '0', '8', '4', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow143_jensenBoundDenominatorChars : List Char := ['1', '4', '1', '0', '3', '6', '3', '2', '2', '7', '6', '5', '3', '3', '6', '8', '3', '7', '9', '1', '5', '1', '0', '8', '9', '9', '9', '6', '0', '4', '2', '3', '7', '0', '4', '9', '6', '7', '1', '7', '5', '2', '3', '6', '9', '6', '6', '4', '6', '6', '0', '2', '0', '8', '7', '9', '7', '9', '9', '7', '5', '7', '3', '9', '5', '5', '5', '8', '6', '8', '5', '2', '2', '9', '4', '1', '6', '1', '8', '4', '9', '9', '7', '8', '1', '8', '9', '2', '2', '5', '8', '5', '4', '9', '8', '0', '2', '2', '5', '7', '4', '8', '4', '9', '6', '7', '8', '1', '1', '3', '3', '8', '8', '1', '0', '9', '7', '2', '0', '1', '7', '3', '0', '9', '4', '2', '5', '6', '1', '7', '1', '5', '5', '6', '0', '3']
noncomputable def geometryRow143_jensenBoundText : String := String.ofList (geometryRow143_jensenBoundNumeratorChars ++ '/' :: geometryRow143_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_jensenBound_before_field"
  err.flush

theorem geometryRow143_jensenBound_field :
    geometryRowsJson143.getObjVal? "jensen_bound" = .ok (.str geometryRow143_jensenBoundText) := by rfl

theorem geometryRow143_jensenBound_numerator_no_slash :
    geometryRow143_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow143_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow143_jensenBoundNumeratorChars = some (755539772894019913968483407871218780408102411659004459620266313912491660899593961710850312355208448437500000000000000 : Int) := by decide +kernel

theorem geometryRow143_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow143_jensenBoundDenominatorChars = some (1410363227653368379151089996042370496717523696646602087979975739555868522941618499781892258549802257484967811338810972017309425617155603 : Int) := by decide +kernel

theorem geometryRow143_jensenBound_denominator_nonzero : (1410363227653368379151089996042370496717523696646602087979975739555868522941618499781892258549802257484967811338810972017309425617155603 : Int) ≠ 0 := by decide +kernel

theorem geometryRow143_jensenBound_parse :
    parseRational geometryRow143_jensenBoundText = .ok geometryRowsTyped143.jensenBound :=
  original_rational_fraction_of_chars geometryRow143_jensenBoundNumeratorChars geometryRow143_jensenBoundDenominatorChars
    (755539772894019913968483407871218780408102411659004459620266313912491660899593961710850312355208448437500000000000000 : Int) (1410363227653368379151089996042370496717523696646602087979975739555868522941618499781892258549802257484967811338810972017309425617155603 : Int)
    geometryRow143_jensenBound_numerator_no_slash geometryRow143_jensenBound_numerator_parse
    geometryRow143_jensenBound_denominator_parse geometryRow143_jensenBound_denominator_nonzero

theorem geometryRow143_jensenBound_read :
    rationalField geometryRowsJson143 "jensen_bound" = .ok geometryRowsTyped143.jensenBound :=
  original_rationalField_of_string geometryRowsJson143 "jensen_bound" geometryRow143_jensenBoundText
    geometryRowsTyped143.jensenBound geometryRow143_jensenBound_field geometryRow143_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_factorMaxima_before"
  err.flush

theorem geometryRow143_factorMaxima_read :
    rationalArrayField geometryRowsJson143 "factor_maxima" = .ok geometryRowsTyped143.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_gapWeightedMeans_before"
  err.flush

theorem geometryRow143_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson143 "gap_weighted_means" = .ok geometryRowsTyped143.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow143_floorChars : List Char := ['4', '2', '4', '4', '2', '9', '8', '6', '8', '4', '1']
noncomputable def geometryRow143_floorText : String := String.ofList geometryRow143_floorChars

theorem geometryRow143_floor_text_read :
    geometryRowsJson143.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow143_floorText := by rfl

theorem geometryRow143_floor_chars_parse :
    SourceJson.intChars geometryRow143_floorChars = some (42442986841 : Int) := by decide +kernel

theorem geometryRow143_floor_parse :
    parseInteger geometryRow143_floorText = .ok geometryRowsTyped143.jensenFloorQ96 := by
  simp only [geometryRow143_floorText, parseInteger, String.toList_ofList, geometryRow143_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_143 :
    decodeGeometryRow geometryRowsJson143 = .ok geometryRowsTyped143 :=
  original_geometryRow_of_fields geometryRowsJson143 geometryRowsTyped143 geometryRow143_floorText
    geometryRow143_simplexId_read geometryRow143_vertexIds_read
    geometryRow143_physicalVolume_read geometryRow143_meanGap_read
    geometryRow143_factorMaxima_read geometryRow143_gapWeightedMeans_read
    geometryRow143_jensenBound_read geometryRow143_floor_text_read geometryRow143_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_143_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock072 : List SourceJson := [geometryRowsJson142, geometryRowsJson143]
noncomputable def geometryRowsTypedBlock072 : List (GeometryRow) := [geometryRowsTyped142, geometryRowsTyped143]
noncomputable def geometryRowsTypedThroughBlock072 : List (GeometryRow) := geometryRowsTypedThroughBlock071 ++ geometryRowsTypedBlock072

theorem geometry_Rows_block_072_push_eq (acc : List SourceJson) :
    SimplicesBlock072.blockPush acc = [geometryRowsJson143, geometryRowsJson142] ++ acc := by rfl

theorem geometry_Rows_block_072_reverse (acc : List SourceJson) :
    (SimplicesBlock072.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock072 := by
  rw [geometry_Rows_block_072_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_072 :
    geometryRowsJsonBlock072.mapM decodeGeometryRow = .ok geometryRowsTypedBlock072 := by
  simp only [geometryRowsJsonBlock072, geometryRowsTypedBlock072, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_142, decode_geometry_Rows_143]
  rfl

theorem decode_geometry_Rows_through_block_072 :
    SimplicesValue.arrayAcc073.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock072 := by
  change (SimplicesBlock072.blockPush SimplicesValue.arrayAcc072).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_072_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_071, decode_geometry_Rows_block_072]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_072_complete"
  err.flush

#print axioms geometryRow142_simplexId_read
#print axioms geometryRow142_vertexIds_read
#print axioms geometryRow142_physicalVolume_field
#print axioms geometryRow142_physicalVolume_numerator_no_slash
#print axioms geometryRow142_physicalVolume_numerator_parse
#print axioms geometryRow142_physicalVolume_denominator_parse
#print axioms geometryRow142_physicalVolume_denominator_nonzero
#print axioms geometryRow142_physicalVolume_parse
#print axioms geometryRow142_physicalVolume_read
#print axioms geometryRow142_meanGap_field
#print axioms geometryRow142_meanGap_numerator_no_slash
#print axioms geometryRow142_meanGap_numerator_parse
#print axioms geometryRow142_meanGap_denominator_parse
#print axioms geometryRow142_meanGap_denominator_nonzero
#print axioms geometryRow142_meanGap_parse
#print axioms geometryRow142_meanGap_read
#print axioms geometryRow142_jensenBound_field
#print axioms geometryRow142_jensenBound_numerator_no_slash
#print axioms geometryRow142_jensenBound_numerator_parse
#print axioms geometryRow142_jensenBound_denominator_parse
#print axioms geometryRow142_jensenBound_denominator_nonzero
#print axioms geometryRow142_jensenBound_parse
#print axioms geometryRow142_jensenBound_read
#print axioms geometryRow142_factorMaxima_read
#print axioms geometryRow142_gapWeightedMeans_read
#print axioms geometryRow142_floor_text_read
#print axioms geometryRow142_floor_chars_parse
#print axioms geometryRow142_floor_parse
#print axioms decode_geometry_Rows_142
#print axioms geometryRow143_simplexId_read
#print axioms geometryRow143_vertexIds_read
#print axioms geometryRow143_physicalVolume_field
#print axioms geometryRow143_physicalVolume_numerator_no_slash
#print axioms geometryRow143_physicalVolume_numerator_parse
#print axioms geometryRow143_physicalVolume_denominator_parse
#print axioms geometryRow143_physicalVolume_denominator_nonzero
#print axioms geometryRow143_physicalVolume_parse
#print axioms geometryRow143_physicalVolume_read
#print axioms geometryRow143_meanGap_field
#print axioms geometryRow143_meanGap_numerator_no_slash
#print axioms geometryRow143_meanGap_numerator_parse
#print axioms geometryRow143_meanGap_denominator_parse
#print axioms geometryRow143_meanGap_denominator_nonzero
#print axioms geometryRow143_meanGap_parse
#print axioms geometryRow143_meanGap_read
#print axioms geometryRow143_jensenBound_field
#print axioms geometryRow143_jensenBound_numerator_no_slash
#print axioms geometryRow143_jensenBound_numerator_parse
#print axioms geometryRow143_jensenBound_denominator_parse
#print axioms geometryRow143_jensenBound_denominator_nonzero
#print axioms geometryRow143_jensenBound_parse
#print axioms geometryRow143_jensenBound_read
#print axioms geometryRow143_factorMaxima_read
#print axioms geometryRow143_gapWeightedMeans_read
#print axioms geometryRow143_floor_text_read
#print axioms geometryRow143_floor_chars_parse
#print axioms geometryRow143_floor_parse
#print axioms decode_geometry_Rows_143
#print axioms geometry_Rows_block_072_push_eq
#print axioms geometry_Rows_block_072_reverse
#print axioms decode_geometry_Rows_block_072
#print axioms decode_geometry_Rows_through_block_072

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
