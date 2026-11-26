import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows057

/-! Original simplices typed block 58, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson114 : SourceJson :=
  (SimplicesBlock058.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped114 : GeometryRow :=
  { simplexId := 114,
    vertexIds := #[39, 37, 31, 24, 23, 21, 20, 16, 15],
    physicalVolume := ((103172892365246606395998981793513628822959 : ℚ) / (94396029472851886080000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((89784929442991 : ℚ) / (1222695600000000 : ℚ)), ((90013237091371 : ℚ) / (1222695600000000 : ℚ)), ((1636833750252781 : ℚ) / (11004260400000000 : ℚ)), ((584465119845197 : ℚ) / (5502130200000000 : ℚ)), ((546829219937561 : ℚ) / (11004260400000000 : ℚ)), ((506879090291543 : ℚ) / (11004260400000000 : ℚ)), ((67947566669 : ℚ) / (1544457600000 : ℚ)), ((31883366307923 : ℚ) / (733617360000000 : ℚ)), ((157345997074489 : ℚ) / (3668086800000000 : ℚ)), ((157345018918009 : ℚ) / (3668086800000000 : ℚ))],
    jensenBound := ((75783805979368347032373496633196921050951345044776293725341280417323800555793406236649126536890695744000000000000000000000 : ℚ) / (114941235131460021475935916475603227159565529343231152618745101157016680016230526482703460375535493547033134408916858753272876009114208447077 : ℚ)),
    jensenFloorQ96 := (52237229652 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_simplexId_before"
  err.flush

theorem geometryRow114_simplexId_read :
    geometryRowsJson114.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped114.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_vertexIds_before"
  err.flush

theorem geometryRow114_vertexIds_read :
    geometryRowsJson114.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped114.vertexIds := by decide +kernel

noncomputable def geometryRow114_physicalVolumeNumeratorChars : List Char := ['1', '0', '3', '1', '7', '2', '8', '9', '2', '3', '6', '5', '2', '4', '6', '6', '0', '6', '3', '9', '5', '9', '9', '8', '9', '8', '1', '7', '9', '3', '5', '1', '3', '6', '2', '8', '8', '2', '2', '9', '5', '9']
noncomputable def geometryRow114_physicalVolumeDenominatorChars : List Char := ['9', '4', '3', '9', '6', '0', '2', '9', '4', '7', '2', '8', '5', '1', '8', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow114_physicalVolumeText : String := String.ofList (geometryRow114_physicalVolumeNumeratorChars ++ '/' :: geometryRow114_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_physicalVolume_before_field"
  err.flush

theorem geometryRow114_physicalVolume_field :
    geometryRowsJson114.getObjVal? "physical_volume" = .ok (.str geometryRow114_physicalVolumeText) := by rfl

theorem geometryRow114_physicalVolume_numerator_no_slash :
    geometryRow114_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow114_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow114_physicalVolumeNumeratorChars = some (103172892365246606395998981793513628822959 : Int) := by decide +kernel

theorem geometryRow114_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow114_physicalVolumeDenominatorChars = some (94396029472851886080000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow114_physicalVolume_denominator_nonzero : (94396029472851886080000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow114_physicalVolume_parse :
    parseRational geometryRow114_physicalVolumeText = .ok geometryRowsTyped114.physicalVolume :=
  original_rational_fraction_of_chars geometryRow114_physicalVolumeNumeratorChars geometryRow114_physicalVolumeDenominatorChars
    (103172892365246606395998981793513628822959 : Int) (94396029472851886080000000000000000000000000000000000000000000000000 : Int)
    geometryRow114_physicalVolume_numerator_no_slash geometryRow114_physicalVolume_numerator_parse
    geometryRow114_physicalVolume_denominator_parse geometryRow114_physicalVolume_denominator_nonzero

theorem geometryRow114_physicalVolume_read :
    rationalField geometryRowsJson114 "physical_volume" = .ok geometryRowsTyped114.physicalVolume :=
  original_rationalField_of_string geometryRowsJson114 "physical_volume" geometryRow114_physicalVolumeText
    geometryRowsTyped114.physicalVolume geometryRow114_physicalVolume_field geometryRow114_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_physicalVolume_complete"
  err.flush

noncomputable def geometryRow114_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow114_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow114_meanGapText : String := String.ofList (geometryRow114_meanGapNumeratorChars ++ '/' :: geometryRow114_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_meanGap_before_field"
  err.flush

theorem geometryRow114_meanGap_field :
    geometryRowsJson114.getObjVal? "mean_gap" = .ok (.str geometryRow114_meanGapText) := by rfl

theorem geometryRow114_meanGap_numerator_no_slash :
    geometryRow114_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow114_meanGap_numerator_parse :
    SourceJson.intChars geometryRow114_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow114_meanGap_denominator_parse :
    SourceJson.intChars geometryRow114_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow114_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow114_meanGap_parse :
    parseRational geometryRow114_meanGapText = .ok geometryRowsTyped114.meanGap :=
  original_rational_fraction_of_chars geometryRow114_meanGapNumeratorChars geometryRow114_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow114_meanGap_numerator_no_slash geometryRow114_meanGap_numerator_parse
    geometryRow114_meanGap_denominator_parse geometryRow114_meanGap_denominator_nonzero

theorem geometryRow114_meanGap_read :
    rationalField geometryRowsJson114 "mean_gap" = .ok geometryRowsTyped114.meanGap :=
  original_rationalField_of_string geometryRowsJson114 "mean_gap" geometryRow114_meanGapText
    geometryRowsTyped114.meanGap geometryRow114_meanGap_field geometryRow114_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_meanGap_complete"
  err.flush

noncomputable def geometryRow114_jensenBoundNumeratorChars : List Char := ['7', '5', '7', '8', '3', '8', '0', '5', '9', '7', '9', '3', '6', '8', '3', '4', '7', '0', '3', '2', '3', '7', '3', '4', '9', '6', '6', '3', '3', '1', '9', '6', '9', '2', '1', '0', '5', '0', '9', '5', '1', '3', '4', '5', '0', '4', '4', '7', '7', '6', '2', '9', '3', '7', '2', '5', '3', '4', '1', '2', '8', '0', '4', '1', '7', '3', '2', '3', '8', '0', '0', '5', '5', '5', '7', '9', '3', '4', '0', '6', '2', '3', '6', '6', '4', '9', '1', '2', '6', '5', '3', '6', '8', '9', '0', '6', '9', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow114_jensenBoundDenominatorChars : List Char := ['1', '1', '4', '9', '4', '1', '2', '3', '5', '1', '3', '1', '4', '6', '0', '0', '2', '1', '4', '7', '5', '9', '3', '5', '9', '1', '6', '4', '7', '5', '6', '0', '3', '2', '2', '7', '1', '5', '9', '5', '6', '5', '5', '2', '9', '3', '4', '3', '2', '3', '1', '1', '5', '2', '6', '1', '8', '7', '4', '5', '1', '0', '1', '1', '5', '7', '0', '1', '6', '6', '8', '0', '0', '1', '6', '2', '3', '0', '5', '2', '6', '4', '8', '2', '7', '0', '3', '4', '6', '0', '3', '7', '5', '5', '3', '5', '4', '9', '3', '5', '4', '7', '0', '3', '3', '1', '3', '4', '4', '0', '8', '9', '1', '6', '8', '5', '8', '7', '5', '3', '2', '7', '2', '8', '7', '6', '0', '0', '9', '1', '1', '4', '2', '0', '8', '4', '4', '7', '0', '7', '7']
noncomputable def geometryRow114_jensenBoundText : String := String.ofList (geometryRow114_jensenBoundNumeratorChars ++ '/' :: geometryRow114_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_jensenBound_before_field"
  err.flush

theorem geometryRow114_jensenBound_field :
    geometryRowsJson114.getObjVal? "jensen_bound" = .ok (.str geometryRow114_jensenBoundText) := by rfl

theorem geometryRow114_jensenBound_numerator_no_slash :
    geometryRow114_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow114_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow114_jensenBoundNumeratorChars = some (75783805979368347032373496633196921050951345044776293725341280417323800555793406236649126536890695744000000000000000000000 : Int) := by decide +kernel

theorem geometryRow114_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow114_jensenBoundDenominatorChars = some (114941235131460021475935916475603227159565529343231152618745101157016680016230526482703460375535493547033134408916858753272876009114208447077 : Int) := by decide +kernel

theorem geometryRow114_jensenBound_denominator_nonzero : (114941235131460021475935916475603227159565529343231152618745101157016680016230526482703460375535493547033134408916858753272876009114208447077 : Int) ≠ 0 := by decide +kernel

theorem geometryRow114_jensenBound_parse :
    parseRational geometryRow114_jensenBoundText = .ok geometryRowsTyped114.jensenBound :=
  original_rational_fraction_of_chars geometryRow114_jensenBoundNumeratorChars geometryRow114_jensenBoundDenominatorChars
    (75783805979368347032373496633196921050951345044776293725341280417323800555793406236649126536890695744000000000000000000000 : Int) (114941235131460021475935916475603227159565529343231152618745101157016680016230526482703460375535493547033134408916858753272876009114208447077 : Int)
    geometryRow114_jensenBound_numerator_no_slash geometryRow114_jensenBound_numerator_parse
    geometryRow114_jensenBound_denominator_parse geometryRow114_jensenBound_denominator_nonzero

theorem geometryRow114_jensenBound_read :
    rationalField geometryRowsJson114 "jensen_bound" = .ok geometryRowsTyped114.jensenBound :=
  original_rationalField_of_string geometryRowsJson114 "jensen_bound" geometryRow114_jensenBoundText
    geometryRowsTyped114.jensenBound geometryRow114_jensenBound_field geometryRow114_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_factorMaxima_before"
  err.flush

theorem geometryRow114_factorMaxima_read :
    rationalArrayField geometryRowsJson114 "factor_maxima" = .ok geometryRowsTyped114.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_gapWeightedMeans_before"
  err.flush

theorem geometryRow114_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson114 "gap_weighted_means" = .ok geometryRowsTyped114.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow114_floorChars : List Char := ['5', '2', '2', '3', '7', '2', '2', '9', '6', '5', '2']
noncomputable def geometryRow114_floorText : String := String.ofList geometryRow114_floorChars

theorem geometryRow114_floor_text_read :
    geometryRowsJson114.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow114_floorText := by rfl

theorem geometryRow114_floor_chars_parse :
    SourceJson.intChars geometryRow114_floorChars = some (52237229652 : Int) := by decide +kernel

theorem geometryRow114_floor_parse :
    parseInteger geometryRow114_floorText = .ok geometryRowsTyped114.jensenFloorQ96 := by
  simp only [geometryRow114_floorText, parseInteger, String.toList_ofList, geometryRow114_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_114 :
    decodeGeometryRow geometryRowsJson114 = .ok geometryRowsTyped114 :=
  original_geometryRow_of_fields geometryRowsJson114 geometryRowsTyped114 geometryRow114_floorText
    geometryRow114_simplexId_read geometryRow114_vertexIds_read
    geometryRow114_physicalVolume_read geometryRow114_meanGap_read
    geometryRow114_factorMaxima_read geometryRow114_gapWeightedMeans_read
    geometryRow114_jensenBound_read geometryRow114_floor_text_read geometryRow114_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_114_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson115 : SourceJson :=
  (SimplicesBlock058.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped115 : GeometryRow :=
  { simplexId := 115,
    vertexIds := #[39, 37, 31, 24, 23, 21, 20, 19, 15],
    physicalVolume := ((1341459125152034599599939797338177236317251 : ℚ) / (1119662770920653838090240000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((91924997 : ℚ) / (407826000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((73038618884281294403137 : ℚ) / (997218141785485200000000 : ℚ)), ((73342705816164196726327 : ℚ) / (997218141785485200000000 : ℚ)), ((148357291218462241923173 : ℚ) / (997218141785485200000000 : ℚ)), ((79712538329884758191359 : ℚ) / (747913606339113900000000 : ℚ)), ((49607228847559919033593 : ℚ) / (997218141785485200000000 : ℚ)), ((45672553560897431668579 : ℚ) / (997218141785485200000000 : ℚ)), ((1385001937228378589839 : ℚ) / (31491099214278480000000 : ℚ)), ((25995547534222305887257 : ℚ) / (598330885071291120000000 : ℚ)), ((128389602050322301211333 : ℚ) / (2991654425356455600000000 : ℚ)), ((128052225235995819854423 : ℚ) / (2991654425356455600000000 : ℚ))],
    jensenBound := ((10335225098705735088838162708364133717701794538236011066483544078784385488802722132852706796132346998798484209768999342564059054746801384444586586431058875791516688853932620030280815793750000000000000000000000000 : ℚ) / (6535341043856888732699989663045856928772840093750367052644926622531888391817291878500681483890706694473973436592034829021776457067909096087943750447034084137486229470055491080652493399521966338895465175681431134019041618725319 : ℚ)),
    jensenFloorQ96 := (125294286594493 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_simplexId_before"
  err.flush

theorem geometryRow115_simplexId_read :
    geometryRowsJson115.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped115.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_vertexIds_before"
  err.flush

theorem geometryRow115_vertexIds_read :
    geometryRowsJson115.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped115.vertexIds := by decide +kernel

noncomputable def geometryRow115_physicalVolumeNumeratorChars : List Char := ['1', '3', '4', '1', '4', '5', '9', '1', '2', '5', '1', '5', '2', '0', '3', '4', '5', '9', '9', '5', '9', '9', '9', '3', '9', '7', '9', '7', '3', '3', '8', '1', '7', '7', '2', '3', '6', '3', '1', '7', '2', '5', '1']
noncomputable def geometryRow115_physicalVolumeDenominatorChars : List Char := ['1', '1', '1', '9', '6', '6', '2', '7', '7', '0', '9', '2', '0', '6', '5', '3', '8', '3', '8', '0', '9', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow115_physicalVolumeText : String := String.ofList (geometryRow115_physicalVolumeNumeratorChars ++ '/' :: geometryRow115_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_physicalVolume_before_field"
  err.flush

theorem geometryRow115_physicalVolume_field :
    geometryRowsJson115.getObjVal? "physical_volume" = .ok (.str geometryRow115_physicalVolumeText) := by rfl

theorem geometryRow115_physicalVolume_numerator_no_slash :
    geometryRow115_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow115_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow115_physicalVolumeNumeratorChars = some (1341459125152034599599939797338177236317251 : Int) := by decide +kernel

theorem geometryRow115_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow115_physicalVolumeDenominatorChars = some (1119662770920653838090240000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow115_physicalVolume_denominator_nonzero : (1119662770920653838090240000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow115_physicalVolume_parse :
    parseRational geometryRow115_physicalVolumeText = .ok geometryRowsTyped115.physicalVolume :=
  original_rational_fraction_of_chars geometryRow115_physicalVolumeNumeratorChars geometryRow115_physicalVolumeDenominatorChars
    (1341459125152034599599939797338177236317251 : Int) (1119662770920653838090240000000000000000000000000000000000000000000 : Int)
    geometryRow115_physicalVolume_numerator_no_slash geometryRow115_physicalVolume_numerator_parse
    geometryRow115_physicalVolume_denominator_parse geometryRow115_physicalVolume_denominator_nonzero

theorem geometryRow115_physicalVolume_read :
    rationalField geometryRowsJson115 "physical_volume" = .ok geometryRowsTyped115.physicalVolume :=
  original_rationalField_of_string geometryRowsJson115 "physical_volume" geometryRow115_physicalVolumeText
    geometryRowsTyped115.physicalVolume geometryRow115_physicalVolume_field geometryRow115_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_physicalVolume_complete"
  err.flush

noncomputable def geometryRow115_meanGapNumeratorChars : List Char := ['9', '1', '9', '2', '4', '9', '9', '7']
noncomputable def geometryRow115_meanGapDenominatorChars : List Char := ['4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow115_meanGapText : String := String.ofList (geometryRow115_meanGapNumeratorChars ++ '/' :: geometryRow115_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_meanGap_before_field"
  err.flush

theorem geometryRow115_meanGap_field :
    geometryRowsJson115.getObjVal? "mean_gap" = .ok (.str geometryRow115_meanGapText) := by rfl

theorem geometryRow115_meanGap_numerator_no_slash :
    geometryRow115_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow115_meanGap_numerator_parse :
    SourceJson.intChars geometryRow115_meanGapNumeratorChars = some (91924997 : Int) := by decide +kernel

theorem geometryRow115_meanGap_denominator_parse :
    SourceJson.intChars geometryRow115_meanGapDenominatorChars = some (407826000000 : Int) := by decide +kernel

theorem geometryRow115_meanGap_denominator_nonzero : (407826000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow115_meanGap_parse :
    parseRational geometryRow115_meanGapText = .ok geometryRowsTyped115.meanGap :=
  original_rational_fraction_of_chars geometryRow115_meanGapNumeratorChars geometryRow115_meanGapDenominatorChars
    (91924997 : Int) (407826000000 : Int)
    geometryRow115_meanGap_numerator_no_slash geometryRow115_meanGap_numerator_parse
    geometryRow115_meanGap_denominator_parse geometryRow115_meanGap_denominator_nonzero

theorem geometryRow115_meanGap_read :
    rationalField geometryRowsJson115 "mean_gap" = .ok geometryRowsTyped115.meanGap :=
  original_rationalField_of_string geometryRowsJson115 "mean_gap" geometryRow115_meanGapText
    geometryRowsTyped115.meanGap geometryRow115_meanGap_field geometryRow115_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_meanGap_complete"
  err.flush

noncomputable def geometryRow115_jensenBoundNumeratorChars : List Char := ['1', '0', '3', '3', '5', '2', '2', '5', '0', '9', '8', '7', '0', '5', '7', '3', '5', '0', '8', '8', '8', '3', '8', '1', '6', '2', '7', '0', '8', '3', '6', '4', '1', '3', '3', '7', '1', '7', '7', '0', '1', '7', '9', '4', '5', '3', '8', '2', '3', '6', '0', '1', '1', '0', '6', '6', '4', '8', '3', '5', '4', '4', '0', '7', '8', '7', '8', '4', '3', '8', '5', '4', '8', '8', '8', '0', '2', '7', '2', '2', '1', '3', '2', '8', '5', '2', '7', '0', '6', '7', '9', '6', '1', '3', '2', '3', '4', '6', '9', '9', '8', '7', '9', '8', '4', '8', '4', '2', '0', '9', '7', '6', '8', '9', '9', '9', '3', '4', '2', '5', '6', '4', '0', '5', '9', '0', '5', '4', '7', '4', '6', '8', '0', '1', '3', '8', '4', '4', '4', '4', '5', '8', '6', '5', '8', '6', '4', '3', '1', '0', '5', '8', '8', '7', '5', '7', '9', '1', '5', '1', '6', '6', '8', '8', '8', '5', '3', '9', '3', '2', '6', '2', '0', '0', '3', '0', '2', '8', '0', '8', '1', '5', '7', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow115_jensenBoundDenominatorChars : List Char := ['6', '5', '3', '5', '3', '4', '1', '0', '4', '3', '8', '5', '6', '8', '8', '8', '7', '3', '2', '6', '9', '9', '9', '8', '9', '6', '6', '3', '0', '4', '5', '8', '5', '6', '9', '2', '8', '7', '7', '2', '8', '4', '0', '0', '9', '3', '7', '5', '0', '3', '6', '7', '0', '5', '2', '6', '4', '4', '9', '2', '6', '6', '2', '2', '5', '3', '1', '8', '8', '8', '3', '9', '1', '8', '1', '7', '2', '9', '1', '8', '7', '8', '5', '0', '0', '6', '8', '1', '4', '8', '3', '8', '9', '0', '7', '0', '6', '6', '9', '4', '4', '7', '3', '9', '7', '3', '4', '3', '6', '5', '9', '2', '0', '3', '4', '8', '2', '9', '0', '2', '1', '7', '7', '6', '4', '5', '7', '0', '6', '7', '9', '0', '9', '0', '9', '6', '0', '8', '7', '9', '4', '3', '7', '5', '0', '4', '4', '7', '0', '3', '4', '0', '8', '4', '1', '3', '7', '4', '8', '6', '2', '2', '9', '4', '7', '0', '0', '5', '5', '4', '9', '1', '0', '8', '0', '6', '5', '2', '4', '9', '3', '3', '9', '9', '5', '2', '1', '9', '6', '6', '3', '3', '8', '8', '9', '5', '4', '6', '5', '1', '7', '5', '6', '8', '1', '4', '3', '1', '1', '3', '4', '0', '1', '9', '0', '4', '1', '6', '1', '8', '7', '2', '5', '3', '1', '9']
noncomputable def geometryRow115_jensenBoundText : String := String.ofList (geometryRow115_jensenBoundNumeratorChars ++ '/' :: geometryRow115_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_jensenBound_before_field"
  err.flush

theorem geometryRow115_jensenBound_field :
    geometryRowsJson115.getObjVal? "jensen_bound" = .ok (.str geometryRow115_jensenBoundText) := by rfl

theorem geometryRow115_jensenBound_numerator_no_slash :
    geometryRow115_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow115_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow115_jensenBoundNumeratorChars = some (10335225098705735088838162708364133717701794538236011066483544078784385488802722132852706796132346998798484209768999342564059054746801384444586586431058875791516688853932620030280815793750000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow115_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow115_jensenBoundDenominatorChars = some (6535341043856888732699989663045856928772840093750367052644926622531888391817291878500681483890706694473973436592034829021776457067909096087943750447034084137486229470055491080652493399521966338895465175681431134019041618725319 : Int) := by decide +kernel

theorem geometryRow115_jensenBound_denominator_nonzero : (6535341043856888732699989663045856928772840093750367052644926622531888391817291878500681483890706694473973436592034829021776457067909096087943750447034084137486229470055491080652493399521966338895465175681431134019041618725319 : Int) ≠ 0 := by decide +kernel

theorem geometryRow115_jensenBound_parse :
    parseRational geometryRow115_jensenBoundText = .ok geometryRowsTyped115.jensenBound :=
  original_rational_fraction_of_chars geometryRow115_jensenBoundNumeratorChars geometryRow115_jensenBoundDenominatorChars
    (10335225098705735088838162708364133717701794538236011066483544078784385488802722132852706796132346998798484209768999342564059054746801384444586586431058875791516688853932620030280815793750000000000000000000000000 : Int) (6535341043856888732699989663045856928772840093750367052644926622531888391817291878500681483890706694473973436592034829021776457067909096087943750447034084137486229470055491080652493399521966338895465175681431134019041618725319 : Int)
    geometryRow115_jensenBound_numerator_no_slash geometryRow115_jensenBound_numerator_parse
    geometryRow115_jensenBound_denominator_parse geometryRow115_jensenBound_denominator_nonzero

theorem geometryRow115_jensenBound_read :
    rationalField geometryRowsJson115 "jensen_bound" = .ok geometryRowsTyped115.jensenBound :=
  original_rationalField_of_string geometryRowsJson115 "jensen_bound" geometryRow115_jensenBoundText
    geometryRowsTyped115.jensenBound geometryRow115_jensenBound_field geometryRow115_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_factorMaxima_before"
  err.flush

theorem geometryRow115_factorMaxima_read :
    rationalArrayField geometryRowsJson115 "factor_maxima" = .ok geometryRowsTyped115.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_gapWeightedMeans_before"
  err.flush

theorem geometryRow115_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson115 "gap_weighted_means" = .ok geometryRowsTyped115.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow115_floorChars : List Char := ['1', '2', '5', '2', '9', '4', '2', '8', '6', '5', '9', '4', '4', '9', '3']
noncomputable def geometryRow115_floorText : String := String.ofList geometryRow115_floorChars

theorem geometryRow115_floor_text_read :
    geometryRowsJson115.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow115_floorText := by rfl

theorem geometryRow115_floor_chars_parse :
    SourceJson.intChars geometryRow115_floorChars = some (125294286594493 : Int) := by decide +kernel

theorem geometryRow115_floor_parse :
    parseInteger geometryRow115_floorText = .ok geometryRowsTyped115.jensenFloorQ96 := by
  simp only [geometryRow115_floorText, parseInteger, String.toList_ofList, geometryRow115_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_115 :
    decodeGeometryRow geometryRowsJson115 = .ok geometryRowsTyped115 :=
  original_geometryRow_of_fields geometryRowsJson115 geometryRowsTyped115 geometryRow115_floorText
    geometryRow115_simplexId_read geometryRow115_vertexIds_read
    geometryRow115_physicalVolume_read geometryRow115_meanGap_read
    geometryRow115_factorMaxima_read geometryRow115_gapWeightedMeans_read
    geometryRow115_jensenBound_read geometryRow115_floor_text_read geometryRow115_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_115_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock058 : List SourceJson := [geometryRowsJson114, geometryRowsJson115]
noncomputable def geometryRowsTypedBlock058 : List (GeometryRow) := [geometryRowsTyped114, geometryRowsTyped115]
noncomputable def geometryRowsTypedThroughBlock058 : List (GeometryRow) := geometryRowsTypedThroughBlock057 ++ geometryRowsTypedBlock058

theorem geometry_Rows_block_058_push_eq (acc : List SourceJson) :
    SimplicesBlock058.blockPush acc = [geometryRowsJson115, geometryRowsJson114] ++ acc := by rfl

theorem geometry_Rows_block_058_reverse (acc : List SourceJson) :
    (SimplicesBlock058.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock058 := by
  rw [geometry_Rows_block_058_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_058 :
    geometryRowsJsonBlock058.mapM decodeGeometryRow = .ok geometryRowsTypedBlock058 := by
  simp only [geometryRowsJsonBlock058, geometryRowsTypedBlock058, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_114, decode_geometry_Rows_115]
  rfl

theorem decode_geometry_Rows_through_block_058 :
    SimplicesValue.arrayAcc059.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock058 := by
  change (SimplicesBlock058.blockPush SimplicesValue.arrayAcc058).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_058_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_057, decode_geometry_Rows_block_058]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_058_complete"
  err.flush

#print axioms geometryRow114_simplexId_read
#print axioms geometryRow114_vertexIds_read
#print axioms geometryRow114_physicalVolume_field
#print axioms geometryRow114_physicalVolume_numerator_no_slash
#print axioms geometryRow114_physicalVolume_numerator_parse
#print axioms geometryRow114_physicalVolume_denominator_parse
#print axioms geometryRow114_physicalVolume_denominator_nonzero
#print axioms geometryRow114_physicalVolume_parse
#print axioms geometryRow114_physicalVolume_read
#print axioms geometryRow114_meanGap_field
#print axioms geometryRow114_meanGap_numerator_no_slash
#print axioms geometryRow114_meanGap_numerator_parse
#print axioms geometryRow114_meanGap_denominator_parse
#print axioms geometryRow114_meanGap_denominator_nonzero
#print axioms geometryRow114_meanGap_parse
#print axioms geometryRow114_meanGap_read
#print axioms geometryRow114_jensenBound_field
#print axioms geometryRow114_jensenBound_numerator_no_slash
#print axioms geometryRow114_jensenBound_numerator_parse
#print axioms geometryRow114_jensenBound_denominator_parse
#print axioms geometryRow114_jensenBound_denominator_nonzero
#print axioms geometryRow114_jensenBound_parse
#print axioms geometryRow114_jensenBound_read
#print axioms geometryRow114_factorMaxima_read
#print axioms geometryRow114_gapWeightedMeans_read
#print axioms geometryRow114_floor_text_read
#print axioms geometryRow114_floor_chars_parse
#print axioms geometryRow114_floor_parse
#print axioms decode_geometry_Rows_114
#print axioms geometryRow115_simplexId_read
#print axioms geometryRow115_vertexIds_read
#print axioms geometryRow115_physicalVolume_field
#print axioms geometryRow115_physicalVolume_numerator_no_slash
#print axioms geometryRow115_physicalVolume_numerator_parse
#print axioms geometryRow115_physicalVolume_denominator_parse
#print axioms geometryRow115_physicalVolume_denominator_nonzero
#print axioms geometryRow115_physicalVolume_parse
#print axioms geometryRow115_physicalVolume_read
#print axioms geometryRow115_meanGap_field
#print axioms geometryRow115_meanGap_numerator_no_slash
#print axioms geometryRow115_meanGap_numerator_parse
#print axioms geometryRow115_meanGap_denominator_parse
#print axioms geometryRow115_meanGap_denominator_nonzero
#print axioms geometryRow115_meanGap_parse
#print axioms geometryRow115_meanGap_read
#print axioms geometryRow115_jensenBound_field
#print axioms geometryRow115_jensenBound_numerator_no_slash
#print axioms geometryRow115_jensenBound_numerator_parse
#print axioms geometryRow115_jensenBound_denominator_parse
#print axioms geometryRow115_jensenBound_denominator_nonzero
#print axioms geometryRow115_jensenBound_parse
#print axioms geometryRow115_jensenBound_read
#print axioms geometryRow115_factorMaxima_read
#print axioms geometryRow115_gapWeightedMeans_read
#print axioms geometryRow115_floor_text_read
#print axioms geometryRow115_floor_chars_parse
#print axioms geometryRow115_floor_parse
#print axioms decode_geometry_Rows_115
#print axioms geometry_Rows_block_058_push_eq
#print axioms geometry_Rows_block_058_reverse
#print axioms decode_geometry_Rows_block_058
#print axioms decode_geometry_Rows_through_block_058

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
