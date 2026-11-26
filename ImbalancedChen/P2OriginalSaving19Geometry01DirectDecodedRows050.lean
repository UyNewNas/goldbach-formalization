import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows049

/-! Original simplices typed block 50, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson098 : SourceJson :=
  (SimplicesBlock050.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped098 : GeometryRow :=
  { simplexId := 98,
    vertexIds := #[39, 37, 24, 23, 19, 7, 6, 2, 0],
    physicalVolume := ((3936095563083281283002139400823402930625436067 : ℚ) / (1044370650115803709440000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((34630061 : ℚ) / (49039200000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((65060927907277648471 : ℚ) / (768247125248400000000 : ℚ)), ((92257471766243284793 : ℚ) / (1075545975347760000000 : ℚ)), ((2327453484642460496219 : ℚ) / (16133189630216400000000 : ℚ)), ((297693226344212879011 : ℚ) / (2688864938369400000000 : ℚ)), ((886961215328721193639 : ℚ) / (16133189630216400000000 : ℚ)), ((776480965391661886057 : ℚ) / (16133189630216400000000 : ℚ)), ((1347561127720597183 : ℚ) / (33964609747824000000 : ℚ)), ((126295387205163009989 : ℚ) / (3226637926043280000000 : ℚ)), ((125433497022626009687 : ℚ) / (3226637926043280000000 : ℚ)), ((576491573838080962961 : ℚ) / (16133189630216400000000 : ℚ))],
    jensenBound := ((1776221516958644452586395428364170297433994158646236063287073218380366049340671518807174950605718269730480734523853780087916861431976827876304170817216661510895158404000000000000000000000000 : ℚ) / (110499161657841360877921392616324125268916239342707699799037849433941903585492973530828607133817438732551170481680809896793067435206596518551690348505123131121624579057257979511790649969079770303598931 : ℚ)),
    jensenFloorQ96 := (1273555064993981399 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_simplexId_before"
  err.flush

theorem geometryRow098_simplexId_read :
    geometryRowsJson098.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped098.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_vertexIds_before"
  err.flush

theorem geometryRow098_vertexIds_read :
    geometryRowsJson098.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped098.vertexIds := by decide +kernel

noncomputable def geometryRow098_physicalVolumeNumeratorChars : List Char := ['3', '9', '3', '6', '0', '9', '5', '5', '6', '3', '0', '8', '3', '2', '8', '1', '2', '8', '3', '0', '0', '2', '1', '3', '9', '4', '0', '0', '8', '2', '3', '4', '0', '2', '9', '3', '0', '6', '2', '5', '4', '3', '6', '0', '6', '7']
noncomputable def geometryRow098_physicalVolumeDenominatorChars : List Char := ['1', '0', '4', '4', '3', '7', '0', '6', '5', '0', '1', '1', '5', '8', '0', '3', '7', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow098_physicalVolumeText : String := String.ofList (geometryRow098_physicalVolumeNumeratorChars ++ '/' :: geometryRow098_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_physicalVolume_before_field"
  err.flush

theorem geometryRow098_physicalVolume_field :
    geometryRowsJson098.getObjVal? "physical_volume" = .ok (.str geometryRow098_physicalVolumeText) := by rfl

theorem geometryRow098_physicalVolume_numerator_no_slash :
    geometryRow098_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow098_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow098_physicalVolumeNumeratorChars = some (3936095563083281283002139400823402930625436067 : Int) := by decide +kernel

theorem geometryRow098_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow098_physicalVolumeDenominatorChars = some (1044370650115803709440000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow098_physicalVolume_denominator_nonzero : (1044370650115803709440000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow098_physicalVolume_parse :
    parseRational geometryRow098_physicalVolumeText = .ok geometryRowsTyped098.physicalVolume :=
  original_rational_fraction_of_chars geometryRow098_physicalVolumeNumeratorChars geometryRow098_physicalVolumeDenominatorChars
    (3936095563083281283002139400823402930625436067 : Int) (1044370650115803709440000000000000000000000000000000000000000000000 : Int)
    geometryRow098_physicalVolume_numerator_no_slash geometryRow098_physicalVolume_numerator_parse
    geometryRow098_physicalVolume_denominator_parse geometryRow098_physicalVolume_denominator_nonzero

theorem geometryRow098_physicalVolume_read :
    rationalField geometryRowsJson098 "physical_volume" = .ok geometryRowsTyped098.physicalVolume :=
  original_rationalField_of_string geometryRowsJson098 "physical_volume" geometryRow098_physicalVolumeText
    geometryRowsTyped098.physicalVolume geometryRow098_physicalVolume_field geometryRow098_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_physicalVolume_complete"
  err.flush

noncomputable def geometryRow098_meanGapNumeratorChars : List Char := ['3', '4', '6', '3', '0', '0', '6', '1']
noncomputable def geometryRow098_meanGapDenominatorChars : List Char := ['4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0']
noncomputable def geometryRow098_meanGapText : String := String.ofList (geometryRow098_meanGapNumeratorChars ++ '/' :: geometryRow098_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_meanGap_before_field"
  err.flush

theorem geometryRow098_meanGap_field :
    geometryRowsJson098.getObjVal? "mean_gap" = .ok (.str geometryRow098_meanGapText) := by rfl

theorem geometryRow098_meanGap_numerator_no_slash :
    geometryRow098_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow098_meanGap_numerator_parse :
    SourceJson.intChars geometryRow098_meanGapNumeratorChars = some (34630061 : Int) := by decide +kernel

theorem geometryRow098_meanGap_denominator_parse :
    SourceJson.intChars geometryRow098_meanGapDenominatorChars = some (49039200000 : Int) := by decide +kernel

theorem geometryRow098_meanGap_denominator_nonzero : (49039200000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow098_meanGap_parse :
    parseRational geometryRow098_meanGapText = .ok geometryRowsTyped098.meanGap :=
  original_rational_fraction_of_chars geometryRow098_meanGapNumeratorChars geometryRow098_meanGapDenominatorChars
    (34630061 : Int) (49039200000 : Int)
    geometryRow098_meanGap_numerator_no_slash geometryRow098_meanGap_numerator_parse
    geometryRow098_meanGap_denominator_parse geometryRow098_meanGap_denominator_nonzero

theorem geometryRow098_meanGap_read :
    rationalField geometryRowsJson098 "mean_gap" = .ok geometryRowsTyped098.meanGap :=
  original_rationalField_of_string geometryRowsJson098 "mean_gap" geometryRow098_meanGapText
    geometryRowsTyped098.meanGap geometryRow098_meanGap_field geometryRow098_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_meanGap_complete"
  err.flush

noncomputable def geometryRow098_jensenBoundNumeratorChars : List Char := ['1', '7', '7', '6', '2', '2', '1', '5', '1', '6', '9', '5', '8', '6', '4', '4', '4', '5', '2', '5', '8', '6', '3', '9', '5', '4', '2', '8', '3', '6', '4', '1', '7', '0', '2', '9', '7', '4', '3', '3', '9', '9', '4', '1', '5', '8', '6', '4', '6', '2', '3', '6', '0', '6', '3', '2', '8', '7', '0', '7', '3', '2', '1', '8', '3', '8', '0', '3', '6', '6', '0', '4', '9', '3', '4', '0', '6', '7', '1', '5', '1', '8', '8', '0', '7', '1', '7', '4', '9', '5', '0', '6', '0', '5', '7', '1', '8', '2', '6', '9', '7', '3', '0', '4', '8', '0', '7', '3', '4', '5', '2', '3', '8', '5', '3', '7', '8', '0', '0', '8', '7', '9', '1', '6', '8', '6', '1', '4', '3', '1', '9', '7', '6', '8', '2', '7', '8', '7', '6', '3', '0', '4', '1', '7', '0', '8', '1', '7', '2', '1', '6', '6', '6', '1', '5', '1', '0', '8', '9', '5', '1', '5', '8', '4', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow098_jensenBoundDenominatorChars : List Char := ['1', '1', '0', '4', '9', '9', '1', '6', '1', '6', '5', '7', '8', '4', '1', '3', '6', '0', '8', '7', '7', '9', '2', '1', '3', '9', '2', '6', '1', '6', '3', '2', '4', '1', '2', '5', '2', '6', '8', '9', '1', '6', '2', '3', '9', '3', '4', '2', '7', '0', '7', '6', '9', '9', '7', '9', '9', '0', '3', '7', '8', '4', '9', '4', '3', '3', '9', '4', '1', '9', '0', '3', '5', '8', '5', '4', '9', '2', '9', '7', '3', '5', '3', '0', '8', '2', '8', '6', '0', '7', '1', '3', '3', '8', '1', '7', '4', '3', '8', '7', '3', '2', '5', '5', '1', '1', '7', '0', '4', '8', '1', '6', '8', '0', '8', '0', '9', '8', '9', '6', '7', '9', '3', '0', '6', '7', '4', '3', '5', '2', '0', '6', '5', '9', '6', '5', '1', '8', '5', '5', '1', '6', '9', '0', '3', '4', '8', '5', '0', '5', '1', '2', '3', '1', '3', '1', '1', '2', '1', '6', '2', '4', '5', '7', '9', '0', '5', '7', '2', '5', '7', '9', '7', '9', '5', '1', '1', '7', '9', '0', '6', '4', '9', '9', '6', '9', '0', '7', '9', '7', '7', '0', '3', '0', '3', '5', '9', '8', '9', '3', '1']
noncomputable def geometryRow098_jensenBoundText : String := String.ofList (geometryRow098_jensenBoundNumeratorChars ++ '/' :: geometryRow098_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_jensenBound_before_field"
  err.flush

theorem geometryRow098_jensenBound_field :
    geometryRowsJson098.getObjVal? "jensen_bound" = .ok (.str geometryRow098_jensenBoundText) := by rfl

theorem geometryRow098_jensenBound_numerator_no_slash :
    geometryRow098_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow098_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow098_jensenBoundNumeratorChars = some (1776221516958644452586395428364170297433994158646236063287073218380366049340671518807174950605718269730480734523853780087916861431976827876304170817216661510895158404000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow098_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow098_jensenBoundDenominatorChars = some (110499161657841360877921392616324125268916239342707699799037849433941903585492973530828607133817438732551170481680809896793067435206596518551690348505123131121624579057257979511790649969079770303598931 : Int) := by decide +kernel

theorem geometryRow098_jensenBound_denominator_nonzero : (110499161657841360877921392616324125268916239342707699799037849433941903585492973530828607133817438732551170481680809896793067435206596518551690348505123131121624579057257979511790649969079770303598931 : Int) ≠ 0 := by decide +kernel

theorem geometryRow098_jensenBound_parse :
    parseRational geometryRow098_jensenBoundText = .ok geometryRowsTyped098.jensenBound :=
  original_rational_fraction_of_chars geometryRow098_jensenBoundNumeratorChars geometryRow098_jensenBoundDenominatorChars
    (1776221516958644452586395428364170297433994158646236063287073218380366049340671518807174950605718269730480734523853780087916861431976827876304170817216661510895158404000000000000000000000000 : Int) (110499161657841360877921392616324125268916239342707699799037849433941903585492973530828607133817438732551170481680809896793067435206596518551690348505123131121624579057257979511790649969079770303598931 : Int)
    geometryRow098_jensenBound_numerator_no_slash geometryRow098_jensenBound_numerator_parse
    geometryRow098_jensenBound_denominator_parse geometryRow098_jensenBound_denominator_nonzero

theorem geometryRow098_jensenBound_read :
    rationalField geometryRowsJson098 "jensen_bound" = .ok geometryRowsTyped098.jensenBound :=
  original_rationalField_of_string geometryRowsJson098 "jensen_bound" geometryRow098_jensenBoundText
    geometryRowsTyped098.jensenBound geometryRow098_jensenBound_field geometryRow098_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_factorMaxima_before"
  err.flush

theorem geometryRow098_factorMaxima_read :
    rationalArrayField geometryRowsJson098 "factor_maxima" = .ok geometryRowsTyped098.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_gapWeightedMeans_before"
  err.flush

theorem geometryRow098_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson098 "gap_weighted_means" = .ok geometryRowsTyped098.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow098_floorChars : List Char := ['1', '2', '7', '3', '5', '5', '5', '0', '6', '4', '9', '9', '3', '9', '8', '1', '3', '9', '9']
noncomputable def geometryRow098_floorText : String := String.ofList geometryRow098_floorChars

theorem geometryRow098_floor_text_read :
    geometryRowsJson098.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow098_floorText := by rfl

theorem geometryRow098_floor_chars_parse :
    SourceJson.intChars geometryRow098_floorChars = some (1273555064993981399 : Int) := by decide +kernel

theorem geometryRow098_floor_parse :
    parseInteger geometryRow098_floorText = .ok geometryRowsTyped098.jensenFloorQ96 := by
  simp only [geometryRow098_floorText, parseInteger, String.toList_ofList, geometryRow098_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_098 :
    decodeGeometryRow geometryRowsJson098 = .ok geometryRowsTyped098 :=
  original_geometryRow_of_fields geometryRowsJson098 geometryRowsTyped098 geometryRow098_floorText
    geometryRow098_simplexId_read geometryRow098_vertexIds_read
    geometryRow098_physicalVolume_read geometryRow098_meanGap_read
    geometryRow098_factorMaxima_read geometryRow098_gapWeightedMeans_read
    geometryRow098_jensenBound_read geometryRow098_floor_text_read geometryRow098_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_098_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson099 : SourceJson :=
  (SimplicesBlock050.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped099 : GeometryRow :=
  { simplexId := 99,
    vertexIds := #[39, 37, 24, 23, 19, 18, 7, 6, 0],
    physicalVolume := ((1031164675058072567015031769435383336793901837 : ℚ) / (1481301228225476689920000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((111567216101 : ℚ) / (1386525000000 : ℚ)), ((447483458309 : ℚ) / (5546100000000 : ℚ)), ((2427769246087 : ℚ) / (16638300000000 : ℚ)), ((300679932353 : ℚ) / (2773050000000 : ℚ)), ((1757679790999 : ℚ) / (33276600000000 : ℚ)), ((798680397041 : ℚ) / (16638300000000 : ℚ)), ((3641055443 : ℚ) / (87570000000 : ℚ)), ((136583244397 : ℚ) / (3327660000000 : ℚ)), ((271388738981 : ℚ) / (6655320000000 : ℚ)), ((631010491999 : ℚ) / (16638300000000 : ℚ))],
    jensenBound := ((113022280976553825874206864062159928341283906940892214997410295819321212184204367694854736328125000000 : ℚ) / (229317783656442448574901481646385809974393065431781378294381004188500837408809150918141780649956554731646095305111 : ℚ)),
    jensenFloorQ96 := (39048640284953688 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_simplexId_before"
  err.flush

theorem geometryRow099_simplexId_read :
    geometryRowsJson099.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped099.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_vertexIds_before"
  err.flush

theorem geometryRow099_vertexIds_read :
    geometryRowsJson099.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped099.vertexIds := by decide +kernel

noncomputable def geometryRow099_physicalVolumeNumeratorChars : List Char := ['1', '0', '3', '1', '1', '6', '4', '6', '7', '5', '0', '5', '8', '0', '7', '2', '5', '6', '7', '0', '1', '5', '0', '3', '1', '7', '6', '9', '4', '3', '5', '3', '8', '3', '3', '3', '6', '7', '9', '3', '9', '0', '1', '8', '3', '7']
noncomputable def geometryRow099_physicalVolumeDenominatorChars : List Char := ['1', '4', '8', '1', '3', '0', '1', '2', '2', '8', '2', '2', '5', '4', '7', '6', '6', '8', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow099_physicalVolumeText : String := String.ofList (geometryRow099_physicalVolumeNumeratorChars ++ '/' :: geometryRow099_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_physicalVolume_before_field"
  err.flush

theorem geometryRow099_physicalVolume_field :
    geometryRowsJson099.getObjVal? "physical_volume" = .ok (.str geometryRow099_physicalVolumeText) := by rfl

theorem geometryRow099_physicalVolume_numerator_no_slash :
    geometryRow099_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow099_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow099_physicalVolumeNumeratorChars = some (1031164675058072567015031769435383336793901837 : Int) := by decide +kernel

theorem geometryRow099_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow099_physicalVolumeDenominatorChars = some (1481301228225476689920000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow099_physicalVolume_denominator_nonzero : (1481301228225476689920000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow099_physicalVolume_parse :
    parseRational geometryRow099_physicalVolumeText = .ok geometryRowsTyped099.physicalVolume :=
  original_rational_fraction_of_chars geometryRow099_physicalVolumeNumeratorChars geometryRow099_physicalVolumeDenominatorChars
    (1031164675058072567015031769435383336793901837 : Int) (1481301228225476689920000000000000000000000000000000000000000000000 : Int)
    geometryRow099_physicalVolume_numerator_no_slash geometryRow099_physicalVolume_numerator_parse
    geometryRow099_physicalVolume_denominator_parse geometryRow099_physicalVolume_denominator_nonzero

theorem geometryRow099_physicalVolume_read :
    rationalField geometryRowsJson099 "physical_volume" = .ok geometryRowsTyped099.physicalVolume :=
  original_rationalField_of_string geometryRowsJson099 "physical_volume" geometryRow099_physicalVolumeText
    geometryRowsTyped099.physicalVolume geometryRow099_physicalVolume_field geometryRow099_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_physicalVolume_complete"
  err.flush

noncomputable def geometryRow099_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow099_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow099_meanGapText : String := String.ofList (geometryRow099_meanGapNumeratorChars ++ '/' :: geometryRow099_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_meanGap_before_field"
  err.flush

theorem geometryRow099_meanGap_field :
    geometryRowsJson099.getObjVal? "mean_gap" = .ok (.str geometryRow099_meanGapText) := by rfl

theorem geometryRow099_meanGap_numerator_no_slash :
    geometryRow099_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow099_meanGap_numerator_parse :
    SourceJson.intChars geometryRow099_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow099_meanGap_denominator_parse :
    SourceJson.intChars geometryRow099_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow099_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow099_meanGap_parse :
    parseRational geometryRow099_meanGapText = .ok geometryRowsTyped099.meanGap :=
  original_rational_fraction_of_chars geometryRow099_meanGapNumeratorChars geometryRow099_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow099_meanGap_numerator_no_slash geometryRow099_meanGap_numerator_parse
    geometryRow099_meanGap_denominator_parse geometryRow099_meanGap_denominator_nonzero

theorem geometryRow099_meanGap_read :
    rationalField geometryRowsJson099 "mean_gap" = .ok geometryRowsTyped099.meanGap :=
  original_rationalField_of_string geometryRowsJson099 "mean_gap" geometryRow099_meanGapText
    geometryRowsTyped099.meanGap geometryRow099_meanGap_field geometryRow099_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_meanGap_complete"
  err.flush

noncomputable def geometryRow099_jensenBoundNumeratorChars : List Char := ['1', '1', '3', '0', '2', '2', '2', '8', '0', '9', '7', '6', '5', '5', '3', '8', '2', '5', '8', '7', '4', '2', '0', '6', '8', '6', '4', '0', '6', '2', '1', '5', '9', '9', '2', '8', '3', '4', '1', '2', '8', '3', '9', '0', '6', '9', '4', '0', '8', '9', '2', '2', '1', '4', '9', '9', '7', '4', '1', '0', '2', '9', '5', '8', '1', '9', '3', '2', '1', '2', '1', '2', '1', '8', '4', '2', '0', '4', '3', '6', '7', '6', '9', '4', '8', '5', '4', '7', '3', '6', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow099_jensenBoundDenominatorChars : List Char := ['2', '2', '9', '3', '1', '7', '7', '8', '3', '6', '5', '6', '4', '4', '2', '4', '4', '8', '5', '7', '4', '9', '0', '1', '4', '8', '1', '6', '4', '6', '3', '8', '5', '8', '0', '9', '9', '7', '4', '3', '9', '3', '0', '6', '5', '4', '3', '1', '7', '8', '1', '3', '7', '8', '2', '9', '4', '3', '8', '1', '0', '0', '4', '1', '8', '8', '5', '0', '0', '8', '3', '7', '4', '0', '8', '8', '0', '9', '1', '5', '0', '9', '1', '8', '1', '4', '1', '7', '8', '0', '6', '4', '9', '9', '5', '6', '5', '5', '4', '7', '3', '1', '6', '4', '6', '0', '9', '5', '3', '0', '5', '1', '1', '1']
noncomputable def geometryRow099_jensenBoundText : String := String.ofList (geometryRow099_jensenBoundNumeratorChars ++ '/' :: geometryRow099_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_jensenBound_before_field"
  err.flush

theorem geometryRow099_jensenBound_field :
    geometryRowsJson099.getObjVal? "jensen_bound" = .ok (.str geometryRow099_jensenBoundText) := by rfl

theorem geometryRow099_jensenBound_numerator_no_slash :
    geometryRow099_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow099_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow099_jensenBoundNumeratorChars = some (113022280976553825874206864062159928341283906940892214997410295819321212184204367694854736328125000000 : Int) := by decide +kernel

theorem geometryRow099_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow099_jensenBoundDenominatorChars = some (229317783656442448574901481646385809974393065431781378294381004188500837408809150918141780649956554731646095305111 : Int) := by decide +kernel

theorem geometryRow099_jensenBound_denominator_nonzero : (229317783656442448574901481646385809974393065431781378294381004188500837408809150918141780649956554731646095305111 : Int) ≠ 0 := by decide +kernel

theorem geometryRow099_jensenBound_parse :
    parseRational geometryRow099_jensenBoundText = .ok geometryRowsTyped099.jensenBound :=
  original_rational_fraction_of_chars geometryRow099_jensenBoundNumeratorChars geometryRow099_jensenBoundDenominatorChars
    (113022280976553825874206864062159928341283906940892214997410295819321212184204367694854736328125000000 : Int) (229317783656442448574901481646385809974393065431781378294381004188500837408809150918141780649956554731646095305111 : Int)
    geometryRow099_jensenBound_numerator_no_slash geometryRow099_jensenBound_numerator_parse
    geometryRow099_jensenBound_denominator_parse geometryRow099_jensenBound_denominator_nonzero

theorem geometryRow099_jensenBound_read :
    rationalField geometryRowsJson099 "jensen_bound" = .ok geometryRowsTyped099.jensenBound :=
  original_rationalField_of_string geometryRowsJson099 "jensen_bound" geometryRow099_jensenBoundText
    geometryRowsTyped099.jensenBound geometryRow099_jensenBound_field geometryRow099_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_factorMaxima_before"
  err.flush

theorem geometryRow099_factorMaxima_read :
    rationalArrayField geometryRowsJson099 "factor_maxima" = .ok geometryRowsTyped099.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_gapWeightedMeans_before"
  err.flush

theorem geometryRow099_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson099 "gap_weighted_means" = .ok geometryRowsTyped099.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow099_floorChars : List Char := ['3', '9', '0', '4', '8', '6', '4', '0', '2', '8', '4', '9', '5', '3', '6', '8', '8']
noncomputable def geometryRow099_floorText : String := String.ofList geometryRow099_floorChars

theorem geometryRow099_floor_text_read :
    geometryRowsJson099.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow099_floorText := by rfl

theorem geometryRow099_floor_chars_parse :
    SourceJson.intChars geometryRow099_floorChars = some (39048640284953688 : Int) := by decide +kernel

theorem geometryRow099_floor_parse :
    parseInteger geometryRow099_floorText = .ok geometryRowsTyped099.jensenFloorQ96 := by
  simp only [geometryRow099_floorText, parseInteger, String.toList_ofList, geometryRow099_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_099 :
    decodeGeometryRow geometryRowsJson099 = .ok geometryRowsTyped099 :=
  original_geometryRow_of_fields geometryRowsJson099 geometryRowsTyped099 geometryRow099_floorText
    geometryRow099_simplexId_read geometryRow099_vertexIds_read
    geometryRow099_physicalVolume_read geometryRow099_meanGap_read
    geometryRow099_factorMaxima_read geometryRow099_gapWeightedMeans_read
    geometryRow099_jensenBound_read geometryRow099_floor_text_read geometryRow099_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_099_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock050 : List SourceJson := [geometryRowsJson098, geometryRowsJson099]
noncomputable def geometryRowsTypedBlock050 : List (GeometryRow) := [geometryRowsTyped098, geometryRowsTyped099]
noncomputable def geometryRowsTypedThroughBlock050 : List (GeometryRow) := geometryRowsTypedThroughBlock049 ++ geometryRowsTypedBlock050

theorem geometry_Rows_block_050_push_eq (acc : List SourceJson) :
    SimplicesBlock050.blockPush acc = [geometryRowsJson099, geometryRowsJson098] ++ acc := by rfl

theorem geometry_Rows_block_050_reverse (acc : List SourceJson) :
    (SimplicesBlock050.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock050 := by
  rw [geometry_Rows_block_050_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_050 :
    geometryRowsJsonBlock050.mapM decodeGeometryRow = .ok geometryRowsTypedBlock050 := by
  simp only [geometryRowsJsonBlock050, geometryRowsTypedBlock050, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_098, decode_geometry_Rows_099]
  rfl

theorem decode_geometry_Rows_through_block_050 :
    SimplicesValue.arrayAcc051.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock050 := by
  change (SimplicesBlock050.blockPush SimplicesValue.arrayAcc050).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_050_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_049, decode_geometry_Rows_block_050]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_050_complete"
  err.flush

#print axioms geometryRow098_simplexId_read
#print axioms geometryRow098_vertexIds_read
#print axioms geometryRow098_physicalVolume_field
#print axioms geometryRow098_physicalVolume_numerator_no_slash
#print axioms geometryRow098_physicalVolume_numerator_parse
#print axioms geometryRow098_physicalVolume_denominator_parse
#print axioms geometryRow098_physicalVolume_denominator_nonzero
#print axioms geometryRow098_physicalVolume_parse
#print axioms geometryRow098_physicalVolume_read
#print axioms geometryRow098_meanGap_field
#print axioms geometryRow098_meanGap_numerator_no_slash
#print axioms geometryRow098_meanGap_numerator_parse
#print axioms geometryRow098_meanGap_denominator_parse
#print axioms geometryRow098_meanGap_denominator_nonzero
#print axioms geometryRow098_meanGap_parse
#print axioms geometryRow098_meanGap_read
#print axioms geometryRow098_jensenBound_field
#print axioms geometryRow098_jensenBound_numerator_no_slash
#print axioms geometryRow098_jensenBound_numerator_parse
#print axioms geometryRow098_jensenBound_denominator_parse
#print axioms geometryRow098_jensenBound_denominator_nonzero
#print axioms geometryRow098_jensenBound_parse
#print axioms geometryRow098_jensenBound_read
#print axioms geometryRow098_factorMaxima_read
#print axioms geometryRow098_gapWeightedMeans_read
#print axioms geometryRow098_floor_text_read
#print axioms geometryRow098_floor_chars_parse
#print axioms geometryRow098_floor_parse
#print axioms decode_geometry_Rows_098
#print axioms geometryRow099_simplexId_read
#print axioms geometryRow099_vertexIds_read
#print axioms geometryRow099_physicalVolume_field
#print axioms geometryRow099_physicalVolume_numerator_no_slash
#print axioms geometryRow099_physicalVolume_numerator_parse
#print axioms geometryRow099_physicalVolume_denominator_parse
#print axioms geometryRow099_physicalVolume_denominator_nonzero
#print axioms geometryRow099_physicalVolume_parse
#print axioms geometryRow099_physicalVolume_read
#print axioms geometryRow099_meanGap_field
#print axioms geometryRow099_meanGap_numerator_no_slash
#print axioms geometryRow099_meanGap_numerator_parse
#print axioms geometryRow099_meanGap_denominator_parse
#print axioms geometryRow099_meanGap_denominator_nonzero
#print axioms geometryRow099_meanGap_parse
#print axioms geometryRow099_meanGap_read
#print axioms geometryRow099_jensenBound_field
#print axioms geometryRow099_jensenBound_numerator_no_slash
#print axioms geometryRow099_jensenBound_numerator_parse
#print axioms geometryRow099_jensenBound_denominator_parse
#print axioms geometryRow099_jensenBound_denominator_nonzero
#print axioms geometryRow099_jensenBound_parse
#print axioms geometryRow099_jensenBound_read
#print axioms geometryRow099_factorMaxima_read
#print axioms geometryRow099_gapWeightedMeans_read
#print axioms geometryRow099_floor_text_read
#print axioms geometryRow099_floor_chars_parse
#print axioms geometryRow099_floor_parse
#print axioms decode_geometry_Rows_099
#print axioms geometry_Rows_block_050_push_eq
#print axioms geometry_Rows_block_050_reverse
#print axioms decode_geometry_Rows_block_050
#print axioms decode_geometry_Rows_through_block_050

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
