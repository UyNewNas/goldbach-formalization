import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows055

/-! Original simplices typed block 56, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson110 : SourceJson :=
  (SimplicesBlock056.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped110 : GeometryRow :=
  { simplexId := 110,
    vertexIds := #[39, 37, 36, 24, 23, 21, 20, 3, 1],
    physicalVolume := ((342704645021960083314375814322906438699 : ℚ) / (11231016076247040000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((66369109 : ℚ) / (99756000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((27079179717572724629 : ℚ) / (318452608114900000000 : ℚ)), ((260398384064437824843 : ℚ) / (3025299777091550000000 : ℚ)), ((8014669369074734168041 : ℚ) / (54455395987647900000000 : ℚ)), ((3024596011485177197377 : ℚ) / (27227697993823950000000 : ℚ)), ((332038068862061620661 : ℚ) / (6406517175017400000000 : ℚ)), ((625181516620976188067 : ℚ) / (13613848996911975000000 : ℚ)), ((867863569951058099693 : ℚ) / (21782158395059160000000 : ℚ)), ((856232604332886523331 : ℚ) / (21782158395059160000000 : ℚ)), ((2078855880525709960037 : ℚ) / (54455395987647900000000 : ℚ)), ((2078848619806244940317 : ℚ) / (54455395987647900000000 : ℚ))],
    jensenBound := ((10247957311179541156504089732136576625888066073536470976198711156492765672631319662451058025188285976471584492288244739035948188173740074448621255485406570591737440462818841552734375000000000 : ℚ) / (82036855691940109648715999908065149063755925318653142590983071921136486057342498893128118073314864756961116179225048188939789369187505917292035859080454508107485876022692895261359900392026622736203009310099 : ℚ)),
    jensenFloorQ96 := (9897098327832 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_simplexId_before"
  err.flush

theorem geometryRow110_simplexId_read :
    geometryRowsJson110.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped110.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_vertexIds_before"
  err.flush

theorem geometryRow110_vertexIds_read :
    geometryRowsJson110.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped110.vertexIds := by decide +kernel

noncomputable def geometryRow110_physicalVolumeNumeratorChars : List Char := ['3', '4', '2', '7', '0', '4', '6', '4', '5', '0', '2', '1', '9', '6', '0', '0', '8', '3', '3', '1', '4', '3', '7', '5', '8', '1', '4', '3', '2', '2', '9', '0', '6', '4', '3', '8', '6', '9', '9']
noncomputable def geometryRow110_physicalVolumeDenominatorChars : List Char := ['1', '1', '2', '3', '1', '0', '1', '6', '0', '7', '6', '2', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow110_physicalVolumeText : String := String.ofList (geometryRow110_physicalVolumeNumeratorChars ++ '/' :: geometryRow110_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_physicalVolume_before_field"
  err.flush

theorem geometryRow110_physicalVolume_field :
    geometryRowsJson110.getObjVal? "physical_volume" = .ok (.str geometryRow110_physicalVolumeText) := by rfl

theorem geometryRow110_physicalVolume_numerator_no_slash :
    geometryRow110_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow110_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow110_physicalVolumeNumeratorChars = some (342704645021960083314375814322906438699 : Int) := by decide +kernel

theorem geometryRow110_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow110_physicalVolumeDenominatorChars = some (11231016076247040000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow110_physicalVolume_denominator_nonzero : (11231016076247040000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow110_physicalVolume_parse :
    parseRational geometryRow110_physicalVolumeText = .ok geometryRowsTyped110.physicalVolume :=
  original_rational_fraction_of_chars geometryRow110_physicalVolumeNumeratorChars geometryRow110_physicalVolumeDenominatorChars
    (342704645021960083314375814322906438699 : Int) (11231016076247040000000000000000000000000000000000000000000000000 : Int)
    geometryRow110_physicalVolume_numerator_no_slash geometryRow110_physicalVolume_numerator_parse
    geometryRow110_physicalVolume_denominator_parse geometryRow110_physicalVolume_denominator_nonzero

theorem geometryRow110_physicalVolume_read :
    rationalField geometryRowsJson110 "physical_volume" = .ok geometryRowsTyped110.physicalVolume :=
  original_rationalField_of_string geometryRowsJson110 "physical_volume" geometryRow110_physicalVolumeText
    geometryRowsTyped110.physicalVolume geometryRow110_physicalVolume_field geometryRow110_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_physicalVolume_complete"
  err.flush

noncomputable def geometryRow110_meanGapNumeratorChars : List Char := ['6', '6', '3', '6', '9', '1', '0', '9']
noncomputable def geometryRow110_meanGapDenominatorChars : List Char := ['9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow110_meanGapText : String := String.ofList (geometryRow110_meanGapNumeratorChars ++ '/' :: geometryRow110_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_meanGap_before_field"
  err.flush

theorem geometryRow110_meanGap_field :
    geometryRowsJson110.getObjVal? "mean_gap" = .ok (.str geometryRow110_meanGapText) := by rfl

theorem geometryRow110_meanGap_numerator_no_slash :
    geometryRow110_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow110_meanGap_numerator_parse :
    SourceJson.intChars geometryRow110_meanGapNumeratorChars = some (66369109 : Int) := by decide +kernel

theorem geometryRow110_meanGap_denominator_parse :
    SourceJson.intChars geometryRow110_meanGapDenominatorChars = some (99756000000 : Int) := by decide +kernel

theorem geometryRow110_meanGap_denominator_nonzero : (99756000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow110_meanGap_parse :
    parseRational geometryRow110_meanGapText = .ok geometryRowsTyped110.meanGap :=
  original_rational_fraction_of_chars geometryRow110_meanGapNumeratorChars geometryRow110_meanGapDenominatorChars
    (66369109 : Int) (99756000000 : Int)
    geometryRow110_meanGap_numerator_no_slash geometryRow110_meanGap_numerator_parse
    geometryRow110_meanGap_denominator_parse geometryRow110_meanGap_denominator_nonzero

theorem geometryRow110_meanGap_read :
    rationalField geometryRowsJson110 "mean_gap" = .ok geometryRowsTyped110.meanGap :=
  original_rationalField_of_string geometryRowsJson110 "mean_gap" geometryRow110_meanGapText
    geometryRowsTyped110.meanGap geometryRow110_meanGap_field geometryRow110_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_meanGap_complete"
  err.flush

noncomputable def geometryRow110_jensenBoundNumeratorChars : List Char := ['1', '0', '2', '4', '7', '9', '5', '7', '3', '1', '1', '1', '7', '9', '5', '4', '1', '1', '5', '6', '5', '0', '4', '0', '8', '9', '7', '3', '2', '1', '3', '6', '5', '7', '6', '6', '2', '5', '8', '8', '8', '0', '6', '6', '0', '7', '3', '5', '3', '6', '4', '7', '0', '9', '7', '6', '1', '9', '8', '7', '1', '1', '1', '5', '6', '4', '9', '2', '7', '6', '5', '6', '7', '2', '6', '3', '1', '3', '1', '9', '6', '6', '2', '4', '5', '1', '0', '5', '8', '0', '2', '5', '1', '8', '8', '2', '8', '5', '9', '7', '6', '4', '7', '1', '5', '8', '4', '4', '9', '2', '2', '8', '8', '2', '4', '4', '7', '3', '9', '0', '3', '5', '9', '4', '8', '1', '8', '8', '1', '7', '3', '7', '4', '0', '0', '7', '4', '4', '4', '8', '6', '2', '1', '2', '5', '5', '4', '8', '5', '4', '0', '6', '5', '7', '0', '5', '9', '1', '7', '3', '7', '4', '4', '0', '4', '6', '2', '8', '1', '8', '8', '4', '1', '5', '5', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow110_jensenBoundDenominatorChars : List Char := ['8', '2', '0', '3', '6', '8', '5', '5', '6', '9', '1', '9', '4', '0', '1', '0', '9', '6', '4', '8', '7', '1', '5', '9', '9', '9', '9', '0', '8', '0', '6', '5', '1', '4', '9', '0', '6', '3', '7', '5', '5', '9', '2', '5', '3', '1', '8', '6', '5', '3', '1', '4', '2', '5', '9', '0', '9', '8', '3', '0', '7', '1', '9', '2', '1', '1', '3', '6', '4', '8', '6', '0', '5', '7', '3', '4', '2', '4', '9', '8', '8', '9', '3', '1', '2', '8', '1', '1', '8', '0', '7', '3', '3', '1', '4', '8', '6', '4', '7', '5', '6', '9', '6', '1', '1', '1', '6', '1', '7', '9', '2', '2', '5', '0', '4', '8', '1', '8', '8', '9', '3', '9', '7', '8', '9', '3', '6', '9', '1', '8', '7', '5', '0', '5', '9', '1', '7', '2', '9', '2', '0', '3', '5', '8', '5', '9', '0', '8', '0', '4', '5', '4', '5', '0', '8', '1', '0', '7', '4', '8', '5', '8', '7', '6', '0', '2', '2', '6', '9', '2', '8', '9', '5', '2', '6', '1', '3', '5', '9', '9', '0', '0', '3', '9', '2', '0', '2', '6', '6', '2', '2', '7', '3', '6', '2', '0', '3', '0', '0', '9', '3', '1', '0', '0', '9', '9']
noncomputable def geometryRow110_jensenBoundText : String := String.ofList (geometryRow110_jensenBoundNumeratorChars ++ '/' :: geometryRow110_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_jensenBound_before_field"
  err.flush

theorem geometryRow110_jensenBound_field :
    geometryRowsJson110.getObjVal? "jensen_bound" = .ok (.str geometryRow110_jensenBoundText) := by rfl

theorem geometryRow110_jensenBound_numerator_no_slash :
    geometryRow110_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow110_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow110_jensenBoundNumeratorChars = some (10247957311179541156504089732136576625888066073536470976198711156492765672631319662451058025188285976471584492288244739035948188173740074448621255485406570591737440462818841552734375000000000 : Int) := by decide +kernel

theorem geometryRow110_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow110_jensenBoundDenominatorChars = some (82036855691940109648715999908065149063755925318653142590983071921136486057342498893128118073314864756961116179225048188939789369187505917292035859080454508107485876022692895261359900392026622736203009310099 : Int) := by decide +kernel

theorem geometryRow110_jensenBound_denominator_nonzero : (82036855691940109648715999908065149063755925318653142590983071921136486057342498893128118073314864756961116179225048188939789369187505917292035859080454508107485876022692895261359900392026622736203009310099 : Int) ≠ 0 := by decide +kernel

theorem geometryRow110_jensenBound_parse :
    parseRational geometryRow110_jensenBoundText = .ok geometryRowsTyped110.jensenBound :=
  original_rational_fraction_of_chars geometryRow110_jensenBoundNumeratorChars geometryRow110_jensenBoundDenominatorChars
    (10247957311179541156504089732136576625888066073536470976198711156492765672631319662451058025188285976471584492288244739035948188173740074448621255485406570591737440462818841552734375000000000 : Int) (82036855691940109648715999908065149063755925318653142590983071921136486057342498893128118073314864756961116179225048188939789369187505917292035859080454508107485876022692895261359900392026622736203009310099 : Int)
    geometryRow110_jensenBound_numerator_no_slash geometryRow110_jensenBound_numerator_parse
    geometryRow110_jensenBound_denominator_parse geometryRow110_jensenBound_denominator_nonzero

theorem geometryRow110_jensenBound_read :
    rationalField geometryRowsJson110 "jensen_bound" = .ok geometryRowsTyped110.jensenBound :=
  original_rationalField_of_string geometryRowsJson110 "jensen_bound" geometryRow110_jensenBoundText
    geometryRowsTyped110.jensenBound geometryRow110_jensenBound_field geometryRow110_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_factorMaxima_before"
  err.flush

theorem geometryRow110_factorMaxima_read :
    rationalArrayField geometryRowsJson110 "factor_maxima" = .ok geometryRowsTyped110.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_gapWeightedMeans_before"
  err.flush

theorem geometryRow110_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson110 "gap_weighted_means" = .ok geometryRowsTyped110.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow110_floorChars : List Char := ['9', '8', '9', '7', '0', '9', '8', '3', '2', '7', '8', '3', '2']
noncomputable def geometryRow110_floorText : String := String.ofList geometryRow110_floorChars

theorem geometryRow110_floor_text_read :
    geometryRowsJson110.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow110_floorText := by rfl

theorem geometryRow110_floor_chars_parse :
    SourceJson.intChars geometryRow110_floorChars = some (9897098327832 : Int) := by decide +kernel

theorem geometryRow110_floor_parse :
    parseInteger geometryRow110_floorText = .ok geometryRowsTyped110.jensenFloorQ96 := by
  simp only [geometryRow110_floorText, parseInteger, String.toList_ofList, geometryRow110_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_110 :
    decodeGeometryRow geometryRowsJson110 = .ok geometryRowsTyped110 :=
  original_geometryRow_of_fields geometryRowsJson110 geometryRowsTyped110 geometryRow110_floorText
    geometryRow110_simplexId_read geometryRow110_vertexIds_read
    geometryRow110_physicalVolume_read geometryRow110_meanGap_read
    geometryRow110_factorMaxima_read geometryRow110_gapWeightedMeans_read
    geometryRow110_jensenBound_read geometryRow110_floor_text_read geometryRow110_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_110_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson111 : SourceJson :=
  (SimplicesBlock056.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped111 : GeometryRow :=
  { simplexId := 111,
    vertexIds := #[39, 37, 36, 24, 23, 21, 20, 16, 1],
    physicalVolume := ((198109136800799521102227073753521838621 : ℚ) / (35674992242196480000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((294668693468363 : ℚ) / (3668086800000000 : ℚ)), ((295353616413503 : ℚ) / (3668086800000000 : ℚ)), ((1636833750252781 : ℚ) / (11004260400000000 : ℚ)), ((49760152322981 : ℚ) / (458510850000000 : ℚ)), ((546829219937561 : ℚ) / (11004260400000000 : ℚ)), ((506879090291543 : ℚ) / (11004260400000000 : ℚ)), ((965922097801 : ℚ) / (23166864000000 : ℚ)), ((90587415711539 : ℚ) / (2200852080000000 : ℚ)), ((446723107927597 : ℚ) / (11004260400000000 : ℚ)), ((446721640692877 : ℚ) / (11004260400000000 : ℚ))],
    jensenBound := ((116955712429781917221050195175133248296419755118980308032945516077183313866367369035647276184885345377760000000000000000000000 : ℚ) / (34308681934660124900070221981948913129974182978623715498102081663322104353970268725029143697054594784592710613900967189638489866614815594359297 : ℚ)),
    jensenFloorQ96 := (270082838186 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_simplexId_before"
  err.flush

theorem geometryRow111_simplexId_read :
    geometryRowsJson111.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped111.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_vertexIds_before"
  err.flush

theorem geometryRow111_vertexIds_read :
    geometryRowsJson111.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped111.vertexIds := by decide +kernel

noncomputable def geometryRow111_physicalVolumeNumeratorChars : List Char := ['1', '9', '8', '1', '0', '9', '1', '3', '6', '8', '0', '0', '7', '9', '9', '5', '2', '1', '1', '0', '2', '2', '2', '7', '0', '7', '3', '7', '5', '3', '5', '2', '1', '8', '3', '8', '6', '2', '1']
noncomputable def geometryRow111_physicalVolumeDenominatorChars : List Char := ['3', '5', '6', '7', '4', '9', '9', '2', '2', '4', '2', '1', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow111_physicalVolumeText : String := String.ofList (geometryRow111_physicalVolumeNumeratorChars ++ '/' :: geometryRow111_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_physicalVolume_before_field"
  err.flush

theorem geometryRow111_physicalVolume_field :
    geometryRowsJson111.getObjVal? "physical_volume" = .ok (.str geometryRow111_physicalVolumeText) := by rfl

theorem geometryRow111_physicalVolume_numerator_no_slash :
    geometryRow111_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow111_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow111_physicalVolumeNumeratorChars = some (198109136800799521102227073753521838621 : Int) := by decide +kernel

theorem geometryRow111_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow111_physicalVolumeDenominatorChars = some (35674992242196480000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow111_physicalVolume_denominator_nonzero : (35674992242196480000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow111_physicalVolume_parse :
    parseRational geometryRow111_physicalVolumeText = .ok geometryRowsTyped111.physicalVolume :=
  original_rational_fraction_of_chars geometryRow111_physicalVolumeNumeratorChars geometryRow111_physicalVolumeDenominatorChars
    (198109136800799521102227073753521838621 : Int) (35674992242196480000000000000000000000000000000000000000000000000 : Int)
    geometryRow111_physicalVolume_numerator_no_slash geometryRow111_physicalVolume_numerator_parse
    geometryRow111_physicalVolume_denominator_parse geometryRow111_physicalVolume_denominator_nonzero

theorem geometryRow111_physicalVolume_read :
    rationalField geometryRowsJson111 "physical_volume" = .ok geometryRowsTyped111.physicalVolume :=
  original_rationalField_of_string geometryRowsJson111 "physical_volume" geometryRow111_physicalVolumeText
    geometryRowsTyped111.physicalVolume geometryRow111_physicalVolume_field geometryRow111_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_physicalVolume_complete"
  err.flush

noncomputable def geometryRow111_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow111_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow111_meanGapText : String := String.ofList (geometryRow111_meanGapNumeratorChars ++ '/' :: geometryRow111_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_meanGap_before_field"
  err.flush

theorem geometryRow111_meanGap_field :
    geometryRowsJson111.getObjVal? "mean_gap" = .ok (.str geometryRow111_meanGapText) := by rfl

theorem geometryRow111_meanGap_numerator_no_slash :
    geometryRow111_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow111_meanGap_numerator_parse :
    SourceJson.intChars geometryRow111_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow111_meanGap_denominator_parse :
    SourceJson.intChars geometryRow111_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow111_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow111_meanGap_parse :
    parseRational geometryRow111_meanGapText = .ok geometryRowsTyped111.meanGap :=
  original_rational_fraction_of_chars geometryRow111_meanGapNumeratorChars geometryRow111_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow111_meanGap_numerator_no_slash geometryRow111_meanGap_numerator_parse
    geometryRow111_meanGap_denominator_parse geometryRow111_meanGap_denominator_nonzero

theorem geometryRow111_meanGap_read :
    rationalField geometryRowsJson111 "mean_gap" = .ok geometryRowsTyped111.meanGap :=
  original_rationalField_of_string geometryRowsJson111 "mean_gap" geometryRow111_meanGapText
    geometryRowsTyped111.meanGap geometryRow111_meanGap_field geometryRow111_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_meanGap_complete"
  err.flush

noncomputable def geometryRow111_jensenBoundNumeratorChars : List Char := ['1', '1', '6', '9', '5', '5', '7', '1', '2', '4', '2', '9', '7', '8', '1', '9', '1', '7', '2', '2', '1', '0', '5', '0', '1', '9', '5', '1', '7', '5', '1', '3', '3', '2', '4', '8', '2', '9', '6', '4', '1', '9', '7', '5', '5', '1', '1', '8', '9', '8', '0', '3', '0', '8', '0', '3', '2', '9', '4', '5', '5', '1', '6', '0', '7', '7', '1', '8', '3', '3', '1', '3', '8', '6', '6', '3', '6', '7', '3', '6', '9', '0', '3', '5', '6', '4', '7', '2', '7', '6', '1', '8', '4', '8', '8', '5', '3', '4', '5', '3', '7', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow111_jensenBoundDenominatorChars : List Char := ['3', '4', '3', '0', '8', '6', '8', '1', '9', '3', '4', '6', '6', '0', '1', '2', '4', '9', '0', '0', '0', '7', '0', '2', '2', '1', '9', '8', '1', '9', '4', '8', '9', '1', '3', '1', '2', '9', '9', '7', '4', '1', '8', '2', '9', '7', '8', '6', '2', '3', '7', '1', '5', '4', '9', '8', '1', '0', '2', '0', '8', '1', '6', '6', '3', '3', '2', '2', '1', '0', '4', '3', '5', '3', '9', '7', '0', '2', '6', '8', '7', '2', '5', '0', '2', '9', '1', '4', '3', '6', '9', '7', '0', '5', '4', '5', '9', '4', '7', '8', '4', '5', '9', '2', '7', '1', '0', '6', '1', '3', '9', '0', '0', '9', '6', '7', '1', '8', '9', '6', '3', '8', '4', '8', '9', '8', '6', '6', '6', '1', '4', '8', '1', '5', '5', '9', '4', '3', '5', '9', '2', '9', '7']
noncomputable def geometryRow111_jensenBoundText : String := String.ofList (geometryRow111_jensenBoundNumeratorChars ++ '/' :: geometryRow111_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_jensenBound_before_field"
  err.flush

theorem geometryRow111_jensenBound_field :
    geometryRowsJson111.getObjVal? "jensen_bound" = .ok (.str geometryRow111_jensenBoundText) := by rfl

theorem geometryRow111_jensenBound_numerator_no_slash :
    geometryRow111_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow111_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow111_jensenBoundNumeratorChars = some (116955712429781917221050195175133248296419755118980308032945516077183313866367369035647276184885345377760000000000000000000000 : Int) := by decide +kernel

theorem geometryRow111_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow111_jensenBoundDenominatorChars = some (34308681934660124900070221981948913129974182978623715498102081663322104353970268725029143697054594784592710613900967189638489866614815594359297 : Int) := by decide +kernel

theorem geometryRow111_jensenBound_denominator_nonzero : (34308681934660124900070221981948913129974182978623715498102081663322104353970268725029143697054594784592710613900967189638489866614815594359297 : Int) ≠ 0 := by decide +kernel

theorem geometryRow111_jensenBound_parse :
    parseRational geometryRow111_jensenBoundText = .ok geometryRowsTyped111.jensenBound :=
  original_rational_fraction_of_chars geometryRow111_jensenBoundNumeratorChars geometryRow111_jensenBoundDenominatorChars
    (116955712429781917221050195175133248296419755118980308032945516077183313866367369035647276184885345377760000000000000000000000 : Int) (34308681934660124900070221981948913129974182978623715498102081663322104353970268725029143697054594784592710613900967189638489866614815594359297 : Int)
    geometryRow111_jensenBound_numerator_no_slash geometryRow111_jensenBound_numerator_parse
    geometryRow111_jensenBound_denominator_parse geometryRow111_jensenBound_denominator_nonzero

theorem geometryRow111_jensenBound_read :
    rationalField geometryRowsJson111 "jensen_bound" = .ok geometryRowsTyped111.jensenBound :=
  original_rationalField_of_string geometryRowsJson111 "jensen_bound" geometryRow111_jensenBoundText
    geometryRowsTyped111.jensenBound geometryRow111_jensenBound_field geometryRow111_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_factorMaxima_before"
  err.flush

theorem geometryRow111_factorMaxima_read :
    rationalArrayField geometryRowsJson111 "factor_maxima" = .ok geometryRowsTyped111.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_gapWeightedMeans_before"
  err.flush

theorem geometryRow111_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson111 "gap_weighted_means" = .ok geometryRowsTyped111.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow111_floorChars : List Char := ['2', '7', '0', '0', '8', '2', '8', '3', '8', '1', '8', '6']
noncomputable def geometryRow111_floorText : String := String.ofList geometryRow111_floorChars

theorem geometryRow111_floor_text_read :
    geometryRowsJson111.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow111_floorText := by rfl

theorem geometryRow111_floor_chars_parse :
    SourceJson.intChars geometryRow111_floorChars = some (270082838186 : Int) := by decide +kernel

theorem geometryRow111_floor_parse :
    parseInteger geometryRow111_floorText = .ok geometryRowsTyped111.jensenFloorQ96 := by
  simp only [geometryRow111_floorText, parseInteger, String.toList_ofList, geometryRow111_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_111 :
    decodeGeometryRow geometryRowsJson111 = .ok geometryRowsTyped111 :=
  original_geometryRow_of_fields geometryRowsJson111 geometryRowsTyped111 geometryRow111_floorText
    geometryRow111_simplexId_read geometryRow111_vertexIds_read
    geometryRow111_physicalVolume_read geometryRow111_meanGap_read
    geometryRow111_factorMaxima_read geometryRow111_gapWeightedMeans_read
    geometryRow111_jensenBound_read geometryRow111_floor_text_read geometryRow111_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_111_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock056 : List SourceJson := [geometryRowsJson110, geometryRowsJson111]
noncomputable def geometryRowsTypedBlock056 : List (GeometryRow) := [geometryRowsTyped110, geometryRowsTyped111]
noncomputable def geometryRowsTypedThroughBlock056 : List (GeometryRow) := geometryRowsTypedThroughBlock055 ++ geometryRowsTypedBlock056

theorem geometry_Rows_block_056_push_eq (acc : List SourceJson) :
    SimplicesBlock056.blockPush acc = [geometryRowsJson111, geometryRowsJson110] ++ acc := by rfl

theorem geometry_Rows_block_056_reverse (acc : List SourceJson) :
    (SimplicesBlock056.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock056 := by
  rw [geometry_Rows_block_056_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_056 :
    geometryRowsJsonBlock056.mapM decodeGeometryRow = .ok geometryRowsTypedBlock056 := by
  simp only [geometryRowsJsonBlock056, geometryRowsTypedBlock056, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_110, decode_geometry_Rows_111]
  rfl

theorem decode_geometry_Rows_through_block_056 :
    SimplicesValue.arrayAcc057.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock056 := by
  change (SimplicesBlock056.blockPush SimplicesValue.arrayAcc056).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_056_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_055, decode_geometry_Rows_block_056]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_056_complete"
  err.flush

#print axioms geometryRow110_simplexId_read
#print axioms geometryRow110_vertexIds_read
#print axioms geometryRow110_physicalVolume_field
#print axioms geometryRow110_physicalVolume_numerator_no_slash
#print axioms geometryRow110_physicalVolume_numerator_parse
#print axioms geometryRow110_physicalVolume_denominator_parse
#print axioms geometryRow110_physicalVolume_denominator_nonzero
#print axioms geometryRow110_physicalVolume_parse
#print axioms geometryRow110_physicalVolume_read
#print axioms geometryRow110_meanGap_field
#print axioms geometryRow110_meanGap_numerator_no_slash
#print axioms geometryRow110_meanGap_numerator_parse
#print axioms geometryRow110_meanGap_denominator_parse
#print axioms geometryRow110_meanGap_denominator_nonzero
#print axioms geometryRow110_meanGap_parse
#print axioms geometryRow110_meanGap_read
#print axioms geometryRow110_jensenBound_field
#print axioms geometryRow110_jensenBound_numerator_no_slash
#print axioms geometryRow110_jensenBound_numerator_parse
#print axioms geometryRow110_jensenBound_denominator_parse
#print axioms geometryRow110_jensenBound_denominator_nonzero
#print axioms geometryRow110_jensenBound_parse
#print axioms geometryRow110_jensenBound_read
#print axioms geometryRow110_factorMaxima_read
#print axioms geometryRow110_gapWeightedMeans_read
#print axioms geometryRow110_floor_text_read
#print axioms geometryRow110_floor_chars_parse
#print axioms geometryRow110_floor_parse
#print axioms decode_geometry_Rows_110
#print axioms geometryRow111_simplexId_read
#print axioms geometryRow111_vertexIds_read
#print axioms geometryRow111_physicalVolume_field
#print axioms geometryRow111_physicalVolume_numerator_no_slash
#print axioms geometryRow111_physicalVolume_numerator_parse
#print axioms geometryRow111_physicalVolume_denominator_parse
#print axioms geometryRow111_physicalVolume_denominator_nonzero
#print axioms geometryRow111_physicalVolume_parse
#print axioms geometryRow111_physicalVolume_read
#print axioms geometryRow111_meanGap_field
#print axioms geometryRow111_meanGap_numerator_no_slash
#print axioms geometryRow111_meanGap_numerator_parse
#print axioms geometryRow111_meanGap_denominator_parse
#print axioms geometryRow111_meanGap_denominator_nonzero
#print axioms geometryRow111_meanGap_parse
#print axioms geometryRow111_meanGap_read
#print axioms geometryRow111_jensenBound_field
#print axioms geometryRow111_jensenBound_numerator_no_slash
#print axioms geometryRow111_jensenBound_numerator_parse
#print axioms geometryRow111_jensenBound_denominator_parse
#print axioms geometryRow111_jensenBound_denominator_nonzero
#print axioms geometryRow111_jensenBound_parse
#print axioms geometryRow111_jensenBound_read
#print axioms geometryRow111_factorMaxima_read
#print axioms geometryRow111_gapWeightedMeans_read
#print axioms geometryRow111_floor_text_read
#print axioms geometryRow111_floor_chars_parse
#print axioms geometryRow111_floor_parse
#print axioms decode_geometry_Rows_111
#print axioms geometry_Rows_block_056_push_eq
#print axioms geometry_Rows_block_056_reverse
#print axioms decode_geometry_Rows_block_056
#print axioms decode_geometry_Rows_through_block_056

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
