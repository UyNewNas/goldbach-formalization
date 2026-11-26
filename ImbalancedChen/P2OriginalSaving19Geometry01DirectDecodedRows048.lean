import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows047

/-! Original simplices typed block 48, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson094 : SourceJson :=
  (SimplicesBlock048.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped094 : GeometryRow :=
  { simplexId := 94,
    vertexIds := #[39, 37, 24, 23, 21, 20, 19, 15, 0],
    physicalVolume := ((1135914692489892485673994674182544442880957 : ℚ) / (186610461820108973015040000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((91924997 : ℚ) / (407826000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((4779971649874428290447 : ℚ) / (62326133861592825000000 : ℚ)), ((38391816664936877485171 : ℚ) / (498609070892742600000000 : ℚ)), ((219972243415472337493337 : ℚ) / (1495827212678227800000000 : ℚ)), ((52860615668134423371101 : ℚ) / (498609070892742600000000 : ℚ)), ((19243634170890225985453 : ℚ) / (373956803169556950000000 : ℚ)), ((71072523753567172894291 : ℚ) / (1495827212678227800000000 : ℚ)), ((674390823805191619951 : ℚ) / (15745549607139240000000 : ℚ)), ((12653681015740197119227 : ℚ) / (299165442535645560000000 : ℚ)), ((62474337268306371483659 : ℚ) / (1495827212678227800000000 : ℚ)), ((15576412215285782701301 : ℚ) / (373956803169556950000000 : ℚ))],
    jensenBound := ((13441022735066212850387090276370527978827430741367176737840819678038928265522375977262325755600977604351436341689535918632744449123069246872847467445069395174588387536714519769219669723510742187500000000000 : ℚ) / (1737430593111099745266727212658391261205189349369273174135841711480148540829165010216736368186635441207478568561192744858832642343156605674312631457423020926839011886099311446447432121182024548180631727010549475426701209 : ℚ)),
    jensenFloorQ96 := (612920906212943 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_simplexId_before"
  err.flush

theorem geometryRow094_simplexId_read :
    geometryRowsJson094.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped094.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_vertexIds_before"
  err.flush

theorem geometryRow094_vertexIds_read :
    geometryRowsJson094.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped094.vertexIds := by decide +kernel

noncomputable def geometryRow094_physicalVolumeNumeratorChars : List Char := ['1', '1', '3', '5', '9', '1', '4', '6', '9', '2', '4', '8', '9', '8', '9', '2', '4', '8', '5', '6', '7', '3', '9', '9', '4', '6', '7', '4', '1', '8', '2', '5', '4', '4', '4', '4', '2', '8', '8', '0', '9', '5', '7']
noncomputable def geometryRow094_physicalVolumeDenominatorChars : List Char := ['1', '8', '6', '6', '1', '0', '4', '6', '1', '8', '2', '0', '1', '0', '8', '9', '7', '3', '0', '1', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow094_physicalVolumeText : String := String.ofList (geometryRow094_physicalVolumeNumeratorChars ++ '/' :: geometryRow094_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_physicalVolume_before_field"
  err.flush

theorem geometryRow094_physicalVolume_field :
    geometryRowsJson094.getObjVal? "physical_volume" = .ok (.str geometryRow094_physicalVolumeText) := by rfl

theorem geometryRow094_physicalVolume_numerator_no_slash :
    geometryRow094_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow094_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow094_physicalVolumeNumeratorChars = some (1135914692489892485673994674182544442880957 : Int) := by decide +kernel

theorem geometryRow094_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow094_physicalVolumeDenominatorChars = some (186610461820108973015040000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow094_physicalVolume_denominator_nonzero : (186610461820108973015040000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow094_physicalVolume_parse :
    parseRational geometryRow094_physicalVolumeText = .ok geometryRowsTyped094.physicalVolume :=
  original_rational_fraction_of_chars geometryRow094_physicalVolumeNumeratorChars geometryRow094_physicalVolumeDenominatorChars
    (1135914692489892485673994674182544442880957 : Int) (186610461820108973015040000000000000000000000000000000000000000000 : Int)
    geometryRow094_physicalVolume_numerator_no_slash geometryRow094_physicalVolume_numerator_parse
    geometryRow094_physicalVolume_denominator_parse geometryRow094_physicalVolume_denominator_nonzero

theorem geometryRow094_physicalVolume_read :
    rationalField geometryRowsJson094 "physical_volume" = .ok geometryRowsTyped094.physicalVolume :=
  original_rationalField_of_string geometryRowsJson094 "physical_volume" geometryRow094_physicalVolumeText
    geometryRowsTyped094.physicalVolume geometryRow094_physicalVolume_field geometryRow094_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_physicalVolume_complete"
  err.flush

noncomputable def geometryRow094_meanGapNumeratorChars : List Char := ['9', '1', '9', '2', '4', '9', '9', '7']
noncomputable def geometryRow094_meanGapDenominatorChars : List Char := ['4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow094_meanGapText : String := String.ofList (geometryRow094_meanGapNumeratorChars ++ '/' :: geometryRow094_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_meanGap_before_field"
  err.flush

theorem geometryRow094_meanGap_field :
    geometryRowsJson094.getObjVal? "mean_gap" = .ok (.str geometryRow094_meanGapText) := by rfl

theorem geometryRow094_meanGap_numerator_no_slash :
    geometryRow094_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow094_meanGap_numerator_parse :
    SourceJson.intChars geometryRow094_meanGapNumeratorChars = some (91924997 : Int) := by decide +kernel

theorem geometryRow094_meanGap_denominator_parse :
    SourceJson.intChars geometryRow094_meanGapDenominatorChars = some (407826000000 : Int) := by decide +kernel

theorem geometryRow094_meanGap_denominator_nonzero : (407826000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow094_meanGap_parse :
    parseRational geometryRow094_meanGapText = .ok geometryRowsTyped094.meanGap :=
  original_rational_fraction_of_chars geometryRow094_meanGapNumeratorChars geometryRow094_meanGapDenominatorChars
    (91924997 : Int) (407826000000 : Int)
    geometryRow094_meanGap_numerator_no_slash geometryRow094_meanGap_numerator_parse
    geometryRow094_meanGap_denominator_parse geometryRow094_meanGap_denominator_nonzero

theorem geometryRow094_meanGap_read :
    rationalField geometryRowsJson094 "mean_gap" = .ok geometryRowsTyped094.meanGap :=
  original_rationalField_of_string geometryRowsJson094 "mean_gap" geometryRow094_meanGapText
    geometryRowsTyped094.meanGap geometryRow094_meanGap_field geometryRow094_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_meanGap_complete"
  err.flush

noncomputable def geometryRow094_jensenBoundNumeratorChars : List Char := ['1', '3', '4', '4', '1', '0', '2', '2', '7', '3', '5', '0', '6', '6', '2', '1', '2', '8', '5', '0', '3', '8', '7', '0', '9', '0', '2', '7', '6', '3', '7', '0', '5', '2', '7', '9', '7', '8', '8', '2', '7', '4', '3', '0', '7', '4', '1', '3', '6', '7', '1', '7', '6', '7', '3', '7', '8', '4', '0', '8', '1', '9', '6', '7', '8', '0', '3', '8', '9', '2', '8', '2', '6', '5', '5', '2', '2', '3', '7', '5', '9', '7', '7', '2', '6', '2', '3', '2', '5', '7', '5', '5', '6', '0', '0', '9', '7', '7', '6', '0', '4', '3', '5', '1', '4', '3', '6', '3', '4', '1', '6', '8', '9', '5', '3', '5', '9', '1', '8', '6', '3', '2', '7', '4', '4', '4', '4', '9', '1', '2', '3', '0', '6', '9', '2', '4', '6', '8', '7', '2', '8', '4', '7', '4', '6', '7', '4', '4', '5', '0', '6', '9', '3', '9', '5', '1', '7', '4', '5', '8', '8', '3', '8', '7', '5', '3', '6', '7', '1', '4', '5', '1', '9', '7', '6', '9', '2', '1', '9', '6', '6', '9', '7', '2', '3', '5', '1', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow094_jensenBoundDenominatorChars : List Char := ['1', '7', '3', '7', '4', '3', '0', '5', '9', '3', '1', '1', '1', '0', '9', '9', '7', '4', '5', '2', '6', '6', '7', '2', '7', '2', '1', '2', '6', '5', '8', '3', '9', '1', '2', '6', '1', '2', '0', '5', '1', '8', '9', '3', '4', '9', '3', '6', '9', '2', '7', '3', '1', '7', '4', '1', '3', '5', '8', '4', '1', '7', '1', '1', '4', '8', '0', '1', '4', '8', '5', '4', '0', '8', '2', '9', '1', '6', '5', '0', '1', '0', '2', '1', '6', '7', '3', '6', '3', '6', '8', '1', '8', '6', '6', '3', '5', '4', '4', '1', '2', '0', '7', '4', '7', '8', '5', '6', '8', '5', '6', '1', '1', '9', '2', '7', '4', '4', '8', '5', '8', '8', '3', '2', '6', '4', '2', '3', '4', '3', '1', '5', '6', '6', '0', '5', '6', '7', '4', '3', '1', '2', '6', '3', '1', '4', '5', '7', '4', '2', '3', '0', '2', '0', '9', '2', '6', '8', '3', '9', '0', '1', '1', '8', '8', '6', '0', '9', '9', '3', '1', '1', '4', '4', '6', '4', '4', '7', '4', '3', '2', '1', '2', '1', '1', '8', '2', '0', '2', '4', '5', '4', '8', '1', '8', '0', '6', '3', '1', '7', '2', '7', '0', '1', '0', '5', '4', '9', '4', '7', '5', '4', '2', '6', '7', '0', '1', '2', '0', '9']
noncomputable def geometryRow094_jensenBoundText : String := String.ofList (geometryRow094_jensenBoundNumeratorChars ++ '/' :: geometryRow094_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_jensenBound_before_field"
  err.flush

theorem geometryRow094_jensenBound_field :
    geometryRowsJson094.getObjVal? "jensen_bound" = .ok (.str geometryRow094_jensenBoundText) := by rfl

theorem geometryRow094_jensenBound_numerator_no_slash :
    geometryRow094_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow094_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow094_jensenBoundNumeratorChars = some (13441022735066212850387090276370527978827430741367176737840819678038928265522375977262325755600977604351436341689535918632744449123069246872847467445069395174588387536714519769219669723510742187500000000000 : Int) := by decide +kernel

theorem geometryRow094_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow094_jensenBoundDenominatorChars = some (1737430593111099745266727212658391261205189349369273174135841711480148540829165010216736368186635441207478568561192744858832642343156605674312631457423020926839011886099311446447432121182024548180631727010549475426701209 : Int) := by decide +kernel

theorem geometryRow094_jensenBound_denominator_nonzero : (1737430593111099745266727212658391261205189349369273174135841711480148540829165010216736368186635441207478568561192744858832642343156605674312631457423020926839011886099311446447432121182024548180631727010549475426701209 : Int) ≠ 0 := by decide +kernel

theorem geometryRow094_jensenBound_parse :
    parseRational geometryRow094_jensenBoundText = .ok geometryRowsTyped094.jensenBound :=
  original_rational_fraction_of_chars geometryRow094_jensenBoundNumeratorChars geometryRow094_jensenBoundDenominatorChars
    (13441022735066212850387090276370527978827430741367176737840819678038928265522375977262325755600977604351436341689535918632744449123069246872847467445069395174588387536714519769219669723510742187500000000000 : Int) (1737430593111099745266727212658391261205189349369273174135841711480148540829165010216736368186635441207478568561192744858832642343156605674312631457423020926839011886099311446447432121182024548180631727010549475426701209 : Int)
    geometryRow094_jensenBound_numerator_no_slash geometryRow094_jensenBound_numerator_parse
    geometryRow094_jensenBound_denominator_parse geometryRow094_jensenBound_denominator_nonzero

theorem geometryRow094_jensenBound_read :
    rationalField geometryRowsJson094 "jensen_bound" = .ok geometryRowsTyped094.jensenBound :=
  original_rationalField_of_string geometryRowsJson094 "jensen_bound" geometryRow094_jensenBoundText
    geometryRowsTyped094.jensenBound geometryRow094_jensenBound_field geometryRow094_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_factorMaxima_before"
  err.flush

theorem geometryRow094_factorMaxima_read :
    rationalArrayField geometryRowsJson094 "factor_maxima" = .ok geometryRowsTyped094.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_gapWeightedMeans_before"
  err.flush

theorem geometryRow094_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson094 "gap_weighted_means" = .ok geometryRowsTyped094.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow094_floorChars : List Char := ['6', '1', '2', '9', '2', '0', '9', '0', '6', '2', '1', '2', '9', '4', '3']
noncomputable def geometryRow094_floorText : String := String.ofList geometryRow094_floorChars

theorem geometryRow094_floor_text_read :
    geometryRowsJson094.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow094_floorText := by rfl

theorem geometryRow094_floor_chars_parse :
    SourceJson.intChars geometryRow094_floorChars = some (612920906212943 : Int) := by decide +kernel

theorem geometryRow094_floor_parse :
    parseInteger geometryRow094_floorText = .ok geometryRowsTyped094.jensenFloorQ96 := by
  simp only [geometryRow094_floorText, parseInteger, String.toList_ofList, geometryRow094_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_094 :
    decodeGeometryRow geometryRowsJson094 = .ok geometryRowsTyped094 :=
  original_geometryRow_of_fields geometryRowsJson094 geometryRowsTyped094 geometryRow094_floorText
    geometryRow094_simplexId_read geometryRow094_vertexIds_read
    geometryRow094_physicalVolume_read geometryRow094_meanGap_read
    geometryRow094_factorMaxima_read geometryRow094_gapWeightedMeans_read
    geometryRow094_jensenBound_read geometryRow094_floor_text_read geometryRow094_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_094_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson095 : SourceJson :=
  (SimplicesBlock048.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped095 : GeometryRow :=
  { simplexId := 95,
    vertexIds := #[39, 37, 24, 23, 21, 19, 6, 2, 0],
    physicalVolume := ((170790526174494330392742176908967589574613473 : ℚ) / (375739612080537600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((34630061 : ℚ) / (49039200000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((600971303037768727063 : ℚ) / (7221522977334960000000 : ℚ)), ((21309456189894731026601 : ℚ) / (252753304206723600000000 : ℚ)), ((7321790084057568408089 : ℚ) / (50550660841344720000000 : ℚ)), ((8301094390645710483197 : ℚ) / (75825991262017080000000 : ℚ)), ((2752225007761306268501 : ℚ) / (50550660841344720000000 : ℚ)), ((2397324096988498911271 : ℚ) / (50550660841344720000000 : ℚ)), ((321099704418014995229 : ℚ) / (7981683290738640000000 : ℚ)), ((6019917147312479956739 : ℚ) / (151651982524034160000000 : ℚ)), ((29766049078455040465909 : ℚ) / (758259912620170800000000 : ℚ)), ((28470187375668615107341 : ℚ) / (758259912620170800000000 : ℚ))],
    jensenBound := ((15975324527608984912311616286112035267298719988878252068306330493215328808515763051915168021239524773043881122096743819358048244803220870276107597417099719308722158599892494751170941865984000000000000000000 : ℚ) / (8412621570706899431904035166825245580777945721173879073559710023335185776918029168429970759526207765061061627308408606818024666416157027648283971918805598571776107153479248461737267041066678860325256310934391216251751 : ℚ)),
    jensenFloorQ96 := (150451984230304964 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_simplexId_before"
  err.flush

theorem geometryRow095_simplexId_read :
    geometryRowsJson095.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped095.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_vertexIds_before"
  err.flush

theorem geometryRow095_vertexIds_read :
    geometryRowsJson095.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped095.vertexIds := by decide +kernel

noncomputable def geometryRow095_physicalVolumeNumeratorChars : List Char := ['1', '7', '0', '7', '9', '0', '5', '2', '6', '1', '7', '4', '4', '9', '4', '3', '3', '0', '3', '9', '2', '7', '4', '2', '1', '7', '6', '9', '0', '8', '9', '6', '7', '5', '8', '9', '5', '7', '4', '6', '1', '3', '4', '7', '3']
noncomputable def geometryRow095_physicalVolumeDenominatorChars : List Char := ['3', '7', '5', '7', '3', '9', '6', '1', '2', '0', '8', '0', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow095_physicalVolumeText : String := String.ofList (geometryRow095_physicalVolumeNumeratorChars ++ '/' :: geometryRow095_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_physicalVolume_before_field"
  err.flush

theorem geometryRow095_physicalVolume_field :
    geometryRowsJson095.getObjVal? "physical_volume" = .ok (.str geometryRow095_physicalVolumeText) := by rfl

theorem geometryRow095_physicalVolume_numerator_no_slash :
    geometryRow095_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow095_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow095_physicalVolumeNumeratorChars = some (170790526174494330392742176908967589574613473 : Int) := by decide +kernel

theorem geometryRow095_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow095_physicalVolumeDenominatorChars = some (375739612080537600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow095_physicalVolume_denominator_nonzero : (375739612080537600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow095_physicalVolume_parse :
    parseRational geometryRow095_physicalVolumeText = .ok geometryRowsTyped095.physicalVolume :=
  original_rational_fraction_of_chars geometryRow095_physicalVolumeNumeratorChars geometryRow095_physicalVolumeDenominatorChars
    (170790526174494330392742176908967589574613473 : Int) (375739612080537600000000000000000000000000000000000000000000000000 : Int)
    geometryRow095_physicalVolume_numerator_no_slash geometryRow095_physicalVolume_numerator_parse
    geometryRow095_physicalVolume_denominator_parse geometryRow095_physicalVolume_denominator_nonzero

theorem geometryRow095_physicalVolume_read :
    rationalField geometryRowsJson095 "physical_volume" = .ok geometryRowsTyped095.physicalVolume :=
  original_rationalField_of_string geometryRowsJson095 "physical_volume" geometryRow095_physicalVolumeText
    geometryRowsTyped095.physicalVolume geometryRow095_physicalVolume_field geometryRow095_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_physicalVolume_complete"
  err.flush

noncomputable def geometryRow095_meanGapNumeratorChars : List Char := ['3', '4', '6', '3', '0', '0', '6', '1']
noncomputable def geometryRow095_meanGapDenominatorChars : List Char := ['4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0']
noncomputable def geometryRow095_meanGapText : String := String.ofList (geometryRow095_meanGapNumeratorChars ++ '/' :: geometryRow095_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_meanGap_before_field"
  err.flush

theorem geometryRow095_meanGap_field :
    geometryRowsJson095.getObjVal? "mean_gap" = .ok (.str geometryRow095_meanGapText) := by rfl

theorem geometryRow095_meanGap_numerator_no_slash :
    geometryRow095_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow095_meanGap_numerator_parse :
    SourceJson.intChars geometryRow095_meanGapNumeratorChars = some (34630061 : Int) := by decide +kernel

theorem geometryRow095_meanGap_denominator_parse :
    SourceJson.intChars geometryRow095_meanGapDenominatorChars = some (49039200000 : Int) := by decide +kernel

theorem geometryRow095_meanGap_denominator_nonzero : (49039200000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow095_meanGap_parse :
    parseRational geometryRow095_meanGapText = .ok geometryRowsTyped095.meanGap :=
  original_rational_fraction_of_chars geometryRow095_meanGapNumeratorChars geometryRow095_meanGapDenominatorChars
    (34630061 : Int) (49039200000 : Int)
    geometryRow095_meanGap_numerator_no_slash geometryRow095_meanGap_numerator_parse
    geometryRow095_meanGap_denominator_parse geometryRow095_meanGap_denominator_nonzero

theorem geometryRow095_meanGap_read :
    rationalField geometryRowsJson095 "mean_gap" = .ok geometryRowsTyped095.meanGap :=
  original_rationalField_of_string geometryRowsJson095 "mean_gap" geometryRow095_meanGapText
    geometryRowsTyped095.meanGap geometryRow095_meanGap_field geometryRow095_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_meanGap_complete"
  err.flush

noncomputable def geometryRow095_jensenBoundNumeratorChars : List Char := ['1', '5', '9', '7', '5', '3', '2', '4', '5', '2', '7', '6', '0', '8', '9', '8', '4', '9', '1', '2', '3', '1', '1', '6', '1', '6', '2', '8', '6', '1', '1', '2', '0', '3', '5', '2', '6', '7', '2', '9', '8', '7', '1', '9', '9', '8', '8', '8', '7', '8', '2', '5', '2', '0', '6', '8', '3', '0', '6', '3', '3', '0', '4', '9', '3', '2', '1', '5', '3', '2', '8', '8', '0', '8', '5', '1', '5', '7', '6', '3', '0', '5', '1', '9', '1', '5', '1', '6', '8', '0', '2', '1', '2', '3', '9', '5', '2', '4', '7', '7', '3', '0', '4', '3', '8', '8', '1', '1', '2', '2', '0', '9', '6', '7', '4', '3', '8', '1', '9', '3', '5', '8', '0', '4', '8', '2', '4', '4', '8', '0', '3', '2', '2', '0', '8', '7', '0', '2', '7', '6', '1', '0', '7', '5', '9', '7', '4', '1', '7', '0', '9', '9', '7', '1', '9', '3', '0', '8', '7', '2', '2', '1', '5', '8', '5', '9', '9', '8', '9', '2', '4', '9', '4', '7', '5', '1', '1', '7', '0', '9', '4', '1', '8', '6', '5', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow095_jensenBoundDenominatorChars : List Char := ['8', '4', '1', '2', '6', '2', '1', '5', '7', '0', '7', '0', '6', '8', '9', '9', '4', '3', '1', '9', '0', '4', '0', '3', '5', '1', '6', '6', '8', '2', '5', '2', '4', '5', '5', '8', '0', '7', '7', '7', '9', '4', '5', '7', '2', '1', '1', '7', '3', '8', '7', '9', '0', '7', '3', '5', '5', '9', '7', '1', '0', '0', '2', '3', '3', '3', '5', '1', '8', '5', '7', '7', '6', '9', '1', '8', '0', '2', '9', '1', '6', '8', '4', '2', '9', '9', '7', '0', '7', '5', '9', '5', '2', '6', '2', '0', '7', '7', '6', '5', '0', '6', '1', '0', '6', '1', '6', '2', '7', '3', '0', '8', '4', '0', '8', '6', '0', '6', '8', '1', '8', '0', '2', '4', '6', '6', '6', '4', '1', '6', '1', '5', '7', '0', '2', '7', '6', '4', '8', '2', '8', '3', '9', '7', '1', '9', '1', '8', '8', '0', '5', '5', '9', '8', '5', '7', '1', '7', '7', '6', '1', '0', '7', '1', '5', '3', '4', '7', '9', '2', '4', '8', '4', '6', '1', '7', '3', '7', '2', '6', '7', '0', '4', '1', '0', '6', '6', '6', '7', '8', '8', '6', '0', '3', '2', '5', '2', '5', '6', '3', '1', '0', '9', '3', '4', '3', '9', '1', '2', '1', '6', '2', '5', '1', '7', '5', '1']
noncomputable def geometryRow095_jensenBoundText : String := String.ofList (geometryRow095_jensenBoundNumeratorChars ++ '/' :: geometryRow095_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_jensenBound_before_field"
  err.flush

theorem geometryRow095_jensenBound_field :
    geometryRowsJson095.getObjVal? "jensen_bound" = .ok (.str geometryRow095_jensenBoundText) := by rfl

theorem geometryRow095_jensenBound_numerator_no_slash :
    geometryRow095_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow095_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow095_jensenBoundNumeratorChars = some (15975324527608984912311616286112035267298719988878252068306330493215328808515763051915168021239524773043881122096743819358048244803220870276107597417099719308722158599892494751170941865984000000000000000000 : Int) := by decide +kernel

theorem geometryRow095_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow095_jensenBoundDenominatorChars = some (8412621570706899431904035166825245580777945721173879073559710023335185776918029168429970759526207765061061627308408606818024666416157027648283971918805598571776107153479248461737267041066678860325256310934391216251751 : Int) := by decide +kernel

theorem geometryRow095_jensenBound_denominator_nonzero : (8412621570706899431904035166825245580777945721173879073559710023335185776918029168429970759526207765061061627308408606818024666416157027648283971918805598571776107153479248461737267041066678860325256310934391216251751 : Int) ≠ 0 := by decide +kernel

theorem geometryRow095_jensenBound_parse :
    parseRational geometryRow095_jensenBoundText = .ok geometryRowsTyped095.jensenBound :=
  original_rational_fraction_of_chars geometryRow095_jensenBoundNumeratorChars geometryRow095_jensenBoundDenominatorChars
    (15975324527608984912311616286112035267298719988878252068306330493215328808515763051915168021239524773043881122096743819358048244803220870276107597417099719308722158599892494751170941865984000000000000000000 : Int) (8412621570706899431904035166825245580777945721173879073559710023335185776918029168429970759526207765061061627308408606818024666416157027648283971918805598571776107153479248461737267041066678860325256310934391216251751 : Int)
    geometryRow095_jensenBound_numerator_no_slash geometryRow095_jensenBound_numerator_parse
    geometryRow095_jensenBound_denominator_parse geometryRow095_jensenBound_denominator_nonzero

theorem geometryRow095_jensenBound_read :
    rationalField geometryRowsJson095 "jensen_bound" = .ok geometryRowsTyped095.jensenBound :=
  original_rationalField_of_string geometryRowsJson095 "jensen_bound" geometryRow095_jensenBoundText
    geometryRowsTyped095.jensenBound geometryRow095_jensenBound_field geometryRow095_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_factorMaxima_before"
  err.flush

theorem geometryRow095_factorMaxima_read :
    rationalArrayField geometryRowsJson095 "factor_maxima" = .ok geometryRowsTyped095.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_gapWeightedMeans_before"
  err.flush

theorem geometryRow095_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson095 "gap_weighted_means" = .ok geometryRowsTyped095.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow095_floorChars : List Char := ['1', '5', '0', '4', '5', '1', '9', '8', '4', '2', '3', '0', '3', '0', '4', '9', '6', '4']
noncomputable def geometryRow095_floorText : String := String.ofList geometryRow095_floorChars

theorem geometryRow095_floor_text_read :
    geometryRowsJson095.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow095_floorText := by rfl

theorem geometryRow095_floor_chars_parse :
    SourceJson.intChars geometryRow095_floorChars = some (150451984230304964 : Int) := by decide +kernel

theorem geometryRow095_floor_parse :
    parseInteger geometryRow095_floorText = .ok geometryRowsTyped095.jensenFloorQ96 := by
  simp only [geometryRow095_floorText, parseInteger, String.toList_ofList, geometryRow095_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_095 :
    decodeGeometryRow geometryRowsJson095 = .ok geometryRowsTyped095 :=
  original_geometryRow_of_fields geometryRowsJson095 geometryRowsTyped095 geometryRow095_floorText
    geometryRow095_simplexId_read geometryRow095_vertexIds_read
    geometryRow095_physicalVolume_read geometryRow095_meanGap_read
    geometryRow095_factorMaxima_read geometryRow095_gapWeightedMeans_read
    geometryRow095_jensenBound_read geometryRow095_floor_text_read geometryRow095_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_095_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock048 : List SourceJson := [geometryRowsJson094, geometryRowsJson095]
noncomputable def geometryRowsTypedBlock048 : List (GeometryRow) := [geometryRowsTyped094, geometryRowsTyped095]
noncomputable def geometryRowsTypedThroughBlock048 : List (GeometryRow) := geometryRowsTypedThroughBlock047 ++ geometryRowsTypedBlock048

theorem geometry_Rows_block_048_push_eq (acc : List SourceJson) :
    SimplicesBlock048.blockPush acc = [geometryRowsJson095, geometryRowsJson094] ++ acc := by rfl

theorem geometry_Rows_block_048_reverse (acc : List SourceJson) :
    (SimplicesBlock048.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock048 := by
  rw [geometry_Rows_block_048_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_048 :
    geometryRowsJsonBlock048.mapM decodeGeometryRow = .ok geometryRowsTypedBlock048 := by
  simp only [geometryRowsJsonBlock048, geometryRowsTypedBlock048, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_094, decode_geometry_Rows_095]
  rfl

theorem decode_geometry_Rows_through_block_048 :
    SimplicesValue.arrayAcc049.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock048 := by
  change (SimplicesBlock048.blockPush SimplicesValue.arrayAcc048).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_048_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_047, decode_geometry_Rows_block_048]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_048_complete"
  err.flush

#print axioms geometryRow094_simplexId_read
#print axioms geometryRow094_vertexIds_read
#print axioms geometryRow094_physicalVolume_field
#print axioms geometryRow094_physicalVolume_numerator_no_slash
#print axioms geometryRow094_physicalVolume_numerator_parse
#print axioms geometryRow094_physicalVolume_denominator_parse
#print axioms geometryRow094_physicalVolume_denominator_nonzero
#print axioms geometryRow094_physicalVolume_parse
#print axioms geometryRow094_physicalVolume_read
#print axioms geometryRow094_meanGap_field
#print axioms geometryRow094_meanGap_numerator_no_slash
#print axioms geometryRow094_meanGap_numerator_parse
#print axioms geometryRow094_meanGap_denominator_parse
#print axioms geometryRow094_meanGap_denominator_nonzero
#print axioms geometryRow094_meanGap_parse
#print axioms geometryRow094_meanGap_read
#print axioms geometryRow094_jensenBound_field
#print axioms geometryRow094_jensenBound_numerator_no_slash
#print axioms geometryRow094_jensenBound_numerator_parse
#print axioms geometryRow094_jensenBound_denominator_parse
#print axioms geometryRow094_jensenBound_denominator_nonzero
#print axioms geometryRow094_jensenBound_parse
#print axioms geometryRow094_jensenBound_read
#print axioms geometryRow094_factorMaxima_read
#print axioms geometryRow094_gapWeightedMeans_read
#print axioms geometryRow094_floor_text_read
#print axioms geometryRow094_floor_chars_parse
#print axioms geometryRow094_floor_parse
#print axioms decode_geometry_Rows_094
#print axioms geometryRow095_simplexId_read
#print axioms geometryRow095_vertexIds_read
#print axioms geometryRow095_physicalVolume_field
#print axioms geometryRow095_physicalVolume_numerator_no_slash
#print axioms geometryRow095_physicalVolume_numerator_parse
#print axioms geometryRow095_physicalVolume_denominator_parse
#print axioms geometryRow095_physicalVolume_denominator_nonzero
#print axioms geometryRow095_physicalVolume_parse
#print axioms geometryRow095_physicalVolume_read
#print axioms geometryRow095_meanGap_field
#print axioms geometryRow095_meanGap_numerator_no_slash
#print axioms geometryRow095_meanGap_numerator_parse
#print axioms geometryRow095_meanGap_denominator_parse
#print axioms geometryRow095_meanGap_denominator_nonzero
#print axioms geometryRow095_meanGap_parse
#print axioms geometryRow095_meanGap_read
#print axioms geometryRow095_jensenBound_field
#print axioms geometryRow095_jensenBound_numerator_no_slash
#print axioms geometryRow095_jensenBound_numerator_parse
#print axioms geometryRow095_jensenBound_denominator_parse
#print axioms geometryRow095_jensenBound_denominator_nonzero
#print axioms geometryRow095_jensenBound_parse
#print axioms geometryRow095_jensenBound_read
#print axioms geometryRow095_factorMaxima_read
#print axioms geometryRow095_gapWeightedMeans_read
#print axioms geometryRow095_floor_text_read
#print axioms geometryRow095_floor_chars_parse
#print axioms geometryRow095_floor_parse
#print axioms decode_geometry_Rows_095
#print axioms geometry_Rows_block_048_push_eq
#print axioms geometry_Rows_block_048_reverse
#print axioms decode_geometry_Rows_block_048
#print axioms decode_geometry_Rows_through_block_048

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
