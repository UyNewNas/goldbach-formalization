import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows044

/-! Original simplices typed block 45, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson089 : SourceJson :=
  (SimplicesBlock045.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped089 : GeometryRow :=
  { simplexId := 89,
    vertexIds := #[39, 37, 24, 23, 21, 20, 3, 1, 0],
    physicalVolume := ((3084365736668461577683876096529930082607 : ℚ) / (101079144686223360000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((66369109 : ℚ) / (99756000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((81237507307457362397 : ℚ) / (955357824344700000000 : ℚ)), ((390597424831667882687 : ℚ) / (4537949665637325000000 : ℚ)), ((109148691488004941413 : ℚ) / (756324944272887500000 : ℚ)), ((5893229046091931426759 : ℚ) / (54455395987647900000000 : ℚ)), ((38931858395632707999 : ℚ) / (711835241668600000000 : ℚ)), ((295187738713587015397 : ℚ) / (6050599554183100000000 : ℚ)), ((867863327927075932369 : ℚ) / (21782158395059160000000 : ℚ)), ((856232362308904356007 : ℚ) / (21782158395059160000000 : ℚ)), ((2078858905825487051587 : ℚ) / (54455395987647900000000 : ℚ)), ((2078848014746289522007 : ℚ) / (54455395987647900000000 : ℚ))],
    jensenBound := ((29289142284621763767689262429912433298504431417934926182269793439915998056203772629046607985775545930116690701825816238138621771286839744232681280697973725524402518493910122680664062500000000 : ℚ) / (251090766713649605029511675248144642473183580541329795292264565756344208741441359570022984714361881694603101398333357126136934490786548759470481930290899998950805218075750460739664275027291497450219362023011 : ℚ)),
    jensenFloorQ96 := (9241777207506 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_simplexId_before"
  err.flush

theorem geometryRow089_simplexId_read :
    geometryRowsJson089.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped089.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_vertexIds_before"
  err.flush

theorem geometryRow089_vertexIds_read :
    geometryRowsJson089.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped089.vertexIds := by decide +kernel

noncomputable def geometryRow089_physicalVolumeNumeratorChars : List Char := ['3', '0', '8', '4', '3', '6', '5', '7', '3', '6', '6', '6', '8', '4', '6', '1', '5', '7', '7', '6', '8', '3', '8', '7', '6', '0', '9', '6', '5', '2', '9', '9', '3', '0', '0', '8', '2', '6', '0', '7']
noncomputable def geometryRow089_physicalVolumeDenominatorChars : List Char := ['1', '0', '1', '0', '7', '9', '1', '4', '4', '6', '8', '6', '2', '2', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow089_physicalVolumeText : String := String.ofList (geometryRow089_physicalVolumeNumeratorChars ++ '/' :: geometryRow089_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_physicalVolume_before_field"
  err.flush

theorem geometryRow089_physicalVolume_field :
    geometryRowsJson089.getObjVal? "physical_volume" = .ok (.str geometryRow089_physicalVolumeText) := by rfl

theorem geometryRow089_physicalVolume_numerator_no_slash :
    geometryRow089_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow089_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow089_physicalVolumeNumeratorChars = some (3084365736668461577683876096529930082607 : Int) := by decide +kernel

theorem geometryRow089_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow089_physicalVolumeDenominatorChars = some (101079144686223360000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow089_physicalVolume_denominator_nonzero : (101079144686223360000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow089_physicalVolume_parse :
    parseRational geometryRow089_physicalVolumeText = .ok geometryRowsTyped089.physicalVolume :=
  original_rational_fraction_of_chars geometryRow089_physicalVolumeNumeratorChars geometryRow089_physicalVolumeDenominatorChars
    (3084365736668461577683876096529930082607 : Int) (101079144686223360000000000000000000000000000000000000000000000000 : Int)
    geometryRow089_physicalVolume_numerator_no_slash geometryRow089_physicalVolume_numerator_parse
    geometryRow089_physicalVolume_denominator_parse geometryRow089_physicalVolume_denominator_nonzero

theorem geometryRow089_physicalVolume_read :
    rationalField geometryRowsJson089 "physical_volume" = .ok geometryRowsTyped089.physicalVolume :=
  original_rationalField_of_string geometryRowsJson089 "physical_volume" geometryRow089_physicalVolumeText
    geometryRowsTyped089.physicalVolume geometryRow089_physicalVolume_field geometryRow089_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_physicalVolume_complete"
  err.flush

noncomputable def geometryRow089_meanGapNumeratorChars : List Char := ['6', '6', '3', '6', '9', '1', '0', '9']
noncomputable def geometryRow089_meanGapDenominatorChars : List Char := ['9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow089_meanGapText : String := String.ofList (geometryRow089_meanGapNumeratorChars ++ '/' :: geometryRow089_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_meanGap_before_field"
  err.flush

theorem geometryRow089_meanGap_field :
    geometryRowsJson089.getObjVal? "mean_gap" = .ok (.str geometryRow089_meanGapText) := by rfl

theorem geometryRow089_meanGap_numerator_no_slash :
    geometryRow089_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow089_meanGap_numerator_parse :
    SourceJson.intChars geometryRow089_meanGapNumeratorChars = some (66369109 : Int) := by decide +kernel

theorem geometryRow089_meanGap_denominator_parse :
    SourceJson.intChars geometryRow089_meanGapDenominatorChars = some (99756000000 : Int) := by decide +kernel

theorem geometryRow089_meanGap_denominator_nonzero : (99756000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow089_meanGap_parse :
    parseRational geometryRow089_meanGapText = .ok geometryRowsTyped089.meanGap :=
  original_rational_fraction_of_chars geometryRow089_meanGapNumeratorChars geometryRow089_meanGapDenominatorChars
    (66369109 : Int) (99756000000 : Int)
    geometryRow089_meanGap_numerator_no_slash geometryRow089_meanGap_numerator_parse
    geometryRow089_meanGap_denominator_parse geometryRow089_meanGap_denominator_nonzero

theorem geometryRow089_meanGap_read :
    rationalField geometryRowsJson089 "mean_gap" = .ok geometryRowsTyped089.meanGap :=
  original_rationalField_of_string geometryRowsJson089 "mean_gap" geometryRow089_meanGapText
    geometryRowsTyped089.meanGap geometryRow089_meanGap_field geometryRow089_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_meanGap_complete"
  err.flush

noncomputable def geometryRow089_jensenBoundNumeratorChars : List Char := ['2', '9', '2', '8', '9', '1', '4', '2', '2', '8', '4', '6', '2', '1', '7', '6', '3', '7', '6', '7', '6', '8', '9', '2', '6', '2', '4', '2', '9', '9', '1', '2', '4', '3', '3', '2', '9', '8', '5', '0', '4', '4', '3', '1', '4', '1', '7', '9', '3', '4', '9', '2', '6', '1', '8', '2', '2', '6', '9', '7', '9', '3', '4', '3', '9', '9', '1', '5', '9', '9', '8', '0', '5', '6', '2', '0', '3', '7', '7', '2', '6', '2', '9', '0', '4', '6', '6', '0', '7', '9', '8', '5', '7', '7', '5', '5', '4', '5', '9', '3', '0', '1', '1', '6', '6', '9', '0', '7', '0', '1', '8', '2', '5', '8', '1', '6', '2', '3', '8', '1', '3', '8', '6', '2', '1', '7', '7', '1', '2', '8', '6', '8', '3', '9', '7', '4', '4', '2', '3', '2', '6', '8', '1', '2', '8', '0', '6', '9', '7', '9', '7', '3', '7', '2', '5', '5', '2', '4', '4', '0', '2', '5', '1', '8', '4', '9', '3', '9', '1', '0', '1', '2', '2', '6', '8', '0', '6', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow089_jensenBoundDenominatorChars : List Char := ['2', '5', '1', '0', '9', '0', '7', '6', '6', '7', '1', '3', '6', '4', '9', '6', '0', '5', '0', '2', '9', '5', '1', '1', '6', '7', '5', '2', '4', '8', '1', '4', '4', '6', '4', '2', '4', '7', '3', '1', '8', '3', '5', '8', '0', '5', '4', '1', '3', '2', '9', '7', '9', '5', '2', '9', '2', '2', '6', '4', '5', '6', '5', '7', '5', '6', '3', '4', '4', '2', '0', '8', '7', '4', '1', '4', '4', '1', '3', '5', '9', '5', '7', '0', '0', '2', '2', '9', '8', '4', '7', '1', '4', '3', '6', '1', '8', '8', '1', '6', '9', '4', '6', '0', '3', '1', '0', '1', '3', '9', '8', '3', '3', '3', '3', '5', '7', '1', '2', '6', '1', '3', '6', '9', '3', '4', '4', '9', '0', '7', '8', '6', '5', '4', '8', '7', '5', '9', '4', '7', '0', '4', '8', '1', '9', '3', '0', '2', '9', '0', '8', '9', '9', '9', '9', '8', '9', '5', '0', '8', '0', '5', '2', '1', '8', '0', '7', '5', '7', '5', '0', '4', '6', '0', '7', '3', '9', '6', '6', '4', '2', '7', '5', '0', '2', '7', '2', '9', '1', '4', '9', '7', '4', '5', '0', '2', '1', '9', '3', '6', '2', '0', '2', '3', '0', '1', '1']
noncomputable def geometryRow089_jensenBoundText : String := String.ofList (geometryRow089_jensenBoundNumeratorChars ++ '/' :: geometryRow089_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_jensenBound_before_field"
  err.flush

theorem geometryRow089_jensenBound_field :
    geometryRowsJson089.getObjVal? "jensen_bound" = .ok (.str geometryRow089_jensenBoundText) := by rfl

theorem geometryRow089_jensenBound_numerator_no_slash :
    geometryRow089_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow089_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow089_jensenBoundNumeratorChars = some (29289142284621763767689262429912433298504431417934926182269793439915998056203772629046607985775545930116690701825816238138621771286839744232681280697973725524402518493910122680664062500000000 : Int) := by decide +kernel

theorem geometryRow089_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow089_jensenBoundDenominatorChars = some (251090766713649605029511675248144642473183580541329795292264565756344208741441359570022984714361881694603101398333357126136934490786548759470481930290899998950805218075750460739664275027291497450219362023011 : Int) := by decide +kernel

theorem geometryRow089_jensenBound_denominator_nonzero : (251090766713649605029511675248144642473183580541329795292264565756344208741441359570022984714361881694603101398333357126136934490786548759470481930290899998950805218075750460739664275027291497450219362023011 : Int) ≠ 0 := by decide +kernel

theorem geometryRow089_jensenBound_parse :
    parseRational geometryRow089_jensenBoundText = .ok geometryRowsTyped089.jensenBound :=
  original_rational_fraction_of_chars geometryRow089_jensenBoundNumeratorChars geometryRow089_jensenBoundDenominatorChars
    (29289142284621763767689262429912433298504431417934926182269793439915998056203772629046607985775545930116690701825816238138621771286839744232681280697973725524402518493910122680664062500000000 : Int) (251090766713649605029511675248144642473183580541329795292264565756344208741441359570022984714361881694603101398333357126136934490786548759470481930290899998950805218075750460739664275027291497450219362023011 : Int)
    geometryRow089_jensenBound_numerator_no_slash geometryRow089_jensenBound_numerator_parse
    geometryRow089_jensenBound_denominator_parse geometryRow089_jensenBound_denominator_nonzero

theorem geometryRow089_jensenBound_read :
    rationalField geometryRowsJson089 "jensen_bound" = .ok geometryRowsTyped089.jensenBound :=
  original_rationalField_of_string geometryRowsJson089 "jensen_bound" geometryRow089_jensenBoundText
    geometryRowsTyped089.jensenBound geometryRow089_jensenBound_field geometryRow089_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_factorMaxima_before"
  err.flush

theorem geometryRow089_factorMaxima_read :
    rationalArrayField geometryRowsJson089 "factor_maxima" = .ok geometryRowsTyped089.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_gapWeightedMeans_before"
  err.flush

theorem geometryRow089_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson089 "gap_weighted_means" = .ok geometryRowsTyped089.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow089_floorChars : List Char := ['9', '2', '4', '1', '7', '7', '7', '2', '0', '7', '5', '0', '6']
noncomputable def geometryRow089_floorText : String := String.ofList geometryRow089_floorChars

theorem geometryRow089_floor_text_read :
    geometryRowsJson089.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow089_floorText := by rfl

theorem geometryRow089_floor_chars_parse :
    SourceJson.intChars geometryRow089_floorChars = some (9241777207506 : Int) := by decide +kernel

theorem geometryRow089_floor_parse :
    parseInteger geometryRow089_floorText = .ok geometryRowsTyped089.jensenFloorQ96 := by
  simp only [geometryRow089_floorText, parseInteger, String.toList_ofList, geometryRow089_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_089 :
    decodeGeometryRow geometryRowsJson089 = .ok geometryRowsTyped089 :=
  original_geometryRow_of_fields geometryRowsJson089 geometryRowsTyped089 geometryRow089_floorText
    geometryRow089_simplexId_read geometryRow089_vertexIds_read
    geometryRow089_physicalVolume_read geometryRow089_meanGap_read
    geometryRow089_factorMaxima_read geometryRow089_gapWeightedMeans_read
    geometryRow089_jensenBound_read geometryRow089_floor_text_read geometryRow089_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_089_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson090 : SourceJson :=
  (SimplicesBlock045.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped090 : GeometryRow :=
  { simplexId := 90,
    vertexIds := #[39, 37, 24, 23, 21, 20, 3, 2, 0],
    physicalVolume := ((233789818573006458929446137850366966433543296223 : ℚ) / (1456146158349733724160000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((6109170227 : ℚ) / (4888044000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((760998590673467725075181 : ℚ) / (9070296032533308600000000 : ℚ)), ((38002578241815168710534219 : ℚ) / (444444505594132121400000000 : ℚ)), ((64231465827331444374043331 : ℚ) / (444444505594132121400000000 : ℚ)), ((73278987543549652000064461 : ℚ) / (666666758391198182100000000 : ℚ)), ((358582846649955990705277 : ℚ) / (6535948611678413550000000 : ℚ)), ((21088355718332121025475143 : ℚ) / (444444505594132121400000000 : ℚ)), ((69930712424091518458171 : ℚ) / (1754386206292626795000000 : ℚ)), ((5243538461920750958785477 : ℚ) / (133333351678239636420000000 : ℚ)), ((51107658523675593688768951 : ℚ) / (1333333516782396364200000000 : ℚ)), ((50420972854820095005831571 : ℚ) / (1333333516782396364200000000 : ℚ))],
    jensenBound := ((1158139424533778677478501719856235931607916984530598562210738913358200912629116910735292216229526948452760786054699699483049254522167192900388826778546042366626290835620549743105442121417605149746476001518597696616177783203125000000000000 : ℚ) / (972626399004762318067381418291646885676639797896085469418829685413630510416454514237136318977274172956096489030073460085610468162627063329627392808179689727537833635888836899937755917633467324712334889159433104012002769374005260529363902270874402873 : ℚ)),
    jensenFloorQ96 := (94339675167185668 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_simplexId_before"
  err.flush

theorem geometryRow090_simplexId_read :
    geometryRowsJson090.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped090.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_vertexIds_before"
  err.flush

theorem geometryRow090_vertexIds_read :
    geometryRowsJson090.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped090.vertexIds := by decide +kernel

noncomputable def geometryRow090_physicalVolumeNumeratorChars : List Char := ['2', '3', '3', '7', '8', '9', '8', '1', '8', '5', '7', '3', '0', '0', '6', '4', '5', '8', '9', '2', '9', '4', '4', '6', '1', '3', '7', '8', '5', '0', '3', '6', '6', '9', '6', '6', '4', '3', '3', '5', '4', '3', '2', '9', '6', '2', '2', '3']
noncomputable def geometryRow090_physicalVolumeDenominatorChars : List Char := ['1', '4', '5', '6', '1', '4', '6', '1', '5', '8', '3', '4', '9', '7', '3', '3', '7', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow090_physicalVolumeText : String := String.ofList (geometryRow090_physicalVolumeNumeratorChars ++ '/' :: geometryRow090_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_physicalVolume_before_field"
  err.flush

theorem geometryRow090_physicalVolume_field :
    geometryRowsJson090.getObjVal? "physical_volume" = .ok (.str geometryRow090_physicalVolumeText) := by rfl

theorem geometryRow090_physicalVolume_numerator_no_slash :
    geometryRow090_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow090_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow090_physicalVolumeNumeratorChars = some (233789818573006458929446137850366966433543296223 : Int) := by decide +kernel

theorem geometryRow090_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow090_physicalVolumeDenominatorChars = some (1456146158349733724160000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow090_physicalVolume_denominator_nonzero : (1456146158349733724160000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow090_physicalVolume_parse :
    parseRational geometryRow090_physicalVolumeText = .ok geometryRowsTyped090.physicalVolume :=
  original_rational_fraction_of_chars geometryRow090_physicalVolumeNumeratorChars geometryRow090_physicalVolumeDenominatorChars
    (233789818573006458929446137850366966433543296223 : Int) (1456146158349733724160000000000000000000000000000000000000000000000000 : Int)
    geometryRow090_physicalVolume_numerator_no_slash geometryRow090_physicalVolume_numerator_parse
    geometryRow090_physicalVolume_denominator_parse geometryRow090_physicalVolume_denominator_nonzero

theorem geometryRow090_physicalVolume_read :
    rationalField geometryRowsJson090 "physical_volume" = .ok geometryRowsTyped090.physicalVolume :=
  original_rationalField_of_string geometryRowsJson090 "physical_volume" geometryRow090_physicalVolumeText
    geometryRowsTyped090.physicalVolume geometryRow090_physicalVolume_field geometryRow090_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_physicalVolume_complete"
  err.flush

noncomputable def geometryRow090_meanGapNumeratorChars : List Char := ['6', '1', '0', '9', '1', '7', '0', '2', '2', '7']
noncomputable def geometryRow090_meanGapDenominatorChars : List Char := ['4', '8', '8', '8', '0', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow090_meanGapText : String := String.ofList (geometryRow090_meanGapNumeratorChars ++ '/' :: geometryRow090_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_meanGap_before_field"
  err.flush

theorem geometryRow090_meanGap_field :
    geometryRowsJson090.getObjVal? "mean_gap" = .ok (.str geometryRow090_meanGapText) := by rfl

theorem geometryRow090_meanGap_numerator_no_slash :
    geometryRow090_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow090_meanGap_numerator_parse :
    SourceJson.intChars geometryRow090_meanGapNumeratorChars = some (6109170227 : Int) := by decide +kernel

theorem geometryRow090_meanGap_denominator_parse :
    SourceJson.intChars geometryRow090_meanGapDenominatorChars = some (4888044000000 : Int) := by decide +kernel

theorem geometryRow090_meanGap_denominator_nonzero : (4888044000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow090_meanGap_parse :
    parseRational geometryRow090_meanGapText = .ok geometryRowsTyped090.meanGap :=
  original_rational_fraction_of_chars geometryRow090_meanGapNumeratorChars geometryRow090_meanGapDenominatorChars
    (6109170227 : Int) (4888044000000 : Int)
    geometryRow090_meanGap_numerator_no_slash geometryRow090_meanGap_numerator_parse
    geometryRow090_meanGap_denominator_parse geometryRow090_meanGap_denominator_nonzero

theorem geometryRow090_meanGap_read :
    rationalField geometryRowsJson090 "mean_gap" = .ok geometryRowsTyped090.meanGap :=
  original_rationalField_of_string geometryRowsJson090 "mean_gap" geometryRow090_meanGapText
    geometryRowsTyped090.meanGap geometryRow090_meanGap_field geometryRow090_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_meanGap_complete"
  err.flush

noncomputable def geometryRow090_jensenBoundNumeratorChars : List Char := ['1', '1', '5', '8', '1', '3', '9', '4', '2', '4', '5', '3', '3', '7', '7', '8', '6', '7', '7', '4', '7', '8', '5', '0', '1', '7', '1', '9', '8', '5', '6', '2', '3', '5', '9', '3', '1', '6', '0', '7', '9', '1', '6', '9', '8', '4', '5', '3', '0', '5', '9', '8', '5', '6', '2', '2', '1', '0', '7', '3', '8', '9', '1', '3', '3', '5', '8', '2', '0', '0', '9', '1', '2', '6', '2', '9', '1', '1', '6', '9', '1', '0', '7', '3', '5', '2', '9', '2', '2', '1', '6', '2', '2', '9', '5', '2', '6', '9', '4', '8', '4', '5', '2', '7', '6', '0', '7', '8', '6', '0', '5', '4', '6', '9', '9', '6', '9', '9', '4', '8', '3', '0', '4', '9', '2', '5', '4', '5', '2', '2', '1', '6', '7', '1', '9', '2', '9', '0', '0', '3', '8', '8', '8', '2', '6', '7', '7', '8', '5', '4', '6', '0', '4', '2', '3', '6', '6', '6', '2', '6', '2', '9', '0', '8', '3', '5', '6', '2', '0', '5', '4', '9', '7', '4', '3', '1', '0', '5', '4', '4', '2', '1', '2', '1', '4', '1', '7', '6', '0', '5', '1', '4', '9', '7', '4', '6', '4', '7', '6', '0', '0', '1', '5', '1', '8', '5', '9', '7', '6', '9', '6', '6', '1', '6', '1', '7', '7', '7', '8', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow090_jensenBoundDenominatorChars : List Char := ['9', '7', '2', '6', '2', '6', '3', '9', '9', '0', '0', '4', '7', '6', '2', '3', '1', '8', '0', '6', '7', '3', '8', '1', '4', '1', '8', '2', '9', '1', '6', '4', '6', '8', '8', '5', '6', '7', '6', '6', '3', '9', '7', '9', '7', '8', '9', '6', '0', '8', '5', '4', '6', '9', '4', '1', '8', '8', '2', '9', '6', '8', '5', '4', '1', '3', '6', '3', '0', '5', '1', '0', '4', '1', '6', '4', '5', '4', '5', '1', '4', '2', '3', '7', '1', '3', '6', '3', '1', '8', '9', '7', '7', '2', '7', '4', '1', '7', '2', '9', '5', '6', '0', '9', '6', '4', '8', '9', '0', '3', '0', '0', '7', '3', '4', '6', '0', '0', '8', '5', '6', '1', '0', '4', '6', '8', '1', '6', '2', '6', '2', '7', '0', '6', '3', '3', '2', '9', '6', '2', '7', '3', '9', '2', '8', '0', '8', '1', '7', '9', '6', '8', '9', '7', '2', '7', '5', '3', '7', '8', '3', '3', '6', '3', '5', '8', '8', '8', '8', '3', '6', '8', '9', '9', '9', '3', '7', '7', '5', '5', '9', '1', '7', '6', '3', '3', '4', '6', '7', '3', '2', '4', '7', '1', '2', '3', '3', '4', '8', '8', '9', '1', '5', '9', '4', '3', '3', '1', '0', '4', '0', '1', '2', '0', '0', '2', '7', '6', '9', '3', '7', '4', '0', '0', '5', '2', '6', '0', '5', '2', '9', '3', '6', '3', '9', '0', '2', '2', '7', '0', '8', '7', '4', '4', '0', '2', '8', '7', '3']
noncomputable def geometryRow090_jensenBoundText : String := String.ofList (geometryRow090_jensenBoundNumeratorChars ++ '/' :: geometryRow090_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_jensenBound_before_field"
  err.flush

theorem geometryRow090_jensenBound_field :
    geometryRowsJson090.getObjVal? "jensen_bound" = .ok (.str geometryRow090_jensenBoundText) := by rfl

theorem geometryRow090_jensenBound_numerator_no_slash :
    geometryRow090_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow090_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow090_jensenBoundNumeratorChars = some (1158139424533778677478501719856235931607916984530598562210738913358200912629116910735292216229526948452760786054699699483049254522167192900388826778546042366626290835620549743105442121417605149746476001518597696616177783203125000000000000 : Int) := by decide +kernel

theorem geometryRow090_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow090_jensenBoundDenominatorChars = some (972626399004762318067381418291646885676639797896085469418829685413630510416454514237136318977274172956096489030073460085610468162627063329627392808179689727537833635888836899937755917633467324712334889159433104012002769374005260529363902270874402873 : Int) := by decide +kernel

theorem geometryRow090_jensenBound_denominator_nonzero : (972626399004762318067381418291646885676639797896085469418829685413630510416454514237136318977274172956096489030073460085610468162627063329627392808179689727537833635888836899937755917633467324712334889159433104012002769374005260529363902270874402873 : Int) ≠ 0 := by decide +kernel

theorem geometryRow090_jensenBound_parse :
    parseRational geometryRow090_jensenBoundText = .ok geometryRowsTyped090.jensenBound :=
  original_rational_fraction_of_chars geometryRow090_jensenBoundNumeratorChars geometryRow090_jensenBoundDenominatorChars
    (1158139424533778677478501719856235931607916984530598562210738913358200912629116910735292216229526948452760786054699699483049254522167192900388826778546042366626290835620549743105442121417605149746476001518597696616177783203125000000000000 : Int) (972626399004762318067381418291646885676639797896085469418829685413630510416454514237136318977274172956096489030073460085610468162627063329627392808179689727537833635888836899937755917633467324712334889159433104012002769374005260529363902270874402873 : Int)
    geometryRow090_jensenBound_numerator_no_slash geometryRow090_jensenBound_numerator_parse
    geometryRow090_jensenBound_denominator_parse geometryRow090_jensenBound_denominator_nonzero

theorem geometryRow090_jensenBound_read :
    rationalField geometryRowsJson090 "jensen_bound" = .ok geometryRowsTyped090.jensenBound :=
  original_rationalField_of_string geometryRowsJson090 "jensen_bound" geometryRow090_jensenBoundText
    geometryRowsTyped090.jensenBound geometryRow090_jensenBound_field geometryRow090_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_factorMaxima_before"
  err.flush

theorem geometryRow090_factorMaxima_read :
    rationalArrayField geometryRowsJson090 "factor_maxima" = .ok geometryRowsTyped090.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_gapWeightedMeans_before"
  err.flush

theorem geometryRow090_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson090 "gap_weighted_means" = .ok geometryRowsTyped090.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow090_floorChars : List Char := ['9', '4', '3', '3', '9', '6', '7', '5', '1', '6', '7', '1', '8', '5', '6', '6', '8']
noncomputable def geometryRow090_floorText : String := String.ofList geometryRow090_floorChars

theorem geometryRow090_floor_text_read :
    geometryRowsJson090.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow090_floorText := by rfl

theorem geometryRow090_floor_chars_parse :
    SourceJson.intChars geometryRow090_floorChars = some (94339675167185668 : Int) := by decide +kernel

theorem geometryRow090_floor_parse :
    parseInteger geometryRow090_floorText = .ok geometryRowsTyped090.jensenFloorQ96 := by
  simp only [geometryRow090_floorText, parseInteger, String.toList_ofList, geometryRow090_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_090 :
    decodeGeometryRow geometryRowsJson090 = .ok geometryRowsTyped090 :=
  original_geometryRow_of_fields geometryRowsJson090 geometryRowsTyped090 geometryRow090_floorText
    geometryRow090_simplexId_read geometryRow090_vertexIds_read
    geometryRow090_physicalVolume_read geometryRow090_meanGap_read
    geometryRow090_factorMaxima_read geometryRow090_gapWeightedMeans_read
    geometryRow090_jensenBound_read geometryRow090_floor_text_read geometryRow090_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_090_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock045 : List SourceJson := [geometryRowsJson089, geometryRowsJson090]
noncomputable def geometryRowsTypedBlock045 : List (GeometryRow) := [geometryRowsTyped089, geometryRowsTyped090]
noncomputable def geometryRowsTypedThroughBlock045 : List (GeometryRow) := geometryRowsTypedThroughBlock044 ++ geometryRowsTypedBlock045

theorem geometry_Rows_block_045_push_eq (acc : List SourceJson) :
    SimplicesBlock045.blockPush acc = [geometryRowsJson090, geometryRowsJson089] ++ acc := by rfl

theorem geometry_Rows_block_045_reverse (acc : List SourceJson) :
    (SimplicesBlock045.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock045 := by
  rw [geometry_Rows_block_045_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_045 :
    geometryRowsJsonBlock045.mapM decodeGeometryRow = .ok geometryRowsTypedBlock045 := by
  simp only [geometryRowsJsonBlock045, geometryRowsTypedBlock045, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_089, decode_geometry_Rows_090]
  rfl

theorem decode_geometry_Rows_through_block_045 :
    SimplicesValue.arrayAcc046.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock045 := by
  change (SimplicesBlock045.blockPush SimplicesValue.arrayAcc045).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_045_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_044, decode_geometry_Rows_block_045]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_045_complete"
  err.flush

#print axioms geometryRow089_simplexId_read
#print axioms geometryRow089_vertexIds_read
#print axioms geometryRow089_physicalVolume_field
#print axioms geometryRow089_physicalVolume_numerator_no_slash
#print axioms geometryRow089_physicalVolume_numerator_parse
#print axioms geometryRow089_physicalVolume_denominator_parse
#print axioms geometryRow089_physicalVolume_denominator_nonzero
#print axioms geometryRow089_physicalVolume_parse
#print axioms geometryRow089_physicalVolume_read
#print axioms geometryRow089_meanGap_field
#print axioms geometryRow089_meanGap_numerator_no_slash
#print axioms geometryRow089_meanGap_numerator_parse
#print axioms geometryRow089_meanGap_denominator_parse
#print axioms geometryRow089_meanGap_denominator_nonzero
#print axioms geometryRow089_meanGap_parse
#print axioms geometryRow089_meanGap_read
#print axioms geometryRow089_jensenBound_field
#print axioms geometryRow089_jensenBound_numerator_no_slash
#print axioms geometryRow089_jensenBound_numerator_parse
#print axioms geometryRow089_jensenBound_denominator_parse
#print axioms geometryRow089_jensenBound_denominator_nonzero
#print axioms geometryRow089_jensenBound_parse
#print axioms geometryRow089_jensenBound_read
#print axioms geometryRow089_factorMaxima_read
#print axioms geometryRow089_gapWeightedMeans_read
#print axioms geometryRow089_floor_text_read
#print axioms geometryRow089_floor_chars_parse
#print axioms geometryRow089_floor_parse
#print axioms decode_geometry_Rows_089
#print axioms geometryRow090_simplexId_read
#print axioms geometryRow090_vertexIds_read
#print axioms geometryRow090_physicalVolume_field
#print axioms geometryRow090_physicalVolume_numerator_no_slash
#print axioms geometryRow090_physicalVolume_numerator_parse
#print axioms geometryRow090_physicalVolume_denominator_parse
#print axioms geometryRow090_physicalVolume_denominator_nonzero
#print axioms geometryRow090_physicalVolume_parse
#print axioms geometryRow090_physicalVolume_read
#print axioms geometryRow090_meanGap_field
#print axioms geometryRow090_meanGap_numerator_no_slash
#print axioms geometryRow090_meanGap_numerator_parse
#print axioms geometryRow090_meanGap_denominator_parse
#print axioms geometryRow090_meanGap_denominator_nonzero
#print axioms geometryRow090_meanGap_parse
#print axioms geometryRow090_meanGap_read
#print axioms geometryRow090_jensenBound_field
#print axioms geometryRow090_jensenBound_numerator_no_slash
#print axioms geometryRow090_jensenBound_numerator_parse
#print axioms geometryRow090_jensenBound_denominator_parse
#print axioms geometryRow090_jensenBound_denominator_nonzero
#print axioms geometryRow090_jensenBound_parse
#print axioms geometryRow090_jensenBound_read
#print axioms geometryRow090_factorMaxima_read
#print axioms geometryRow090_gapWeightedMeans_read
#print axioms geometryRow090_floor_text_read
#print axioms geometryRow090_floor_chars_parse
#print axioms geometryRow090_floor_parse
#print axioms decode_geometry_Rows_090
#print axioms geometry_Rows_block_045_push_eq
#print axioms geometry_Rows_block_045_reverse
#print axioms decode_geometry_Rows_block_045
#print axioms decode_geometry_Rows_through_block_045

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
