import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows029

/-! Original simplices typed block 30, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson059 : SourceJson :=
  (SimplicesBlock030.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped059 : GeometryRow :=
  { simplexId := 59,
    vertexIds := #[39, 35, 24, 22, 19, 18, 15, 14, 7],
    physicalVolume := ((63496060214316332557841822907533526423173 : ℚ) / (8121169014394060800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((403117 : ℚ) / (7200000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((10390765801 : ℚ) / (148556250000 : ℚ)), ((166772793061 : ℚ) / (2376900000000 : ℚ)), ((2097060172849 : ℚ) / (14261400000000 : ℚ)), ((3565194189407 : ℚ) / (33276600000000 : ℚ)), ((172675744627 : ℚ) / (3119681250000 : ℚ)), ((678971267441 : ℚ) / (14261400000000 : ℚ)), ((2196745370621 : ℚ) / (49914900000000 : ℚ)), ((2143435294151 : ℚ) / (49914900000000 : ℚ)), ((2143431966491 : ℚ) / (49914900000000 : ℚ)), ((2013881840951 : ℚ) / (49914900000000 : ℚ))],
    jensenBound := ((9532741995506666728372871546918438981056796969515756896109104121323178877412926673889160156250000 : ℚ) / (1671267358667350703518786747243046781462614497246350690087877248215878463794463167606979820298209579018220562616527 : ℚ)),
    jensenFloorQ96 := (451909521304 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_simplexId_before"
  err.flush

theorem geometryRow059_simplexId_read :
    geometryRowsJson059.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped059.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_vertexIds_before"
  err.flush

theorem geometryRow059_vertexIds_read :
    geometryRowsJson059.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped059.vertexIds := by decide +kernel

noncomputable def geometryRow059_physicalVolumeNumeratorChars : List Char := ['6', '3', '4', '9', '6', '0', '6', '0', '2', '1', '4', '3', '1', '6', '3', '3', '2', '5', '5', '7', '8', '4', '1', '8', '2', '2', '9', '0', '7', '5', '3', '3', '5', '2', '6', '4', '2', '3', '1', '7', '3']
noncomputable def geometryRow059_physicalVolumeDenominatorChars : List Char := ['8', '1', '2', '1', '1', '6', '9', '0', '1', '4', '3', '9', '4', '0', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow059_physicalVolumeText : String := String.ofList (geometryRow059_physicalVolumeNumeratorChars ++ '/' :: geometryRow059_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_physicalVolume_before_field"
  err.flush

theorem geometryRow059_physicalVolume_field :
    geometryRowsJson059.getObjVal? "physical_volume" = .ok (.str geometryRow059_physicalVolumeText) := by rfl

theorem geometryRow059_physicalVolume_numerator_no_slash :
    geometryRow059_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow059_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow059_physicalVolumeNumeratorChars = some (63496060214316332557841822907533526423173 : Int) := by decide +kernel

theorem geometryRow059_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow059_physicalVolumeDenominatorChars = some (8121169014394060800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow059_physicalVolume_denominator_nonzero : (8121169014394060800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow059_physicalVolume_parse :
    parseRational geometryRow059_physicalVolumeText = .ok geometryRowsTyped059.physicalVolume :=
  original_rational_fraction_of_chars geometryRow059_physicalVolumeNumeratorChars geometryRow059_physicalVolumeDenominatorChars
    (63496060214316332557841822907533526423173 : Int) (8121169014394060800000000000000000000000000000000000000000000000000 : Int)
    geometryRow059_physicalVolume_numerator_no_slash geometryRow059_physicalVolume_numerator_parse
    geometryRow059_physicalVolume_denominator_parse geometryRow059_physicalVolume_denominator_nonzero

theorem geometryRow059_physicalVolume_read :
    rationalField geometryRowsJson059 "physical_volume" = .ok geometryRowsTyped059.physicalVolume :=
  original_rationalField_of_string geometryRowsJson059 "physical_volume" geometryRow059_physicalVolumeText
    geometryRowsTyped059.physicalVolume geometryRow059_physicalVolume_field geometryRow059_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_physicalVolume_complete"
  err.flush

noncomputable def geometryRow059_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow059_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow059_meanGapText : String := String.ofList (geometryRow059_meanGapNumeratorChars ++ '/' :: geometryRow059_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_meanGap_before_field"
  err.flush

theorem geometryRow059_meanGap_field :
    geometryRowsJson059.getObjVal? "mean_gap" = .ok (.str geometryRow059_meanGapText) := by rfl

theorem geometryRow059_meanGap_numerator_no_slash :
    geometryRow059_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow059_meanGap_numerator_parse :
    SourceJson.intChars geometryRow059_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow059_meanGap_denominator_parse :
    SourceJson.intChars geometryRow059_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow059_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow059_meanGap_parse :
    parseRational geometryRow059_meanGapText = .ok geometryRowsTyped059.meanGap :=
  original_rational_fraction_of_chars geometryRow059_meanGapNumeratorChars geometryRow059_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow059_meanGap_numerator_no_slash geometryRow059_meanGap_numerator_parse
    geometryRow059_meanGap_denominator_parse geometryRow059_meanGap_denominator_nonzero

theorem geometryRow059_meanGap_read :
    rationalField geometryRowsJson059 "mean_gap" = .ok geometryRowsTyped059.meanGap :=
  original_rationalField_of_string geometryRowsJson059 "mean_gap" geometryRow059_meanGapText
    geometryRowsTyped059.meanGap geometryRow059_meanGap_field geometryRow059_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_meanGap_complete"
  err.flush

noncomputable def geometryRow059_jensenBoundNumeratorChars : List Char := ['9', '5', '3', '2', '7', '4', '1', '9', '9', '5', '5', '0', '6', '6', '6', '6', '7', '2', '8', '3', '7', '2', '8', '7', '1', '5', '4', '6', '9', '1', '8', '4', '3', '8', '9', '8', '1', '0', '5', '6', '7', '9', '6', '9', '6', '9', '5', '1', '5', '7', '5', '6', '8', '9', '6', '1', '0', '9', '1', '0', '4', '1', '2', '1', '3', '2', '3', '1', '7', '8', '8', '7', '7', '4', '1', '2', '9', '2', '6', '6', '7', '3', '8', '8', '9', '1', '6', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0']
noncomputable def geometryRow059_jensenBoundDenominatorChars : List Char := ['1', '6', '7', '1', '2', '6', '7', '3', '5', '8', '6', '6', '7', '3', '5', '0', '7', '0', '3', '5', '1', '8', '7', '8', '6', '7', '4', '7', '2', '4', '3', '0', '4', '6', '7', '8', '1', '4', '6', '2', '6', '1', '4', '4', '9', '7', '2', '4', '6', '3', '5', '0', '6', '9', '0', '0', '8', '7', '8', '7', '7', '2', '4', '8', '2', '1', '5', '8', '7', '8', '4', '6', '3', '7', '9', '4', '4', '6', '3', '1', '6', '7', '6', '0', '6', '9', '7', '9', '8', '2', '0', '2', '9', '8', '2', '0', '9', '5', '7', '9', '0', '1', '8', '2', '2', '0', '5', '6', '2', '6', '1', '6', '5', '2', '7']
noncomputable def geometryRow059_jensenBoundText : String := String.ofList (geometryRow059_jensenBoundNumeratorChars ++ '/' :: geometryRow059_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_jensenBound_before_field"
  err.flush

theorem geometryRow059_jensenBound_field :
    geometryRowsJson059.getObjVal? "jensen_bound" = .ok (.str geometryRow059_jensenBoundText) := by rfl

theorem geometryRow059_jensenBound_numerator_no_slash :
    geometryRow059_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow059_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow059_jensenBoundNumeratorChars = some (9532741995506666728372871546918438981056796969515756896109104121323178877412926673889160156250000 : Int) := by decide +kernel

theorem geometryRow059_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow059_jensenBoundDenominatorChars = some (1671267358667350703518786747243046781462614497246350690087877248215878463794463167606979820298209579018220562616527 : Int) := by decide +kernel

theorem geometryRow059_jensenBound_denominator_nonzero : (1671267358667350703518786747243046781462614497246350690087877248215878463794463167606979820298209579018220562616527 : Int) ≠ 0 := by decide +kernel

theorem geometryRow059_jensenBound_parse :
    parseRational geometryRow059_jensenBoundText = .ok geometryRowsTyped059.jensenBound :=
  original_rational_fraction_of_chars geometryRow059_jensenBoundNumeratorChars geometryRow059_jensenBoundDenominatorChars
    (9532741995506666728372871546918438981056796969515756896109104121323178877412926673889160156250000 : Int) (1671267358667350703518786747243046781462614497246350690087877248215878463794463167606979820298209579018220562616527 : Int)
    geometryRow059_jensenBound_numerator_no_slash geometryRow059_jensenBound_numerator_parse
    geometryRow059_jensenBound_denominator_parse geometryRow059_jensenBound_denominator_nonzero

theorem geometryRow059_jensenBound_read :
    rationalField geometryRowsJson059 "jensen_bound" = .ok geometryRowsTyped059.jensenBound :=
  original_rationalField_of_string geometryRowsJson059 "jensen_bound" geometryRow059_jensenBoundText
    geometryRowsTyped059.jensenBound geometryRow059_jensenBound_field geometryRow059_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_factorMaxima_before"
  err.flush

theorem geometryRow059_factorMaxima_read :
    rationalArrayField geometryRowsJson059 "factor_maxima" = .ok geometryRowsTyped059.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_gapWeightedMeans_before"
  err.flush

theorem geometryRow059_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson059 "gap_weighted_means" = .ok geometryRowsTyped059.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow059_floorChars : List Char := ['4', '5', '1', '9', '0', '9', '5', '2', '1', '3', '0', '4']
noncomputable def geometryRow059_floorText : String := String.ofList geometryRow059_floorChars

theorem geometryRow059_floor_text_read :
    geometryRowsJson059.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow059_floorText := by rfl

theorem geometryRow059_floor_chars_parse :
    SourceJson.intChars geometryRow059_floorChars = some (451909521304 : Int) := by decide +kernel

theorem geometryRow059_floor_parse :
    parseInteger geometryRow059_floorText = .ok geometryRowsTyped059.jensenFloorQ96 := by
  simp only [geometryRow059_floorText, parseInteger, String.toList_ofList, geometryRow059_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_059 :
    decodeGeometryRow geometryRowsJson059 = .ok geometryRowsTyped059 :=
  original_geometryRow_of_fields geometryRowsJson059 geometryRowsTyped059 geometryRow059_floorText
    geometryRow059_simplexId_read geometryRow059_vertexIds_read
    geometryRow059_physicalVolume_read geometryRow059_meanGap_read
    geometryRow059_factorMaxima_read geometryRow059_gapWeightedMeans_read
    geometryRow059_jensenBound_read geometryRow059_floor_text_read geometryRow059_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_059_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson060 : SourceJson :=
  (SimplicesBlock030.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped060 : GeometryRow :=
  { simplexId := 60,
    vertexIds := #[39, 35, 34, 29, 28, 25, 13, 3, 1],
    physicalVolume := ((15413080178482142783031666254417981406629 : ℚ) / (9508876399411200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2280689070559 : ℚ) / (27988800000000 : ℚ)), ((2308981302079 : ℚ) / (27988800000000 : ℚ)), ((292836480869 : ℚ) / (1999200000000 : ℚ)), ((1087601791659 : ℚ) / (9329600000000 : ℚ)), ((5553614319 : ℚ) / (78400000000 : ℚ)), ((646979113477 : ℚ) / (13994400000000 : ℚ)), ((583544688073 : ℚ) / (15993600000000 : ℚ)), ((183453758361 : ℚ) / (5331200000000 : ℚ)), ((297849843223 : ℚ) / (9329600000000 : ℚ)), ((893545797829 : ℚ) / (27988800000000 : ℚ))],
    jensenBound := ((68399625534389719053037615218484770160398612358043509653353569972922347552768000000000000000000000000 : ℚ) / (9036679770950342026999118421190955198043529771098215487053568659489734757045259919138691945499705625901460333059037 : ℚ)),
    jensenFloorQ96 := (599686697449891 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_simplexId_before"
  err.flush

theorem geometryRow060_simplexId_read :
    geometryRowsJson060.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped060.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_vertexIds_before"
  err.flush

theorem geometryRow060_vertexIds_read :
    geometryRowsJson060.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped060.vertexIds := by decide +kernel

noncomputable def geometryRow060_physicalVolumeNumeratorChars : List Char := ['1', '5', '4', '1', '3', '0', '8', '0', '1', '7', '8', '4', '8', '2', '1', '4', '2', '7', '8', '3', '0', '3', '1', '6', '6', '6', '2', '5', '4', '4', '1', '7', '9', '8', '1', '4', '0', '6', '6', '2', '9']
noncomputable def geometryRow060_physicalVolumeDenominatorChars : List Char := ['9', '5', '0', '8', '8', '7', '6', '3', '9', '9', '4', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow060_physicalVolumeText : String := String.ofList (geometryRow060_physicalVolumeNumeratorChars ++ '/' :: geometryRow060_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_physicalVolume_before_field"
  err.flush

theorem geometryRow060_physicalVolume_field :
    geometryRowsJson060.getObjVal? "physical_volume" = .ok (.str geometryRow060_physicalVolumeText) := by rfl

theorem geometryRow060_physicalVolume_numerator_no_slash :
    geometryRow060_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow060_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow060_physicalVolumeNumeratorChars = some (15413080178482142783031666254417981406629 : Int) := by decide +kernel

theorem geometryRow060_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow060_physicalVolumeDenominatorChars = some (9508876399411200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow060_physicalVolume_denominator_nonzero : (9508876399411200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow060_physicalVolume_parse :
    parseRational geometryRow060_physicalVolumeText = .ok geometryRowsTyped060.physicalVolume :=
  original_rational_fraction_of_chars geometryRow060_physicalVolumeNumeratorChars geometryRow060_physicalVolumeDenominatorChars
    (15413080178482142783031666254417981406629 : Int) (9508876399411200000000000000000000000000000000000000000000000000 : Int)
    geometryRow060_physicalVolume_numerator_no_slash geometryRow060_physicalVolume_numerator_parse
    geometryRow060_physicalVolume_denominator_parse geometryRow060_physicalVolume_denominator_nonzero

theorem geometryRow060_physicalVolume_read :
    rationalField geometryRowsJson060 "physical_volume" = .ok geometryRowsTyped060.physicalVolume :=
  original_rationalField_of_string geometryRowsJson060 "physical_volume" geometryRow060_physicalVolumeText
    geometryRowsTyped060.physicalVolume geometryRow060_physicalVolume_field geometryRow060_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_physicalVolume_complete"
  err.flush

noncomputable def geometryRow060_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow060_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow060_meanGapText : String := String.ofList (geometryRow060_meanGapNumeratorChars ++ '/' :: geometryRow060_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_meanGap_before_field"
  err.flush

theorem geometryRow060_meanGap_field :
    geometryRowsJson060.getObjVal? "mean_gap" = .ok (.str geometryRow060_meanGapText) := by rfl

theorem geometryRow060_meanGap_numerator_no_slash :
    geometryRow060_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow060_meanGap_numerator_parse :
    SourceJson.intChars geometryRow060_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow060_meanGap_denominator_parse :
    SourceJson.intChars geometryRow060_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow060_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow060_meanGap_parse :
    parseRational geometryRow060_meanGapText = .ok geometryRowsTyped060.meanGap :=
  original_rational_fraction_of_chars geometryRow060_meanGapNumeratorChars geometryRow060_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow060_meanGap_numerator_no_slash geometryRow060_meanGap_numerator_parse
    geometryRow060_meanGap_denominator_parse geometryRow060_meanGap_denominator_nonzero

theorem geometryRow060_meanGap_read :
    rationalField geometryRowsJson060 "mean_gap" = .ok geometryRowsTyped060.meanGap :=
  original_rationalField_of_string geometryRowsJson060 "mean_gap" geometryRow060_meanGapText
    geometryRowsTyped060.meanGap geometryRow060_meanGap_field geometryRow060_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_meanGap_complete"
  err.flush

noncomputable def geometryRow060_jensenBoundNumeratorChars : List Char := ['6', '8', '3', '9', '9', '6', '2', '5', '5', '3', '4', '3', '8', '9', '7', '1', '9', '0', '5', '3', '0', '3', '7', '6', '1', '5', '2', '1', '8', '4', '8', '4', '7', '7', '0', '1', '6', '0', '3', '9', '8', '6', '1', '2', '3', '5', '8', '0', '4', '3', '5', '0', '9', '6', '5', '3', '3', '5', '3', '5', '6', '9', '9', '7', '2', '9', '2', '2', '3', '4', '7', '5', '5', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow060_jensenBoundDenominatorChars : List Char := ['9', '0', '3', '6', '6', '7', '9', '7', '7', '0', '9', '5', '0', '3', '4', '2', '0', '2', '6', '9', '9', '9', '1', '1', '8', '4', '2', '1', '1', '9', '0', '9', '5', '5', '1', '9', '8', '0', '4', '3', '5', '2', '9', '7', '7', '1', '0', '9', '8', '2', '1', '5', '4', '8', '7', '0', '5', '3', '5', '6', '8', '6', '5', '9', '4', '8', '9', '7', '3', '4', '7', '5', '7', '0', '4', '5', '2', '5', '9', '9', '1', '9', '1', '3', '8', '6', '9', '1', '9', '4', '5', '4', '9', '9', '7', '0', '5', '6', '2', '5', '9', '0', '1', '4', '6', '0', '3', '3', '3', '0', '5', '9', '0', '3', '7']
noncomputable def geometryRow060_jensenBoundText : String := String.ofList (geometryRow060_jensenBoundNumeratorChars ++ '/' :: geometryRow060_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_jensenBound_before_field"
  err.flush

theorem geometryRow060_jensenBound_field :
    geometryRowsJson060.getObjVal? "jensen_bound" = .ok (.str geometryRow060_jensenBoundText) := by rfl

theorem geometryRow060_jensenBound_numerator_no_slash :
    geometryRow060_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow060_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow060_jensenBoundNumeratorChars = some (68399625534389719053037615218484770160398612358043509653353569972922347552768000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow060_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow060_jensenBoundDenominatorChars = some (9036679770950342026999118421190955198043529771098215487053568659489734757045259919138691945499705625901460333059037 : Int) := by decide +kernel

theorem geometryRow060_jensenBound_denominator_nonzero : (9036679770950342026999118421190955198043529771098215487053568659489734757045259919138691945499705625901460333059037 : Int) ≠ 0 := by decide +kernel

theorem geometryRow060_jensenBound_parse :
    parseRational geometryRow060_jensenBoundText = .ok geometryRowsTyped060.jensenBound :=
  original_rational_fraction_of_chars geometryRow060_jensenBoundNumeratorChars geometryRow060_jensenBoundDenominatorChars
    (68399625534389719053037615218484770160398612358043509653353569972922347552768000000000000000000000000 : Int) (9036679770950342026999118421190955198043529771098215487053568659489734757045259919138691945499705625901460333059037 : Int)
    geometryRow060_jensenBound_numerator_no_slash geometryRow060_jensenBound_numerator_parse
    geometryRow060_jensenBound_denominator_parse geometryRow060_jensenBound_denominator_nonzero

theorem geometryRow060_jensenBound_read :
    rationalField geometryRowsJson060 "jensen_bound" = .ok geometryRowsTyped060.jensenBound :=
  original_rationalField_of_string geometryRowsJson060 "jensen_bound" geometryRow060_jensenBoundText
    geometryRowsTyped060.jensenBound geometryRow060_jensenBound_field geometryRow060_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_factorMaxima_before"
  err.flush

theorem geometryRow060_factorMaxima_read :
    rationalArrayField geometryRowsJson060 "factor_maxima" = .ok geometryRowsTyped060.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_gapWeightedMeans_before"
  err.flush

theorem geometryRow060_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson060 "gap_weighted_means" = .ok geometryRowsTyped060.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow060_floorChars : List Char := ['5', '9', '9', '6', '8', '6', '6', '9', '7', '4', '4', '9', '8', '9', '1']
noncomputable def geometryRow060_floorText : String := String.ofList geometryRow060_floorChars

theorem geometryRow060_floor_text_read :
    geometryRowsJson060.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow060_floorText := by rfl

theorem geometryRow060_floor_chars_parse :
    SourceJson.intChars geometryRow060_floorChars = some (599686697449891 : Int) := by decide +kernel

theorem geometryRow060_floor_parse :
    parseInteger geometryRow060_floorText = .ok geometryRowsTyped060.jensenFloorQ96 := by
  simp only [geometryRow060_floorText, parseInteger, String.toList_ofList, geometryRow060_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_060 :
    decodeGeometryRow geometryRowsJson060 = .ok geometryRowsTyped060 :=
  original_geometryRow_of_fields geometryRowsJson060 geometryRowsTyped060 geometryRow060_floorText
    geometryRow060_simplexId_read geometryRow060_vertexIds_read
    geometryRow060_physicalVolume_read geometryRow060_meanGap_read
    geometryRow060_factorMaxima_read geometryRow060_gapWeightedMeans_read
    geometryRow060_jensenBound_read geometryRow060_floor_text_read geometryRow060_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_060_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock030 : List SourceJson := [geometryRowsJson059, geometryRowsJson060]
noncomputable def geometryRowsTypedBlock030 : List (GeometryRow) := [geometryRowsTyped059, geometryRowsTyped060]
noncomputable def geometryRowsTypedThroughBlock030 : List (GeometryRow) := geometryRowsTypedThroughBlock029 ++ geometryRowsTypedBlock030

theorem geometry_Rows_block_030_push_eq (acc : List SourceJson) :
    SimplicesBlock030.blockPush acc = [geometryRowsJson060, geometryRowsJson059] ++ acc := by rfl

theorem geometry_Rows_block_030_reverse (acc : List SourceJson) :
    (SimplicesBlock030.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock030 := by
  rw [geometry_Rows_block_030_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_030 :
    geometryRowsJsonBlock030.mapM decodeGeometryRow = .ok geometryRowsTypedBlock030 := by
  simp only [geometryRowsJsonBlock030, geometryRowsTypedBlock030, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_059, decode_geometry_Rows_060]
  rfl

theorem decode_geometry_Rows_through_block_030 :
    SimplicesValue.arrayAcc031.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock030 := by
  change (SimplicesBlock030.blockPush SimplicesValue.arrayAcc030).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_030_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_029, decode_geometry_Rows_block_030]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_030_complete"
  err.flush

#print axioms geometryRow059_simplexId_read
#print axioms geometryRow059_vertexIds_read
#print axioms geometryRow059_physicalVolume_field
#print axioms geometryRow059_physicalVolume_numerator_no_slash
#print axioms geometryRow059_physicalVolume_numerator_parse
#print axioms geometryRow059_physicalVolume_denominator_parse
#print axioms geometryRow059_physicalVolume_denominator_nonzero
#print axioms geometryRow059_physicalVolume_parse
#print axioms geometryRow059_physicalVolume_read
#print axioms geometryRow059_meanGap_field
#print axioms geometryRow059_meanGap_numerator_no_slash
#print axioms geometryRow059_meanGap_numerator_parse
#print axioms geometryRow059_meanGap_denominator_parse
#print axioms geometryRow059_meanGap_denominator_nonzero
#print axioms geometryRow059_meanGap_parse
#print axioms geometryRow059_meanGap_read
#print axioms geometryRow059_jensenBound_field
#print axioms geometryRow059_jensenBound_numerator_no_slash
#print axioms geometryRow059_jensenBound_numerator_parse
#print axioms geometryRow059_jensenBound_denominator_parse
#print axioms geometryRow059_jensenBound_denominator_nonzero
#print axioms geometryRow059_jensenBound_parse
#print axioms geometryRow059_jensenBound_read
#print axioms geometryRow059_factorMaxima_read
#print axioms geometryRow059_gapWeightedMeans_read
#print axioms geometryRow059_floor_text_read
#print axioms geometryRow059_floor_chars_parse
#print axioms geometryRow059_floor_parse
#print axioms decode_geometry_Rows_059
#print axioms geometryRow060_simplexId_read
#print axioms geometryRow060_vertexIds_read
#print axioms geometryRow060_physicalVolume_field
#print axioms geometryRow060_physicalVolume_numerator_no_slash
#print axioms geometryRow060_physicalVolume_numerator_parse
#print axioms geometryRow060_physicalVolume_denominator_parse
#print axioms geometryRow060_physicalVolume_denominator_nonzero
#print axioms geometryRow060_physicalVolume_parse
#print axioms geometryRow060_physicalVolume_read
#print axioms geometryRow060_meanGap_field
#print axioms geometryRow060_meanGap_numerator_no_slash
#print axioms geometryRow060_meanGap_numerator_parse
#print axioms geometryRow060_meanGap_denominator_parse
#print axioms geometryRow060_meanGap_denominator_nonzero
#print axioms geometryRow060_meanGap_parse
#print axioms geometryRow060_meanGap_read
#print axioms geometryRow060_jensenBound_field
#print axioms geometryRow060_jensenBound_numerator_no_slash
#print axioms geometryRow060_jensenBound_numerator_parse
#print axioms geometryRow060_jensenBound_denominator_parse
#print axioms geometryRow060_jensenBound_denominator_nonzero
#print axioms geometryRow060_jensenBound_parse
#print axioms geometryRow060_jensenBound_read
#print axioms geometryRow060_factorMaxima_read
#print axioms geometryRow060_gapWeightedMeans_read
#print axioms geometryRow060_floor_text_read
#print axioms geometryRow060_floor_chars_parse
#print axioms geometryRow060_floor_parse
#print axioms decode_geometry_Rows_060
#print axioms geometry_Rows_block_030_push_eq
#print axioms geometry_Rows_block_030_reverse
#print axioms decode_geometry_Rows_block_030
#print axioms decode_geometry_Rows_through_block_030

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
