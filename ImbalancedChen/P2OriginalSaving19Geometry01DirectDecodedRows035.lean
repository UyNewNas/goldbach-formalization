import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows034

/-! Original simplices typed block 35, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson069 : SourceJson :=
  (SimplicesBlock035.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped069 : GeometryRow :=
  { simplexId := 69,
    vertexIds := #[39, 35, 34, 24, 23, 21, 20, 16, 1],
    physicalVolume := ((176912612176799270363411811460544010965359 : ℚ) / (29134576997793792000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((255988736502797 : ℚ) / (3668086800000000 : ℚ)), ((256673659447937 : ℚ) / (3668086800000000 : ℚ)), ((1626806124076759 : ℚ) / (11004260400000000 : ℚ)), ((260930756311 : ℚ) / (2445391200000 : ℚ)), ((128562767696443 : ℚ) / (2200852080000000 : ℚ)), ((103381343293513 : ℚ) / (2200852080000000 : ℚ)), ((24675822243763 : ℚ) / (579171600000000 : ℚ)), ((462964704733717 : ℚ) / (11004260400000000 : ℚ)), ((456750734103619 : ℚ) / (11004260400000000 : ℚ)), ((456749266868899 : ℚ) / (11004260400000000 : ℚ))],
    jensenBound := ((3410355327117343221686398200796336174686838067033062693911920017749991852869256117090302510346498383995136000000000000000000 : ℚ) / (883481060907724869484845790450818126491965112476317873018557579297158471629619651765232670313952161058888841860113670238824468315303234076049 : ℚ)),
    jensenFloorQ96 := (305831327963 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_simplexId_before"
  err.flush

theorem geometryRow069_simplexId_read :
    geometryRowsJson069.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped069.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_vertexIds_before"
  err.flush

theorem geometryRow069_vertexIds_read :
    geometryRowsJson069.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped069.vertexIds := by decide +kernel

noncomputable def geometryRow069_physicalVolumeNumeratorChars : List Char := ['1', '7', '6', '9', '1', '2', '6', '1', '2', '1', '7', '6', '7', '9', '9', '2', '7', '0', '3', '6', '3', '4', '1', '1', '8', '1', '1', '4', '6', '0', '5', '4', '4', '0', '1', '0', '9', '6', '5', '3', '5', '9']
noncomputable def geometryRow069_physicalVolumeDenominatorChars : List Char := ['2', '9', '1', '3', '4', '5', '7', '6', '9', '9', '7', '7', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow069_physicalVolumeText : String := String.ofList (geometryRow069_physicalVolumeNumeratorChars ++ '/' :: geometryRow069_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_physicalVolume_before_field"
  err.flush

theorem geometryRow069_physicalVolume_field :
    geometryRowsJson069.getObjVal? "physical_volume" = .ok (.str geometryRow069_physicalVolumeText) := by rfl

theorem geometryRow069_physicalVolume_numerator_no_slash :
    geometryRow069_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow069_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow069_physicalVolumeNumeratorChars = some (176912612176799270363411811460544010965359 : Int) := by decide +kernel

theorem geometryRow069_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow069_physicalVolumeDenominatorChars = some (29134576997793792000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow069_physicalVolume_denominator_nonzero : (29134576997793792000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow069_physicalVolume_parse :
    parseRational geometryRow069_physicalVolumeText = .ok geometryRowsTyped069.physicalVolume :=
  original_rational_fraction_of_chars geometryRow069_physicalVolumeNumeratorChars geometryRow069_physicalVolumeDenominatorChars
    (176912612176799270363411811460544010965359 : Int) (29134576997793792000000000000000000000000000000000000000000000000000 : Int)
    geometryRow069_physicalVolume_numerator_no_slash geometryRow069_physicalVolume_numerator_parse
    geometryRow069_physicalVolume_denominator_parse geometryRow069_physicalVolume_denominator_nonzero

theorem geometryRow069_physicalVolume_read :
    rationalField geometryRowsJson069 "physical_volume" = .ok geometryRowsTyped069.physicalVolume :=
  original_rationalField_of_string geometryRowsJson069 "physical_volume" geometryRow069_physicalVolumeText
    geometryRowsTyped069.physicalVolume geometryRow069_physicalVolume_field geometryRow069_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_physicalVolume_complete"
  err.flush

noncomputable def geometryRow069_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow069_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow069_meanGapText : String := String.ofList (geometryRow069_meanGapNumeratorChars ++ '/' :: geometryRow069_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_meanGap_before_field"
  err.flush

theorem geometryRow069_meanGap_field :
    geometryRowsJson069.getObjVal? "mean_gap" = .ok (.str geometryRow069_meanGapText) := by rfl

theorem geometryRow069_meanGap_numerator_no_slash :
    geometryRow069_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow069_meanGap_numerator_parse :
    SourceJson.intChars geometryRow069_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow069_meanGap_denominator_parse :
    SourceJson.intChars geometryRow069_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow069_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow069_meanGap_parse :
    parseRational geometryRow069_meanGapText = .ok geometryRowsTyped069.meanGap :=
  original_rational_fraction_of_chars geometryRow069_meanGapNumeratorChars geometryRow069_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow069_meanGap_numerator_no_slash geometryRow069_meanGap_numerator_parse
    geometryRow069_meanGap_denominator_parse geometryRow069_meanGap_denominator_nonzero

theorem geometryRow069_meanGap_read :
    rationalField geometryRowsJson069 "mean_gap" = .ok geometryRowsTyped069.meanGap :=
  original_rationalField_of_string geometryRowsJson069 "mean_gap" geometryRow069_meanGapText
    geometryRowsTyped069.meanGap geometryRow069_meanGap_field geometryRow069_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_meanGap_complete"
  err.flush

noncomputable def geometryRow069_jensenBoundNumeratorChars : List Char := ['3', '4', '1', '0', '3', '5', '5', '3', '2', '7', '1', '1', '7', '3', '4', '3', '2', '2', '1', '6', '8', '6', '3', '9', '8', '2', '0', '0', '7', '9', '6', '3', '3', '6', '1', '7', '4', '6', '8', '6', '8', '3', '8', '0', '6', '7', '0', '3', '3', '0', '6', '2', '6', '9', '3', '9', '1', '1', '9', '2', '0', '0', '1', '7', '7', '4', '9', '9', '9', '1', '8', '5', '2', '8', '6', '9', '2', '5', '6', '1', '1', '7', '0', '9', '0', '3', '0', '2', '5', '1', '0', '3', '4', '6', '4', '9', '8', '3', '8', '3', '9', '9', '5', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow069_jensenBoundDenominatorChars : List Char := ['8', '8', '3', '4', '8', '1', '0', '6', '0', '9', '0', '7', '7', '2', '4', '8', '6', '9', '4', '8', '4', '8', '4', '5', '7', '9', '0', '4', '5', '0', '8', '1', '8', '1', '2', '6', '4', '9', '1', '9', '6', '5', '1', '1', '2', '4', '7', '6', '3', '1', '7', '8', '7', '3', '0', '1', '8', '5', '5', '7', '5', '7', '9', '2', '9', '7', '1', '5', '8', '4', '7', '1', '6', '2', '9', '6', '1', '9', '6', '5', '1', '7', '6', '5', '2', '3', '2', '6', '7', '0', '3', '1', '3', '9', '5', '2', '1', '6', '1', '0', '5', '8', '8', '8', '8', '8', '4', '1', '8', '6', '0', '1', '1', '3', '6', '7', '0', '2', '3', '8', '8', '2', '4', '4', '6', '8', '3', '1', '5', '3', '0', '3', '2', '3', '4', '0', '7', '6', '0', '4', '9']
noncomputable def geometryRow069_jensenBoundText : String := String.ofList (geometryRow069_jensenBoundNumeratorChars ++ '/' :: geometryRow069_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_jensenBound_before_field"
  err.flush

theorem geometryRow069_jensenBound_field :
    geometryRowsJson069.getObjVal? "jensen_bound" = .ok (.str geometryRow069_jensenBoundText) := by rfl

theorem geometryRow069_jensenBound_numerator_no_slash :
    geometryRow069_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow069_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow069_jensenBoundNumeratorChars = some (3410355327117343221686398200796336174686838067033062693911920017749991852869256117090302510346498383995136000000000000000000 : Int) := by decide +kernel

theorem geometryRow069_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow069_jensenBoundDenominatorChars = some (883481060907724869484845790450818126491965112476317873018557579297158471629619651765232670313952161058888841860113670238824468315303234076049 : Int) := by decide +kernel

theorem geometryRow069_jensenBound_denominator_nonzero : (883481060907724869484845790450818126491965112476317873018557579297158471629619651765232670313952161058888841860113670238824468315303234076049 : Int) ≠ 0 := by decide +kernel

theorem geometryRow069_jensenBound_parse :
    parseRational geometryRow069_jensenBoundText = .ok geometryRowsTyped069.jensenBound :=
  original_rational_fraction_of_chars geometryRow069_jensenBoundNumeratorChars geometryRow069_jensenBoundDenominatorChars
    (3410355327117343221686398200796336174686838067033062693911920017749991852869256117090302510346498383995136000000000000000000 : Int) (883481060907724869484845790450818126491965112476317873018557579297158471629619651765232670313952161058888841860113670238824468315303234076049 : Int)
    geometryRow069_jensenBound_numerator_no_slash geometryRow069_jensenBound_numerator_parse
    geometryRow069_jensenBound_denominator_parse geometryRow069_jensenBound_denominator_nonzero

theorem geometryRow069_jensenBound_read :
    rationalField geometryRowsJson069 "jensen_bound" = .ok geometryRowsTyped069.jensenBound :=
  original_rationalField_of_string geometryRowsJson069 "jensen_bound" geometryRow069_jensenBoundText
    geometryRowsTyped069.jensenBound geometryRow069_jensenBound_field geometryRow069_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_factorMaxima_before"
  err.flush

theorem geometryRow069_factorMaxima_read :
    rationalArrayField geometryRowsJson069 "factor_maxima" = .ok geometryRowsTyped069.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_gapWeightedMeans_before"
  err.flush

theorem geometryRow069_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson069 "gap_weighted_means" = .ok geometryRowsTyped069.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow069_floorChars : List Char := ['3', '0', '5', '8', '3', '1', '3', '2', '7', '9', '6', '3']
noncomputable def geometryRow069_floorText : String := String.ofList geometryRow069_floorChars

theorem geometryRow069_floor_text_read :
    geometryRowsJson069.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow069_floorText := by rfl

theorem geometryRow069_floor_chars_parse :
    SourceJson.intChars geometryRow069_floorChars = some (305831327963 : Int) := by decide +kernel

theorem geometryRow069_floor_parse :
    parseInteger geometryRow069_floorText = .ok geometryRowsTyped069.jensenFloorQ96 := by
  simp only [geometryRow069_floorText, parseInteger, String.toList_ofList, geometryRow069_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_069 :
    decodeGeometryRow geometryRowsJson069 = .ok geometryRowsTyped069 :=
  original_geometryRow_of_fields geometryRowsJson069 geometryRowsTyped069 geometryRow069_floorText
    geometryRow069_simplexId_read geometryRow069_vertexIds_read
    geometryRow069_physicalVolume_read geometryRow069_meanGap_read
    geometryRow069_factorMaxima_read geometryRow069_gapWeightedMeans_read
    geometryRow069_jensenBound_read geometryRow069_floor_text_read geometryRow069_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_069_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson070 : SourceJson :=
  (SimplicesBlock035.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped070 : GeometryRow :=
  { simplexId := 70,
    vertexIds := #[39, 35, 34, 32, 24, 23, 21, 20, 16],
    physicalVolume := ((5206634501275833476295728836623100382701 : ℚ) / (7283644249448448000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((23836965316919 : ℚ) / (366808680000000 : ℚ)), ((23905457611433 : ℚ) / (366808680000000 : ℚ)), ((20601832775987 : ℚ) / (137553255000000 : ℚ)), ((65852924855849 : ℚ) / (611347800000000 : ℚ)), ((321900914245789 : ℚ) / (5502130200000000 : ℚ)), ((123891554616341 : ℚ) / (2751065100000000 : ℚ)), ((6302853639841 : ℚ) / (144792900000000 : ℚ)), ((59142619841267 : ℚ) / (1375532550000000 : ℚ)), ((233463494050019 : ℚ) / (5502130200000000 : ℚ)), ((233462760432659 : ℚ) / (5502130200000000 : ℚ))],
    jensenBound := ((16121089596130401751373115213859172503470501187572460789446099453294626012710714560429875764881561063281250000000000000 : ℚ) / (32969597312302559976083622554562102924007703675461353425349216610757259810186586901625981664550104043905942629580973384580619539340226077 : ℚ)),
    jensenFloorQ96 := (38740063893 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_simplexId_before"
  err.flush

theorem geometryRow070_simplexId_read :
    geometryRowsJson070.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped070.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_vertexIds_before"
  err.flush

theorem geometryRow070_vertexIds_read :
    geometryRowsJson070.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped070.vertexIds := by decide +kernel

noncomputable def geometryRow070_physicalVolumeNumeratorChars : List Char := ['5', '2', '0', '6', '6', '3', '4', '5', '0', '1', '2', '7', '5', '8', '3', '3', '4', '7', '6', '2', '9', '5', '7', '2', '8', '8', '3', '6', '6', '2', '3', '1', '0', '0', '3', '8', '2', '7', '0', '1']
noncomputable def geometryRow070_physicalVolumeDenominatorChars : List Char := ['7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow070_physicalVolumeText : String := String.ofList (geometryRow070_physicalVolumeNumeratorChars ++ '/' :: geometryRow070_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_physicalVolume_before_field"
  err.flush

theorem geometryRow070_physicalVolume_field :
    geometryRowsJson070.getObjVal? "physical_volume" = .ok (.str geometryRow070_physicalVolumeText) := by rfl

theorem geometryRow070_physicalVolume_numerator_no_slash :
    geometryRow070_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow070_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow070_physicalVolumeNumeratorChars = some (5206634501275833476295728836623100382701 : Int) := by decide +kernel

theorem geometryRow070_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow070_physicalVolumeDenominatorChars = some (7283644249448448000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow070_physicalVolume_denominator_nonzero : (7283644249448448000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow070_physicalVolume_parse :
    parseRational geometryRow070_physicalVolumeText = .ok geometryRowsTyped070.physicalVolume :=
  original_rational_fraction_of_chars geometryRow070_physicalVolumeNumeratorChars geometryRow070_physicalVolumeDenominatorChars
    (5206634501275833476295728836623100382701 : Int) (7283644249448448000000000000000000000000000000000000000000000000000 : Int)
    geometryRow070_physicalVolume_numerator_no_slash geometryRow070_physicalVolume_numerator_parse
    geometryRow070_physicalVolume_denominator_parse geometryRow070_physicalVolume_denominator_nonzero

theorem geometryRow070_physicalVolume_read :
    rationalField geometryRowsJson070 "physical_volume" = .ok geometryRowsTyped070.physicalVolume :=
  original_rationalField_of_string geometryRowsJson070 "physical_volume" geometryRow070_physicalVolumeText
    geometryRowsTyped070.physicalVolume geometryRow070_physicalVolume_field geometryRow070_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_physicalVolume_complete"
  err.flush

noncomputable def geometryRow070_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow070_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow070_meanGapText : String := String.ofList (geometryRow070_meanGapNumeratorChars ++ '/' :: geometryRow070_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_meanGap_before_field"
  err.flush

theorem geometryRow070_meanGap_field :
    geometryRowsJson070.getObjVal? "mean_gap" = .ok (.str geometryRow070_meanGapText) := by rfl

theorem geometryRow070_meanGap_numerator_no_slash :
    geometryRow070_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow070_meanGap_numerator_parse :
    SourceJson.intChars geometryRow070_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow070_meanGap_denominator_parse :
    SourceJson.intChars geometryRow070_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow070_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow070_meanGap_parse :
    parseRational geometryRow070_meanGapText = .ok geometryRowsTyped070.meanGap :=
  original_rational_fraction_of_chars geometryRow070_meanGapNumeratorChars geometryRow070_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow070_meanGap_numerator_no_slash geometryRow070_meanGap_numerator_parse
    geometryRow070_meanGap_denominator_parse geometryRow070_meanGap_denominator_nonzero

theorem geometryRow070_meanGap_read :
    rationalField geometryRowsJson070 "mean_gap" = .ok geometryRowsTyped070.meanGap :=
  original_rationalField_of_string geometryRowsJson070 "mean_gap" geometryRow070_meanGapText
    geometryRowsTyped070.meanGap geometryRow070_meanGap_field geometryRow070_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_meanGap_complete"
  err.flush

noncomputable def geometryRow070_jensenBoundNumeratorChars : List Char := ['1', '6', '1', '2', '1', '0', '8', '9', '5', '9', '6', '1', '3', '0', '4', '0', '1', '7', '5', '1', '3', '7', '3', '1', '1', '5', '2', '1', '3', '8', '5', '9', '1', '7', '2', '5', '0', '3', '4', '7', '0', '5', '0', '1', '1', '8', '7', '5', '7', '2', '4', '6', '0', '7', '8', '9', '4', '4', '6', '0', '9', '9', '4', '5', '3', '2', '9', '4', '6', '2', '6', '0', '1', '2', '7', '1', '0', '7', '1', '4', '5', '6', '0', '4', '2', '9', '8', '7', '5', '7', '6', '4', '8', '8', '1', '5', '6', '1', '0', '6', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow070_jensenBoundDenominatorChars : List Char := ['3', '2', '9', '6', '9', '5', '9', '7', '3', '1', '2', '3', '0', '2', '5', '5', '9', '9', '7', '6', '0', '8', '3', '6', '2', '2', '5', '5', '4', '5', '6', '2', '1', '0', '2', '9', '2', '4', '0', '0', '7', '7', '0', '3', '6', '7', '5', '4', '6', '1', '3', '5', '3', '4', '2', '5', '3', '4', '9', '2', '1', '6', '6', '1', '0', '7', '5', '7', '2', '5', '9', '8', '1', '0', '1', '8', '6', '5', '8', '6', '9', '0', '1', '6', '2', '5', '9', '8', '1', '6', '6', '4', '5', '5', '0', '1', '0', '4', '0', '4', '3', '9', '0', '5', '9', '4', '2', '6', '2', '9', '5', '8', '0', '9', '7', '3', '3', '8', '4', '5', '8', '0', '6', '1', '9', '5', '3', '9', '3', '4', '0', '2', '2', '6', '0', '7', '7']
noncomputable def geometryRow070_jensenBoundText : String := String.ofList (geometryRow070_jensenBoundNumeratorChars ++ '/' :: geometryRow070_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_jensenBound_before_field"
  err.flush

theorem geometryRow070_jensenBound_field :
    geometryRowsJson070.getObjVal? "jensen_bound" = .ok (.str geometryRow070_jensenBoundText) := by rfl

theorem geometryRow070_jensenBound_numerator_no_slash :
    geometryRow070_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow070_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow070_jensenBoundNumeratorChars = some (16121089596130401751373115213859172503470501187572460789446099453294626012710714560429875764881561063281250000000000000 : Int) := by decide +kernel

theorem geometryRow070_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow070_jensenBoundDenominatorChars = some (32969597312302559976083622554562102924007703675461353425349216610757259810186586901625981664550104043905942629580973384580619539340226077 : Int) := by decide +kernel

theorem geometryRow070_jensenBound_denominator_nonzero : (32969597312302559976083622554562102924007703675461353425349216610757259810186586901625981664550104043905942629580973384580619539340226077 : Int) ≠ 0 := by decide +kernel

theorem geometryRow070_jensenBound_parse :
    parseRational geometryRow070_jensenBoundText = .ok geometryRowsTyped070.jensenBound :=
  original_rational_fraction_of_chars geometryRow070_jensenBoundNumeratorChars geometryRow070_jensenBoundDenominatorChars
    (16121089596130401751373115213859172503470501187572460789446099453294626012710714560429875764881561063281250000000000000 : Int) (32969597312302559976083622554562102924007703675461353425349216610757259810186586901625981664550104043905942629580973384580619539340226077 : Int)
    geometryRow070_jensenBound_numerator_no_slash geometryRow070_jensenBound_numerator_parse
    geometryRow070_jensenBound_denominator_parse geometryRow070_jensenBound_denominator_nonzero

theorem geometryRow070_jensenBound_read :
    rationalField geometryRowsJson070 "jensen_bound" = .ok geometryRowsTyped070.jensenBound :=
  original_rationalField_of_string geometryRowsJson070 "jensen_bound" geometryRow070_jensenBoundText
    geometryRowsTyped070.jensenBound geometryRow070_jensenBound_field geometryRow070_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_factorMaxima_before"
  err.flush

theorem geometryRow070_factorMaxima_read :
    rationalArrayField geometryRowsJson070 "factor_maxima" = .ok geometryRowsTyped070.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_gapWeightedMeans_before"
  err.flush

theorem geometryRow070_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson070 "gap_weighted_means" = .ok geometryRowsTyped070.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow070_floorChars : List Char := ['3', '8', '7', '4', '0', '0', '6', '3', '8', '9', '3']
noncomputable def geometryRow070_floorText : String := String.ofList geometryRow070_floorChars

theorem geometryRow070_floor_text_read :
    geometryRowsJson070.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow070_floorText := by rfl

theorem geometryRow070_floor_chars_parse :
    SourceJson.intChars geometryRow070_floorChars = some (38740063893 : Int) := by decide +kernel

theorem geometryRow070_floor_parse :
    parseInteger geometryRow070_floorText = .ok geometryRowsTyped070.jensenFloorQ96 := by
  simp only [geometryRow070_floorText, parseInteger, String.toList_ofList, geometryRow070_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_070 :
    decodeGeometryRow geometryRowsJson070 = .ok geometryRowsTyped070 :=
  original_geometryRow_of_fields geometryRowsJson070 geometryRowsTyped070 geometryRow070_floorText
    geometryRow070_simplexId_read geometryRow070_vertexIds_read
    geometryRow070_physicalVolume_read geometryRow070_meanGap_read
    geometryRow070_factorMaxima_read geometryRow070_gapWeightedMeans_read
    geometryRow070_jensenBound_read geometryRow070_floor_text_read geometryRow070_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_070_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock035 : List SourceJson := [geometryRowsJson069, geometryRowsJson070]
noncomputable def geometryRowsTypedBlock035 : List (GeometryRow) := [geometryRowsTyped069, geometryRowsTyped070]
noncomputable def geometryRowsTypedThroughBlock035 : List (GeometryRow) := geometryRowsTypedThroughBlock034 ++ geometryRowsTypedBlock035

theorem geometry_Rows_block_035_push_eq (acc : List SourceJson) :
    SimplicesBlock035.blockPush acc = [geometryRowsJson070, geometryRowsJson069] ++ acc := by rfl

theorem geometry_Rows_block_035_reverse (acc : List SourceJson) :
    (SimplicesBlock035.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock035 := by
  rw [geometry_Rows_block_035_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_035 :
    geometryRowsJsonBlock035.mapM decodeGeometryRow = .ok geometryRowsTypedBlock035 := by
  simp only [geometryRowsJsonBlock035, geometryRowsTypedBlock035, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_069, decode_geometry_Rows_070]
  rfl

theorem decode_geometry_Rows_through_block_035 :
    SimplicesValue.arrayAcc036.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock035 := by
  change (SimplicesBlock035.blockPush SimplicesValue.arrayAcc035).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_035_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_034, decode_geometry_Rows_block_035]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_035_complete"
  err.flush

#print axioms geometryRow069_simplexId_read
#print axioms geometryRow069_vertexIds_read
#print axioms geometryRow069_physicalVolume_field
#print axioms geometryRow069_physicalVolume_numerator_no_slash
#print axioms geometryRow069_physicalVolume_numerator_parse
#print axioms geometryRow069_physicalVolume_denominator_parse
#print axioms geometryRow069_physicalVolume_denominator_nonzero
#print axioms geometryRow069_physicalVolume_parse
#print axioms geometryRow069_physicalVolume_read
#print axioms geometryRow069_meanGap_field
#print axioms geometryRow069_meanGap_numerator_no_slash
#print axioms geometryRow069_meanGap_numerator_parse
#print axioms geometryRow069_meanGap_denominator_parse
#print axioms geometryRow069_meanGap_denominator_nonzero
#print axioms geometryRow069_meanGap_parse
#print axioms geometryRow069_meanGap_read
#print axioms geometryRow069_jensenBound_field
#print axioms geometryRow069_jensenBound_numerator_no_slash
#print axioms geometryRow069_jensenBound_numerator_parse
#print axioms geometryRow069_jensenBound_denominator_parse
#print axioms geometryRow069_jensenBound_denominator_nonzero
#print axioms geometryRow069_jensenBound_parse
#print axioms geometryRow069_jensenBound_read
#print axioms geometryRow069_factorMaxima_read
#print axioms geometryRow069_gapWeightedMeans_read
#print axioms geometryRow069_floor_text_read
#print axioms geometryRow069_floor_chars_parse
#print axioms geometryRow069_floor_parse
#print axioms decode_geometry_Rows_069
#print axioms geometryRow070_simplexId_read
#print axioms geometryRow070_vertexIds_read
#print axioms geometryRow070_physicalVolume_field
#print axioms geometryRow070_physicalVolume_numerator_no_slash
#print axioms geometryRow070_physicalVolume_numerator_parse
#print axioms geometryRow070_physicalVolume_denominator_parse
#print axioms geometryRow070_physicalVolume_denominator_nonzero
#print axioms geometryRow070_physicalVolume_parse
#print axioms geometryRow070_physicalVolume_read
#print axioms geometryRow070_meanGap_field
#print axioms geometryRow070_meanGap_numerator_no_slash
#print axioms geometryRow070_meanGap_numerator_parse
#print axioms geometryRow070_meanGap_denominator_parse
#print axioms geometryRow070_meanGap_denominator_nonzero
#print axioms geometryRow070_meanGap_parse
#print axioms geometryRow070_meanGap_read
#print axioms geometryRow070_jensenBound_field
#print axioms geometryRow070_jensenBound_numerator_no_slash
#print axioms geometryRow070_jensenBound_numerator_parse
#print axioms geometryRow070_jensenBound_denominator_parse
#print axioms geometryRow070_jensenBound_denominator_nonzero
#print axioms geometryRow070_jensenBound_parse
#print axioms geometryRow070_jensenBound_read
#print axioms geometryRow070_factorMaxima_read
#print axioms geometryRow070_gapWeightedMeans_read
#print axioms geometryRow070_floor_text_read
#print axioms geometryRow070_floor_chars_parse
#print axioms geometryRow070_floor_parse
#print axioms decode_geometry_Rows_070
#print axioms geometry_Rows_block_035_push_eq
#print axioms geometry_Rows_block_035_reverse
#print axioms decode_geometry_Rows_block_035
#print axioms decode_geometry_Rows_through_block_035

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
