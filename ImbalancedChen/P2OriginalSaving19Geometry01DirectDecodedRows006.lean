import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows005

/-! Original simplices typed block 6, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson012 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped012 : GeometryRow :=
  { simplexId := 12,
    vertexIds := #[39, 35, 29, 28, 10, 8, 3, 1, 0],
    physicalVolume := ((33610968462058490340207907493300351 : ℚ) / (17112760320000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((653097122179 : ℚ) / (7425600000000 : ℚ)), ((660603224419 : ℚ) / (7425600000000 : ℚ)), ((122773038863 : ℚ) / (856800000000 : ℚ)), ((842425129097 : ℚ) / (7425600000000 : ℚ)), ((85305858457 : ℚ) / (1310400000000 : ℚ)), ((549516907141 : ℚ) / (11138400000000 : ℚ)), ((3364945916233 : ℚ) / (89107200000000 : ℚ)), ((3180066901003 : ℚ) / (89107200000000 : ℚ)), ((709909245547 : ℚ) / (22276800000000 : ℚ)), ((709904790187 : ℚ) / (22276800000000 : ℚ))],
    jensenBound := ((89015037850131542492141827067546214487120465132982079686559061075008356501422080000000000000000000000000 : ℚ) / (11280542305443610000130920626716429777434825891851540467960337745981261688661632477075276985984195327257442650835451777 : ℚ)),
    jensenFloorQ96 := (625191386552427 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_simplexId_before"
  err.flush

theorem geometryRow012_simplexId_read :
    geometryRowsJson012.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped012.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_vertexIds_before"
  err.flush

theorem geometryRow012_vertexIds_read :
    geometryRowsJson012.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped012.vertexIds := by decide +kernel

noncomputable def geometryRow012_physicalVolumeNumeratorChars : List Char := ['3', '3', '6', '1', '0', '9', '6', '8', '4', '6', '2', '0', '5', '8', '4', '9', '0', '3', '4', '0', '2', '0', '7', '9', '0', '7', '4', '9', '3', '3', '0', '0', '3', '5', '1']
noncomputable def geometryRow012_physicalVolumeDenominatorChars : List Char := ['1', '7', '1', '1', '2', '7', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_physicalVolumeText : String := String.ofList (geometryRow012_physicalVolumeNumeratorChars ++ '/' :: geometryRow012_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_physicalVolume_before_field"
  err.flush

theorem geometryRow012_physicalVolume_field :
    geometryRowsJson012.getObjVal? "physical_volume" = .ok (.str geometryRow012_physicalVolumeText) := by rfl

theorem geometryRow012_physicalVolume_numerator_no_slash :
    geometryRow012_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeNumeratorChars = some (33610968462058490340207907493300351 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeDenominatorChars = some (17112760320000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_nonzero : (17112760320000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_physicalVolume_parse :
    parseRational geometryRow012_physicalVolumeText = .ok geometryRowsTyped012.physicalVolume :=
  original_rational_fraction_of_chars geometryRow012_physicalVolumeNumeratorChars geometryRow012_physicalVolumeDenominatorChars
    (33610968462058490340207907493300351 : Int) (17112760320000000000000000000000000000000000000000000000000 : Int)
    geometryRow012_physicalVolume_numerator_no_slash geometryRow012_physicalVolume_numerator_parse
    geometryRow012_physicalVolume_denominator_parse geometryRow012_physicalVolume_denominator_nonzero

theorem geometryRow012_physicalVolume_read :
    rationalField geometryRowsJson012 "physical_volume" = .ok geometryRowsTyped012.physicalVolume :=
  original_rationalField_of_string geometryRowsJson012 "physical_volume" geometryRow012_physicalVolumeText
    geometryRowsTyped012.physicalVolume geometryRow012_physicalVolume_field geometryRow012_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_physicalVolume_complete"
  err.flush

noncomputable def geometryRow012_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow012_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_meanGapText : String := String.ofList (geometryRow012_meanGapNumeratorChars ++ '/' :: geometryRow012_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_meanGap_before_field"
  err.flush

theorem geometryRow012_meanGap_field :
    geometryRowsJson012.getObjVal? "mean_gap" = .ok (.str geometryRow012_meanGapText) := by rfl

theorem geometryRow012_meanGap_numerator_no_slash :
    geometryRow012_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_meanGap_numerator_parse :
    SourceJson.intChars geometryRow012_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_parse :
    SourceJson.intChars geometryRow012_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_meanGap_parse :
    parseRational geometryRow012_meanGapText = .ok geometryRowsTyped012.meanGap :=
  original_rational_fraction_of_chars geometryRow012_meanGapNumeratorChars geometryRow012_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow012_meanGap_numerator_no_slash geometryRow012_meanGap_numerator_parse
    geometryRow012_meanGap_denominator_parse geometryRow012_meanGap_denominator_nonzero

theorem geometryRow012_meanGap_read :
    rationalField geometryRowsJson012 "mean_gap" = .ok geometryRowsTyped012.meanGap :=
  original_rationalField_of_string geometryRowsJson012 "mean_gap" geometryRow012_meanGapText
    geometryRowsTyped012.meanGap geometryRow012_meanGap_field geometryRow012_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_meanGap_complete"
  err.flush

noncomputable def geometryRow012_jensenBoundNumeratorChars : List Char := ['8', '9', '0', '1', '5', '0', '3', '7', '8', '5', '0', '1', '3', '1', '5', '4', '2', '4', '9', '2', '1', '4', '1', '8', '2', '7', '0', '6', '7', '5', '4', '6', '2', '1', '4', '4', '8', '7', '1', '2', '0', '4', '6', '5', '1', '3', '2', '9', '8', '2', '0', '7', '9', '6', '8', '6', '5', '5', '9', '0', '6', '1', '0', '7', '5', '0', '0', '8', '3', '5', '6', '5', '0', '1', '4', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_jensenBoundDenominatorChars : List Char := ['1', '1', '2', '8', '0', '5', '4', '2', '3', '0', '5', '4', '4', '3', '6', '1', '0', '0', '0', '0', '1', '3', '0', '9', '2', '0', '6', '2', '6', '7', '1', '6', '4', '2', '9', '7', '7', '7', '4', '3', '4', '8', '2', '5', '8', '9', '1', '8', '5', '1', '5', '4', '0', '4', '6', '7', '9', '6', '0', '3', '3', '7', '7', '4', '5', '9', '8', '1', '2', '6', '1', '6', '8', '8', '6', '6', '1', '6', '3', '2', '4', '7', '7', '0', '7', '5', '2', '7', '6', '9', '8', '5', '9', '8', '4', '1', '9', '5', '3', '2', '7', '2', '5', '7', '4', '4', '2', '6', '5', '0', '8', '3', '5', '4', '5', '1', '7', '7', '7']
noncomputable def geometryRow012_jensenBoundText : String := String.ofList (geometryRow012_jensenBoundNumeratorChars ++ '/' :: geometryRow012_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_jensenBound_before_field"
  err.flush

theorem geometryRow012_jensenBound_field :
    geometryRowsJson012.getObjVal? "jensen_bound" = .ok (.str geometryRow012_jensenBoundText) := by rfl

theorem geometryRow012_jensenBound_numerator_no_slash :
    geometryRow012_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow012_jensenBoundNumeratorChars = some (89015037850131542492141827067546214487120465132982079686559061075008356501422080000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow012_jensenBoundDenominatorChars = some (11280542305443610000130920626716429777434825891851540467960337745981261688661632477075276985984195327257442650835451777 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_nonzero : (11280542305443610000130920626716429777434825891851540467960337745981261688661632477075276985984195327257442650835451777 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_jensenBound_parse :
    parseRational geometryRow012_jensenBoundText = .ok geometryRowsTyped012.jensenBound :=
  original_rational_fraction_of_chars geometryRow012_jensenBoundNumeratorChars geometryRow012_jensenBoundDenominatorChars
    (89015037850131542492141827067546214487120465132982079686559061075008356501422080000000000000000000000000 : Int) (11280542305443610000130920626716429777434825891851540467960337745981261688661632477075276985984195327257442650835451777 : Int)
    geometryRow012_jensenBound_numerator_no_slash geometryRow012_jensenBound_numerator_parse
    geometryRow012_jensenBound_denominator_parse geometryRow012_jensenBound_denominator_nonzero

theorem geometryRow012_jensenBound_read :
    rationalField geometryRowsJson012 "jensen_bound" = .ok geometryRowsTyped012.jensenBound :=
  original_rationalField_of_string geometryRowsJson012 "jensen_bound" geometryRow012_jensenBoundText
    geometryRowsTyped012.jensenBound geometryRow012_jensenBound_field geometryRow012_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_factorMaxima_before"
  err.flush

theorem geometryRow012_factorMaxima_read :
    rationalArrayField geometryRowsJson012 "factor_maxima" = .ok geometryRowsTyped012.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_gapWeightedMeans_before"
  err.flush

theorem geometryRow012_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson012 "gap_weighted_means" = .ok geometryRowsTyped012.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow012_floorChars : List Char := ['6', '2', '5', '1', '9', '1', '3', '8', '6', '5', '5', '2', '4', '2', '7']
noncomputable def geometryRow012_floorText : String := String.ofList geometryRow012_floorChars

theorem geometryRow012_floor_text_read :
    geometryRowsJson012.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow012_floorText := by rfl

theorem geometryRow012_floor_chars_parse :
    SourceJson.intChars geometryRow012_floorChars = some (625191386552427 : Int) := by decide +kernel

theorem geometryRow012_floor_parse :
    parseInteger geometryRow012_floorText = .ok geometryRowsTyped012.jensenFloorQ96 := by
  simp only [geometryRow012_floorText, parseInteger, String.toList_ofList, geometryRow012_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_012 :
    decodeGeometryRow geometryRowsJson012 = .ok geometryRowsTyped012 :=
  original_geometryRow_of_fields geometryRowsJson012 geometryRowsTyped012 geometryRow012_floorText
    geometryRow012_simplexId_read geometryRow012_vertexIds_read
    geometryRow012_physicalVolume_read geometryRow012_meanGap_read
    geometryRow012_factorMaxima_read geometryRow012_gapWeightedMeans_read
    geometryRow012_jensenBound_read geometryRow012_floor_text_read geometryRow012_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_012_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson013 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped013 : GeometryRow :=
  { simplexId := 13,
    vertexIds := #[39, 35, 29, 28, 10, 8, 3, 2, 0],
    physicalVolume := ((1061081127522485195373355150457173508239 : ℚ) / (102676561920000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((24670376435756189 : ℚ) / (284830899600000000 : ℚ)), ((2460890642481782437 : ℚ) / (27913428160800000000 : ℚ)), ((1849526186951820731 : ℚ) / (12883120689600000000 : ℚ)), ((6423354006294744187 : ℚ) / (55826856321600000000 : ℚ)), ((160553216514632003 : ℚ) / (2462949543600000000 : ℚ)), ((8037854507660643277 : ℚ) / (167480568964800000000 : ℚ)), ((25358888048642342693 : ℚ) / (669922275859200000000 : ℚ)), ((23968937846621750663 : ℚ) / (669922275859200000000 : ℚ)), ((1345295014875873713 : ℚ) / (41870142241200000000 : ℚ)), ((2646219196979738761 : ℚ) / (83740284482400000000 : ℚ))],
    jensenBound := ((175843166991171645462459020688718244435915838813698609848990015088691814852733338034043826460880580623382580500532985305655831282845090436121084231680000000000000000000000000 : ℚ) / (2014057797005895055349951576191054385891962239783289998135194639243678791386645474539655798089695005846864035850426677149394573245457031269670480183685017828001980411748826170117400437 : ℚ)),
    jensenFloorQ96 := (6917244893423826579 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_simplexId_before"
  err.flush

theorem geometryRow013_simplexId_read :
    geometryRowsJson013.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped013.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_vertexIds_before"
  err.flush

theorem geometryRow013_vertexIds_read :
    geometryRowsJson013.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped013.vertexIds := by decide +kernel

noncomputable def geometryRow013_physicalVolumeNumeratorChars : List Char := ['1', '0', '6', '1', '0', '8', '1', '1', '2', '7', '5', '2', '2', '4', '8', '5', '1', '9', '5', '3', '7', '3', '3', '5', '5', '1', '5', '0', '4', '5', '7', '1', '7', '3', '5', '0', '8', '2', '3', '9']
noncomputable def geometryRow013_physicalVolumeDenominatorChars : List Char := ['1', '0', '2', '6', '7', '6', '5', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_physicalVolumeText : String := String.ofList (geometryRow013_physicalVolumeNumeratorChars ++ '/' :: geometryRow013_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_physicalVolume_before_field"
  err.flush

theorem geometryRow013_physicalVolume_field :
    geometryRowsJson013.getObjVal? "physical_volume" = .ok (.str geometryRow013_physicalVolumeText) := by rfl

theorem geometryRow013_physicalVolume_numerator_no_slash :
    geometryRow013_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeNumeratorChars = some (1061081127522485195373355150457173508239 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeDenominatorChars = some (102676561920000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_nonzero : (102676561920000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_physicalVolume_parse :
    parseRational geometryRow013_physicalVolumeText = .ok geometryRowsTyped013.physicalVolume :=
  original_rational_fraction_of_chars geometryRow013_physicalVolumeNumeratorChars geometryRow013_physicalVolumeDenominatorChars
    (1061081127522485195373355150457173508239 : Int) (102676561920000000000000000000000000000000000000000000000000 : Int)
    geometryRow013_physicalVolume_numerator_no_slash geometryRow013_physicalVolume_numerator_parse
    geometryRow013_physicalVolume_denominator_parse geometryRow013_physicalVolume_denominator_nonzero

theorem geometryRow013_physicalVolume_read :
    rationalField geometryRowsJson013 "physical_volume" = .ok geometryRowsTyped013.physicalVolume :=
  original_rationalField_of_string geometryRowsJson013 "physical_volume" geometryRow013_physicalVolumeText
    geometryRowsTyped013.physicalVolume geometryRow013_physicalVolume_field geometryRow013_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_physicalVolume_complete"
  err.flush

noncomputable def geometryRow013_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow013_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow013_meanGapText : String := String.ofList (geometryRow013_meanGapNumeratorChars ++ '/' :: geometryRow013_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_meanGap_before_field"
  err.flush

theorem geometryRow013_meanGap_field :
    geometryRowsJson013.getObjVal? "mean_gap" = .ok (.str geometryRow013_meanGapText) := by rfl

theorem geometryRow013_meanGap_numerator_no_slash :
    geometryRow013_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_meanGap_numerator_parse :
    SourceJson.intChars geometryRow013_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_parse :
    SourceJson.intChars geometryRow013_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_meanGap_parse :
    parseRational geometryRow013_meanGapText = .ok geometryRowsTyped013.meanGap :=
  original_rational_fraction_of_chars geometryRow013_meanGapNumeratorChars geometryRow013_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow013_meanGap_numerator_no_slash geometryRow013_meanGap_numerator_parse
    geometryRow013_meanGap_denominator_parse geometryRow013_meanGap_denominator_nonzero

theorem geometryRow013_meanGap_read :
    rationalField geometryRowsJson013 "mean_gap" = .ok geometryRowsTyped013.meanGap :=
  original_rationalField_of_string geometryRowsJson013 "mean_gap" geometryRow013_meanGapText
    geometryRowsTyped013.meanGap geometryRow013_meanGap_field geometryRow013_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_meanGap_complete"
  err.flush

noncomputable def geometryRow013_jensenBoundNumeratorChars : List Char := ['1', '7', '5', '8', '4', '3', '1', '6', '6', '9', '9', '1', '1', '7', '1', '6', '4', '5', '4', '6', '2', '4', '5', '9', '0', '2', '0', '6', '8', '8', '7', '1', '8', '2', '4', '4', '4', '3', '5', '9', '1', '5', '8', '3', '8', '8', '1', '3', '6', '9', '8', '6', '0', '9', '8', '4', '8', '9', '9', '0', '0', '1', '5', '0', '8', '8', '6', '9', '1', '8', '1', '4', '8', '5', '2', '7', '3', '3', '3', '3', '8', '0', '3', '4', '0', '4', '3', '8', '2', '6', '4', '6', '0', '8', '8', '0', '5', '8', '0', '6', '2', '3', '3', '8', '2', '5', '8', '0', '5', '0', '0', '5', '3', '2', '9', '8', '5', '3', '0', '5', '6', '5', '5', '8', '3', '1', '2', '8', '2', '8', '4', '5', '0', '9', '0', '4', '3', '6', '1', '2', '1', '0', '8', '4', '2', '3', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_jensenBoundDenominatorChars : List Char := ['2', '0', '1', '4', '0', '5', '7', '7', '9', '7', '0', '0', '5', '8', '9', '5', '0', '5', '5', '3', '4', '9', '9', '5', '1', '5', '7', '6', '1', '9', '1', '0', '5', '4', '3', '8', '5', '8', '9', '1', '9', '6', '2', '2', '3', '9', '7', '8', '3', '2', '8', '9', '9', '9', '8', '1', '3', '5', '1', '9', '4', '6', '3', '9', '2', '4', '3', '6', '7', '8', '7', '9', '1', '3', '8', '6', '6', '4', '5', '4', '7', '4', '5', '3', '9', '6', '5', '5', '7', '9', '8', '0', '8', '9', '6', '9', '5', '0', '0', '5', '8', '4', '6', '8', '6', '4', '0', '3', '5', '8', '5', '0', '4', '2', '6', '6', '7', '7', '1', '4', '9', '3', '9', '4', '5', '7', '3', '2', '4', '5', '4', '5', '7', '0', '3', '1', '2', '6', '9', '6', '7', '0', '4', '8', '0', '1', '8', '3', '6', '8', '5', '0', '1', '7', '8', '2', '8', '0', '0', '1', '9', '8', '0', '4', '1', '1', '7', '4', '8', '8', '2', '6', '1', '7', '0', '1', '1', '7', '4', '0', '0', '4', '3', '7']
noncomputable def geometryRow013_jensenBoundText : String := String.ofList (geometryRow013_jensenBoundNumeratorChars ++ '/' :: geometryRow013_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_jensenBound_before_field"
  err.flush

theorem geometryRow013_jensenBound_field :
    geometryRowsJson013.getObjVal? "jensen_bound" = .ok (.str geometryRow013_jensenBoundText) := by rfl

theorem geometryRow013_jensenBound_numerator_no_slash :
    geometryRow013_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow013_jensenBoundNumeratorChars = some (175843166991171645462459020688718244435915838813698609848990015088691814852733338034043826460880580623382580500532985305655831282845090436121084231680000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow013_jensenBoundDenominatorChars = some (2014057797005895055349951576191054385891962239783289998135194639243678791386645474539655798089695005846864035850426677149394573245457031269670480183685017828001980411748826170117400437 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_nonzero : (2014057797005895055349951576191054385891962239783289998135194639243678791386645474539655798089695005846864035850426677149394573245457031269670480183685017828001980411748826170117400437 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_jensenBound_parse :
    parseRational geometryRow013_jensenBoundText = .ok geometryRowsTyped013.jensenBound :=
  original_rational_fraction_of_chars geometryRow013_jensenBoundNumeratorChars geometryRow013_jensenBoundDenominatorChars
    (175843166991171645462459020688718244435915838813698609848990015088691814852733338034043826460880580623382580500532985305655831282845090436121084231680000000000000000000000000 : Int) (2014057797005895055349951576191054385891962239783289998135194639243678791386645474539655798089695005846864035850426677149394573245457031269670480183685017828001980411748826170117400437 : Int)
    geometryRow013_jensenBound_numerator_no_slash geometryRow013_jensenBound_numerator_parse
    geometryRow013_jensenBound_denominator_parse geometryRow013_jensenBound_denominator_nonzero

theorem geometryRow013_jensenBound_read :
    rationalField geometryRowsJson013 "jensen_bound" = .ok geometryRowsTyped013.jensenBound :=
  original_rationalField_of_string geometryRowsJson013 "jensen_bound" geometryRow013_jensenBoundText
    geometryRowsTyped013.jensenBound geometryRow013_jensenBound_field geometryRow013_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_factorMaxima_before"
  err.flush

theorem geometryRow013_factorMaxima_read :
    rationalArrayField geometryRowsJson013 "factor_maxima" = .ok geometryRowsTyped013.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_gapWeightedMeans_before"
  err.flush

theorem geometryRow013_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson013 "gap_weighted_means" = .ok geometryRowsTyped013.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow013_floorChars : List Char := ['6', '9', '1', '7', '2', '4', '4', '8', '9', '3', '4', '2', '3', '8', '2', '6', '5', '7', '9']
noncomputable def geometryRow013_floorText : String := String.ofList geometryRow013_floorChars

theorem geometryRow013_floor_text_read :
    geometryRowsJson013.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow013_floorText := by rfl

theorem geometryRow013_floor_chars_parse :
    SourceJson.intChars geometryRow013_floorChars = some (6917244893423826579 : Int) := by decide +kernel

theorem geometryRow013_floor_parse :
    parseInteger geometryRow013_floorText = .ok geometryRowsTyped013.jensenFloorQ96 := by
  simp only [geometryRow013_floorText, parseInteger, String.toList_ofList, geometryRow013_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_013 :
    decodeGeometryRow geometryRowsJson013 = .ok geometryRowsTyped013 :=
  original_geometryRow_of_fields geometryRowsJson013 geometryRowsTyped013 geometryRow013_floorText
    geometryRow013_simplexId_read geometryRow013_vertexIds_read
    geometryRow013_physicalVolume_read geometryRow013_meanGap_read
    geometryRow013_factorMaxima_read geometryRow013_gapWeightedMeans_read
    geometryRow013_jensenBound_read geometryRow013_floor_text_read geometryRow013_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_013_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock006 : List SourceJson := [geometryRowsJson012, geometryRowsJson013]
noncomputable def geometryRowsTypedBlock006 : List (GeometryRow) := [geometryRowsTyped012, geometryRowsTyped013]
noncomputable def geometryRowsTypedThroughBlock006 : List (GeometryRow) := geometryRowsTypedThroughBlock005 ++ geometryRowsTypedBlock006

theorem geometry_Rows_block_006_push_eq (acc : List SourceJson) :
    SimplicesBlock006.blockPush acc = [geometryRowsJson013, geometryRowsJson012] ++ acc := by rfl

theorem geometry_Rows_block_006_reverse (acc : List SourceJson) :
    (SimplicesBlock006.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock006 := by
  rw [geometry_Rows_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_006 :
    geometryRowsJsonBlock006.mapM decodeGeometryRow = .ok geometryRowsTypedBlock006 := by
  simp only [geometryRowsJsonBlock006, geometryRowsTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_012, decode_geometry_Rows_013]
  rfl

theorem decode_geometry_Rows_through_block_006 :
    SimplicesValue.arrayAcc007.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock006 := by
  change (SimplicesBlock006.blockPush SimplicesValue.arrayAcc006).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_006_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_005, decode_geometry_Rows_block_006]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_006_complete"
  err.flush

#print axioms geometryRow012_simplexId_read
#print axioms geometryRow012_vertexIds_read
#print axioms geometryRow012_physicalVolume_field
#print axioms geometryRow012_physicalVolume_numerator_no_slash
#print axioms geometryRow012_physicalVolume_numerator_parse
#print axioms geometryRow012_physicalVolume_denominator_parse
#print axioms geometryRow012_physicalVolume_denominator_nonzero
#print axioms geometryRow012_physicalVolume_parse
#print axioms geometryRow012_physicalVolume_read
#print axioms geometryRow012_meanGap_field
#print axioms geometryRow012_meanGap_numerator_no_slash
#print axioms geometryRow012_meanGap_numerator_parse
#print axioms geometryRow012_meanGap_denominator_parse
#print axioms geometryRow012_meanGap_denominator_nonzero
#print axioms geometryRow012_meanGap_parse
#print axioms geometryRow012_meanGap_read
#print axioms geometryRow012_jensenBound_field
#print axioms geometryRow012_jensenBound_numerator_no_slash
#print axioms geometryRow012_jensenBound_numerator_parse
#print axioms geometryRow012_jensenBound_denominator_parse
#print axioms geometryRow012_jensenBound_denominator_nonzero
#print axioms geometryRow012_jensenBound_parse
#print axioms geometryRow012_jensenBound_read
#print axioms geometryRow012_factorMaxima_read
#print axioms geometryRow012_gapWeightedMeans_read
#print axioms geometryRow012_floor_text_read
#print axioms geometryRow012_floor_chars_parse
#print axioms geometryRow012_floor_parse
#print axioms decode_geometry_Rows_012
#print axioms geometryRow013_simplexId_read
#print axioms geometryRow013_vertexIds_read
#print axioms geometryRow013_physicalVolume_field
#print axioms geometryRow013_physicalVolume_numerator_no_slash
#print axioms geometryRow013_physicalVolume_numerator_parse
#print axioms geometryRow013_physicalVolume_denominator_parse
#print axioms geometryRow013_physicalVolume_denominator_nonzero
#print axioms geometryRow013_physicalVolume_parse
#print axioms geometryRow013_physicalVolume_read
#print axioms geometryRow013_meanGap_field
#print axioms geometryRow013_meanGap_numerator_no_slash
#print axioms geometryRow013_meanGap_numerator_parse
#print axioms geometryRow013_meanGap_denominator_parse
#print axioms geometryRow013_meanGap_denominator_nonzero
#print axioms geometryRow013_meanGap_parse
#print axioms geometryRow013_meanGap_read
#print axioms geometryRow013_jensenBound_field
#print axioms geometryRow013_jensenBound_numerator_no_slash
#print axioms geometryRow013_jensenBound_numerator_parse
#print axioms geometryRow013_jensenBound_denominator_parse
#print axioms geometryRow013_jensenBound_denominator_nonzero
#print axioms geometryRow013_jensenBound_parse
#print axioms geometryRow013_jensenBound_read
#print axioms geometryRow013_factorMaxima_read
#print axioms geometryRow013_gapWeightedMeans_read
#print axioms geometryRow013_floor_text_read
#print axioms geometryRow013_floor_chars_parse
#print axioms geometryRow013_floor_parse
#print axioms decode_geometry_Rows_013
#print axioms geometry_Rows_block_006_push_eq
#print axioms geometry_Rows_block_006_reverse
#print axioms decode_geometry_Rows_block_006
#print axioms decode_geometry_Rows_through_block_006

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
