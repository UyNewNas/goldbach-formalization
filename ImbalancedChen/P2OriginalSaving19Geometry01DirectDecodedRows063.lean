import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows062

/-! Original simplices typed block 63, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson124 : SourceJson :=
  (SimplicesBlock063.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped124 : GeometryRow :=
  { simplexId := 124,
    vertexIds := #[39, 38, 34, 24, 11, 10, 8, 3, 1],
    physicalVolume := ((24677973888548885878242582278182217 : ℚ) / (7144243200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((435116015267 : ℚ) / (5038800000000 : ℚ)), ((440209441787 : ℚ) / (5038800000000 : ℚ)), ((56438146811 : ℚ) / (387600000000 : ℚ)), ((287356266193 : ℚ) / (2519400000000 : ℚ)), ((5969300879 : ℚ) / (98800000000 : ℚ)), ((236917468477 : ℚ) / (5038800000000 : ℚ)), ((66088295879 : ℚ) / (1679600000000 : ℚ)), ((183204581857 : ℚ) / (5038800000000 : ℚ)), ((169180642717 : ℚ) / (5038800000000 : ℚ)), ((56393435599 : ℚ) / (1679600000000 : ℚ))],
    jensenBound := ((623614449087837001956010699288750342992753835776899215112282912997631872000000000000000000000000 : ℚ) / (46134499694387001580864919334682803436691785737177165564579449391408906285834897718597061940599610046036929199 : ℚ)),
    jensenFloorQ96 := (1070951830969694 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_simplexId_before"
  err.flush

theorem geometryRow124_simplexId_read :
    geometryRowsJson124.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped124.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_vertexIds_before"
  err.flush

theorem geometryRow124_vertexIds_read :
    geometryRowsJson124.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped124.vertexIds := by decide +kernel

noncomputable def geometryRow124_physicalVolumeNumeratorChars : List Char := ['2', '4', '6', '7', '7', '9', '7', '3', '8', '8', '8', '5', '4', '8', '8', '8', '5', '8', '7', '8', '2', '4', '2', '5', '8', '2', '2', '7', '8', '1', '8', '2', '2', '1', '7']
noncomputable def geometryRow124_physicalVolumeDenominatorChars : List Char := ['7', '1', '4', '4', '2', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow124_physicalVolumeText : String := String.ofList (geometryRow124_physicalVolumeNumeratorChars ++ '/' :: geometryRow124_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_physicalVolume_before_field"
  err.flush

theorem geometryRow124_physicalVolume_field :
    geometryRowsJson124.getObjVal? "physical_volume" = .ok (.str geometryRow124_physicalVolumeText) := by rfl

theorem geometryRow124_physicalVolume_numerator_no_slash :
    geometryRow124_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow124_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow124_physicalVolumeNumeratorChars = some (24677973888548885878242582278182217 : Int) := by decide +kernel

theorem geometryRow124_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow124_physicalVolumeDenominatorChars = some (7144243200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow124_physicalVolume_denominator_nonzero : (7144243200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow124_physicalVolume_parse :
    parseRational geometryRow124_physicalVolumeText = .ok geometryRowsTyped124.physicalVolume :=
  original_rational_fraction_of_chars geometryRow124_physicalVolumeNumeratorChars geometryRow124_physicalVolumeDenominatorChars
    (24677973888548885878242582278182217 : Int) (7144243200000000000000000000000000000000000000000000000000 : Int)
    geometryRow124_physicalVolume_numerator_no_slash geometryRow124_physicalVolume_numerator_parse
    geometryRow124_physicalVolume_denominator_parse geometryRow124_physicalVolume_denominator_nonzero

theorem geometryRow124_physicalVolume_read :
    rationalField geometryRowsJson124 "physical_volume" = .ok geometryRowsTyped124.physicalVolume :=
  original_rationalField_of_string geometryRowsJson124 "physical_volume" geometryRow124_physicalVolumeText
    geometryRowsTyped124.physicalVolume geometryRow124_physicalVolume_field geometryRow124_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_physicalVolume_complete"
  err.flush

noncomputable def geometryRow124_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow124_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow124_meanGapText : String := String.ofList (geometryRow124_meanGapNumeratorChars ++ '/' :: geometryRow124_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_meanGap_before_field"
  err.flush

theorem geometryRow124_meanGap_field :
    geometryRowsJson124.getObjVal? "mean_gap" = .ok (.str geometryRow124_meanGapText) := by rfl

theorem geometryRow124_meanGap_numerator_no_slash :
    geometryRow124_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow124_meanGap_numerator_parse :
    SourceJson.intChars geometryRow124_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow124_meanGap_denominator_parse :
    SourceJson.intChars geometryRow124_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow124_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow124_meanGap_parse :
    parseRational geometryRow124_meanGapText = .ok geometryRowsTyped124.meanGap :=
  original_rational_fraction_of_chars geometryRow124_meanGapNumeratorChars geometryRow124_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow124_meanGap_numerator_no_slash geometryRow124_meanGap_numerator_parse
    geometryRow124_meanGap_denominator_parse geometryRow124_meanGap_denominator_nonzero

theorem geometryRow124_meanGap_read :
    rationalField geometryRowsJson124 "mean_gap" = .ok geometryRowsTyped124.meanGap :=
  original_rationalField_of_string geometryRowsJson124 "mean_gap" geometryRow124_meanGapText
    geometryRowsTyped124.meanGap geometryRow124_meanGap_field geometryRow124_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_meanGap_complete"
  err.flush

noncomputable def geometryRow124_jensenBoundNumeratorChars : List Char := ['6', '2', '3', '6', '1', '4', '4', '4', '9', '0', '8', '7', '8', '3', '7', '0', '0', '1', '9', '5', '6', '0', '1', '0', '6', '9', '9', '2', '8', '8', '7', '5', '0', '3', '4', '2', '9', '9', '2', '7', '5', '3', '8', '3', '5', '7', '7', '6', '8', '9', '9', '2', '1', '5', '1', '1', '2', '2', '8', '2', '9', '1', '2', '9', '9', '7', '6', '3', '1', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow124_jensenBoundDenominatorChars : List Char := ['4', '6', '1', '3', '4', '4', '9', '9', '6', '9', '4', '3', '8', '7', '0', '0', '1', '5', '8', '0', '8', '6', '4', '9', '1', '9', '3', '3', '4', '6', '8', '2', '8', '0', '3', '4', '3', '6', '6', '9', '1', '7', '8', '5', '7', '3', '7', '1', '7', '7', '1', '6', '5', '5', '6', '4', '5', '7', '9', '4', '4', '9', '3', '9', '1', '4', '0', '8', '9', '0', '6', '2', '8', '5', '8', '3', '4', '8', '9', '7', '7', '1', '8', '5', '9', '7', '0', '6', '1', '9', '4', '0', '5', '9', '9', '6', '1', '0', '0', '4', '6', '0', '3', '6', '9', '2', '9', '1', '9', '9']
noncomputable def geometryRow124_jensenBoundText : String := String.ofList (geometryRow124_jensenBoundNumeratorChars ++ '/' :: geometryRow124_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_jensenBound_before_field"
  err.flush

theorem geometryRow124_jensenBound_field :
    geometryRowsJson124.getObjVal? "jensen_bound" = .ok (.str geometryRow124_jensenBoundText) := by rfl

theorem geometryRow124_jensenBound_numerator_no_slash :
    geometryRow124_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow124_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow124_jensenBoundNumeratorChars = some (623614449087837001956010699288750342992753835776899215112282912997631872000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow124_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow124_jensenBoundDenominatorChars = some (46134499694387001580864919334682803436691785737177165564579449391408906285834897718597061940599610046036929199 : Int) := by decide +kernel

theorem geometryRow124_jensenBound_denominator_nonzero : (46134499694387001580864919334682803436691785737177165564579449391408906285834897718597061940599610046036929199 : Int) ≠ 0 := by decide +kernel

theorem geometryRow124_jensenBound_parse :
    parseRational geometryRow124_jensenBoundText = .ok geometryRowsTyped124.jensenBound :=
  original_rational_fraction_of_chars geometryRow124_jensenBoundNumeratorChars geometryRow124_jensenBoundDenominatorChars
    (623614449087837001956010699288750342992753835776899215112282912997631872000000000000000000000000 : Int) (46134499694387001580864919334682803436691785737177165564579449391408906285834897718597061940599610046036929199 : Int)
    geometryRow124_jensenBound_numerator_no_slash geometryRow124_jensenBound_numerator_parse
    geometryRow124_jensenBound_denominator_parse geometryRow124_jensenBound_denominator_nonzero

theorem geometryRow124_jensenBound_read :
    rationalField geometryRowsJson124 "jensen_bound" = .ok geometryRowsTyped124.jensenBound :=
  original_rationalField_of_string geometryRowsJson124 "jensen_bound" geometryRow124_jensenBoundText
    geometryRowsTyped124.jensenBound geometryRow124_jensenBound_field geometryRow124_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_factorMaxima_before"
  err.flush

theorem geometryRow124_factorMaxima_read :
    rationalArrayField geometryRowsJson124 "factor_maxima" = .ok geometryRowsTyped124.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_gapWeightedMeans_before"
  err.flush

theorem geometryRow124_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson124 "gap_weighted_means" = .ok geometryRowsTyped124.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow124_floorChars : List Char := ['1', '0', '7', '0', '9', '5', '1', '8', '3', '0', '9', '6', '9', '6', '9', '4']
noncomputable def geometryRow124_floorText : String := String.ofList geometryRow124_floorChars

theorem geometryRow124_floor_text_read :
    geometryRowsJson124.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow124_floorText := by rfl

theorem geometryRow124_floor_chars_parse :
    SourceJson.intChars geometryRow124_floorChars = some (1070951830969694 : Int) := by decide +kernel

theorem geometryRow124_floor_parse :
    parseInteger geometryRow124_floorText = .ok geometryRowsTyped124.jensenFloorQ96 := by
  simp only [geometryRow124_floorText, parseInteger, String.toList_ofList, geometryRow124_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_124 :
    decodeGeometryRow geometryRowsJson124 = .ok geometryRowsTyped124 :=
  original_geometryRow_of_fields geometryRowsJson124 geometryRowsTyped124 geometryRow124_floorText
    geometryRow124_simplexId_read geometryRow124_vertexIds_read
    geometryRow124_physicalVolume_read geometryRow124_meanGap_read
    geometryRow124_factorMaxima_read geometryRow124_gapWeightedMeans_read
    geometryRow124_jensenBound_read geometryRow124_floor_text_read geometryRow124_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_124_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson125 : SourceJson :=
  (SimplicesBlock063.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped125 : GeometryRow :=
  { simplexId := 125,
    vertexIds := #[39, 38, 34, 24, 23, 10, 8, 3, 1],
    physicalVolume := ((1835763204125521625132770305770733677 : ℚ) / (2443331174400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((8812854629 : ℚ) / (104975000000 : ℚ)), ((17837935363 : ℚ) / (209950000000 : ℚ)), ((9437380861 : ℚ) / (64600000000 : ℚ)), ((47489411263 : ℚ) / (419900000000 : ℚ)), ((8882780771 : ℚ) / (148200000000 : ℚ)), ((39082944977 : ℚ) / (839800000000 : ℚ)), ((1279604021 : ℚ) / (33150000000 : ℚ)), ((47952313883 : ℚ) / (1259700000000 : ℚ)), ((88220019281 : ℚ) / (2519400000000 : ℚ)), ((29406617107 : ℚ) / (839800000000 : ℚ))],
    jensenBound := ((291126011789478170416780457225637361934174718243049982403809995466064453125000000000000 : ℚ) / (102162486357898586089817419828476147876178636556440907447265654907467233056192007483933150967616557261 : ℚ)),
    jensenFloorQ96 := (225771511603418 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_simplexId_before"
  err.flush

theorem geometryRow125_simplexId_read :
    geometryRowsJson125.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped125.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_vertexIds_before"
  err.flush

theorem geometryRow125_vertexIds_read :
    geometryRowsJson125.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped125.vertexIds := by decide +kernel

noncomputable def geometryRow125_physicalVolumeNumeratorChars : List Char := ['1', '8', '3', '5', '7', '6', '3', '2', '0', '4', '1', '2', '5', '5', '2', '1', '6', '2', '5', '1', '3', '2', '7', '7', '0', '3', '0', '5', '7', '7', '0', '7', '3', '3', '6', '7', '7']
noncomputable def geometryRow125_physicalVolumeDenominatorChars : List Char := ['2', '4', '4', '3', '3', '3', '1', '1', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow125_physicalVolumeText : String := String.ofList (geometryRow125_physicalVolumeNumeratorChars ++ '/' :: geometryRow125_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_physicalVolume_before_field"
  err.flush

theorem geometryRow125_physicalVolume_field :
    geometryRowsJson125.getObjVal? "physical_volume" = .ok (.str geometryRow125_physicalVolumeText) := by rfl

theorem geometryRow125_physicalVolume_numerator_no_slash :
    geometryRow125_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow125_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow125_physicalVolumeNumeratorChars = some (1835763204125521625132770305770733677 : Int) := by decide +kernel

theorem geometryRow125_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow125_physicalVolumeDenominatorChars = some (2443331174400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow125_physicalVolume_denominator_nonzero : (2443331174400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow125_physicalVolume_parse :
    parseRational geometryRow125_physicalVolumeText = .ok geometryRowsTyped125.physicalVolume :=
  original_rational_fraction_of_chars geometryRow125_physicalVolumeNumeratorChars geometryRow125_physicalVolumeDenominatorChars
    (1835763204125521625132770305770733677 : Int) (2443331174400000000000000000000000000000000000000000000000000 : Int)
    geometryRow125_physicalVolume_numerator_no_slash geometryRow125_physicalVolume_numerator_parse
    geometryRow125_physicalVolume_denominator_parse geometryRow125_physicalVolume_denominator_nonzero

theorem geometryRow125_physicalVolume_read :
    rationalField geometryRowsJson125 "physical_volume" = .ok geometryRowsTyped125.physicalVolume :=
  original_rationalField_of_string geometryRowsJson125 "physical_volume" geometryRow125_physicalVolumeText
    geometryRowsTyped125.physicalVolume geometryRow125_physicalVolume_field geometryRow125_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_physicalVolume_complete"
  err.flush

noncomputable def geometryRow125_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow125_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow125_meanGapText : String := String.ofList (geometryRow125_meanGapNumeratorChars ++ '/' :: geometryRow125_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_meanGap_before_field"
  err.flush

theorem geometryRow125_meanGap_field :
    geometryRowsJson125.getObjVal? "mean_gap" = .ok (.str geometryRow125_meanGapText) := by rfl

theorem geometryRow125_meanGap_numerator_no_slash :
    geometryRow125_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow125_meanGap_numerator_parse :
    SourceJson.intChars geometryRow125_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow125_meanGap_denominator_parse :
    SourceJson.intChars geometryRow125_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow125_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow125_meanGap_parse :
    parseRational geometryRow125_meanGapText = .ok geometryRowsTyped125.meanGap :=
  original_rational_fraction_of_chars geometryRow125_meanGapNumeratorChars geometryRow125_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow125_meanGap_numerator_no_slash geometryRow125_meanGap_numerator_parse
    geometryRow125_meanGap_denominator_parse geometryRow125_meanGap_denominator_nonzero

theorem geometryRow125_meanGap_read :
    rationalField geometryRowsJson125 "mean_gap" = .ok geometryRowsTyped125.meanGap :=
  original_rationalField_of_string geometryRowsJson125 "mean_gap" geometryRow125_meanGapText
    geometryRowsTyped125.meanGap geometryRow125_meanGap_field geometryRow125_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_meanGap_complete"
  err.flush

noncomputable def geometryRow125_jensenBoundNumeratorChars : List Char := ['2', '9', '1', '1', '2', '6', '0', '1', '1', '7', '8', '9', '4', '7', '8', '1', '7', '0', '4', '1', '6', '7', '8', '0', '4', '5', '7', '2', '2', '5', '6', '3', '7', '3', '6', '1', '9', '3', '4', '1', '7', '4', '7', '1', '8', '2', '4', '3', '0', '4', '9', '9', '8', '2', '4', '0', '3', '8', '0', '9', '9', '9', '5', '4', '6', '6', '0', '6', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow125_jensenBoundDenominatorChars : List Char := ['1', '0', '2', '1', '6', '2', '4', '8', '6', '3', '5', '7', '8', '9', '8', '5', '8', '6', '0', '8', '9', '8', '1', '7', '4', '1', '9', '8', '2', '8', '4', '7', '6', '1', '4', '7', '8', '7', '6', '1', '7', '8', '6', '3', '6', '5', '5', '6', '4', '4', '0', '9', '0', '7', '4', '4', '7', '2', '6', '5', '6', '5', '4', '9', '0', '7', '4', '6', '7', '2', '3', '3', '0', '5', '6', '1', '9', '2', '0', '0', '7', '4', '8', '3', '9', '3', '3', '1', '5', '0', '9', '6', '7', '6', '1', '6', '5', '5', '7', '2', '6', '1']
noncomputable def geometryRow125_jensenBoundText : String := String.ofList (geometryRow125_jensenBoundNumeratorChars ++ '/' :: geometryRow125_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_jensenBound_before_field"
  err.flush

theorem geometryRow125_jensenBound_field :
    geometryRowsJson125.getObjVal? "jensen_bound" = .ok (.str geometryRow125_jensenBoundText) := by rfl

theorem geometryRow125_jensenBound_numerator_no_slash :
    geometryRow125_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow125_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow125_jensenBoundNumeratorChars = some (291126011789478170416780457225637361934174718243049982403809995466064453125000000000000 : Int) := by decide +kernel

theorem geometryRow125_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow125_jensenBoundDenominatorChars = some (102162486357898586089817419828476147876178636556440907447265654907467233056192007483933150967616557261 : Int) := by decide +kernel

theorem geometryRow125_jensenBound_denominator_nonzero : (102162486357898586089817419828476147876178636556440907447265654907467233056192007483933150967616557261 : Int) ≠ 0 := by decide +kernel

theorem geometryRow125_jensenBound_parse :
    parseRational geometryRow125_jensenBoundText = .ok geometryRowsTyped125.jensenBound :=
  original_rational_fraction_of_chars geometryRow125_jensenBoundNumeratorChars geometryRow125_jensenBoundDenominatorChars
    (291126011789478170416780457225637361934174718243049982403809995466064453125000000000000 : Int) (102162486357898586089817419828476147876178636556440907447265654907467233056192007483933150967616557261 : Int)
    geometryRow125_jensenBound_numerator_no_slash geometryRow125_jensenBound_numerator_parse
    geometryRow125_jensenBound_denominator_parse geometryRow125_jensenBound_denominator_nonzero

theorem geometryRow125_jensenBound_read :
    rationalField geometryRowsJson125 "jensen_bound" = .ok geometryRowsTyped125.jensenBound :=
  original_rationalField_of_string geometryRowsJson125 "jensen_bound" geometryRow125_jensenBoundText
    geometryRowsTyped125.jensenBound geometryRow125_jensenBound_field geometryRow125_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_factorMaxima_before"
  err.flush

theorem geometryRow125_factorMaxima_read :
    rationalArrayField geometryRowsJson125 "factor_maxima" = .ok geometryRowsTyped125.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_gapWeightedMeans_before"
  err.flush

theorem geometryRow125_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson125 "gap_weighted_means" = .ok geometryRowsTyped125.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow125_floorChars : List Char := ['2', '2', '5', '7', '7', '1', '5', '1', '1', '6', '0', '3', '4', '1', '8']
noncomputable def geometryRow125_floorText : String := String.ofList geometryRow125_floorChars

theorem geometryRow125_floor_text_read :
    geometryRowsJson125.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow125_floorText := by rfl

theorem geometryRow125_floor_chars_parse :
    SourceJson.intChars geometryRow125_floorChars = some (225771511603418 : Int) := by decide +kernel

theorem geometryRow125_floor_parse :
    parseInteger geometryRow125_floorText = .ok geometryRowsTyped125.jensenFloorQ96 := by
  simp only [geometryRow125_floorText, parseInteger, String.toList_ofList, geometryRow125_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_125 :
    decodeGeometryRow geometryRowsJson125 = .ok geometryRowsTyped125 :=
  original_geometryRow_of_fields geometryRowsJson125 geometryRowsTyped125 geometryRow125_floorText
    geometryRow125_simplexId_read geometryRow125_vertexIds_read
    geometryRow125_physicalVolume_read geometryRow125_meanGap_read
    geometryRow125_factorMaxima_read geometryRow125_gapWeightedMeans_read
    geometryRow125_jensenBound_read geometryRow125_floor_text_read geometryRow125_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_125_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock063 : List SourceJson := [geometryRowsJson124, geometryRowsJson125]
noncomputable def geometryRowsTypedBlock063 : List (GeometryRow) := [geometryRowsTyped124, geometryRowsTyped125]
noncomputable def geometryRowsTypedThroughBlock063 : List (GeometryRow) := geometryRowsTypedThroughBlock062 ++ geometryRowsTypedBlock063

theorem geometry_Rows_block_063_push_eq (acc : List SourceJson) :
    SimplicesBlock063.blockPush acc = [geometryRowsJson125, geometryRowsJson124] ++ acc := by rfl

theorem geometry_Rows_block_063_reverse (acc : List SourceJson) :
    (SimplicesBlock063.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock063 := by
  rw [geometry_Rows_block_063_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_063 :
    geometryRowsJsonBlock063.mapM decodeGeometryRow = .ok geometryRowsTypedBlock063 := by
  simp only [geometryRowsJsonBlock063, geometryRowsTypedBlock063, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_124, decode_geometry_Rows_125]
  rfl

theorem decode_geometry_Rows_through_block_063 :
    SimplicesValue.arrayAcc064.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock063 := by
  change (SimplicesBlock063.blockPush SimplicesValue.arrayAcc063).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_063_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_062, decode_geometry_Rows_block_063]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_063_complete"
  err.flush

#print axioms geometryRow124_simplexId_read
#print axioms geometryRow124_vertexIds_read
#print axioms geometryRow124_physicalVolume_field
#print axioms geometryRow124_physicalVolume_numerator_no_slash
#print axioms geometryRow124_physicalVolume_numerator_parse
#print axioms geometryRow124_physicalVolume_denominator_parse
#print axioms geometryRow124_physicalVolume_denominator_nonzero
#print axioms geometryRow124_physicalVolume_parse
#print axioms geometryRow124_physicalVolume_read
#print axioms geometryRow124_meanGap_field
#print axioms geometryRow124_meanGap_numerator_no_slash
#print axioms geometryRow124_meanGap_numerator_parse
#print axioms geometryRow124_meanGap_denominator_parse
#print axioms geometryRow124_meanGap_denominator_nonzero
#print axioms geometryRow124_meanGap_parse
#print axioms geometryRow124_meanGap_read
#print axioms geometryRow124_jensenBound_field
#print axioms geometryRow124_jensenBound_numerator_no_slash
#print axioms geometryRow124_jensenBound_numerator_parse
#print axioms geometryRow124_jensenBound_denominator_parse
#print axioms geometryRow124_jensenBound_denominator_nonzero
#print axioms geometryRow124_jensenBound_parse
#print axioms geometryRow124_jensenBound_read
#print axioms geometryRow124_factorMaxima_read
#print axioms geometryRow124_gapWeightedMeans_read
#print axioms geometryRow124_floor_text_read
#print axioms geometryRow124_floor_chars_parse
#print axioms geometryRow124_floor_parse
#print axioms decode_geometry_Rows_124
#print axioms geometryRow125_simplexId_read
#print axioms geometryRow125_vertexIds_read
#print axioms geometryRow125_physicalVolume_field
#print axioms geometryRow125_physicalVolume_numerator_no_slash
#print axioms geometryRow125_physicalVolume_numerator_parse
#print axioms geometryRow125_physicalVolume_denominator_parse
#print axioms geometryRow125_physicalVolume_denominator_nonzero
#print axioms geometryRow125_physicalVolume_parse
#print axioms geometryRow125_physicalVolume_read
#print axioms geometryRow125_meanGap_field
#print axioms geometryRow125_meanGap_numerator_no_slash
#print axioms geometryRow125_meanGap_numerator_parse
#print axioms geometryRow125_meanGap_denominator_parse
#print axioms geometryRow125_meanGap_denominator_nonzero
#print axioms geometryRow125_meanGap_parse
#print axioms geometryRow125_meanGap_read
#print axioms geometryRow125_jensenBound_field
#print axioms geometryRow125_jensenBound_numerator_no_slash
#print axioms geometryRow125_jensenBound_numerator_parse
#print axioms geometryRow125_jensenBound_denominator_parse
#print axioms geometryRow125_jensenBound_denominator_nonzero
#print axioms geometryRow125_jensenBound_parse
#print axioms geometryRow125_jensenBound_read
#print axioms geometryRow125_factorMaxima_read
#print axioms geometryRow125_gapWeightedMeans_read
#print axioms geometryRow125_floor_text_read
#print axioms geometryRow125_floor_chars_parse
#print axioms geometryRow125_floor_parse
#print axioms decode_geometry_Rows_125
#print axioms geometry_Rows_block_063_push_eq
#print axioms geometry_Rows_block_063_reverse
#print axioms decode_geometry_Rows_block_063
#print axioms decode_geometry_Rows_through_block_063

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
