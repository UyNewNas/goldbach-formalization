import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows042

/-! Original simplices typed block 43, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson085 : SourceJson :=
  (SimplicesBlock043.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped085 : GeometryRow :=
  { simplexId := 85,
    vertexIds := #[39, 37, 24, 23, 10, 7, 6, 2, 0],
    physicalVolume := ((3445259186255796362261593818713815853703202321 : ℚ) / (201253336995594240000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((13970760029 : ℚ) / (159600000000 : ℚ)), ((98970735443 : ℚ) / (1117200000000 : ℚ)), ((481735379989 : ℚ) / (3351600000000 : ℚ)), ((62466896501 : ℚ) / (558600000000 : ℚ)), ((185960990609 : ℚ) / (3351600000000 : ℚ)), ((163346428367 : ℚ) / (3351600000000 : ℚ)), ((1381425529 : ℚ) / (35280000000 : ℚ)), ((25889155927 : ℚ) / (670320000000 : ℚ)), ((24887273017 : ℚ) / (670320000000 : ℚ)), ((113993195623 : ℚ) / (3351600000000 : ℚ))],
    jensenBound := ((215521879298935470035925842258265425956582754449188076821995605739306724480000000000000000000000 : ℚ) / (3465905225225450145451926012739439660641375599586127016681609782710352151904419914504523847379753653763981 : ℚ)),
    jensenFloorQ96 := (4926678996932180061 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_simplexId_before"
  err.flush

theorem geometryRow085_simplexId_read :
    geometryRowsJson085.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped085.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_vertexIds_before"
  err.flush

theorem geometryRow085_vertexIds_read :
    geometryRowsJson085.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped085.vertexIds := by decide +kernel

noncomputable def geometryRow085_physicalVolumeNumeratorChars : List Char := ['3', '4', '4', '5', '2', '5', '9', '1', '8', '6', '2', '5', '5', '7', '9', '6', '3', '6', '2', '2', '6', '1', '5', '9', '3', '8', '1', '8', '7', '1', '3', '8', '1', '5', '8', '5', '3', '7', '0', '3', '2', '0', '2', '3', '2', '1']
noncomputable def geometryRow085_physicalVolumeDenominatorChars : List Char := ['2', '0', '1', '2', '5', '3', '3', '3', '6', '9', '9', '5', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow085_physicalVolumeText : String := String.ofList (geometryRow085_physicalVolumeNumeratorChars ++ '/' :: geometryRow085_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_physicalVolume_before_field"
  err.flush

theorem geometryRow085_physicalVolume_field :
    geometryRowsJson085.getObjVal? "physical_volume" = .ok (.str geometryRow085_physicalVolumeText) := by rfl

theorem geometryRow085_physicalVolume_numerator_no_slash :
    geometryRow085_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow085_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow085_physicalVolumeNumeratorChars = some (3445259186255796362261593818713815853703202321 : Int) := by decide +kernel

theorem geometryRow085_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow085_physicalVolumeDenominatorChars = some (201253336995594240000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow085_physicalVolume_denominator_nonzero : (201253336995594240000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow085_physicalVolume_parse :
    parseRational geometryRow085_physicalVolumeText = .ok geometryRowsTyped085.physicalVolume :=
  original_rational_fraction_of_chars geometryRow085_physicalVolumeNumeratorChars geometryRow085_physicalVolumeDenominatorChars
    (3445259186255796362261593818713815853703202321 : Int) (201253336995594240000000000000000000000000000000000000000000000000 : Int)
    geometryRow085_physicalVolume_numerator_no_slash geometryRow085_physicalVolume_numerator_parse
    geometryRow085_physicalVolume_denominator_parse geometryRow085_physicalVolume_denominator_nonzero

theorem geometryRow085_physicalVolume_read :
    rationalField geometryRowsJson085 "physical_volume" = .ok geometryRowsTyped085.physicalVolume :=
  original_rationalField_of_string geometryRowsJson085 "physical_volume" geometryRow085_physicalVolumeText
    geometryRowsTyped085.physicalVolume geometryRow085_physicalVolume_field geometryRow085_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_physicalVolume_complete"
  err.flush

noncomputable def geometryRow085_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow085_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow085_meanGapText : String := String.ofList (geometryRow085_meanGapNumeratorChars ++ '/' :: geometryRow085_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_meanGap_before_field"
  err.flush

theorem geometryRow085_meanGap_field :
    geometryRowsJson085.getObjVal? "mean_gap" = .ok (.str geometryRow085_meanGapText) := by rfl

theorem geometryRow085_meanGap_numerator_no_slash :
    geometryRow085_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow085_meanGap_numerator_parse :
    SourceJson.intChars geometryRow085_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow085_meanGap_denominator_parse :
    SourceJson.intChars geometryRow085_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow085_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow085_meanGap_parse :
    parseRational geometryRow085_meanGapText = .ok geometryRowsTyped085.meanGap :=
  original_rational_fraction_of_chars geometryRow085_meanGapNumeratorChars geometryRow085_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow085_meanGap_numerator_no_slash geometryRow085_meanGap_numerator_parse
    geometryRow085_meanGap_denominator_parse geometryRow085_meanGap_denominator_nonzero

theorem geometryRow085_meanGap_read :
    rationalField geometryRowsJson085 "mean_gap" = .ok geometryRowsTyped085.meanGap :=
  original_rationalField_of_string geometryRowsJson085 "mean_gap" geometryRow085_meanGapText
    geometryRowsTyped085.meanGap geometryRow085_meanGap_field geometryRow085_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_meanGap_complete"
  err.flush

noncomputable def geometryRow085_jensenBoundNumeratorChars : List Char := ['2', '1', '5', '5', '2', '1', '8', '7', '9', '2', '9', '8', '9', '3', '5', '4', '7', '0', '0', '3', '5', '9', '2', '5', '8', '4', '2', '2', '5', '8', '2', '6', '5', '4', '2', '5', '9', '5', '6', '5', '8', '2', '7', '5', '4', '4', '4', '9', '1', '8', '8', '0', '7', '6', '8', '2', '1', '9', '9', '5', '6', '0', '5', '7', '3', '9', '3', '0', '6', '7', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow085_jensenBoundDenominatorChars : List Char := ['3', '4', '6', '5', '9', '0', '5', '2', '2', '5', '2', '2', '5', '4', '5', '0', '1', '4', '5', '4', '5', '1', '9', '2', '6', '0', '1', '2', '7', '3', '9', '4', '3', '9', '6', '6', '0', '6', '4', '1', '3', '7', '5', '5', '9', '9', '5', '8', '6', '1', '2', '7', '0', '1', '6', '6', '8', '1', '6', '0', '9', '7', '8', '2', '7', '1', '0', '3', '5', '2', '1', '5', '1', '9', '0', '4', '4', '1', '9', '9', '1', '4', '5', '0', '4', '5', '2', '3', '8', '4', '7', '3', '7', '9', '7', '5', '3', '6', '5', '3', '7', '6', '3', '9', '8', '1']
noncomputable def geometryRow085_jensenBoundText : String := String.ofList (geometryRow085_jensenBoundNumeratorChars ++ '/' :: geometryRow085_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_jensenBound_before_field"
  err.flush

theorem geometryRow085_jensenBound_field :
    geometryRowsJson085.getObjVal? "jensen_bound" = .ok (.str geometryRow085_jensenBoundText) := by rfl

theorem geometryRow085_jensenBound_numerator_no_slash :
    geometryRow085_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow085_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow085_jensenBoundNumeratorChars = some (215521879298935470035925842258265425956582754449188076821995605739306724480000000000000000000000 : Int) := by decide +kernel

theorem geometryRow085_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow085_jensenBoundDenominatorChars = some (3465905225225450145451926012739439660641375599586127016681609782710352151904419914504523847379753653763981 : Int) := by decide +kernel

theorem geometryRow085_jensenBound_denominator_nonzero : (3465905225225450145451926012739439660641375599586127016681609782710352151904419914504523847379753653763981 : Int) ≠ 0 := by decide +kernel

theorem geometryRow085_jensenBound_parse :
    parseRational geometryRow085_jensenBoundText = .ok geometryRowsTyped085.jensenBound :=
  original_rational_fraction_of_chars geometryRow085_jensenBoundNumeratorChars geometryRow085_jensenBoundDenominatorChars
    (215521879298935470035925842258265425956582754449188076821995605739306724480000000000000000000000 : Int) (3465905225225450145451926012739439660641375599586127016681609782710352151904419914504523847379753653763981 : Int)
    geometryRow085_jensenBound_numerator_no_slash geometryRow085_jensenBound_numerator_parse
    geometryRow085_jensenBound_denominator_parse geometryRow085_jensenBound_denominator_nonzero

theorem geometryRow085_jensenBound_read :
    rationalField geometryRowsJson085 "jensen_bound" = .ok geometryRowsTyped085.jensenBound :=
  original_rationalField_of_string geometryRowsJson085 "jensen_bound" geometryRow085_jensenBoundText
    geometryRowsTyped085.jensenBound geometryRow085_jensenBound_field geometryRow085_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_factorMaxima_before"
  err.flush

theorem geometryRow085_factorMaxima_read :
    rationalArrayField geometryRowsJson085 "factor_maxima" = .ok geometryRowsTyped085.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_gapWeightedMeans_before"
  err.flush

theorem geometryRow085_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson085 "gap_weighted_means" = .ok geometryRowsTyped085.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow085_floorChars : List Char := ['4', '9', '2', '6', '6', '7', '8', '9', '9', '6', '9', '3', '2', '1', '8', '0', '0', '6', '1']
noncomputable def geometryRow085_floorText : String := String.ofList geometryRow085_floorChars

theorem geometryRow085_floor_text_read :
    geometryRowsJson085.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow085_floorText := by rfl

theorem geometryRow085_floor_chars_parse :
    SourceJson.intChars geometryRow085_floorChars = some (4926678996932180061 : Int) := by decide +kernel

theorem geometryRow085_floor_parse :
    parseInteger geometryRow085_floorText = .ok geometryRowsTyped085.jensenFloorQ96 := by
  simp only [geometryRow085_floorText, parseInteger, String.toList_ofList, geometryRow085_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_085 :
    decodeGeometryRow geometryRowsJson085 = .ok geometryRowsTyped085 :=
  original_geometryRow_of_fields geometryRowsJson085 geometryRowsTyped085 geometryRow085_floorText
    geometryRow085_simplexId_read geometryRow085_vertexIds_read
    geometryRow085_physicalVolume_read geometryRow085_meanGap_read
    geometryRow085_factorMaxima_read geometryRow085_gapWeightedMeans_read
    geometryRow085_jensenBound_read geometryRow085_floor_text_read geometryRow085_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_085_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson086 : SourceJson :=
  (SimplicesBlock043.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped086 : GeometryRow :=
  { simplexId := 86,
    vertexIds := #[39, 37, 24, 23, 21, 8, 3, 1, 0],
    physicalVolume := ((103169201485269348659610143012922081031 : ℚ) / (671793906401280000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((146404300803857 : ℚ) / (1657765200000000 : ℚ)), ((148080038128937 : ℚ) / (1657765200000000 : ℚ)), ((18319786602821 : ℚ) / (127520400000000 : ℚ)), ((271356120129943 : ℚ) / (2486647800000000 : ℚ)), ((5416607965669 : ℚ) / (97515600000000 : ℚ)), ((80959868861239 : ℚ) / (1657765200000000 : ℚ)), ((2046352511717 : ℚ) / (52350480000000 : ℚ)), ((38349582035339 : ℚ) / (994659120000000 : ℚ)), ((181824802450933 : ℚ) / (4973295600000000 : ℚ)), ((181823807791813 : ℚ) / (4973295600000000 : ℚ))],
    jensenBound := ((1691621813124492796477600129944479824317695395901783764585867320058142945958254073264605079817267200000000000000000000000 : ℚ) / (3313987125443078399826888903917633039957540014463688056541343308766700672461223824686249012525233527180617134603766870799334955372268547 : ℚ)),
    jensenFloorQ96 := (40441945864525 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_simplexId_before"
  err.flush

theorem geometryRow086_simplexId_read :
    geometryRowsJson086.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped086.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_vertexIds_before"
  err.flush

theorem geometryRow086_vertexIds_read :
    geometryRowsJson086.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped086.vertexIds := by decide +kernel

noncomputable def geometryRow086_physicalVolumeNumeratorChars : List Char := ['1', '0', '3', '1', '6', '9', '2', '0', '1', '4', '8', '5', '2', '6', '9', '3', '4', '8', '6', '5', '9', '6', '1', '0', '1', '4', '3', '0', '1', '2', '9', '2', '2', '0', '8', '1', '0', '3', '1']
noncomputable def geometryRow086_physicalVolumeDenominatorChars : List Char := ['6', '7', '1', '7', '9', '3', '9', '0', '6', '4', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow086_physicalVolumeText : String := String.ofList (geometryRow086_physicalVolumeNumeratorChars ++ '/' :: geometryRow086_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_physicalVolume_before_field"
  err.flush

theorem geometryRow086_physicalVolume_field :
    geometryRowsJson086.getObjVal? "physical_volume" = .ok (.str geometryRow086_physicalVolumeText) := by rfl

theorem geometryRow086_physicalVolume_numerator_no_slash :
    geometryRow086_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow086_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow086_physicalVolumeNumeratorChars = some (103169201485269348659610143012922081031 : Int) := by decide +kernel

theorem geometryRow086_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow086_physicalVolumeDenominatorChars = some (671793906401280000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow086_physicalVolume_denominator_nonzero : (671793906401280000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow086_physicalVolume_parse :
    parseRational geometryRow086_physicalVolumeText = .ok geometryRowsTyped086.physicalVolume :=
  original_rational_fraction_of_chars geometryRow086_physicalVolumeNumeratorChars geometryRow086_physicalVolumeDenominatorChars
    (103169201485269348659610143012922081031 : Int) (671793906401280000000000000000000000000000000000000000000000000 : Int)
    geometryRow086_physicalVolume_numerator_no_slash geometryRow086_physicalVolume_numerator_parse
    geometryRow086_physicalVolume_denominator_parse geometryRow086_physicalVolume_denominator_nonzero

theorem geometryRow086_physicalVolume_read :
    rationalField geometryRowsJson086 "physical_volume" = .ok geometryRowsTyped086.physicalVolume :=
  original_rationalField_of_string geometryRowsJson086 "physical_volume" geometryRow086_physicalVolumeText
    geometryRowsTyped086.physicalVolume geometryRow086_physicalVolume_field geometryRow086_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_physicalVolume_complete"
  err.flush

noncomputable def geometryRow086_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow086_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow086_meanGapText : String := String.ofList (geometryRow086_meanGapNumeratorChars ++ '/' :: geometryRow086_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_meanGap_before_field"
  err.flush

theorem geometryRow086_meanGap_field :
    geometryRowsJson086.getObjVal? "mean_gap" = .ok (.str geometryRow086_meanGapText) := by rfl

theorem geometryRow086_meanGap_numerator_no_slash :
    geometryRow086_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow086_meanGap_numerator_parse :
    SourceJson.intChars geometryRow086_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow086_meanGap_denominator_parse :
    SourceJson.intChars geometryRow086_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow086_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow086_meanGap_parse :
    parseRational geometryRow086_meanGapText = .ok geometryRowsTyped086.meanGap :=
  original_rational_fraction_of_chars geometryRow086_meanGapNumeratorChars geometryRow086_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow086_meanGap_numerator_no_slash geometryRow086_meanGap_numerator_parse
    geometryRow086_meanGap_denominator_parse geometryRow086_meanGap_denominator_nonzero

theorem geometryRow086_meanGap_read :
    rationalField geometryRowsJson086 "mean_gap" = .ok geometryRowsTyped086.meanGap :=
  original_rationalField_of_string geometryRowsJson086 "mean_gap" geometryRow086_meanGapText
    geometryRowsTyped086.meanGap geometryRow086_meanGap_field geometryRow086_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_meanGap_complete"
  err.flush

noncomputable def geometryRow086_jensenBoundNumeratorChars : List Char := ['1', '6', '9', '1', '6', '2', '1', '8', '1', '3', '1', '2', '4', '4', '9', '2', '7', '9', '6', '4', '7', '7', '6', '0', '0', '1', '2', '9', '9', '4', '4', '4', '7', '9', '8', '2', '4', '3', '1', '7', '6', '9', '5', '3', '9', '5', '9', '0', '1', '7', '8', '3', '7', '6', '4', '5', '8', '5', '8', '6', '7', '3', '2', '0', '0', '5', '8', '1', '4', '2', '9', '4', '5', '9', '5', '8', '2', '5', '4', '0', '7', '3', '2', '6', '4', '6', '0', '5', '0', '7', '9', '8', '1', '7', '2', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow086_jensenBoundDenominatorChars : List Char := ['3', '3', '1', '3', '9', '8', '7', '1', '2', '5', '4', '4', '3', '0', '7', '8', '3', '9', '9', '8', '2', '6', '8', '8', '8', '9', '0', '3', '9', '1', '7', '6', '3', '3', '0', '3', '9', '9', '5', '7', '5', '4', '0', '0', '1', '4', '4', '6', '3', '6', '8', '8', '0', '5', '6', '5', '4', '1', '3', '4', '3', '3', '0', '8', '7', '6', '6', '7', '0', '0', '6', '7', '2', '4', '6', '1', '2', '2', '3', '8', '2', '4', '6', '8', '6', '2', '4', '9', '0', '1', '2', '5', '2', '5', '2', '3', '3', '5', '2', '7', '1', '8', '0', '6', '1', '7', '1', '3', '4', '6', '0', '3', '7', '6', '6', '8', '7', '0', '7', '9', '9', '3', '3', '4', '9', '5', '5', '3', '7', '2', '2', '6', '8', '5', '4', '7']
noncomputable def geometryRow086_jensenBoundText : String := String.ofList (geometryRow086_jensenBoundNumeratorChars ++ '/' :: geometryRow086_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_jensenBound_before_field"
  err.flush

theorem geometryRow086_jensenBound_field :
    geometryRowsJson086.getObjVal? "jensen_bound" = .ok (.str geometryRow086_jensenBoundText) := by rfl

theorem geometryRow086_jensenBound_numerator_no_slash :
    geometryRow086_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow086_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow086_jensenBoundNumeratorChars = some (1691621813124492796477600129944479824317695395901783764585867320058142945958254073264605079817267200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow086_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow086_jensenBoundDenominatorChars = some (3313987125443078399826888903917633039957540014463688056541343308766700672461223824686249012525233527180617134603766870799334955372268547 : Int) := by decide +kernel

theorem geometryRow086_jensenBound_denominator_nonzero : (3313987125443078399826888903917633039957540014463688056541343308766700672461223824686249012525233527180617134603766870799334955372268547 : Int) ≠ 0 := by decide +kernel

theorem geometryRow086_jensenBound_parse :
    parseRational geometryRow086_jensenBoundText = .ok geometryRowsTyped086.jensenBound :=
  original_rational_fraction_of_chars geometryRow086_jensenBoundNumeratorChars geometryRow086_jensenBoundDenominatorChars
    (1691621813124492796477600129944479824317695395901783764585867320058142945958254073264605079817267200000000000000000000000 : Int) (3313987125443078399826888903917633039957540014463688056541343308766700672461223824686249012525233527180617134603766870799334955372268547 : Int)
    geometryRow086_jensenBound_numerator_no_slash geometryRow086_jensenBound_numerator_parse
    geometryRow086_jensenBound_denominator_parse geometryRow086_jensenBound_denominator_nonzero

theorem geometryRow086_jensenBound_read :
    rationalField geometryRowsJson086 "jensen_bound" = .ok geometryRowsTyped086.jensenBound :=
  original_rationalField_of_string geometryRowsJson086 "jensen_bound" geometryRow086_jensenBoundText
    geometryRowsTyped086.jensenBound geometryRow086_jensenBound_field geometryRow086_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_factorMaxima_before"
  err.flush

theorem geometryRow086_factorMaxima_read :
    rationalArrayField geometryRowsJson086 "factor_maxima" = .ok geometryRowsTyped086.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_gapWeightedMeans_before"
  err.flush

theorem geometryRow086_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson086 "gap_weighted_means" = .ok geometryRowsTyped086.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow086_floorChars : List Char := ['4', '0', '4', '4', '1', '9', '4', '5', '8', '6', '4', '5', '2', '5']
noncomputable def geometryRow086_floorText : String := String.ofList geometryRow086_floorChars

theorem geometryRow086_floor_text_read :
    geometryRowsJson086.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow086_floorText := by rfl

theorem geometryRow086_floor_chars_parse :
    SourceJson.intChars geometryRow086_floorChars = some (40441945864525 : Int) := by decide +kernel

theorem geometryRow086_floor_parse :
    parseInteger geometryRow086_floorText = .ok geometryRowsTyped086.jensenFloorQ96 := by
  simp only [geometryRow086_floorText, parseInteger, String.toList_ofList, geometryRow086_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_086 :
    decodeGeometryRow geometryRowsJson086 = .ok geometryRowsTyped086 :=
  original_geometryRow_of_fields geometryRowsJson086 geometryRowsTyped086 geometryRow086_floorText
    geometryRow086_simplexId_read geometryRow086_vertexIds_read
    geometryRow086_physicalVolume_read geometryRow086_meanGap_read
    geometryRow086_factorMaxima_read geometryRow086_gapWeightedMeans_read
    geometryRow086_jensenBound_read geometryRow086_floor_text_read geometryRow086_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_086_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock043 : List SourceJson := [geometryRowsJson085, geometryRowsJson086]
noncomputable def geometryRowsTypedBlock043 : List (GeometryRow) := [geometryRowsTyped085, geometryRowsTyped086]
noncomputable def geometryRowsTypedThroughBlock043 : List (GeometryRow) := geometryRowsTypedThroughBlock042 ++ geometryRowsTypedBlock043

theorem geometry_Rows_block_043_push_eq (acc : List SourceJson) :
    SimplicesBlock043.blockPush acc = [geometryRowsJson086, geometryRowsJson085] ++ acc := by rfl

theorem geometry_Rows_block_043_reverse (acc : List SourceJson) :
    (SimplicesBlock043.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock043 := by
  rw [geometry_Rows_block_043_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_043 :
    geometryRowsJsonBlock043.mapM decodeGeometryRow = .ok geometryRowsTypedBlock043 := by
  simp only [geometryRowsJsonBlock043, geometryRowsTypedBlock043, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_085, decode_geometry_Rows_086]
  rfl

theorem decode_geometry_Rows_through_block_043 :
    SimplicesValue.arrayAcc044.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock043 := by
  change (SimplicesBlock043.blockPush SimplicesValue.arrayAcc043).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_043_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_042, decode_geometry_Rows_block_043]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_043_complete"
  err.flush

#print axioms geometryRow085_simplexId_read
#print axioms geometryRow085_vertexIds_read
#print axioms geometryRow085_physicalVolume_field
#print axioms geometryRow085_physicalVolume_numerator_no_slash
#print axioms geometryRow085_physicalVolume_numerator_parse
#print axioms geometryRow085_physicalVolume_denominator_parse
#print axioms geometryRow085_physicalVolume_denominator_nonzero
#print axioms geometryRow085_physicalVolume_parse
#print axioms geometryRow085_physicalVolume_read
#print axioms geometryRow085_meanGap_field
#print axioms geometryRow085_meanGap_numerator_no_slash
#print axioms geometryRow085_meanGap_numerator_parse
#print axioms geometryRow085_meanGap_denominator_parse
#print axioms geometryRow085_meanGap_denominator_nonzero
#print axioms geometryRow085_meanGap_parse
#print axioms geometryRow085_meanGap_read
#print axioms geometryRow085_jensenBound_field
#print axioms geometryRow085_jensenBound_numerator_no_slash
#print axioms geometryRow085_jensenBound_numerator_parse
#print axioms geometryRow085_jensenBound_denominator_parse
#print axioms geometryRow085_jensenBound_denominator_nonzero
#print axioms geometryRow085_jensenBound_parse
#print axioms geometryRow085_jensenBound_read
#print axioms geometryRow085_factorMaxima_read
#print axioms geometryRow085_gapWeightedMeans_read
#print axioms geometryRow085_floor_text_read
#print axioms geometryRow085_floor_chars_parse
#print axioms geometryRow085_floor_parse
#print axioms decode_geometry_Rows_085
#print axioms geometryRow086_simplexId_read
#print axioms geometryRow086_vertexIds_read
#print axioms geometryRow086_physicalVolume_field
#print axioms geometryRow086_physicalVolume_numerator_no_slash
#print axioms geometryRow086_physicalVolume_numerator_parse
#print axioms geometryRow086_physicalVolume_denominator_parse
#print axioms geometryRow086_physicalVolume_denominator_nonzero
#print axioms geometryRow086_physicalVolume_parse
#print axioms geometryRow086_physicalVolume_read
#print axioms geometryRow086_meanGap_field
#print axioms geometryRow086_meanGap_numerator_no_slash
#print axioms geometryRow086_meanGap_numerator_parse
#print axioms geometryRow086_meanGap_denominator_parse
#print axioms geometryRow086_meanGap_denominator_nonzero
#print axioms geometryRow086_meanGap_parse
#print axioms geometryRow086_meanGap_read
#print axioms geometryRow086_jensenBound_field
#print axioms geometryRow086_jensenBound_numerator_no_slash
#print axioms geometryRow086_jensenBound_numerator_parse
#print axioms geometryRow086_jensenBound_denominator_parse
#print axioms geometryRow086_jensenBound_denominator_nonzero
#print axioms geometryRow086_jensenBound_parse
#print axioms geometryRow086_jensenBound_read
#print axioms geometryRow086_factorMaxima_read
#print axioms geometryRow086_gapWeightedMeans_read
#print axioms geometryRow086_floor_text_read
#print axioms geometryRow086_floor_chars_parse
#print axioms geometryRow086_floor_parse
#print axioms decode_geometry_Rows_086
#print axioms geometry_Rows_block_043_push_eq
#print axioms geometry_Rows_block_043_reverse
#print axioms decode_geometry_Rows_block_043
#print axioms decode_geometry_Rows_through_block_043

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
