import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows053

/-! Original simplices typed block 54, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson106 : SourceJson :=
  (SimplicesBlock054.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped106 : GeometryRow :=
  { simplexId := 106,
    vertexIds := #[39, 37, 24, 22, 19, 18, 15, 14, 7],
    physicalVolume := ((31356995879186140269558226687239483168259 : ℚ) / (4385431267772792832000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((403117 : ℚ) / (7200000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((143027593391 : ℚ) / (1901520000000 : ℚ)), ((143444025587 : ℚ) / (1901520000000 : ℚ)), ((841423239397 : ℚ) / (5704560000000 : ℚ)), ((39950198249 : ℚ) / (369740000000 : ℚ)), ((2036096300927 : ℚ) / (39931920000000 : ℚ)), ((268989336719 : ℚ) / (5704560000000 : ℚ)), ((347840420939 : ℚ) / (7986384000000 : ℚ)), ((1696554043519 : ℚ) / (39931920000000 : ℚ)), ((1696551381391 : ℚ) / (39931920000000 : ℚ)), ((1592911280959 : ℚ) / (39931920000000 : ℚ))],
    jensenBound := ((16952747584812168426142307819686209889494620589839813295632616235947558618832896000000000000000 : ℚ) / (3321919020885108784938497517410926033445367157489648948345076515402472504284480433126809129894793652178194104021 : ℚ)),
    jensenFloorQ96 := (404325039914 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_simplexId_before"
  err.flush

theorem geometryRow106_simplexId_read :
    geometryRowsJson106.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped106.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_vertexIds_before"
  err.flush

theorem geometryRow106_vertexIds_read :
    geometryRowsJson106.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped106.vertexIds := by decide +kernel

noncomputable def geometryRow106_physicalVolumeNumeratorChars : List Char := ['3', '1', '3', '5', '6', '9', '9', '5', '8', '7', '9', '1', '8', '6', '1', '4', '0', '2', '6', '9', '5', '5', '8', '2', '2', '6', '6', '8', '7', '2', '3', '9', '4', '8', '3', '1', '6', '8', '2', '5', '9']
noncomputable def geometryRow106_physicalVolumeDenominatorChars : List Char := ['4', '3', '8', '5', '4', '3', '1', '2', '6', '7', '7', '7', '2', '7', '9', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow106_physicalVolumeText : String := String.ofList (geometryRow106_physicalVolumeNumeratorChars ++ '/' :: geometryRow106_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_physicalVolume_before_field"
  err.flush

theorem geometryRow106_physicalVolume_field :
    geometryRowsJson106.getObjVal? "physical_volume" = .ok (.str geometryRow106_physicalVolumeText) := by rfl

theorem geometryRow106_physicalVolume_numerator_no_slash :
    geometryRow106_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow106_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow106_physicalVolumeNumeratorChars = some (31356995879186140269558226687239483168259 : Int) := by decide +kernel

theorem geometryRow106_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow106_physicalVolumeDenominatorChars = some (4385431267772792832000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow106_physicalVolume_denominator_nonzero : (4385431267772792832000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow106_physicalVolume_parse :
    parseRational geometryRow106_physicalVolumeText = .ok geometryRowsTyped106.physicalVolume :=
  original_rational_fraction_of_chars geometryRow106_physicalVolumeNumeratorChars geometryRow106_physicalVolumeDenominatorChars
    (31356995879186140269558226687239483168259 : Int) (4385431267772792832000000000000000000000000000000000000000000000000 : Int)
    geometryRow106_physicalVolume_numerator_no_slash geometryRow106_physicalVolume_numerator_parse
    geometryRow106_physicalVolume_denominator_parse geometryRow106_physicalVolume_denominator_nonzero

theorem geometryRow106_physicalVolume_read :
    rationalField geometryRowsJson106 "physical_volume" = .ok geometryRowsTyped106.physicalVolume :=
  original_rationalField_of_string geometryRowsJson106 "physical_volume" geometryRow106_physicalVolumeText
    geometryRowsTyped106.physicalVolume geometryRow106_physicalVolume_field geometryRow106_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_physicalVolume_complete"
  err.flush

noncomputable def geometryRow106_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow106_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow106_meanGapText : String := String.ofList (geometryRow106_meanGapNumeratorChars ++ '/' :: geometryRow106_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_meanGap_before_field"
  err.flush

theorem geometryRow106_meanGap_field :
    geometryRowsJson106.getObjVal? "mean_gap" = .ok (.str geometryRow106_meanGapText) := by rfl

theorem geometryRow106_meanGap_numerator_no_slash :
    geometryRow106_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow106_meanGap_numerator_parse :
    SourceJson.intChars geometryRow106_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow106_meanGap_denominator_parse :
    SourceJson.intChars geometryRow106_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow106_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow106_meanGap_parse :
    parseRational geometryRow106_meanGapText = .ok geometryRowsTyped106.meanGap :=
  original_rational_fraction_of_chars geometryRow106_meanGapNumeratorChars geometryRow106_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow106_meanGap_numerator_no_slash geometryRow106_meanGap_numerator_parse
    geometryRow106_meanGap_denominator_parse geometryRow106_meanGap_denominator_nonzero

theorem geometryRow106_meanGap_read :
    rationalField geometryRowsJson106 "mean_gap" = .ok geometryRowsTyped106.meanGap :=
  original_rationalField_of_string geometryRowsJson106 "mean_gap" geometryRow106_meanGapText
    geometryRowsTyped106.meanGap geometryRow106_meanGap_field geometryRow106_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_meanGap_complete"
  err.flush

noncomputable def geometryRow106_jensenBoundNumeratorChars : List Char := ['1', '6', '9', '5', '2', '7', '4', '7', '5', '8', '4', '8', '1', '2', '1', '6', '8', '4', '2', '6', '1', '4', '2', '3', '0', '7', '8', '1', '9', '6', '8', '6', '2', '0', '9', '8', '8', '9', '4', '9', '4', '6', '2', '0', '5', '8', '9', '8', '3', '9', '8', '1', '3', '2', '9', '5', '6', '3', '2', '6', '1', '6', '2', '3', '5', '9', '4', '7', '5', '5', '8', '6', '1', '8', '8', '3', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow106_jensenBoundDenominatorChars : List Char := ['3', '3', '2', '1', '9', '1', '9', '0', '2', '0', '8', '8', '5', '1', '0', '8', '7', '8', '4', '9', '3', '8', '4', '9', '7', '5', '1', '7', '4', '1', '0', '9', '2', '6', '0', '3', '3', '4', '4', '5', '3', '6', '7', '1', '5', '7', '4', '8', '9', '6', '4', '8', '9', '4', '8', '3', '4', '5', '0', '7', '6', '5', '1', '5', '4', '0', '2', '4', '7', '2', '5', '0', '4', '2', '8', '4', '4', '8', '0', '4', '3', '3', '1', '2', '6', '8', '0', '9', '1', '2', '9', '8', '9', '4', '7', '9', '3', '6', '5', '2', '1', '7', '8', '1', '9', '4', '1', '0', '4', '0', '2', '1']
noncomputable def geometryRow106_jensenBoundText : String := String.ofList (geometryRow106_jensenBoundNumeratorChars ++ '/' :: geometryRow106_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_jensenBound_before_field"
  err.flush

theorem geometryRow106_jensenBound_field :
    geometryRowsJson106.getObjVal? "jensen_bound" = .ok (.str geometryRow106_jensenBoundText) := by rfl

theorem geometryRow106_jensenBound_numerator_no_slash :
    geometryRow106_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow106_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow106_jensenBoundNumeratorChars = some (16952747584812168426142307819686209889494620589839813295632616235947558618832896000000000000000 : Int) := by decide +kernel

theorem geometryRow106_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow106_jensenBoundDenominatorChars = some (3321919020885108784938497517410926033445367157489648948345076515402472504284480433126809129894793652178194104021 : Int) := by decide +kernel

theorem geometryRow106_jensenBound_denominator_nonzero : (3321919020885108784938497517410926033445367157489648948345076515402472504284480433126809129894793652178194104021 : Int) ≠ 0 := by decide +kernel

theorem geometryRow106_jensenBound_parse :
    parseRational geometryRow106_jensenBoundText = .ok geometryRowsTyped106.jensenBound :=
  original_rational_fraction_of_chars geometryRow106_jensenBoundNumeratorChars geometryRow106_jensenBoundDenominatorChars
    (16952747584812168426142307819686209889494620589839813295632616235947558618832896000000000000000 : Int) (3321919020885108784938497517410926033445367157489648948345076515402472504284480433126809129894793652178194104021 : Int)
    geometryRow106_jensenBound_numerator_no_slash geometryRow106_jensenBound_numerator_parse
    geometryRow106_jensenBound_denominator_parse geometryRow106_jensenBound_denominator_nonzero

theorem geometryRow106_jensenBound_read :
    rationalField geometryRowsJson106 "jensen_bound" = .ok geometryRowsTyped106.jensenBound :=
  original_rationalField_of_string geometryRowsJson106 "jensen_bound" geometryRow106_jensenBoundText
    geometryRowsTyped106.jensenBound geometryRow106_jensenBound_field geometryRow106_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_factorMaxima_before"
  err.flush

theorem geometryRow106_factorMaxima_read :
    rationalArrayField geometryRowsJson106 "factor_maxima" = .ok geometryRowsTyped106.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_gapWeightedMeans_before"
  err.flush

theorem geometryRow106_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson106 "gap_weighted_means" = .ok geometryRowsTyped106.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow106_floorChars : List Char := ['4', '0', '4', '3', '2', '5', '0', '3', '9', '9', '1', '4']
noncomputable def geometryRow106_floorText : String := String.ofList geometryRow106_floorChars

theorem geometryRow106_floor_text_read :
    geometryRowsJson106.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow106_floorText := by rfl

theorem geometryRow106_floor_chars_parse :
    SourceJson.intChars geometryRow106_floorChars = some (404325039914 : Int) := by decide +kernel

theorem geometryRow106_floor_parse :
    parseInteger geometryRow106_floorText = .ok geometryRowsTyped106.jensenFloorQ96 := by
  simp only [geometryRow106_floorText, parseInteger, String.toList_ofList, geometryRow106_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_106 :
    decodeGeometryRow geometryRowsJson106 = .ok geometryRowsTyped106 :=
  original_geometryRow_of_fields geometryRowsJson106 geometryRowsTyped106 geometryRow106_floorText
    geometryRow106_simplexId_read geometryRow106_vertexIds_read
    geometryRow106_physicalVolume_read geometryRow106_meanGap_read
    geometryRow106_factorMaxima_read geometryRow106_gapWeightedMeans_read
    geometryRow106_jensenBound_read geometryRow106_floor_text_read geometryRow106_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_106_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson107 : SourceJson :=
  (SimplicesBlock054.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped107 : GeometryRow :=
  { simplexId := 107,
    vertexIds := #[39, 37, 36, 24, 11, 10, 8, 3, 1],
    physicalVolume := ((150457257862564746558444027302443 : ℚ) / (47628288000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((656786281819 : ℚ) / (7054320000000 : ℚ)), ((663917078947 : ℚ) / (7054320000000 : ℚ)), ((236979613279 : ℚ) / (1627920000000 : ℚ)), ((1206108474757 : ℚ) / (10581480000000 : ℚ)), ((2668648399 : ℚ) / (49795200000 : ℚ)), ((995841210857 : ℚ) / (21162960000000 : ℚ)), ((833500371329 : ℚ) / (21162960000000 : ℚ)), ((770247087053 : ℚ) / (21162960000000 : ℚ)), ((711347953529 : ℚ) / (21162960000000 : ℚ)), ((711345131801 : ℚ) / (21162960000000 : ℚ))],
    jensenBound := ((1285813275749787366859601319050353278019989953058420118336646013704097331984853654018457600000000000000 : ℚ) / (107600684646348693802680018352507514739965066193025484491853085870738520982777444489916309555293458733418073845151481 : ℚ)),
    jensenFloorQ96 := (946765566677643 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_simplexId_before"
  err.flush

theorem geometryRow107_simplexId_read :
    geometryRowsJson107.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped107.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_vertexIds_before"
  err.flush

theorem geometryRow107_vertexIds_read :
    geometryRowsJson107.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped107.vertexIds := by decide +kernel

noncomputable def geometryRow107_physicalVolumeNumeratorChars : List Char := ['1', '5', '0', '4', '5', '7', '2', '5', '7', '8', '6', '2', '5', '6', '4', '7', '4', '6', '5', '5', '8', '4', '4', '4', '0', '2', '7', '3', '0', '2', '4', '4', '3']
noncomputable def geometryRow107_physicalVolumeDenominatorChars : List Char := ['4', '7', '6', '2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow107_physicalVolumeText : String := String.ofList (geometryRow107_physicalVolumeNumeratorChars ++ '/' :: geometryRow107_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_physicalVolume_before_field"
  err.flush

theorem geometryRow107_physicalVolume_field :
    geometryRowsJson107.getObjVal? "physical_volume" = .ok (.str geometryRow107_physicalVolumeText) := by rfl

theorem geometryRow107_physicalVolume_numerator_no_slash :
    geometryRow107_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow107_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow107_physicalVolumeNumeratorChars = some (150457257862564746558444027302443 : Int) := by decide +kernel

theorem geometryRow107_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow107_physicalVolumeDenominatorChars = some (47628288000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow107_physicalVolume_denominator_nonzero : (47628288000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow107_physicalVolume_parse :
    parseRational geometryRow107_physicalVolumeText = .ok geometryRowsTyped107.physicalVolume :=
  original_rational_fraction_of_chars geometryRow107_physicalVolumeNumeratorChars geometryRow107_physicalVolumeDenominatorChars
    (150457257862564746558444027302443 : Int) (47628288000000000000000000000000000000000000000000000000 : Int)
    geometryRow107_physicalVolume_numerator_no_slash geometryRow107_physicalVolume_numerator_parse
    geometryRow107_physicalVolume_denominator_parse geometryRow107_physicalVolume_denominator_nonzero

theorem geometryRow107_physicalVolume_read :
    rationalField geometryRowsJson107 "physical_volume" = .ok geometryRowsTyped107.physicalVolume :=
  original_rationalField_of_string geometryRowsJson107 "physical_volume" geometryRow107_physicalVolumeText
    geometryRowsTyped107.physicalVolume geometryRow107_physicalVolume_field geometryRow107_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_physicalVolume_complete"
  err.flush

noncomputable def geometryRow107_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow107_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow107_meanGapText : String := String.ofList (geometryRow107_meanGapNumeratorChars ++ '/' :: geometryRow107_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_meanGap_before_field"
  err.flush

theorem geometryRow107_meanGap_field :
    geometryRowsJson107.getObjVal? "mean_gap" = .ok (.str geometryRow107_meanGapText) := by rfl

theorem geometryRow107_meanGap_numerator_no_slash :
    geometryRow107_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow107_meanGap_numerator_parse :
    SourceJson.intChars geometryRow107_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow107_meanGap_denominator_parse :
    SourceJson.intChars geometryRow107_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow107_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow107_meanGap_parse :
    parseRational geometryRow107_meanGapText = .ok geometryRowsTyped107.meanGap :=
  original_rational_fraction_of_chars geometryRow107_meanGapNumeratorChars geometryRow107_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow107_meanGap_numerator_no_slash geometryRow107_meanGap_numerator_parse
    geometryRow107_meanGap_denominator_parse geometryRow107_meanGap_denominator_nonzero

theorem geometryRow107_meanGap_read :
    rationalField geometryRowsJson107 "mean_gap" = .ok geometryRowsTyped107.meanGap :=
  original_rationalField_of_string geometryRowsJson107 "mean_gap" geometryRow107_meanGapText
    geometryRowsTyped107.meanGap geometryRow107_meanGap_field geometryRow107_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_meanGap_complete"
  err.flush

noncomputable def geometryRow107_jensenBoundNumeratorChars : List Char := ['1', '2', '8', '5', '8', '1', '3', '2', '7', '5', '7', '4', '9', '7', '8', '7', '3', '6', '6', '8', '5', '9', '6', '0', '1', '3', '1', '9', '0', '5', '0', '3', '5', '3', '2', '7', '8', '0', '1', '9', '9', '8', '9', '9', '5', '3', '0', '5', '8', '4', '2', '0', '1', '1', '8', '3', '3', '6', '6', '4', '6', '0', '1', '3', '7', '0', '4', '0', '9', '7', '3', '3', '1', '9', '8', '4', '8', '5', '3', '6', '5', '4', '0', '1', '8', '4', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow107_jensenBoundDenominatorChars : List Char := ['1', '0', '7', '6', '0', '0', '6', '8', '4', '6', '4', '6', '3', '4', '8', '6', '9', '3', '8', '0', '2', '6', '8', '0', '0', '1', '8', '3', '5', '2', '5', '0', '7', '5', '1', '4', '7', '3', '9', '9', '6', '5', '0', '6', '6', '1', '9', '3', '0', '2', '5', '4', '8', '4', '4', '9', '1', '8', '5', '3', '0', '8', '5', '8', '7', '0', '7', '3', '8', '5', '2', '0', '9', '8', '2', '7', '7', '7', '4', '4', '4', '4', '8', '9', '9', '1', '6', '3', '0', '9', '5', '5', '5', '2', '9', '3', '4', '5', '8', '7', '3', '3', '4', '1', '8', '0', '7', '3', '8', '4', '5', '1', '5', '1', '4', '8', '1']
noncomputable def geometryRow107_jensenBoundText : String := String.ofList (geometryRow107_jensenBoundNumeratorChars ++ '/' :: geometryRow107_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_jensenBound_before_field"
  err.flush

theorem geometryRow107_jensenBound_field :
    geometryRowsJson107.getObjVal? "jensen_bound" = .ok (.str geometryRow107_jensenBoundText) := by rfl

theorem geometryRow107_jensenBound_numerator_no_slash :
    geometryRow107_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow107_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow107_jensenBoundNumeratorChars = some (1285813275749787366859601319050353278019989953058420118336646013704097331984853654018457600000000000000 : Int) := by decide +kernel

theorem geometryRow107_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow107_jensenBoundDenominatorChars = some (107600684646348693802680018352507514739965066193025484491853085870738520982777444489916309555293458733418073845151481 : Int) := by decide +kernel

theorem geometryRow107_jensenBound_denominator_nonzero : (107600684646348693802680018352507514739965066193025484491853085870738520982777444489916309555293458733418073845151481 : Int) ≠ 0 := by decide +kernel

theorem geometryRow107_jensenBound_parse :
    parseRational geometryRow107_jensenBoundText = .ok geometryRowsTyped107.jensenBound :=
  original_rational_fraction_of_chars geometryRow107_jensenBoundNumeratorChars geometryRow107_jensenBoundDenominatorChars
    (1285813275749787366859601319050353278019989953058420118336646013704097331984853654018457600000000000000 : Int) (107600684646348693802680018352507514739965066193025484491853085870738520982777444489916309555293458733418073845151481 : Int)
    geometryRow107_jensenBound_numerator_no_slash geometryRow107_jensenBound_numerator_parse
    geometryRow107_jensenBound_denominator_parse geometryRow107_jensenBound_denominator_nonzero

theorem geometryRow107_jensenBound_read :
    rationalField geometryRowsJson107 "jensen_bound" = .ok geometryRowsTyped107.jensenBound :=
  original_rationalField_of_string geometryRowsJson107 "jensen_bound" geometryRow107_jensenBoundText
    geometryRowsTyped107.jensenBound geometryRow107_jensenBound_field geometryRow107_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_factorMaxima_before"
  err.flush

theorem geometryRow107_factorMaxima_read :
    rationalArrayField geometryRowsJson107 "factor_maxima" = .ok geometryRowsTyped107.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_gapWeightedMeans_before"
  err.flush

theorem geometryRow107_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson107 "gap_weighted_means" = .ok geometryRowsTyped107.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow107_floorChars : List Char := ['9', '4', '6', '7', '6', '5', '5', '6', '6', '6', '7', '7', '6', '4', '3']
noncomputable def geometryRow107_floorText : String := String.ofList geometryRow107_floorChars

theorem geometryRow107_floor_text_read :
    geometryRowsJson107.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow107_floorText := by rfl

theorem geometryRow107_floor_chars_parse :
    SourceJson.intChars geometryRow107_floorChars = some (946765566677643 : Int) := by decide +kernel

theorem geometryRow107_floor_parse :
    parseInteger geometryRow107_floorText = .ok geometryRowsTyped107.jensenFloorQ96 := by
  simp only [geometryRow107_floorText, parseInteger, String.toList_ofList, geometryRow107_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_107 :
    decodeGeometryRow geometryRowsJson107 = .ok geometryRowsTyped107 :=
  original_geometryRow_of_fields geometryRowsJson107 geometryRowsTyped107 geometryRow107_floorText
    geometryRow107_simplexId_read geometryRow107_vertexIds_read
    geometryRow107_physicalVolume_read geometryRow107_meanGap_read
    geometryRow107_factorMaxima_read geometryRow107_gapWeightedMeans_read
    geometryRow107_jensenBound_read geometryRow107_floor_text_read geometryRow107_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_107_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock054 : List SourceJson := [geometryRowsJson106, geometryRowsJson107]
noncomputable def geometryRowsTypedBlock054 : List (GeometryRow) := [geometryRowsTyped106, geometryRowsTyped107]
noncomputable def geometryRowsTypedThroughBlock054 : List (GeometryRow) := geometryRowsTypedThroughBlock053 ++ geometryRowsTypedBlock054

theorem geometry_Rows_block_054_push_eq (acc : List SourceJson) :
    SimplicesBlock054.blockPush acc = [geometryRowsJson107, geometryRowsJson106] ++ acc := by rfl

theorem geometry_Rows_block_054_reverse (acc : List SourceJson) :
    (SimplicesBlock054.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock054 := by
  rw [geometry_Rows_block_054_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_054 :
    geometryRowsJsonBlock054.mapM decodeGeometryRow = .ok geometryRowsTypedBlock054 := by
  simp only [geometryRowsJsonBlock054, geometryRowsTypedBlock054, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_106, decode_geometry_Rows_107]
  rfl

theorem decode_geometry_Rows_through_block_054 :
    SimplicesValue.arrayAcc055.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock054 := by
  change (SimplicesBlock054.blockPush SimplicesValue.arrayAcc054).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_054_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_053, decode_geometry_Rows_block_054]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_054_complete"
  err.flush

#print axioms geometryRow106_simplexId_read
#print axioms geometryRow106_vertexIds_read
#print axioms geometryRow106_physicalVolume_field
#print axioms geometryRow106_physicalVolume_numerator_no_slash
#print axioms geometryRow106_physicalVolume_numerator_parse
#print axioms geometryRow106_physicalVolume_denominator_parse
#print axioms geometryRow106_physicalVolume_denominator_nonzero
#print axioms geometryRow106_physicalVolume_parse
#print axioms geometryRow106_physicalVolume_read
#print axioms geometryRow106_meanGap_field
#print axioms geometryRow106_meanGap_numerator_no_slash
#print axioms geometryRow106_meanGap_numerator_parse
#print axioms geometryRow106_meanGap_denominator_parse
#print axioms geometryRow106_meanGap_denominator_nonzero
#print axioms geometryRow106_meanGap_parse
#print axioms geometryRow106_meanGap_read
#print axioms geometryRow106_jensenBound_field
#print axioms geometryRow106_jensenBound_numerator_no_slash
#print axioms geometryRow106_jensenBound_numerator_parse
#print axioms geometryRow106_jensenBound_denominator_parse
#print axioms geometryRow106_jensenBound_denominator_nonzero
#print axioms geometryRow106_jensenBound_parse
#print axioms geometryRow106_jensenBound_read
#print axioms geometryRow106_factorMaxima_read
#print axioms geometryRow106_gapWeightedMeans_read
#print axioms geometryRow106_floor_text_read
#print axioms geometryRow106_floor_chars_parse
#print axioms geometryRow106_floor_parse
#print axioms decode_geometry_Rows_106
#print axioms geometryRow107_simplexId_read
#print axioms geometryRow107_vertexIds_read
#print axioms geometryRow107_physicalVolume_field
#print axioms geometryRow107_physicalVolume_numerator_no_slash
#print axioms geometryRow107_physicalVolume_numerator_parse
#print axioms geometryRow107_physicalVolume_denominator_parse
#print axioms geometryRow107_physicalVolume_denominator_nonzero
#print axioms geometryRow107_physicalVolume_parse
#print axioms geometryRow107_physicalVolume_read
#print axioms geometryRow107_meanGap_field
#print axioms geometryRow107_meanGap_numerator_no_slash
#print axioms geometryRow107_meanGap_numerator_parse
#print axioms geometryRow107_meanGap_denominator_parse
#print axioms geometryRow107_meanGap_denominator_nonzero
#print axioms geometryRow107_meanGap_parse
#print axioms geometryRow107_meanGap_read
#print axioms geometryRow107_jensenBound_field
#print axioms geometryRow107_jensenBound_numerator_no_slash
#print axioms geometryRow107_jensenBound_numerator_parse
#print axioms geometryRow107_jensenBound_denominator_parse
#print axioms geometryRow107_jensenBound_denominator_nonzero
#print axioms geometryRow107_jensenBound_parse
#print axioms geometryRow107_jensenBound_read
#print axioms geometryRow107_factorMaxima_read
#print axioms geometryRow107_gapWeightedMeans_read
#print axioms geometryRow107_floor_text_read
#print axioms geometryRow107_floor_chars_parse
#print axioms geometryRow107_floor_parse
#print axioms decode_geometry_Rows_107
#print axioms geometry_Rows_block_054_push_eq
#print axioms geometry_Rows_block_054_reverse
#print axioms decode_geometry_Rows_block_054
#print axioms decode_geometry_Rows_through_block_054

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
