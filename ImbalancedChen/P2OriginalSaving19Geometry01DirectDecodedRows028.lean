import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows027

/-! Original simplices typed block 28, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson055 : SourceJson :=
  (SimplicesBlock028.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped055 : GeometryRow :=
  { simplexId := 55,
    vertexIds := #[39, 35, 24, 22, 9, 7, 6, 2, 0],
    physicalVolume := ((6932511985563617706576707858357081701789 : ℚ) / (1483258355712000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((1703169 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((1641158261 : ℚ) / (19950000000 : ℚ)), ((2908758683 : ℚ) / (34912500000 : ℚ)), ((16006940101 : ℚ) / (111720000000 : ℚ)), ((11617105349 : ℚ) / (104737500000 : ℚ)), ((5571618187 : ℚ) / (93100000000 : ℚ)), ((27478934221 : ℚ) / (558600000000 : ℚ)), ((11480945537 : ℚ) / (279300000000 : ℚ)), ((10496988857 : ℚ) / (279300000000 : ℚ)), ((3498990079 : ℚ) / (93100000000 : ℚ)), ((57760013251 : ℚ) / (1675800000000 : ℚ))],
    jensenBound := ((149520824038951949833629885036785415111971738624444089683143124425354003906250000000 : ℚ) / (8780447959974798915645066950941905230885982709714457722676908210509936346967131986622035871496557 : ℚ)),
    jensenFloorQ96 := (1349163527900324 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_simplexId_before"
  err.flush

theorem geometryRow055_simplexId_read :
    geometryRowsJson055.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped055.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_vertexIds_before"
  err.flush

theorem geometryRow055_vertexIds_read :
    geometryRowsJson055.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped055.vertexIds := by decide +kernel

noncomputable def geometryRow055_physicalVolumeNumeratorChars : List Char := ['6', '9', '3', '2', '5', '1', '1', '9', '8', '5', '5', '6', '3', '6', '1', '7', '7', '0', '6', '5', '7', '6', '7', '0', '7', '8', '5', '8', '3', '5', '7', '0', '8', '1', '7', '0', '1', '7', '8', '9']
noncomputable def geometryRow055_physicalVolumeDenominatorChars : List Char := ['1', '4', '8', '3', '2', '5', '8', '3', '5', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_physicalVolumeText : String := String.ofList (geometryRow055_physicalVolumeNumeratorChars ++ '/' :: geometryRow055_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_physicalVolume_before_field"
  err.flush

theorem geometryRow055_physicalVolume_field :
    geometryRowsJson055.getObjVal? "physical_volume" = .ok (.str geometryRow055_physicalVolumeText) := by rfl

theorem geometryRow055_physicalVolume_numerator_no_slash :
    geometryRow055_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeNumeratorChars = some (6932511985563617706576707858357081701789 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeDenominatorChars = some (1483258355712000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_nonzero : (1483258355712000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_physicalVolume_parse :
    parseRational geometryRow055_physicalVolumeText = .ok geometryRowsTyped055.physicalVolume :=
  original_rational_fraction_of_chars geometryRow055_physicalVolumeNumeratorChars geometryRow055_physicalVolumeDenominatorChars
    (6932511985563617706576707858357081701789 : Int) (1483258355712000000000000000000000000000000000000000000000000000 : Int)
    geometryRow055_physicalVolume_numerator_no_slash geometryRow055_physicalVolume_numerator_parse
    geometryRow055_physicalVolume_denominator_parse geometryRow055_physicalVolume_denominator_nonzero

theorem geometryRow055_physicalVolume_read :
    rationalField geometryRowsJson055 "physical_volume" = .ok geometryRowsTyped055.physicalVolume :=
  original_rationalField_of_string geometryRowsJson055 "physical_volume" geometryRow055_physicalVolumeText
    geometryRowsTyped055.physicalVolume geometryRow055_physicalVolume_field geometryRow055_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_physicalVolume_complete"
  err.flush

noncomputable def geometryRow055_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow055_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_meanGapText : String := String.ofList (geometryRow055_meanGapNumeratorChars ++ '/' :: geometryRow055_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_meanGap_before_field"
  err.flush

theorem geometryRow055_meanGap_field :
    geometryRowsJson055.getObjVal? "mean_gap" = .ok (.str geometryRow055_meanGapText) := by rfl

theorem geometryRow055_meanGap_numerator_no_slash :
    geometryRow055_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_meanGap_numerator_parse :
    SourceJson.intChars geometryRow055_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_parse :
    SourceJson.intChars geometryRow055_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_meanGap_parse :
    parseRational geometryRow055_meanGapText = .ok geometryRowsTyped055.meanGap :=
  original_rational_fraction_of_chars geometryRow055_meanGapNumeratorChars geometryRow055_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow055_meanGap_numerator_no_slash geometryRow055_meanGap_numerator_parse
    geometryRow055_meanGap_denominator_parse geometryRow055_meanGap_denominator_nonzero

theorem geometryRow055_meanGap_read :
    rationalField geometryRowsJson055 "mean_gap" = .ok geometryRowsTyped055.meanGap :=
  original_rationalField_of_string geometryRowsJson055 "mean_gap" geometryRow055_meanGapText
    geometryRowsTyped055.meanGap geometryRow055_meanGap_field geometryRow055_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_meanGap_complete"
  err.flush

noncomputable def geometryRow055_jensenBoundNumeratorChars : List Char := ['1', '4', '9', '5', '2', '0', '8', '2', '4', '0', '3', '8', '9', '5', '1', '9', '4', '9', '8', '3', '3', '6', '2', '9', '8', '8', '5', '0', '3', '6', '7', '8', '5', '4', '1', '5', '1', '1', '1', '9', '7', '1', '7', '3', '8', '6', '2', '4', '4', '4', '4', '0', '8', '9', '6', '8', '3', '1', '4', '3', '1', '2', '4', '4', '2', '5', '3', '5', '4', '0', '0', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_jensenBoundDenominatorChars : List Char := ['8', '7', '8', '0', '4', '4', '7', '9', '5', '9', '9', '7', '4', '7', '9', '8', '9', '1', '5', '6', '4', '5', '0', '6', '6', '9', '5', '0', '9', '4', '1', '9', '0', '5', '2', '3', '0', '8', '8', '5', '9', '8', '2', '7', '0', '9', '7', '1', '4', '4', '5', '7', '7', '2', '2', '6', '7', '6', '9', '0', '8', '2', '1', '0', '5', '0', '9', '9', '3', '6', '3', '4', '6', '9', '6', '7', '1', '3', '1', '9', '8', '6', '6', '2', '2', '0', '3', '5', '8', '7', '1', '4', '9', '6', '5', '5', '7']
noncomputable def geometryRow055_jensenBoundText : String := String.ofList (geometryRow055_jensenBoundNumeratorChars ++ '/' :: geometryRow055_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_jensenBound_before_field"
  err.flush

theorem geometryRow055_jensenBound_field :
    geometryRowsJson055.getObjVal? "jensen_bound" = .ok (.str geometryRow055_jensenBoundText) := by rfl

theorem geometryRow055_jensenBound_numerator_no_slash :
    geometryRow055_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow055_jensenBoundNumeratorChars = some (149520824038951949833629885036785415111971738624444089683143124425354003906250000000 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow055_jensenBoundDenominatorChars = some (8780447959974798915645066950941905230885982709714457722676908210509936346967131986622035871496557 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_nonzero : (8780447959974798915645066950941905230885982709714457722676908210509936346967131986622035871496557 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_jensenBound_parse :
    parseRational geometryRow055_jensenBoundText = .ok geometryRowsTyped055.jensenBound :=
  original_rational_fraction_of_chars geometryRow055_jensenBoundNumeratorChars geometryRow055_jensenBoundDenominatorChars
    (149520824038951949833629885036785415111971738624444089683143124425354003906250000000 : Int) (8780447959974798915645066950941905230885982709714457722676908210509936346967131986622035871496557 : Int)
    geometryRow055_jensenBound_numerator_no_slash geometryRow055_jensenBound_numerator_parse
    geometryRow055_jensenBound_denominator_parse geometryRow055_jensenBound_denominator_nonzero

theorem geometryRow055_jensenBound_read :
    rationalField geometryRowsJson055 "jensen_bound" = .ok geometryRowsTyped055.jensenBound :=
  original_rationalField_of_string geometryRowsJson055 "jensen_bound" geometryRow055_jensenBoundText
    geometryRowsTyped055.jensenBound geometryRow055_jensenBound_field geometryRow055_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_factorMaxima_before"
  err.flush

theorem geometryRow055_factorMaxima_read :
    rationalArrayField geometryRowsJson055 "factor_maxima" = .ok geometryRowsTyped055.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_gapWeightedMeans_before"
  err.flush

theorem geometryRow055_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson055 "gap_weighted_means" = .ok geometryRowsTyped055.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow055_floorChars : List Char := ['1', '3', '4', '9', '1', '6', '3', '5', '2', '7', '9', '0', '0', '3', '2', '4']
noncomputable def geometryRow055_floorText : String := String.ofList geometryRow055_floorChars

theorem geometryRow055_floor_text_read :
    geometryRowsJson055.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow055_floorText := by rfl

theorem geometryRow055_floor_chars_parse :
    SourceJson.intChars geometryRow055_floorChars = some (1349163527900324 : Int) := by decide +kernel

theorem geometryRow055_floor_parse :
    parseInteger geometryRow055_floorText = .ok geometryRowsTyped055.jensenFloorQ96 := by
  simp only [geometryRow055_floorText, parseInteger, String.toList_ofList, geometryRow055_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_055 :
    decodeGeometryRow geometryRowsJson055 = .ok geometryRowsTyped055 :=
  original_geometryRow_of_fields geometryRowsJson055 geometryRowsTyped055 geometryRow055_floorText
    geometryRow055_simplexId_read geometryRow055_vertexIds_read
    geometryRow055_physicalVolume_read geometryRow055_meanGap_read
    geometryRow055_factorMaxima_read geometryRow055_gapWeightedMeans_read
    geometryRow055_jensenBound_read geometryRow055_floor_text_read geometryRow055_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_055_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson056 : SourceJson :=
  (SimplicesBlock028.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped056 : GeometryRow :=
  { simplexId := 56,
    vertexIds := #[39, 35, 24, 22, 19, 7, 6, 2, 0],
    physicalVolume := ((1636546390516636403564706970205213318572307 : ℚ) / (1590476745424896000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((34630061 : ℚ) / (49039200000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((15252590926886987273 : ℚ) / (192061781312100000000 : ℚ)), ((54116676179138566039 : ℚ) / (672216234592350000000 : ℚ)), ((386683729220617659283 : ℚ) / (2688864938369400000000 : ℚ)), ((13839519515719985203 : ℚ) / (126040543986065625000 : ℚ)), ((79776873875695023143 : ℚ) / (1344432469184700000000 : ℚ)), ((130638679118402737763 : ℚ) / (2688864938369400000000 : ℚ)), ((54312495400564375703 : ℚ) / (1344432469184700000000 : ℚ)), ((52876615578287114293 : ℚ) / (1344432469184700000000 : ℚ)), ((17625508649818611771 : ℚ) / (448144156394900000000 : ℚ)), ((291920662286222795261 : ℚ) / (8066594815108200000000 : ℚ))],
    jensenBound := ((34528265962580721098186766957397976674583107487249866090413321405017223901323362292420626740067655796696656306822013653456666641108556390892410978265314573088210338592529296875000000 : ℚ) / (7818997814231215081653727481216942480699314060345390124848332468372857984895991445259112516828221002842224212074531380562435757518056854735693387405043395531671524242910443565313851477073060960129 : ℚ)),
    jensenFloorQ96 := (349867224932593 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_simplexId_before"
  err.flush

theorem geometryRow056_simplexId_read :
    geometryRowsJson056.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped056.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_vertexIds_before"
  err.flush

theorem geometryRow056_vertexIds_read :
    geometryRowsJson056.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped056.vertexIds := by decide +kernel

noncomputable def geometryRow056_physicalVolumeNumeratorChars : List Char := ['1', '6', '3', '6', '5', '4', '6', '3', '9', '0', '5', '1', '6', '6', '3', '6', '4', '0', '3', '5', '6', '4', '7', '0', '6', '9', '7', '0', '2', '0', '5', '2', '1', '3', '3', '1', '8', '5', '7', '2', '3', '0', '7']
noncomputable def geometryRow056_physicalVolumeDenominatorChars : List Char := ['1', '5', '9', '0', '4', '7', '6', '7', '4', '5', '4', '2', '4', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow056_physicalVolumeText : String := String.ofList (geometryRow056_physicalVolumeNumeratorChars ++ '/' :: geometryRow056_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_physicalVolume_before_field"
  err.flush

theorem geometryRow056_physicalVolume_field :
    geometryRowsJson056.getObjVal? "physical_volume" = .ok (.str geometryRow056_physicalVolumeText) := by rfl

theorem geometryRow056_physicalVolume_numerator_no_slash :
    geometryRow056_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow056_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow056_physicalVolumeNumeratorChars = some (1636546390516636403564706970205213318572307 : Int) := by decide +kernel

theorem geometryRow056_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow056_physicalVolumeDenominatorChars = some (1590476745424896000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow056_physicalVolume_denominator_nonzero : (1590476745424896000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow056_physicalVolume_parse :
    parseRational geometryRow056_physicalVolumeText = .ok geometryRowsTyped056.physicalVolume :=
  original_rational_fraction_of_chars geometryRow056_physicalVolumeNumeratorChars geometryRow056_physicalVolumeDenominatorChars
    (1636546390516636403564706970205213318572307 : Int) (1590476745424896000000000000000000000000000000000000000000000000000 : Int)
    geometryRow056_physicalVolume_numerator_no_slash geometryRow056_physicalVolume_numerator_parse
    geometryRow056_physicalVolume_denominator_parse geometryRow056_physicalVolume_denominator_nonzero

theorem geometryRow056_physicalVolume_read :
    rationalField geometryRowsJson056 "physical_volume" = .ok geometryRowsTyped056.physicalVolume :=
  original_rationalField_of_string geometryRowsJson056 "physical_volume" geometryRow056_physicalVolumeText
    geometryRowsTyped056.physicalVolume geometryRow056_physicalVolume_field geometryRow056_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_physicalVolume_complete"
  err.flush

noncomputable def geometryRow056_meanGapNumeratorChars : List Char := ['3', '4', '6', '3', '0', '0', '6', '1']
noncomputable def geometryRow056_meanGapDenominatorChars : List Char := ['4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0']
noncomputable def geometryRow056_meanGapText : String := String.ofList (geometryRow056_meanGapNumeratorChars ++ '/' :: geometryRow056_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_meanGap_before_field"
  err.flush

theorem geometryRow056_meanGap_field :
    geometryRowsJson056.getObjVal? "mean_gap" = .ok (.str geometryRow056_meanGapText) := by rfl

theorem geometryRow056_meanGap_numerator_no_slash :
    geometryRow056_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow056_meanGap_numerator_parse :
    SourceJson.intChars geometryRow056_meanGapNumeratorChars = some (34630061 : Int) := by decide +kernel

theorem geometryRow056_meanGap_denominator_parse :
    SourceJson.intChars geometryRow056_meanGapDenominatorChars = some (49039200000 : Int) := by decide +kernel

theorem geometryRow056_meanGap_denominator_nonzero : (49039200000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow056_meanGap_parse :
    parseRational geometryRow056_meanGapText = .ok geometryRowsTyped056.meanGap :=
  original_rational_fraction_of_chars geometryRow056_meanGapNumeratorChars geometryRow056_meanGapDenominatorChars
    (34630061 : Int) (49039200000 : Int)
    geometryRow056_meanGap_numerator_no_slash geometryRow056_meanGap_numerator_parse
    geometryRow056_meanGap_denominator_parse geometryRow056_meanGap_denominator_nonzero

theorem geometryRow056_meanGap_read :
    rationalField geometryRowsJson056 "mean_gap" = .ok geometryRowsTyped056.meanGap :=
  original_rationalField_of_string geometryRowsJson056 "mean_gap" geometryRow056_meanGapText
    geometryRowsTyped056.meanGap geometryRow056_meanGap_field geometryRow056_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_meanGap_complete"
  err.flush

noncomputable def geometryRow056_jensenBoundNumeratorChars : List Char := ['3', '4', '5', '2', '8', '2', '6', '5', '9', '6', '2', '5', '8', '0', '7', '2', '1', '0', '9', '8', '1', '8', '6', '7', '6', '6', '9', '5', '7', '3', '9', '7', '9', '7', '6', '6', '7', '4', '5', '8', '3', '1', '0', '7', '4', '8', '7', '2', '4', '9', '8', '6', '6', '0', '9', '0', '4', '1', '3', '3', '2', '1', '4', '0', '5', '0', '1', '7', '2', '2', '3', '9', '0', '1', '3', '2', '3', '3', '6', '2', '2', '9', '2', '4', '2', '0', '6', '2', '6', '7', '4', '0', '0', '6', '7', '6', '5', '5', '7', '9', '6', '6', '9', '6', '6', '5', '6', '3', '0', '6', '8', '2', '2', '0', '1', '3', '6', '5', '3', '4', '5', '6', '6', '6', '6', '6', '4', '1', '1', '0', '8', '5', '5', '6', '3', '9', '0', '8', '9', '2', '4', '1', '0', '9', '7', '8', '2', '6', '5', '3', '1', '4', '5', '7', '3', '0', '8', '8', '2', '1', '0', '3', '3', '8', '5', '9', '2', '5', '2', '9', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow056_jensenBoundDenominatorChars : List Char := ['7', '8', '1', '8', '9', '9', '7', '8', '1', '4', '2', '3', '1', '2', '1', '5', '0', '8', '1', '6', '5', '3', '7', '2', '7', '4', '8', '1', '2', '1', '6', '9', '4', '2', '4', '8', '0', '6', '9', '9', '3', '1', '4', '0', '6', '0', '3', '4', '5', '3', '9', '0', '1', '2', '4', '8', '4', '8', '3', '3', '2', '4', '6', '8', '3', '7', '2', '8', '5', '7', '9', '8', '4', '8', '9', '5', '9', '9', '1', '4', '4', '5', '2', '5', '9', '1', '1', '2', '5', '1', '6', '8', '2', '8', '2', '2', '1', '0', '0', '2', '8', '4', '2', '2', '2', '4', '2', '1', '2', '0', '7', '4', '5', '3', '1', '3', '8', '0', '5', '6', '2', '4', '3', '5', '7', '5', '7', '5', '1', '8', '0', '5', '6', '8', '5', '4', '7', '3', '5', '6', '9', '3', '3', '8', '7', '4', '0', '5', '0', '4', '3', '3', '9', '5', '5', '3', '1', '6', '7', '1', '5', '2', '4', '2', '4', '2', '9', '1', '0', '4', '4', '3', '5', '6', '5', '3', '1', '3', '8', '5', '1', '4', '7', '7', '0', '7', '3', '0', '6', '0', '9', '6', '0', '1', '2', '9']
noncomputable def geometryRow056_jensenBoundText : String := String.ofList (geometryRow056_jensenBoundNumeratorChars ++ '/' :: geometryRow056_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_jensenBound_before_field"
  err.flush

theorem geometryRow056_jensenBound_field :
    geometryRowsJson056.getObjVal? "jensen_bound" = .ok (.str geometryRow056_jensenBoundText) := by rfl

theorem geometryRow056_jensenBound_numerator_no_slash :
    geometryRow056_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow056_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow056_jensenBoundNumeratorChars = some (34528265962580721098186766957397976674583107487249866090413321405017223901323362292420626740067655796696656306822013653456666641108556390892410978265314573088210338592529296875000000 : Int) := by decide +kernel

theorem geometryRow056_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow056_jensenBoundDenominatorChars = some (7818997814231215081653727481216942480699314060345390124848332468372857984895991445259112516828221002842224212074531380562435757518056854735693387405043395531671524242910443565313851477073060960129 : Int) := by decide +kernel

theorem geometryRow056_jensenBound_denominator_nonzero : (7818997814231215081653727481216942480699314060345390124848332468372857984895991445259112516828221002842224212074531380562435757518056854735693387405043395531671524242910443565313851477073060960129 : Int) ≠ 0 := by decide +kernel

theorem geometryRow056_jensenBound_parse :
    parseRational geometryRow056_jensenBoundText = .ok geometryRowsTyped056.jensenBound :=
  original_rational_fraction_of_chars geometryRow056_jensenBoundNumeratorChars geometryRow056_jensenBoundDenominatorChars
    (34528265962580721098186766957397976674583107487249866090413321405017223901323362292420626740067655796696656306822013653456666641108556390892410978265314573088210338592529296875000000 : Int) (7818997814231215081653727481216942480699314060345390124848332468372857984895991445259112516828221002842224212074531380562435757518056854735693387405043395531671524242910443565313851477073060960129 : Int)
    geometryRow056_jensenBound_numerator_no_slash geometryRow056_jensenBound_numerator_parse
    geometryRow056_jensenBound_denominator_parse geometryRow056_jensenBound_denominator_nonzero

theorem geometryRow056_jensenBound_read :
    rationalField geometryRowsJson056 "jensen_bound" = .ok geometryRowsTyped056.jensenBound :=
  original_rationalField_of_string geometryRowsJson056 "jensen_bound" geometryRow056_jensenBoundText
    geometryRowsTyped056.jensenBound geometryRow056_jensenBound_field geometryRow056_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_factorMaxima_before"
  err.flush

theorem geometryRow056_factorMaxima_read :
    rationalArrayField geometryRowsJson056 "factor_maxima" = .ok geometryRowsTyped056.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_gapWeightedMeans_before"
  err.flush

theorem geometryRow056_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson056 "gap_weighted_means" = .ok geometryRowsTyped056.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow056_floorChars : List Char := ['3', '4', '9', '8', '6', '7', '2', '2', '4', '9', '3', '2', '5', '9', '3']
noncomputable def geometryRow056_floorText : String := String.ofList geometryRow056_floorChars

theorem geometryRow056_floor_text_read :
    geometryRowsJson056.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow056_floorText := by rfl

theorem geometryRow056_floor_chars_parse :
    SourceJson.intChars geometryRow056_floorChars = some (349867224932593 : Int) := by decide +kernel

theorem geometryRow056_floor_parse :
    parseInteger geometryRow056_floorText = .ok geometryRowsTyped056.jensenFloorQ96 := by
  simp only [geometryRow056_floorText, parseInteger, String.toList_ofList, geometryRow056_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_056 :
    decodeGeometryRow geometryRowsJson056 = .ok geometryRowsTyped056 :=
  original_geometryRow_of_fields geometryRowsJson056 geometryRowsTyped056 geometryRow056_floorText
    geometryRow056_simplexId_read geometryRow056_vertexIds_read
    geometryRow056_physicalVolume_read geometryRow056_meanGap_read
    geometryRow056_factorMaxima_read geometryRow056_gapWeightedMeans_read
    geometryRow056_jensenBound_read geometryRow056_floor_text_read geometryRow056_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_056_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock028 : List SourceJson := [geometryRowsJson055, geometryRowsJson056]
noncomputable def geometryRowsTypedBlock028 : List (GeometryRow) := [geometryRowsTyped055, geometryRowsTyped056]
noncomputable def geometryRowsTypedThroughBlock028 : List (GeometryRow) := geometryRowsTypedThroughBlock027 ++ geometryRowsTypedBlock028

theorem geometry_Rows_block_028_push_eq (acc : List SourceJson) :
    SimplicesBlock028.blockPush acc = [geometryRowsJson056, geometryRowsJson055] ++ acc := by rfl

theorem geometry_Rows_block_028_reverse (acc : List SourceJson) :
    (SimplicesBlock028.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock028 := by
  rw [geometry_Rows_block_028_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_028 :
    geometryRowsJsonBlock028.mapM decodeGeometryRow = .ok geometryRowsTypedBlock028 := by
  simp only [geometryRowsJsonBlock028, geometryRowsTypedBlock028, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_055, decode_geometry_Rows_056]
  rfl

theorem decode_geometry_Rows_through_block_028 :
    SimplicesValue.arrayAcc029.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock028 := by
  change (SimplicesBlock028.blockPush SimplicesValue.arrayAcc028).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_028_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_027, decode_geometry_Rows_block_028]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_028_complete"
  err.flush

#print axioms geometryRow055_simplexId_read
#print axioms geometryRow055_vertexIds_read
#print axioms geometryRow055_physicalVolume_field
#print axioms geometryRow055_physicalVolume_numerator_no_slash
#print axioms geometryRow055_physicalVolume_numerator_parse
#print axioms geometryRow055_physicalVolume_denominator_parse
#print axioms geometryRow055_physicalVolume_denominator_nonzero
#print axioms geometryRow055_physicalVolume_parse
#print axioms geometryRow055_physicalVolume_read
#print axioms geometryRow055_meanGap_field
#print axioms geometryRow055_meanGap_numerator_no_slash
#print axioms geometryRow055_meanGap_numerator_parse
#print axioms geometryRow055_meanGap_denominator_parse
#print axioms geometryRow055_meanGap_denominator_nonzero
#print axioms geometryRow055_meanGap_parse
#print axioms geometryRow055_meanGap_read
#print axioms geometryRow055_jensenBound_field
#print axioms geometryRow055_jensenBound_numerator_no_slash
#print axioms geometryRow055_jensenBound_numerator_parse
#print axioms geometryRow055_jensenBound_denominator_parse
#print axioms geometryRow055_jensenBound_denominator_nonzero
#print axioms geometryRow055_jensenBound_parse
#print axioms geometryRow055_jensenBound_read
#print axioms geometryRow055_factorMaxima_read
#print axioms geometryRow055_gapWeightedMeans_read
#print axioms geometryRow055_floor_text_read
#print axioms geometryRow055_floor_chars_parse
#print axioms geometryRow055_floor_parse
#print axioms decode_geometry_Rows_055
#print axioms geometryRow056_simplexId_read
#print axioms geometryRow056_vertexIds_read
#print axioms geometryRow056_physicalVolume_field
#print axioms geometryRow056_physicalVolume_numerator_no_slash
#print axioms geometryRow056_physicalVolume_numerator_parse
#print axioms geometryRow056_physicalVolume_denominator_parse
#print axioms geometryRow056_physicalVolume_denominator_nonzero
#print axioms geometryRow056_physicalVolume_parse
#print axioms geometryRow056_physicalVolume_read
#print axioms geometryRow056_meanGap_field
#print axioms geometryRow056_meanGap_numerator_no_slash
#print axioms geometryRow056_meanGap_numerator_parse
#print axioms geometryRow056_meanGap_denominator_parse
#print axioms geometryRow056_meanGap_denominator_nonzero
#print axioms geometryRow056_meanGap_parse
#print axioms geometryRow056_meanGap_read
#print axioms geometryRow056_jensenBound_field
#print axioms geometryRow056_jensenBound_numerator_no_slash
#print axioms geometryRow056_jensenBound_numerator_parse
#print axioms geometryRow056_jensenBound_denominator_parse
#print axioms geometryRow056_jensenBound_denominator_nonzero
#print axioms geometryRow056_jensenBound_parse
#print axioms geometryRow056_jensenBound_read
#print axioms geometryRow056_factorMaxima_read
#print axioms geometryRow056_gapWeightedMeans_read
#print axioms geometryRow056_floor_text_read
#print axioms geometryRow056_floor_chars_parse
#print axioms geometryRow056_floor_parse
#print axioms decode_geometry_Rows_056
#print axioms geometry_Rows_block_028_push_eq
#print axioms geometry_Rows_block_028_reverse
#print axioms decode_geometry_Rows_block_028
#print axioms decode_geometry_Rows_through_block_028

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
