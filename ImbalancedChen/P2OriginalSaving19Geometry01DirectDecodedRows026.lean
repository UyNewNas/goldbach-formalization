import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows025

/-! Original simplices typed block 26, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson051 : SourceJson :=
  (SimplicesBlock026.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped051 : GeometryRow :=
  { simplexId := 51,
    vertexIds := #[39, 35, 24, 23, 19, 7, 6, 2, 0],
    physicalVolume := ((7970360484970224592044199078065919286312690149 : ℚ) / (1934019722436673536000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((34630061 : ℚ) / (49039200000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((5084194504658709871 : ℚ) / (64020593770700000000 : ℚ)), ((18038883411316854743 : ℚ) / (224072078197450000000 : ℚ)), ((386683785828300572323 : ℚ) / (2688864938369400000000 : ℚ)), ((27679028417499424211 : ℚ) / (252081087972131250000 : ℚ)), ((79776845571853566623 : ℚ) / (1344432469184700000000 : ℚ)), ((130638622510719824723 : ℚ) / (2688864938369400000000 : ℚ)), ((5679318467894216879 : ℚ) / (141519207282600000000 : ℚ)), ((106471284283078685371 : ℚ) / (2688864938369400000000 : ℚ)), ((52876521232148925893 : ℚ) / (1344432469184700000000 : ℚ)), ((291921171755369012621 : ℚ) / (8066594815108200000000 : ℚ))],
    jensenBound := ((3064598763601409532835257796737709390443780794221351909608787188040100728456751078589410796830796530313762308547543664237967941500127162161057520086837397639785720348358154296875000000 : ℚ) / (173297640341337198503072632495033820670456548299293574355524950575156682977258818068127355914193236808978029579389510633848367915821566777851862265752456461471410410522179893056014582753798681847 : ℚ)),
    jensenFloorQ96 := (1401072330848752047 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_simplexId_before"
  err.flush

theorem geometryRow051_simplexId_read :
    geometryRowsJson051.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped051.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_vertexIds_before"
  err.flush

theorem geometryRow051_vertexIds_read :
    geometryRowsJson051.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped051.vertexIds := by decide +kernel

noncomputable def geometryRow051_physicalVolumeNumeratorChars : List Char := ['7', '9', '7', '0', '3', '6', '0', '4', '8', '4', '9', '7', '0', '2', '2', '4', '5', '9', '2', '0', '4', '4', '1', '9', '9', '0', '7', '8', '0', '6', '5', '9', '1', '9', '2', '8', '6', '3', '1', '2', '6', '9', '0', '1', '4', '9']
noncomputable def geometryRow051_physicalVolumeDenominatorChars : List Char := ['1', '9', '3', '4', '0', '1', '9', '7', '2', '2', '4', '3', '6', '6', '7', '3', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_physicalVolumeText : String := String.ofList (geometryRow051_physicalVolumeNumeratorChars ++ '/' :: geometryRow051_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_physicalVolume_before_field"
  err.flush

theorem geometryRow051_physicalVolume_field :
    geometryRowsJson051.getObjVal? "physical_volume" = .ok (.str geometryRow051_physicalVolumeText) := by rfl

theorem geometryRow051_physicalVolume_numerator_no_slash :
    geometryRow051_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeNumeratorChars = some (7970360484970224592044199078065919286312690149 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeDenominatorChars = some (1934019722436673536000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_nonzero : (1934019722436673536000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_physicalVolume_parse :
    parseRational geometryRow051_physicalVolumeText = .ok geometryRowsTyped051.physicalVolume :=
  original_rational_fraction_of_chars geometryRow051_physicalVolumeNumeratorChars geometryRow051_physicalVolumeDenominatorChars
    (7970360484970224592044199078065919286312690149 : Int) (1934019722436673536000000000000000000000000000000000000000000000000 : Int)
    geometryRow051_physicalVolume_numerator_no_slash geometryRow051_physicalVolume_numerator_parse
    geometryRow051_physicalVolume_denominator_parse geometryRow051_physicalVolume_denominator_nonzero

theorem geometryRow051_physicalVolume_read :
    rationalField geometryRowsJson051 "physical_volume" = .ok geometryRowsTyped051.physicalVolume :=
  original_rationalField_of_string geometryRowsJson051 "physical_volume" geometryRow051_physicalVolumeText
    geometryRowsTyped051.physicalVolume geometryRow051_physicalVolume_field geometryRow051_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_physicalVolume_complete"
  err.flush

noncomputable def geometryRow051_meanGapNumeratorChars : List Char := ['3', '4', '6', '3', '0', '0', '6', '1']
noncomputable def geometryRow051_meanGapDenominatorChars : List Char := ['4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_meanGapText : String := String.ofList (geometryRow051_meanGapNumeratorChars ++ '/' :: geometryRow051_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_meanGap_before_field"
  err.flush

theorem geometryRow051_meanGap_field :
    geometryRowsJson051.getObjVal? "mean_gap" = .ok (.str geometryRow051_meanGapText) := by rfl

theorem geometryRow051_meanGap_numerator_no_slash :
    geometryRow051_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_meanGap_numerator_parse :
    SourceJson.intChars geometryRow051_meanGapNumeratorChars = some (34630061 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_parse :
    SourceJson.intChars geometryRow051_meanGapDenominatorChars = some (49039200000 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_nonzero : (49039200000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_meanGap_parse :
    parseRational geometryRow051_meanGapText = .ok geometryRowsTyped051.meanGap :=
  original_rational_fraction_of_chars geometryRow051_meanGapNumeratorChars geometryRow051_meanGapDenominatorChars
    (34630061 : Int) (49039200000 : Int)
    geometryRow051_meanGap_numerator_no_slash geometryRow051_meanGap_numerator_parse
    geometryRow051_meanGap_denominator_parse geometryRow051_meanGap_denominator_nonzero

theorem geometryRow051_meanGap_read :
    rationalField geometryRowsJson051 "mean_gap" = .ok geometryRowsTyped051.meanGap :=
  original_rationalField_of_string geometryRowsJson051 "mean_gap" geometryRow051_meanGapText
    geometryRowsTyped051.meanGap geometryRow051_meanGap_field geometryRow051_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_meanGap_complete"
  err.flush

noncomputable def geometryRow051_jensenBoundNumeratorChars : List Char := ['3', '0', '6', '4', '5', '9', '8', '7', '6', '3', '6', '0', '1', '4', '0', '9', '5', '3', '2', '8', '3', '5', '2', '5', '7', '7', '9', '6', '7', '3', '7', '7', '0', '9', '3', '9', '0', '4', '4', '3', '7', '8', '0', '7', '9', '4', '2', '2', '1', '3', '5', '1', '9', '0', '9', '6', '0', '8', '7', '8', '7', '1', '8', '8', '0', '4', '0', '1', '0', '0', '7', '2', '8', '4', '5', '6', '7', '5', '1', '0', '7', '8', '5', '8', '9', '4', '1', '0', '7', '9', '6', '8', '3', '0', '7', '9', '6', '5', '3', '0', '3', '1', '3', '7', '6', '2', '3', '0', '8', '5', '4', '7', '5', '4', '3', '6', '6', '4', '2', '3', '7', '9', '6', '7', '9', '4', '1', '5', '0', '0', '1', '2', '7', '1', '6', '2', '1', '6', '1', '0', '5', '7', '5', '2', '0', '0', '8', '6', '8', '3', '7', '3', '9', '7', '6', '3', '9', '7', '8', '5', '7', '2', '0', '3', '4', '8', '3', '5', '8', '1', '5', '4', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_jensenBoundDenominatorChars : List Char := ['1', '7', '3', '2', '9', '7', '6', '4', '0', '3', '4', '1', '3', '3', '7', '1', '9', '8', '5', '0', '3', '0', '7', '2', '6', '3', '2', '4', '9', '5', '0', '3', '3', '8', '2', '0', '6', '7', '0', '4', '5', '6', '5', '4', '8', '2', '9', '9', '2', '9', '3', '5', '7', '4', '3', '5', '5', '5', '2', '4', '9', '5', '0', '5', '7', '5', '1', '5', '6', '6', '8', '2', '9', '7', '7', '2', '5', '8', '8', '1', '8', '0', '6', '8', '1', '2', '7', '3', '5', '5', '9', '1', '4', '1', '9', '3', '2', '3', '6', '8', '0', '8', '9', '7', '8', '0', '2', '9', '5', '7', '9', '3', '8', '9', '5', '1', '0', '6', '3', '3', '8', '4', '8', '3', '6', '7', '9', '1', '5', '8', '2', '1', '5', '6', '6', '7', '7', '7', '8', '5', '1', '8', '6', '2', '2', '6', '5', '7', '5', '2', '4', '5', '6', '4', '6', '1', '4', '7', '1', '4', '1', '0', '4', '1', '0', '5', '2', '2', '1', '7', '9', '8', '9', '3', '0', '5', '6', '0', '1', '4', '5', '8', '2', '7', '5', '3', '7', '9', '8', '6', '8', '1', '8', '4', '7']
noncomputable def geometryRow051_jensenBoundText : String := String.ofList (geometryRow051_jensenBoundNumeratorChars ++ '/' :: geometryRow051_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_jensenBound_before_field"
  err.flush

theorem geometryRow051_jensenBound_field :
    geometryRowsJson051.getObjVal? "jensen_bound" = .ok (.str geometryRow051_jensenBoundText) := by rfl

theorem geometryRow051_jensenBound_numerator_no_slash :
    geometryRow051_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow051_jensenBoundNumeratorChars = some (3064598763601409532835257796737709390443780794221351909608787188040100728456751078589410796830796530313762308547543664237967941500127162161057520086837397639785720348358154296875000000 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow051_jensenBoundDenominatorChars = some (173297640341337198503072632495033820670456548299293574355524950575156682977258818068127355914193236808978029579389510633848367915821566777851862265752456461471410410522179893056014582753798681847 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_nonzero : (173297640341337198503072632495033820670456548299293574355524950575156682977258818068127355914193236808978029579389510633848367915821566777851862265752456461471410410522179893056014582753798681847 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_jensenBound_parse :
    parseRational geometryRow051_jensenBoundText = .ok geometryRowsTyped051.jensenBound :=
  original_rational_fraction_of_chars geometryRow051_jensenBoundNumeratorChars geometryRow051_jensenBoundDenominatorChars
    (3064598763601409532835257796737709390443780794221351909608787188040100728456751078589410796830796530313762308547543664237967941500127162161057520086837397639785720348358154296875000000 : Int) (173297640341337198503072632495033820670456548299293574355524950575156682977258818068127355914193236808978029579389510633848367915821566777851862265752456461471410410522179893056014582753798681847 : Int)
    geometryRow051_jensenBound_numerator_no_slash geometryRow051_jensenBound_numerator_parse
    geometryRow051_jensenBound_denominator_parse geometryRow051_jensenBound_denominator_nonzero

theorem geometryRow051_jensenBound_read :
    rationalField geometryRowsJson051 "jensen_bound" = .ok geometryRowsTyped051.jensenBound :=
  original_rationalField_of_string geometryRowsJson051 "jensen_bound" geometryRow051_jensenBoundText
    geometryRowsTyped051.jensenBound geometryRow051_jensenBound_field geometryRow051_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_factorMaxima_before"
  err.flush

theorem geometryRow051_factorMaxima_read :
    rationalArrayField geometryRowsJson051 "factor_maxima" = .ok geometryRowsTyped051.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_gapWeightedMeans_before"
  err.flush

theorem geometryRow051_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson051 "gap_weighted_means" = .ok geometryRowsTyped051.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow051_floorChars : List Char := ['1', '4', '0', '1', '0', '7', '2', '3', '3', '0', '8', '4', '8', '7', '5', '2', '0', '4', '7']
noncomputable def geometryRow051_floorText : String := String.ofList geometryRow051_floorChars

theorem geometryRow051_floor_text_read :
    geometryRowsJson051.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow051_floorText := by rfl

theorem geometryRow051_floor_chars_parse :
    SourceJson.intChars geometryRow051_floorChars = some (1401072330848752047 : Int) := by decide +kernel

theorem geometryRow051_floor_parse :
    parseInteger geometryRow051_floorText = .ok geometryRowsTyped051.jensenFloorQ96 := by
  simp only [geometryRow051_floorText, parseInteger, String.toList_ofList, geometryRow051_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_051 :
    decodeGeometryRow geometryRowsJson051 = .ok geometryRowsTyped051 :=
  original_geometryRow_of_fields geometryRowsJson051 geometryRowsTyped051 geometryRow051_floorText
    geometryRow051_simplexId_read geometryRow051_vertexIds_read
    geometryRow051_physicalVolume_read geometryRow051_meanGap_read
    geometryRow051_factorMaxima_read geometryRow051_gapWeightedMeans_read
    geometryRow051_jensenBound_read geometryRow051_floor_text_read geometryRow051_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_051_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson052 : SourceJson :=
  (SimplicesBlock026.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped052 : GeometryRow :=
  { simplexId := 52,
    vertexIds := #[39, 35, 24, 23, 19, 18, 7, 6, 0],
    physicalVolume := ((2088047418529133930873834120046777032286031339 : ℚ) / (2743150422639771648000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((556035964779 : ℚ) / (7394800000000 : ℚ)), ((557655423319 : ℚ) / (7394800000000 : ℚ)), ((645383555423 : ℚ) / (4436880000000 : ℚ)), ((3577835535233 : ℚ) / (33276600000000 : ℚ)), ((1268538321943 : ℚ) / (22184400000000 : ℚ)), ((1075015080389 : ℚ) / (22184400000000 : ℚ)), ((49079399819 : ℚ) / (1167600000000 : ℚ)), ((920662846981 : ℚ) / (22184400000000 : ℚ)), ((914737014271 : ℚ) / (22184400000000 : ℚ)), ((2554365620999 : ℚ) / (66553200000000 : ℚ))],
    jensenBound := ((18763922852602015757423559849597160946910796751995080168624508886652186856248202060000000000000000000000000 : ℚ) / (34362373120097164005667743923315958675608675943965720990476785027277902073630671298418060564773054281867343324836086861 : ℚ)),
    jensenFloorQ96 := (43263342842337058 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_simplexId_before"
  err.flush

theorem geometryRow052_simplexId_read :
    geometryRowsJson052.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped052.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_vertexIds_before"
  err.flush

theorem geometryRow052_vertexIds_read :
    geometryRowsJson052.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped052.vertexIds := by decide +kernel

noncomputable def geometryRow052_physicalVolumeNumeratorChars : List Char := ['2', '0', '8', '8', '0', '4', '7', '4', '1', '8', '5', '2', '9', '1', '3', '3', '9', '3', '0', '8', '7', '3', '8', '3', '4', '1', '2', '0', '0', '4', '6', '7', '7', '7', '0', '3', '2', '2', '8', '6', '0', '3', '1', '3', '3', '9']
noncomputable def geometryRow052_physicalVolumeDenominatorChars : List Char := ['2', '7', '4', '3', '1', '5', '0', '4', '2', '2', '6', '3', '9', '7', '7', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_physicalVolumeText : String := String.ofList (geometryRow052_physicalVolumeNumeratorChars ++ '/' :: geometryRow052_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_physicalVolume_before_field"
  err.flush

theorem geometryRow052_physicalVolume_field :
    geometryRowsJson052.getObjVal? "physical_volume" = .ok (.str geometryRow052_physicalVolumeText) := by rfl

theorem geometryRow052_physicalVolume_numerator_no_slash :
    geometryRow052_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeNumeratorChars = some (2088047418529133930873834120046777032286031339 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeDenominatorChars = some (2743150422639771648000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_nonzero : (2743150422639771648000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_physicalVolume_parse :
    parseRational geometryRow052_physicalVolumeText = .ok geometryRowsTyped052.physicalVolume :=
  original_rational_fraction_of_chars geometryRow052_physicalVolumeNumeratorChars geometryRow052_physicalVolumeDenominatorChars
    (2088047418529133930873834120046777032286031339 : Int) (2743150422639771648000000000000000000000000000000000000000000000000 : Int)
    geometryRow052_physicalVolume_numerator_no_slash geometryRow052_physicalVolume_numerator_parse
    geometryRow052_physicalVolume_denominator_parse geometryRow052_physicalVolume_denominator_nonzero

theorem geometryRow052_physicalVolume_read :
    rationalField geometryRowsJson052 "physical_volume" = .ok geometryRowsTyped052.physicalVolume :=
  original_rationalField_of_string geometryRowsJson052 "physical_volume" geometryRow052_physicalVolumeText
    geometryRowsTyped052.physicalVolume geometryRow052_physicalVolume_field geometryRow052_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_physicalVolume_complete"
  err.flush

noncomputable def geometryRow052_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow052_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_meanGapText : String := String.ofList (geometryRow052_meanGapNumeratorChars ++ '/' :: geometryRow052_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_meanGap_before_field"
  err.flush

theorem geometryRow052_meanGap_field :
    geometryRowsJson052.getObjVal? "mean_gap" = .ok (.str geometryRow052_meanGapText) := by rfl

theorem geometryRow052_meanGap_numerator_no_slash :
    geometryRow052_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_meanGap_numerator_parse :
    SourceJson.intChars geometryRow052_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_parse :
    SourceJson.intChars geometryRow052_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_meanGap_parse :
    parseRational geometryRow052_meanGapText = .ok geometryRowsTyped052.meanGap :=
  original_rational_fraction_of_chars geometryRow052_meanGapNumeratorChars geometryRow052_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow052_meanGap_numerator_no_slash geometryRow052_meanGap_numerator_parse
    geometryRow052_meanGap_denominator_parse geometryRow052_meanGap_denominator_nonzero

theorem geometryRow052_meanGap_read :
    rationalField geometryRowsJson052 "mean_gap" = .ok geometryRowsTyped052.meanGap :=
  original_rationalField_of_string geometryRowsJson052 "mean_gap" geometryRow052_meanGapText
    geometryRowsTyped052.meanGap geometryRow052_meanGap_field geometryRow052_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_meanGap_complete"
  err.flush

noncomputable def geometryRow052_jensenBoundNumeratorChars : List Char := ['1', '8', '7', '6', '3', '9', '2', '2', '8', '5', '2', '6', '0', '2', '0', '1', '5', '7', '5', '7', '4', '2', '3', '5', '5', '9', '8', '4', '9', '5', '9', '7', '1', '6', '0', '9', '4', '6', '9', '1', '0', '7', '9', '6', '7', '5', '1', '9', '9', '5', '0', '8', '0', '1', '6', '8', '6', '2', '4', '5', '0', '8', '8', '8', '6', '6', '5', '2', '1', '8', '6', '8', '5', '6', '2', '4', '8', '2', '0', '2', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_jensenBoundDenominatorChars : List Char := ['3', '4', '3', '6', '2', '3', '7', '3', '1', '2', '0', '0', '9', '7', '1', '6', '4', '0', '0', '5', '6', '6', '7', '7', '4', '3', '9', '2', '3', '3', '1', '5', '9', '5', '8', '6', '7', '5', '6', '0', '8', '6', '7', '5', '9', '4', '3', '9', '6', '5', '7', '2', '0', '9', '9', '0', '4', '7', '6', '7', '8', '5', '0', '2', '7', '2', '7', '7', '9', '0', '2', '0', '7', '3', '6', '3', '0', '6', '7', '1', '2', '9', '8', '4', '1', '8', '0', '6', '0', '5', '6', '4', '7', '7', '3', '0', '5', '4', '2', '8', '1', '8', '6', '7', '3', '4', '3', '3', '2', '4', '8', '3', '6', '0', '8', '6', '8', '6', '1']
noncomputable def geometryRow052_jensenBoundText : String := String.ofList (geometryRow052_jensenBoundNumeratorChars ++ '/' :: geometryRow052_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_jensenBound_before_field"
  err.flush

theorem geometryRow052_jensenBound_field :
    geometryRowsJson052.getObjVal? "jensen_bound" = .ok (.str geometryRow052_jensenBoundText) := by rfl

theorem geometryRow052_jensenBound_numerator_no_slash :
    geometryRow052_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow052_jensenBoundNumeratorChars = some (18763922852602015757423559849597160946910796751995080168624508886652186856248202060000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow052_jensenBoundDenominatorChars = some (34362373120097164005667743923315958675608675943965720990476785027277902073630671298418060564773054281867343324836086861 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_nonzero : (34362373120097164005667743923315958675608675943965720990476785027277902073630671298418060564773054281867343324836086861 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_jensenBound_parse :
    parseRational geometryRow052_jensenBoundText = .ok geometryRowsTyped052.jensenBound :=
  original_rational_fraction_of_chars geometryRow052_jensenBoundNumeratorChars geometryRow052_jensenBoundDenominatorChars
    (18763922852602015757423559849597160946910796751995080168624508886652186856248202060000000000000000000000000 : Int) (34362373120097164005667743923315958675608675943965720990476785027277902073630671298418060564773054281867343324836086861 : Int)
    geometryRow052_jensenBound_numerator_no_slash geometryRow052_jensenBound_numerator_parse
    geometryRow052_jensenBound_denominator_parse geometryRow052_jensenBound_denominator_nonzero

theorem geometryRow052_jensenBound_read :
    rationalField geometryRowsJson052 "jensen_bound" = .ok geometryRowsTyped052.jensenBound :=
  original_rationalField_of_string geometryRowsJson052 "jensen_bound" geometryRow052_jensenBoundText
    geometryRowsTyped052.jensenBound geometryRow052_jensenBound_field geometryRow052_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_factorMaxima_before"
  err.flush

theorem geometryRow052_factorMaxima_read :
    rationalArrayField geometryRowsJson052 "factor_maxima" = .ok geometryRowsTyped052.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_gapWeightedMeans_before"
  err.flush

theorem geometryRow052_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson052 "gap_weighted_means" = .ok geometryRowsTyped052.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow052_floorChars : List Char := ['4', '3', '2', '6', '3', '3', '4', '2', '8', '4', '2', '3', '3', '7', '0', '5', '8']
noncomputable def geometryRow052_floorText : String := String.ofList geometryRow052_floorChars

theorem geometryRow052_floor_text_read :
    geometryRowsJson052.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow052_floorText := by rfl

theorem geometryRow052_floor_chars_parse :
    SourceJson.intChars geometryRow052_floorChars = some (43263342842337058 : Int) := by decide +kernel

theorem geometryRow052_floor_parse :
    parseInteger geometryRow052_floorText = .ok geometryRowsTyped052.jensenFloorQ96 := by
  simp only [geometryRow052_floorText, parseInteger, String.toList_ofList, geometryRow052_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_052 :
    decodeGeometryRow geometryRowsJson052 = .ok geometryRowsTyped052 :=
  original_geometryRow_of_fields geometryRowsJson052 geometryRowsTyped052 geometryRow052_floorText
    geometryRow052_simplexId_read geometryRow052_vertexIds_read
    geometryRow052_physicalVolume_read geometryRow052_meanGap_read
    geometryRow052_factorMaxima_read geometryRow052_gapWeightedMeans_read
    geometryRow052_jensenBound_read geometryRow052_floor_text_read geometryRow052_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_052_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock026 : List SourceJson := [geometryRowsJson051, geometryRowsJson052]
noncomputable def geometryRowsTypedBlock026 : List (GeometryRow) := [geometryRowsTyped051, geometryRowsTyped052]
noncomputable def geometryRowsTypedThroughBlock026 : List (GeometryRow) := geometryRowsTypedThroughBlock025 ++ geometryRowsTypedBlock026

theorem geometry_Rows_block_026_push_eq (acc : List SourceJson) :
    SimplicesBlock026.blockPush acc = [geometryRowsJson052, geometryRowsJson051] ++ acc := by rfl

theorem geometry_Rows_block_026_reverse (acc : List SourceJson) :
    (SimplicesBlock026.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock026 := by
  rw [geometry_Rows_block_026_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_026 :
    geometryRowsJsonBlock026.mapM decodeGeometryRow = .ok geometryRowsTypedBlock026 := by
  simp only [geometryRowsJsonBlock026, geometryRowsTypedBlock026, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_051, decode_geometry_Rows_052]
  rfl

theorem decode_geometry_Rows_through_block_026 :
    SimplicesValue.arrayAcc027.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock026 := by
  change (SimplicesBlock026.blockPush SimplicesValue.arrayAcc026).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_026_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_025, decode_geometry_Rows_block_026]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_026_complete"
  err.flush

#print axioms geometryRow051_simplexId_read
#print axioms geometryRow051_vertexIds_read
#print axioms geometryRow051_physicalVolume_field
#print axioms geometryRow051_physicalVolume_numerator_no_slash
#print axioms geometryRow051_physicalVolume_numerator_parse
#print axioms geometryRow051_physicalVolume_denominator_parse
#print axioms geometryRow051_physicalVolume_denominator_nonzero
#print axioms geometryRow051_physicalVolume_parse
#print axioms geometryRow051_physicalVolume_read
#print axioms geometryRow051_meanGap_field
#print axioms geometryRow051_meanGap_numerator_no_slash
#print axioms geometryRow051_meanGap_numerator_parse
#print axioms geometryRow051_meanGap_denominator_parse
#print axioms geometryRow051_meanGap_denominator_nonzero
#print axioms geometryRow051_meanGap_parse
#print axioms geometryRow051_meanGap_read
#print axioms geometryRow051_jensenBound_field
#print axioms geometryRow051_jensenBound_numerator_no_slash
#print axioms geometryRow051_jensenBound_numerator_parse
#print axioms geometryRow051_jensenBound_denominator_parse
#print axioms geometryRow051_jensenBound_denominator_nonzero
#print axioms geometryRow051_jensenBound_parse
#print axioms geometryRow051_jensenBound_read
#print axioms geometryRow051_factorMaxima_read
#print axioms geometryRow051_gapWeightedMeans_read
#print axioms geometryRow051_floor_text_read
#print axioms geometryRow051_floor_chars_parse
#print axioms geometryRow051_floor_parse
#print axioms decode_geometry_Rows_051
#print axioms geometryRow052_simplexId_read
#print axioms geometryRow052_vertexIds_read
#print axioms geometryRow052_physicalVolume_field
#print axioms geometryRow052_physicalVolume_numerator_no_slash
#print axioms geometryRow052_physicalVolume_numerator_parse
#print axioms geometryRow052_physicalVolume_denominator_parse
#print axioms geometryRow052_physicalVolume_denominator_nonzero
#print axioms geometryRow052_physicalVolume_parse
#print axioms geometryRow052_physicalVolume_read
#print axioms geometryRow052_meanGap_field
#print axioms geometryRow052_meanGap_numerator_no_slash
#print axioms geometryRow052_meanGap_numerator_parse
#print axioms geometryRow052_meanGap_denominator_parse
#print axioms geometryRow052_meanGap_denominator_nonzero
#print axioms geometryRow052_meanGap_parse
#print axioms geometryRow052_meanGap_read
#print axioms geometryRow052_jensenBound_field
#print axioms geometryRow052_jensenBound_numerator_no_slash
#print axioms geometryRow052_jensenBound_numerator_parse
#print axioms geometryRow052_jensenBound_denominator_parse
#print axioms geometryRow052_jensenBound_denominator_nonzero
#print axioms geometryRow052_jensenBound_parse
#print axioms geometryRow052_jensenBound_read
#print axioms geometryRow052_factorMaxima_read
#print axioms geometryRow052_gapWeightedMeans_read
#print axioms geometryRow052_floor_text_read
#print axioms geometryRow052_floor_chars_parse
#print axioms geometryRow052_floor_parse
#print axioms decode_geometry_Rows_052
#print axioms geometry_Rows_block_026_push_eq
#print axioms geometry_Rows_block_026_reverse
#print axioms decode_geometry_Rows_block_026
#print axioms decode_geometry_Rows_through_block_026

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
