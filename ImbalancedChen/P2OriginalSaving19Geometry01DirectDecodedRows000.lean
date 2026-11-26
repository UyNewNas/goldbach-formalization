import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue

/-! Original simplices typed block 0, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson000 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped000 : GeometryRow :=
  { simplexId := 0,
    vertexIds := #[39, 35, 29, 28, 25, 13, 3, 1, 0],
    physicalVolume := ((1712581660411696500285032755320815818261 : ℚ) / (1056541822156800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2428258549147 : ℚ) / (27988800000000 : ℚ)), ((2456550780667 : ℚ) / (27988800000000 : ℚ)), ((864064571201 : ℚ) / (5997600000000 : ℚ)), ((3208148519801 : ℚ) / (27988800000000 : ℚ)), ((48926117683 : ℚ) / (705600000000 : ℚ)), ((2042051440273 : ℚ) / (41983200000000 : ℚ)), ((1728772558987 : ℚ) / (47980800000000 : ℚ)), ((1629222320017 : ℚ) / (47980800000000 : ℚ)), ((2642396552611 : ℚ) / (83966400000000 : ℚ)), ((2642379759331 : ℚ) / (83966400000000 : ℚ))],
    jensenBound := ((5515207160294537965567950443092912537072504241157128988164573018885558113271808000000000000000000000000 : ℚ) / (778317063272418567639385318796819173497930331158214089130434372626259736947218743557755923197953170333865089230402343 : ℚ)),
    jensenFloorQ96 := (561416098676369 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_simplexId_before"
  err.flush

theorem geometryRow000_simplexId_read :
    geometryRowsJson000.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped000.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_vertexIds_before"
  err.flush

theorem geometryRow000_vertexIds_read :
    geometryRowsJson000.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped000.vertexIds := by decide +kernel

noncomputable def geometryRow000_physicalVolumeNumeratorChars : List Char := ['1', '7', '1', '2', '5', '8', '1', '6', '6', '0', '4', '1', '1', '6', '9', '6', '5', '0', '0', '2', '8', '5', '0', '3', '2', '7', '5', '5', '3', '2', '0', '8', '1', '5', '8', '1', '8', '2', '6', '1']
noncomputable def geometryRow000_physicalVolumeDenominatorChars : List Char := ['1', '0', '5', '6', '5', '4', '1', '8', '2', '2', '1', '5', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_physicalVolumeText : String := String.ofList (geometryRow000_physicalVolumeNumeratorChars ++ '/' :: geometryRow000_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_physicalVolume_before_field"
  err.flush

theorem geometryRow000_physicalVolume_field :
    geometryRowsJson000.getObjVal? "physical_volume" = .ok (.str geometryRow000_physicalVolumeText) := by rfl

theorem geometryRow000_physicalVolume_numerator_no_slash :
    geometryRow000_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeNumeratorChars = some (1712581660411696500285032755320815818261 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeDenominatorChars = some (1056541822156800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_nonzero : (1056541822156800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_physicalVolume_parse :
    parseRational geometryRow000_physicalVolumeText = .ok geometryRowsTyped000.physicalVolume :=
  original_rational_fraction_of_chars geometryRow000_physicalVolumeNumeratorChars geometryRow000_physicalVolumeDenominatorChars
    (1712581660411696500285032755320815818261 : Int) (1056541822156800000000000000000000000000000000000000000000000000 : Int)
    geometryRow000_physicalVolume_numerator_no_slash geometryRow000_physicalVolume_numerator_parse
    geometryRow000_physicalVolume_denominator_parse geometryRow000_physicalVolume_denominator_nonzero

theorem geometryRow000_physicalVolume_read :
    rationalField geometryRowsJson000 "physical_volume" = .ok geometryRowsTyped000.physicalVolume :=
  original_rationalField_of_string geometryRowsJson000 "physical_volume" geometryRow000_physicalVolumeText
    geometryRowsTyped000.physicalVolume geometryRow000_physicalVolume_field geometryRow000_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_physicalVolume_complete"
  err.flush

noncomputable def geometryRow000_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow000_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_meanGapText : String := String.ofList (geometryRow000_meanGapNumeratorChars ++ '/' :: geometryRow000_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_meanGap_before_field"
  err.flush

theorem geometryRow000_meanGap_field :
    geometryRowsJson000.getObjVal? "mean_gap" = .ok (.str geometryRow000_meanGapText) := by rfl

theorem geometryRow000_meanGap_numerator_no_slash :
    geometryRow000_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_meanGap_numerator_parse :
    SourceJson.intChars geometryRow000_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_parse :
    SourceJson.intChars geometryRow000_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_meanGap_parse :
    parseRational geometryRow000_meanGapText = .ok geometryRowsTyped000.meanGap :=
  original_rational_fraction_of_chars geometryRow000_meanGapNumeratorChars geometryRow000_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow000_meanGap_numerator_no_slash geometryRow000_meanGap_numerator_parse
    geometryRow000_meanGap_denominator_parse geometryRow000_meanGap_denominator_nonzero

theorem geometryRow000_meanGap_read :
    rationalField geometryRowsJson000 "mean_gap" = .ok geometryRowsTyped000.meanGap :=
  original_rationalField_of_string geometryRowsJson000 "mean_gap" geometryRow000_meanGapText
    geometryRowsTyped000.meanGap geometryRow000_meanGap_field geometryRow000_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_meanGap_complete"
  err.flush

noncomputable def geometryRow000_jensenBoundNumeratorChars : List Char := ['5', '5', '1', '5', '2', '0', '7', '1', '6', '0', '2', '9', '4', '5', '3', '7', '9', '6', '5', '5', '6', '7', '9', '5', '0', '4', '4', '3', '0', '9', '2', '9', '1', '2', '5', '3', '7', '0', '7', '2', '5', '0', '4', '2', '4', '1', '1', '5', '7', '1', '2', '8', '9', '8', '8', '1', '6', '4', '5', '7', '3', '0', '1', '8', '8', '8', '5', '5', '5', '8', '1', '1', '3', '2', '7', '1', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_jensenBoundDenominatorChars : List Char := ['7', '7', '8', '3', '1', '7', '0', '6', '3', '2', '7', '2', '4', '1', '8', '5', '6', '7', '6', '3', '9', '3', '8', '5', '3', '1', '8', '7', '9', '6', '8', '1', '9', '1', '7', '3', '4', '9', '7', '9', '3', '0', '3', '3', '1', '1', '5', '8', '2', '1', '4', '0', '8', '9', '1', '3', '0', '4', '3', '4', '3', '7', '2', '6', '2', '6', '2', '5', '9', '7', '3', '6', '9', '4', '7', '2', '1', '8', '7', '4', '3', '5', '5', '7', '7', '5', '5', '9', '2', '3', '1', '9', '7', '9', '5', '3', '1', '7', '0', '3', '3', '3', '8', '6', '5', '0', '8', '9', '2', '3', '0', '4', '0', '2', '3', '4', '3']
noncomputable def geometryRow000_jensenBoundText : String := String.ofList (geometryRow000_jensenBoundNumeratorChars ++ '/' :: geometryRow000_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_jensenBound_before_field"
  err.flush

theorem geometryRow000_jensenBound_field :
    geometryRowsJson000.getObjVal? "jensen_bound" = .ok (.str geometryRow000_jensenBoundText) := by rfl

theorem geometryRow000_jensenBound_numerator_no_slash :
    geometryRow000_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow000_jensenBoundNumeratorChars = some (5515207160294537965567950443092912537072504241157128988164573018885558113271808000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow000_jensenBoundDenominatorChars = some (778317063272418567639385318796819173497930331158214089130434372626259736947218743557755923197953170333865089230402343 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_nonzero : (778317063272418567639385318796819173497930331158214089130434372626259736947218743557755923197953170333865089230402343 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_jensenBound_parse :
    parseRational geometryRow000_jensenBoundText = .ok geometryRowsTyped000.jensenBound :=
  original_rational_fraction_of_chars geometryRow000_jensenBoundNumeratorChars geometryRow000_jensenBoundDenominatorChars
    (5515207160294537965567950443092912537072504241157128988164573018885558113271808000000000000000000000000 : Int) (778317063272418567639385318796819173497930331158214089130434372626259736947218743557755923197953170333865089230402343 : Int)
    geometryRow000_jensenBound_numerator_no_slash geometryRow000_jensenBound_numerator_parse
    geometryRow000_jensenBound_denominator_parse geometryRow000_jensenBound_denominator_nonzero

theorem geometryRow000_jensenBound_read :
    rationalField geometryRowsJson000 "jensen_bound" = .ok geometryRowsTyped000.jensenBound :=
  original_rationalField_of_string geometryRowsJson000 "jensen_bound" geometryRow000_jensenBoundText
    geometryRowsTyped000.jensenBound geometryRow000_jensenBound_field geometryRow000_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_factorMaxima_before"
  err.flush

theorem geometryRow000_factorMaxima_read :
    rationalArrayField geometryRowsJson000 "factor_maxima" = .ok geometryRowsTyped000.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_gapWeightedMeans_before"
  err.flush

theorem geometryRow000_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson000 "gap_weighted_means" = .ok geometryRowsTyped000.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow000_floorChars : List Char := ['5', '6', '1', '4', '1', '6', '0', '9', '8', '6', '7', '6', '3', '6', '9']
noncomputable def geometryRow000_floorText : String := String.ofList geometryRow000_floorChars

theorem geometryRow000_floor_text_read :
    geometryRowsJson000.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow000_floorText := by rfl

theorem geometryRow000_floor_chars_parse :
    SourceJson.intChars geometryRow000_floorChars = some (561416098676369 : Int) := by decide +kernel

theorem geometryRow000_floor_parse :
    parseInteger geometryRow000_floorText = .ok geometryRowsTyped000.jensenFloorQ96 := by
  simp only [geometryRow000_floorText, parseInteger, String.toList_ofList, geometryRow000_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_000 :
    decodeGeometryRow geometryRowsJson000 = .ok geometryRowsTyped000 :=
  original_geometryRow_of_fields geometryRowsJson000 geometryRowsTyped000 geometryRow000_floorText
    geometryRow000_simplexId_read geometryRow000_vertexIds_read
    geometryRow000_physicalVolume_read geometryRow000_meanGap_read
    geometryRow000_factorMaxima_read geometryRow000_gapWeightedMeans_read
    geometryRow000_jensenBound_read geometryRow000_floor_text_read geometryRow000_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_000_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson001 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped001 : GeometryRow :=
  { simplexId := 1,
    vertexIds := #[39, 35, 29, 28, 25, 13, 3, 2, 0],
    physicalVolume := ((908675990150587573882556374508062593635582652803 : ℚ) / (106543790429936025600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((20060819224822927 : ℚ) / (234848554237500000 : ℚ)), ((1307150604422800513 : ℚ) / (15030307471200000000 : ℚ)), ((1859521687599262091 : ℚ) / (12883120689600000000 : ℚ)), ((3494014819765613653 : ℚ) / (30060614942400000000 : ℚ)), ((13153668691054301 : ℚ) / (189457657200000000 : ℚ)), ((4265342692081216183 : ℚ) / (90181844827200000000 : ℚ)), ((265915629293206223 : ℚ) / (7361783251200000000 : ℚ)), ((250641451249023893 : ℚ) / (7361783251200000000 : ℚ)), ((178854361234482323 : ℚ) / (5636365301700000000 : ℚ)), ((1406942902998623149 : ℚ) / (45090922413600000000 : ℚ))],
    jensenBound := ((33363828787325068368539011362710454062168943328594877852652421990510865017342011671777136190667299849051526804659216812181588897420967296896000000000000000000000000 : ℚ) / (425238452808207161964823758057157456723624448527232696072897065857686793746836679783902813806821969768684724531687568702824231030209041038990733569659756816801322233858731951 : ℚ)),
    jensenFloorQ96 := (6216170790303619159 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_simplexId_before"
  err.flush

theorem geometryRow001_simplexId_read :
    geometryRowsJson001.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped001.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_vertexIds_before"
  err.flush

theorem geometryRow001_vertexIds_read :
    geometryRowsJson001.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped001.vertexIds := by decide +kernel

noncomputable def geometryRow001_physicalVolumeNumeratorChars : List Char := ['9', '0', '8', '6', '7', '5', '9', '9', '0', '1', '5', '0', '5', '8', '7', '5', '7', '3', '8', '8', '2', '5', '5', '6', '3', '7', '4', '5', '0', '8', '0', '6', '2', '5', '9', '3', '6', '3', '5', '5', '8', '2', '6', '5', '2', '8', '0', '3']
noncomputable def geometryRow001_physicalVolumeDenominatorChars : List Char := ['1', '0', '6', '5', '4', '3', '7', '9', '0', '4', '2', '9', '9', '3', '6', '0', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_physicalVolumeText : String := String.ofList (geometryRow001_physicalVolumeNumeratorChars ++ '/' :: geometryRow001_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_physicalVolume_before_field"
  err.flush

theorem geometryRow001_physicalVolume_field :
    geometryRowsJson001.getObjVal? "physical_volume" = .ok (.str geometryRow001_physicalVolumeText) := by rfl

theorem geometryRow001_physicalVolume_numerator_no_slash :
    geometryRow001_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeNumeratorChars = some (908675990150587573882556374508062593635582652803 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeDenominatorChars = some (106543790429936025600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_nonzero : (106543790429936025600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_physicalVolume_parse :
    parseRational geometryRow001_physicalVolumeText = .ok geometryRowsTyped001.physicalVolume :=
  original_rational_fraction_of_chars geometryRow001_physicalVolumeNumeratorChars geometryRow001_physicalVolumeDenominatorChars
    (908675990150587573882556374508062593635582652803 : Int) (106543790429936025600000000000000000000000000000000000000000000000000 : Int)
    geometryRow001_physicalVolume_numerator_no_slash geometryRow001_physicalVolume_numerator_parse
    geometryRow001_physicalVolume_denominator_parse geometryRow001_physicalVolume_denominator_nonzero

theorem geometryRow001_physicalVolume_read :
    rationalField geometryRowsJson001 "physical_volume" = .ok geometryRowsTyped001.physicalVolume :=
  original_rationalField_of_string geometryRowsJson001 "physical_volume" geometryRow001_physicalVolumeText
    geometryRowsTyped001.physicalVolume geometryRow001_physicalVolume_field geometryRow001_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_physicalVolume_complete"
  err.flush

noncomputable def geometryRow001_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow001_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow001_meanGapText : String := String.ofList (geometryRow001_meanGapNumeratorChars ++ '/' :: geometryRow001_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_meanGap_before_field"
  err.flush

theorem geometryRow001_meanGap_field :
    geometryRowsJson001.getObjVal? "mean_gap" = .ok (.str geometryRow001_meanGapText) := by rfl

theorem geometryRow001_meanGap_numerator_no_slash :
    geometryRow001_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_meanGap_numerator_parse :
    SourceJson.intChars geometryRow001_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_parse :
    SourceJson.intChars geometryRow001_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_meanGap_parse :
    parseRational geometryRow001_meanGapText = .ok geometryRowsTyped001.meanGap :=
  original_rational_fraction_of_chars geometryRow001_meanGapNumeratorChars geometryRow001_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow001_meanGap_numerator_no_slash geometryRow001_meanGap_numerator_parse
    geometryRow001_meanGap_denominator_parse geometryRow001_meanGap_denominator_nonzero

theorem geometryRow001_meanGap_read :
    rationalField geometryRowsJson001 "mean_gap" = .ok geometryRowsTyped001.meanGap :=
  original_rationalField_of_string geometryRowsJson001 "mean_gap" geometryRow001_meanGapText
    geometryRowsTyped001.meanGap geometryRow001_meanGap_field geometryRow001_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_meanGap_complete"
  err.flush

noncomputable def geometryRow001_jensenBoundNumeratorChars : List Char := ['3', '3', '3', '6', '3', '8', '2', '8', '7', '8', '7', '3', '2', '5', '0', '6', '8', '3', '6', '8', '5', '3', '9', '0', '1', '1', '3', '6', '2', '7', '1', '0', '4', '5', '4', '0', '6', '2', '1', '6', '8', '9', '4', '3', '3', '2', '8', '5', '9', '4', '8', '7', '7', '8', '5', '2', '6', '5', '2', '4', '2', '1', '9', '9', '0', '5', '1', '0', '8', '6', '5', '0', '1', '7', '3', '4', '2', '0', '1', '1', '6', '7', '1', '7', '7', '7', '1', '3', '6', '1', '9', '0', '6', '6', '7', '2', '9', '9', '8', '4', '9', '0', '5', '1', '5', '2', '6', '8', '0', '4', '6', '5', '9', '2', '1', '6', '8', '1', '2', '1', '8', '1', '5', '8', '8', '8', '9', '7', '4', '2', '0', '9', '6', '7', '2', '9', '6', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_jensenBoundDenominatorChars : List Char := ['4', '2', '5', '2', '3', '8', '4', '5', '2', '8', '0', '8', '2', '0', '7', '1', '6', '1', '9', '6', '4', '8', '2', '3', '7', '5', '8', '0', '5', '7', '1', '5', '7', '4', '5', '6', '7', '2', '3', '6', '2', '4', '4', '4', '8', '5', '2', '7', '2', '3', '2', '6', '9', '6', '0', '7', '2', '8', '9', '7', '0', '6', '5', '8', '5', '7', '6', '8', '6', '7', '9', '3', '7', '4', '6', '8', '3', '6', '6', '7', '9', '7', '8', '3', '9', '0', '2', '8', '1', '3', '8', '0', '6', '8', '2', '1', '9', '6', '9', '7', '6', '8', '6', '8', '4', '7', '2', '4', '5', '3', '1', '6', '8', '7', '5', '6', '8', '7', '0', '2', '8', '2', '4', '2', '3', '1', '0', '3', '0', '2', '0', '9', '0', '4', '1', '0', '3', '8', '9', '9', '0', '7', '3', '3', '5', '6', '9', '6', '5', '9', '7', '5', '6', '8', '1', '6', '8', '0', '1', '3', '2', '2', '2', '3', '3', '8', '5', '8', '7', '3', '1', '9', '5', '1']
noncomputable def geometryRow001_jensenBoundText : String := String.ofList (geometryRow001_jensenBoundNumeratorChars ++ '/' :: geometryRow001_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_jensenBound_before_field"
  err.flush

theorem geometryRow001_jensenBound_field :
    geometryRowsJson001.getObjVal? "jensen_bound" = .ok (.str geometryRow001_jensenBoundText) := by rfl

theorem geometryRow001_jensenBound_numerator_no_slash :
    geometryRow001_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow001_jensenBoundNumeratorChars = some (33363828787325068368539011362710454062168943328594877852652421990510865017342011671777136190667299849051526804659216812181588897420967296896000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow001_jensenBoundDenominatorChars = some (425238452808207161964823758057157456723624448527232696072897065857686793746836679783902813806821969768684724531687568702824231030209041038990733569659756816801322233858731951 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_nonzero : (425238452808207161964823758057157456723624448527232696072897065857686793746836679783902813806821969768684724531687568702824231030209041038990733569659756816801322233858731951 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_jensenBound_parse :
    parseRational geometryRow001_jensenBoundText = .ok geometryRowsTyped001.jensenBound :=
  original_rational_fraction_of_chars geometryRow001_jensenBoundNumeratorChars geometryRow001_jensenBoundDenominatorChars
    (33363828787325068368539011362710454062168943328594877852652421990510865017342011671777136190667299849051526804659216812181588897420967296896000000000000000000000000 : Int) (425238452808207161964823758057157456723624448527232696072897065857686793746836679783902813806821969768684724531687568702824231030209041038990733569659756816801322233858731951 : Int)
    geometryRow001_jensenBound_numerator_no_slash geometryRow001_jensenBound_numerator_parse
    geometryRow001_jensenBound_denominator_parse geometryRow001_jensenBound_denominator_nonzero

theorem geometryRow001_jensenBound_read :
    rationalField geometryRowsJson001 "jensen_bound" = .ok geometryRowsTyped001.jensenBound :=
  original_rationalField_of_string geometryRowsJson001 "jensen_bound" geometryRow001_jensenBoundText
    geometryRowsTyped001.jensenBound geometryRow001_jensenBound_field geometryRow001_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_factorMaxima_before"
  err.flush

theorem geometryRow001_factorMaxima_read :
    rationalArrayField geometryRowsJson001 "factor_maxima" = .ok geometryRowsTyped001.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_gapWeightedMeans_before"
  err.flush

theorem geometryRow001_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson001 "gap_weighted_means" = .ok geometryRowsTyped001.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow001_floorChars : List Char := ['6', '2', '1', '6', '1', '7', '0', '7', '9', '0', '3', '0', '3', '6', '1', '9', '1', '5', '9']
noncomputable def geometryRow001_floorText : String := String.ofList geometryRow001_floorChars

theorem geometryRow001_floor_text_read :
    geometryRowsJson001.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow001_floorText := by rfl

theorem geometryRow001_floor_chars_parse :
    SourceJson.intChars geometryRow001_floorChars = some (6216170790303619159 : Int) := by decide +kernel

theorem geometryRow001_floor_parse :
    parseInteger geometryRow001_floorText = .ok geometryRowsTyped001.jensenFloorQ96 := by
  simp only [geometryRow001_floorText, parseInteger, String.toList_ofList, geometryRow001_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_001 :
    decodeGeometryRow geometryRowsJson001 = .ok geometryRowsTyped001 :=
  original_geometryRow_of_fields geometryRowsJson001 geometryRowsTyped001 geometryRow001_floorText
    geometryRow001_simplexId_read geometryRow001_vertexIds_read
    geometryRow001_physicalVolume_read geometryRow001_meanGap_read
    geometryRow001_factorMaxima_read geometryRow001_gapWeightedMeans_read
    geometryRow001_jensenBound_read geometryRow001_floor_text_read geometryRow001_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_001_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock000 : List SourceJson := [geometryRowsJson000, geometryRowsJson001]
noncomputable def geometryRowsTypedBlock000 : List (GeometryRow) := [geometryRowsTyped000, geometryRowsTyped001]
noncomputable def geometryRowsTypedThroughBlock000 : List (GeometryRow) := geometryRowsTypedBlock000

theorem geometry_Rows_block_000_push_eq (acc : List SourceJson) :
    SimplicesBlock000.blockPush acc = [geometryRowsJson001, geometryRowsJson000] ++ acc := by rfl

theorem geometry_Rows_block_000_reverse (acc : List SourceJson) :
    (SimplicesBlock000.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock000 := by
  rw [geometry_Rows_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_000 :
    geometryRowsJsonBlock000.mapM decodeGeometryRow = .ok geometryRowsTypedBlock000 := by
  simp only [geometryRowsJsonBlock000, geometryRowsTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_000, decode_geometry_Rows_001]
  rfl

theorem decode_geometry_Rows_through_block_000 :
    SimplicesValue.arrayAcc001.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock000 := by
  change (SimplicesBlock000.blockPush SimplicesValue.arrayAcc000).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_000_reverse]
  exact decode_geometry_Rows_block_000

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_000_complete"
  err.flush

#print axioms geometryRow000_simplexId_read
#print axioms geometryRow000_vertexIds_read
#print axioms geometryRow000_physicalVolume_field
#print axioms geometryRow000_physicalVolume_numerator_no_slash
#print axioms geometryRow000_physicalVolume_numerator_parse
#print axioms geometryRow000_physicalVolume_denominator_parse
#print axioms geometryRow000_physicalVolume_denominator_nonzero
#print axioms geometryRow000_physicalVolume_parse
#print axioms geometryRow000_physicalVolume_read
#print axioms geometryRow000_meanGap_field
#print axioms geometryRow000_meanGap_numerator_no_slash
#print axioms geometryRow000_meanGap_numerator_parse
#print axioms geometryRow000_meanGap_denominator_parse
#print axioms geometryRow000_meanGap_denominator_nonzero
#print axioms geometryRow000_meanGap_parse
#print axioms geometryRow000_meanGap_read
#print axioms geometryRow000_jensenBound_field
#print axioms geometryRow000_jensenBound_numerator_no_slash
#print axioms geometryRow000_jensenBound_numerator_parse
#print axioms geometryRow000_jensenBound_denominator_parse
#print axioms geometryRow000_jensenBound_denominator_nonzero
#print axioms geometryRow000_jensenBound_parse
#print axioms geometryRow000_jensenBound_read
#print axioms geometryRow000_factorMaxima_read
#print axioms geometryRow000_gapWeightedMeans_read
#print axioms geometryRow000_floor_text_read
#print axioms geometryRow000_floor_chars_parse
#print axioms geometryRow000_floor_parse
#print axioms decode_geometry_Rows_000
#print axioms geometryRow001_simplexId_read
#print axioms geometryRow001_vertexIds_read
#print axioms geometryRow001_physicalVolume_field
#print axioms geometryRow001_physicalVolume_numerator_no_slash
#print axioms geometryRow001_physicalVolume_numerator_parse
#print axioms geometryRow001_physicalVolume_denominator_parse
#print axioms geometryRow001_physicalVolume_denominator_nonzero
#print axioms geometryRow001_physicalVolume_parse
#print axioms geometryRow001_physicalVolume_read
#print axioms geometryRow001_meanGap_field
#print axioms geometryRow001_meanGap_numerator_no_slash
#print axioms geometryRow001_meanGap_numerator_parse
#print axioms geometryRow001_meanGap_denominator_parse
#print axioms geometryRow001_meanGap_denominator_nonzero
#print axioms geometryRow001_meanGap_parse
#print axioms geometryRow001_meanGap_read
#print axioms geometryRow001_jensenBound_field
#print axioms geometryRow001_jensenBound_numerator_no_slash
#print axioms geometryRow001_jensenBound_numerator_parse
#print axioms geometryRow001_jensenBound_denominator_parse
#print axioms geometryRow001_jensenBound_denominator_nonzero
#print axioms geometryRow001_jensenBound_parse
#print axioms geometryRow001_jensenBound_read
#print axioms geometryRow001_factorMaxima_read
#print axioms geometryRow001_gapWeightedMeans_read
#print axioms geometryRow001_floor_text_read
#print axioms geometryRow001_floor_chars_parse
#print axioms geometryRow001_floor_parse
#print axioms decode_geometry_Rows_001
#print axioms geometry_Rows_block_000_push_eq
#print axioms geometry_Rows_block_000_reverse
#print axioms decode_geometry_Rows_block_000
#print axioms decode_geometry_Rows_through_block_000

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
