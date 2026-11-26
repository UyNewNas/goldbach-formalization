import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows032

/-! Original simplices typed block 33, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson065 : SourceJson :=
  (SimplicesBlock033.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped065 : GeometryRow :=
  { simplexId := 65,
    vertexIds := #[39, 35, 34, 24, 11, 10, 8, 3, 1],
    physicalVolume := ((2742024631562614976851076642437753 : ℚ) / (793804800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((2911992563453 : ℚ) / (35271600000000 : ℚ)), ((2947646549093 : ℚ) / (35271600000000 : ℚ)), ((130831206713 : ℚ) / (904400000000 : ℚ)), ((1978039565357 : ℚ) / (17635800000000 : ℚ)), ((129291118223 : ℚ) / (2074800000000 : ℚ)), ((563958859111 : ℚ) / (11757200000000 : ℚ)), ((1421308511453 : ℚ) / (35271600000000 : ℚ)), ((438628790331 : ℚ) / (11757200000000 : ℚ)), ((1217721148453 : ℚ) / (35271600000000 : ℚ)), ((1217716445573 : ℚ) / (35271600000000 : ℚ))],
    jensenBound := ((23922611994156681590986499442436834534762669536973165716037946167648948743278208000000000000000000000000 : ℚ) / (1848513369758206821262414551700466307694335563765370202774084240887616772578617974875943686192561606661669385365051819 : ℚ)),
    jensenFloorQ96 := (1025334531979421 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_simplexId_before"
  err.flush

theorem geometryRow065_simplexId_read :
    geometryRowsJson065.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped065.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_vertexIds_before"
  err.flush

theorem geometryRow065_vertexIds_read :
    geometryRowsJson065.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped065.vertexIds := by decide +kernel

noncomputable def geometryRow065_physicalVolumeNumeratorChars : List Char := ['2', '7', '4', '2', '0', '2', '4', '6', '3', '1', '5', '6', '2', '6', '1', '4', '9', '7', '6', '8', '5', '1', '0', '7', '6', '6', '4', '2', '4', '3', '7', '7', '5', '3']
noncomputable def geometryRow065_physicalVolumeDenominatorChars : List Char := ['7', '9', '3', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow065_physicalVolumeText : String := String.ofList (geometryRow065_physicalVolumeNumeratorChars ++ '/' :: geometryRow065_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_physicalVolume_before_field"
  err.flush

theorem geometryRow065_physicalVolume_field :
    geometryRowsJson065.getObjVal? "physical_volume" = .ok (.str geometryRow065_physicalVolumeText) := by rfl

theorem geometryRow065_physicalVolume_numerator_no_slash :
    geometryRow065_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow065_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow065_physicalVolumeNumeratorChars = some (2742024631562614976851076642437753 : Int) := by decide +kernel

theorem geometryRow065_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow065_physicalVolumeDenominatorChars = some (793804800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow065_physicalVolume_denominator_nonzero : (793804800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow065_physicalVolume_parse :
    parseRational geometryRow065_physicalVolumeText = .ok geometryRowsTyped065.physicalVolume :=
  original_rational_fraction_of_chars geometryRow065_physicalVolumeNumeratorChars geometryRow065_physicalVolumeDenominatorChars
    (2742024631562614976851076642437753 : Int) (793804800000000000000000000000000000000000000000000000000 : Int)
    geometryRow065_physicalVolume_numerator_no_slash geometryRow065_physicalVolume_numerator_parse
    geometryRow065_physicalVolume_denominator_parse geometryRow065_physicalVolume_denominator_nonzero

theorem geometryRow065_physicalVolume_read :
    rationalField geometryRowsJson065 "physical_volume" = .ok geometryRowsTyped065.physicalVolume :=
  original_rationalField_of_string geometryRowsJson065 "physical_volume" geometryRow065_physicalVolumeText
    geometryRowsTyped065.physicalVolume geometryRow065_physicalVolume_field geometryRow065_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_physicalVolume_complete"
  err.flush

noncomputable def geometryRow065_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow065_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow065_meanGapText : String := String.ofList (geometryRow065_meanGapNumeratorChars ++ '/' :: geometryRow065_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_meanGap_before_field"
  err.flush

theorem geometryRow065_meanGap_field :
    geometryRowsJson065.getObjVal? "mean_gap" = .ok (.str geometryRow065_meanGapText) := by rfl

theorem geometryRow065_meanGap_numerator_no_slash :
    geometryRow065_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow065_meanGap_numerator_parse :
    SourceJson.intChars geometryRow065_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow065_meanGap_denominator_parse :
    SourceJson.intChars geometryRow065_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow065_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow065_meanGap_parse :
    parseRational geometryRow065_meanGapText = .ok geometryRowsTyped065.meanGap :=
  original_rational_fraction_of_chars geometryRow065_meanGapNumeratorChars geometryRow065_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow065_meanGap_numerator_no_slash geometryRow065_meanGap_numerator_parse
    geometryRow065_meanGap_denominator_parse geometryRow065_meanGap_denominator_nonzero

theorem geometryRow065_meanGap_read :
    rationalField geometryRowsJson065 "mean_gap" = .ok geometryRowsTyped065.meanGap :=
  original_rationalField_of_string geometryRowsJson065 "mean_gap" geometryRow065_meanGapText
    geometryRowsTyped065.meanGap geometryRow065_meanGap_field geometryRow065_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_meanGap_complete"
  err.flush

noncomputable def geometryRow065_jensenBoundNumeratorChars : List Char := ['2', '3', '9', '2', '2', '6', '1', '1', '9', '9', '4', '1', '5', '6', '6', '8', '1', '5', '9', '0', '9', '8', '6', '4', '9', '9', '4', '4', '2', '4', '3', '6', '8', '3', '4', '5', '3', '4', '7', '6', '2', '6', '6', '9', '5', '3', '6', '9', '7', '3', '1', '6', '5', '7', '1', '6', '0', '3', '7', '9', '4', '6', '1', '6', '7', '6', '4', '8', '9', '4', '8', '7', '4', '3', '2', '7', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow065_jensenBoundDenominatorChars : List Char := ['1', '8', '4', '8', '5', '1', '3', '3', '6', '9', '7', '5', '8', '2', '0', '6', '8', '2', '1', '2', '6', '2', '4', '1', '4', '5', '5', '1', '7', '0', '0', '4', '6', '6', '3', '0', '7', '6', '9', '4', '3', '3', '5', '5', '6', '3', '7', '6', '5', '3', '7', '0', '2', '0', '2', '7', '7', '4', '0', '8', '4', '2', '4', '0', '8', '8', '7', '6', '1', '6', '7', '7', '2', '5', '7', '8', '6', '1', '7', '9', '7', '4', '8', '7', '5', '9', '4', '3', '6', '8', '6', '1', '9', '2', '5', '6', '1', '6', '0', '6', '6', '6', '1', '6', '6', '9', '3', '8', '5', '3', '6', '5', '0', '5', '1', '8', '1', '9']
noncomputable def geometryRow065_jensenBoundText : String := String.ofList (geometryRow065_jensenBoundNumeratorChars ++ '/' :: geometryRow065_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_jensenBound_before_field"
  err.flush

theorem geometryRow065_jensenBound_field :
    geometryRowsJson065.getObjVal? "jensen_bound" = .ok (.str geometryRow065_jensenBoundText) := by rfl

theorem geometryRow065_jensenBound_numerator_no_slash :
    geometryRow065_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow065_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow065_jensenBoundNumeratorChars = some (23922611994156681590986499442436834534762669536973165716037946167648948743278208000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow065_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow065_jensenBoundDenominatorChars = some (1848513369758206821262414551700466307694335563765370202774084240887616772578617974875943686192561606661669385365051819 : Int) := by decide +kernel

theorem geometryRow065_jensenBound_denominator_nonzero : (1848513369758206821262414551700466307694335563765370202774084240887616772578617974875943686192561606661669385365051819 : Int) ≠ 0 := by decide +kernel

theorem geometryRow065_jensenBound_parse :
    parseRational geometryRow065_jensenBoundText = .ok geometryRowsTyped065.jensenBound :=
  original_rational_fraction_of_chars geometryRow065_jensenBoundNumeratorChars geometryRow065_jensenBoundDenominatorChars
    (23922611994156681590986499442436834534762669536973165716037946167648948743278208000000000000000000000000 : Int) (1848513369758206821262414551700466307694335563765370202774084240887616772578617974875943686192561606661669385365051819 : Int)
    geometryRow065_jensenBound_numerator_no_slash geometryRow065_jensenBound_numerator_parse
    geometryRow065_jensenBound_denominator_parse geometryRow065_jensenBound_denominator_nonzero

theorem geometryRow065_jensenBound_read :
    rationalField geometryRowsJson065 "jensen_bound" = .ok geometryRowsTyped065.jensenBound :=
  original_rationalField_of_string geometryRowsJson065 "jensen_bound" geometryRow065_jensenBoundText
    geometryRowsTyped065.jensenBound geometryRow065_jensenBound_field geometryRow065_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_factorMaxima_before"
  err.flush

theorem geometryRow065_factorMaxima_read :
    rationalArrayField geometryRowsJson065 "factor_maxima" = .ok geometryRowsTyped065.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_gapWeightedMeans_before"
  err.flush

theorem geometryRow065_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson065 "gap_weighted_means" = .ok geometryRowsTyped065.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow065_floorChars : List Char := ['1', '0', '2', '5', '3', '3', '4', '5', '3', '1', '9', '7', '9', '4', '2', '1']
noncomputable def geometryRow065_floorText : String := String.ofList geometryRow065_floorChars

theorem geometryRow065_floor_text_read :
    geometryRowsJson065.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow065_floorText := by rfl

theorem geometryRow065_floor_chars_parse :
    SourceJson.intChars geometryRow065_floorChars = some (1025334531979421 : Int) := by decide +kernel

theorem geometryRow065_floor_parse :
    parseInteger geometryRow065_floorText = .ok geometryRowsTyped065.jensenFloorQ96 := by
  simp only [geometryRow065_floorText, parseInteger, String.toList_ofList, geometryRow065_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_065 :
    decodeGeometryRow geometryRowsJson065 = .ok geometryRowsTyped065 :=
  original_geometryRow_of_fields geometryRowsJson065 geometryRowsTyped065 geometryRow065_floorText
    geometryRow065_simplexId_read geometryRow065_vertexIds_read
    geometryRow065_physicalVolume_read geometryRow065_meanGap_read
    geometryRow065_factorMaxima_read geometryRow065_gapWeightedMeans_read
    geometryRow065_jensenBound_read geometryRow065_floor_text_read geometryRow065_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_065_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson066 : SourceJson :=
  (SimplicesBlock033.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped066 : GeometryRow :=
  { simplexId := 66,
    vertexIds := #[39, 35, 34, 24, 23, 10, 8, 3, 1],
    physicalVolume := ((203975737479981629787818395089164893 : ℚ) / (271481241600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((117804150497 : ℚ) / (1469650000000 : ℚ)), ((7455608327 : ℚ) / (91853125000 : ℚ)), ((24612286789 : ℚ) / (169575000000 : ℚ)), ((490275243763 : ℚ) / (4408950000000 : ℚ)), ((21382455093 : ℚ) / (345800000000 : ℚ)), ((418734496757 : ℚ) / (8817900000000 : ℚ)), ((12236429617 : ℚ) / (309400000000 : ℚ)), ((688059543359 : ℚ) / (17635800000000 : ℚ)), ((158567114921 : ℚ) / (4408950000000 : ℚ)), ((158566527061 : ℚ) / (4408950000000 : ℚ))],
    jensenBound := ((57567582647927644839878343724381880798732594568620786467440739213681703471660614013671875000 : ℚ) / (20990624411489026897900126042993061112470191858396160724783528349138098829239274255641260652286925679539167 : ℚ)),
    jensenFloorQ96 := (217286237139613 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_simplexId_before"
  err.flush

theorem geometryRow066_simplexId_read :
    geometryRowsJson066.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped066.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_vertexIds_before"
  err.flush

theorem geometryRow066_vertexIds_read :
    geometryRowsJson066.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped066.vertexIds := by decide +kernel

noncomputable def geometryRow066_physicalVolumeNumeratorChars : List Char := ['2', '0', '3', '9', '7', '5', '7', '3', '7', '4', '7', '9', '9', '8', '1', '6', '2', '9', '7', '8', '7', '8', '1', '8', '3', '9', '5', '0', '8', '9', '1', '6', '4', '8', '9', '3']
noncomputable def geometryRow066_physicalVolumeDenominatorChars : List Char := ['2', '7', '1', '4', '8', '1', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow066_physicalVolumeText : String := String.ofList (geometryRow066_physicalVolumeNumeratorChars ++ '/' :: geometryRow066_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_physicalVolume_before_field"
  err.flush

theorem geometryRow066_physicalVolume_field :
    geometryRowsJson066.getObjVal? "physical_volume" = .ok (.str geometryRow066_physicalVolumeText) := by rfl

theorem geometryRow066_physicalVolume_numerator_no_slash :
    geometryRow066_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow066_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow066_physicalVolumeNumeratorChars = some (203975737479981629787818395089164893 : Int) := by decide +kernel

theorem geometryRow066_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow066_physicalVolumeDenominatorChars = some (271481241600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow066_physicalVolume_denominator_nonzero : (271481241600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow066_physicalVolume_parse :
    parseRational geometryRow066_physicalVolumeText = .ok geometryRowsTyped066.physicalVolume :=
  original_rational_fraction_of_chars geometryRow066_physicalVolumeNumeratorChars geometryRow066_physicalVolumeDenominatorChars
    (203975737479981629787818395089164893 : Int) (271481241600000000000000000000000000000000000000000000000000 : Int)
    geometryRow066_physicalVolume_numerator_no_slash geometryRow066_physicalVolume_numerator_parse
    geometryRow066_physicalVolume_denominator_parse geometryRow066_physicalVolume_denominator_nonzero

theorem geometryRow066_physicalVolume_read :
    rationalField geometryRowsJson066 "physical_volume" = .ok geometryRowsTyped066.physicalVolume :=
  original_rationalField_of_string geometryRowsJson066 "physical_volume" geometryRow066_physicalVolumeText
    geometryRowsTyped066.physicalVolume geometryRow066_physicalVolume_field geometryRow066_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_physicalVolume_complete"
  err.flush

noncomputable def geometryRow066_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow066_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow066_meanGapText : String := String.ofList (geometryRow066_meanGapNumeratorChars ++ '/' :: geometryRow066_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_meanGap_before_field"
  err.flush

theorem geometryRow066_meanGap_field :
    geometryRowsJson066.getObjVal? "mean_gap" = .ok (.str geometryRow066_meanGapText) := by rfl

theorem geometryRow066_meanGap_numerator_no_slash :
    geometryRow066_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow066_meanGap_numerator_parse :
    SourceJson.intChars geometryRow066_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow066_meanGap_denominator_parse :
    SourceJson.intChars geometryRow066_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow066_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow066_meanGap_parse :
    parseRational geometryRow066_meanGapText = .ok geometryRowsTyped066.meanGap :=
  original_rational_fraction_of_chars geometryRow066_meanGapNumeratorChars geometryRow066_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow066_meanGap_numerator_no_slash geometryRow066_meanGap_numerator_parse
    geometryRow066_meanGap_denominator_parse geometryRow066_meanGap_denominator_nonzero

theorem geometryRow066_meanGap_read :
    rationalField geometryRowsJson066 "mean_gap" = .ok geometryRowsTyped066.meanGap :=
  original_rationalField_of_string geometryRowsJson066 "mean_gap" geometryRow066_meanGapText
    geometryRowsTyped066.meanGap geometryRow066_meanGap_field geometryRow066_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_meanGap_complete"
  err.flush

noncomputable def geometryRow066_jensenBoundNumeratorChars : List Char := ['5', '7', '5', '6', '7', '5', '8', '2', '6', '4', '7', '9', '2', '7', '6', '4', '4', '8', '3', '9', '8', '7', '8', '3', '4', '3', '7', '2', '4', '3', '8', '1', '8', '8', '0', '7', '9', '8', '7', '3', '2', '5', '9', '4', '5', '6', '8', '6', '2', '0', '7', '8', '6', '4', '6', '7', '4', '4', '0', '7', '3', '9', '2', '1', '3', '6', '8', '1', '7', '0', '3', '4', '7', '1', '6', '6', '0', '6', '1', '4', '0', '1', '3', '6', '7', '1', '8', '7', '5', '0', '0', '0']
noncomputable def geometryRow066_jensenBoundDenominatorChars : List Char := ['2', '0', '9', '9', '0', '6', '2', '4', '4', '1', '1', '4', '8', '9', '0', '2', '6', '8', '9', '7', '9', '0', '0', '1', '2', '6', '0', '4', '2', '9', '9', '3', '0', '6', '1', '1', '1', '2', '4', '7', '0', '1', '9', '1', '8', '5', '8', '3', '9', '6', '1', '6', '0', '7', '2', '4', '7', '8', '3', '5', '2', '8', '3', '4', '9', '1', '3', '8', '0', '9', '8', '8', '2', '9', '2', '3', '9', '2', '7', '4', '2', '5', '5', '6', '4', '1', '2', '6', '0', '6', '5', '2', '2', '8', '6', '9', '2', '5', '6', '7', '9', '5', '3', '9', '1', '6', '7']
noncomputable def geometryRow066_jensenBoundText : String := String.ofList (geometryRow066_jensenBoundNumeratorChars ++ '/' :: geometryRow066_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_jensenBound_before_field"
  err.flush

theorem geometryRow066_jensenBound_field :
    geometryRowsJson066.getObjVal? "jensen_bound" = .ok (.str geometryRow066_jensenBoundText) := by rfl

theorem geometryRow066_jensenBound_numerator_no_slash :
    geometryRow066_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow066_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow066_jensenBoundNumeratorChars = some (57567582647927644839878343724381880798732594568620786467440739213681703471660614013671875000 : Int) := by decide +kernel

theorem geometryRow066_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow066_jensenBoundDenominatorChars = some (20990624411489026897900126042993061112470191858396160724783528349138098829239274255641260652286925679539167 : Int) := by decide +kernel

theorem geometryRow066_jensenBound_denominator_nonzero : (20990624411489026897900126042993061112470191858396160724783528349138098829239274255641260652286925679539167 : Int) ≠ 0 := by decide +kernel

theorem geometryRow066_jensenBound_parse :
    parseRational geometryRow066_jensenBoundText = .ok geometryRowsTyped066.jensenBound :=
  original_rational_fraction_of_chars geometryRow066_jensenBoundNumeratorChars geometryRow066_jensenBoundDenominatorChars
    (57567582647927644839878343724381880798732594568620786467440739213681703471660614013671875000 : Int) (20990624411489026897900126042993061112470191858396160724783528349138098829239274255641260652286925679539167 : Int)
    geometryRow066_jensenBound_numerator_no_slash geometryRow066_jensenBound_numerator_parse
    geometryRow066_jensenBound_denominator_parse geometryRow066_jensenBound_denominator_nonzero

theorem geometryRow066_jensenBound_read :
    rationalField geometryRowsJson066 "jensen_bound" = .ok geometryRowsTyped066.jensenBound :=
  original_rationalField_of_string geometryRowsJson066 "jensen_bound" geometryRow066_jensenBoundText
    geometryRowsTyped066.jensenBound geometryRow066_jensenBound_field geometryRow066_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_factorMaxima_before"
  err.flush

theorem geometryRow066_factorMaxima_read :
    rationalArrayField geometryRowsJson066 "factor_maxima" = .ok geometryRowsTyped066.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_gapWeightedMeans_before"
  err.flush

theorem geometryRow066_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson066 "gap_weighted_means" = .ok geometryRowsTyped066.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow066_floorChars : List Char := ['2', '1', '7', '2', '8', '6', '2', '3', '7', '1', '3', '9', '6', '1', '3']
noncomputable def geometryRow066_floorText : String := String.ofList geometryRow066_floorChars

theorem geometryRow066_floor_text_read :
    geometryRowsJson066.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow066_floorText := by rfl

theorem geometryRow066_floor_chars_parse :
    SourceJson.intChars geometryRow066_floorChars = some (217286237139613 : Int) := by decide +kernel

theorem geometryRow066_floor_parse :
    parseInteger geometryRow066_floorText = .ok geometryRowsTyped066.jensenFloorQ96 := by
  simp only [geometryRow066_floorText, parseInteger, String.toList_ofList, geometryRow066_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_066 :
    decodeGeometryRow geometryRowsJson066 = .ok geometryRowsTyped066 :=
  original_geometryRow_of_fields geometryRowsJson066 geometryRowsTyped066 geometryRow066_floorText
    geometryRow066_simplexId_read geometryRow066_vertexIds_read
    geometryRow066_physicalVolume_read geometryRow066_meanGap_read
    geometryRow066_factorMaxima_read geometryRow066_gapWeightedMeans_read
    geometryRow066_jensenBound_read geometryRow066_floor_text_read geometryRow066_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_066_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock033 : List SourceJson := [geometryRowsJson065, geometryRowsJson066]
noncomputable def geometryRowsTypedBlock033 : List (GeometryRow) := [geometryRowsTyped065, geometryRowsTyped066]
noncomputable def geometryRowsTypedThroughBlock033 : List (GeometryRow) := geometryRowsTypedThroughBlock032 ++ geometryRowsTypedBlock033

theorem geometry_Rows_block_033_push_eq (acc : List SourceJson) :
    SimplicesBlock033.blockPush acc = [geometryRowsJson066, geometryRowsJson065] ++ acc := by rfl

theorem geometry_Rows_block_033_reverse (acc : List SourceJson) :
    (SimplicesBlock033.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock033 := by
  rw [geometry_Rows_block_033_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_033 :
    geometryRowsJsonBlock033.mapM decodeGeometryRow = .ok geometryRowsTypedBlock033 := by
  simp only [geometryRowsJsonBlock033, geometryRowsTypedBlock033, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_065, decode_geometry_Rows_066]
  rfl

theorem decode_geometry_Rows_through_block_033 :
    SimplicesValue.arrayAcc034.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock033 := by
  change (SimplicesBlock033.blockPush SimplicesValue.arrayAcc033).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_033_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_032, decode_geometry_Rows_block_033]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_033_complete"
  err.flush

#print axioms geometryRow065_simplexId_read
#print axioms geometryRow065_vertexIds_read
#print axioms geometryRow065_physicalVolume_field
#print axioms geometryRow065_physicalVolume_numerator_no_slash
#print axioms geometryRow065_physicalVolume_numerator_parse
#print axioms geometryRow065_physicalVolume_denominator_parse
#print axioms geometryRow065_physicalVolume_denominator_nonzero
#print axioms geometryRow065_physicalVolume_parse
#print axioms geometryRow065_physicalVolume_read
#print axioms geometryRow065_meanGap_field
#print axioms geometryRow065_meanGap_numerator_no_slash
#print axioms geometryRow065_meanGap_numerator_parse
#print axioms geometryRow065_meanGap_denominator_parse
#print axioms geometryRow065_meanGap_denominator_nonzero
#print axioms geometryRow065_meanGap_parse
#print axioms geometryRow065_meanGap_read
#print axioms geometryRow065_jensenBound_field
#print axioms geometryRow065_jensenBound_numerator_no_slash
#print axioms geometryRow065_jensenBound_numerator_parse
#print axioms geometryRow065_jensenBound_denominator_parse
#print axioms geometryRow065_jensenBound_denominator_nonzero
#print axioms geometryRow065_jensenBound_parse
#print axioms geometryRow065_jensenBound_read
#print axioms geometryRow065_factorMaxima_read
#print axioms geometryRow065_gapWeightedMeans_read
#print axioms geometryRow065_floor_text_read
#print axioms geometryRow065_floor_chars_parse
#print axioms geometryRow065_floor_parse
#print axioms decode_geometry_Rows_065
#print axioms geometryRow066_simplexId_read
#print axioms geometryRow066_vertexIds_read
#print axioms geometryRow066_physicalVolume_field
#print axioms geometryRow066_physicalVolume_numerator_no_slash
#print axioms geometryRow066_physicalVolume_numerator_parse
#print axioms geometryRow066_physicalVolume_denominator_parse
#print axioms geometryRow066_physicalVolume_denominator_nonzero
#print axioms geometryRow066_physicalVolume_parse
#print axioms geometryRow066_physicalVolume_read
#print axioms geometryRow066_meanGap_field
#print axioms geometryRow066_meanGap_numerator_no_slash
#print axioms geometryRow066_meanGap_numerator_parse
#print axioms geometryRow066_meanGap_denominator_parse
#print axioms geometryRow066_meanGap_denominator_nonzero
#print axioms geometryRow066_meanGap_parse
#print axioms geometryRow066_meanGap_read
#print axioms geometryRow066_jensenBound_field
#print axioms geometryRow066_jensenBound_numerator_no_slash
#print axioms geometryRow066_jensenBound_numerator_parse
#print axioms geometryRow066_jensenBound_denominator_parse
#print axioms geometryRow066_jensenBound_denominator_nonzero
#print axioms geometryRow066_jensenBound_parse
#print axioms geometryRow066_jensenBound_read
#print axioms geometryRow066_factorMaxima_read
#print axioms geometryRow066_gapWeightedMeans_read
#print axioms geometryRow066_floor_text_read
#print axioms geometryRow066_floor_chars_parse
#print axioms geometryRow066_floor_parse
#print axioms decode_geometry_Rows_066
#print axioms geometry_Rows_block_033_push_eq
#print axioms geometry_Rows_block_033_reverse
#print axioms decode_geometry_Rows_block_033
#print axioms decode_geometry_Rows_through_block_033

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
