import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows067

/-! Original simplices typed block 68, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson134 : SourceJson :=
  (SimplicesBlock068.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped134 : GeometryRow :=
  { simplexId := 134,
    vertexIds := #[39, 38, 36, 24, 23, 21, 20, 16, 1],
    physicalVolume := ((17378050424099167530759831736989664241 : ℚ) / (3129385284403200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((5165094300853 : ℚ) / (65501550000000 : ℚ)), ((10354650135461 : ℚ) / (131003100000000 : ℚ)), ((7331505191399 : ℚ) / (49126162500000 : ℚ)), ((9564210166609 : ℚ) / (87335400000000 : ℚ)), ((10249053868891 : ℚ) / (196504650000000 : ℚ)), ((17909131345391 : ℚ) / (393009300000000 : ℚ)), ((2663237687 : ℚ) / (64639687500 : ℚ)), ((639305237053 : ℚ) / (15720372000000 : ℚ)), ((31521354406403 : ℚ) / (786018600000000 : ℚ)), ((31521302005163 : ℚ) / (786018600000000 : ℚ))],
    jensenBound := ((587588450734762786907707616755046349254361633813103404456095281187416111474079087757388958476066589355468750 : ℚ) / (166357891361812645357546205909242427377174834774106894428876794058590244433308901752698561037023821953409276151843511316204671 : ℚ)),
    jensenFloorQ96 := (279839765250 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_simplexId_before"
  err.flush

theorem geometryRow134_simplexId_read :
    geometryRowsJson134.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped134.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_vertexIds_before"
  err.flush

theorem geometryRow134_vertexIds_read :
    geometryRowsJson134.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped134.vertexIds := by decide +kernel

noncomputable def geometryRow134_physicalVolumeNumeratorChars : List Char := ['1', '7', '3', '7', '8', '0', '5', '0', '4', '2', '4', '0', '9', '9', '1', '6', '7', '5', '3', '0', '7', '5', '9', '8', '3', '1', '7', '3', '6', '9', '8', '9', '6', '6', '4', '2', '4', '1']
noncomputable def geometryRow134_physicalVolumeDenominatorChars : List Char := ['3', '1', '2', '9', '3', '8', '5', '2', '8', '4', '4', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow134_physicalVolumeText : String := String.ofList (geometryRow134_physicalVolumeNumeratorChars ++ '/' :: geometryRow134_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_physicalVolume_before_field"
  err.flush

theorem geometryRow134_physicalVolume_field :
    geometryRowsJson134.getObjVal? "physical_volume" = .ok (.str geometryRow134_physicalVolumeText) := by rfl

theorem geometryRow134_physicalVolume_numerator_no_slash :
    geometryRow134_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow134_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow134_physicalVolumeNumeratorChars = some (17378050424099167530759831736989664241 : Int) := by decide +kernel

theorem geometryRow134_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow134_physicalVolumeDenominatorChars = some (3129385284403200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow134_physicalVolume_denominator_nonzero : (3129385284403200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow134_physicalVolume_parse :
    parseRational geometryRow134_physicalVolumeText = .ok geometryRowsTyped134.physicalVolume :=
  original_rational_fraction_of_chars geometryRow134_physicalVolumeNumeratorChars geometryRow134_physicalVolumeDenominatorChars
    (17378050424099167530759831736989664241 : Int) (3129385284403200000000000000000000000000000000000000000000000000 : Int)
    geometryRow134_physicalVolume_numerator_no_slash geometryRow134_physicalVolume_numerator_parse
    geometryRow134_physicalVolume_denominator_parse geometryRow134_physicalVolume_denominator_nonzero

theorem geometryRow134_physicalVolume_read :
    rationalField geometryRowsJson134 "physical_volume" = .ok geometryRowsTyped134.physicalVolume :=
  original_rationalField_of_string geometryRowsJson134 "physical_volume" geometryRow134_physicalVolumeText
    geometryRowsTyped134.physicalVolume geometryRow134_physicalVolume_field geometryRow134_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_physicalVolume_complete"
  err.flush

noncomputable def geometryRow134_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow134_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow134_meanGapText : String := String.ofList (geometryRow134_meanGapNumeratorChars ++ '/' :: geometryRow134_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_meanGap_before_field"
  err.flush

theorem geometryRow134_meanGap_field :
    geometryRowsJson134.getObjVal? "mean_gap" = .ok (.str geometryRow134_meanGapText) := by rfl

theorem geometryRow134_meanGap_numerator_no_slash :
    geometryRow134_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow134_meanGap_numerator_parse :
    SourceJson.intChars geometryRow134_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow134_meanGap_denominator_parse :
    SourceJson.intChars geometryRow134_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow134_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow134_meanGap_parse :
    parseRational geometryRow134_meanGapText = .ok geometryRowsTyped134.meanGap :=
  original_rational_fraction_of_chars geometryRow134_meanGapNumeratorChars geometryRow134_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow134_meanGap_numerator_no_slash geometryRow134_meanGap_numerator_parse
    geometryRow134_meanGap_denominator_parse geometryRow134_meanGap_denominator_nonzero

theorem geometryRow134_meanGap_read :
    rationalField geometryRowsJson134 "mean_gap" = .ok geometryRowsTyped134.meanGap :=
  original_rationalField_of_string geometryRowsJson134 "mean_gap" geometryRow134_meanGapText
    geometryRowsTyped134.meanGap geometryRow134_meanGap_field geometryRow134_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_meanGap_complete"
  err.flush

noncomputable def geometryRow134_jensenBoundNumeratorChars : List Char := ['5', '8', '7', '5', '8', '8', '4', '5', '0', '7', '3', '4', '7', '6', '2', '7', '8', '6', '9', '0', '7', '7', '0', '7', '6', '1', '6', '7', '5', '5', '0', '4', '6', '3', '4', '9', '2', '5', '4', '3', '6', '1', '6', '3', '3', '8', '1', '3', '1', '0', '3', '4', '0', '4', '4', '5', '6', '0', '9', '5', '2', '8', '1', '1', '8', '7', '4', '1', '6', '1', '1', '1', '4', '7', '4', '0', '7', '9', '0', '8', '7', '7', '5', '7', '3', '8', '8', '9', '5', '8', '4', '7', '6', '0', '6', '6', '5', '8', '9', '3', '5', '5', '4', '6', '8', '7', '5', '0']
noncomputable def geometryRow134_jensenBoundDenominatorChars : List Char := ['1', '6', '6', '3', '5', '7', '8', '9', '1', '3', '6', '1', '8', '1', '2', '6', '4', '5', '3', '5', '7', '5', '4', '6', '2', '0', '5', '9', '0', '9', '2', '4', '2', '4', '2', '7', '3', '7', '7', '1', '7', '4', '8', '3', '4', '7', '7', '4', '1', '0', '6', '8', '9', '4', '4', '2', '8', '8', '7', '6', '7', '9', '4', '0', '5', '8', '5', '9', '0', '2', '4', '4', '4', '3', '3', '3', '0', '8', '9', '0', '1', '7', '5', '2', '6', '9', '8', '5', '6', '1', '0', '3', '7', '0', '2', '3', '8', '2', '1', '9', '5', '3', '4', '0', '9', '2', '7', '6', '1', '5', '1', '8', '4', '3', '5', '1', '1', '3', '1', '6', '2', '0', '4', '6', '7', '1']
noncomputable def geometryRow134_jensenBoundText : String := String.ofList (geometryRow134_jensenBoundNumeratorChars ++ '/' :: geometryRow134_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_jensenBound_before_field"
  err.flush

theorem geometryRow134_jensenBound_field :
    geometryRowsJson134.getObjVal? "jensen_bound" = .ok (.str geometryRow134_jensenBoundText) := by rfl

theorem geometryRow134_jensenBound_numerator_no_slash :
    geometryRow134_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow134_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow134_jensenBoundNumeratorChars = some (587588450734762786907707616755046349254361633813103404456095281187416111474079087757388958476066589355468750 : Int) := by decide +kernel

theorem geometryRow134_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow134_jensenBoundDenominatorChars = some (166357891361812645357546205909242427377174834774106894428876794058590244433308901752698561037023821953409276151843511316204671 : Int) := by decide +kernel

theorem geometryRow134_jensenBound_denominator_nonzero : (166357891361812645357546205909242427377174834774106894428876794058590244433308901752698561037023821953409276151843511316204671 : Int) ≠ 0 := by decide +kernel

theorem geometryRow134_jensenBound_parse :
    parseRational geometryRow134_jensenBoundText = .ok geometryRowsTyped134.jensenBound :=
  original_rational_fraction_of_chars geometryRow134_jensenBoundNumeratorChars geometryRow134_jensenBoundDenominatorChars
    (587588450734762786907707616755046349254361633813103404456095281187416111474079087757388958476066589355468750 : Int) (166357891361812645357546205909242427377174834774106894428876794058590244433308901752698561037023821953409276151843511316204671 : Int)
    geometryRow134_jensenBound_numerator_no_slash geometryRow134_jensenBound_numerator_parse
    geometryRow134_jensenBound_denominator_parse geometryRow134_jensenBound_denominator_nonzero

theorem geometryRow134_jensenBound_read :
    rationalField geometryRowsJson134 "jensen_bound" = .ok geometryRowsTyped134.jensenBound :=
  original_rationalField_of_string geometryRowsJson134 "jensen_bound" geometryRow134_jensenBoundText
    geometryRowsTyped134.jensenBound geometryRow134_jensenBound_field geometryRow134_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_factorMaxima_before"
  err.flush

theorem geometryRow134_factorMaxima_read :
    rationalArrayField geometryRowsJson134 "factor_maxima" = .ok geometryRowsTyped134.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_gapWeightedMeans_before"
  err.flush

theorem geometryRow134_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson134 "gap_weighted_means" = .ok geometryRowsTyped134.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow134_floorChars : List Char := ['2', '7', '9', '8', '3', '9', '7', '6', '5', '2', '5', '0']
noncomputable def geometryRow134_floorText : String := String.ofList geometryRow134_floorChars

theorem geometryRow134_floor_text_read :
    geometryRowsJson134.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow134_floorText := by rfl

theorem geometryRow134_floor_chars_parse :
    SourceJson.intChars geometryRow134_floorChars = some (279839765250 : Int) := by decide +kernel

theorem geometryRow134_floor_parse :
    parseInteger geometryRow134_floorText = .ok geometryRowsTyped134.jensenFloorQ96 := by
  simp only [geometryRow134_floorText, parseInteger, String.toList_ofList, geometryRow134_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_134 :
    decodeGeometryRow geometryRowsJson134 = .ok geometryRowsTyped134 :=
  original_geometryRow_of_fields geometryRowsJson134 geometryRowsTyped134 geometryRow134_floorText
    geometryRow134_simplexId_read geometryRow134_vertexIds_read
    geometryRow134_physicalVolume_read geometryRow134_meanGap_read
    geometryRow134_factorMaxima_read geometryRow134_gapWeightedMeans_read
    geometryRow134_jensenBound_read geometryRow134_floor_text_read geometryRow134_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_134_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson135 : SourceJson :=
  (SimplicesBlock068.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped135 : GeometryRow :=
  { simplexId := 135,
    vertexIds := #[39, 38, 36, 30, 24, 23, 21, 20, 16],
    physicalVolume := ((9049118039614129646558355050843079029747 : ℚ) / (8280353462530867200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484451 : ℚ) / (42000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((39512583391279 : ℚ) / (524012400000000 : ℚ)), ((39610429526299 : ℚ) / (524012400000000 : ℚ)), ((26366932027987 : ℚ) / (174670800000000 : ℚ)), ((43260458527633 : ℚ) / (393009300000000 : ℚ)), ((8810912091557 : ℚ) / (174670800000000 : ℚ)), ((7660255917161 : ℚ) / (174670800000000 : ℚ)), ((700822226983 : ℚ) / (16547760000000 : ℚ)), ((13147738944169 : ℚ) / (314407440000000 : ℚ)), ((64850879828351 : ℚ) / (1572037200000000 : ℚ)), ((64850775025871 : ℚ) / (1572037200000000 : ℚ))],
    jensenBound := ((164303798609045689455004873929096912816771205294827431943586935764799014347473993804946498256160000000000000000000000 : ℚ) / (228794671189872735466296946074312723333087190599026832660055421183980786703636154614354060996946268371614988932167738075528082936940781 : ℚ)),
    jensenFloorQ96 := (56895940758 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_simplexId_before"
  err.flush

theorem geometryRow135_simplexId_read :
    geometryRowsJson135.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped135.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_vertexIds_before"
  err.flush

theorem geometryRow135_vertexIds_read :
    geometryRowsJson135.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped135.vertexIds := by decide +kernel

noncomputable def geometryRow135_physicalVolumeNumeratorChars : List Char := ['9', '0', '4', '9', '1', '1', '8', '0', '3', '9', '6', '1', '4', '1', '2', '9', '6', '4', '6', '5', '5', '8', '3', '5', '5', '0', '5', '0', '8', '4', '3', '0', '7', '9', '0', '2', '9', '7', '4', '7']
noncomputable def geometryRow135_physicalVolumeDenominatorChars : List Char := ['8', '2', '8', '0', '3', '5', '3', '4', '6', '2', '5', '3', '0', '8', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow135_physicalVolumeText : String := String.ofList (geometryRow135_physicalVolumeNumeratorChars ++ '/' :: geometryRow135_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_physicalVolume_before_field"
  err.flush

theorem geometryRow135_physicalVolume_field :
    geometryRowsJson135.getObjVal? "physical_volume" = .ok (.str geometryRow135_physicalVolumeText) := by rfl

theorem geometryRow135_physicalVolume_numerator_no_slash :
    geometryRow135_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow135_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow135_physicalVolumeNumeratorChars = some (9049118039614129646558355050843079029747 : Int) := by decide +kernel

theorem geometryRow135_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow135_physicalVolumeDenominatorChars = some (8280353462530867200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow135_physicalVolume_denominator_nonzero : (8280353462530867200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow135_physicalVolume_parse :
    parseRational geometryRow135_physicalVolumeText = .ok geometryRowsTyped135.physicalVolume :=
  original_rational_fraction_of_chars geometryRow135_physicalVolumeNumeratorChars geometryRow135_physicalVolumeDenominatorChars
    (9049118039614129646558355050843079029747 : Int) (8280353462530867200000000000000000000000000000000000000000000000000 : Int)
    geometryRow135_physicalVolume_numerator_no_slash geometryRow135_physicalVolume_numerator_parse
    geometryRow135_physicalVolume_denominator_parse geometryRow135_physicalVolume_denominator_nonzero

theorem geometryRow135_physicalVolume_read :
    rationalField geometryRowsJson135 "physical_volume" = .ok geometryRowsTyped135.physicalVolume :=
  original_rationalField_of_string geometryRowsJson135 "physical_volume" geometryRow135_physicalVolumeText
    geometryRowsTyped135.physicalVolume geometryRow135_physicalVolume_field geometryRow135_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_physicalVolume_complete"
  err.flush

noncomputable def geometryRow135_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow135_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow135_meanGapText : String := String.ofList (geometryRow135_meanGapNumeratorChars ++ '/' :: geometryRow135_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_meanGap_before_field"
  err.flush

theorem geometryRow135_meanGap_field :
    geometryRowsJson135.getObjVal? "mean_gap" = .ok (.str geometryRow135_meanGapText) := by rfl

theorem geometryRow135_meanGap_numerator_no_slash :
    geometryRow135_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow135_meanGap_numerator_parse :
    SourceJson.intChars geometryRow135_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow135_meanGap_denominator_parse :
    SourceJson.intChars geometryRow135_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow135_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow135_meanGap_parse :
    parseRational geometryRow135_meanGapText = .ok geometryRowsTyped135.meanGap :=
  original_rational_fraction_of_chars geometryRow135_meanGapNumeratorChars geometryRow135_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow135_meanGap_numerator_no_slash geometryRow135_meanGap_numerator_parse
    geometryRow135_meanGap_denominator_parse geometryRow135_meanGap_denominator_nonzero

theorem geometryRow135_meanGap_read :
    rationalField geometryRowsJson135 "mean_gap" = .ok geometryRowsTyped135.meanGap :=
  original_rationalField_of_string geometryRowsJson135 "mean_gap" geometryRow135_meanGapText
    geometryRowsTyped135.meanGap geometryRow135_meanGap_field geometryRow135_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_meanGap_complete"
  err.flush

noncomputable def geometryRow135_jensenBoundNumeratorChars : List Char := ['1', '6', '4', '3', '0', '3', '7', '9', '8', '6', '0', '9', '0', '4', '5', '6', '8', '9', '4', '5', '5', '0', '0', '4', '8', '7', '3', '9', '2', '9', '0', '9', '6', '9', '1', '2', '8', '1', '6', '7', '7', '1', '2', '0', '5', '2', '9', '4', '8', '2', '7', '4', '3', '1', '9', '4', '3', '5', '8', '6', '9', '3', '5', '7', '6', '4', '7', '9', '9', '0', '1', '4', '3', '4', '7', '4', '7', '3', '9', '9', '3', '8', '0', '4', '9', '4', '6', '4', '9', '8', '2', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow135_jensenBoundDenominatorChars : List Char := ['2', '2', '8', '7', '9', '4', '6', '7', '1', '1', '8', '9', '8', '7', '2', '7', '3', '5', '4', '6', '6', '2', '9', '6', '9', '4', '6', '0', '7', '4', '3', '1', '2', '7', '2', '3', '3', '3', '3', '0', '8', '7', '1', '9', '0', '5', '9', '9', '0', '2', '6', '8', '3', '2', '6', '6', '0', '0', '5', '5', '4', '2', '1', '1', '8', '3', '9', '8', '0', '7', '8', '6', '7', '0', '3', '6', '3', '6', '1', '5', '4', '6', '1', '4', '3', '5', '4', '0', '6', '0', '9', '9', '6', '9', '4', '6', '2', '6', '8', '3', '7', '1', '6', '1', '4', '9', '8', '8', '9', '3', '2', '1', '6', '7', '7', '3', '8', '0', '7', '5', '5', '2', '8', '0', '8', '2', '9', '3', '6', '9', '4', '0', '7', '8', '1']
noncomputable def geometryRow135_jensenBoundText : String := String.ofList (geometryRow135_jensenBoundNumeratorChars ++ '/' :: geometryRow135_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_jensenBound_before_field"
  err.flush

theorem geometryRow135_jensenBound_field :
    geometryRowsJson135.getObjVal? "jensen_bound" = .ok (.str geometryRow135_jensenBoundText) := by rfl

theorem geometryRow135_jensenBound_numerator_no_slash :
    geometryRow135_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow135_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow135_jensenBoundNumeratorChars = some (164303798609045689455004873929096912816771205294827431943586935764799014347473993804946498256160000000000000000000000 : Int) := by decide +kernel

theorem geometryRow135_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow135_jensenBoundDenominatorChars = some (228794671189872735466296946074312723333087190599026832660055421183980786703636154614354060996946268371614988932167738075528082936940781 : Int) := by decide +kernel

theorem geometryRow135_jensenBound_denominator_nonzero : (228794671189872735466296946074312723333087190599026832660055421183980786703636154614354060996946268371614988932167738075528082936940781 : Int) ≠ 0 := by decide +kernel

theorem geometryRow135_jensenBound_parse :
    parseRational geometryRow135_jensenBoundText = .ok geometryRowsTyped135.jensenBound :=
  original_rational_fraction_of_chars geometryRow135_jensenBoundNumeratorChars geometryRow135_jensenBoundDenominatorChars
    (164303798609045689455004873929096912816771205294827431943586935764799014347473993804946498256160000000000000000000000 : Int) (228794671189872735466296946074312723333087190599026832660055421183980786703636154614354060996946268371614988932167738075528082936940781 : Int)
    geometryRow135_jensenBound_numerator_no_slash geometryRow135_jensenBound_numerator_parse
    geometryRow135_jensenBound_denominator_parse geometryRow135_jensenBound_denominator_nonzero

theorem geometryRow135_jensenBound_read :
    rationalField geometryRowsJson135 "jensen_bound" = .ok geometryRowsTyped135.jensenBound :=
  original_rationalField_of_string geometryRowsJson135 "jensen_bound" geometryRow135_jensenBoundText
    geometryRowsTyped135.jensenBound geometryRow135_jensenBound_field geometryRow135_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_factorMaxima_before"
  err.flush

theorem geometryRow135_factorMaxima_read :
    rationalArrayField geometryRowsJson135 "factor_maxima" = .ok geometryRowsTyped135.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_gapWeightedMeans_before"
  err.flush

theorem geometryRow135_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson135 "gap_weighted_means" = .ok geometryRowsTyped135.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow135_floorChars : List Char := ['5', '6', '8', '9', '5', '9', '4', '0', '7', '5', '8']
noncomputable def geometryRow135_floorText : String := String.ofList geometryRow135_floorChars

theorem geometryRow135_floor_text_read :
    geometryRowsJson135.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow135_floorText := by rfl

theorem geometryRow135_floor_chars_parse :
    SourceJson.intChars geometryRow135_floorChars = some (56895940758 : Int) := by decide +kernel

theorem geometryRow135_floor_parse :
    parseInteger geometryRow135_floorText = .ok geometryRowsTyped135.jensenFloorQ96 := by
  simp only [geometryRow135_floorText, parseInteger, String.toList_ofList, geometryRow135_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_135 :
    decodeGeometryRow geometryRowsJson135 = .ok geometryRowsTyped135 :=
  original_geometryRow_of_fields geometryRowsJson135 geometryRowsTyped135 geometryRow135_floorText
    geometryRow135_simplexId_read geometryRow135_vertexIds_read
    geometryRow135_physicalVolume_read geometryRow135_meanGap_read
    geometryRow135_factorMaxima_read geometryRow135_gapWeightedMeans_read
    geometryRow135_jensenBound_read geometryRow135_floor_text_read geometryRow135_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_135_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock068 : List SourceJson := [geometryRowsJson134, geometryRowsJson135]
noncomputable def geometryRowsTypedBlock068 : List (GeometryRow) := [geometryRowsTyped134, geometryRowsTyped135]
noncomputable def geometryRowsTypedThroughBlock068 : List (GeometryRow) := geometryRowsTypedThroughBlock067 ++ geometryRowsTypedBlock068

theorem geometry_Rows_block_068_push_eq (acc : List SourceJson) :
    SimplicesBlock068.blockPush acc = [geometryRowsJson135, geometryRowsJson134] ++ acc := by rfl

theorem geometry_Rows_block_068_reverse (acc : List SourceJson) :
    (SimplicesBlock068.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock068 := by
  rw [geometry_Rows_block_068_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_068 :
    geometryRowsJsonBlock068.mapM decodeGeometryRow = .ok geometryRowsTypedBlock068 := by
  simp only [geometryRowsJsonBlock068, geometryRowsTypedBlock068, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_134, decode_geometry_Rows_135]
  rfl

theorem decode_geometry_Rows_through_block_068 :
    SimplicesValue.arrayAcc069.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock068 := by
  change (SimplicesBlock068.blockPush SimplicesValue.arrayAcc068).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_068_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_067, decode_geometry_Rows_block_068]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_068_complete"
  err.flush

#print axioms geometryRow134_simplexId_read
#print axioms geometryRow134_vertexIds_read
#print axioms geometryRow134_physicalVolume_field
#print axioms geometryRow134_physicalVolume_numerator_no_slash
#print axioms geometryRow134_physicalVolume_numerator_parse
#print axioms geometryRow134_physicalVolume_denominator_parse
#print axioms geometryRow134_physicalVolume_denominator_nonzero
#print axioms geometryRow134_physicalVolume_parse
#print axioms geometryRow134_physicalVolume_read
#print axioms geometryRow134_meanGap_field
#print axioms geometryRow134_meanGap_numerator_no_slash
#print axioms geometryRow134_meanGap_numerator_parse
#print axioms geometryRow134_meanGap_denominator_parse
#print axioms geometryRow134_meanGap_denominator_nonzero
#print axioms geometryRow134_meanGap_parse
#print axioms geometryRow134_meanGap_read
#print axioms geometryRow134_jensenBound_field
#print axioms geometryRow134_jensenBound_numerator_no_slash
#print axioms geometryRow134_jensenBound_numerator_parse
#print axioms geometryRow134_jensenBound_denominator_parse
#print axioms geometryRow134_jensenBound_denominator_nonzero
#print axioms geometryRow134_jensenBound_parse
#print axioms geometryRow134_jensenBound_read
#print axioms geometryRow134_factorMaxima_read
#print axioms geometryRow134_gapWeightedMeans_read
#print axioms geometryRow134_floor_text_read
#print axioms geometryRow134_floor_chars_parse
#print axioms geometryRow134_floor_parse
#print axioms decode_geometry_Rows_134
#print axioms geometryRow135_simplexId_read
#print axioms geometryRow135_vertexIds_read
#print axioms geometryRow135_physicalVolume_field
#print axioms geometryRow135_physicalVolume_numerator_no_slash
#print axioms geometryRow135_physicalVolume_numerator_parse
#print axioms geometryRow135_physicalVolume_denominator_parse
#print axioms geometryRow135_physicalVolume_denominator_nonzero
#print axioms geometryRow135_physicalVolume_parse
#print axioms geometryRow135_physicalVolume_read
#print axioms geometryRow135_meanGap_field
#print axioms geometryRow135_meanGap_numerator_no_slash
#print axioms geometryRow135_meanGap_numerator_parse
#print axioms geometryRow135_meanGap_denominator_parse
#print axioms geometryRow135_meanGap_denominator_nonzero
#print axioms geometryRow135_meanGap_parse
#print axioms geometryRow135_meanGap_read
#print axioms geometryRow135_jensenBound_field
#print axioms geometryRow135_jensenBound_numerator_no_slash
#print axioms geometryRow135_jensenBound_numerator_parse
#print axioms geometryRow135_jensenBound_denominator_parse
#print axioms geometryRow135_jensenBound_denominator_nonzero
#print axioms geometryRow135_jensenBound_parse
#print axioms geometryRow135_jensenBound_read
#print axioms geometryRow135_factorMaxima_read
#print axioms geometryRow135_gapWeightedMeans_read
#print axioms geometryRow135_floor_text_read
#print axioms geometryRow135_floor_chars_parse
#print axioms geometryRow135_floor_parse
#print axioms decode_geometry_Rows_135
#print axioms geometry_Rows_block_068_push_eq
#print axioms geometry_Rows_block_068_reverse
#print axioms decode_geometry_Rows_block_068
#print axioms decode_geometry_Rows_through_block_068

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
