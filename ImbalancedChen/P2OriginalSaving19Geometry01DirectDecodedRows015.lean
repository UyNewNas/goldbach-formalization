import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows014

/-! Original simplices typed block 15, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson030 : SourceJson :=
  (SimplicesBlock015.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped030 : GeometryRow :=
  { simplexId := 30,
    vertexIds := #[39, 35, 24, 11, 10, 8, 3, 1, 0],
    physicalVolume := ((2742024631562614976851076642437753 : ℚ) / (793804800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((1548980111347 : ℚ) / (17635800000000 : ℚ)), ((1566807104167 : ℚ) / (17635800000000 : ℚ)), ((578938553183 : ℚ) / (4069800000000 : ℚ)), ((323933361561 : ℚ) / (2939300000000 : ℚ)), ((23659643677 : ℚ) / (389025000000 : ℚ)), ((2665239267331 : ℚ) / (52907400000000 : ℚ)), ((2107856553821 : ℚ) / (52907400000000 : ℚ)), ((1949723343131 : ℚ) / (52907400000000 : ℚ)), ((1802479036481 : ℚ) / (52907400000000 : ℚ)), ((1802468455001 : ℚ) / (52907400000000 : ℚ))],
    jensenBound := ((517311883170028524633604176846845450113476882381126145886105230683655801150574305734375000000000000000000 : ℚ) / (42579774328541678651726766554530636123368233535607517647358569511249003211231851442089171478645078548327160565159577371 : ℚ)),
    jensenFloorQ96 := (962561934549333 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_simplexId_before"
  err.flush

theorem geometryRow030_simplexId_read :
    geometryRowsJson030.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped030.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_vertexIds_before"
  err.flush

theorem geometryRow030_vertexIds_read :
    geometryRowsJson030.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped030.vertexIds := by decide +kernel

noncomputable def geometryRow030_physicalVolumeNumeratorChars : List Char := ['2', '7', '4', '2', '0', '2', '4', '6', '3', '1', '5', '6', '2', '6', '1', '4', '9', '7', '6', '8', '5', '1', '0', '7', '6', '6', '4', '2', '4', '3', '7', '7', '5', '3']
noncomputable def geometryRow030_physicalVolumeDenominatorChars : List Char := ['7', '9', '3', '8', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_physicalVolumeText : String := String.ofList (geometryRow030_physicalVolumeNumeratorChars ++ '/' :: geometryRow030_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_physicalVolume_before_field"
  err.flush

theorem geometryRow030_physicalVolume_field :
    geometryRowsJson030.getObjVal? "physical_volume" = .ok (.str geometryRow030_physicalVolumeText) := by rfl

theorem geometryRow030_physicalVolume_numerator_no_slash :
    geometryRow030_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeNumeratorChars = some (2742024631562614976851076642437753 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeDenominatorChars = some (793804800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_nonzero : (793804800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_physicalVolume_parse :
    parseRational geometryRow030_physicalVolumeText = .ok geometryRowsTyped030.physicalVolume :=
  original_rational_fraction_of_chars geometryRow030_physicalVolumeNumeratorChars geometryRow030_physicalVolumeDenominatorChars
    (2742024631562614976851076642437753 : Int) (793804800000000000000000000000000000000000000000000000000 : Int)
    geometryRow030_physicalVolume_numerator_no_slash geometryRow030_physicalVolume_numerator_parse
    geometryRow030_physicalVolume_denominator_parse geometryRow030_physicalVolume_denominator_nonzero

theorem geometryRow030_physicalVolume_read :
    rationalField geometryRowsJson030 "physical_volume" = .ok geometryRowsTyped030.physicalVolume :=
  original_rationalField_of_string geometryRowsJson030 "physical_volume" geometryRow030_physicalVolumeText
    geometryRowsTyped030.physicalVolume geometryRow030_physicalVolume_field geometryRow030_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_physicalVolume_complete"
  err.flush

noncomputable def geometryRow030_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow030_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_meanGapText : String := String.ofList (geometryRow030_meanGapNumeratorChars ++ '/' :: geometryRow030_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_meanGap_before_field"
  err.flush

theorem geometryRow030_meanGap_field :
    geometryRowsJson030.getObjVal? "mean_gap" = .ok (.str geometryRow030_meanGapText) := by rfl

theorem geometryRow030_meanGap_numerator_no_slash :
    geometryRow030_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_meanGap_numerator_parse :
    SourceJson.intChars geometryRow030_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_parse :
    SourceJson.intChars geometryRow030_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_meanGap_parse :
    parseRational geometryRow030_meanGapText = .ok geometryRowsTyped030.meanGap :=
  original_rational_fraction_of_chars geometryRow030_meanGapNumeratorChars geometryRow030_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow030_meanGap_numerator_no_slash geometryRow030_meanGap_numerator_parse
    geometryRow030_meanGap_denominator_parse geometryRow030_meanGap_denominator_nonzero

theorem geometryRow030_meanGap_read :
    rationalField geometryRowsJson030 "mean_gap" = .ok geometryRowsTyped030.meanGap :=
  original_rationalField_of_string geometryRowsJson030 "mean_gap" geometryRow030_meanGapText
    geometryRowsTyped030.meanGap geometryRow030_meanGap_field geometryRow030_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_meanGap_complete"
  err.flush

noncomputable def geometryRow030_jensenBoundNumeratorChars : List Char := ['5', '1', '7', '3', '1', '1', '8', '8', '3', '1', '7', '0', '0', '2', '8', '5', '2', '4', '6', '3', '3', '6', '0', '4', '1', '7', '6', '8', '4', '6', '8', '4', '5', '4', '5', '0', '1', '1', '3', '4', '7', '6', '8', '8', '2', '3', '8', '1', '1', '2', '6', '1', '4', '5', '8', '8', '6', '1', '0', '5', '2', '3', '0', '6', '8', '3', '6', '5', '5', '8', '0', '1', '1', '5', '0', '5', '7', '4', '3', '0', '5', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_jensenBoundDenominatorChars : List Char := ['4', '2', '5', '7', '9', '7', '7', '4', '3', '2', '8', '5', '4', '1', '6', '7', '8', '6', '5', '1', '7', '2', '6', '7', '6', '6', '5', '5', '4', '5', '3', '0', '6', '3', '6', '1', '2', '3', '3', '6', '8', '2', '3', '3', '5', '3', '5', '6', '0', '7', '5', '1', '7', '6', '4', '7', '3', '5', '8', '5', '6', '9', '5', '1', '1', '2', '4', '9', '0', '0', '3', '2', '1', '1', '2', '3', '1', '8', '5', '1', '4', '4', '2', '0', '8', '9', '1', '7', '1', '4', '7', '8', '6', '4', '5', '0', '7', '8', '5', '4', '8', '3', '2', '7', '1', '6', '0', '5', '6', '5', '1', '5', '9', '5', '7', '7', '3', '7', '1']
noncomputable def geometryRow030_jensenBoundText : String := String.ofList (geometryRow030_jensenBoundNumeratorChars ++ '/' :: geometryRow030_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_jensenBound_before_field"
  err.flush

theorem geometryRow030_jensenBound_field :
    geometryRowsJson030.getObjVal? "jensen_bound" = .ok (.str geometryRow030_jensenBoundText) := by rfl

theorem geometryRow030_jensenBound_numerator_no_slash :
    geometryRow030_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow030_jensenBoundNumeratorChars = some (517311883170028524633604176846845450113476882381126145886105230683655801150574305734375000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow030_jensenBoundDenominatorChars = some (42579774328541678651726766554530636123368233535607517647358569511249003211231851442089171478645078548327160565159577371 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_nonzero : (42579774328541678651726766554530636123368233535607517647358569511249003211231851442089171478645078548327160565159577371 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_jensenBound_parse :
    parseRational geometryRow030_jensenBoundText = .ok geometryRowsTyped030.jensenBound :=
  original_rational_fraction_of_chars geometryRow030_jensenBoundNumeratorChars geometryRow030_jensenBoundDenominatorChars
    (517311883170028524633604176846845450113476882381126145886105230683655801150574305734375000000000000000000 : Int) (42579774328541678651726766554530636123368233535607517647358569511249003211231851442089171478645078548327160565159577371 : Int)
    geometryRow030_jensenBound_numerator_no_slash geometryRow030_jensenBound_numerator_parse
    geometryRow030_jensenBound_denominator_parse geometryRow030_jensenBound_denominator_nonzero

theorem geometryRow030_jensenBound_read :
    rationalField geometryRowsJson030 "jensen_bound" = .ok geometryRowsTyped030.jensenBound :=
  original_rationalField_of_string geometryRowsJson030 "jensen_bound" geometryRow030_jensenBoundText
    geometryRowsTyped030.jensenBound geometryRow030_jensenBound_field geometryRow030_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_factorMaxima_before"
  err.flush

theorem geometryRow030_factorMaxima_read :
    rationalArrayField geometryRowsJson030 "factor_maxima" = .ok geometryRowsTyped030.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_gapWeightedMeans_before"
  err.flush

theorem geometryRow030_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson030 "gap_weighted_means" = .ok geometryRowsTyped030.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow030_floorChars : List Char := ['9', '6', '2', '5', '6', '1', '9', '3', '4', '5', '4', '9', '3', '3', '3']
noncomputable def geometryRow030_floorText : String := String.ofList geometryRow030_floorChars

theorem geometryRow030_floor_text_read :
    geometryRowsJson030.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow030_floorText := by rfl

theorem geometryRow030_floor_chars_parse :
    SourceJson.intChars geometryRow030_floorChars = some (962561934549333 : Int) := by decide +kernel

theorem geometryRow030_floor_parse :
    parseInteger geometryRow030_floorText = .ok geometryRowsTyped030.jensenFloorQ96 := by
  simp only [geometryRow030_floorText, parseInteger, String.toList_ofList, geometryRow030_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_030 :
    decodeGeometryRow geometryRowsJson030 = .ok geometryRowsTyped030 :=
  original_geometryRow_of_fields geometryRowsJson030 geometryRowsTyped030 geometryRow030_floorText
    geometryRow030_simplexId_read geometryRow030_vertexIds_read
    geometryRow030_physicalVolume_read geometryRow030_meanGap_read
    geometryRow030_factorMaxima_read geometryRow030_gapWeightedMeans_read
    geometryRow030_jensenBound_read geometryRow030_floor_text_read geometryRow030_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_030_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson031 : SourceJson :=
  (SimplicesBlock015.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped031 : GeometryRow :=
  { simplexId := 31,
    vertexIds := #[39, 35, 24, 11, 10, 8, 3, 2, 0],
    physicalVolume := ((86564318759135651876197246534987191017 : ℚ) / (4762828800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((1872339587747019739 : ℚ) / (21647148369600000000 : ℚ)), ((93386002367155651981 : ℚ) / (1060710270110400000000 : ℚ)), ((34886379607590389759 : ℚ) / (244779293102400000000 : ℚ)), ((19767641799003900873 : ℚ) / (176785045018400000000 : ℚ)), ((11400652734220570073 : ℚ) / (187184165313600000000 : ℚ)), ((156029268923976875953 : ℚ) / (3182130810331200000000 : ℚ)), ((127065883239274687553 : ℚ) / (3182130810331200000000 : ℚ)), ((117554915739959958833 : ℚ) / (3182130810331200000000 : ℚ)), ((109246013828871951443 : ℚ) / (3182130810331200000000 : ℚ)), ((107559922183535622173 : ℚ) / (3182130810331200000000 : ℚ))],
    jensenBound := ((5283418023073367080130416969783464851562437198287771542945480947446236349682313287913382844450389491799421340813999210289466666523590240274603349195363794812928000000000000000000000000 : ℚ) / (39339320613537143167996668973172546410463715428142211928864323534412673580271036417179351834312303693316976627240694458336419702948060656099335159887622597704993142572968862315094699696622640531 : ℚ)),
    jensenFloorQ96 := (10640638812120361930 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_simplexId_before"
  err.flush

theorem geometryRow031_simplexId_read :
    geometryRowsJson031.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped031.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_vertexIds_before"
  err.flush

theorem geometryRow031_vertexIds_read :
    geometryRowsJson031.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped031.vertexIds := by decide +kernel

noncomputable def geometryRow031_physicalVolumeNumeratorChars : List Char := ['8', '6', '5', '6', '4', '3', '1', '8', '7', '5', '9', '1', '3', '5', '6', '5', '1', '8', '7', '6', '1', '9', '7', '2', '4', '6', '5', '3', '4', '9', '8', '7', '1', '9', '1', '0', '1', '7']
noncomputable def geometryRow031_physicalVolumeDenominatorChars : List Char := ['4', '7', '6', '2', '8', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_physicalVolumeText : String := String.ofList (geometryRow031_physicalVolumeNumeratorChars ++ '/' :: geometryRow031_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_physicalVolume_before_field"
  err.flush

theorem geometryRow031_physicalVolume_field :
    geometryRowsJson031.getObjVal? "physical_volume" = .ok (.str geometryRow031_physicalVolumeText) := by rfl

theorem geometryRow031_physicalVolume_numerator_no_slash :
    geometryRow031_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeNumeratorChars = some (86564318759135651876197246534987191017 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeDenominatorChars = some (4762828800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_nonzero : (4762828800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_physicalVolume_parse :
    parseRational geometryRow031_physicalVolumeText = .ok geometryRowsTyped031.physicalVolume :=
  original_rational_fraction_of_chars geometryRow031_physicalVolumeNumeratorChars geometryRow031_physicalVolumeDenominatorChars
    (86564318759135651876197246534987191017 : Int) (4762828800000000000000000000000000000000000000000000000000 : Int)
    geometryRow031_physicalVolume_numerator_no_slash geometryRow031_physicalVolume_numerator_parse
    geometryRow031_physicalVolume_denominator_parse geometryRow031_physicalVolume_denominator_nonzero

theorem geometryRow031_physicalVolume_read :
    rationalField geometryRowsJson031 "physical_volume" = .ok geometryRowsTyped031.physicalVolume :=
  original_rationalField_of_string geometryRowsJson031 "physical_volume" geometryRow031_physicalVolumeText
    geometryRowsTyped031.physicalVolume geometryRow031_physicalVolume_field geometryRow031_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_physicalVolume_complete"
  err.flush

noncomputable def geometryRow031_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow031_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow031_meanGapText : String := String.ofList (geometryRow031_meanGapNumeratorChars ++ '/' :: geometryRow031_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_meanGap_before_field"
  err.flush

theorem geometryRow031_meanGap_field :
    geometryRowsJson031.getObjVal? "mean_gap" = .ok (.str geometryRow031_meanGapText) := by rfl

theorem geometryRow031_meanGap_numerator_no_slash :
    geometryRow031_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_meanGap_numerator_parse :
    SourceJson.intChars geometryRow031_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_parse :
    SourceJson.intChars geometryRow031_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_meanGap_parse :
    parseRational geometryRow031_meanGapText = .ok geometryRowsTyped031.meanGap :=
  original_rational_fraction_of_chars geometryRow031_meanGapNumeratorChars geometryRow031_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow031_meanGap_numerator_no_slash geometryRow031_meanGap_numerator_parse
    geometryRow031_meanGap_denominator_parse geometryRow031_meanGap_denominator_nonzero

theorem geometryRow031_meanGap_read :
    rationalField geometryRowsJson031 "mean_gap" = .ok geometryRowsTyped031.meanGap :=
  original_rationalField_of_string geometryRowsJson031 "mean_gap" geometryRow031_meanGapText
    geometryRowsTyped031.meanGap geometryRow031_meanGap_field geometryRow031_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_meanGap_complete"
  err.flush

noncomputable def geometryRow031_jensenBoundNumeratorChars : List Char := ['5', '2', '8', '3', '4', '1', '8', '0', '2', '3', '0', '7', '3', '3', '6', '7', '0', '8', '0', '1', '3', '0', '4', '1', '6', '9', '6', '9', '7', '8', '3', '4', '6', '4', '8', '5', '1', '5', '6', '2', '4', '3', '7', '1', '9', '8', '2', '8', '7', '7', '7', '1', '5', '4', '2', '9', '4', '5', '4', '8', '0', '9', '4', '7', '4', '4', '6', '2', '3', '6', '3', '4', '9', '6', '8', '2', '3', '1', '3', '2', '8', '7', '9', '1', '3', '3', '8', '2', '8', '4', '4', '4', '5', '0', '3', '8', '9', '4', '9', '1', '7', '9', '9', '4', '2', '1', '3', '4', '0', '8', '1', '3', '9', '9', '9', '2', '1', '0', '2', '8', '9', '4', '6', '6', '6', '6', '6', '5', '2', '3', '5', '9', '0', '2', '4', '0', '2', '7', '4', '6', '0', '3', '3', '4', '9', '1', '9', '5', '3', '6', '3', '7', '9', '4', '8', '1', '2', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_jensenBoundDenominatorChars : List Char := ['3', '9', '3', '3', '9', '3', '2', '0', '6', '1', '3', '5', '3', '7', '1', '4', '3', '1', '6', '7', '9', '9', '6', '6', '6', '8', '9', '7', '3', '1', '7', '2', '5', '4', '6', '4', '1', '0', '4', '6', '3', '7', '1', '5', '4', '2', '8', '1', '4', '2', '2', '1', '1', '9', '2', '8', '8', '6', '4', '3', '2', '3', '5', '3', '4', '4', '1', '2', '6', '7', '3', '5', '8', '0', '2', '7', '1', '0', '3', '6', '4', '1', '7', '1', '7', '9', '3', '5', '1', '8', '3', '4', '3', '1', '2', '3', '0', '3', '6', '9', '3', '3', '1', '6', '9', '7', '6', '6', '2', '7', '2', '4', '0', '6', '9', '4', '4', '5', '8', '3', '3', '6', '4', '1', '9', '7', '0', '2', '9', '4', '8', '0', '6', '0', '6', '5', '6', '0', '9', '9', '3', '3', '5', '1', '5', '9', '8', '8', '7', '6', '2', '2', '5', '9', '7', '7', '0', '4', '9', '9', '3', '1', '4', '2', '5', '7', '2', '9', '6', '8', '8', '6', '2', '3', '1', '5', '0', '9', '4', '6', '9', '9', '6', '9', '6', '6', '2', '2', '6', '4', '0', '5', '3', '1']
noncomputable def geometryRow031_jensenBoundText : String := String.ofList (geometryRow031_jensenBoundNumeratorChars ++ '/' :: geometryRow031_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_jensenBound_before_field"
  err.flush

theorem geometryRow031_jensenBound_field :
    geometryRowsJson031.getObjVal? "jensen_bound" = .ok (.str geometryRow031_jensenBoundText) := by rfl

theorem geometryRow031_jensenBound_numerator_no_slash :
    geometryRow031_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow031_jensenBoundNumeratorChars = some (5283418023073367080130416969783464851562437198287771542945480947446236349682313287913382844450389491799421340813999210289466666523590240274603349195363794812928000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow031_jensenBoundDenominatorChars = some (39339320613537143167996668973172546410463715428142211928864323534412673580271036417179351834312303693316976627240694458336419702948060656099335159887622597704993142572968862315094699696622640531 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_nonzero : (39339320613537143167996668973172546410463715428142211928864323534412673580271036417179351834312303693316976627240694458336419702948060656099335159887622597704993142572968862315094699696622640531 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_jensenBound_parse :
    parseRational geometryRow031_jensenBoundText = .ok geometryRowsTyped031.jensenBound :=
  original_rational_fraction_of_chars geometryRow031_jensenBoundNumeratorChars geometryRow031_jensenBoundDenominatorChars
    (5283418023073367080130416969783464851562437198287771542945480947446236349682313287913382844450389491799421340813999210289466666523590240274603349195363794812928000000000000000000000000 : Int) (39339320613537143167996668973172546410463715428142211928864323534412673580271036417179351834312303693316976627240694458336419702948060656099335159887622597704993142572968862315094699696622640531 : Int)
    geometryRow031_jensenBound_numerator_no_slash geometryRow031_jensenBound_numerator_parse
    geometryRow031_jensenBound_denominator_parse geometryRow031_jensenBound_denominator_nonzero

theorem geometryRow031_jensenBound_read :
    rationalField geometryRowsJson031 "jensen_bound" = .ok geometryRowsTyped031.jensenBound :=
  original_rationalField_of_string geometryRowsJson031 "jensen_bound" geometryRow031_jensenBoundText
    geometryRowsTyped031.jensenBound geometryRow031_jensenBound_field geometryRow031_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_factorMaxima_before"
  err.flush

theorem geometryRow031_factorMaxima_read :
    rationalArrayField geometryRowsJson031 "factor_maxima" = .ok geometryRowsTyped031.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_gapWeightedMeans_before"
  err.flush

theorem geometryRow031_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson031 "gap_weighted_means" = .ok geometryRowsTyped031.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow031_floorChars : List Char := ['1', '0', '6', '4', '0', '6', '3', '8', '8', '1', '2', '1', '2', '0', '3', '6', '1', '9', '3', '0']
noncomputable def geometryRow031_floorText : String := String.ofList geometryRow031_floorChars

theorem geometryRow031_floor_text_read :
    geometryRowsJson031.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow031_floorText := by rfl

theorem geometryRow031_floor_chars_parse :
    SourceJson.intChars geometryRow031_floorChars = some (10640638812120361930 : Int) := by decide +kernel

theorem geometryRow031_floor_parse :
    parseInteger geometryRow031_floorText = .ok geometryRowsTyped031.jensenFloorQ96 := by
  simp only [geometryRow031_floorText, parseInteger, String.toList_ofList, geometryRow031_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_031 :
    decodeGeometryRow geometryRowsJson031 = .ok geometryRowsTyped031 :=
  original_geometryRow_of_fields geometryRowsJson031 geometryRowsTyped031 geometryRow031_floorText
    geometryRow031_simplexId_read geometryRow031_vertexIds_read
    geometryRow031_physicalVolume_read geometryRow031_meanGap_read
    geometryRow031_factorMaxima_read geometryRow031_gapWeightedMeans_read
    geometryRow031_jensenBound_read geometryRow031_floor_text_read geometryRow031_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_031_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock015 : List SourceJson := [geometryRowsJson030, geometryRowsJson031]
noncomputable def geometryRowsTypedBlock015 : List (GeometryRow) := [geometryRowsTyped030, geometryRowsTyped031]
noncomputable def geometryRowsTypedThroughBlock015 : List (GeometryRow) := geometryRowsTypedThroughBlock014 ++ geometryRowsTypedBlock015

theorem geometry_Rows_block_015_push_eq (acc : List SourceJson) :
    SimplicesBlock015.blockPush acc = [geometryRowsJson031, geometryRowsJson030] ++ acc := by rfl

theorem geometry_Rows_block_015_reverse (acc : List SourceJson) :
    (SimplicesBlock015.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock015 := by
  rw [geometry_Rows_block_015_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_015 :
    geometryRowsJsonBlock015.mapM decodeGeometryRow = .ok geometryRowsTypedBlock015 := by
  simp only [geometryRowsJsonBlock015, geometryRowsTypedBlock015, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_030, decode_geometry_Rows_031]
  rfl

theorem decode_geometry_Rows_through_block_015 :
    SimplicesValue.arrayAcc016.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock015 := by
  change (SimplicesBlock015.blockPush SimplicesValue.arrayAcc015).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_015_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_014, decode_geometry_Rows_block_015]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_015_complete"
  err.flush

#print axioms geometryRow030_simplexId_read
#print axioms geometryRow030_vertexIds_read
#print axioms geometryRow030_physicalVolume_field
#print axioms geometryRow030_physicalVolume_numerator_no_slash
#print axioms geometryRow030_physicalVolume_numerator_parse
#print axioms geometryRow030_physicalVolume_denominator_parse
#print axioms geometryRow030_physicalVolume_denominator_nonzero
#print axioms geometryRow030_physicalVolume_parse
#print axioms geometryRow030_physicalVolume_read
#print axioms geometryRow030_meanGap_field
#print axioms geometryRow030_meanGap_numerator_no_slash
#print axioms geometryRow030_meanGap_numerator_parse
#print axioms geometryRow030_meanGap_denominator_parse
#print axioms geometryRow030_meanGap_denominator_nonzero
#print axioms geometryRow030_meanGap_parse
#print axioms geometryRow030_meanGap_read
#print axioms geometryRow030_jensenBound_field
#print axioms geometryRow030_jensenBound_numerator_no_slash
#print axioms geometryRow030_jensenBound_numerator_parse
#print axioms geometryRow030_jensenBound_denominator_parse
#print axioms geometryRow030_jensenBound_denominator_nonzero
#print axioms geometryRow030_jensenBound_parse
#print axioms geometryRow030_jensenBound_read
#print axioms geometryRow030_factorMaxima_read
#print axioms geometryRow030_gapWeightedMeans_read
#print axioms geometryRow030_floor_text_read
#print axioms geometryRow030_floor_chars_parse
#print axioms geometryRow030_floor_parse
#print axioms decode_geometry_Rows_030
#print axioms geometryRow031_simplexId_read
#print axioms geometryRow031_vertexIds_read
#print axioms geometryRow031_physicalVolume_field
#print axioms geometryRow031_physicalVolume_numerator_no_slash
#print axioms geometryRow031_physicalVolume_numerator_parse
#print axioms geometryRow031_physicalVolume_denominator_parse
#print axioms geometryRow031_physicalVolume_denominator_nonzero
#print axioms geometryRow031_physicalVolume_parse
#print axioms geometryRow031_physicalVolume_read
#print axioms geometryRow031_meanGap_field
#print axioms geometryRow031_meanGap_numerator_no_slash
#print axioms geometryRow031_meanGap_numerator_parse
#print axioms geometryRow031_meanGap_denominator_parse
#print axioms geometryRow031_meanGap_denominator_nonzero
#print axioms geometryRow031_meanGap_parse
#print axioms geometryRow031_meanGap_read
#print axioms geometryRow031_jensenBound_field
#print axioms geometryRow031_jensenBound_numerator_no_slash
#print axioms geometryRow031_jensenBound_numerator_parse
#print axioms geometryRow031_jensenBound_denominator_parse
#print axioms geometryRow031_jensenBound_denominator_nonzero
#print axioms geometryRow031_jensenBound_parse
#print axioms geometryRow031_jensenBound_read
#print axioms geometryRow031_factorMaxima_read
#print axioms geometryRow031_gapWeightedMeans_read
#print axioms geometryRow031_floor_text_read
#print axioms geometryRow031_floor_chars_parse
#print axioms geometryRow031_floor_parse
#print axioms decode_geometry_Rows_031
#print axioms geometry_Rows_block_015_push_eq
#print axioms geometry_Rows_block_015_reverse
#print axioms decode_geometry_Rows_block_015
#print axioms decode_geometry_Rows_through_block_015

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
