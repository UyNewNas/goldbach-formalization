import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows059

/-! Original simplices typed block 60, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson118 : SourceJson :=
  (SimplicesBlock060.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped118 : GeometryRow :=
  { simplexId := 118,
    vertexIds := #[39, 37, 31, 30, 24, 23, 21, 20, 16],
    physicalVolume := ((103156623822926042034154138084213857777103 : ℚ) / (94396029472851886080000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((29928282643317 : ℚ) / (407565200000000 : ℚ)), ((30004385192777 : ℚ) / (407565200000000 : ℚ)), ((1643036597112011 : ℚ) / (11004260400000000 : ℚ)), ((146891574683923 : ℚ) / (1375532550000000 : ℚ)), ((540626373078331 : ℚ) / (11004260400000000 : ℚ)), ((500676243432313 : ℚ) / (11004260400000000 : ℚ)), ((188743431421 : ℚ) / (4290160000000 : ℚ)), ((10627799637713 : ℚ) / (244539120000000 : ℚ)), ((52448638520483 : ℚ) / (1222695600000000 : ℚ)), ((52448393981363 : ℚ) / (1222695600000000 : ℚ))],
    jensenBound := ((217396402359209456884371851836882686742145717155602692028344621773482663653892855712216638800000000000000000000000 : ℚ) / (324982275590612940721527637884190146013017963910910878917617567561301122655779073638403237899820458643811766941157161688821394847229 : ℚ)),
    jensenFloorQ96 := (52999559636 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_simplexId_before"
  err.flush

theorem geometryRow118_simplexId_read :
    geometryRowsJson118.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped118.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_vertexIds_before"
  err.flush

theorem geometryRow118_vertexIds_read :
    geometryRowsJson118.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped118.vertexIds := by decide +kernel

noncomputable def geometryRow118_physicalVolumeNumeratorChars : List Char := ['1', '0', '3', '1', '5', '6', '6', '2', '3', '8', '2', '2', '9', '2', '6', '0', '4', '2', '0', '3', '4', '1', '5', '4', '1', '3', '8', '0', '8', '4', '2', '1', '3', '8', '5', '7', '7', '7', '7', '1', '0', '3']
noncomputable def geometryRow118_physicalVolumeDenominatorChars : List Char := ['9', '4', '3', '9', '6', '0', '2', '9', '4', '7', '2', '8', '5', '1', '8', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow118_physicalVolumeText : String := String.ofList (geometryRow118_physicalVolumeNumeratorChars ++ '/' :: geometryRow118_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_physicalVolume_before_field"
  err.flush

theorem geometryRow118_physicalVolume_field :
    geometryRowsJson118.getObjVal? "physical_volume" = .ok (.str geometryRow118_physicalVolumeText) := by rfl

theorem geometryRow118_physicalVolume_numerator_no_slash :
    geometryRow118_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow118_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow118_physicalVolumeNumeratorChars = some (103156623822926042034154138084213857777103 : Int) := by decide +kernel

theorem geometryRow118_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow118_physicalVolumeDenominatorChars = some (94396029472851886080000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow118_physicalVolume_denominator_nonzero : (94396029472851886080000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow118_physicalVolume_parse :
    parseRational geometryRow118_physicalVolumeText = .ok geometryRowsTyped118.physicalVolume :=
  original_rational_fraction_of_chars geometryRow118_physicalVolumeNumeratorChars geometryRow118_physicalVolumeDenominatorChars
    (103156623822926042034154138084213857777103 : Int) (94396029472851886080000000000000000000000000000000000000000000000000 : Int)
    geometryRow118_physicalVolume_numerator_no_slash geometryRow118_physicalVolume_numerator_parse
    geometryRow118_physicalVolume_denominator_parse geometryRow118_physicalVolume_denominator_nonzero

theorem geometryRow118_physicalVolume_read :
    rationalField geometryRowsJson118 "physical_volume" = .ok geometryRowsTyped118.physicalVolume :=
  original_rationalField_of_string geometryRowsJson118 "physical_volume" geometryRow118_physicalVolumeText
    geometryRowsTyped118.physicalVolume geometryRow118_physicalVolume_field geometryRow118_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_physicalVolume_complete"
  err.flush

noncomputable def geometryRow118_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow118_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow118_meanGapText : String := String.ofList (geometryRow118_meanGapNumeratorChars ++ '/' :: geometryRow118_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_meanGap_before_field"
  err.flush

theorem geometryRow118_meanGap_field :
    geometryRowsJson118.getObjVal? "mean_gap" = .ok (.str geometryRow118_meanGapText) := by rfl

theorem geometryRow118_meanGap_numerator_no_slash :
    geometryRow118_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow118_meanGap_numerator_parse :
    SourceJson.intChars geometryRow118_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow118_meanGap_denominator_parse :
    SourceJson.intChars geometryRow118_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow118_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow118_meanGap_parse :
    parseRational geometryRow118_meanGapText = .ok geometryRowsTyped118.meanGap :=
  original_rational_fraction_of_chars geometryRow118_meanGapNumeratorChars geometryRow118_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow118_meanGap_numerator_no_slash geometryRow118_meanGap_numerator_parse
    geometryRow118_meanGap_denominator_parse geometryRow118_meanGap_denominator_nonzero

theorem geometryRow118_meanGap_read :
    rationalField geometryRowsJson118 "mean_gap" = .ok geometryRowsTyped118.meanGap :=
  original_rationalField_of_string geometryRowsJson118 "mean_gap" geometryRow118_meanGapText
    geometryRowsTyped118.meanGap geometryRow118_meanGap_field geometryRow118_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_meanGap_complete"
  err.flush

noncomputable def geometryRow118_jensenBoundNumeratorChars : List Char := ['2', '1', '7', '3', '9', '6', '4', '0', '2', '3', '5', '9', '2', '0', '9', '4', '5', '6', '8', '8', '4', '3', '7', '1', '8', '5', '1', '8', '3', '6', '8', '8', '2', '6', '8', '6', '7', '4', '2', '1', '4', '5', '7', '1', '7', '1', '5', '5', '6', '0', '2', '6', '9', '2', '0', '2', '8', '3', '4', '4', '6', '2', '1', '7', '7', '3', '4', '8', '2', '6', '6', '3', '6', '5', '3', '8', '9', '2', '8', '5', '5', '7', '1', '2', '2', '1', '6', '6', '3', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow118_jensenBoundDenominatorChars : List Char := ['3', '2', '4', '9', '8', '2', '2', '7', '5', '5', '9', '0', '6', '1', '2', '9', '4', '0', '7', '2', '1', '5', '2', '7', '6', '3', '7', '8', '8', '4', '1', '9', '0', '1', '4', '6', '0', '1', '3', '0', '1', '7', '9', '6', '3', '9', '1', '0', '9', '1', '0', '8', '7', '8', '9', '1', '7', '6', '1', '7', '5', '6', '7', '5', '6', '1', '3', '0', '1', '1', '2', '2', '6', '5', '5', '7', '7', '9', '0', '7', '3', '6', '3', '8', '4', '0', '3', '2', '3', '7', '8', '9', '9', '8', '2', '0', '4', '5', '8', '6', '4', '3', '8', '1', '1', '7', '6', '6', '9', '4', '1', '1', '5', '7', '1', '6', '1', '6', '8', '8', '8', '2', '1', '3', '9', '4', '8', '4', '7', '2', '2', '9']
noncomputable def geometryRow118_jensenBoundText : String := String.ofList (geometryRow118_jensenBoundNumeratorChars ++ '/' :: geometryRow118_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_jensenBound_before_field"
  err.flush

theorem geometryRow118_jensenBound_field :
    geometryRowsJson118.getObjVal? "jensen_bound" = .ok (.str geometryRow118_jensenBoundText) := by rfl

theorem geometryRow118_jensenBound_numerator_no_slash :
    geometryRow118_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow118_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow118_jensenBoundNumeratorChars = some (217396402359209456884371851836882686742145717155602692028344621773482663653892855712216638800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow118_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow118_jensenBoundDenominatorChars = some (324982275590612940721527637884190146013017963910910878917617567561301122655779073638403237899820458643811766941157161688821394847229 : Int) := by decide +kernel

theorem geometryRow118_jensenBound_denominator_nonzero : (324982275590612940721527637884190146013017963910910878917617567561301122655779073638403237899820458643811766941157161688821394847229 : Int) ≠ 0 := by decide +kernel

theorem geometryRow118_jensenBound_parse :
    parseRational geometryRow118_jensenBoundText = .ok geometryRowsTyped118.jensenBound :=
  original_rational_fraction_of_chars geometryRow118_jensenBoundNumeratorChars geometryRow118_jensenBoundDenominatorChars
    (217396402359209456884371851836882686742145717155602692028344621773482663653892855712216638800000000000000000000000 : Int) (324982275590612940721527637884190146013017963910910878917617567561301122655779073638403237899820458643811766941157161688821394847229 : Int)
    geometryRow118_jensenBound_numerator_no_slash geometryRow118_jensenBound_numerator_parse
    geometryRow118_jensenBound_denominator_parse geometryRow118_jensenBound_denominator_nonzero

theorem geometryRow118_jensenBound_read :
    rationalField geometryRowsJson118 "jensen_bound" = .ok geometryRowsTyped118.jensenBound :=
  original_rationalField_of_string geometryRowsJson118 "jensen_bound" geometryRow118_jensenBoundText
    geometryRowsTyped118.jensenBound geometryRow118_jensenBound_field geometryRow118_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_factorMaxima_before"
  err.flush

theorem geometryRow118_factorMaxima_read :
    rationalArrayField geometryRowsJson118 "factor_maxima" = .ok geometryRowsTyped118.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_gapWeightedMeans_before"
  err.flush

theorem geometryRow118_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson118 "gap_weighted_means" = .ok geometryRowsTyped118.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow118_floorChars : List Char := ['5', '2', '9', '9', '9', '5', '5', '9', '6', '3', '6']
noncomputable def geometryRow118_floorText : String := String.ofList geometryRow118_floorChars

theorem geometryRow118_floor_text_read :
    geometryRowsJson118.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow118_floorText := by rfl

theorem geometryRow118_floor_chars_parse :
    SourceJson.intChars geometryRow118_floorChars = some (52999559636 : Int) := by decide +kernel

theorem geometryRow118_floor_parse :
    parseInteger geometryRow118_floorText = .ok geometryRowsTyped118.jensenFloorQ96 := by
  simp only [geometryRow118_floorText, parseInteger, String.toList_ofList, geometryRow118_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_118 :
    decodeGeometryRow geometryRowsJson118 = .ok geometryRowsTyped118 :=
  original_geometryRow_of_fields geometryRowsJson118 geometryRowsTyped118 geometryRow118_floorText
    geometryRow118_simplexId_read geometryRow118_vertexIds_read
    geometryRow118_physicalVolume_read geometryRow118_meanGap_read
    geometryRow118_factorMaxima_read geometryRow118_gapWeightedMeans_read
    geometryRow118_jensenBound_read geometryRow118_floor_text_read geometryRow118_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_118_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson119 : SourceJson :=
  (SimplicesBlock060.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped119 : GeometryRow :=
  { simplexId := 119,
    vertexIds := #[39, 38, 34, 29, 28, 25, 13, 3, 1],
    physicalVolume := ((138716328733317216159234061153292126294581 : ℚ) / (85579887594700800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2386877858047 : ℚ) / (27988800000000 : ℚ)), ((2415170089567 : ℚ) / (27988800000000 : ℚ)), ((98244225299 : ℚ) / (666400000000 : ℚ)), ((3315898835761 : ℚ) / (27988800000000 : ℚ)), ((16214679421 : ℚ) / (235200000000 : ℚ)), ((211235249427 : ℚ) / (4664800000000 : ℚ)), ((568375127849 : ℚ) / (15993600000000 : ℚ)), ((535191714859 : ℚ) / (15993600000000 : ℚ)), ((289000311119 : ℚ) / (9329600000000 : ℚ)), ((866999067437 : ℚ) / (27988800000000 : ℚ))],
    jensenBound := ((899709117135743964972055522847215884922069906459084022043727491108944528408576000000000000000000000000 : ℚ) / (113135856772704810455498842823424957608589054321544709405264243389008484653323023439735553598025006223852582450648531 : ℚ)),
    jensenFloorQ96 := (630059312594462 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_simplexId_before"
  err.flush

theorem geometryRow119_simplexId_read :
    geometryRowsJson119.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped119.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_vertexIds_before"
  err.flush

theorem geometryRow119_vertexIds_read :
    geometryRowsJson119.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped119.vertexIds := by decide +kernel

noncomputable def geometryRow119_physicalVolumeNumeratorChars : List Char := ['1', '3', '8', '7', '1', '6', '3', '2', '8', '7', '3', '3', '3', '1', '7', '2', '1', '6', '1', '5', '9', '2', '3', '4', '0', '6', '1', '1', '5', '3', '2', '9', '2', '1', '2', '6', '2', '9', '4', '5', '8', '1']
noncomputable def geometryRow119_physicalVolumeDenominatorChars : List Char := ['8', '5', '5', '7', '9', '8', '8', '7', '5', '9', '4', '7', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow119_physicalVolumeText : String := String.ofList (geometryRow119_physicalVolumeNumeratorChars ++ '/' :: geometryRow119_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_physicalVolume_before_field"
  err.flush

theorem geometryRow119_physicalVolume_field :
    geometryRowsJson119.getObjVal? "physical_volume" = .ok (.str geometryRow119_physicalVolumeText) := by rfl

theorem geometryRow119_physicalVolume_numerator_no_slash :
    geometryRow119_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow119_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow119_physicalVolumeNumeratorChars = some (138716328733317216159234061153292126294581 : Int) := by decide +kernel

theorem geometryRow119_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow119_physicalVolumeDenominatorChars = some (85579887594700800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow119_physicalVolume_denominator_nonzero : (85579887594700800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow119_physicalVolume_parse :
    parseRational geometryRow119_physicalVolumeText = .ok geometryRowsTyped119.physicalVolume :=
  original_rational_fraction_of_chars geometryRow119_physicalVolumeNumeratorChars geometryRow119_physicalVolumeDenominatorChars
    (138716328733317216159234061153292126294581 : Int) (85579887594700800000000000000000000000000000000000000000000000000 : Int)
    geometryRow119_physicalVolume_numerator_no_slash geometryRow119_physicalVolume_numerator_parse
    geometryRow119_physicalVolume_denominator_parse geometryRow119_physicalVolume_denominator_nonzero

theorem geometryRow119_physicalVolume_read :
    rationalField geometryRowsJson119 "physical_volume" = .ok geometryRowsTyped119.physicalVolume :=
  original_rationalField_of_string geometryRowsJson119 "physical_volume" geometryRow119_physicalVolumeText
    geometryRowsTyped119.physicalVolume geometryRow119_physicalVolume_field geometryRow119_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_physicalVolume_complete"
  err.flush

noncomputable def geometryRow119_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow119_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow119_meanGapText : String := String.ofList (geometryRow119_meanGapNumeratorChars ++ '/' :: geometryRow119_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_meanGap_before_field"
  err.flush

theorem geometryRow119_meanGap_field :
    geometryRowsJson119.getObjVal? "mean_gap" = .ok (.str geometryRow119_meanGapText) := by rfl

theorem geometryRow119_meanGap_numerator_no_slash :
    geometryRow119_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow119_meanGap_numerator_parse :
    SourceJson.intChars geometryRow119_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow119_meanGap_denominator_parse :
    SourceJson.intChars geometryRow119_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow119_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow119_meanGap_parse :
    parseRational geometryRow119_meanGapText = .ok geometryRowsTyped119.meanGap :=
  original_rational_fraction_of_chars geometryRow119_meanGapNumeratorChars geometryRow119_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow119_meanGap_numerator_no_slash geometryRow119_meanGap_numerator_parse
    geometryRow119_meanGap_denominator_parse geometryRow119_meanGap_denominator_nonzero

theorem geometryRow119_meanGap_read :
    rationalField geometryRowsJson119 "mean_gap" = .ok geometryRowsTyped119.meanGap :=
  original_rationalField_of_string geometryRowsJson119 "mean_gap" geometryRow119_meanGapText
    geometryRowsTyped119.meanGap geometryRow119_meanGap_field geometryRow119_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_meanGap_complete"
  err.flush

noncomputable def geometryRow119_jensenBoundNumeratorChars : List Char := ['8', '9', '9', '7', '0', '9', '1', '1', '7', '1', '3', '5', '7', '4', '3', '9', '6', '4', '9', '7', '2', '0', '5', '5', '5', '2', '2', '8', '4', '7', '2', '1', '5', '8', '8', '4', '9', '2', '2', '0', '6', '9', '9', '0', '6', '4', '5', '9', '0', '8', '4', '0', '2', '2', '0', '4', '3', '7', '2', '7', '4', '9', '1', '1', '0', '8', '9', '4', '4', '5', '2', '8', '4', '0', '8', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow119_jensenBoundDenominatorChars : List Char := ['1', '1', '3', '1', '3', '5', '8', '5', '6', '7', '7', '2', '7', '0', '4', '8', '1', '0', '4', '5', '5', '4', '9', '8', '8', '4', '2', '8', '2', '3', '4', '2', '4', '9', '5', '7', '6', '0', '8', '5', '8', '9', '0', '5', '4', '3', '2', '1', '5', '4', '4', '7', '0', '9', '4', '0', '5', '2', '6', '4', '2', '4', '3', '3', '8', '9', '0', '0', '8', '4', '8', '4', '6', '5', '3', '3', '2', '3', '0', '2', '3', '4', '3', '9', '7', '3', '5', '5', '5', '3', '5', '9', '8', '0', '2', '5', '0', '0', '6', '2', '2', '3', '8', '5', '2', '5', '8', '2', '4', '5', '0', '6', '4', '8', '5', '3', '1']
noncomputable def geometryRow119_jensenBoundText : String := String.ofList (geometryRow119_jensenBoundNumeratorChars ++ '/' :: geometryRow119_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_jensenBound_before_field"
  err.flush

theorem geometryRow119_jensenBound_field :
    geometryRowsJson119.getObjVal? "jensen_bound" = .ok (.str geometryRow119_jensenBoundText) := by rfl

theorem geometryRow119_jensenBound_numerator_no_slash :
    geometryRow119_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow119_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow119_jensenBoundNumeratorChars = some (899709117135743964972055522847215884922069906459084022043727491108944528408576000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow119_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow119_jensenBoundDenominatorChars = some (113135856772704810455498842823424957608589054321544709405264243389008484653323023439735553598025006223852582450648531 : Int) := by decide +kernel

theorem geometryRow119_jensenBound_denominator_nonzero : (113135856772704810455498842823424957608589054321544709405264243389008484653323023439735553598025006223852582450648531 : Int) ≠ 0 := by decide +kernel

theorem geometryRow119_jensenBound_parse :
    parseRational geometryRow119_jensenBoundText = .ok geometryRowsTyped119.jensenBound :=
  original_rational_fraction_of_chars geometryRow119_jensenBoundNumeratorChars geometryRow119_jensenBoundDenominatorChars
    (899709117135743964972055522847215884922069906459084022043727491108944528408576000000000000000000000000 : Int) (113135856772704810455498842823424957608589054321544709405264243389008484653323023439735553598025006223852582450648531 : Int)
    geometryRow119_jensenBound_numerator_no_slash geometryRow119_jensenBound_numerator_parse
    geometryRow119_jensenBound_denominator_parse geometryRow119_jensenBound_denominator_nonzero

theorem geometryRow119_jensenBound_read :
    rationalField geometryRowsJson119 "jensen_bound" = .ok geometryRowsTyped119.jensenBound :=
  original_rationalField_of_string geometryRowsJson119 "jensen_bound" geometryRow119_jensenBoundText
    geometryRowsTyped119.jensenBound geometryRow119_jensenBound_field geometryRow119_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_factorMaxima_before"
  err.flush

theorem geometryRow119_factorMaxima_read :
    rationalArrayField geometryRowsJson119 "factor_maxima" = .ok geometryRowsTyped119.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_gapWeightedMeans_before"
  err.flush

theorem geometryRow119_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson119 "gap_weighted_means" = .ok geometryRowsTyped119.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow119_floorChars : List Char := ['6', '3', '0', '0', '5', '9', '3', '1', '2', '5', '9', '4', '4', '6', '2']
noncomputable def geometryRow119_floorText : String := String.ofList geometryRow119_floorChars

theorem geometryRow119_floor_text_read :
    geometryRowsJson119.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow119_floorText := by rfl

theorem geometryRow119_floor_chars_parse :
    SourceJson.intChars geometryRow119_floorChars = some (630059312594462 : Int) := by decide +kernel

theorem geometryRow119_floor_parse :
    parseInteger geometryRow119_floorText = .ok geometryRowsTyped119.jensenFloorQ96 := by
  simp only [geometryRow119_floorText, parseInteger, String.toList_ofList, geometryRow119_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_119 :
    decodeGeometryRow geometryRowsJson119 = .ok geometryRowsTyped119 :=
  original_geometryRow_of_fields geometryRowsJson119 geometryRowsTyped119 geometryRow119_floorText
    geometryRow119_simplexId_read geometryRow119_vertexIds_read
    geometryRow119_physicalVolume_read geometryRow119_meanGap_read
    geometryRow119_factorMaxima_read geometryRow119_gapWeightedMeans_read
    geometryRow119_jensenBound_read geometryRow119_floor_text_read geometryRow119_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_119_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock060 : List SourceJson := [geometryRowsJson118, geometryRowsJson119]
noncomputable def geometryRowsTypedBlock060 : List (GeometryRow) := [geometryRowsTyped118, geometryRowsTyped119]
noncomputable def geometryRowsTypedThroughBlock060 : List (GeometryRow) := geometryRowsTypedThroughBlock059 ++ geometryRowsTypedBlock060

theorem geometry_Rows_block_060_push_eq (acc : List SourceJson) :
    SimplicesBlock060.blockPush acc = [geometryRowsJson119, geometryRowsJson118] ++ acc := by rfl

theorem geometry_Rows_block_060_reverse (acc : List SourceJson) :
    (SimplicesBlock060.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock060 := by
  rw [geometry_Rows_block_060_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_060 :
    geometryRowsJsonBlock060.mapM decodeGeometryRow = .ok geometryRowsTypedBlock060 := by
  simp only [geometryRowsJsonBlock060, geometryRowsTypedBlock060, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_118, decode_geometry_Rows_119]
  rfl

theorem decode_geometry_Rows_through_block_060 :
    SimplicesValue.arrayAcc061.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock060 := by
  change (SimplicesBlock060.blockPush SimplicesValue.arrayAcc060).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_060_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_059, decode_geometry_Rows_block_060]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_060_complete"
  err.flush

#print axioms geometryRow118_simplexId_read
#print axioms geometryRow118_vertexIds_read
#print axioms geometryRow118_physicalVolume_field
#print axioms geometryRow118_physicalVolume_numerator_no_slash
#print axioms geometryRow118_physicalVolume_numerator_parse
#print axioms geometryRow118_physicalVolume_denominator_parse
#print axioms geometryRow118_physicalVolume_denominator_nonzero
#print axioms geometryRow118_physicalVolume_parse
#print axioms geometryRow118_physicalVolume_read
#print axioms geometryRow118_meanGap_field
#print axioms geometryRow118_meanGap_numerator_no_slash
#print axioms geometryRow118_meanGap_numerator_parse
#print axioms geometryRow118_meanGap_denominator_parse
#print axioms geometryRow118_meanGap_denominator_nonzero
#print axioms geometryRow118_meanGap_parse
#print axioms geometryRow118_meanGap_read
#print axioms geometryRow118_jensenBound_field
#print axioms geometryRow118_jensenBound_numerator_no_slash
#print axioms geometryRow118_jensenBound_numerator_parse
#print axioms geometryRow118_jensenBound_denominator_parse
#print axioms geometryRow118_jensenBound_denominator_nonzero
#print axioms geometryRow118_jensenBound_parse
#print axioms geometryRow118_jensenBound_read
#print axioms geometryRow118_factorMaxima_read
#print axioms geometryRow118_gapWeightedMeans_read
#print axioms geometryRow118_floor_text_read
#print axioms geometryRow118_floor_chars_parse
#print axioms geometryRow118_floor_parse
#print axioms decode_geometry_Rows_118
#print axioms geometryRow119_simplexId_read
#print axioms geometryRow119_vertexIds_read
#print axioms geometryRow119_physicalVolume_field
#print axioms geometryRow119_physicalVolume_numerator_no_slash
#print axioms geometryRow119_physicalVolume_numerator_parse
#print axioms geometryRow119_physicalVolume_denominator_parse
#print axioms geometryRow119_physicalVolume_denominator_nonzero
#print axioms geometryRow119_physicalVolume_parse
#print axioms geometryRow119_physicalVolume_read
#print axioms geometryRow119_meanGap_field
#print axioms geometryRow119_meanGap_numerator_no_slash
#print axioms geometryRow119_meanGap_numerator_parse
#print axioms geometryRow119_meanGap_denominator_parse
#print axioms geometryRow119_meanGap_denominator_nonzero
#print axioms geometryRow119_meanGap_parse
#print axioms geometryRow119_meanGap_read
#print axioms geometryRow119_jensenBound_field
#print axioms geometryRow119_jensenBound_numerator_no_slash
#print axioms geometryRow119_jensenBound_numerator_parse
#print axioms geometryRow119_jensenBound_denominator_parse
#print axioms geometryRow119_jensenBound_denominator_nonzero
#print axioms geometryRow119_jensenBound_parse
#print axioms geometryRow119_jensenBound_read
#print axioms geometryRow119_factorMaxima_read
#print axioms geometryRow119_gapWeightedMeans_read
#print axioms geometryRow119_floor_text_read
#print axioms geometryRow119_floor_chars_parse
#print axioms geometryRow119_floor_parse
#print axioms decode_geometry_Rows_119
#print axioms geometry_Rows_block_060_push_eq
#print axioms geometry_Rows_block_060_reverse
#print axioms decode_geometry_Rows_block_060
#print axioms decode_geometry_Rows_through_block_060

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
