import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows040

/-! Original simplices typed block 41, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson081 : SourceJson :=
  (SimplicesBlock041.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped081 : GeometryRow :=
  { simplexId := 81,
    vertexIds := #[39, 37, 24, 11, 9, 7, 6, 2, 0],
    physicalVolume := ((39616856316665293756570370563201394887541 : ℚ) / (9268245782691840000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((2392329869 : ℚ) / (26600000000 : ℚ)), ((16942211623 : ℚ) / (186200000000 : ℚ)), ((120031453681 : ℚ) / (837900000000 : ℚ)), ((3937713641 : ℚ) / (34912500000 : ℚ)), ((93785277937 : ℚ) / (1675800000000 : ℚ)), ((5154874801 : ℚ) / (104737500000 : ℚ)), ((551414939 : ℚ) / (13406400000 : ℚ)), ((11960833961 : ℚ) / (335160000000 : ℚ)), ((11960789273 : ℚ) / (335160000000 : ℚ)), ((27291124957 : ℚ) / (837900000000 : ℚ))],
    jensenBound := ((22990840011193519341462147028242250417454410167622441383836474283984375000000000000 : ℚ) / (1429424904498136178994628920826302765734563251159345133533428224384449830362600908469046182545169 : ℚ)),
    jensenFloorQ96 := (1274304094614762 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_simplexId_before"
  err.flush

theorem geometryRow081_simplexId_read :
    geometryRowsJson081.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped081.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_vertexIds_before"
  err.flush

theorem geometryRow081_vertexIds_read :
    geometryRowsJson081.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped081.vertexIds := by decide +kernel

noncomputable def geometryRow081_physicalVolumeNumeratorChars : List Char := ['3', '9', '6', '1', '6', '8', '5', '6', '3', '1', '6', '6', '6', '5', '2', '9', '3', '7', '5', '6', '5', '7', '0', '3', '7', '0', '5', '6', '3', '2', '0', '1', '3', '9', '4', '8', '8', '7', '5', '4', '1']
noncomputable def geometryRow081_physicalVolumeDenominatorChars : List Char := ['9', '2', '6', '8', '2', '4', '5', '7', '8', '2', '6', '9', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow081_physicalVolumeText : String := String.ofList (geometryRow081_physicalVolumeNumeratorChars ++ '/' :: geometryRow081_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_physicalVolume_before_field"
  err.flush

theorem geometryRow081_physicalVolume_field :
    geometryRowsJson081.getObjVal? "physical_volume" = .ok (.str geometryRow081_physicalVolumeText) := by rfl

theorem geometryRow081_physicalVolume_numerator_no_slash :
    geometryRow081_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow081_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow081_physicalVolumeNumeratorChars = some (39616856316665293756570370563201394887541 : Int) := by decide +kernel

theorem geometryRow081_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow081_physicalVolumeDenominatorChars = some (9268245782691840000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow081_physicalVolume_denominator_nonzero : (9268245782691840000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow081_physicalVolume_parse :
    parseRational geometryRow081_physicalVolumeText = .ok geometryRowsTyped081.physicalVolume :=
  original_rational_fraction_of_chars geometryRow081_physicalVolumeNumeratorChars geometryRow081_physicalVolumeDenominatorChars
    (39616856316665293756570370563201394887541 : Int) (9268245782691840000000000000000000000000000000000000000000000000 : Int)
    geometryRow081_physicalVolume_numerator_no_slash geometryRow081_physicalVolume_numerator_parse
    geometryRow081_physicalVolume_denominator_parse geometryRow081_physicalVolume_denominator_nonzero

theorem geometryRow081_physicalVolume_read :
    rationalField geometryRowsJson081 "physical_volume" = .ok geometryRowsTyped081.physicalVolume :=
  original_rationalField_of_string geometryRowsJson081 "physical_volume" geometryRow081_physicalVolumeText
    geometryRowsTyped081.physicalVolume geometryRow081_physicalVolume_field geometryRow081_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_physicalVolume_complete"
  err.flush

noncomputable def geometryRow081_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow081_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow081_meanGapText : String := String.ofList (geometryRow081_meanGapNumeratorChars ++ '/' :: geometryRow081_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_meanGap_before_field"
  err.flush

theorem geometryRow081_meanGap_field :
    geometryRowsJson081.getObjVal? "mean_gap" = .ok (.str geometryRow081_meanGapText) := by rfl

theorem geometryRow081_meanGap_numerator_no_slash :
    geometryRow081_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow081_meanGap_numerator_parse :
    SourceJson.intChars geometryRow081_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow081_meanGap_denominator_parse :
    SourceJson.intChars geometryRow081_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow081_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow081_meanGap_parse :
    parseRational geometryRow081_meanGapText = .ok geometryRowsTyped081.meanGap :=
  original_rational_fraction_of_chars geometryRow081_meanGapNumeratorChars geometryRow081_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow081_meanGap_numerator_no_slash geometryRow081_meanGap_numerator_parse
    geometryRow081_meanGap_denominator_parse geometryRow081_meanGap_denominator_nonzero

theorem geometryRow081_meanGap_read :
    rationalField geometryRowsJson081 "mean_gap" = .ok geometryRowsTyped081.meanGap :=
  original_rationalField_of_string geometryRowsJson081 "mean_gap" geometryRow081_meanGapText
    geometryRowsTyped081.meanGap geometryRow081_meanGap_field geometryRow081_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_meanGap_complete"
  err.flush

noncomputable def geometryRow081_jensenBoundNumeratorChars : List Char := ['2', '2', '9', '9', '0', '8', '4', '0', '0', '1', '1', '1', '9', '3', '5', '1', '9', '3', '4', '1', '4', '6', '2', '1', '4', '7', '0', '2', '8', '2', '4', '2', '2', '5', '0', '4', '1', '7', '4', '5', '4', '4', '1', '0', '1', '6', '7', '6', '2', '2', '4', '4', '1', '3', '8', '3', '8', '3', '6', '4', '7', '4', '2', '8', '3', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow081_jensenBoundDenominatorChars : List Char := ['1', '4', '2', '9', '4', '2', '4', '9', '0', '4', '4', '9', '8', '1', '3', '6', '1', '7', '8', '9', '9', '4', '6', '2', '8', '9', '2', '0', '8', '2', '6', '3', '0', '2', '7', '6', '5', '7', '3', '4', '5', '6', '3', '2', '5', '1', '1', '5', '9', '3', '4', '5', '1', '3', '3', '5', '3', '3', '4', '2', '8', '2', '2', '4', '3', '8', '4', '4', '4', '9', '8', '3', '0', '3', '6', '2', '6', '0', '0', '9', '0', '8', '4', '6', '9', '0', '4', '6', '1', '8', '2', '5', '4', '5', '1', '6', '9']
noncomputable def geometryRow081_jensenBoundText : String := String.ofList (geometryRow081_jensenBoundNumeratorChars ++ '/' :: geometryRow081_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_jensenBound_before_field"
  err.flush

theorem geometryRow081_jensenBound_field :
    geometryRowsJson081.getObjVal? "jensen_bound" = .ok (.str geometryRow081_jensenBoundText) := by rfl

theorem geometryRow081_jensenBound_numerator_no_slash :
    geometryRow081_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow081_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow081_jensenBoundNumeratorChars = some (22990840011193519341462147028242250417454410167622441383836474283984375000000000000 : Int) := by decide +kernel

theorem geometryRow081_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow081_jensenBoundDenominatorChars = some (1429424904498136178994628920826302765734563251159345133533428224384449830362600908469046182545169 : Int) := by decide +kernel

theorem geometryRow081_jensenBound_denominator_nonzero : (1429424904498136178994628920826302765734563251159345133533428224384449830362600908469046182545169 : Int) ≠ 0 := by decide +kernel

theorem geometryRow081_jensenBound_parse :
    parseRational geometryRow081_jensenBoundText = .ok geometryRowsTyped081.jensenBound :=
  original_rational_fraction_of_chars geometryRow081_jensenBoundNumeratorChars geometryRow081_jensenBoundDenominatorChars
    (22990840011193519341462147028242250417454410167622441383836474283984375000000000000 : Int) (1429424904498136178994628920826302765734563251159345133533428224384449830362600908469046182545169 : Int)
    geometryRow081_jensenBound_numerator_no_slash geometryRow081_jensenBound_numerator_parse
    geometryRow081_jensenBound_denominator_parse geometryRow081_jensenBound_denominator_nonzero

theorem geometryRow081_jensenBound_read :
    rationalField geometryRowsJson081 "jensen_bound" = .ok geometryRowsTyped081.jensenBound :=
  original_rationalField_of_string geometryRowsJson081 "jensen_bound" geometryRow081_jensenBoundText
    geometryRowsTyped081.jensenBound geometryRow081_jensenBound_field geometryRow081_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_factorMaxima_before"
  err.flush

theorem geometryRow081_factorMaxima_read :
    rationalArrayField geometryRowsJson081 "factor_maxima" = .ok geometryRowsTyped081.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_gapWeightedMeans_before"
  err.flush

theorem geometryRow081_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson081 "gap_weighted_means" = .ok geometryRowsTyped081.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow081_floorChars : List Char := ['1', '2', '7', '4', '3', '0', '4', '0', '9', '4', '6', '1', '4', '7', '6', '2']
noncomputable def geometryRow081_floorText : String := String.ofList geometryRow081_floorChars

theorem geometryRow081_floor_text_read :
    geometryRowsJson081.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow081_floorText := by rfl

theorem geometryRow081_floor_chars_parse :
    SourceJson.intChars geometryRow081_floorChars = some (1274304094614762 : Int) := by decide +kernel

theorem geometryRow081_floor_parse :
    parseInteger geometryRow081_floorText = .ok geometryRowsTyped081.jensenFloorQ96 := by
  simp only [geometryRow081_floorText, parseInteger, String.toList_ofList, geometryRow081_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_081 :
    decodeGeometryRow geometryRowsJson081 = .ok geometryRowsTyped081 :=
  original_geometryRow_of_fields geometryRowsJson081 geometryRowsTyped081 geometryRow081_floorText
    geometryRow081_simplexId_read geometryRow081_vertexIds_read
    geometryRow081_physicalVolume_read geometryRow081_meanGap_read
    geometryRow081_factorMaxima_read geometryRow081_gapWeightedMeans_read
    geometryRow081_jensenBound_read geometryRow081_floor_text_read geometryRow081_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_081_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson082 : SourceJson :=
  (SimplicesBlock041.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped082 : GeometryRow :=
  { simplexId := 82,
    vertexIds := #[39, 37, 24, 23, 10, 8, 3, 1, 0],
    physicalVolume := ((100731704266773221492077509743767019 : ℚ) / (146599870464000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((63984745637 : ℚ) / (705432000000 : ℚ)), ((323489126749 : ℚ) / (3527160000000 : ℚ)), ((12949940667 : ℚ) / (90440000000 : ℚ)), ((58281971639 : ℚ) / (529074000000 : ℚ)), ((1935660827 : ℚ) / (34580000000 : ℚ)), ((58127225967 : ℚ) / (1175720000000 : ℚ)), ((10759037041 : ℚ) / (278460000000 : ℚ)), ((12599788771 : ℚ) / (330671250000 : ℚ)), ((370919295899 : ℚ) / (10581480000000 : ℚ)), ((370917179603 : ℚ) / (10581480000000 : ℚ))],
    jensenBound := ((950946883015683203551709137808331291042015512288304191836436856335822434371150000000000000 : ℚ) / (404720340248633136734744559004794020317357962184420152690846675290722528950390756240334138221059917966147 : ℚ)),
    jensenFloorQ96 := (186157617241858 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_simplexId_before"
  err.flush

theorem geometryRow082_simplexId_read :
    geometryRowsJson082.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped082.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_vertexIds_before"
  err.flush

theorem geometryRow082_vertexIds_read :
    geometryRowsJson082.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped082.vertexIds := by decide +kernel

noncomputable def geometryRow082_physicalVolumeNumeratorChars : List Char := ['1', '0', '0', '7', '3', '1', '7', '0', '4', '2', '6', '6', '7', '7', '3', '2', '2', '1', '4', '9', '2', '0', '7', '7', '5', '0', '9', '7', '4', '3', '7', '6', '7', '0', '1', '9']
noncomputable def geometryRow082_physicalVolumeDenominatorChars : List Char := ['1', '4', '6', '5', '9', '9', '8', '7', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow082_physicalVolumeText : String := String.ofList (geometryRow082_physicalVolumeNumeratorChars ++ '/' :: geometryRow082_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_physicalVolume_before_field"
  err.flush

theorem geometryRow082_physicalVolume_field :
    geometryRowsJson082.getObjVal? "physical_volume" = .ok (.str geometryRow082_physicalVolumeText) := by rfl

theorem geometryRow082_physicalVolume_numerator_no_slash :
    geometryRow082_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow082_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow082_physicalVolumeNumeratorChars = some (100731704266773221492077509743767019 : Int) := by decide +kernel

theorem geometryRow082_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow082_physicalVolumeDenominatorChars = some (146599870464000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow082_physicalVolume_denominator_nonzero : (146599870464000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow082_physicalVolume_parse :
    parseRational geometryRow082_physicalVolumeText = .ok geometryRowsTyped082.physicalVolume :=
  original_rational_fraction_of_chars geometryRow082_physicalVolumeNumeratorChars geometryRow082_physicalVolumeDenominatorChars
    (100731704266773221492077509743767019 : Int) (146599870464000000000000000000000000000000000000000000000000 : Int)
    geometryRow082_physicalVolume_numerator_no_slash geometryRow082_physicalVolume_numerator_parse
    geometryRow082_physicalVolume_denominator_parse geometryRow082_physicalVolume_denominator_nonzero

theorem geometryRow082_physicalVolume_read :
    rationalField geometryRowsJson082 "physical_volume" = .ok geometryRowsTyped082.physicalVolume :=
  original_rationalField_of_string geometryRowsJson082 "physical_volume" geometryRow082_physicalVolumeText
    geometryRowsTyped082.physicalVolume geometryRow082_physicalVolume_field geometryRow082_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_physicalVolume_complete"
  err.flush

noncomputable def geometryRow082_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow082_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow082_meanGapText : String := String.ofList (geometryRow082_meanGapNumeratorChars ++ '/' :: geometryRow082_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_meanGap_before_field"
  err.flush

theorem geometryRow082_meanGap_field :
    geometryRowsJson082.getObjVal? "mean_gap" = .ok (.str geometryRow082_meanGapText) := by rfl

theorem geometryRow082_meanGap_numerator_no_slash :
    geometryRow082_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow082_meanGap_numerator_parse :
    SourceJson.intChars geometryRow082_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow082_meanGap_denominator_parse :
    SourceJson.intChars geometryRow082_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow082_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow082_meanGap_parse :
    parseRational geometryRow082_meanGapText = .ok geometryRowsTyped082.meanGap :=
  original_rational_fraction_of_chars geometryRow082_meanGapNumeratorChars geometryRow082_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow082_meanGap_numerator_no_slash geometryRow082_meanGap_numerator_parse
    geometryRow082_meanGap_denominator_parse geometryRow082_meanGap_denominator_nonzero

theorem geometryRow082_meanGap_read :
    rationalField geometryRowsJson082 "mean_gap" = .ok geometryRowsTyped082.meanGap :=
  original_rationalField_of_string geometryRowsJson082 "mean_gap" geometryRow082_meanGapText
    geometryRowsTyped082.meanGap geometryRow082_meanGap_field geometryRow082_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_meanGap_complete"
  err.flush

noncomputable def geometryRow082_jensenBoundNumeratorChars : List Char := ['9', '5', '0', '9', '4', '6', '8', '8', '3', '0', '1', '5', '6', '8', '3', '2', '0', '3', '5', '5', '1', '7', '0', '9', '1', '3', '7', '8', '0', '8', '3', '3', '1', '2', '9', '1', '0', '4', '2', '0', '1', '5', '5', '1', '2', '2', '8', '8', '3', '0', '4', '1', '9', '1', '8', '3', '6', '4', '3', '6', '8', '5', '6', '3', '3', '5', '8', '2', '2', '4', '3', '4', '3', '7', '1', '1', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow082_jensenBoundDenominatorChars : List Char := ['4', '0', '4', '7', '2', '0', '3', '4', '0', '2', '4', '8', '6', '3', '3', '1', '3', '6', '7', '3', '4', '7', '4', '4', '5', '5', '9', '0', '0', '4', '7', '9', '4', '0', '2', '0', '3', '1', '7', '3', '5', '7', '9', '6', '2', '1', '8', '4', '4', '2', '0', '1', '5', '2', '6', '9', '0', '8', '4', '6', '6', '7', '5', '2', '9', '0', '7', '2', '2', '5', '2', '8', '9', '5', '0', '3', '9', '0', '7', '5', '6', '2', '4', '0', '3', '3', '4', '1', '3', '8', '2', '2', '1', '0', '5', '9', '9', '1', '7', '9', '6', '6', '1', '4', '7']
noncomputable def geometryRow082_jensenBoundText : String := String.ofList (geometryRow082_jensenBoundNumeratorChars ++ '/' :: geometryRow082_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_jensenBound_before_field"
  err.flush

theorem geometryRow082_jensenBound_field :
    geometryRowsJson082.getObjVal? "jensen_bound" = .ok (.str geometryRow082_jensenBoundText) := by rfl

theorem geometryRow082_jensenBound_numerator_no_slash :
    geometryRow082_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow082_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow082_jensenBoundNumeratorChars = some (950946883015683203551709137808331291042015512288304191836436856335822434371150000000000000 : Int) := by decide +kernel

theorem geometryRow082_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow082_jensenBoundDenominatorChars = some (404720340248633136734744559004794020317357962184420152690846675290722528950390756240334138221059917966147 : Int) := by decide +kernel

theorem geometryRow082_jensenBound_denominator_nonzero : (404720340248633136734744559004794020317357962184420152690846675290722528950390756240334138221059917966147 : Int) ≠ 0 := by decide +kernel

theorem geometryRow082_jensenBound_parse :
    parseRational geometryRow082_jensenBoundText = .ok geometryRowsTyped082.jensenBound :=
  original_rational_fraction_of_chars geometryRow082_jensenBoundNumeratorChars geometryRow082_jensenBoundDenominatorChars
    (950946883015683203551709137808331291042015512288304191836436856335822434371150000000000000 : Int) (404720340248633136734744559004794020317357962184420152690846675290722528950390756240334138221059917966147 : Int)
    geometryRow082_jensenBound_numerator_no_slash geometryRow082_jensenBound_numerator_parse
    geometryRow082_jensenBound_denominator_parse geometryRow082_jensenBound_denominator_nonzero

theorem geometryRow082_jensenBound_read :
    rationalField geometryRowsJson082 "jensen_bound" = .ok geometryRowsTyped082.jensenBound :=
  original_rationalField_of_string geometryRowsJson082 "jensen_bound" geometryRow082_jensenBoundText
    geometryRowsTyped082.jensenBound geometryRow082_jensenBound_field geometryRow082_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_factorMaxima_before"
  err.flush

theorem geometryRow082_factorMaxima_read :
    rationalArrayField geometryRowsJson082 "factor_maxima" = .ok geometryRowsTyped082.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_gapWeightedMeans_before"
  err.flush

theorem geometryRow082_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson082 "gap_weighted_means" = .ok geometryRowsTyped082.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow082_floorChars : List Char := ['1', '8', '6', '1', '5', '7', '6', '1', '7', '2', '4', '1', '8', '5', '8']
noncomputable def geometryRow082_floorText : String := String.ofList geometryRow082_floorChars

theorem geometryRow082_floor_text_read :
    geometryRowsJson082.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow082_floorText := by rfl

theorem geometryRow082_floor_chars_parse :
    SourceJson.intChars geometryRow082_floorChars = some (186157617241858 : Int) := by decide +kernel

theorem geometryRow082_floor_parse :
    parseInteger geometryRow082_floorText = .ok geometryRowsTyped082.jensenFloorQ96 := by
  simp only [geometryRow082_floorText, parseInteger, String.toList_ofList, geometryRow082_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_082 :
    decodeGeometryRow geometryRowsJson082 = .ok geometryRowsTyped082 :=
  original_geometryRow_of_fields geometryRowsJson082 geometryRowsTyped082 geometryRow082_floorText
    geometryRow082_simplexId_read geometryRow082_vertexIds_read
    geometryRow082_physicalVolume_read geometryRow082_meanGap_read
    geometryRow082_factorMaxima_read geometryRow082_gapWeightedMeans_read
    geometryRow082_jensenBound_read geometryRow082_floor_text_read geometryRow082_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_082_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock041 : List SourceJson := [geometryRowsJson081, geometryRowsJson082]
noncomputable def geometryRowsTypedBlock041 : List (GeometryRow) := [geometryRowsTyped081, geometryRowsTyped082]
noncomputable def geometryRowsTypedThroughBlock041 : List (GeometryRow) := geometryRowsTypedThroughBlock040 ++ geometryRowsTypedBlock041

theorem geometry_Rows_block_041_push_eq (acc : List SourceJson) :
    SimplicesBlock041.blockPush acc = [geometryRowsJson082, geometryRowsJson081] ++ acc := by rfl

theorem geometry_Rows_block_041_reverse (acc : List SourceJson) :
    (SimplicesBlock041.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock041 := by
  rw [geometry_Rows_block_041_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_041 :
    geometryRowsJsonBlock041.mapM decodeGeometryRow = .ok geometryRowsTypedBlock041 := by
  simp only [geometryRowsJsonBlock041, geometryRowsTypedBlock041, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_081, decode_geometry_Rows_082]
  rfl

theorem decode_geometry_Rows_through_block_041 :
    SimplicesValue.arrayAcc042.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock041 := by
  change (SimplicesBlock041.blockPush SimplicesValue.arrayAcc041).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_041_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_040, decode_geometry_Rows_block_041]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_041_complete"
  err.flush

#print axioms geometryRow081_simplexId_read
#print axioms geometryRow081_vertexIds_read
#print axioms geometryRow081_physicalVolume_field
#print axioms geometryRow081_physicalVolume_numerator_no_slash
#print axioms geometryRow081_physicalVolume_numerator_parse
#print axioms geometryRow081_physicalVolume_denominator_parse
#print axioms geometryRow081_physicalVolume_denominator_nonzero
#print axioms geometryRow081_physicalVolume_parse
#print axioms geometryRow081_physicalVolume_read
#print axioms geometryRow081_meanGap_field
#print axioms geometryRow081_meanGap_numerator_no_slash
#print axioms geometryRow081_meanGap_numerator_parse
#print axioms geometryRow081_meanGap_denominator_parse
#print axioms geometryRow081_meanGap_denominator_nonzero
#print axioms geometryRow081_meanGap_parse
#print axioms geometryRow081_meanGap_read
#print axioms geometryRow081_jensenBound_field
#print axioms geometryRow081_jensenBound_numerator_no_slash
#print axioms geometryRow081_jensenBound_numerator_parse
#print axioms geometryRow081_jensenBound_denominator_parse
#print axioms geometryRow081_jensenBound_denominator_nonzero
#print axioms geometryRow081_jensenBound_parse
#print axioms geometryRow081_jensenBound_read
#print axioms geometryRow081_factorMaxima_read
#print axioms geometryRow081_gapWeightedMeans_read
#print axioms geometryRow081_floor_text_read
#print axioms geometryRow081_floor_chars_parse
#print axioms geometryRow081_floor_parse
#print axioms decode_geometry_Rows_081
#print axioms geometryRow082_simplexId_read
#print axioms geometryRow082_vertexIds_read
#print axioms geometryRow082_physicalVolume_field
#print axioms geometryRow082_physicalVolume_numerator_no_slash
#print axioms geometryRow082_physicalVolume_numerator_parse
#print axioms geometryRow082_physicalVolume_denominator_parse
#print axioms geometryRow082_physicalVolume_denominator_nonzero
#print axioms geometryRow082_physicalVolume_parse
#print axioms geometryRow082_physicalVolume_read
#print axioms geometryRow082_meanGap_field
#print axioms geometryRow082_meanGap_numerator_no_slash
#print axioms geometryRow082_meanGap_numerator_parse
#print axioms geometryRow082_meanGap_denominator_parse
#print axioms geometryRow082_meanGap_denominator_nonzero
#print axioms geometryRow082_meanGap_parse
#print axioms geometryRow082_meanGap_read
#print axioms geometryRow082_jensenBound_field
#print axioms geometryRow082_jensenBound_numerator_no_slash
#print axioms geometryRow082_jensenBound_numerator_parse
#print axioms geometryRow082_jensenBound_denominator_parse
#print axioms geometryRow082_jensenBound_denominator_nonzero
#print axioms geometryRow082_jensenBound_parse
#print axioms geometryRow082_jensenBound_read
#print axioms geometryRow082_factorMaxima_read
#print axioms geometryRow082_gapWeightedMeans_read
#print axioms geometryRow082_floor_text_read
#print axioms geometryRow082_floor_chars_parse
#print axioms geometryRow082_floor_parse
#print axioms decode_geometry_Rows_082
#print axioms geometry_Rows_block_041_push_eq
#print axioms geometry_Rows_block_041_reverse
#print axioms decode_geometry_Rows_block_041
#print axioms decode_geometry_Rows_through_block_041

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
