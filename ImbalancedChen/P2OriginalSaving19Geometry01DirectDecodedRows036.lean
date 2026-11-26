import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows035

/-! Original simplices typed block 36, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson071 : SourceJson :=
  (SimplicesBlock036.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped071 : GeometryRow :=
  { simplexId := 71,
    vertexIds := #[39, 35, 33, 24, 23, 19, 18, 15, 14],
    physicalVolume := ((25373191689045391074586059103100279557178387 : ℚ) / (1645890253583862988800000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((159940532893 : ℚ) / (2376900000000 : ℚ)), ((80230536569 : ℚ) / (1188450000000 : ℚ)), ((264313425299 : ℚ) / (1782675000000 : ℚ)), ((1183768401997 : ℚ) / (11092200000000 : ℚ)), ((5606087484617 : ℚ) / (99829800000000 : ℚ)), ((330762018949 : ℚ) / (7130700000000 : ℚ)), ((230929846129 : ℚ) / (5254200000000 : ℚ)), ((4334361203341 : ℚ) / (99829800000000 : ℚ)), ((2153847478073 : ℚ) / (49914900000000 : ℚ)), ((4191561238951 : ℚ) / (99829800000000 : ℚ))],
    jensenBound := ((111387983018892158187284066887434676958888418458671672702736921385724605696714094150543212890625000000000 : ℚ) / (9610756956414129365856323461545908321470388867631964630708861890370954627710635136417983542542716140448353847332050643 : ℚ)),
    jensenFloorQ96 := (918248714516408 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_simplexId_before"
  err.flush

theorem geometryRow071_simplexId_read :
    geometryRowsJson071.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped071.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_vertexIds_before"
  err.flush

theorem geometryRow071_vertexIds_read :
    geometryRowsJson071.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped071.vertexIds := by decide +kernel

noncomputable def geometryRow071_physicalVolumeNumeratorChars : List Char := ['2', '5', '3', '7', '3', '1', '9', '1', '6', '8', '9', '0', '4', '5', '3', '9', '1', '0', '7', '4', '5', '8', '6', '0', '5', '9', '1', '0', '3', '1', '0', '0', '2', '7', '9', '5', '5', '7', '1', '7', '8', '3', '8', '7']
noncomputable def geometryRow071_physicalVolumeDenominatorChars : List Char := ['1', '6', '4', '5', '8', '9', '0', '2', '5', '3', '5', '8', '3', '8', '6', '2', '9', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow071_physicalVolumeText : String := String.ofList (geometryRow071_physicalVolumeNumeratorChars ++ '/' :: geometryRow071_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_physicalVolume_before_field"
  err.flush

theorem geometryRow071_physicalVolume_field :
    geometryRowsJson071.getObjVal? "physical_volume" = .ok (.str geometryRow071_physicalVolumeText) := by rfl

theorem geometryRow071_physicalVolume_numerator_no_slash :
    geometryRow071_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow071_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow071_physicalVolumeNumeratorChars = some (25373191689045391074586059103100279557178387 : Int) := by decide +kernel

theorem geometryRow071_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow071_physicalVolumeDenominatorChars = some (1645890253583862988800000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow071_physicalVolume_denominator_nonzero : (1645890253583862988800000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow071_physicalVolume_parse :
    parseRational geometryRow071_physicalVolumeText = .ok geometryRowsTyped071.physicalVolume :=
  original_rational_fraction_of_chars geometryRow071_physicalVolumeNumeratorChars geometryRow071_physicalVolumeDenominatorChars
    (25373191689045391074586059103100279557178387 : Int) (1645890253583862988800000000000000000000000000000000000000000000000 : Int)
    geometryRow071_physicalVolume_numerator_no_slash geometryRow071_physicalVolume_numerator_parse
    geometryRow071_physicalVolume_denominator_parse geometryRow071_physicalVolume_denominator_nonzero

theorem geometryRow071_physicalVolume_read :
    rationalField geometryRowsJson071 "physical_volume" = .ok geometryRowsTyped071.physicalVolume :=
  original_rationalField_of_string geometryRowsJson071 "physical_volume" geometryRow071_physicalVolumeText
    geometryRowsTyped071.physicalVolume geometryRow071_physicalVolume_field geometryRow071_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_physicalVolume_complete"
  err.flush

noncomputable def geometryRow071_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow071_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow071_meanGapText : String := String.ofList (geometryRow071_meanGapNumeratorChars ++ '/' :: geometryRow071_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_meanGap_before_field"
  err.flush

theorem geometryRow071_meanGap_field :
    geometryRowsJson071.getObjVal? "mean_gap" = .ok (.str geometryRow071_meanGapText) := by rfl

theorem geometryRow071_meanGap_numerator_no_slash :
    geometryRow071_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow071_meanGap_numerator_parse :
    SourceJson.intChars geometryRow071_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow071_meanGap_denominator_parse :
    SourceJson.intChars geometryRow071_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow071_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow071_meanGap_parse :
    parseRational geometryRow071_meanGapText = .ok geometryRowsTyped071.meanGap :=
  original_rational_fraction_of_chars geometryRow071_meanGapNumeratorChars geometryRow071_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow071_meanGap_numerator_no_slash geometryRow071_meanGap_numerator_parse
    geometryRow071_meanGap_denominator_parse geometryRow071_meanGap_denominator_nonzero

theorem geometryRow071_meanGap_read :
    rationalField geometryRowsJson071 "mean_gap" = .ok geometryRowsTyped071.meanGap :=
  original_rationalField_of_string geometryRowsJson071 "mean_gap" geometryRow071_meanGapText
    geometryRowsTyped071.meanGap geometryRow071_meanGap_field geometryRow071_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_meanGap_complete"
  err.flush

noncomputable def geometryRow071_jensenBoundNumeratorChars : List Char := ['1', '1', '1', '3', '8', '7', '9', '8', '3', '0', '1', '8', '8', '9', '2', '1', '5', '8', '1', '8', '7', '2', '8', '4', '0', '6', '6', '8', '8', '7', '4', '3', '4', '6', '7', '6', '9', '5', '8', '8', '8', '8', '4', '1', '8', '4', '5', '8', '6', '7', '1', '6', '7', '2', '7', '0', '2', '7', '3', '6', '9', '2', '1', '3', '8', '5', '7', '2', '4', '6', '0', '5', '6', '9', '6', '7', '1', '4', '0', '9', '4', '1', '5', '0', '5', '4', '3', '2', '1', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow071_jensenBoundDenominatorChars : List Char := ['9', '6', '1', '0', '7', '5', '6', '9', '5', '6', '4', '1', '4', '1', '2', '9', '3', '6', '5', '8', '5', '6', '3', '2', '3', '4', '6', '1', '5', '4', '5', '9', '0', '8', '3', '2', '1', '4', '7', '0', '3', '8', '8', '8', '6', '7', '6', '3', '1', '9', '6', '4', '6', '3', '0', '7', '0', '8', '8', '6', '1', '8', '9', '0', '3', '7', '0', '9', '5', '4', '6', '2', '7', '7', '1', '0', '6', '3', '5', '1', '3', '6', '4', '1', '7', '9', '8', '3', '5', '4', '2', '5', '4', '2', '7', '1', '6', '1', '4', '0', '4', '4', '8', '3', '5', '3', '8', '4', '7', '3', '3', '2', '0', '5', '0', '6', '4', '3']
noncomputable def geometryRow071_jensenBoundText : String := String.ofList (geometryRow071_jensenBoundNumeratorChars ++ '/' :: geometryRow071_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_jensenBound_before_field"
  err.flush

theorem geometryRow071_jensenBound_field :
    geometryRowsJson071.getObjVal? "jensen_bound" = .ok (.str geometryRow071_jensenBoundText) := by rfl

theorem geometryRow071_jensenBound_numerator_no_slash :
    geometryRow071_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow071_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow071_jensenBoundNumeratorChars = some (111387983018892158187284066887434676958888418458671672702736921385724605696714094150543212890625000000000 : Int) := by decide +kernel

theorem geometryRow071_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow071_jensenBoundDenominatorChars = some (9610756956414129365856323461545908321470388867631964630708861890370954627710635136417983542542716140448353847332050643 : Int) := by decide +kernel

theorem geometryRow071_jensenBound_denominator_nonzero : (9610756956414129365856323461545908321470388867631964630708861890370954627710635136417983542542716140448353847332050643 : Int) ≠ 0 := by decide +kernel

theorem geometryRow071_jensenBound_parse :
    parseRational geometryRow071_jensenBoundText = .ok geometryRowsTyped071.jensenBound :=
  original_rational_fraction_of_chars geometryRow071_jensenBoundNumeratorChars geometryRow071_jensenBoundDenominatorChars
    (111387983018892158187284066887434676958888418458671672702736921385724605696714094150543212890625000000000 : Int) (9610756956414129365856323461545908321470388867631964630708861890370954627710635136417983542542716140448353847332050643 : Int)
    geometryRow071_jensenBound_numerator_no_slash geometryRow071_jensenBound_numerator_parse
    geometryRow071_jensenBound_denominator_parse geometryRow071_jensenBound_denominator_nonzero

theorem geometryRow071_jensenBound_read :
    rationalField geometryRowsJson071 "jensen_bound" = .ok geometryRowsTyped071.jensenBound :=
  original_rationalField_of_string geometryRowsJson071 "jensen_bound" geometryRow071_jensenBoundText
    geometryRowsTyped071.jensenBound geometryRow071_jensenBound_field geometryRow071_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_factorMaxima_before"
  err.flush

theorem geometryRow071_factorMaxima_read :
    rationalArrayField geometryRowsJson071 "factor_maxima" = .ok geometryRowsTyped071.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_gapWeightedMeans_before"
  err.flush

theorem geometryRow071_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson071 "gap_weighted_means" = .ok geometryRowsTyped071.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow071_floorChars : List Char := ['9', '1', '8', '2', '4', '8', '7', '1', '4', '5', '1', '6', '4', '0', '8']
noncomputable def geometryRow071_floorText : String := String.ofList geometryRow071_floorChars

theorem geometryRow071_floor_text_read :
    geometryRowsJson071.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow071_floorText := by rfl

theorem geometryRow071_floor_chars_parse :
    SourceJson.intChars geometryRow071_floorChars = some (918248714516408 : Int) := by decide +kernel

theorem geometryRow071_floor_parse :
    parseInteger geometryRow071_floorText = .ok geometryRowsTyped071.jensenFloorQ96 := by
  simp only [geometryRow071_floorText, parseInteger, String.toList_ofList, geometryRow071_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_071 :
    decodeGeometryRow geometryRowsJson071 = .ok geometryRowsTyped071 :=
  original_geometryRow_of_fields geometryRowsJson071 geometryRowsTyped071 geometryRow071_floorText
    geometryRow071_simplexId_read geometryRow071_vertexIds_read
    geometryRow071_physicalVolume_read geometryRow071_meanGap_read
    geometryRow071_factorMaxima_read geometryRow071_gapWeightedMeans_read
    geometryRow071_jensenBound_read geometryRow071_floor_text_read geometryRow071_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_071_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson072 : SourceJson :=
  (SimplicesBlock036.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped072 : GeometryRow :=
  { simplexId := 72,
    vertexIds := #[39, 35, 33, 24, 23, 21, 20, 16, 15],
    physicalVolume := ((5206567618438689400979569875205051419061 : ℚ) / (7283644249448448000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((122526039980717 : ℚ) / (1834043400000000 : ℚ)), ((122868501453287 : ℚ) / (1834043400000000 : ℚ)), ((817150605202489 : ℚ) / (5502130200000000 : ℚ)), ((10776529259211 : ℚ) / (101891300000000 : ℚ)), ((153668066336143 : ℚ) / (2751065100000000 : ℚ)), ((254705815069673 : ℚ) / (5502130200000000 : ℚ)), ((6403407267953 : ℚ) / (144792900000000 : ℚ)), ((60097879308331 : ℚ) / (1375532550000000 : ℚ)), ((47457053107127 : ℚ) / (1100426040000000 : ℚ)), ((47456759660183 : ℚ) / (1100426040000000 : ℚ))],
    jensenBound := ((680659483735941096414145545637333650681482680962375189625035972040910034779070311655011000252274934546875000000000000000 : ℚ) / (1499064535523962000832245238502712156906723625200314446945563188938179705929241155404432647141449841344353392060003027195427035360926842479 : ℚ)),
    jensenFloorQ96 := (35974035084 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_simplexId_before"
  err.flush

theorem geometryRow072_simplexId_read :
    geometryRowsJson072.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped072.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_vertexIds_before"
  err.flush

theorem geometryRow072_vertexIds_read :
    geometryRowsJson072.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped072.vertexIds := by decide +kernel

noncomputable def geometryRow072_physicalVolumeNumeratorChars : List Char := ['5', '2', '0', '6', '5', '6', '7', '6', '1', '8', '4', '3', '8', '6', '8', '9', '4', '0', '0', '9', '7', '9', '5', '6', '9', '8', '7', '5', '2', '0', '5', '0', '5', '1', '4', '1', '9', '0', '6', '1']
noncomputable def geometryRow072_physicalVolumeDenominatorChars : List Char := ['7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow072_physicalVolumeText : String := String.ofList (geometryRow072_physicalVolumeNumeratorChars ++ '/' :: geometryRow072_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_physicalVolume_before_field"
  err.flush

theorem geometryRow072_physicalVolume_field :
    geometryRowsJson072.getObjVal? "physical_volume" = .ok (.str geometryRow072_physicalVolumeText) := by rfl

theorem geometryRow072_physicalVolume_numerator_no_slash :
    geometryRow072_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow072_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow072_physicalVolumeNumeratorChars = some (5206567618438689400979569875205051419061 : Int) := by decide +kernel

theorem geometryRow072_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow072_physicalVolumeDenominatorChars = some (7283644249448448000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow072_physicalVolume_denominator_nonzero : (7283644249448448000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow072_physicalVolume_parse :
    parseRational geometryRow072_physicalVolumeText = .ok geometryRowsTyped072.physicalVolume :=
  original_rational_fraction_of_chars geometryRow072_physicalVolumeNumeratorChars geometryRow072_physicalVolumeDenominatorChars
    (5206567618438689400979569875205051419061 : Int) (7283644249448448000000000000000000000000000000000000000000000000000 : Int)
    geometryRow072_physicalVolume_numerator_no_slash geometryRow072_physicalVolume_numerator_parse
    geometryRow072_physicalVolume_denominator_parse geometryRow072_physicalVolume_denominator_nonzero

theorem geometryRow072_physicalVolume_read :
    rationalField geometryRowsJson072 "physical_volume" = .ok geometryRowsTyped072.physicalVolume :=
  original_rationalField_of_string geometryRowsJson072 "physical_volume" geometryRow072_physicalVolumeText
    geometryRowsTyped072.physicalVolume geometryRow072_physicalVolume_field geometryRow072_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_physicalVolume_complete"
  err.flush

noncomputable def geometryRow072_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow072_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow072_meanGapText : String := String.ofList (geometryRow072_meanGapNumeratorChars ++ '/' :: geometryRow072_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_meanGap_before_field"
  err.flush

theorem geometryRow072_meanGap_field :
    geometryRowsJson072.getObjVal? "mean_gap" = .ok (.str geometryRow072_meanGapText) := by rfl

theorem geometryRow072_meanGap_numerator_no_slash :
    geometryRow072_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow072_meanGap_numerator_parse :
    SourceJson.intChars geometryRow072_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow072_meanGap_denominator_parse :
    SourceJson.intChars geometryRow072_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow072_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow072_meanGap_parse :
    parseRational geometryRow072_meanGapText = .ok geometryRowsTyped072.meanGap :=
  original_rational_fraction_of_chars geometryRow072_meanGapNumeratorChars geometryRow072_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow072_meanGap_numerator_no_slash geometryRow072_meanGap_numerator_parse
    geometryRow072_meanGap_denominator_parse geometryRow072_meanGap_denominator_nonzero

theorem geometryRow072_meanGap_read :
    rationalField geometryRowsJson072 "mean_gap" = .ok geometryRowsTyped072.meanGap :=
  original_rationalField_of_string geometryRowsJson072 "mean_gap" geometryRow072_meanGapText
    geometryRowsTyped072.meanGap geometryRow072_meanGap_field geometryRow072_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_meanGap_complete"
  err.flush

noncomputable def geometryRow072_jensenBoundNumeratorChars : List Char := ['6', '8', '0', '6', '5', '9', '4', '8', '3', '7', '3', '5', '9', '4', '1', '0', '9', '6', '4', '1', '4', '1', '4', '5', '5', '4', '5', '6', '3', '7', '3', '3', '3', '6', '5', '0', '6', '8', '1', '4', '8', '2', '6', '8', '0', '9', '6', '2', '3', '7', '5', '1', '8', '9', '6', '2', '5', '0', '3', '5', '9', '7', '2', '0', '4', '0', '9', '1', '0', '0', '3', '4', '7', '7', '9', '0', '7', '0', '3', '1', '1', '6', '5', '5', '0', '1', '1', '0', '0', '0', '2', '5', '2', '2', '7', '4', '9', '3', '4', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow072_jensenBoundDenominatorChars : List Char := ['1', '4', '9', '9', '0', '6', '4', '5', '3', '5', '5', '2', '3', '9', '6', '2', '0', '0', '0', '8', '3', '2', '2', '4', '5', '2', '3', '8', '5', '0', '2', '7', '1', '2', '1', '5', '6', '9', '0', '6', '7', '2', '3', '6', '2', '5', '2', '0', '0', '3', '1', '4', '4', '4', '6', '9', '4', '5', '5', '6', '3', '1', '8', '8', '9', '3', '8', '1', '7', '9', '7', '0', '5', '9', '2', '9', '2', '4', '1', '1', '5', '5', '4', '0', '4', '4', '3', '2', '6', '4', '7', '1', '4', '1', '4', '4', '9', '8', '4', '1', '3', '4', '4', '3', '5', '3', '3', '9', '2', '0', '6', '0', '0', '0', '3', '0', '2', '7', '1', '9', '5', '4', '2', '7', '0', '3', '5', '3', '6', '0', '9', '2', '6', '8', '4', '2', '4', '7', '9']
noncomputable def geometryRow072_jensenBoundText : String := String.ofList (geometryRow072_jensenBoundNumeratorChars ++ '/' :: geometryRow072_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_jensenBound_before_field"
  err.flush

theorem geometryRow072_jensenBound_field :
    geometryRowsJson072.getObjVal? "jensen_bound" = .ok (.str geometryRow072_jensenBoundText) := by rfl

theorem geometryRow072_jensenBound_numerator_no_slash :
    geometryRow072_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow072_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow072_jensenBoundNumeratorChars = some (680659483735941096414145545637333650681482680962375189625035972040910034779070311655011000252274934546875000000000000000 : Int) := by decide +kernel

theorem geometryRow072_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow072_jensenBoundDenominatorChars = some (1499064535523962000832245238502712156906723625200314446945563188938179705929241155404432647141449841344353392060003027195427035360926842479 : Int) := by decide +kernel

theorem geometryRow072_jensenBound_denominator_nonzero : (1499064535523962000832245238502712156906723625200314446945563188938179705929241155404432647141449841344353392060003027195427035360926842479 : Int) ≠ 0 := by decide +kernel

theorem geometryRow072_jensenBound_parse :
    parseRational geometryRow072_jensenBoundText = .ok geometryRowsTyped072.jensenBound :=
  original_rational_fraction_of_chars geometryRow072_jensenBoundNumeratorChars geometryRow072_jensenBoundDenominatorChars
    (680659483735941096414145545637333650681482680962375189625035972040910034779070311655011000252274934546875000000000000000 : Int) (1499064535523962000832245238502712156906723625200314446945563188938179705929241155404432647141449841344353392060003027195427035360926842479 : Int)
    geometryRow072_jensenBound_numerator_no_slash geometryRow072_jensenBound_numerator_parse
    geometryRow072_jensenBound_denominator_parse geometryRow072_jensenBound_denominator_nonzero

theorem geometryRow072_jensenBound_read :
    rationalField geometryRowsJson072 "jensen_bound" = .ok geometryRowsTyped072.jensenBound :=
  original_rationalField_of_string geometryRowsJson072 "jensen_bound" geometryRow072_jensenBoundText
    geometryRowsTyped072.jensenBound geometryRow072_jensenBound_field geometryRow072_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_factorMaxima_before"
  err.flush

theorem geometryRow072_factorMaxima_read :
    rationalArrayField geometryRowsJson072 "factor_maxima" = .ok geometryRowsTyped072.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_gapWeightedMeans_before"
  err.flush

theorem geometryRow072_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson072 "gap_weighted_means" = .ok geometryRowsTyped072.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow072_floorChars : List Char := ['3', '5', '9', '7', '4', '0', '3', '5', '0', '8', '4']
noncomputable def geometryRow072_floorText : String := String.ofList geometryRow072_floorChars

theorem geometryRow072_floor_text_read :
    geometryRowsJson072.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow072_floorText := by rfl

theorem geometryRow072_floor_chars_parse :
    SourceJson.intChars geometryRow072_floorChars = some (35974035084 : Int) := by decide +kernel

theorem geometryRow072_floor_parse :
    parseInteger geometryRow072_floorText = .ok geometryRowsTyped072.jensenFloorQ96 := by
  simp only [geometryRow072_floorText, parseInteger, String.toList_ofList, geometryRow072_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_072 :
    decodeGeometryRow geometryRowsJson072 = .ok geometryRowsTyped072 :=
  original_geometryRow_of_fields geometryRowsJson072 geometryRowsTyped072 geometryRow072_floorText
    geometryRow072_simplexId_read geometryRow072_vertexIds_read
    geometryRow072_physicalVolume_read geometryRow072_meanGap_read
    geometryRow072_factorMaxima_read geometryRow072_gapWeightedMeans_read
    geometryRow072_jensenBound_read geometryRow072_floor_text_read geometryRow072_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_072_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock036 : List SourceJson := [geometryRowsJson071, geometryRowsJson072]
noncomputable def geometryRowsTypedBlock036 : List (GeometryRow) := [geometryRowsTyped071, geometryRowsTyped072]
noncomputable def geometryRowsTypedThroughBlock036 : List (GeometryRow) := geometryRowsTypedThroughBlock035 ++ geometryRowsTypedBlock036

theorem geometry_Rows_block_036_push_eq (acc : List SourceJson) :
    SimplicesBlock036.blockPush acc = [geometryRowsJson072, geometryRowsJson071] ++ acc := by rfl

theorem geometry_Rows_block_036_reverse (acc : List SourceJson) :
    (SimplicesBlock036.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock036 := by
  rw [geometry_Rows_block_036_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_036 :
    geometryRowsJsonBlock036.mapM decodeGeometryRow = .ok geometryRowsTypedBlock036 := by
  simp only [geometryRowsJsonBlock036, geometryRowsTypedBlock036, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_071, decode_geometry_Rows_072]
  rfl

theorem decode_geometry_Rows_through_block_036 :
    SimplicesValue.arrayAcc037.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock036 := by
  change (SimplicesBlock036.blockPush SimplicesValue.arrayAcc036).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_036_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_035, decode_geometry_Rows_block_036]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_036_complete"
  err.flush

#print axioms geometryRow071_simplexId_read
#print axioms geometryRow071_vertexIds_read
#print axioms geometryRow071_physicalVolume_field
#print axioms geometryRow071_physicalVolume_numerator_no_slash
#print axioms geometryRow071_physicalVolume_numerator_parse
#print axioms geometryRow071_physicalVolume_denominator_parse
#print axioms geometryRow071_physicalVolume_denominator_nonzero
#print axioms geometryRow071_physicalVolume_parse
#print axioms geometryRow071_physicalVolume_read
#print axioms geometryRow071_meanGap_field
#print axioms geometryRow071_meanGap_numerator_no_slash
#print axioms geometryRow071_meanGap_numerator_parse
#print axioms geometryRow071_meanGap_denominator_parse
#print axioms geometryRow071_meanGap_denominator_nonzero
#print axioms geometryRow071_meanGap_parse
#print axioms geometryRow071_meanGap_read
#print axioms geometryRow071_jensenBound_field
#print axioms geometryRow071_jensenBound_numerator_no_slash
#print axioms geometryRow071_jensenBound_numerator_parse
#print axioms geometryRow071_jensenBound_denominator_parse
#print axioms geometryRow071_jensenBound_denominator_nonzero
#print axioms geometryRow071_jensenBound_parse
#print axioms geometryRow071_jensenBound_read
#print axioms geometryRow071_factorMaxima_read
#print axioms geometryRow071_gapWeightedMeans_read
#print axioms geometryRow071_floor_text_read
#print axioms geometryRow071_floor_chars_parse
#print axioms geometryRow071_floor_parse
#print axioms decode_geometry_Rows_071
#print axioms geometryRow072_simplexId_read
#print axioms geometryRow072_vertexIds_read
#print axioms geometryRow072_physicalVolume_field
#print axioms geometryRow072_physicalVolume_numerator_no_slash
#print axioms geometryRow072_physicalVolume_numerator_parse
#print axioms geometryRow072_physicalVolume_denominator_parse
#print axioms geometryRow072_physicalVolume_denominator_nonzero
#print axioms geometryRow072_physicalVolume_parse
#print axioms geometryRow072_physicalVolume_read
#print axioms geometryRow072_meanGap_field
#print axioms geometryRow072_meanGap_numerator_no_slash
#print axioms geometryRow072_meanGap_numerator_parse
#print axioms geometryRow072_meanGap_denominator_parse
#print axioms geometryRow072_meanGap_denominator_nonzero
#print axioms geometryRow072_meanGap_parse
#print axioms geometryRow072_meanGap_read
#print axioms geometryRow072_jensenBound_field
#print axioms geometryRow072_jensenBound_numerator_no_slash
#print axioms geometryRow072_jensenBound_numerator_parse
#print axioms geometryRow072_jensenBound_denominator_parse
#print axioms geometryRow072_jensenBound_denominator_nonzero
#print axioms geometryRow072_jensenBound_parse
#print axioms geometryRow072_jensenBound_read
#print axioms geometryRow072_factorMaxima_read
#print axioms geometryRow072_gapWeightedMeans_read
#print axioms geometryRow072_floor_text_read
#print axioms geometryRow072_floor_chars_parse
#print axioms geometryRow072_floor_parse
#print axioms decode_geometry_Rows_072
#print axioms geometry_Rows_block_036_push_eq
#print axioms geometry_Rows_block_036_reverse
#print axioms decode_geometry_Rows_block_036
#print axioms decode_geometry_Rows_through_block_036

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
