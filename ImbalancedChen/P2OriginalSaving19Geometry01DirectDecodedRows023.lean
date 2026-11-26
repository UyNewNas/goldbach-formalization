import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows022

/-! Original simplices typed block 23, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson045 : SourceJson :=
  (SimplicesBlock023.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped045 : GeometryRow :=
  { simplexId := 45,
    vertexIds := #[39, 35, 24, 23, 21, 20, 16, 15, 0],
    physicalVolume := ((176907485205860125438651304752854803503111 : ℚ) / (29134576997793792000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((52534315802309 : ℚ) / (733617360000000 : ℚ)), ((52671300391337 : ℚ) / (733617360000000 : ℚ)), ((322591941958477 : ℚ) / (2200852080000000 : ℚ)), ((64038841961519 : ℚ) / (611347800000000 : ℚ)), ((613681756582273 : ℚ) / (11004260400000000 : ℚ)), ((530753130751939 : ℚ) / (11004260400000000 : ℚ)), ((25078076654699 : ℚ) / (579171600000000 : ℚ)), ((470607538541501 : ℚ) / (11004260400000000 : ℚ)), ((464395035146123 : ℚ) / (11004260400000000 : ℚ)), ((464392100676683 : ℚ) / (11004260400000000 : ℚ))],
    jensenBound := ((15501165882648187824904928284130891162185624382386021302526286933809351569273836723834266257601456763635200000000000000000000 : ℚ) / (4308069443826095890296967930659318913739490509787848792801154363266141920679384004266307345127150263547068813750929135251975267501316782225753 : ℚ)),
    jensenFloorQ96 := (285076391113 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_simplexId_before"
  err.flush

theorem geometryRow045_simplexId_read :
    geometryRowsJson045.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped045.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_vertexIds_before"
  err.flush

theorem geometryRow045_vertexIds_read :
    geometryRowsJson045.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped045.vertexIds := by decide +kernel

noncomputable def geometryRow045_physicalVolumeNumeratorChars : List Char := ['1', '7', '6', '9', '0', '7', '4', '8', '5', '2', '0', '5', '8', '6', '0', '1', '2', '5', '4', '3', '8', '6', '5', '1', '3', '0', '4', '7', '5', '2', '8', '5', '4', '8', '0', '3', '5', '0', '3', '1', '1', '1']
noncomputable def geometryRow045_physicalVolumeDenominatorChars : List Char := ['2', '9', '1', '3', '4', '5', '7', '6', '9', '9', '7', '7', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_physicalVolumeText : String := String.ofList (geometryRow045_physicalVolumeNumeratorChars ++ '/' :: geometryRow045_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_physicalVolume_before_field"
  err.flush

theorem geometryRow045_physicalVolume_field :
    geometryRowsJson045.getObjVal? "physical_volume" = .ok (.str geometryRow045_physicalVolumeText) := by rfl

theorem geometryRow045_physicalVolume_numerator_no_slash :
    geometryRow045_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeNumeratorChars = some (176907485205860125438651304752854803503111 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeDenominatorChars = some (29134576997793792000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_nonzero : (29134576997793792000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_physicalVolume_parse :
    parseRational geometryRow045_physicalVolumeText = .ok geometryRowsTyped045.physicalVolume :=
  original_rational_fraction_of_chars geometryRow045_physicalVolumeNumeratorChars geometryRow045_physicalVolumeDenominatorChars
    (176907485205860125438651304752854803503111 : Int) (29134576997793792000000000000000000000000000000000000000000000000000 : Int)
    geometryRow045_physicalVolume_numerator_no_slash geometryRow045_physicalVolume_numerator_parse
    geometryRow045_physicalVolume_denominator_parse geometryRow045_physicalVolume_denominator_nonzero

theorem geometryRow045_physicalVolume_read :
    rationalField geometryRowsJson045 "physical_volume" = .ok geometryRowsTyped045.physicalVolume :=
  original_rationalField_of_string geometryRowsJson045 "physical_volume" geometryRow045_physicalVolumeText
    geometryRowsTyped045.physicalVolume geometryRow045_physicalVolume_field geometryRow045_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_physicalVolume_complete"
  err.flush

noncomputable def geometryRow045_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow045_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_meanGapText : String := String.ofList (geometryRow045_meanGapNumeratorChars ++ '/' :: geometryRow045_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_meanGap_before_field"
  err.flush

theorem geometryRow045_meanGap_field :
    geometryRowsJson045.getObjVal? "mean_gap" = .ok (.str geometryRow045_meanGapText) := by rfl

theorem geometryRow045_meanGap_numerator_no_slash :
    geometryRow045_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_meanGap_numerator_parse :
    SourceJson.intChars geometryRow045_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_parse :
    SourceJson.intChars geometryRow045_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_meanGap_parse :
    parseRational geometryRow045_meanGapText = .ok geometryRowsTyped045.meanGap :=
  original_rational_fraction_of_chars geometryRow045_meanGapNumeratorChars geometryRow045_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow045_meanGap_numerator_no_slash geometryRow045_meanGap_numerator_parse
    geometryRow045_meanGap_denominator_parse geometryRow045_meanGap_denominator_nonzero

theorem geometryRow045_meanGap_read :
    rationalField geometryRowsJson045 "mean_gap" = .ok geometryRowsTyped045.meanGap :=
  original_rationalField_of_string geometryRowsJson045 "mean_gap" geometryRow045_meanGapText
    geometryRowsTyped045.meanGap geometryRow045_meanGap_field geometryRow045_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_meanGap_complete"
  err.flush

noncomputable def geometryRow045_jensenBoundNumeratorChars : List Char := ['1', '5', '5', '0', '1', '1', '6', '5', '8', '8', '2', '6', '4', '8', '1', '8', '7', '8', '2', '4', '9', '0', '4', '9', '2', '8', '2', '8', '4', '1', '3', '0', '8', '9', '1', '1', '6', '2', '1', '8', '5', '6', '2', '4', '3', '8', '2', '3', '8', '6', '0', '2', '1', '3', '0', '2', '5', '2', '6', '2', '8', '6', '9', '3', '3', '8', '0', '9', '3', '5', '1', '5', '6', '9', '2', '7', '3', '8', '3', '6', '7', '2', '3', '8', '3', '4', '2', '6', '6', '2', '5', '7', '6', '0', '1', '4', '5', '6', '7', '6', '3', '6', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_jensenBoundDenominatorChars : List Char := ['4', '3', '0', '8', '0', '6', '9', '4', '4', '3', '8', '2', '6', '0', '9', '5', '8', '9', '0', '2', '9', '6', '9', '6', '7', '9', '3', '0', '6', '5', '9', '3', '1', '8', '9', '1', '3', '7', '3', '9', '4', '9', '0', '5', '0', '9', '7', '8', '7', '8', '4', '8', '7', '9', '2', '8', '0', '1', '1', '5', '4', '3', '6', '3', '2', '6', '6', '1', '4', '1', '9', '2', '0', '6', '7', '9', '3', '8', '4', '0', '0', '4', '2', '6', '6', '3', '0', '7', '3', '4', '5', '1', '2', '7', '1', '5', '0', '2', '6', '3', '5', '4', '7', '0', '6', '8', '8', '1', '3', '7', '5', '0', '9', '2', '9', '1', '3', '5', '2', '5', '1', '9', '7', '5', '2', '6', '7', '5', '0', '1', '3', '1', '6', '7', '8', '2', '2', '2', '5', '7', '5', '3']
noncomputable def geometryRow045_jensenBoundText : String := String.ofList (geometryRow045_jensenBoundNumeratorChars ++ '/' :: geometryRow045_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_jensenBound_before_field"
  err.flush

theorem geometryRow045_jensenBound_field :
    geometryRowsJson045.getObjVal? "jensen_bound" = .ok (.str geometryRow045_jensenBoundText) := by rfl

theorem geometryRow045_jensenBound_numerator_no_slash :
    geometryRow045_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow045_jensenBoundNumeratorChars = some (15501165882648187824904928284130891162185624382386021302526286933809351569273836723834266257601456763635200000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow045_jensenBoundDenominatorChars = some (4308069443826095890296967930659318913739490509787848792801154363266141920679384004266307345127150263547068813750929135251975267501316782225753 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_nonzero : (4308069443826095890296967930659318913739490509787848792801154363266141920679384004266307345127150263547068813750929135251975267501316782225753 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_jensenBound_parse :
    parseRational geometryRow045_jensenBoundText = .ok geometryRowsTyped045.jensenBound :=
  original_rational_fraction_of_chars geometryRow045_jensenBoundNumeratorChars geometryRow045_jensenBoundDenominatorChars
    (15501165882648187824904928284130891162185624382386021302526286933809351569273836723834266257601456763635200000000000000000000 : Int) (4308069443826095890296967930659318913739490509787848792801154363266141920679384004266307345127150263547068813750929135251975267501316782225753 : Int)
    geometryRow045_jensenBound_numerator_no_slash geometryRow045_jensenBound_numerator_parse
    geometryRow045_jensenBound_denominator_parse geometryRow045_jensenBound_denominator_nonzero

theorem geometryRow045_jensenBound_read :
    rationalField geometryRowsJson045 "jensen_bound" = .ok geometryRowsTyped045.jensenBound :=
  original_rationalField_of_string geometryRowsJson045 "jensen_bound" geometryRow045_jensenBoundText
    geometryRowsTyped045.jensenBound geometryRow045_jensenBound_field geometryRow045_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_factorMaxima_before"
  err.flush

theorem geometryRow045_factorMaxima_read :
    rationalArrayField geometryRowsJson045 "factor_maxima" = .ok geometryRowsTyped045.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_gapWeightedMeans_before"
  err.flush

theorem geometryRow045_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson045 "gap_weighted_means" = .ok geometryRowsTyped045.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow045_floorChars : List Char := ['2', '8', '5', '0', '7', '6', '3', '9', '1', '1', '1', '3']
noncomputable def geometryRow045_floorText : String := String.ofList geometryRow045_floorChars

theorem geometryRow045_floor_text_read :
    geometryRowsJson045.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow045_floorText := by rfl

theorem geometryRow045_floor_chars_parse :
    SourceJson.intChars geometryRow045_floorChars = some (285076391113 : Int) := by decide +kernel

theorem geometryRow045_floor_parse :
    parseInteger geometryRow045_floorText = .ok geometryRowsTyped045.jensenFloorQ96 := by
  simp only [geometryRow045_floorText, parseInteger, String.toList_ofList, geometryRow045_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_045 :
    decodeGeometryRow geometryRowsJson045 = .ok geometryRowsTyped045 :=
  original_geometryRow_of_fields geometryRowsJson045 geometryRowsTyped045 geometryRow045_floorText
    geometryRow045_simplexId_read geometryRow045_vertexIds_read
    geometryRow045_physicalVolume_read geometryRow045_meanGap_read
    geometryRow045_factorMaxima_read geometryRow045_gapWeightedMeans_read
    geometryRow045_jensenBound_read geometryRow045_floor_text_read geometryRow045_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_045_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson046 : SourceJson :=
  (SimplicesBlock023.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped046 : GeometryRow :=
  { simplexId := 46,
    vertexIds := #[39, 35, 24, 23, 21, 20, 19, 2, 0],
    physicalVolume := ((29657167443559868609606917132914366623655767 : ℚ) / (940731751973800378368000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((899153113 : ℚ) / (1110193000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((658482481754353178265421 : ℚ) / (8732302122503142240000000 : ℚ)), ((6550426616326749793128139 : ℚ) / (85576560800530793952000000 : ℚ)), ((186232655266411222715395901 : ℚ) / (1283648412007961909280000000 : ℚ)), ((115101552539082803532032197 : ℚ) / (1069707010006634924400000000 : ℚ)), ((123864254452371173867870101 : ℚ) / (2139414020013269848800000000 : ℚ)), ((306960783230871213408356939 : ℚ) / (6418242060039809546400000000 : ℚ)), ((14014725486249165968061629 : ℚ) / (337802213686305765600000000 : ℚ)), ((262852651290038001650615471 : ℚ) / (6418242060039809546400000000 : ℚ)), ((259578320176816356919726333 : ℚ) / (6418242060039809546400000000 : ℚ)), ((255161541851792668922931103 : ℚ) / (6418242060039809546400000000 : ℚ))],
    jensenBound := ((898750607870118820055984602299142059866546367796553324796105673829225837834985426591168162635759242681530280070557829289643760295558129663088009983512470502756802593039215648979204852767161624231129176566365000710799360000000000000000000000000 : ℚ) / (5998245967712489190092185010160859171995716073339358762179186944355381584931265857827617390276964820678517930973413598881955981016664630813808271360354579549340223832639719845830256478952340642202700663090615656564963594509372265376989964684745479332774399 : ℚ)),
    jensenFloorQ96 := (11871196947144054 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_simplexId_before"
  err.flush

theorem geometryRow046_simplexId_read :
    geometryRowsJson046.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped046.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_vertexIds_before"
  err.flush

theorem geometryRow046_vertexIds_read :
    geometryRowsJson046.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped046.vertexIds := by decide +kernel

noncomputable def geometryRow046_physicalVolumeNumeratorChars : List Char := ['2', '9', '6', '5', '7', '1', '6', '7', '4', '4', '3', '5', '5', '9', '8', '6', '8', '6', '0', '9', '6', '0', '6', '9', '1', '7', '1', '3', '2', '9', '1', '4', '3', '6', '6', '6', '2', '3', '6', '5', '5', '7', '6', '7']
noncomputable def geometryRow046_physicalVolumeDenominatorChars : List Char := ['9', '4', '0', '7', '3', '1', '7', '5', '1', '9', '7', '3', '8', '0', '0', '3', '7', '8', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_physicalVolumeText : String := String.ofList (geometryRow046_physicalVolumeNumeratorChars ++ '/' :: geometryRow046_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_physicalVolume_before_field"
  err.flush

theorem geometryRow046_physicalVolume_field :
    geometryRowsJson046.getObjVal? "physical_volume" = .ok (.str geometryRow046_physicalVolumeText) := by rfl

theorem geometryRow046_physicalVolume_numerator_no_slash :
    geometryRow046_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeNumeratorChars = some (29657167443559868609606917132914366623655767 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeDenominatorChars = some (940731751973800378368000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_nonzero : (940731751973800378368000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_physicalVolume_parse :
    parseRational geometryRow046_physicalVolumeText = .ok geometryRowsTyped046.physicalVolume :=
  original_rational_fraction_of_chars geometryRow046_physicalVolumeNumeratorChars geometryRow046_physicalVolumeDenominatorChars
    (29657167443559868609606917132914366623655767 : Int) (940731751973800378368000000000000000000000000000000000000000000000 : Int)
    geometryRow046_physicalVolume_numerator_no_slash geometryRow046_physicalVolume_numerator_parse
    geometryRow046_physicalVolume_denominator_parse geometryRow046_physicalVolume_denominator_nonzero

theorem geometryRow046_physicalVolume_read :
    rationalField geometryRowsJson046 "physical_volume" = .ok geometryRowsTyped046.physicalVolume :=
  original_rationalField_of_string geometryRowsJson046 "physical_volume" geometryRow046_physicalVolumeText
    geometryRowsTyped046.physicalVolume geometryRow046_physicalVolume_field geometryRow046_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_physicalVolume_complete"
  err.flush

noncomputable def geometryRow046_meanGapNumeratorChars : List Char := ['8', '9', '9', '1', '5', '3', '1', '1', '3']
noncomputable def geometryRow046_meanGapDenominatorChars : List Char := ['1', '1', '1', '0', '1', '9', '3', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_meanGapText : String := String.ofList (geometryRow046_meanGapNumeratorChars ++ '/' :: geometryRow046_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_meanGap_before_field"
  err.flush

theorem geometryRow046_meanGap_field :
    geometryRowsJson046.getObjVal? "mean_gap" = .ok (.str geometryRow046_meanGapText) := by rfl

theorem geometryRow046_meanGap_numerator_no_slash :
    geometryRow046_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_meanGap_numerator_parse :
    SourceJson.intChars geometryRow046_meanGapNumeratorChars = some (899153113 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_parse :
    SourceJson.intChars geometryRow046_meanGapDenominatorChars = some (1110193000000 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_nonzero : (1110193000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_meanGap_parse :
    parseRational geometryRow046_meanGapText = .ok geometryRowsTyped046.meanGap :=
  original_rational_fraction_of_chars geometryRow046_meanGapNumeratorChars geometryRow046_meanGapDenominatorChars
    (899153113 : Int) (1110193000000 : Int)
    geometryRow046_meanGap_numerator_no_slash geometryRow046_meanGap_numerator_parse
    geometryRow046_meanGap_denominator_parse geometryRow046_meanGap_denominator_nonzero

theorem geometryRow046_meanGap_read :
    rationalField geometryRowsJson046 "mean_gap" = .ok geometryRowsTyped046.meanGap :=
  original_rationalField_of_string geometryRowsJson046 "mean_gap" geometryRow046_meanGapText
    geometryRowsTyped046.meanGap geometryRow046_meanGap_field geometryRow046_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_meanGap_complete"
  err.flush

noncomputable def geometryRow046_jensenBoundNumeratorChars : List Char := ['8', '9', '8', '7', '5', '0', '6', '0', '7', '8', '7', '0', '1', '1', '8', '8', '2', '0', '0', '5', '5', '9', '8', '4', '6', '0', '2', '2', '9', '9', '1', '4', '2', '0', '5', '9', '8', '6', '6', '5', '4', '6', '3', '6', '7', '7', '9', '6', '5', '5', '3', '3', '2', '4', '7', '9', '6', '1', '0', '5', '6', '7', '3', '8', '2', '9', '2', '2', '5', '8', '3', '7', '8', '3', '4', '9', '8', '5', '4', '2', '6', '5', '9', '1', '1', '6', '8', '1', '6', '2', '6', '3', '5', '7', '5', '9', '2', '4', '2', '6', '8', '1', '5', '3', '0', '2', '8', '0', '0', '7', '0', '5', '5', '7', '8', '2', '9', '2', '8', '9', '6', '4', '3', '7', '6', '0', '2', '9', '5', '5', '5', '8', '1', '2', '9', '6', '6', '3', '0', '8', '8', '0', '0', '9', '9', '8', '3', '5', '1', '2', '4', '7', '0', '5', '0', '2', '7', '5', '6', '8', '0', '2', '5', '9', '3', '0', '3', '9', '2', '1', '5', '6', '4', '8', '9', '7', '9', '2', '0', '4', '8', '5', '2', '7', '6', '7', '1', '6', '1', '6', '2', '4', '2', '3', '1', '1', '2', '9', '1', '7', '6', '5', '6', '6', '3', '6', '5', '0', '0', '0', '7', '1', '0', '7', '9', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_jensenBoundDenominatorChars : List Char := ['5', '9', '9', '8', '2', '4', '5', '9', '6', '7', '7', '1', '2', '4', '8', '9', '1', '9', '0', '0', '9', '2', '1', '8', '5', '0', '1', '0', '1', '6', '0', '8', '5', '9', '1', '7', '1', '9', '9', '5', '7', '1', '6', '0', '7', '3', '3', '3', '9', '3', '5', '8', '7', '6', '2', '1', '7', '9', '1', '8', '6', '9', '4', '4', '3', '5', '5', '3', '8', '1', '5', '8', '4', '9', '3', '1', '2', '6', '5', '8', '5', '7', '8', '2', '7', '6', '1', '7', '3', '9', '0', '2', '7', '6', '9', '6', '4', '8', '2', '0', '6', '7', '8', '5', '1', '7', '9', '3', '0', '9', '7', '3', '4', '1', '3', '5', '9', '8', '8', '8', '1', '9', '5', '5', '9', '8', '1', '0', '1', '6', '6', '6', '4', '6', '3', '0', '8', '1', '3', '8', '0', '8', '2', '7', '1', '3', '6', '0', '3', '5', '4', '5', '7', '9', '5', '4', '9', '3', '4', '0', '2', '2', '3', '8', '3', '2', '6', '3', '9', '7', '1', '9', '8', '4', '5', '8', '3', '0', '2', '5', '6', '4', '7', '8', '9', '5', '2', '3', '4', '0', '6', '4', '2', '2', '0', '2', '7', '0', '0', '6', '6', '3', '0', '9', '0', '6', '1', '5', '6', '5', '6', '5', '6', '4', '9', '6', '3', '5', '9', '4', '5', '0', '9', '3', '7', '2', '2', '6', '5', '3', '7', '6', '9', '8', '9', '9', '6', '4', '6', '8', '4', '7', '4', '5', '4', '7', '9', '3', '3', '2', '7', '7', '4', '3', '9', '9']
noncomputable def geometryRow046_jensenBoundText : String := String.ofList (geometryRow046_jensenBoundNumeratorChars ++ '/' :: geometryRow046_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_jensenBound_before_field"
  err.flush

theorem geometryRow046_jensenBound_field :
    geometryRowsJson046.getObjVal? "jensen_bound" = .ok (.str geometryRow046_jensenBoundText) := by rfl

theorem geometryRow046_jensenBound_numerator_no_slash :
    geometryRow046_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow046_jensenBoundNumeratorChars = some (898750607870118820055984602299142059866546367796553324796105673829225837834985426591168162635759242681530280070557829289643760295558129663088009983512470502756802593039215648979204852767161624231129176566365000710799360000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow046_jensenBoundDenominatorChars = some (5998245967712489190092185010160859171995716073339358762179186944355381584931265857827617390276964820678517930973413598881955981016664630813808271360354579549340223832639719845830256478952340642202700663090615656564963594509372265376989964684745479332774399 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_nonzero : (5998245967712489190092185010160859171995716073339358762179186944355381584931265857827617390276964820678517930973413598881955981016664630813808271360354579549340223832639719845830256478952340642202700663090615656564963594509372265376989964684745479332774399 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_jensenBound_parse :
    parseRational geometryRow046_jensenBoundText = .ok geometryRowsTyped046.jensenBound :=
  original_rational_fraction_of_chars geometryRow046_jensenBoundNumeratorChars geometryRow046_jensenBoundDenominatorChars
    (898750607870118820055984602299142059866546367796553324796105673829225837834985426591168162635759242681530280070557829289643760295558129663088009983512470502756802593039215648979204852767161624231129176566365000710799360000000000000000000000000 : Int) (5998245967712489190092185010160859171995716073339358762179186944355381584931265857827617390276964820678517930973413598881955981016664630813808271360354579549340223832639719845830256478952340642202700663090615656564963594509372265376989964684745479332774399 : Int)
    geometryRow046_jensenBound_numerator_no_slash geometryRow046_jensenBound_numerator_parse
    geometryRow046_jensenBound_denominator_parse geometryRow046_jensenBound_denominator_nonzero

theorem geometryRow046_jensenBound_read :
    rationalField geometryRowsJson046 "jensen_bound" = .ok geometryRowsTyped046.jensenBound :=
  original_rationalField_of_string geometryRowsJson046 "jensen_bound" geometryRow046_jensenBoundText
    geometryRowsTyped046.jensenBound geometryRow046_jensenBound_field geometryRow046_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_factorMaxima_before"
  err.flush

theorem geometryRow046_factorMaxima_read :
    rationalArrayField geometryRowsJson046 "factor_maxima" = .ok geometryRowsTyped046.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_gapWeightedMeans_before"
  err.flush

theorem geometryRow046_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson046 "gap_weighted_means" = .ok geometryRowsTyped046.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow046_floorChars : List Char := ['1', '1', '8', '7', '1', '1', '9', '6', '9', '4', '7', '1', '4', '4', '0', '5', '4']
noncomputable def geometryRow046_floorText : String := String.ofList geometryRow046_floorChars

theorem geometryRow046_floor_text_read :
    geometryRowsJson046.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow046_floorText := by rfl

theorem geometryRow046_floor_chars_parse :
    SourceJson.intChars geometryRow046_floorChars = some (11871196947144054 : Int) := by decide +kernel

theorem geometryRow046_floor_parse :
    parseInteger geometryRow046_floorText = .ok geometryRowsTyped046.jensenFloorQ96 := by
  simp only [geometryRow046_floorText, parseInteger, String.toList_ofList, geometryRow046_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_046 :
    decodeGeometryRow geometryRowsJson046 = .ok geometryRowsTyped046 :=
  original_geometryRow_of_fields geometryRowsJson046 geometryRowsTyped046 geometryRow046_floorText
    geometryRow046_simplexId_read geometryRow046_vertexIds_read
    geometryRow046_physicalVolume_read geometryRow046_meanGap_read
    geometryRow046_factorMaxima_read geometryRow046_gapWeightedMeans_read
    geometryRow046_jensenBound_read geometryRow046_floor_text_read geometryRow046_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_046_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock023 : List SourceJson := [geometryRowsJson045, geometryRowsJson046]
noncomputable def geometryRowsTypedBlock023 : List (GeometryRow) := [geometryRowsTyped045, geometryRowsTyped046]
noncomputable def geometryRowsTypedThroughBlock023 : List (GeometryRow) := geometryRowsTypedThroughBlock022 ++ geometryRowsTypedBlock023

theorem geometry_Rows_block_023_push_eq (acc : List SourceJson) :
    SimplicesBlock023.blockPush acc = [geometryRowsJson046, geometryRowsJson045] ++ acc := by rfl

theorem geometry_Rows_block_023_reverse (acc : List SourceJson) :
    (SimplicesBlock023.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock023 := by
  rw [geometry_Rows_block_023_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_023 :
    geometryRowsJsonBlock023.mapM decodeGeometryRow = .ok geometryRowsTypedBlock023 := by
  simp only [geometryRowsJsonBlock023, geometryRowsTypedBlock023, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_045, decode_geometry_Rows_046]
  rfl

theorem decode_geometry_Rows_through_block_023 :
    SimplicesValue.arrayAcc024.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock023 := by
  change (SimplicesBlock023.blockPush SimplicesValue.arrayAcc023).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_023_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_022, decode_geometry_Rows_block_023]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_023_complete"
  err.flush

#print axioms geometryRow045_simplexId_read
#print axioms geometryRow045_vertexIds_read
#print axioms geometryRow045_physicalVolume_field
#print axioms geometryRow045_physicalVolume_numerator_no_slash
#print axioms geometryRow045_physicalVolume_numerator_parse
#print axioms geometryRow045_physicalVolume_denominator_parse
#print axioms geometryRow045_physicalVolume_denominator_nonzero
#print axioms geometryRow045_physicalVolume_parse
#print axioms geometryRow045_physicalVolume_read
#print axioms geometryRow045_meanGap_field
#print axioms geometryRow045_meanGap_numerator_no_slash
#print axioms geometryRow045_meanGap_numerator_parse
#print axioms geometryRow045_meanGap_denominator_parse
#print axioms geometryRow045_meanGap_denominator_nonzero
#print axioms geometryRow045_meanGap_parse
#print axioms geometryRow045_meanGap_read
#print axioms geometryRow045_jensenBound_field
#print axioms geometryRow045_jensenBound_numerator_no_slash
#print axioms geometryRow045_jensenBound_numerator_parse
#print axioms geometryRow045_jensenBound_denominator_parse
#print axioms geometryRow045_jensenBound_denominator_nonzero
#print axioms geometryRow045_jensenBound_parse
#print axioms geometryRow045_jensenBound_read
#print axioms geometryRow045_factorMaxima_read
#print axioms geometryRow045_gapWeightedMeans_read
#print axioms geometryRow045_floor_text_read
#print axioms geometryRow045_floor_chars_parse
#print axioms geometryRow045_floor_parse
#print axioms decode_geometry_Rows_045
#print axioms geometryRow046_simplexId_read
#print axioms geometryRow046_vertexIds_read
#print axioms geometryRow046_physicalVolume_field
#print axioms geometryRow046_physicalVolume_numerator_no_slash
#print axioms geometryRow046_physicalVolume_numerator_parse
#print axioms geometryRow046_physicalVolume_denominator_parse
#print axioms geometryRow046_physicalVolume_denominator_nonzero
#print axioms geometryRow046_physicalVolume_parse
#print axioms geometryRow046_physicalVolume_read
#print axioms geometryRow046_meanGap_field
#print axioms geometryRow046_meanGap_numerator_no_slash
#print axioms geometryRow046_meanGap_numerator_parse
#print axioms geometryRow046_meanGap_denominator_parse
#print axioms geometryRow046_meanGap_denominator_nonzero
#print axioms geometryRow046_meanGap_parse
#print axioms geometryRow046_meanGap_read
#print axioms geometryRow046_jensenBound_field
#print axioms geometryRow046_jensenBound_numerator_no_slash
#print axioms geometryRow046_jensenBound_numerator_parse
#print axioms geometryRow046_jensenBound_denominator_parse
#print axioms geometryRow046_jensenBound_denominator_nonzero
#print axioms geometryRow046_jensenBound_parse
#print axioms geometryRow046_jensenBound_read
#print axioms geometryRow046_factorMaxima_read
#print axioms geometryRow046_gapWeightedMeans_read
#print axioms geometryRow046_floor_text_read
#print axioms geometryRow046_floor_chars_parse
#print axioms geometryRow046_floor_parse
#print axioms decode_geometry_Rows_046
#print axioms geometry_Rows_block_023_push_eq
#print axioms geometry_Rows_block_023_reverse
#print axioms decode_geometry_Rows_block_023
#print axioms decode_geometry_Rows_through_block_023

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
