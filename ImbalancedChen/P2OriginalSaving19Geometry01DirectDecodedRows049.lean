import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows048

/-! Original simplices typed block 49, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson096 : SourceJson :=
  (SimplicesBlock049.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped096 : GeometryRow :=
  { simplexId := 96,
    vertexIds := #[39, 37, 24, 23, 21, 19, 18, 6, 0],
    physicalVolume := ((44743110171787620326372376199379188298205103 : ℚ) / (532936796726476800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((329471517469 : ℚ) / (4170667200000 : ℚ)), ((8259622302139 : ℚ) / (104266680000000 : ℚ)), ((76370239667767 : ℚ) / (521333400000000 : ℚ)), ((83823810279817 : ℚ) / (782000100000000 : ℚ)), ((6814838423203 : ℚ) / (130333350000000 : ℚ)), ((24657661710971 : ℚ) / (521333400000000 : ℚ)), ((4335256559 : ℚ) / (102894750000 : ℚ)), ((6506077435141 : ℚ) / (156400020000000 : ℚ)), ((64372815788251 : ℚ) / (1564000200000000 : ℚ)), ((62151257406487 : ℚ) / (1564000200000000 : ℚ))],
    jensenBound := ((523633957356868687605153624987463864696740875812003582385299615872367332206187972976577603350458131250000000000000 : ℚ) / (8928156681904075701308450955770487796771214430254898933526454764145985642213798973657276641547794847995350802825557189225575603 : ℚ)),
    jensenFloorQ96 := (4646710149648680 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_simplexId_before"
  err.flush

theorem geometryRow096_simplexId_read :
    geometryRowsJson096.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped096.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_vertexIds_before"
  err.flush

theorem geometryRow096_vertexIds_read :
    geometryRowsJson096.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped096.vertexIds := by decide +kernel

noncomputable def geometryRow096_physicalVolumeNumeratorChars : List Char := ['4', '4', '7', '4', '3', '1', '1', '0', '1', '7', '1', '7', '8', '7', '6', '2', '0', '3', '2', '6', '3', '7', '2', '3', '7', '6', '1', '9', '9', '3', '7', '9', '1', '8', '8', '2', '9', '8', '2', '0', '5', '1', '0', '3']
noncomputable def geometryRow096_physicalVolumeDenominatorChars : List Char := ['5', '3', '2', '9', '3', '6', '7', '9', '6', '7', '2', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow096_physicalVolumeText : String := String.ofList (geometryRow096_physicalVolumeNumeratorChars ++ '/' :: geometryRow096_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_physicalVolume_before_field"
  err.flush

theorem geometryRow096_physicalVolume_field :
    geometryRowsJson096.getObjVal? "physical_volume" = .ok (.str geometryRow096_physicalVolumeText) := by rfl

theorem geometryRow096_physicalVolume_numerator_no_slash :
    geometryRow096_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow096_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow096_physicalVolumeNumeratorChars = some (44743110171787620326372376199379188298205103 : Int) := by decide +kernel

theorem geometryRow096_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow096_physicalVolumeDenominatorChars = some (532936796726476800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow096_physicalVolume_denominator_nonzero : (532936796726476800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow096_physicalVolume_parse :
    parseRational geometryRow096_physicalVolumeText = .ok geometryRowsTyped096.physicalVolume :=
  original_rational_fraction_of_chars geometryRow096_physicalVolumeNumeratorChars geometryRow096_physicalVolumeDenominatorChars
    (44743110171787620326372376199379188298205103 : Int) (532936796726476800000000000000000000000000000000000000000000000000 : Int)
    geometryRow096_physicalVolume_numerator_no_slash geometryRow096_physicalVolume_numerator_parse
    geometryRow096_physicalVolume_denominator_parse geometryRow096_physicalVolume_denominator_nonzero

theorem geometryRow096_physicalVolume_read :
    rationalField geometryRowsJson096 "physical_volume" = .ok geometryRowsTyped096.physicalVolume :=
  original_rationalField_of_string geometryRowsJson096 "physical_volume" geometryRow096_physicalVolumeText
    geometryRowsTyped096.physicalVolume geometryRow096_physicalVolume_field geometryRow096_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_physicalVolume_complete"
  err.flush

noncomputable def geometryRow096_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow096_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow096_meanGapText : String := String.ofList (geometryRow096_meanGapNumeratorChars ++ '/' :: geometryRow096_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_meanGap_before_field"
  err.flush

theorem geometryRow096_meanGap_field :
    geometryRowsJson096.getObjVal? "mean_gap" = .ok (.str geometryRow096_meanGapText) := by rfl

theorem geometryRow096_meanGap_numerator_no_slash :
    geometryRow096_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow096_meanGap_numerator_parse :
    SourceJson.intChars geometryRow096_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow096_meanGap_denominator_parse :
    SourceJson.intChars geometryRow096_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow096_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow096_meanGap_parse :
    parseRational geometryRow096_meanGapText = .ok geometryRowsTyped096.meanGap :=
  original_rational_fraction_of_chars geometryRow096_meanGapNumeratorChars geometryRow096_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow096_meanGap_numerator_no_slash geometryRow096_meanGap_numerator_parse
    geometryRow096_meanGap_denominator_parse geometryRow096_meanGap_denominator_nonzero

theorem geometryRow096_meanGap_read :
    rationalField geometryRowsJson096 "mean_gap" = .ok geometryRowsTyped096.meanGap :=
  original_rationalField_of_string geometryRowsJson096 "mean_gap" geometryRow096_meanGapText
    geometryRowsTyped096.meanGap geometryRow096_meanGap_field geometryRow096_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_meanGap_complete"
  err.flush

noncomputable def geometryRow096_jensenBoundNumeratorChars : List Char := ['5', '2', '3', '6', '3', '3', '9', '5', '7', '3', '5', '6', '8', '6', '8', '6', '8', '7', '6', '0', '5', '1', '5', '3', '6', '2', '4', '9', '8', '7', '4', '6', '3', '8', '6', '4', '6', '9', '6', '7', '4', '0', '8', '7', '5', '8', '1', '2', '0', '0', '3', '5', '8', '2', '3', '8', '5', '2', '9', '9', '6', '1', '5', '8', '7', '2', '3', '6', '7', '3', '3', '2', '2', '0', '6', '1', '8', '7', '9', '7', '2', '9', '7', '6', '5', '7', '7', '6', '0', '3', '3', '5', '0', '4', '5', '8', '1', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow096_jensenBoundDenominatorChars : List Char := ['8', '9', '2', '8', '1', '5', '6', '6', '8', '1', '9', '0', '4', '0', '7', '5', '7', '0', '1', '3', '0', '8', '4', '5', '0', '9', '5', '5', '7', '7', '0', '4', '8', '7', '7', '9', '6', '7', '7', '1', '2', '1', '4', '4', '3', '0', '2', '5', '4', '8', '9', '8', '9', '3', '3', '5', '2', '6', '4', '5', '4', '7', '6', '4', '1', '4', '5', '9', '8', '5', '6', '4', '2', '2', '1', '3', '7', '9', '8', '9', '7', '3', '6', '5', '7', '2', '7', '6', '6', '4', '1', '5', '4', '7', '7', '9', '4', '8', '4', '7', '9', '9', '5', '3', '5', '0', '8', '0', '2', '8', '2', '5', '5', '5', '7', '1', '8', '9', '2', '2', '5', '5', '7', '5', '6', '0', '3']
noncomputable def geometryRow096_jensenBoundText : String := String.ofList (geometryRow096_jensenBoundNumeratorChars ++ '/' :: geometryRow096_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_jensenBound_before_field"
  err.flush

theorem geometryRow096_jensenBound_field :
    geometryRowsJson096.getObjVal? "jensen_bound" = .ok (.str geometryRow096_jensenBoundText) := by rfl

theorem geometryRow096_jensenBound_numerator_no_slash :
    geometryRow096_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow096_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow096_jensenBoundNumeratorChars = some (523633957356868687605153624987463864696740875812003582385299615872367332206187972976577603350458131250000000000000 : Int) := by decide +kernel

theorem geometryRow096_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow096_jensenBoundDenominatorChars = some (8928156681904075701308450955770487796771214430254898933526454764145985642213798973657276641547794847995350802825557189225575603 : Int) := by decide +kernel

theorem geometryRow096_jensenBound_denominator_nonzero : (8928156681904075701308450955770487796771214430254898933526454764145985642213798973657276641547794847995350802825557189225575603 : Int) ≠ 0 := by decide +kernel

theorem geometryRow096_jensenBound_parse :
    parseRational geometryRow096_jensenBoundText = .ok geometryRowsTyped096.jensenBound :=
  original_rational_fraction_of_chars geometryRow096_jensenBoundNumeratorChars geometryRow096_jensenBoundDenominatorChars
    (523633957356868687605153624987463864696740875812003582385299615872367332206187972976577603350458131250000000000000 : Int) (8928156681904075701308450955770487796771214430254898933526454764145985642213798973657276641547794847995350802825557189225575603 : Int)
    geometryRow096_jensenBound_numerator_no_slash geometryRow096_jensenBound_numerator_parse
    geometryRow096_jensenBound_denominator_parse geometryRow096_jensenBound_denominator_nonzero

theorem geometryRow096_jensenBound_read :
    rationalField geometryRowsJson096 "jensen_bound" = .ok geometryRowsTyped096.jensenBound :=
  original_rationalField_of_string geometryRowsJson096 "jensen_bound" geometryRow096_jensenBoundText
    geometryRowsTyped096.jensenBound geometryRow096_jensenBound_field geometryRow096_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_factorMaxima_before"
  err.flush

theorem geometryRow096_factorMaxima_read :
    rationalArrayField geometryRowsJson096 "factor_maxima" = .ok geometryRowsTyped096.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_gapWeightedMeans_before"
  err.flush

theorem geometryRow096_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson096 "gap_weighted_means" = .ok geometryRowsTyped096.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow096_floorChars : List Char := ['4', '6', '4', '6', '7', '1', '0', '1', '4', '9', '6', '4', '8', '6', '8', '0']
noncomputable def geometryRow096_floorText : String := String.ofList geometryRow096_floorChars

theorem geometryRow096_floor_text_read :
    geometryRowsJson096.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow096_floorText := by rfl

theorem geometryRow096_floor_chars_parse :
    SourceJson.intChars geometryRow096_floorChars = some (4646710149648680 : Int) := by decide +kernel

theorem geometryRow096_floor_parse :
    parseInteger geometryRow096_floorText = .ok geometryRowsTyped096.jensenFloorQ96 := by
  simp only [geometryRow096_floorText, parseInteger, String.toList_ofList, geometryRow096_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_096 :
    decodeGeometryRow geometryRowsJson096 = .ok geometryRowsTyped096 :=
  original_geometryRow_of_fields geometryRowsJson096 geometryRowsTyped096 geometryRow096_floorText
    geometryRow096_simplexId_read geometryRow096_vertexIds_read
    geometryRow096_physicalVolume_read geometryRow096_meanGap_read
    geometryRow096_factorMaxima_read geometryRow096_gapWeightedMeans_read
    geometryRow096_jensenBound_read geometryRow096_floor_text_read geometryRow096_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_096_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson097 : SourceJson :=
  (SimplicesBlock049.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped097 : GeometryRow :=
  { simplexId := 97,
    vertexIds := #[39, 37, 24, 23, 21, 19, 18, 15, 0],
    physicalVolume := ((15643138181569473462561976424272870861875043 : ℚ) / (548163562347233280000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((120362904070387 : ℚ) / (1564000200000000 : ℚ)), ((120705419551597 : ℚ) / (1564000200000000 : ℚ)), ((689753173214099 : ℚ) / (4692000600000000 : ℚ)), ((165919848312977 : ℚ) / (1564000200000000 : ℚ)), ((120880659433337 : ℚ) / (2346000300000000 : ℚ)), ((222953483687857 : ℚ) / (4692000600000000 : ℚ)), ((2112469888177 : ℚ) / (49389480000000 : ℚ)), ((39635852668129 : ℚ) / (938400120000000 : ℚ)), ((6128605864099 : ℚ) / (146625018750000 : ℚ)), ((48514526290907 : ℚ) / (1173000150000000 : ℚ))],
    jensenBound := ((591188710857291660391940409603572174023451864721021051393495131321011884411242368220018272291497191522607421875000000000000 : ℚ) / (30150398452468797260458959992980089436865147573940935522153517301364738239625257692755885678886774179966888528868034322923478448926514601 : ℚ)),
    jensenFloorQ96 := (1553505016998030 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_simplexId_before"
  err.flush

theorem geometryRow097_simplexId_read :
    geometryRowsJson097.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped097.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_vertexIds_before"
  err.flush

theorem geometryRow097_vertexIds_read :
    geometryRowsJson097.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped097.vertexIds := by decide +kernel

noncomputable def geometryRow097_physicalVolumeNumeratorChars : List Char := ['1', '5', '6', '4', '3', '1', '3', '8', '1', '8', '1', '5', '6', '9', '4', '7', '3', '4', '6', '2', '5', '6', '1', '9', '7', '6', '4', '2', '4', '2', '7', '2', '8', '7', '0', '8', '6', '1', '8', '7', '5', '0', '4', '3']
noncomputable def geometryRow097_physicalVolumeDenominatorChars : List Char := ['5', '4', '8', '1', '6', '3', '5', '6', '2', '3', '4', '7', '2', '3', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow097_physicalVolumeText : String := String.ofList (geometryRow097_physicalVolumeNumeratorChars ++ '/' :: geometryRow097_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_physicalVolume_before_field"
  err.flush

theorem geometryRow097_physicalVolume_field :
    geometryRowsJson097.getObjVal? "physical_volume" = .ok (.str geometryRow097_physicalVolumeText) := by rfl

theorem geometryRow097_physicalVolume_numerator_no_slash :
    geometryRow097_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow097_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow097_physicalVolumeNumeratorChars = some (15643138181569473462561976424272870861875043 : Int) := by decide +kernel

theorem geometryRow097_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow097_physicalVolumeDenominatorChars = some (548163562347233280000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow097_physicalVolume_denominator_nonzero : (548163562347233280000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow097_physicalVolume_parse :
    parseRational geometryRow097_physicalVolumeText = .ok geometryRowsTyped097.physicalVolume :=
  original_rational_fraction_of_chars geometryRow097_physicalVolumeNumeratorChars geometryRow097_physicalVolumeDenominatorChars
    (15643138181569473462561976424272870861875043 : Int) (548163562347233280000000000000000000000000000000000000000000000000 : Int)
    geometryRow097_physicalVolume_numerator_no_slash geometryRow097_physicalVolume_numerator_parse
    geometryRow097_physicalVolume_denominator_parse geometryRow097_physicalVolume_denominator_nonzero

theorem geometryRow097_physicalVolume_read :
    rationalField geometryRowsJson097 "physical_volume" = .ok geometryRowsTyped097.physicalVolume :=
  original_rationalField_of_string geometryRowsJson097 "physical_volume" geometryRow097_physicalVolumeText
    geometryRowsTyped097.physicalVolume geometryRow097_physicalVolume_field geometryRow097_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_physicalVolume_complete"
  err.flush

noncomputable def geometryRow097_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow097_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow097_meanGapText : String := String.ofList (geometryRow097_meanGapNumeratorChars ++ '/' :: geometryRow097_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_meanGap_before_field"
  err.flush

theorem geometryRow097_meanGap_field :
    geometryRowsJson097.getObjVal? "mean_gap" = .ok (.str geometryRow097_meanGapText) := by rfl

theorem geometryRow097_meanGap_numerator_no_slash :
    geometryRow097_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow097_meanGap_numerator_parse :
    SourceJson.intChars geometryRow097_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow097_meanGap_denominator_parse :
    SourceJson.intChars geometryRow097_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow097_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow097_meanGap_parse :
    parseRational geometryRow097_meanGapText = .ok geometryRowsTyped097.meanGap :=
  original_rational_fraction_of_chars geometryRow097_meanGapNumeratorChars geometryRow097_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow097_meanGap_numerator_no_slash geometryRow097_meanGap_numerator_parse
    geometryRow097_meanGap_denominator_parse geometryRow097_meanGap_denominator_nonzero

theorem geometryRow097_meanGap_read :
    rationalField geometryRowsJson097 "mean_gap" = .ok geometryRowsTyped097.meanGap :=
  original_rationalField_of_string geometryRowsJson097 "mean_gap" geometryRow097_meanGapText
    geometryRowsTyped097.meanGap geometryRow097_meanGap_field geometryRow097_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_meanGap_complete"
  err.flush

noncomputable def geometryRow097_jensenBoundNumeratorChars : List Char := ['5', '9', '1', '1', '8', '8', '7', '1', '0', '8', '5', '7', '2', '9', '1', '6', '6', '0', '3', '9', '1', '9', '4', '0', '4', '0', '9', '6', '0', '3', '5', '7', '2', '1', '7', '4', '0', '2', '3', '4', '5', '1', '8', '6', '4', '7', '2', '1', '0', '2', '1', '0', '5', '1', '3', '9', '3', '4', '9', '5', '1', '3', '1', '3', '2', '1', '0', '1', '1', '8', '8', '4', '4', '1', '1', '2', '4', '2', '3', '6', '8', '2', '2', '0', '0', '1', '8', '2', '7', '2', '2', '9', '1', '4', '9', '7', '1', '9', '1', '5', '2', '2', '6', '0', '7', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow097_jensenBoundDenominatorChars : List Char := ['3', '0', '1', '5', '0', '3', '9', '8', '4', '5', '2', '4', '6', '8', '7', '9', '7', '2', '6', '0', '4', '5', '8', '9', '5', '9', '9', '9', '2', '9', '8', '0', '0', '8', '9', '4', '3', '6', '8', '6', '5', '1', '4', '7', '5', '7', '3', '9', '4', '0', '9', '3', '5', '5', '2', '2', '1', '5', '3', '5', '1', '7', '3', '0', '1', '3', '6', '4', '7', '3', '8', '2', '3', '9', '6', '2', '5', '2', '5', '7', '6', '9', '2', '7', '5', '5', '8', '8', '5', '6', '7', '8', '8', '8', '6', '7', '7', '4', '1', '7', '9', '9', '6', '6', '8', '8', '8', '5', '2', '8', '8', '6', '8', '0', '3', '4', '3', '2', '2', '9', '2', '3', '4', '7', '8', '4', '4', '8', '9', '2', '6', '5', '1', '4', '6', '0', '1']
noncomputable def geometryRow097_jensenBoundText : String := String.ofList (geometryRow097_jensenBoundNumeratorChars ++ '/' :: geometryRow097_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_jensenBound_before_field"
  err.flush

theorem geometryRow097_jensenBound_field :
    geometryRowsJson097.getObjVal? "jensen_bound" = .ok (.str geometryRow097_jensenBoundText) := by rfl

theorem geometryRow097_jensenBound_numerator_no_slash :
    geometryRow097_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow097_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow097_jensenBoundNumeratorChars = some (591188710857291660391940409603572174023451864721021051393495131321011884411242368220018272291497191522607421875000000000000 : Int) := by decide +kernel

theorem geometryRow097_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow097_jensenBoundDenominatorChars = some (30150398452468797260458959992980089436865147573940935522153517301364738239625257692755885678886774179966888528868034322923478448926514601 : Int) := by decide +kernel

theorem geometryRow097_jensenBound_denominator_nonzero : (30150398452468797260458959992980089436865147573940935522153517301364738239625257692755885678886774179966888528868034322923478448926514601 : Int) ≠ 0 := by decide +kernel

theorem geometryRow097_jensenBound_parse :
    parseRational geometryRow097_jensenBoundText = .ok geometryRowsTyped097.jensenBound :=
  original_rational_fraction_of_chars geometryRow097_jensenBoundNumeratorChars geometryRow097_jensenBoundDenominatorChars
    (591188710857291660391940409603572174023451864721021051393495131321011884411242368220018272291497191522607421875000000000000 : Int) (30150398452468797260458959992980089436865147573940935522153517301364738239625257692755885678886774179966888528868034322923478448926514601 : Int)
    geometryRow097_jensenBound_numerator_no_slash geometryRow097_jensenBound_numerator_parse
    geometryRow097_jensenBound_denominator_parse geometryRow097_jensenBound_denominator_nonzero

theorem geometryRow097_jensenBound_read :
    rationalField geometryRowsJson097 "jensen_bound" = .ok geometryRowsTyped097.jensenBound :=
  original_rationalField_of_string geometryRowsJson097 "jensen_bound" geometryRow097_jensenBoundText
    geometryRowsTyped097.jensenBound geometryRow097_jensenBound_field geometryRow097_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_factorMaxima_before"
  err.flush

theorem geometryRow097_factorMaxima_read :
    rationalArrayField geometryRowsJson097 "factor_maxima" = .ok geometryRowsTyped097.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_gapWeightedMeans_before"
  err.flush

theorem geometryRow097_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson097 "gap_weighted_means" = .ok geometryRowsTyped097.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow097_floorChars : List Char := ['1', '5', '5', '3', '5', '0', '5', '0', '1', '6', '9', '9', '8', '0', '3', '0']
noncomputable def geometryRow097_floorText : String := String.ofList geometryRow097_floorChars

theorem geometryRow097_floor_text_read :
    geometryRowsJson097.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow097_floorText := by rfl

theorem geometryRow097_floor_chars_parse :
    SourceJson.intChars geometryRow097_floorChars = some (1553505016998030 : Int) := by decide +kernel

theorem geometryRow097_floor_parse :
    parseInteger geometryRow097_floorText = .ok geometryRowsTyped097.jensenFloorQ96 := by
  simp only [geometryRow097_floorText, parseInteger, String.toList_ofList, geometryRow097_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_097 :
    decodeGeometryRow geometryRowsJson097 = .ok geometryRowsTyped097 :=
  original_geometryRow_of_fields geometryRowsJson097 geometryRowsTyped097 geometryRow097_floorText
    geometryRow097_simplexId_read geometryRow097_vertexIds_read
    geometryRow097_physicalVolume_read geometryRow097_meanGap_read
    geometryRow097_factorMaxima_read geometryRow097_gapWeightedMeans_read
    geometryRow097_jensenBound_read geometryRow097_floor_text_read geometryRow097_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_097_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock049 : List SourceJson := [geometryRowsJson096, geometryRowsJson097]
noncomputable def geometryRowsTypedBlock049 : List (GeometryRow) := [geometryRowsTyped096, geometryRowsTyped097]
noncomputable def geometryRowsTypedThroughBlock049 : List (GeometryRow) := geometryRowsTypedThroughBlock048 ++ geometryRowsTypedBlock049

theorem geometry_Rows_block_049_push_eq (acc : List SourceJson) :
    SimplicesBlock049.blockPush acc = [geometryRowsJson097, geometryRowsJson096] ++ acc := by rfl

theorem geometry_Rows_block_049_reverse (acc : List SourceJson) :
    (SimplicesBlock049.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock049 := by
  rw [geometry_Rows_block_049_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_049 :
    geometryRowsJsonBlock049.mapM decodeGeometryRow = .ok geometryRowsTypedBlock049 := by
  simp only [geometryRowsJsonBlock049, geometryRowsTypedBlock049, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_096, decode_geometry_Rows_097]
  rfl

theorem decode_geometry_Rows_through_block_049 :
    SimplicesValue.arrayAcc050.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock049 := by
  change (SimplicesBlock049.blockPush SimplicesValue.arrayAcc049).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_049_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_048, decode_geometry_Rows_block_049]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_049_complete"
  err.flush

#print axioms geometryRow096_simplexId_read
#print axioms geometryRow096_vertexIds_read
#print axioms geometryRow096_physicalVolume_field
#print axioms geometryRow096_physicalVolume_numerator_no_slash
#print axioms geometryRow096_physicalVolume_numerator_parse
#print axioms geometryRow096_physicalVolume_denominator_parse
#print axioms geometryRow096_physicalVolume_denominator_nonzero
#print axioms geometryRow096_physicalVolume_parse
#print axioms geometryRow096_physicalVolume_read
#print axioms geometryRow096_meanGap_field
#print axioms geometryRow096_meanGap_numerator_no_slash
#print axioms geometryRow096_meanGap_numerator_parse
#print axioms geometryRow096_meanGap_denominator_parse
#print axioms geometryRow096_meanGap_denominator_nonzero
#print axioms geometryRow096_meanGap_parse
#print axioms geometryRow096_meanGap_read
#print axioms geometryRow096_jensenBound_field
#print axioms geometryRow096_jensenBound_numerator_no_slash
#print axioms geometryRow096_jensenBound_numerator_parse
#print axioms geometryRow096_jensenBound_denominator_parse
#print axioms geometryRow096_jensenBound_denominator_nonzero
#print axioms geometryRow096_jensenBound_parse
#print axioms geometryRow096_jensenBound_read
#print axioms geometryRow096_factorMaxima_read
#print axioms geometryRow096_gapWeightedMeans_read
#print axioms geometryRow096_floor_text_read
#print axioms geometryRow096_floor_chars_parse
#print axioms geometryRow096_floor_parse
#print axioms decode_geometry_Rows_096
#print axioms geometryRow097_simplexId_read
#print axioms geometryRow097_vertexIds_read
#print axioms geometryRow097_physicalVolume_field
#print axioms geometryRow097_physicalVolume_numerator_no_slash
#print axioms geometryRow097_physicalVolume_numerator_parse
#print axioms geometryRow097_physicalVolume_denominator_parse
#print axioms geometryRow097_physicalVolume_denominator_nonzero
#print axioms geometryRow097_physicalVolume_parse
#print axioms geometryRow097_physicalVolume_read
#print axioms geometryRow097_meanGap_field
#print axioms geometryRow097_meanGap_numerator_no_slash
#print axioms geometryRow097_meanGap_numerator_parse
#print axioms geometryRow097_meanGap_denominator_parse
#print axioms geometryRow097_meanGap_denominator_nonzero
#print axioms geometryRow097_meanGap_parse
#print axioms geometryRow097_meanGap_read
#print axioms geometryRow097_jensenBound_field
#print axioms geometryRow097_jensenBound_numerator_no_slash
#print axioms geometryRow097_jensenBound_numerator_parse
#print axioms geometryRow097_jensenBound_denominator_parse
#print axioms geometryRow097_jensenBound_denominator_nonzero
#print axioms geometryRow097_jensenBound_parse
#print axioms geometryRow097_jensenBound_read
#print axioms geometryRow097_factorMaxima_read
#print axioms geometryRow097_gapWeightedMeans_read
#print axioms geometryRow097_floor_text_read
#print axioms geometryRow097_floor_chars_parse
#print axioms geometryRow097_floor_parse
#print axioms decode_geometry_Rows_097
#print axioms geometry_Rows_block_049_push_eq
#print axioms geometry_Rows_block_049_reverse
#print axioms decode_geometry_Rows_block_049
#print axioms decode_geometry_Rows_through_block_049

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
