import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows036

/-! Original simplices typed block 37, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson073 : SourceJson :=
  (SimplicesBlock037.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped073 : GeometryRow :=
  { simplexId := 73,
    vertexIds := #[39, 35, 33, 24, 23, 21, 20, 19, 15],
    physicalVolume := ((67696053511322749019496141552203604264529 : ℚ) / (86393732324124524544000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((91924997 : ℚ) / (407826000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((33215802327937160513683 : ℚ) / (498609070892742600000000 : ℚ)), ((16683922896939305837639 : ℚ) / (249304535446371300000000 : ℚ)), ((111095842260709860691363 : ℚ) / (747913606339113900000000 : ℚ)), ((5879132298045267902913 : ℚ) / (55401007876971400000000 : ℚ)), ((83632860001403055609979 : ℚ) / (1495827212678227800000000 : ℚ)), ((34426541323809894502451 : ℚ) / (747913606339113900000000 : ℚ)), ((1740311692753200645247 : ℚ) / (39363874017848100000000 : ℚ)), ((4083320071364337888761 : ℚ) / (93489200792389237500000 : ℚ)), ((645390533314347921077 : ℚ) / (14958272126782278000000 : ℚ)), ((12874072984854310285849 : ℚ) / (299165442535645560000000 : ℚ))],
    jensenBound := ((29157097633769296583730157338059563363899505695348108795340686422315805115282543683097824100898183871895192033781867996088972493995863502756628691429669769720459075866402152718630218505859375000000000 : ℚ) / (26761061629781146723977526131205625381497932520069336704657312312915973721253009560612018845852264663418184810401241669643111608579161942840002800001880081736380588167583783534335355064366090339785988910994114556079 : ℚ)),
    jensenFloorQ96 := (86321809714820 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_simplexId_before"
  err.flush

theorem geometryRow073_simplexId_read :
    geometryRowsJson073.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped073.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_vertexIds_before"
  err.flush

theorem geometryRow073_vertexIds_read :
    geometryRowsJson073.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped073.vertexIds := by decide +kernel

noncomputable def geometryRow073_physicalVolumeNumeratorChars : List Char := ['6', '7', '6', '9', '6', '0', '5', '3', '5', '1', '1', '3', '2', '2', '7', '4', '9', '0', '1', '9', '4', '9', '6', '1', '4', '1', '5', '5', '2', '2', '0', '3', '6', '0', '4', '2', '6', '4', '5', '2', '9']
noncomputable def geometryRow073_physicalVolumeDenominatorChars : List Char := ['8', '6', '3', '9', '3', '7', '3', '2', '3', '2', '4', '1', '2', '4', '5', '2', '4', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow073_physicalVolumeText : String := String.ofList (geometryRow073_physicalVolumeNumeratorChars ++ '/' :: geometryRow073_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_physicalVolume_before_field"
  err.flush

theorem geometryRow073_physicalVolume_field :
    geometryRowsJson073.getObjVal? "physical_volume" = .ok (.str geometryRow073_physicalVolumeText) := by rfl

theorem geometryRow073_physicalVolume_numerator_no_slash :
    geometryRow073_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow073_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow073_physicalVolumeNumeratorChars = some (67696053511322749019496141552203604264529 : Int) := by decide +kernel

theorem geometryRow073_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow073_physicalVolumeDenominatorChars = some (86393732324124524544000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow073_physicalVolume_denominator_nonzero : (86393732324124524544000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow073_physicalVolume_parse :
    parseRational geometryRow073_physicalVolumeText = .ok geometryRowsTyped073.physicalVolume :=
  original_rational_fraction_of_chars geometryRow073_physicalVolumeNumeratorChars geometryRow073_physicalVolumeDenominatorChars
    (67696053511322749019496141552203604264529 : Int) (86393732324124524544000000000000000000000000000000000000000000000 : Int)
    geometryRow073_physicalVolume_numerator_no_slash geometryRow073_physicalVolume_numerator_parse
    geometryRow073_physicalVolume_denominator_parse geometryRow073_physicalVolume_denominator_nonzero

theorem geometryRow073_physicalVolume_read :
    rationalField geometryRowsJson073 "physical_volume" = .ok geometryRowsTyped073.physicalVolume :=
  original_rationalField_of_string geometryRowsJson073 "physical_volume" geometryRow073_physicalVolumeText
    geometryRowsTyped073.physicalVolume geometryRow073_physicalVolume_field geometryRow073_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_physicalVolume_complete"
  err.flush

noncomputable def geometryRow073_meanGapNumeratorChars : List Char := ['9', '1', '9', '2', '4', '9', '9', '7']
noncomputable def geometryRow073_meanGapDenominatorChars : List Char := ['4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow073_meanGapText : String := String.ofList (geometryRow073_meanGapNumeratorChars ++ '/' :: geometryRow073_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_meanGap_before_field"
  err.flush

theorem geometryRow073_meanGap_field :
    geometryRowsJson073.getObjVal? "mean_gap" = .ok (.str geometryRow073_meanGapText) := by rfl

theorem geometryRow073_meanGap_numerator_no_slash :
    geometryRow073_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow073_meanGap_numerator_parse :
    SourceJson.intChars geometryRow073_meanGapNumeratorChars = some (91924997 : Int) := by decide +kernel

theorem geometryRow073_meanGap_denominator_parse :
    SourceJson.intChars geometryRow073_meanGapDenominatorChars = some (407826000000 : Int) := by decide +kernel

theorem geometryRow073_meanGap_denominator_nonzero : (407826000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow073_meanGap_parse :
    parseRational geometryRow073_meanGapText = .ok geometryRowsTyped073.meanGap :=
  original_rational_fraction_of_chars geometryRow073_meanGapNumeratorChars geometryRow073_meanGapDenominatorChars
    (91924997 : Int) (407826000000 : Int)
    geometryRow073_meanGap_numerator_no_slash geometryRow073_meanGap_numerator_parse
    geometryRow073_meanGap_denominator_parse geometryRow073_meanGap_denominator_nonzero

theorem geometryRow073_meanGap_read :
    rationalField geometryRowsJson073 "mean_gap" = .ok geometryRowsTyped073.meanGap :=
  original_rationalField_of_string geometryRowsJson073 "mean_gap" geometryRow073_meanGapText
    geometryRowsTyped073.meanGap geometryRow073_meanGap_field geometryRow073_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_meanGap_complete"
  err.flush

noncomputable def geometryRow073_jensenBoundNumeratorChars : List Char := ['2', '9', '1', '5', '7', '0', '9', '7', '6', '3', '3', '7', '6', '9', '2', '9', '6', '5', '8', '3', '7', '3', '0', '1', '5', '7', '3', '3', '8', '0', '5', '9', '5', '6', '3', '3', '6', '3', '8', '9', '9', '5', '0', '5', '6', '9', '5', '3', '4', '8', '1', '0', '8', '7', '9', '5', '3', '4', '0', '6', '8', '6', '4', '2', '2', '3', '1', '5', '8', '0', '5', '1', '1', '5', '2', '8', '2', '5', '4', '3', '6', '8', '3', '0', '9', '7', '8', '2', '4', '1', '0', '0', '8', '9', '8', '1', '8', '3', '8', '7', '1', '8', '9', '5', '1', '9', '2', '0', '3', '3', '7', '8', '1', '8', '6', '7', '9', '9', '6', '0', '8', '8', '9', '7', '2', '4', '9', '3', '9', '9', '5', '8', '6', '3', '5', '0', '2', '7', '5', '6', '6', '2', '8', '6', '9', '1', '4', '2', '9', '6', '6', '9', '7', '6', '9', '7', '2', '0', '4', '5', '9', '0', '7', '5', '8', '6', '6', '4', '0', '2', '1', '5', '2', '7', '1', '8', '6', '3', '0', '2', '1', '8', '5', '0', '5', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow073_jensenBoundDenominatorChars : List Char := ['2', '6', '7', '6', '1', '0', '6', '1', '6', '2', '9', '7', '8', '1', '1', '4', '6', '7', '2', '3', '9', '7', '7', '5', '2', '6', '1', '3', '1', '2', '0', '5', '6', '2', '5', '3', '8', '1', '4', '9', '7', '9', '3', '2', '5', '2', '0', '0', '6', '9', '3', '3', '6', '7', '0', '4', '6', '5', '7', '3', '1', '2', '3', '1', '2', '9', '1', '5', '9', '7', '3', '7', '2', '1', '2', '5', '3', '0', '0', '9', '5', '6', '0', '6', '1', '2', '0', '1', '8', '8', '4', '5', '8', '5', '2', '2', '6', '4', '6', '6', '3', '4', '1', '8', '1', '8', '4', '8', '1', '0', '4', '0', '1', '2', '4', '1', '6', '6', '9', '6', '4', '3', '1', '1', '1', '6', '0', '8', '5', '7', '9', '1', '6', '1', '9', '4', '2', '8', '4', '0', '0', '0', '2', '8', '0', '0', '0', '0', '1', '8', '8', '0', '0', '8', '1', '7', '3', '6', '3', '8', '0', '5', '8', '8', '1', '6', '7', '5', '8', '3', '7', '8', '3', '5', '3', '4', '3', '3', '5', '3', '5', '5', '0', '6', '4', '3', '6', '6', '0', '9', '0', '3', '3', '9', '7', '8', '5', '9', '8', '8', '9', '1', '0', '9', '9', '4', '1', '1', '4', '5', '5', '6', '0', '7', '9']
noncomputable def geometryRow073_jensenBoundText : String := String.ofList (geometryRow073_jensenBoundNumeratorChars ++ '/' :: geometryRow073_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_jensenBound_before_field"
  err.flush

theorem geometryRow073_jensenBound_field :
    geometryRowsJson073.getObjVal? "jensen_bound" = .ok (.str geometryRow073_jensenBoundText) := by rfl

theorem geometryRow073_jensenBound_numerator_no_slash :
    geometryRow073_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow073_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow073_jensenBoundNumeratorChars = some (29157097633769296583730157338059563363899505695348108795340686422315805115282543683097824100898183871895192033781867996088972493995863502756628691429669769720459075866402152718630218505859375000000000 : Int) := by decide +kernel

theorem geometryRow073_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow073_jensenBoundDenominatorChars = some (26761061629781146723977526131205625381497932520069336704657312312915973721253009560612018845852264663418184810401241669643111608579161942840002800001880081736380588167583783534335355064366090339785988910994114556079 : Int) := by decide +kernel

theorem geometryRow073_jensenBound_denominator_nonzero : (26761061629781146723977526131205625381497932520069336704657312312915973721253009560612018845852264663418184810401241669643111608579161942840002800001880081736380588167583783534335355064366090339785988910994114556079 : Int) ≠ 0 := by decide +kernel

theorem geometryRow073_jensenBound_parse :
    parseRational geometryRow073_jensenBoundText = .ok geometryRowsTyped073.jensenBound :=
  original_rational_fraction_of_chars geometryRow073_jensenBoundNumeratorChars geometryRow073_jensenBoundDenominatorChars
    (29157097633769296583730157338059563363899505695348108795340686422315805115282543683097824100898183871895192033781867996088972493995863502756628691429669769720459075866402152718630218505859375000000000 : Int) (26761061629781146723977526131205625381497932520069336704657312312915973721253009560612018845852264663418184810401241669643111608579161942840002800001880081736380588167583783534335355064366090339785988910994114556079 : Int)
    geometryRow073_jensenBound_numerator_no_slash geometryRow073_jensenBound_numerator_parse
    geometryRow073_jensenBound_denominator_parse geometryRow073_jensenBound_denominator_nonzero

theorem geometryRow073_jensenBound_read :
    rationalField geometryRowsJson073 "jensen_bound" = .ok geometryRowsTyped073.jensenBound :=
  original_rationalField_of_string geometryRowsJson073 "jensen_bound" geometryRow073_jensenBoundText
    geometryRowsTyped073.jensenBound geometryRow073_jensenBound_field geometryRow073_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_factorMaxima_before"
  err.flush

theorem geometryRow073_factorMaxima_read :
    rationalArrayField geometryRowsJson073 "factor_maxima" = .ok geometryRowsTyped073.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_gapWeightedMeans_before"
  err.flush

theorem geometryRow073_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson073 "gap_weighted_means" = .ok geometryRowsTyped073.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow073_floorChars : List Char := ['8', '6', '3', '2', '1', '8', '0', '9', '7', '1', '4', '8', '2', '0']
noncomputable def geometryRow073_floorText : String := String.ofList geometryRow073_floorChars

theorem geometryRow073_floor_text_read :
    geometryRowsJson073.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow073_floorText := by rfl

theorem geometryRow073_floor_chars_parse :
    SourceJson.intChars geometryRow073_floorChars = some (86321809714820 : Int) := by decide +kernel

theorem geometryRow073_floor_parse :
    parseInteger geometryRow073_floorText = .ok geometryRowsTyped073.jensenFloorQ96 := by
  simp only [geometryRow073_floorText, parseInteger, String.toList_ofList, geometryRow073_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_073 :
    decodeGeometryRow geometryRowsJson073 = .ok geometryRowsTyped073 :=
  original_geometryRow_of_fields geometryRowsJson073 geometryRowsTyped073 geometryRow073_floorText
    geometryRow073_simplexId_read geometryRow073_vertexIds_read
    geometryRow073_physicalVolume_read geometryRow073_meanGap_read
    geometryRow073_factorMaxima_read geometryRow073_gapWeightedMeans_read
    geometryRow073_jensenBound_read geometryRow073_floor_text_read geometryRow073_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_073_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson074 : SourceJson :=
  (SimplicesBlock037.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped074 : GeometryRow :=
  { simplexId := 74,
    vertexIds := #[39, 35, 33, 24, 23, 21, 19, 18, 15],
    physicalVolume := ((932269585406358361005025935284839960667471 : ℚ) / (253779427012608000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((52302041184263 : ℚ) / (782000100000000 : ℚ)), ((13118324731217 : ℚ) / (195500025000000 : ℚ)), ((5443085566909 : ℚ) / (36656254687500 : ℚ)), ((18453513890901 : ℚ) / (173777800000000 : ℚ)), ((262646656917433 : ℚ) / (4692000600000000 : ℚ)), ((53997926084401 : ℚ) / (1173000150000000 : ℚ)), ((1362901898761 : ℚ) / (30868425000000 : ℚ)), ((102327856287751 : ℚ) / (2346000300000000 : ℚ)), ((8103673475441 : ℚ) / (187680024000000 : ℚ)), ((40106910879697 : ℚ) / (938400120000000 : ℚ))],
    jensenBound := ((3558180350442591636329750769033456596416628942356301439710552394192495438764331319064408860254369602966308593750000 : ℚ) / (1289855380355484047036508343007128582056348632261888601270447526602133769808872924276678573882465770526427741448090967469118240787 : ℚ)),
    jensenFloorQ96 := (218557906067138 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_simplexId_before"
  err.flush

theorem geometryRow074_simplexId_read :
    geometryRowsJson074.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped074.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_vertexIds_before"
  err.flush

theorem geometryRow074_vertexIds_read :
    geometryRowsJson074.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped074.vertexIds := by decide +kernel

noncomputable def geometryRow074_physicalVolumeNumeratorChars : List Char := ['9', '3', '2', '2', '6', '9', '5', '8', '5', '4', '0', '6', '3', '5', '8', '3', '6', '1', '0', '0', '5', '0', '2', '5', '9', '3', '5', '2', '8', '4', '8', '3', '9', '9', '6', '0', '6', '6', '7', '4', '7', '1']
noncomputable def geometryRow074_physicalVolumeDenominatorChars : List Char := ['2', '5', '3', '7', '7', '9', '4', '2', '7', '0', '1', '2', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow074_physicalVolumeText : String := String.ofList (geometryRow074_physicalVolumeNumeratorChars ++ '/' :: geometryRow074_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_physicalVolume_before_field"
  err.flush

theorem geometryRow074_physicalVolume_field :
    geometryRowsJson074.getObjVal? "physical_volume" = .ok (.str geometryRow074_physicalVolumeText) := by rfl

theorem geometryRow074_physicalVolume_numerator_no_slash :
    geometryRow074_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow074_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow074_physicalVolumeNumeratorChars = some (932269585406358361005025935284839960667471 : Int) := by decide +kernel

theorem geometryRow074_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow074_physicalVolumeDenominatorChars = some (253779427012608000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow074_physicalVolume_denominator_nonzero : (253779427012608000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow074_physicalVolume_parse :
    parseRational geometryRow074_physicalVolumeText = .ok geometryRowsTyped074.physicalVolume :=
  original_rational_fraction_of_chars geometryRow074_physicalVolumeNumeratorChars geometryRow074_physicalVolumeDenominatorChars
    (932269585406358361005025935284839960667471 : Int) (253779427012608000000000000000000000000000000000000000000000000000 : Int)
    geometryRow074_physicalVolume_numerator_no_slash geometryRow074_physicalVolume_numerator_parse
    geometryRow074_physicalVolume_denominator_parse geometryRow074_physicalVolume_denominator_nonzero

theorem geometryRow074_physicalVolume_read :
    rationalField geometryRowsJson074 "physical_volume" = .ok geometryRowsTyped074.physicalVolume :=
  original_rationalField_of_string geometryRowsJson074 "physical_volume" geometryRow074_physicalVolumeText
    geometryRowsTyped074.physicalVolume geometryRow074_physicalVolume_field geometryRow074_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_physicalVolume_complete"
  err.flush

noncomputable def geometryRow074_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow074_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow074_meanGapText : String := String.ofList (geometryRow074_meanGapNumeratorChars ++ '/' :: geometryRow074_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_meanGap_before_field"
  err.flush

theorem geometryRow074_meanGap_field :
    geometryRowsJson074.getObjVal? "mean_gap" = .ok (.str geometryRow074_meanGapText) := by rfl

theorem geometryRow074_meanGap_numerator_no_slash :
    geometryRow074_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow074_meanGap_numerator_parse :
    SourceJson.intChars geometryRow074_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow074_meanGap_denominator_parse :
    SourceJson.intChars geometryRow074_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow074_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow074_meanGap_parse :
    parseRational geometryRow074_meanGapText = .ok geometryRowsTyped074.meanGap :=
  original_rational_fraction_of_chars geometryRow074_meanGapNumeratorChars geometryRow074_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow074_meanGap_numerator_no_slash geometryRow074_meanGap_numerator_parse
    geometryRow074_meanGap_denominator_parse geometryRow074_meanGap_denominator_nonzero

theorem geometryRow074_meanGap_read :
    rationalField geometryRowsJson074 "mean_gap" = .ok geometryRowsTyped074.meanGap :=
  original_rationalField_of_string geometryRowsJson074 "mean_gap" geometryRow074_meanGapText
    geometryRowsTyped074.meanGap geometryRow074_meanGap_field geometryRow074_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_meanGap_complete"
  err.flush

noncomputable def geometryRow074_jensenBoundNumeratorChars : List Char := ['3', '5', '5', '8', '1', '8', '0', '3', '5', '0', '4', '4', '2', '5', '9', '1', '6', '3', '6', '3', '2', '9', '7', '5', '0', '7', '6', '9', '0', '3', '3', '4', '5', '6', '5', '9', '6', '4', '1', '6', '6', '2', '8', '9', '4', '2', '3', '5', '6', '3', '0', '1', '4', '3', '9', '7', '1', '0', '5', '5', '2', '3', '9', '4', '1', '9', '2', '4', '9', '5', '4', '3', '8', '7', '6', '4', '3', '3', '1', '3', '1', '9', '0', '6', '4', '4', '0', '8', '8', '6', '0', '2', '5', '4', '3', '6', '9', '6', '0', '2', '9', '6', '6', '3', '0', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0']
noncomputable def geometryRow074_jensenBoundDenominatorChars : List Char := ['1', '2', '8', '9', '8', '5', '5', '3', '8', '0', '3', '5', '5', '4', '8', '4', '0', '4', '7', '0', '3', '6', '5', '0', '8', '3', '4', '3', '0', '0', '7', '1', '2', '8', '5', '8', '2', '0', '5', '6', '3', '4', '8', '6', '3', '2', '2', '6', '1', '8', '8', '8', '6', '0', '1', '2', '7', '0', '4', '4', '7', '5', '2', '6', '6', '0', '2', '1', '3', '3', '7', '6', '9', '8', '0', '8', '8', '7', '2', '9', '2', '4', '2', '7', '6', '6', '7', '8', '5', '7', '3', '8', '8', '2', '4', '6', '5', '7', '7', '0', '5', '2', '6', '4', '2', '7', '7', '4', '1', '4', '4', '8', '0', '9', '0', '9', '6', '7', '4', '6', '9', '1', '1', '8', '2', '4', '0', '7', '8', '7']
noncomputable def geometryRow074_jensenBoundText : String := String.ofList (geometryRow074_jensenBoundNumeratorChars ++ '/' :: geometryRow074_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_jensenBound_before_field"
  err.flush

theorem geometryRow074_jensenBound_field :
    geometryRowsJson074.getObjVal? "jensen_bound" = .ok (.str geometryRow074_jensenBoundText) := by rfl

theorem geometryRow074_jensenBound_numerator_no_slash :
    geometryRow074_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow074_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow074_jensenBoundNumeratorChars = some (3558180350442591636329750769033456596416628942356301439710552394192495438764331319064408860254369602966308593750000 : Int) := by decide +kernel

theorem geometryRow074_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow074_jensenBoundDenominatorChars = some (1289855380355484047036508343007128582056348632261888601270447526602133769808872924276678573882465770526427741448090967469118240787 : Int) := by decide +kernel

theorem geometryRow074_jensenBound_denominator_nonzero : (1289855380355484047036508343007128582056348632261888601270447526602133769808872924276678573882465770526427741448090967469118240787 : Int) ≠ 0 := by decide +kernel

theorem geometryRow074_jensenBound_parse :
    parseRational geometryRow074_jensenBoundText = .ok geometryRowsTyped074.jensenBound :=
  original_rational_fraction_of_chars geometryRow074_jensenBoundNumeratorChars geometryRow074_jensenBoundDenominatorChars
    (3558180350442591636329750769033456596416628942356301439710552394192495438764331319064408860254369602966308593750000 : Int) (1289855380355484047036508343007128582056348632261888601270447526602133769808872924276678573882465770526427741448090967469118240787 : Int)
    geometryRow074_jensenBound_numerator_no_slash geometryRow074_jensenBound_numerator_parse
    geometryRow074_jensenBound_denominator_parse geometryRow074_jensenBound_denominator_nonzero

theorem geometryRow074_jensenBound_read :
    rationalField geometryRowsJson074 "jensen_bound" = .ok geometryRowsTyped074.jensenBound :=
  original_rationalField_of_string geometryRowsJson074 "jensen_bound" geometryRow074_jensenBoundText
    geometryRowsTyped074.jensenBound geometryRow074_jensenBound_field geometryRow074_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_factorMaxima_before"
  err.flush

theorem geometryRow074_factorMaxima_read :
    rationalArrayField geometryRowsJson074 "factor_maxima" = .ok geometryRowsTyped074.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_gapWeightedMeans_before"
  err.flush

theorem geometryRow074_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson074 "gap_weighted_means" = .ok geometryRowsTyped074.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow074_floorChars : List Char := ['2', '1', '8', '5', '5', '7', '9', '0', '6', '0', '6', '7', '1', '3', '8']
noncomputable def geometryRow074_floorText : String := String.ofList geometryRow074_floorChars

theorem geometryRow074_floor_text_read :
    geometryRowsJson074.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow074_floorText := by rfl

theorem geometryRow074_floor_chars_parse :
    SourceJson.intChars geometryRow074_floorChars = some (218557906067138 : Int) := by decide +kernel

theorem geometryRow074_floor_parse :
    parseInteger geometryRow074_floorText = .ok geometryRowsTyped074.jensenFloorQ96 := by
  simp only [geometryRow074_floorText, parseInteger, String.toList_ofList, geometryRow074_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_074 :
    decodeGeometryRow geometryRowsJson074 = .ok geometryRowsTyped074 :=
  original_geometryRow_of_fields geometryRowsJson074 geometryRowsTyped074 geometryRow074_floorText
    geometryRow074_simplexId_read geometryRow074_vertexIds_read
    geometryRow074_physicalVolume_read geometryRow074_meanGap_read
    geometryRow074_factorMaxima_read geometryRow074_gapWeightedMeans_read
    geometryRow074_jensenBound_read geometryRow074_floor_text_read geometryRow074_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_074_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock037 : List SourceJson := [geometryRowsJson073, geometryRowsJson074]
noncomputable def geometryRowsTypedBlock037 : List (GeometryRow) := [geometryRowsTyped073, geometryRowsTyped074]
noncomputable def geometryRowsTypedThroughBlock037 : List (GeometryRow) := geometryRowsTypedThroughBlock036 ++ geometryRowsTypedBlock037

theorem geometry_Rows_block_037_push_eq (acc : List SourceJson) :
    SimplicesBlock037.blockPush acc = [geometryRowsJson074, geometryRowsJson073] ++ acc := by rfl

theorem geometry_Rows_block_037_reverse (acc : List SourceJson) :
    (SimplicesBlock037.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock037 := by
  rw [geometry_Rows_block_037_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_037 :
    geometryRowsJsonBlock037.mapM decodeGeometryRow = .ok geometryRowsTypedBlock037 := by
  simp only [geometryRowsJsonBlock037, geometryRowsTypedBlock037, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_073, decode_geometry_Rows_074]
  rfl

theorem decode_geometry_Rows_through_block_037 :
    SimplicesValue.arrayAcc038.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock037 := by
  change (SimplicesBlock037.blockPush SimplicesValue.arrayAcc037).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_037_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_036, decode_geometry_Rows_block_037]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_037_complete"
  err.flush

#print axioms geometryRow073_simplexId_read
#print axioms geometryRow073_vertexIds_read
#print axioms geometryRow073_physicalVolume_field
#print axioms geometryRow073_physicalVolume_numerator_no_slash
#print axioms geometryRow073_physicalVolume_numerator_parse
#print axioms geometryRow073_physicalVolume_denominator_parse
#print axioms geometryRow073_physicalVolume_denominator_nonzero
#print axioms geometryRow073_physicalVolume_parse
#print axioms geometryRow073_physicalVolume_read
#print axioms geometryRow073_meanGap_field
#print axioms geometryRow073_meanGap_numerator_no_slash
#print axioms geometryRow073_meanGap_numerator_parse
#print axioms geometryRow073_meanGap_denominator_parse
#print axioms geometryRow073_meanGap_denominator_nonzero
#print axioms geometryRow073_meanGap_parse
#print axioms geometryRow073_meanGap_read
#print axioms geometryRow073_jensenBound_field
#print axioms geometryRow073_jensenBound_numerator_no_slash
#print axioms geometryRow073_jensenBound_numerator_parse
#print axioms geometryRow073_jensenBound_denominator_parse
#print axioms geometryRow073_jensenBound_denominator_nonzero
#print axioms geometryRow073_jensenBound_parse
#print axioms geometryRow073_jensenBound_read
#print axioms geometryRow073_factorMaxima_read
#print axioms geometryRow073_gapWeightedMeans_read
#print axioms geometryRow073_floor_text_read
#print axioms geometryRow073_floor_chars_parse
#print axioms geometryRow073_floor_parse
#print axioms decode_geometry_Rows_073
#print axioms geometryRow074_simplexId_read
#print axioms geometryRow074_vertexIds_read
#print axioms geometryRow074_physicalVolume_field
#print axioms geometryRow074_physicalVolume_numerator_no_slash
#print axioms geometryRow074_physicalVolume_numerator_parse
#print axioms geometryRow074_physicalVolume_denominator_parse
#print axioms geometryRow074_physicalVolume_denominator_nonzero
#print axioms geometryRow074_physicalVolume_parse
#print axioms geometryRow074_physicalVolume_read
#print axioms geometryRow074_meanGap_field
#print axioms geometryRow074_meanGap_numerator_no_slash
#print axioms geometryRow074_meanGap_numerator_parse
#print axioms geometryRow074_meanGap_denominator_parse
#print axioms geometryRow074_meanGap_denominator_nonzero
#print axioms geometryRow074_meanGap_parse
#print axioms geometryRow074_meanGap_read
#print axioms geometryRow074_jensenBound_field
#print axioms geometryRow074_jensenBound_numerator_no_slash
#print axioms geometryRow074_jensenBound_numerator_parse
#print axioms geometryRow074_jensenBound_denominator_parse
#print axioms geometryRow074_jensenBound_denominator_nonzero
#print axioms geometryRow074_jensenBound_parse
#print axioms geometryRow074_jensenBound_read
#print axioms geometryRow074_factorMaxima_read
#print axioms geometryRow074_gapWeightedMeans_read
#print axioms geometryRow074_floor_text_read
#print axioms geometryRow074_floor_chars_parse
#print axioms geometryRow074_floor_parse
#print axioms decode_geometry_Rows_074
#print axioms geometry_Rows_block_037_push_eq
#print axioms geometry_Rows_block_037_reverse
#print axioms decode_geometry_Rows_block_037
#print axioms decode_geometry_Rows_through_block_037

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
