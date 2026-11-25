import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500

/-! Original GeometryRow 22: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson022 : SourceJson :=
  (simplicesChunk022Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped022 : GeometryRow :=
  { simplexId := 22,
    vertexIds := #[27, 25, 23, 21, 19, 18, 13, 3, 2],
    physicalVolume := ((1823822554926274007850061543297 : ℚ) / (82776887254687500000000000000000000000000000000000000 : ℚ)),
    meanGap := ((4997753873 : ℚ) / (4197024000000 : ℚ)),
    factorMaxima := #[((14640661 : ℚ) / (152000000 : ℚ)), ((3796851 : ℚ) / (38000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((8140597 : ℚ) / (114000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ))],
    gapWeightedMeans := #[((46365861074109440646043 : ℚ) / (524392323776848800000000 : ℚ)), ((11779156685650199180857 : ℚ) / (131098080944212200000000 : ℚ)), ((1315742703125676231533 : ℚ) / (10487846475536976000000 : ℚ)), ((246250467071880630913 : ℚ) / (2521116941234850000000 : ℚ)), ((5921427244378293793927 : ℚ) / (65549040472106100000000 : ℚ)), ((1749511784338158740509 : ℚ) / (26219616188842440000000 : ℚ)), ((8739761041362478380937 : ℚ) / (262196161888424400000000 : ℚ)), ((946812834856099334017 : ℚ) / (29132906876491600000000 : ℚ)), ((387103072612292704903 : ℚ) / (12485531518496400000000 : ℚ)), ((1339134843913575516593 : ℚ) / (43699360314737400000000 : ℚ))],
    jensenBound := ((47117886642487315507554551898097793007902789544665480447100422634423867748062933416275693214188132577818418470205180476608485973599156173066042914888202860693046258202836992000000000000000000000000000 : ℚ) / (271156773279128481158851565122601503587026993379790208209810490506153542364975288368214571584253770607952149163380563055620232020338302614605200054808123110880999296729888684229037514701748156185459277189805077663 : ℚ)),
    jensenFloorQ96 := (13767178061220172 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_simplexId_before"
  err.flush

theorem geometryRow022_simplexId_read :
    geometryRowsJson022.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped022.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_vertexIds_before"
  err.flush

theorem geometryRow022_vertexIds_read :
    geometryRowsJson022.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped022.vertexIds := by decide +kernel

noncomputable def geometryRow022_physicalVolumeNumeratorChars : List Char := ['1', '8', '2', '3', '8', '2', '2', '5', '5', '4', '9', '2', '6', '2', '7', '4', '0', '0', '7', '8', '5', '0', '0', '6', '1', '5', '4', '3', '2', '9', '7']
noncomputable def geometryRow022_physicalVolumeDenominatorChars : List Char := ['8', '2', '7', '7', '6', '8', '8', '7', '2', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_physicalVolumeText : String := String.ofList (geometryRow022_physicalVolumeNumeratorChars ++ '/' :: geometryRow022_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_physicalVolume_before_field"
  err.flush

theorem geometryRow022_physicalVolume_field :
    geometryRowsJson022.getObjVal? "physical_volume" = .ok (.str geometryRow022_physicalVolumeText) := by rfl

theorem geometryRow022_physicalVolume_numerator_no_slash :
    geometryRow022_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeNumeratorChars = some (1823822554926274007850061543297 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeDenominatorChars = some (82776887254687500000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_nonzero : (82776887254687500000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_physicalVolume_parse :
    parseRational geometryRow022_physicalVolumeText = .ok geometryRowsTyped022.physicalVolume :=
  original_rational_fraction_of_chars geometryRow022_physicalVolumeNumeratorChars geometryRow022_physicalVolumeDenominatorChars
    (1823822554926274007850061543297 : Int) (82776887254687500000000000000000000000000000000000000 : Int)
    geometryRow022_physicalVolume_numerator_no_slash geometryRow022_physicalVolume_numerator_parse
    geometryRow022_physicalVolume_denominator_parse geometryRow022_physicalVolume_denominator_nonzero

theorem geometryRow022_physicalVolume_read :
    rationalField geometryRowsJson022 "physical_volume" = .ok geometryRowsTyped022.physicalVolume :=
  original_rationalField_of_string geometryRowsJson022 "physical_volume" geometryRow022_physicalVolumeText
    geometryRowsTyped022.physicalVolume geometryRow022_physicalVolume_field geometryRow022_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_physicalVolume_complete"
  err.flush

noncomputable def geometryRow022_meanGapNumeratorChars : List Char := ['4', '9', '9', '7', '7', '5', '3', '8', '7', '3']
noncomputable def geometryRow022_meanGapDenominatorChars : List Char := ['4', '1', '9', '7', '0', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_meanGapText : String := String.ofList (geometryRow022_meanGapNumeratorChars ++ '/' :: geometryRow022_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_meanGap_before_field"
  err.flush

theorem geometryRow022_meanGap_field :
    geometryRowsJson022.getObjVal? "mean_gap" = .ok (.str geometryRow022_meanGapText) := by rfl

theorem geometryRow022_meanGap_numerator_no_slash :
    geometryRow022_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_meanGap_numerator_parse :
    SourceJson.intChars geometryRow022_meanGapNumeratorChars = some (4997753873 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_parse :
    SourceJson.intChars geometryRow022_meanGapDenominatorChars = some (4197024000000 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_nonzero : (4197024000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_meanGap_parse :
    parseRational geometryRow022_meanGapText = .ok geometryRowsTyped022.meanGap :=
  original_rational_fraction_of_chars geometryRow022_meanGapNumeratorChars geometryRow022_meanGapDenominatorChars
    (4997753873 : Int) (4197024000000 : Int)
    geometryRow022_meanGap_numerator_no_slash geometryRow022_meanGap_numerator_parse
    geometryRow022_meanGap_denominator_parse geometryRow022_meanGap_denominator_nonzero

theorem geometryRow022_meanGap_read :
    rationalField geometryRowsJson022 "mean_gap" = .ok geometryRowsTyped022.meanGap :=
  original_rationalField_of_string geometryRowsJson022 "mean_gap" geometryRow022_meanGapText
    geometryRowsTyped022.meanGap geometryRow022_meanGap_field geometryRow022_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_meanGap_complete"
  err.flush

noncomputable def geometryRow022_jensenBoundNumeratorChars : List Char := ['4', '7', '1', '1', '7', '8', '8', '6', '6', '4', '2', '4', '8', '7', '3', '1', '5', '5', '0', '7', '5', '5', '4', '5', '5', '1', '8', '9', '8', '0', '9', '7', '7', '9', '3', '0', '0', '7', '9', '0', '2', '7', '8', '9', '5', '4', '4', '6', '6', '5', '4', '8', '0', '4', '4', '7', '1', '0', '0', '4', '2', '2', '6', '3', '4', '4', '2', '3', '8', '6', '7', '7', '4', '8', '0', '6', '2', '9', '3', '3', '4', '1', '6', '2', '7', '5', '6', '9', '3', '2', '1', '4', '1', '8', '8', '1', '3', '2', '5', '7', '7', '8', '1', '8', '4', '1', '8', '4', '7', '0', '2', '0', '5', '1', '8', '0', '4', '7', '6', '6', '0', '8', '4', '8', '5', '9', '7', '3', '5', '9', '9', '1', '5', '6', '1', '7', '3', '0', '6', '6', '0', '4', '2', '9', '1', '4', '8', '8', '8', '2', '0', '2', '8', '6', '0', '6', '9', '3', '0', '4', '6', '2', '5', '8', '2', '0', '2', '8', '3', '6', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_jensenBoundDenominatorChars : List Char := ['2', '7', '1', '1', '5', '6', '7', '7', '3', '2', '7', '9', '1', '2', '8', '4', '8', '1', '1', '5', '8', '8', '5', '1', '5', '6', '5', '1', '2', '2', '6', '0', '1', '5', '0', '3', '5', '8', '7', '0', '2', '6', '9', '9', '3', '3', '7', '9', '7', '9', '0', '2', '0', '8', '2', '0', '9', '8', '1', '0', '4', '9', '0', '5', '0', '6', '1', '5', '3', '5', '4', '2', '3', '6', '4', '9', '7', '5', '2', '8', '8', '3', '6', '8', '2', '1', '4', '5', '7', '1', '5', '8', '4', '2', '5', '3', '7', '7', '0', '6', '0', '7', '9', '5', '2', '1', '4', '9', '1', '6', '3', '3', '8', '0', '5', '6', '3', '0', '5', '5', '6', '2', '0', '2', '3', '2', '0', '2', '0', '3', '3', '8', '3', '0', '2', '6', '1', '4', '6', '0', '5', '2', '0', '0', '0', '5', '4', '8', '0', '8', '1', '2', '3', '1', '1', '0', '8', '8', '0', '9', '9', '9', '2', '9', '6', '7', '2', '9', '8', '8', '8', '6', '8', '4', '2', '2', '9', '0', '3', '7', '5', '1', '4', '7', '0', '1', '7', '4', '8', '1', '5', '6', '1', '8', '5', '4', '5', '9', '2', '7', '7', '1', '8', '9', '8', '0', '5', '0', '7', '7', '6', '6', '3']
noncomputable def geometryRow022_jensenBoundText : String := String.ofList (geometryRow022_jensenBoundNumeratorChars ++ '/' :: geometryRow022_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_jensenBound_before_field"
  err.flush

theorem geometryRow022_jensenBound_field :
    geometryRowsJson022.getObjVal? "jensen_bound" = .ok (.str geometryRow022_jensenBoundText) := by rfl

theorem geometryRow022_jensenBound_numerator_no_slash :
    geometryRow022_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow022_jensenBoundNumeratorChars = some (47117886642487315507554551898097793007902789544665480447100422634423867748062933416275693214188132577818418470205180476608485973599156173066042914888202860693046258202836992000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow022_jensenBoundDenominatorChars = some (271156773279128481158851565122601503587026993379790208209810490506153542364975288368214571584253770607952149163380563055620232020338302614605200054808123110880999296729888684229037514701748156185459277189805077663 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_nonzero : (271156773279128481158851565122601503587026993379790208209810490506153542364975288368214571584253770607952149163380563055620232020338302614605200054808123110880999296729888684229037514701748156185459277189805077663 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_jensenBound_parse :
    parseRational geometryRow022_jensenBoundText = .ok geometryRowsTyped022.jensenBound :=
  original_rational_fraction_of_chars geometryRow022_jensenBoundNumeratorChars geometryRow022_jensenBoundDenominatorChars
    (47117886642487315507554551898097793007902789544665480447100422634423867748062933416275693214188132577818418470205180476608485973599156173066042914888202860693046258202836992000000000000000000000000000 : Int) (271156773279128481158851565122601503587026993379790208209810490506153542364975288368214571584253770607952149163380563055620232020338302614605200054808123110880999296729888684229037514701748156185459277189805077663 : Int)
    geometryRow022_jensenBound_numerator_no_slash geometryRow022_jensenBound_numerator_parse
    geometryRow022_jensenBound_denominator_parse geometryRow022_jensenBound_denominator_nonzero

theorem geometryRow022_jensenBound_read :
    rationalField geometryRowsJson022 "jensen_bound" = .ok geometryRowsTyped022.jensenBound :=
  original_rationalField_of_string geometryRowsJson022 "jensen_bound" geometryRow022_jensenBoundText
    geometryRowsTyped022.jensenBound geometryRow022_jensenBound_field geometryRow022_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_factorMaxima_before"
  err.flush

theorem geometryRow022_factorMaxima_read :
    rationalArrayField geometryRowsJson022 "factor_maxima" = .ok geometryRowsTyped022.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_gapWeightedMeans_before"
  err.flush

theorem geometryRow022_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson022 "gap_weighted_means" = .ok geometryRowsTyped022.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow022_floorChars : List Char := ['1', '3', '7', '6', '7', '1', '7', '8', '0', '6', '1', '2', '2', '0', '1', '7', '2']
noncomputable def geometryRow022_floorText : String := String.ofList geometryRow022_floorChars

theorem geometryRow022_floor_text_read :
    geometryRowsJson022.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow022_floorText := by rfl

theorem geometryRow022_floor_chars_parse :
    SourceJson.intChars geometryRow022_floorChars = some (13767178061220172 : Int) := by decide +kernel

theorem geometryRow022_floor_parse :
    parseInteger geometryRow022_floorText = .ok geometryRowsTyped022.jensenFloorQ96 := by
  simp only [geometryRow022_floorText, parseInteger, String.toList_ofList, geometryRow022_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_022 :
    decodeGeometryRow geometryRowsJson022 = .ok geometryRowsTyped022 :=
  original_geometryRow_of_fields geometryRowsJson022 geometryRowsTyped022 geometryRow022_floorText
    geometryRow022_simplexId_read geometryRow022_vertexIds_read
    geometryRow022_physicalVolume_read geometryRow022_meanGap_read
    geometryRow022_factorMaxima_read geometryRow022_gapWeightedMeans_read
    geometryRow022_jensenBound_read geometryRow022_floor_text_read geometryRow022_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_022_original_decoder_complete"
  err.flush

#print axioms geometryRow022_simplexId_read
#print axioms geometryRow022_vertexIds_read
#print axioms geometryRow022_physicalVolume_field
#print axioms geometryRow022_physicalVolume_numerator_no_slash
#print axioms geometryRow022_physicalVolume_numerator_parse
#print axioms geometryRow022_physicalVolume_denominator_parse
#print axioms geometryRow022_physicalVolume_denominator_nonzero
#print axioms geometryRow022_physicalVolume_parse
#print axioms geometryRow022_physicalVolume_read
#print axioms geometryRow022_meanGap_field
#print axioms geometryRow022_meanGap_numerator_no_slash
#print axioms geometryRow022_meanGap_numerator_parse
#print axioms geometryRow022_meanGap_denominator_parse
#print axioms geometryRow022_meanGap_denominator_nonzero
#print axioms geometryRow022_meanGap_parse
#print axioms geometryRow022_meanGap_read
#print axioms geometryRow022_jensenBound_field
#print axioms geometryRow022_jensenBound_numerator_no_slash
#print axioms geometryRow022_jensenBound_numerator_parse
#print axioms geometryRow022_jensenBound_denominator_parse
#print axioms geometryRow022_jensenBound_denominator_nonzero
#print axioms geometryRow022_jensenBound_parse
#print axioms geometryRow022_jensenBound_read
#print axioms geometryRow022_factorMaxima_read
#print axioms geometryRow022_gapWeightedMeans_read
#print axioms geometryRow022_floor_text_read
#print axioms geometryRow022_floor_chars_parse
#print axioms geometryRow022_floor_parse
#print axioms decode_geometry_Rows_022

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
