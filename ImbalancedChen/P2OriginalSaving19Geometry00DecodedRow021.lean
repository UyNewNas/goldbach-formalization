import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500

/-! Original GeometryRow 21: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson021 : SourceJson :=
  (simplicesChunk021Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped021 : GeometryRow :=
  { simplexId := 21,
    vertexIds := #[27, 25, 23, 21, 19, 18, 17, 12, 2],
    physicalVolume := ((44738900938220768073665063 : ℚ) / (8280784705352783203125000000000000000000000000000000 : ℚ)),
    meanGap := ((164915953 : ℚ) / (198432000000 : ℚ)),
    factorMaxima := #[((39234443 : ℚ) / (416000000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((7359347 : ℚ) / (104000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))],
    gapWeightedMeans := #[((17251485831814127017 : ℚ) / (197476048879200000000 : ℚ)), ((68254950998068327 : ℚ) / (771390815934375000 : ℚ)), ((2498099679158372899 : ℚ) / (19747604887920000000 : ℚ)), ((374296702733129983 : ℚ) / (3797616324600000000 : ℚ)), ((4544150699239260761 : ℚ) / (49369012219800000000 : ℚ)), ((93512175291793543 : ℚ) / (1410543206280000000 : ℚ)), ((460845781780341979 : ℚ) / (14105432062800000000 : ℚ)), ((149698004485648457 : ℚ) / (4701810687600000000 : ℚ)), ((339415167790287653 : ℚ) / (10970891604400000000 : ℚ)), ((7762404230392523 : ℚ) / (257130271978125000 : ℚ))],
    jensenBound := ((454080275468589779376685025695711768312620424225210389780916814445071250576397037451131631121343176218168564687337318727807580241920000000000000000000000000 : ℚ) / (14444829116811496840963797583960815223387674498842099211459263792355770355111731379364666294798924025704565390414279062629587514066042137041594122248184285724634938402116559 : ℚ)),
    jensenFloorQ96 := (2490576078707 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_simplexId_before"
  err.flush

theorem geometryRow021_simplexId_read :
    geometryRowsJson021.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped021.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_vertexIds_before"
  err.flush

theorem geometryRow021_vertexIds_read :
    geometryRowsJson021.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped021.vertexIds := by decide +kernel

noncomputable def geometryRow021_physicalVolumeNumeratorChars : List Char := ['4', '4', '7', '3', '8', '9', '0', '0', '9', '3', '8', '2', '2', '0', '7', '6', '8', '0', '7', '3', '6', '6', '5', '0', '6', '3']
noncomputable def geometryRow021_physicalVolumeDenominatorChars : List Char := ['8', '2', '8', '0', '7', '8', '4', '7', '0', '5', '3', '5', '2', '7', '8', '3', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_physicalVolumeText : String := String.ofList (geometryRow021_physicalVolumeNumeratorChars ++ '/' :: geometryRow021_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_physicalVolume_before_field"
  err.flush

theorem geometryRow021_physicalVolume_field :
    geometryRowsJson021.getObjVal? "physical_volume" = .ok (.str geometryRow021_physicalVolumeText) := by rfl

theorem geometryRow021_physicalVolume_numerator_no_slash :
    geometryRow021_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeNumeratorChars = some (44738900938220768073665063 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeDenominatorChars = some (8280784705352783203125000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_nonzero : (8280784705352783203125000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_physicalVolume_parse :
    parseRational geometryRow021_physicalVolumeText = .ok geometryRowsTyped021.physicalVolume :=
  original_rational_fraction_of_chars geometryRow021_physicalVolumeNumeratorChars geometryRow021_physicalVolumeDenominatorChars
    (44738900938220768073665063 : Int) (8280784705352783203125000000000000000000000000000000 : Int)
    geometryRow021_physicalVolume_numerator_no_slash geometryRow021_physicalVolume_numerator_parse
    geometryRow021_physicalVolume_denominator_parse geometryRow021_physicalVolume_denominator_nonzero

theorem geometryRow021_physicalVolume_read :
    rationalField geometryRowsJson021 "physical_volume" = .ok geometryRowsTyped021.physicalVolume :=
  original_rationalField_of_string geometryRowsJson021 "physical_volume" geometryRow021_physicalVolumeText
    geometryRowsTyped021.physicalVolume geometryRow021_physicalVolume_field geometryRow021_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_physicalVolume_complete"
  err.flush

noncomputable def geometryRow021_meanGapNumeratorChars : List Char := ['1', '6', '4', '9', '1', '5', '9', '5', '3']
noncomputable def geometryRow021_meanGapDenominatorChars : List Char := ['1', '9', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_meanGapText : String := String.ofList (geometryRow021_meanGapNumeratorChars ++ '/' :: geometryRow021_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_meanGap_before_field"
  err.flush

theorem geometryRow021_meanGap_field :
    geometryRowsJson021.getObjVal? "mean_gap" = .ok (.str geometryRow021_meanGapText) := by rfl

theorem geometryRow021_meanGap_numerator_no_slash :
    geometryRow021_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_meanGap_numerator_parse :
    SourceJson.intChars geometryRow021_meanGapNumeratorChars = some (164915953 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_parse :
    SourceJson.intChars geometryRow021_meanGapDenominatorChars = some (198432000000 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_nonzero : (198432000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_meanGap_parse :
    parseRational geometryRow021_meanGapText = .ok geometryRowsTyped021.meanGap :=
  original_rational_fraction_of_chars geometryRow021_meanGapNumeratorChars geometryRow021_meanGapDenominatorChars
    (164915953 : Int) (198432000000 : Int)
    geometryRow021_meanGap_numerator_no_slash geometryRow021_meanGap_numerator_parse
    geometryRow021_meanGap_denominator_parse geometryRow021_meanGap_denominator_nonzero

theorem geometryRow021_meanGap_read :
    rationalField geometryRowsJson021 "mean_gap" = .ok geometryRowsTyped021.meanGap :=
  original_rationalField_of_string geometryRowsJson021 "mean_gap" geometryRow021_meanGapText
    geometryRowsTyped021.meanGap geometryRow021_meanGap_field geometryRow021_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_meanGap_complete"
  err.flush

noncomputable def geometryRow021_jensenBoundNumeratorChars : List Char := ['4', '5', '4', '0', '8', '0', '2', '7', '5', '4', '6', '8', '5', '8', '9', '7', '7', '9', '3', '7', '6', '6', '8', '5', '0', '2', '5', '6', '9', '5', '7', '1', '1', '7', '6', '8', '3', '1', '2', '6', '2', '0', '4', '2', '4', '2', '2', '5', '2', '1', '0', '3', '8', '9', '7', '8', '0', '9', '1', '6', '8', '1', '4', '4', '4', '5', '0', '7', '1', '2', '5', '0', '5', '7', '6', '3', '9', '7', '0', '3', '7', '4', '5', '1', '1', '3', '1', '6', '3', '1', '1', '2', '1', '3', '4', '3', '1', '7', '6', '2', '1', '8', '1', '6', '8', '5', '6', '4', '6', '8', '7', '3', '3', '7', '3', '1', '8', '7', '2', '7', '8', '0', '7', '5', '8', '0', '2', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_jensenBoundDenominatorChars : List Char := ['1', '4', '4', '4', '4', '8', '2', '9', '1', '1', '6', '8', '1', '1', '4', '9', '6', '8', '4', '0', '9', '6', '3', '7', '9', '7', '5', '8', '3', '9', '6', '0', '8', '1', '5', '2', '2', '3', '3', '8', '7', '6', '7', '4', '4', '9', '8', '8', '4', '2', '0', '9', '9', '2', '1', '1', '4', '5', '9', '2', '6', '3', '7', '9', '2', '3', '5', '5', '7', '7', '0', '3', '5', '5', '1', '1', '1', '7', '3', '1', '3', '7', '9', '3', '6', '4', '6', '6', '6', '2', '9', '4', '7', '9', '8', '9', '2', '4', '0', '2', '5', '7', '0', '4', '5', '6', '5', '3', '9', '0', '4', '1', '4', '2', '7', '9', '0', '6', '2', '6', '2', '9', '5', '8', '7', '5', '1', '4', '0', '6', '6', '0', '4', '2', '1', '3', '7', '0', '4', '1', '5', '9', '4', '1', '2', '2', '2', '4', '8', '1', '8', '4', '2', '8', '5', '7', '2', '4', '6', '3', '4', '9', '3', '8', '4', '0', '2', '1', '1', '6', '5', '5', '9']
noncomputable def geometryRow021_jensenBoundText : String := String.ofList (geometryRow021_jensenBoundNumeratorChars ++ '/' :: geometryRow021_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_jensenBound_before_field"
  err.flush

theorem geometryRow021_jensenBound_field :
    geometryRowsJson021.getObjVal? "jensen_bound" = .ok (.str geometryRow021_jensenBoundText) := by rfl

theorem geometryRow021_jensenBound_numerator_no_slash :
    geometryRow021_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow021_jensenBoundNumeratorChars = some (454080275468589779376685025695711768312620424225210389780916814445071250576397037451131631121343176218168564687337318727807580241920000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow021_jensenBoundDenominatorChars = some (14444829116811496840963797583960815223387674498842099211459263792355770355111731379364666294798924025704565390414279062629587514066042137041594122248184285724634938402116559 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_nonzero : (14444829116811496840963797583960815223387674498842099211459263792355770355111731379364666294798924025704565390414279062629587514066042137041594122248184285724634938402116559 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_jensenBound_parse :
    parseRational geometryRow021_jensenBoundText = .ok geometryRowsTyped021.jensenBound :=
  original_rational_fraction_of_chars geometryRow021_jensenBoundNumeratorChars geometryRow021_jensenBoundDenominatorChars
    (454080275468589779376685025695711768312620424225210389780916814445071250576397037451131631121343176218168564687337318727807580241920000000000000000000000000 : Int) (14444829116811496840963797583960815223387674498842099211459263792355770355111731379364666294798924025704565390414279062629587514066042137041594122248184285724634938402116559 : Int)
    geometryRow021_jensenBound_numerator_no_slash geometryRow021_jensenBound_numerator_parse
    geometryRow021_jensenBound_denominator_parse geometryRow021_jensenBound_denominator_nonzero

theorem geometryRow021_jensenBound_read :
    rationalField geometryRowsJson021 "jensen_bound" = .ok geometryRowsTyped021.jensenBound :=
  original_rationalField_of_string geometryRowsJson021 "jensen_bound" geometryRow021_jensenBoundText
    geometryRowsTyped021.jensenBound geometryRow021_jensenBound_field geometryRow021_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_factorMaxima_before"
  err.flush

theorem geometryRow021_factorMaxima_read :
    rationalArrayField geometryRowsJson021 "factor_maxima" = .ok geometryRowsTyped021.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_gapWeightedMeans_before"
  err.flush

theorem geometryRow021_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson021 "gap_weighted_means" = .ok geometryRowsTyped021.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow021_floorChars : List Char := ['2', '4', '9', '0', '5', '7', '6', '0', '7', '8', '7', '0', '7']
noncomputable def geometryRow021_floorText : String := String.ofList geometryRow021_floorChars

theorem geometryRow021_floor_text_read :
    geometryRowsJson021.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow021_floorText := by rfl

theorem geometryRow021_floor_chars_parse :
    SourceJson.intChars geometryRow021_floorChars = some (2490576078707 : Int) := by decide +kernel

theorem geometryRow021_floor_parse :
    parseInteger geometryRow021_floorText = .ok geometryRowsTyped021.jensenFloorQ96 := by
  simp only [geometryRow021_floorText, parseInteger, String.toList_ofList, geometryRow021_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_021 :
    decodeGeometryRow geometryRowsJson021 = .ok geometryRowsTyped021 :=
  original_geometryRow_of_fields geometryRowsJson021 geometryRowsTyped021 geometryRow021_floorText
    geometryRow021_simplexId_read geometryRow021_vertexIds_read
    geometryRow021_physicalVolume_read geometryRow021_meanGap_read
    geometryRow021_factorMaxima_read geometryRow021_gapWeightedMeans_read
    geometryRow021_jensenBound_read geometryRow021_floor_text_read geometryRow021_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_021_original_decoder_complete"
  err.flush

#print axioms geometryRow021_simplexId_read
#print axioms geometryRow021_vertexIds_read
#print axioms geometryRow021_physicalVolume_field
#print axioms geometryRow021_physicalVolume_numerator_no_slash
#print axioms geometryRow021_physicalVolume_numerator_parse
#print axioms geometryRow021_physicalVolume_denominator_parse
#print axioms geometryRow021_physicalVolume_denominator_nonzero
#print axioms geometryRow021_physicalVolume_parse
#print axioms geometryRow021_physicalVolume_read
#print axioms geometryRow021_meanGap_field
#print axioms geometryRow021_meanGap_numerator_no_slash
#print axioms geometryRow021_meanGap_numerator_parse
#print axioms geometryRow021_meanGap_denominator_parse
#print axioms geometryRow021_meanGap_denominator_nonzero
#print axioms geometryRow021_meanGap_parse
#print axioms geometryRow021_meanGap_read
#print axioms geometryRow021_jensenBound_field
#print axioms geometryRow021_jensenBound_numerator_no_slash
#print axioms geometryRow021_jensenBound_numerator_parse
#print axioms geometryRow021_jensenBound_denominator_parse
#print axioms geometryRow021_jensenBound_denominator_nonzero
#print axioms geometryRow021_jensenBound_parse
#print axioms geometryRow021_jensenBound_read
#print axioms geometryRow021_factorMaxima_read
#print axioms geometryRow021_gapWeightedMeans_read
#print axioms geometryRow021_floor_text_read
#print axioms geometryRow021_floor_chars_parse
#print axioms geometryRow021_floor_parse
#print axioms decode_geometry_Rows_021

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
