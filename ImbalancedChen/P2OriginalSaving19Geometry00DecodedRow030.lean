import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700

/-! Original GeometryRow 30: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson030 : SourceJson :=
  (simplicesChunk030Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped030 : GeometryRow :=
  { simplexId := 30,
    vertexIds := #[27, 25, 23, 21, 20, 17, 16, 12, 2],
    physicalVolume := ((4526570593158516748153750189 : ℚ) / (62945954594761133193969726562500000000000000000000 : ℚ)),
    meanGap := ((164915953 : ℚ) / (198432000000 : ℚ)),
    factorMaxima := #[((39234443 : ℚ) / (416000000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((7359347 : ℚ) / (104000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))],
    gapWeightedMeans := #[((289389067321588512449 : ℚ) / (3357092830946400000000 : ℚ)), ((36644919365542714033 : ℚ) / (419636603868300000000 : ℚ)), ((42464648900801339507 : ℚ) / (335709283094640000000 : ℚ)), ((6387369731543476721 : ℚ) / (64559477518200000000 : ℚ)), ((76887818955698100787 : ℚ) / (839273207736600000000 : ℚ)), ((11120170137103759301 : ℚ) / (167854641547320000000 : ℚ)), ((55550905670144360921 : ℚ) / (1678546415473200000000 : ℚ)), ((18050815079886721523 : ℚ) / (559515471824400000000 : ℚ)), ((17746774372497342563 : ℚ) / (559515471824400000000 : ℚ)), ((4168773014955037417 : ℚ) / (139878867956100000000 : ℚ))],
    jensenBound := ((748337485815055278326019135308963755960460872965209909075838176187455003429671464710492329343221093127355486612899723980622747998323467267299098903490634711040000000000000000000000 : ℚ) / (1806378358999421390346163347891526505687563284384022027414849847597220369364834444501583245335272375657118891316056502991046525592210098631952030527718691831859886804943121730550932622650503009 : ℚ)),
    jensenFloorQ96 := (32822251023042827 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_simplexId_before"
  err.flush

theorem geometryRow030_simplexId_read :
    geometryRowsJson030.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped030.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_vertexIds_before"
  err.flush

theorem geometryRow030_vertexIds_read :
    geometryRowsJson030.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped030.vertexIds := by decide +kernel

noncomputable def geometryRow030_physicalVolumeNumeratorChars : List Char := ['4', '5', '2', '6', '5', '7', '0', '5', '9', '3', '1', '5', '8', '5', '1', '6', '7', '4', '8', '1', '5', '3', '7', '5', '0', '1', '8', '9']
noncomputable def geometryRow030_physicalVolumeDenominatorChars : List Char := ['6', '2', '9', '4', '5', '9', '5', '4', '5', '9', '4', '7', '6', '1', '1', '3', '3', '1', '9', '3', '9', '6', '9', '7', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_physicalVolumeText : String := String.ofList (geometryRow030_physicalVolumeNumeratorChars ++ '/' :: geometryRow030_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_physicalVolume_before_field"
  err.flush

theorem geometryRow030_physicalVolume_field :
    geometryRowsJson030.getObjVal? "physical_volume" = .ok (.str geometryRow030_physicalVolumeText) := by rfl

theorem geometryRow030_physicalVolume_numerator_no_slash :
    geometryRow030_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeNumeratorChars = some (4526570593158516748153750189 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeDenominatorChars = some (62945954594761133193969726562500000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_nonzero : (62945954594761133193969726562500000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_physicalVolume_parse :
    parseRational geometryRow030_physicalVolumeText = .ok geometryRowsTyped030.physicalVolume :=
  original_rational_fraction_of_chars geometryRow030_physicalVolumeNumeratorChars geometryRow030_physicalVolumeDenominatorChars
    (4526570593158516748153750189 : Int) (62945954594761133193969726562500000000000000000000 : Int)
    geometryRow030_physicalVolume_numerator_no_slash geometryRow030_physicalVolume_numerator_parse
    geometryRow030_physicalVolume_denominator_parse geometryRow030_physicalVolume_denominator_nonzero

theorem geometryRow030_physicalVolume_read :
    rationalField geometryRowsJson030 "physical_volume" = .ok geometryRowsTyped030.physicalVolume :=
  original_rationalField_of_string geometryRowsJson030 "physical_volume" geometryRow030_physicalVolumeText
    geometryRowsTyped030.physicalVolume geometryRow030_physicalVolume_field geometryRow030_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_physicalVolume_complete"
  err.flush

noncomputable def geometryRow030_meanGapNumeratorChars : List Char := ['1', '6', '4', '9', '1', '5', '9', '5', '3']
noncomputable def geometryRow030_meanGapDenominatorChars : List Char := ['1', '9', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_meanGapText : String := String.ofList (geometryRow030_meanGapNumeratorChars ++ '/' :: geometryRow030_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_meanGap_before_field"
  err.flush

theorem geometryRow030_meanGap_field :
    geometryRowsJson030.getObjVal? "mean_gap" = .ok (.str geometryRow030_meanGapText) := by rfl

theorem geometryRow030_meanGap_numerator_no_slash :
    geometryRow030_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_meanGap_numerator_parse :
    SourceJson.intChars geometryRow030_meanGapNumeratorChars = some (164915953 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_parse :
    SourceJson.intChars geometryRow030_meanGapDenominatorChars = some (198432000000 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_nonzero : (198432000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_meanGap_parse :
    parseRational geometryRow030_meanGapText = .ok geometryRowsTyped030.meanGap :=
  original_rational_fraction_of_chars geometryRow030_meanGapNumeratorChars geometryRow030_meanGapDenominatorChars
    (164915953 : Int) (198432000000 : Int)
    geometryRow030_meanGap_numerator_no_slash geometryRow030_meanGap_numerator_parse
    geometryRow030_meanGap_denominator_parse geometryRow030_meanGap_denominator_nonzero

theorem geometryRow030_meanGap_read :
    rationalField geometryRowsJson030 "mean_gap" = .ok geometryRowsTyped030.meanGap :=
  original_rationalField_of_string geometryRowsJson030 "mean_gap" geometryRow030_meanGapText
    geometryRowsTyped030.meanGap geometryRow030_meanGap_field geometryRow030_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_meanGap_complete"
  err.flush

noncomputable def geometryRow030_jensenBoundNumeratorChars : List Char := ['7', '4', '8', '3', '3', '7', '4', '8', '5', '8', '1', '5', '0', '5', '5', '2', '7', '8', '3', '2', '6', '0', '1', '9', '1', '3', '5', '3', '0', '8', '9', '6', '3', '7', '5', '5', '9', '6', '0', '4', '6', '0', '8', '7', '2', '9', '6', '5', '2', '0', '9', '9', '0', '9', '0', '7', '5', '8', '3', '8', '1', '7', '6', '1', '8', '7', '4', '5', '5', '0', '0', '3', '4', '2', '9', '6', '7', '1', '4', '6', '4', '7', '1', '0', '4', '9', '2', '3', '2', '9', '3', '4', '3', '2', '2', '1', '0', '9', '3', '1', '2', '7', '3', '5', '5', '4', '8', '6', '6', '1', '2', '8', '9', '9', '7', '2', '3', '9', '8', '0', '6', '2', '2', '7', '4', '7', '9', '9', '8', '3', '2', '3', '4', '6', '7', '2', '6', '7', '2', '9', '9', '0', '9', '8', '9', '0', '3', '4', '9', '0', '6', '3', '4', '7', '1', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_jensenBoundDenominatorChars : List Char := ['1', '8', '0', '6', '3', '7', '8', '3', '5', '8', '9', '9', '9', '4', '2', '1', '3', '9', '0', '3', '4', '6', '1', '6', '3', '3', '4', '7', '8', '9', '1', '5', '2', '6', '5', '0', '5', '6', '8', '7', '5', '6', '3', '2', '8', '4', '3', '8', '4', '0', '2', '2', '0', '2', '7', '4', '1', '4', '8', '4', '9', '8', '4', '7', '5', '9', '7', '2', '2', '0', '3', '6', '9', '3', '6', '4', '8', '3', '4', '4', '4', '4', '5', '0', '1', '5', '8', '3', '2', '4', '5', '3', '3', '5', '2', '7', '2', '3', '7', '5', '6', '5', '7', '1', '1', '8', '8', '9', '1', '3', '1', '6', '0', '5', '6', '5', '0', '2', '9', '9', '1', '0', '4', '6', '5', '2', '5', '5', '9', '2', '2', '1', '0', '0', '9', '8', '6', '3', '1', '9', '5', '2', '0', '3', '0', '5', '2', '7', '7', '1', '8', '6', '9', '1', '8', '3', '1', '8', '5', '9', '8', '8', '6', '8', '0', '4', '9', '4', '3', '1', '2', '1', '7', '3', '0', '5', '5', '0', '9', '3', '2', '6', '2', '2', '6', '5', '0', '5', '0', '3', '0', '0', '9']
noncomputable def geometryRow030_jensenBoundText : String := String.ofList (geometryRow030_jensenBoundNumeratorChars ++ '/' :: geometryRow030_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_jensenBound_before_field"
  err.flush

theorem geometryRow030_jensenBound_field :
    geometryRowsJson030.getObjVal? "jensen_bound" = .ok (.str geometryRow030_jensenBoundText) := by rfl

theorem geometryRow030_jensenBound_numerator_no_slash :
    geometryRow030_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow030_jensenBoundNumeratorChars = some (748337485815055278326019135308963755960460872965209909075838176187455003429671464710492329343221093127355486612899723980622747998323467267299098903490634711040000000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow030_jensenBoundDenominatorChars = some (1806378358999421390346163347891526505687563284384022027414849847597220369364834444501583245335272375657118891316056502991046525592210098631952030527718691831859886804943121730550932622650503009 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_nonzero : (1806378358999421390346163347891526505687563284384022027414849847597220369364834444501583245335272375657118891316056502991046525592210098631952030527718691831859886804943121730550932622650503009 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_jensenBound_parse :
    parseRational geometryRow030_jensenBoundText = .ok geometryRowsTyped030.jensenBound :=
  original_rational_fraction_of_chars geometryRow030_jensenBoundNumeratorChars geometryRow030_jensenBoundDenominatorChars
    (748337485815055278326019135308963755960460872965209909075838176187455003429671464710492329343221093127355486612899723980622747998323467267299098903490634711040000000000000000000000 : Int) (1806378358999421390346163347891526505687563284384022027414849847597220369364834444501583245335272375657118891316056502991046525592210098631952030527718691831859886804943121730550932622650503009 : Int)
    geometryRow030_jensenBound_numerator_no_slash geometryRow030_jensenBound_numerator_parse
    geometryRow030_jensenBound_denominator_parse geometryRow030_jensenBound_denominator_nonzero

theorem geometryRow030_jensenBound_read :
    rationalField geometryRowsJson030 "jensen_bound" = .ok geometryRowsTyped030.jensenBound :=
  original_rationalField_of_string geometryRowsJson030 "jensen_bound" geometryRow030_jensenBoundText
    geometryRowsTyped030.jensenBound geometryRow030_jensenBound_field geometryRow030_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_factorMaxima_before"
  err.flush

theorem geometryRow030_factorMaxima_read :
    rationalArrayField geometryRowsJson030 "factor_maxima" = .ok geometryRowsTyped030.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_gapWeightedMeans_before"
  err.flush

theorem geometryRow030_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson030 "gap_weighted_means" = .ok geometryRowsTyped030.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow030_floorChars : List Char := ['3', '2', '8', '2', '2', '2', '5', '1', '0', '2', '3', '0', '4', '2', '8', '2', '7']
noncomputable def geometryRow030_floorText : String := String.ofList geometryRow030_floorChars

theorem geometryRow030_floor_text_read :
    geometryRowsJson030.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow030_floorText := by rfl

theorem geometryRow030_floor_chars_parse :
    SourceJson.intChars geometryRow030_floorChars = some (32822251023042827 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_030_original_decoder_complete"
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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
