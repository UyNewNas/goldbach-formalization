import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800

/-! Original GeometryRow 35: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson035 : SourceJson :=
  (simplicesChunk035Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped035 : GeometryRow :=
  { simplexId := 35,
    vertexIds := #[27, 25, 23, 22, 21, 19, 18, 13, 3],
    physicalVolume := ((277452124603345737960446779 : ℚ) / (49666132352812500000000000000000000000000000000000000 : ℚ)),
    meanGap := ((20250079 : ℚ) / (26904000000 : ℚ)),
    factorMaxima := #[((14640661 : ℚ) / (152000000 : ℚ)), ((3796851 : ℚ) / (38000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((8140597 : ℚ) / (114000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ))],
    gapWeightedMeans := #[((24775493234737917229 : ℚ) / (286024265843400000000 : ℚ)), ((12533249742651370487 : ℚ) / (143012132921700000000 : ℚ)), ((3630256468119839707 : ℚ) / (28602426584340000000 : ℚ)), ((4688748842743577197 : ℚ) / (47670710973900000000 : ℚ)), ((13174623737501837579 : ℚ) / (143012132921700000000 : ℚ)), ((472559299483685231 : ℚ) / (7150606646085000000 : ℚ)), ((393444976933533893 : ℚ) / (11917677743475000000 : ℚ)), ((1150547728146190351 : ℚ) / (35753033230425000000 : ℚ)), ((4376356689625718429 : ℚ) / (143012132921700000000 : ℚ)), ((4376328087199134089 : ℚ) / (143012132921700000000 : ℚ))],
    jensenBound := ((288267655913542339770291687606426301505584287893964295057228849106533351655257022061998211167778724512509874955625508163676830100834892029400000000000000000000000000000 : ℚ) / (9837574774854211270886715994143810914738583482762855861251490724536804484415989907634876755187256823712359526833519983144492637219894881050462198969808009038967033299774586079334795291 : ℚ)),
    jensenFloorQ96 := (2321600314409 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_simplexId_before"
  err.flush

theorem geometryRow035_simplexId_read :
    geometryRowsJson035.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped035.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_vertexIds_before"
  err.flush

theorem geometryRow035_vertexIds_read :
    geometryRowsJson035.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped035.vertexIds := by decide +kernel

noncomputable def geometryRow035_physicalVolumeNumeratorChars : List Char := ['2', '7', '7', '4', '5', '2', '1', '2', '4', '6', '0', '3', '3', '4', '5', '7', '3', '7', '9', '6', '0', '4', '4', '6', '7', '7', '9']
noncomputable def geometryRow035_physicalVolumeDenominatorChars : List Char := ['4', '9', '6', '6', '6', '1', '3', '2', '3', '5', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_physicalVolumeText : String := String.ofList (geometryRow035_physicalVolumeNumeratorChars ++ '/' :: geometryRow035_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_physicalVolume_before_field"
  err.flush

theorem geometryRow035_physicalVolume_field :
    geometryRowsJson035.getObjVal? "physical_volume" = .ok (.str geometryRow035_physicalVolumeText) := by rfl

theorem geometryRow035_physicalVolume_numerator_no_slash :
    geometryRow035_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeNumeratorChars = some (277452124603345737960446779 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeDenominatorChars = some (49666132352812500000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_nonzero : (49666132352812500000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_physicalVolume_parse :
    parseRational geometryRow035_physicalVolumeText = .ok geometryRowsTyped035.physicalVolume :=
  original_rational_fraction_of_chars geometryRow035_physicalVolumeNumeratorChars geometryRow035_physicalVolumeDenominatorChars
    (277452124603345737960446779 : Int) (49666132352812500000000000000000000000000000000000000 : Int)
    geometryRow035_physicalVolume_numerator_no_slash geometryRow035_physicalVolume_numerator_parse
    geometryRow035_physicalVolume_denominator_parse geometryRow035_physicalVolume_denominator_nonzero

theorem geometryRow035_physicalVolume_read :
    rationalField geometryRowsJson035 "physical_volume" = .ok geometryRowsTyped035.physicalVolume :=
  original_rationalField_of_string geometryRowsJson035 "physical_volume" geometryRow035_physicalVolumeText
    geometryRowsTyped035.physicalVolume geometryRow035_physicalVolume_field geometryRow035_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_physicalVolume_complete"
  err.flush

noncomputable def geometryRow035_meanGapNumeratorChars : List Char := ['2', '0', '2', '5', '0', '0', '7', '9']
noncomputable def geometryRow035_meanGapDenominatorChars : List Char := ['2', '6', '9', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_meanGapText : String := String.ofList (geometryRow035_meanGapNumeratorChars ++ '/' :: geometryRow035_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_meanGap_before_field"
  err.flush

theorem geometryRow035_meanGap_field :
    geometryRowsJson035.getObjVal? "mean_gap" = .ok (.str geometryRow035_meanGapText) := by rfl

theorem geometryRow035_meanGap_numerator_no_slash :
    geometryRow035_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_meanGap_numerator_parse :
    SourceJson.intChars geometryRow035_meanGapNumeratorChars = some (20250079 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_parse :
    SourceJson.intChars geometryRow035_meanGapDenominatorChars = some (26904000000 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_nonzero : (26904000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_meanGap_parse :
    parseRational geometryRow035_meanGapText = .ok geometryRowsTyped035.meanGap :=
  original_rational_fraction_of_chars geometryRow035_meanGapNumeratorChars geometryRow035_meanGapDenominatorChars
    (20250079 : Int) (26904000000 : Int)
    geometryRow035_meanGap_numerator_no_slash geometryRow035_meanGap_numerator_parse
    geometryRow035_meanGap_denominator_parse geometryRow035_meanGap_denominator_nonzero

theorem geometryRow035_meanGap_read :
    rationalField geometryRowsJson035 "mean_gap" = .ok geometryRowsTyped035.meanGap :=
  original_rationalField_of_string geometryRowsJson035 "mean_gap" geometryRow035_meanGapText
    geometryRowsTyped035.meanGap geometryRow035_meanGap_field geometryRow035_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_meanGap_complete"
  err.flush

noncomputable def geometryRow035_jensenBoundNumeratorChars : List Char := ['2', '8', '8', '2', '6', '7', '6', '5', '5', '9', '1', '3', '5', '4', '2', '3', '3', '9', '7', '7', '0', '2', '9', '1', '6', '8', '7', '6', '0', '6', '4', '2', '6', '3', '0', '1', '5', '0', '5', '5', '8', '4', '2', '8', '7', '8', '9', '3', '9', '6', '4', '2', '9', '5', '0', '5', '7', '2', '2', '8', '8', '4', '9', '1', '0', '6', '5', '3', '3', '3', '5', '1', '6', '5', '5', '2', '5', '7', '0', '2', '2', '0', '6', '1', '9', '9', '8', '2', '1', '1', '1', '6', '7', '7', '7', '8', '7', '2', '4', '5', '1', '2', '5', '0', '9', '8', '7', '4', '9', '5', '5', '6', '2', '5', '5', '0', '8', '1', '6', '3', '6', '7', '6', '8', '3', '0', '1', '0', '0', '8', '3', '4', '8', '9', '2', '0', '2', '9', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_jensenBoundDenominatorChars : List Char := ['9', '8', '3', '7', '5', '7', '4', '7', '7', '4', '8', '5', '4', '2', '1', '1', '2', '7', '0', '8', '8', '6', '7', '1', '5', '9', '9', '4', '1', '4', '3', '8', '1', '0', '9', '1', '4', '7', '3', '8', '5', '8', '3', '4', '8', '2', '7', '6', '2', '8', '5', '5', '8', '6', '1', '2', '5', '1', '4', '9', '0', '7', '2', '4', '5', '3', '6', '8', '0', '4', '4', '8', '4', '4', '1', '5', '9', '8', '9', '9', '0', '7', '6', '3', '4', '8', '7', '6', '7', '5', '5', '1', '8', '7', '2', '5', '6', '8', '2', '3', '7', '1', '2', '3', '5', '9', '5', '2', '6', '8', '3', '3', '5', '1', '9', '9', '8', '3', '1', '4', '4', '4', '9', '2', '6', '3', '7', '2', '1', '9', '8', '9', '4', '8', '8', '1', '0', '5', '0', '4', '6', '2', '1', '9', '8', '9', '6', '9', '8', '0', '8', '0', '0', '9', '0', '3', '8', '9', '6', '7', '0', '3', '3', '2', '9', '9', '7', '7', '4', '5', '8', '6', '0', '7', '9', '3', '3', '4', '7', '9', '5', '2', '9', '1']
noncomputable def geometryRow035_jensenBoundText : String := String.ofList (geometryRow035_jensenBoundNumeratorChars ++ '/' :: geometryRow035_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_jensenBound_before_field"
  err.flush

theorem geometryRow035_jensenBound_field :
    geometryRowsJson035.getObjVal? "jensen_bound" = .ok (.str geometryRow035_jensenBoundText) := by rfl

theorem geometryRow035_jensenBound_numerator_no_slash :
    geometryRow035_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow035_jensenBoundNumeratorChars = some (288267655913542339770291687606426301505584287893964295057228849106533351655257022061998211167778724512509874955625508163676830100834892029400000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow035_jensenBoundDenominatorChars = some (9837574774854211270886715994143810914738583482762855861251490724536804484415989907634876755187256823712359526833519983144492637219894881050462198969808009038967033299774586079334795291 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_nonzero : (9837574774854211270886715994143810914738583482762855861251490724536804484415989907634876755187256823712359526833519983144492637219894881050462198969808009038967033299774586079334795291 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_jensenBound_parse :
    parseRational geometryRow035_jensenBoundText = .ok geometryRowsTyped035.jensenBound :=
  original_rational_fraction_of_chars geometryRow035_jensenBoundNumeratorChars geometryRow035_jensenBoundDenominatorChars
    (288267655913542339770291687606426301505584287893964295057228849106533351655257022061998211167778724512509874955625508163676830100834892029400000000000000000000000000000 : Int) (9837574774854211270886715994143810914738583482762855861251490724536804484415989907634876755187256823712359526833519983144492637219894881050462198969808009038967033299774586079334795291 : Int)
    geometryRow035_jensenBound_numerator_no_slash geometryRow035_jensenBound_numerator_parse
    geometryRow035_jensenBound_denominator_parse geometryRow035_jensenBound_denominator_nonzero

theorem geometryRow035_jensenBound_read :
    rationalField geometryRowsJson035 "jensen_bound" = .ok geometryRowsTyped035.jensenBound :=
  original_rationalField_of_string geometryRowsJson035 "jensen_bound" geometryRow035_jensenBoundText
    geometryRowsTyped035.jensenBound geometryRow035_jensenBound_field geometryRow035_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_factorMaxima_before"
  err.flush

theorem geometryRow035_factorMaxima_read :
    rationalArrayField geometryRowsJson035 "factor_maxima" = .ok geometryRowsTyped035.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_gapWeightedMeans_before"
  err.flush

theorem geometryRow035_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson035 "gap_weighted_means" = .ok geometryRowsTyped035.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow035_floorChars : List Char := ['2', '3', '2', '1', '6', '0', '0', '3', '1', '4', '4', '0', '9']
noncomputable def geometryRow035_floorText : String := String.ofList geometryRow035_floorChars

theorem geometryRow035_floor_text_read :
    geometryRowsJson035.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow035_floorText := by rfl

theorem geometryRow035_floor_chars_parse :
    SourceJson.intChars geometryRow035_floorChars = some (2321600314409 : Int) := by decide +kernel

theorem geometryRow035_floor_parse :
    parseInteger geometryRow035_floorText = .ok geometryRowsTyped035.jensenFloorQ96 := by
  simp only [geometryRow035_floorText, parseInteger, String.toList_ofList, geometryRow035_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_035 :
    decodeGeometryRow geometryRowsJson035 = .ok geometryRowsTyped035 :=
  original_geometryRow_of_fields geometryRowsJson035 geometryRowsTyped035 geometryRow035_floorText
    geometryRow035_simplexId_read geometryRow035_vertexIds_read
    geometryRow035_physicalVolume_read geometryRow035_meanGap_read
    geometryRow035_factorMaxima_read geometryRow035_gapWeightedMeans_read
    geometryRow035_jensenBound_read geometryRow035_floor_text_read geometryRow035_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_035_original_decoder_complete"
  err.flush

#print axioms geometryRow035_simplexId_read
#print axioms geometryRow035_vertexIds_read
#print axioms geometryRow035_physicalVolume_field
#print axioms geometryRow035_physicalVolume_numerator_no_slash
#print axioms geometryRow035_physicalVolume_numerator_parse
#print axioms geometryRow035_physicalVolume_denominator_parse
#print axioms geometryRow035_physicalVolume_denominator_nonzero
#print axioms geometryRow035_physicalVolume_parse
#print axioms geometryRow035_physicalVolume_read
#print axioms geometryRow035_meanGap_field
#print axioms geometryRow035_meanGap_numerator_no_slash
#print axioms geometryRow035_meanGap_numerator_parse
#print axioms geometryRow035_meanGap_denominator_parse
#print axioms geometryRow035_meanGap_denominator_nonzero
#print axioms geometryRow035_meanGap_parse
#print axioms geometryRow035_meanGap_read
#print axioms geometryRow035_jensenBound_field
#print axioms geometryRow035_jensenBound_numerator_no_slash
#print axioms geometryRow035_jensenBound_numerator_parse
#print axioms geometryRow035_jensenBound_denominator_parse
#print axioms geometryRow035_jensenBound_denominator_nonzero
#print axioms geometryRow035_jensenBound_parse
#print axioms geometryRow035_jensenBound_read
#print axioms geometryRow035_factorMaxima_read
#print axioms geometryRow035_gapWeightedMeans_read
#print axioms geometryRow035_floor_text_read
#print axioms geometryRow035_floor_chars_parse
#print axioms geometryRow035_floor_parse
#print axioms decode_geometry_Rows_035

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
