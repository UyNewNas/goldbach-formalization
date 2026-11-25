import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900

/-! Original GeometryRow 36: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson036 : SourceJson :=
  (simplicesChunk036Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped036 : GeometryRow :=
  { simplexId := 36,
    vertexIds := #[27, 25, 24, 10, 8, 6, 5, 3, 1],
    physicalVolume := ((20886821678861246294674741046425871167 : ℚ) / (642764408832000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((3365581 : ℚ) / (36000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((26366 : ℚ) / (609375 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((32353735617109 : ℚ) / (344416800000000 : ℚ)), ((32601508609849 : ℚ) / (344416800000000 : ℚ)), ((125594362695101 : ℚ) / (1033250400000000 : ℚ)), ((584625132313 : ℚ) / (6457815000000 : ℚ)), ((85742477288207 : ℚ) / (1033250400000000 : ℚ)), ((74383336884739 : ℚ) / (1033250400000000 : ℚ)), ((2111512688223 : ℚ) / (57402800000000 : ℚ)), ((3519918678121 : ℚ) / (103325040000000 : ℚ)), ((33543183748981 : ℚ) / (1033250400000000 : ℚ)), ((33543045982261 : ℚ) / (1033250400000000 : ℚ))],
    jensenBound := ((31634273171466613756177363226911171777029957596303742222147056782234474427082496930773344256000000000000000000000 : ℚ) / (470082321921228927230589999689626668957644936005926715926584291803211150018946346654620996979230602132215277410520621279675200721 : ℚ)),
    jensenFloorQ96 := (5331673238862 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_simplexId_before"
  err.flush

theorem geometryRow036_simplexId_read :
    geometryRowsJson036.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped036.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_vertexIds_before"
  err.flush

theorem geometryRow036_vertexIds_read :
    geometryRowsJson036.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped036.vertexIds := by decide +kernel

noncomputable def geometryRow036_physicalVolumeNumeratorChars : List Char := ['2', '0', '8', '8', '6', '8', '2', '1', '6', '7', '8', '8', '6', '1', '2', '4', '6', '2', '9', '4', '6', '7', '4', '7', '4', '1', '0', '4', '6', '4', '2', '5', '8', '7', '1', '1', '6', '7']
noncomputable def geometryRow036_physicalVolumeDenominatorChars : List Char := ['6', '4', '2', '7', '6', '4', '4', '0', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_physicalVolumeText : String := String.ofList (geometryRow036_physicalVolumeNumeratorChars ++ '/' :: geometryRow036_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_physicalVolume_before_field"
  err.flush

theorem geometryRow036_physicalVolume_field :
    geometryRowsJson036.getObjVal? "physical_volume" = .ok (.str geometryRow036_physicalVolumeText) := by rfl

theorem geometryRow036_physicalVolume_numerator_no_slash :
    geometryRow036_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeNumeratorChars = some (20886821678861246294674741046425871167 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeDenominatorChars = some (642764408832000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_nonzero : (642764408832000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_physicalVolume_parse :
    parseRational geometryRow036_physicalVolumeText = .ok geometryRowsTyped036.physicalVolume :=
  original_rational_fraction_of_chars geometryRow036_physicalVolumeNumeratorChars geometryRow036_physicalVolumeDenominatorChars
    (20886821678861246294674741046425871167 : Int) (642764408832000000000000000000000000000000000000000000000000000 : Int)
    geometryRow036_physicalVolume_numerator_no_slash geometryRow036_physicalVolume_numerator_parse
    geometryRow036_physicalVolume_denominator_parse geometryRow036_physicalVolume_denominator_nonzero

theorem geometryRow036_physicalVolume_read :
    rationalField geometryRowsJson036 "physical_volume" = .ok geometryRowsTyped036.physicalVolume :=
  original_rationalField_of_string geometryRowsJson036 "physical_volume" geometryRow036_physicalVolumeText
    geometryRowsTyped036.physicalVolume geometryRow036_physicalVolume_field geometryRow036_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_physicalVolume_complete"
  err.flush

noncomputable def geometryRow036_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow036_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_meanGapText : String := String.ofList (geometryRow036_meanGapNumeratorChars ++ '/' :: geometryRow036_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_meanGap_before_field"
  err.flush

theorem geometryRow036_meanGap_field :
    geometryRowsJson036.getObjVal? "mean_gap" = .ok (.str geometryRow036_meanGapText) := by rfl

theorem geometryRow036_meanGap_numerator_no_slash :
    geometryRow036_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_meanGap_numerator_parse :
    SourceJson.intChars geometryRow036_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_parse :
    SourceJson.intChars geometryRow036_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_meanGap_parse :
    parseRational geometryRow036_meanGapText = .ok geometryRowsTyped036.meanGap :=
  original_rational_fraction_of_chars geometryRow036_meanGapNumeratorChars geometryRow036_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow036_meanGap_numerator_no_slash geometryRow036_meanGap_numerator_parse
    geometryRow036_meanGap_denominator_parse geometryRow036_meanGap_denominator_nonzero

theorem geometryRow036_meanGap_read :
    rationalField geometryRowsJson036 "mean_gap" = .ok geometryRowsTyped036.meanGap :=
  original_rationalField_of_string geometryRowsJson036 "mean_gap" geometryRow036_meanGapText
    geometryRowsTyped036.meanGap geometryRow036_meanGap_field geometryRow036_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_meanGap_complete"
  err.flush

noncomputable def geometryRow036_jensenBoundNumeratorChars : List Char := ['3', '1', '6', '3', '4', '2', '7', '3', '1', '7', '1', '4', '6', '6', '6', '1', '3', '7', '5', '6', '1', '7', '7', '3', '6', '3', '2', '2', '6', '9', '1', '1', '1', '7', '1', '7', '7', '7', '0', '2', '9', '9', '5', '7', '5', '9', '6', '3', '0', '3', '7', '4', '2', '2', '2', '2', '1', '4', '7', '0', '5', '6', '7', '8', '2', '2', '3', '4', '4', '7', '4', '4', '2', '7', '0', '8', '2', '4', '9', '6', '9', '3', '0', '7', '7', '3', '3', '4', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_jensenBoundDenominatorChars : List Char := ['4', '7', '0', '0', '8', '2', '3', '2', '1', '9', '2', '1', '2', '2', '8', '9', '2', '7', '2', '3', '0', '5', '8', '9', '9', '9', '9', '6', '8', '9', '6', '2', '6', '6', '6', '8', '9', '5', '7', '6', '4', '4', '9', '3', '6', '0', '0', '5', '9', '2', '6', '7', '1', '5', '9', '2', '6', '5', '8', '4', '2', '9', '1', '8', '0', '3', '2', '1', '1', '1', '5', '0', '0', '1', '8', '9', '4', '6', '3', '4', '6', '6', '5', '4', '6', '2', '0', '9', '9', '6', '9', '7', '9', '2', '3', '0', '6', '0', '2', '1', '3', '2', '2', '1', '5', '2', '7', '7', '4', '1', '0', '5', '2', '0', '6', '2', '1', '2', '7', '9', '6', '7', '5', '2', '0', '0', '7', '2', '1']
noncomputable def geometryRow036_jensenBoundText : String := String.ofList (geometryRow036_jensenBoundNumeratorChars ++ '/' :: geometryRow036_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_jensenBound_before_field"
  err.flush

theorem geometryRow036_jensenBound_field :
    geometryRowsJson036.getObjVal? "jensen_bound" = .ok (.str geometryRow036_jensenBoundText) := by rfl

theorem geometryRow036_jensenBound_numerator_no_slash :
    geometryRow036_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow036_jensenBoundNumeratorChars = some (31634273171466613756177363226911171777029957596303742222147056782234474427082496930773344256000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow036_jensenBoundDenominatorChars = some (470082321921228927230589999689626668957644936005926715926584291803211150018946346654620996979230602132215277410520621279675200721 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_nonzero : (470082321921228927230589999689626668957644936005926715926584291803211150018946346654620996979230602132215277410520621279675200721 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_jensenBound_parse :
    parseRational geometryRow036_jensenBoundText = .ok geometryRowsTyped036.jensenBound :=
  original_rational_fraction_of_chars geometryRow036_jensenBoundNumeratorChars geometryRow036_jensenBoundDenominatorChars
    (31634273171466613756177363226911171777029957596303742222147056782234474427082496930773344256000000000000000000000 : Int) (470082321921228927230589999689626668957644936005926715926584291803211150018946346654620996979230602132215277410520621279675200721 : Int)
    geometryRow036_jensenBound_numerator_no_slash geometryRow036_jensenBound_numerator_parse
    geometryRow036_jensenBound_denominator_parse geometryRow036_jensenBound_denominator_nonzero

theorem geometryRow036_jensenBound_read :
    rationalField geometryRowsJson036 "jensen_bound" = .ok geometryRowsTyped036.jensenBound :=
  original_rationalField_of_string geometryRowsJson036 "jensen_bound" geometryRow036_jensenBoundText
    geometryRowsTyped036.jensenBound geometryRow036_jensenBound_field geometryRow036_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_factorMaxima_before"
  err.flush

theorem geometryRow036_factorMaxima_read :
    rationalArrayField geometryRowsJson036 "factor_maxima" = .ok geometryRowsTyped036.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_gapWeightedMeans_before"
  err.flush

theorem geometryRow036_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson036 "gap_weighted_means" = .ok geometryRowsTyped036.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow036_floorChars : List Char := ['5', '3', '3', '1', '6', '7', '3', '2', '3', '8', '8', '6', '2']
noncomputable def geometryRow036_floorText : String := String.ofList geometryRow036_floorChars

theorem geometryRow036_floor_text_read :
    geometryRowsJson036.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow036_floorText := by rfl

theorem geometryRow036_floor_chars_parse :
    SourceJson.intChars geometryRow036_floorChars = some (5331673238862 : Int) := by decide +kernel

theorem geometryRow036_floor_parse :
    parseInteger geometryRow036_floorText = .ok geometryRowsTyped036.jensenFloorQ96 := by
  simp only [geometryRow036_floorText, parseInteger, String.toList_ofList, geometryRow036_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_036 :
    decodeGeometryRow geometryRowsJson036 = .ok geometryRowsTyped036 :=
  original_geometryRow_of_fields geometryRowsJson036 geometryRowsTyped036 geometryRow036_floorText
    geometryRow036_simplexId_read geometryRow036_vertexIds_read
    geometryRow036_physicalVolume_read geometryRow036_meanGap_read
    geometryRow036_factorMaxima_read geometryRow036_gapWeightedMeans_read
    geometryRow036_jensenBound_read geometryRow036_floor_text_read geometryRow036_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_036_original_decoder_complete"
  err.flush

#print axioms geometryRow036_simplexId_read
#print axioms geometryRow036_vertexIds_read
#print axioms geometryRow036_physicalVolume_field
#print axioms geometryRow036_physicalVolume_numerator_no_slash
#print axioms geometryRow036_physicalVolume_numerator_parse
#print axioms geometryRow036_physicalVolume_denominator_parse
#print axioms geometryRow036_physicalVolume_denominator_nonzero
#print axioms geometryRow036_physicalVolume_parse
#print axioms geometryRow036_physicalVolume_read
#print axioms geometryRow036_meanGap_field
#print axioms geometryRow036_meanGap_numerator_no_slash
#print axioms geometryRow036_meanGap_numerator_parse
#print axioms geometryRow036_meanGap_denominator_parse
#print axioms geometryRow036_meanGap_denominator_nonzero
#print axioms geometryRow036_meanGap_parse
#print axioms geometryRow036_meanGap_read
#print axioms geometryRow036_jensenBound_field
#print axioms geometryRow036_jensenBound_numerator_no_slash
#print axioms geometryRow036_jensenBound_numerator_parse
#print axioms geometryRow036_jensenBound_denominator_parse
#print axioms geometryRow036_jensenBound_denominator_nonzero
#print axioms geometryRow036_jensenBound_parse
#print axioms geometryRow036_jensenBound_read
#print axioms geometryRow036_factorMaxima_read
#print axioms geometryRow036_gapWeightedMeans_read
#print axioms geometryRow036_floor_text_read
#print axioms geometryRow036_floor_chars_parse
#print axioms geometryRow036_floor_parse
#print axioms decode_geometry_Rows_036

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
