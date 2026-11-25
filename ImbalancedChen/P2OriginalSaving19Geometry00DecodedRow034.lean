import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00800

/-! Original GeometryRow 34: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson034 : SourceJson :=
  (simplicesChunk034Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped034 : GeometryRow :=
  { simplexId := 34,
    vertexIds := #[27, 25, 23, 22, 21, 19, 18, 3, 1],
    physicalVolume := ((468293058603433574233269551 : ℚ) / (35444162250000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((42320273833 : ℚ) / (478800000000 : ℚ)), ((42664721923 : ℚ) / (478800000000 : ℚ)), ((2676931779 : ℚ) / (21280000000 : ℚ)), ((92068823053 : ℚ) / (957600000000 : ℚ)), ((86859596717 : ℚ) / (957600000000 : ℚ)), ((1442959573 : ℚ) / (21280000000 : ℚ)), ((15946367309 : ℚ) / (478800000000 : ℚ)), ((15547460941 : ℚ) / (478800000000 : ℚ)), ((14886503041 : ℚ) / (478800000000 : ℚ)), ((14886407281 : ℚ) / (478800000000 : ℚ))],
    jensenBound := ((41884106167746366201856540324696348348603990425414402048000000000000000000000000000 : ℚ) / (1214579174656388829336837398863483801393407746185803411157642271062017404727574287780998361563368639 : ℚ)),
    jensenFloorQ96 := (2732140349073 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_simplexId_before"
  err.flush

theorem geometryRow034_simplexId_read :
    geometryRowsJson034.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped034.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_vertexIds_before"
  err.flush

theorem geometryRow034_vertexIds_read :
    geometryRowsJson034.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped034.vertexIds := by decide +kernel

noncomputable def geometryRow034_physicalVolumeNumeratorChars : List Char := ['4', '6', '8', '2', '9', '3', '0', '5', '8', '6', '0', '3', '4', '3', '3', '5', '7', '4', '2', '3', '3', '2', '6', '9', '5', '5', '1']
noncomputable def geometryRow034_physicalVolumeDenominatorChars : List Char := ['3', '5', '4', '4', '4', '1', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_physicalVolumeText : String := String.ofList (geometryRow034_physicalVolumeNumeratorChars ++ '/' :: geometryRow034_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_physicalVolume_before_field"
  err.flush

theorem geometryRow034_physicalVolume_field :
    geometryRowsJson034.getObjVal? "physical_volume" = .ok (.str geometryRow034_physicalVolumeText) := by rfl

theorem geometryRow034_physicalVolume_numerator_no_slash :
    geometryRow034_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeNumeratorChars = some (468293058603433574233269551 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeDenominatorChars = some (35444162250000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_nonzero : (35444162250000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_physicalVolume_parse :
    parseRational geometryRow034_physicalVolumeText = .ok geometryRowsTyped034.physicalVolume :=
  original_rational_fraction_of_chars geometryRow034_physicalVolumeNumeratorChars geometryRow034_physicalVolumeDenominatorChars
    (468293058603433574233269551 : Int) (35444162250000000000000000000000000000000000000000000 : Int)
    geometryRow034_physicalVolume_numerator_no_slash geometryRow034_physicalVolume_numerator_parse
    geometryRow034_physicalVolume_denominator_parse geometryRow034_physicalVolume_denominator_nonzero

theorem geometryRow034_physicalVolume_read :
    rationalField geometryRowsJson034 "physical_volume" = .ok geometryRowsTyped034.physicalVolume :=
  original_rationalField_of_string geometryRowsJson034 "physical_volume" geometryRow034_physicalVolumeText
    geometryRowsTyped034.physicalVolume geometryRow034_physicalVolume_field geometryRow034_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_physicalVolume_complete"
  err.flush

noncomputable def geometryRow034_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow034_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_meanGapText : String := String.ofList (geometryRow034_meanGapNumeratorChars ++ '/' :: geometryRow034_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_meanGap_before_field"
  err.flush

theorem geometryRow034_meanGap_field :
    geometryRowsJson034.getObjVal? "mean_gap" = .ok (.str geometryRow034_meanGapText) := by rfl

theorem geometryRow034_meanGap_numerator_no_slash :
    geometryRow034_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_meanGap_numerator_parse :
    SourceJson.intChars geometryRow034_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_parse :
    SourceJson.intChars geometryRow034_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_meanGap_parse :
    parseRational geometryRow034_meanGapText = .ok geometryRowsTyped034.meanGap :=
  original_rational_fraction_of_chars geometryRow034_meanGapNumeratorChars geometryRow034_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow034_meanGap_numerator_no_slash geometryRow034_meanGap_numerator_parse
    geometryRow034_meanGap_denominator_parse geometryRow034_meanGap_denominator_nonzero

theorem geometryRow034_meanGap_read :
    rationalField geometryRowsJson034 "mean_gap" = .ok geometryRowsTyped034.meanGap :=
  original_rationalField_of_string geometryRowsJson034 "mean_gap" geometryRow034_meanGapText
    geometryRowsTyped034.meanGap geometryRow034_meanGap_field geometryRow034_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_meanGap_complete"
  err.flush

noncomputable def geometryRow034_jensenBoundNumeratorChars : List Char := ['4', '1', '8', '8', '4', '1', '0', '6', '1', '6', '7', '7', '4', '6', '3', '6', '6', '2', '0', '1', '8', '5', '6', '5', '4', '0', '3', '2', '4', '6', '9', '6', '3', '4', '8', '3', '4', '8', '6', '0', '3', '9', '9', '0', '4', '2', '5', '4', '1', '4', '4', '0', '2', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_jensenBoundDenominatorChars : List Char := ['1', '2', '1', '4', '5', '7', '9', '1', '7', '4', '6', '5', '6', '3', '8', '8', '8', '2', '9', '3', '3', '6', '8', '3', '7', '3', '9', '8', '8', '6', '3', '4', '8', '3', '8', '0', '1', '3', '9', '3', '4', '0', '7', '7', '4', '6', '1', '8', '5', '8', '0', '3', '4', '1', '1', '1', '5', '7', '6', '4', '2', '2', '7', '1', '0', '6', '2', '0', '1', '7', '4', '0', '4', '7', '2', '7', '5', '7', '4', '2', '8', '7', '7', '8', '0', '9', '9', '8', '3', '6', '1', '5', '6', '3', '3', '6', '8', '6', '3', '9']
noncomputable def geometryRow034_jensenBoundText : String := String.ofList (geometryRow034_jensenBoundNumeratorChars ++ '/' :: geometryRow034_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_jensenBound_before_field"
  err.flush

theorem geometryRow034_jensenBound_field :
    geometryRowsJson034.getObjVal? "jensen_bound" = .ok (.str geometryRow034_jensenBoundText) := by rfl

theorem geometryRow034_jensenBound_numerator_no_slash :
    geometryRow034_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow034_jensenBoundNumeratorChars = some (41884106167746366201856540324696348348603990425414402048000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow034_jensenBoundDenominatorChars = some (1214579174656388829336837398863483801393407746185803411157642271062017404727574287780998361563368639 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_nonzero : (1214579174656388829336837398863483801393407746185803411157642271062017404727574287780998361563368639 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_jensenBound_parse :
    parseRational geometryRow034_jensenBoundText = .ok geometryRowsTyped034.jensenBound :=
  original_rational_fraction_of_chars geometryRow034_jensenBoundNumeratorChars geometryRow034_jensenBoundDenominatorChars
    (41884106167746366201856540324696348348603990425414402048000000000000000000000000000 : Int) (1214579174656388829336837398863483801393407746185803411157642271062017404727574287780998361563368639 : Int)
    geometryRow034_jensenBound_numerator_no_slash geometryRow034_jensenBound_numerator_parse
    geometryRow034_jensenBound_denominator_parse geometryRow034_jensenBound_denominator_nonzero

theorem geometryRow034_jensenBound_read :
    rationalField geometryRowsJson034 "jensen_bound" = .ok geometryRowsTyped034.jensenBound :=
  original_rationalField_of_string geometryRowsJson034 "jensen_bound" geometryRow034_jensenBoundText
    geometryRowsTyped034.jensenBound geometryRow034_jensenBound_field geometryRow034_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_factorMaxima_before"
  err.flush

theorem geometryRow034_factorMaxima_read :
    rationalArrayField geometryRowsJson034 "factor_maxima" = .ok geometryRowsTyped034.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_gapWeightedMeans_before"
  err.flush

theorem geometryRow034_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson034 "gap_weighted_means" = .ok geometryRowsTyped034.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow034_floorChars : List Char := ['2', '7', '3', '2', '1', '4', '0', '3', '4', '9', '0', '7', '3']
noncomputable def geometryRow034_floorText : String := String.ofList geometryRow034_floorChars

theorem geometryRow034_floor_text_read :
    geometryRowsJson034.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow034_floorText := by rfl

theorem geometryRow034_floor_chars_parse :
    SourceJson.intChars geometryRow034_floorChars = some (2732140349073 : Int) := by decide +kernel

theorem geometryRow034_floor_parse :
    parseInteger geometryRow034_floorText = .ok geometryRowsTyped034.jensenFloorQ96 := by
  simp only [geometryRow034_floorText, parseInteger, String.toList_ofList, geometryRow034_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_034 :
    decodeGeometryRow geometryRowsJson034 = .ok geometryRowsTyped034 :=
  original_geometryRow_of_fields geometryRowsJson034 geometryRowsTyped034 geometryRow034_floorText
    geometryRow034_simplexId_read geometryRow034_vertexIds_read
    geometryRow034_physicalVolume_read geometryRow034_meanGap_read
    geometryRow034_factorMaxima_read geometryRow034_gapWeightedMeans_read
    geometryRow034_jensenBound_read geometryRow034_floor_text_read geometryRow034_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_034_original_decoder_complete"
  err.flush

#print axioms geometryRow034_simplexId_read
#print axioms geometryRow034_vertexIds_read
#print axioms geometryRow034_physicalVolume_field
#print axioms geometryRow034_physicalVolume_numerator_no_slash
#print axioms geometryRow034_physicalVolume_numerator_parse
#print axioms geometryRow034_physicalVolume_denominator_parse
#print axioms geometryRow034_physicalVolume_denominator_nonzero
#print axioms geometryRow034_physicalVolume_parse
#print axioms geometryRow034_physicalVolume_read
#print axioms geometryRow034_meanGap_field
#print axioms geometryRow034_meanGap_numerator_no_slash
#print axioms geometryRow034_meanGap_numerator_parse
#print axioms geometryRow034_meanGap_denominator_parse
#print axioms geometryRow034_meanGap_denominator_nonzero
#print axioms geometryRow034_meanGap_parse
#print axioms geometryRow034_meanGap_read
#print axioms geometryRow034_jensenBound_field
#print axioms geometryRow034_jensenBound_numerator_no_slash
#print axioms geometryRow034_jensenBound_numerator_parse
#print axioms geometryRow034_jensenBound_denominator_parse
#print axioms geometryRow034_jensenBound_denominator_nonzero
#print axioms geometryRow034_jensenBound_parse
#print axioms geometryRow034_jensenBound_read
#print axioms geometryRow034_factorMaxima_read
#print axioms geometryRow034_gapWeightedMeans_read
#print axioms geometryRow034_floor_text_read
#print axioms geometryRow034_floor_chars_parse
#print axioms geometryRow034_floor_parse
#print axioms decode_geometry_Rows_034

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
