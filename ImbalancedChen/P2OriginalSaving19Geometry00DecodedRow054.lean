import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01300

/-! Original GeometryRow 54: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson054 : SourceJson :=
  (simplicesChunk054Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped054 : GeometryRow :=
  { simplexId := 54,
    vertexIds := #[27, 26, 24, 22, 21, 19, 18, 13, 3],
    physicalVolume := ((454548461623175475018690019 : ℚ) / (81372991246848000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((20250079 : ℚ) / (26904000000 : ℚ)),
    factorMaxima := #[((14640661 : ℚ) / (152000000 : ℚ)), ((3796851 : ℚ) / (38000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((8140597 : ℚ) / (114000000 : ℚ)), ((146871 : ℚ) / (4000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ)), ((1265617 : ℚ) / (38000000 : ℚ))],
    gapWeightedMeans := #[((1004637520840948181 : ℚ) / (11440970633736000000 : ℚ)), ((2540694427158852827 : ℚ) / (28602426584340000000 : ℚ)), ((1215759060657125969 : ℚ) / (9534142194780000000 : ℚ)), ((946259998352588609 : ℚ) / (9534142194780000000 : ℚ)), ((372770579726964001 : ℚ) / (4086060940620000000 : ℚ)), ((52033791224533409 : ℚ) / (794511849565000000 : ℚ)), ((233939301587256113 : ℚ) / (7150606646085000000 : ℚ)), ((227982051739217743 : ℚ) / (7150606646085000000 : ℚ)), ((19261278860181877 : ℚ) / (635609479652000000 : ℚ)), ((288918547293248503 : ℚ) / (9534142194780000000 : ℚ))],
    jensenBound := ((503224475297986964056484885262368976430793776738059150053104701589445564361485907611149234724083707223358161186786049341170617661776718037500000000000000000000 : ℚ) / (16904849655721642804896066196809803365307865446827735697462920522085218611632933012594216478774727556207837373036217573756317608325642523421716904238855042934932568158953539147 : ℚ)),
    jensenFloorQ96 := (2358468210131 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_simplexId_before"
  err.flush

theorem geometryRow054_simplexId_read :
    geometryRowsJson054.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped054.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_vertexIds_before"
  err.flush

theorem geometryRow054_vertexIds_read :
    geometryRowsJson054.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped054.vertexIds := by decide +kernel

noncomputable def geometryRow054_physicalVolumeNumeratorChars : List Char := ['4', '5', '4', '5', '4', '8', '4', '6', '1', '6', '2', '3', '1', '7', '5', '4', '7', '5', '0', '1', '8', '6', '9', '0', '0', '1', '9']
noncomputable def geometryRow054_physicalVolumeDenominatorChars : List Char := ['8', '1', '3', '7', '2', '9', '9', '1', '2', '4', '6', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_physicalVolumeText : String := String.ofList (geometryRow054_physicalVolumeNumeratorChars ++ '/' :: geometryRow054_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_physicalVolume_before_field"
  err.flush

theorem geometryRow054_physicalVolume_field :
    geometryRowsJson054.getObjVal? "physical_volume" = .ok (.str geometryRow054_physicalVolumeText) := by rfl

theorem geometryRow054_physicalVolume_numerator_no_slash :
    geometryRow054_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeNumeratorChars = some (454548461623175475018690019 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeDenominatorChars = some (81372991246848000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_nonzero : (81372991246848000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_physicalVolume_parse :
    parseRational geometryRow054_physicalVolumeText = .ok geometryRowsTyped054.physicalVolume :=
  original_rational_fraction_of_chars geometryRow054_physicalVolumeNumeratorChars geometryRow054_physicalVolumeDenominatorChars
    (454548461623175475018690019 : Int) (81372991246848000000000000000000000000000000000000000 : Int)
    geometryRow054_physicalVolume_numerator_no_slash geometryRow054_physicalVolume_numerator_parse
    geometryRow054_physicalVolume_denominator_parse geometryRow054_physicalVolume_denominator_nonzero

theorem geometryRow054_physicalVolume_read :
    rationalField geometryRowsJson054 "physical_volume" = .ok geometryRowsTyped054.physicalVolume :=
  original_rationalField_of_string geometryRowsJson054 "physical_volume" geometryRow054_physicalVolumeText
    geometryRowsTyped054.physicalVolume geometryRow054_physicalVolume_field geometryRow054_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_physicalVolume_complete"
  err.flush

noncomputable def geometryRow054_meanGapNumeratorChars : List Char := ['2', '0', '2', '5', '0', '0', '7', '9']
noncomputable def geometryRow054_meanGapDenominatorChars : List Char := ['2', '6', '9', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_meanGapText : String := String.ofList (geometryRow054_meanGapNumeratorChars ++ '/' :: geometryRow054_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_meanGap_before_field"
  err.flush

theorem geometryRow054_meanGap_field :
    geometryRowsJson054.getObjVal? "mean_gap" = .ok (.str geometryRow054_meanGapText) := by rfl

theorem geometryRow054_meanGap_numerator_no_slash :
    geometryRow054_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_meanGap_numerator_parse :
    SourceJson.intChars geometryRow054_meanGapNumeratorChars = some (20250079 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_parse :
    SourceJson.intChars geometryRow054_meanGapDenominatorChars = some (26904000000 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_nonzero : (26904000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_meanGap_parse :
    parseRational geometryRow054_meanGapText = .ok geometryRowsTyped054.meanGap :=
  original_rational_fraction_of_chars geometryRow054_meanGapNumeratorChars geometryRow054_meanGapDenominatorChars
    (20250079 : Int) (26904000000 : Int)
    geometryRow054_meanGap_numerator_no_slash geometryRow054_meanGap_numerator_parse
    geometryRow054_meanGap_denominator_parse geometryRow054_meanGap_denominator_nonzero

theorem geometryRow054_meanGap_read :
    rationalField geometryRowsJson054 "mean_gap" = .ok geometryRowsTyped054.meanGap :=
  original_rationalField_of_string geometryRowsJson054 "mean_gap" geometryRow054_meanGapText
    geometryRowsTyped054.meanGap geometryRow054_meanGap_field geometryRow054_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_meanGap_complete"
  err.flush

noncomputable def geometryRow054_jensenBoundNumeratorChars : List Char := ['5', '0', '3', '2', '2', '4', '4', '7', '5', '2', '9', '7', '9', '8', '6', '9', '6', '4', '0', '5', '6', '4', '8', '4', '8', '8', '5', '2', '6', '2', '3', '6', '8', '9', '7', '6', '4', '3', '0', '7', '9', '3', '7', '7', '6', '7', '3', '8', '0', '5', '9', '1', '5', '0', '0', '5', '3', '1', '0', '4', '7', '0', '1', '5', '8', '9', '4', '4', '5', '5', '6', '4', '3', '6', '1', '4', '8', '5', '9', '0', '7', '6', '1', '1', '1', '4', '9', '2', '3', '4', '7', '2', '4', '0', '8', '3', '7', '0', '7', '2', '2', '3', '3', '5', '8', '1', '6', '1', '1', '8', '6', '7', '8', '6', '0', '4', '9', '3', '4', '1', '1', '7', '0', '6', '1', '7', '6', '6', '1', '7', '7', '6', '7', '1', '8', '0', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_jensenBoundDenominatorChars : List Char := ['1', '6', '9', '0', '4', '8', '4', '9', '6', '5', '5', '7', '2', '1', '6', '4', '2', '8', '0', '4', '8', '9', '6', '0', '6', '6', '1', '9', '6', '8', '0', '9', '8', '0', '3', '3', '6', '5', '3', '0', '7', '8', '6', '5', '4', '4', '6', '8', '2', '7', '7', '3', '5', '6', '9', '7', '4', '6', '2', '9', '2', '0', '5', '2', '2', '0', '8', '5', '2', '1', '8', '6', '1', '1', '6', '3', '2', '9', '3', '3', '0', '1', '2', '5', '9', '4', '2', '1', '6', '4', '7', '8', '7', '7', '4', '7', '2', '7', '5', '5', '6', '2', '0', '7', '8', '3', '7', '3', '7', '3', '0', '3', '6', '2', '1', '7', '5', '7', '3', '7', '5', '6', '3', '1', '7', '6', '0', '8', '3', '2', '5', '6', '4', '2', '5', '2', '3', '4', '2', '1', '7', '1', '6', '9', '0', '4', '2', '3', '8', '8', '5', '5', '0', '4', '2', '9', '3', '4', '9', '3', '2', '5', '6', '8', '1', '5', '8', '9', '5', '3', '5', '3', '9', '1', '4', '7']
noncomputable def geometryRow054_jensenBoundText : String := String.ofList (geometryRow054_jensenBoundNumeratorChars ++ '/' :: geometryRow054_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_jensenBound_before_field"
  err.flush

theorem geometryRow054_jensenBound_field :
    geometryRowsJson054.getObjVal? "jensen_bound" = .ok (.str geometryRow054_jensenBoundText) := by rfl

theorem geometryRow054_jensenBound_numerator_no_slash :
    geometryRow054_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow054_jensenBoundNumeratorChars = some (503224475297986964056484885262368976430793776738059150053104701589445564361485907611149234724083707223358161186786049341170617661776718037500000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow054_jensenBoundDenominatorChars = some (16904849655721642804896066196809803365307865446827735697462920522085218611632933012594216478774727556207837373036217573756317608325642523421716904238855042934932568158953539147 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_nonzero : (16904849655721642804896066196809803365307865446827735697462920522085218611632933012594216478774727556207837373036217573756317608325642523421716904238855042934932568158953539147 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_jensenBound_parse :
    parseRational geometryRow054_jensenBoundText = .ok geometryRowsTyped054.jensenBound :=
  original_rational_fraction_of_chars geometryRow054_jensenBoundNumeratorChars geometryRow054_jensenBoundDenominatorChars
    (503224475297986964056484885262368976430793776738059150053104701589445564361485907611149234724083707223358161186786049341170617661776718037500000000000000000000 : Int) (16904849655721642804896066196809803365307865446827735697462920522085218611632933012594216478774727556207837373036217573756317608325642523421716904238855042934932568158953539147 : Int)
    geometryRow054_jensenBound_numerator_no_slash geometryRow054_jensenBound_numerator_parse
    geometryRow054_jensenBound_denominator_parse geometryRow054_jensenBound_denominator_nonzero

theorem geometryRow054_jensenBound_read :
    rationalField geometryRowsJson054 "jensen_bound" = .ok geometryRowsTyped054.jensenBound :=
  original_rationalField_of_string geometryRowsJson054 "jensen_bound" geometryRow054_jensenBoundText
    geometryRowsTyped054.jensenBound geometryRow054_jensenBound_field geometryRow054_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_factorMaxima_before"
  err.flush

theorem geometryRow054_factorMaxima_read :
    rationalArrayField geometryRowsJson054 "factor_maxima" = .ok geometryRowsTyped054.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_gapWeightedMeans_before"
  err.flush

theorem geometryRow054_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson054 "gap_weighted_means" = .ok geometryRowsTyped054.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow054_floorChars : List Char := ['2', '3', '5', '8', '4', '6', '8', '2', '1', '0', '1', '3', '1']
noncomputable def geometryRow054_floorText : String := String.ofList geometryRow054_floorChars

theorem geometryRow054_floor_text_read :
    geometryRowsJson054.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow054_floorText := by rfl

theorem geometryRow054_floor_chars_parse :
    SourceJson.intChars geometryRow054_floorChars = some (2358468210131 : Int) := by decide +kernel

theorem geometryRow054_floor_parse :
    parseInteger geometryRow054_floorText = .ok geometryRowsTyped054.jensenFloorQ96 := by
  simp only [geometryRow054_floorText, parseInteger, String.toList_ofList, geometryRow054_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_054 :
    decodeGeometryRow geometryRowsJson054 = .ok geometryRowsTyped054 :=
  original_geometryRow_of_fields geometryRowsJson054 geometryRowsTyped054 geometryRow054_floorText
    geometryRow054_simplexId_read geometryRow054_vertexIds_read
    geometryRow054_physicalVolume_read geometryRow054_meanGap_read
    geometryRow054_factorMaxima_read geometryRow054_gapWeightedMeans_read
    geometryRow054_jensenBound_read geometryRow054_floor_text_read geometryRow054_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_054_original_decoder_complete"
  err.flush

#print axioms geometryRow054_simplexId_read
#print axioms geometryRow054_vertexIds_read
#print axioms geometryRow054_physicalVolume_field
#print axioms geometryRow054_physicalVolume_numerator_no_slash
#print axioms geometryRow054_physicalVolume_numerator_parse
#print axioms geometryRow054_physicalVolume_denominator_parse
#print axioms geometryRow054_physicalVolume_denominator_nonzero
#print axioms geometryRow054_physicalVolume_parse
#print axioms geometryRow054_physicalVolume_read
#print axioms geometryRow054_meanGap_field
#print axioms geometryRow054_meanGap_numerator_no_slash
#print axioms geometryRow054_meanGap_numerator_parse
#print axioms geometryRow054_meanGap_denominator_parse
#print axioms geometryRow054_meanGap_denominator_nonzero
#print axioms geometryRow054_meanGap_parse
#print axioms geometryRow054_meanGap_read
#print axioms geometryRow054_jensenBound_field
#print axioms geometryRow054_jensenBound_numerator_no_slash
#print axioms geometryRow054_jensenBound_numerator_parse
#print axioms geometryRow054_jensenBound_denominator_parse
#print axioms geometryRow054_jensenBound_denominator_nonzero
#print axioms geometryRow054_jensenBound_parse
#print axioms geometryRow054_jensenBound_read
#print axioms geometryRow054_factorMaxima_read
#print axioms geometryRow054_gapWeightedMeans_read
#print axioms geometryRow054_floor_text_read
#print axioms geometryRow054_floor_chars_parse
#print axioms geometryRow054_floor_parse
#print axioms decode_geometry_Rows_054

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
