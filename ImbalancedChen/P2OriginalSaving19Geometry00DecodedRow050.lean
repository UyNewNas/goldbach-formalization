import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200

/-! Original GeometryRow 50: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson050 : SourceJson :=
  (simplicesChunk050Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped050 : GeometryRow :=
  { simplexId := 50,
    vertexIds := #[27, 26, 24, 22, 8, 6, 5, 3, 1],
    physicalVolume := ((1471551338178443020753176080564013487 : ℚ) / (49838963392512000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1046328506213 : ℚ) / (11354400000000 : ℚ)), ((1054496846633 : ℚ) / (11354400000000 : ℚ)), ((1399308935411 : ℚ) / (11354400000000 : ℚ)), ((261484978577 : ℚ) / (2838600000000 : ℚ)), ((961380434749 : ℚ) / (11354400000000 : ℚ)), ((798248202829 : ℚ) / (11354400000000 : ℚ)), ((198693618491 : ℚ) / (5677200000000 : ℚ)), ((64654626697 : ℚ) / (1892400000000 : ℚ)), ((123243055901 : ℚ) / (3784800000000 : ℚ)), ((41080934527 : ℚ) / (1261600000000 : ℚ))],
    jensenBound := ((5778349861343523453797849836987181844376329225966197125920033828019431321600000000000000000000000000 : ℚ) / (89762847197388492386764877035140134799217719427142278631606027019271678325716074434215915801796458046388350598868853 : ℚ)),
    jensenFloorQ96 := (5100195194032 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_simplexId_before"
  err.flush

theorem geometryRow050_simplexId_read :
    geometryRowsJson050.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped050.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_vertexIds_before"
  err.flush

theorem geometryRow050_vertexIds_read :
    geometryRowsJson050.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped050.vertexIds := by decide +kernel

noncomputable def geometryRow050_physicalVolumeNumeratorChars : List Char := ['1', '4', '7', '1', '5', '5', '1', '3', '3', '8', '1', '7', '8', '4', '4', '3', '0', '2', '0', '7', '5', '3', '1', '7', '6', '0', '8', '0', '5', '6', '4', '0', '1', '3', '4', '8', '7']
noncomputable def geometryRow050_physicalVolumeDenominatorChars : List Char := ['4', '9', '8', '3', '8', '9', '6', '3', '3', '9', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_physicalVolumeText : String := String.ofList (geometryRow050_physicalVolumeNumeratorChars ++ '/' :: geometryRow050_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_physicalVolume_before_field"
  err.flush

theorem geometryRow050_physicalVolume_field :
    geometryRowsJson050.getObjVal? "physical_volume" = .ok (.str geometryRow050_physicalVolumeText) := by rfl

theorem geometryRow050_physicalVolume_numerator_no_slash :
    geometryRow050_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeNumeratorChars = some (1471551338178443020753176080564013487 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeDenominatorChars = some (49838963392512000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_nonzero : (49838963392512000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_physicalVolume_parse :
    parseRational geometryRow050_physicalVolumeText = .ok geometryRowsTyped050.physicalVolume :=
  original_rational_fraction_of_chars geometryRow050_physicalVolumeNumeratorChars geometryRow050_physicalVolumeDenominatorChars
    (1471551338178443020753176080564013487 : Int) (49838963392512000000000000000000000000000000000000000000000000 : Int)
    geometryRow050_physicalVolume_numerator_no_slash geometryRow050_physicalVolume_numerator_parse
    geometryRow050_physicalVolume_denominator_parse geometryRow050_physicalVolume_denominator_nonzero

theorem geometryRow050_physicalVolume_read :
    rationalField geometryRowsJson050 "physical_volume" = .ok geometryRowsTyped050.physicalVolume :=
  original_rationalField_of_string geometryRowsJson050 "physical_volume" geometryRow050_physicalVolumeText
    geometryRowsTyped050.physicalVolume geometryRow050_physicalVolume_field geometryRow050_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_physicalVolume_complete"
  err.flush

noncomputable def geometryRow050_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow050_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_meanGapText : String := String.ofList (geometryRow050_meanGapNumeratorChars ++ '/' :: geometryRow050_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_meanGap_before_field"
  err.flush

theorem geometryRow050_meanGap_field :
    geometryRowsJson050.getObjVal? "mean_gap" = .ok (.str geometryRow050_meanGapText) := by rfl

theorem geometryRow050_meanGap_numerator_no_slash :
    geometryRow050_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_meanGap_numerator_parse :
    SourceJson.intChars geometryRow050_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_parse :
    SourceJson.intChars geometryRow050_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_meanGap_parse :
    parseRational geometryRow050_meanGapText = .ok geometryRowsTyped050.meanGap :=
  original_rational_fraction_of_chars geometryRow050_meanGapNumeratorChars geometryRow050_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow050_meanGap_numerator_no_slash geometryRow050_meanGap_numerator_parse
    geometryRow050_meanGap_denominator_parse geometryRow050_meanGap_denominator_nonzero

theorem geometryRow050_meanGap_read :
    rationalField geometryRowsJson050 "mean_gap" = .ok geometryRowsTyped050.meanGap :=
  original_rationalField_of_string geometryRowsJson050 "mean_gap" geometryRow050_meanGapText
    geometryRowsTyped050.meanGap geometryRow050_meanGap_field geometryRow050_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_meanGap_complete"
  err.flush

noncomputable def geometryRow050_jensenBoundNumeratorChars : List Char := ['5', '7', '7', '8', '3', '4', '9', '8', '6', '1', '3', '4', '3', '5', '2', '3', '4', '5', '3', '7', '9', '7', '8', '4', '9', '8', '3', '6', '9', '8', '7', '1', '8', '1', '8', '4', '4', '3', '7', '6', '3', '2', '9', '2', '2', '5', '9', '6', '6', '1', '9', '7', '1', '2', '5', '9', '2', '0', '0', '3', '3', '8', '2', '8', '0', '1', '9', '4', '3', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_jensenBoundDenominatorChars : List Char := ['8', '9', '7', '6', '2', '8', '4', '7', '1', '9', '7', '3', '8', '8', '4', '9', '2', '3', '8', '6', '7', '6', '4', '8', '7', '7', '0', '3', '5', '1', '4', '0', '1', '3', '4', '7', '9', '9', '2', '1', '7', '7', '1', '9', '4', '2', '7', '1', '4', '2', '2', '7', '8', '6', '3', '1', '6', '0', '6', '0', '2', '7', '0', '1', '9', '2', '7', '1', '6', '7', '8', '3', '2', '5', '7', '1', '6', '0', '7', '4', '4', '3', '4', '2', '1', '5', '9', '1', '5', '8', '0', '1', '7', '9', '6', '4', '5', '8', '0', '4', '6', '3', '8', '8', '3', '5', '0', '5', '9', '8', '8', '6', '8', '8', '5', '3']
noncomputable def geometryRow050_jensenBoundText : String := String.ofList (geometryRow050_jensenBoundNumeratorChars ++ '/' :: geometryRow050_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_jensenBound_before_field"
  err.flush

theorem geometryRow050_jensenBound_field :
    geometryRowsJson050.getObjVal? "jensen_bound" = .ok (.str geometryRow050_jensenBoundText) := by rfl

theorem geometryRow050_jensenBound_numerator_no_slash :
    geometryRow050_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow050_jensenBoundNumeratorChars = some (5778349861343523453797849836987181844376329225966197125920033828019431321600000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow050_jensenBoundDenominatorChars = some (89762847197388492386764877035140134799217719427142278631606027019271678325716074434215915801796458046388350598868853 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_nonzero : (89762847197388492386764877035140134799217719427142278631606027019271678325716074434215915801796458046388350598868853 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_jensenBound_parse :
    parseRational geometryRow050_jensenBoundText = .ok geometryRowsTyped050.jensenBound :=
  original_rational_fraction_of_chars geometryRow050_jensenBoundNumeratorChars geometryRow050_jensenBoundDenominatorChars
    (5778349861343523453797849836987181844376329225966197125920033828019431321600000000000000000000000000 : Int) (89762847197388492386764877035140134799217719427142278631606027019271678325716074434215915801796458046388350598868853 : Int)
    geometryRow050_jensenBound_numerator_no_slash geometryRow050_jensenBound_numerator_parse
    geometryRow050_jensenBound_denominator_parse geometryRow050_jensenBound_denominator_nonzero

theorem geometryRow050_jensenBound_read :
    rationalField geometryRowsJson050 "jensen_bound" = .ok geometryRowsTyped050.jensenBound :=
  original_rationalField_of_string geometryRowsJson050 "jensen_bound" geometryRow050_jensenBoundText
    geometryRowsTyped050.jensenBound geometryRow050_jensenBound_field geometryRow050_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_factorMaxima_before"
  err.flush

theorem geometryRow050_factorMaxima_read :
    rationalArrayField geometryRowsJson050 "factor_maxima" = .ok geometryRowsTyped050.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_gapWeightedMeans_before"
  err.flush

theorem geometryRow050_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson050 "gap_weighted_means" = .ok geometryRowsTyped050.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow050_floorChars : List Char := ['5', '1', '0', '0', '1', '9', '5', '1', '9', '4', '0', '3', '2']
noncomputable def geometryRow050_floorText : String := String.ofList geometryRow050_floorChars

theorem geometryRow050_floor_text_read :
    geometryRowsJson050.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow050_floorText := by rfl

theorem geometryRow050_floor_chars_parse :
    SourceJson.intChars geometryRow050_floorChars = some (5100195194032 : Int) := by decide +kernel

theorem geometryRow050_floor_parse :
    parseInteger geometryRow050_floorText = .ok geometryRowsTyped050.jensenFloorQ96 := by
  simp only [geometryRow050_floorText, parseInteger, String.toList_ofList, geometryRow050_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_050 :
    decodeGeometryRow geometryRowsJson050 = .ok geometryRowsTyped050 :=
  original_geometryRow_of_fields geometryRowsJson050 geometryRowsTyped050 geometryRow050_floorText
    geometryRow050_simplexId_read geometryRow050_vertexIds_read
    geometryRow050_physicalVolume_read geometryRow050_meanGap_read
    geometryRow050_factorMaxima_read geometryRow050_gapWeightedMeans_read
    geometryRow050_jensenBound_read geometryRow050_floor_text_read geometryRow050_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_050_original_decoder_complete"
  err.flush

#print axioms geometryRow050_simplexId_read
#print axioms geometryRow050_vertexIds_read
#print axioms geometryRow050_physicalVolume_field
#print axioms geometryRow050_physicalVolume_numerator_no_slash
#print axioms geometryRow050_physicalVolume_numerator_parse
#print axioms geometryRow050_physicalVolume_denominator_parse
#print axioms geometryRow050_physicalVolume_denominator_nonzero
#print axioms geometryRow050_physicalVolume_parse
#print axioms geometryRow050_physicalVolume_read
#print axioms geometryRow050_meanGap_field
#print axioms geometryRow050_meanGap_numerator_no_slash
#print axioms geometryRow050_meanGap_numerator_parse
#print axioms geometryRow050_meanGap_denominator_parse
#print axioms geometryRow050_meanGap_denominator_nonzero
#print axioms geometryRow050_meanGap_parse
#print axioms geometryRow050_meanGap_read
#print axioms geometryRow050_jensenBound_field
#print axioms geometryRow050_jensenBound_numerator_no_slash
#print axioms geometryRow050_jensenBound_numerator_parse
#print axioms geometryRow050_jensenBound_denominator_parse
#print axioms geometryRow050_jensenBound_denominator_nonzero
#print axioms geometryRow050_jensenBound_parse
#print axioms geometryRow050_jensenBound_read
#print axioms geometryRow050_factorMaxima_read
#print axioms geometryRow050_gapWeightedMeans_read
#print axioms geometryRow050_floor_text_read
#print axioms geometryRow050_floor_chars_parse
#print axioms geometryRow050_floor_parse
#print axioms decode_geometry_Rows_050

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
