import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01300

/-! Original GeometryRow 55: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson055 : SourceJson :=
  (simplicesChunk055Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped055 : GeometryRow :=
  { simplexId := 55,
    vertexIds := #[27, 26, 14, 10, 8, 6, 5, 3, 1],
    physicalVolume := ((1164063438607380939083392581935137621771 : ℚ) / (26943481184256000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((7453129 : ℚ) / (84000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((26366 : ℚ) / (609375 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1576616249791 : ℚ) / (16400800000000 : ℚ)), ((1588414963731 : ℚ) / (16400800000000 : ℚ)), ((5990743036621 : ℚ) / (49202400000000 : ℚ)), ((738063941393 : ℚ) / (8200400000000 : ℚ)), ((3939129697979 : ℚ) / (49202400000000 : ℚ)), ((3532004562419 : ℚ) / (49202400000000 : ℚ)), ((146987228911 : ℚ) / (4100200000000 : ℚ)), ((35669040089 : ℚ) / (1025050000000 : ℚ)), ((544417785621 : ℚ) / (16400800000000 : ℚ)), ((1633250076703 : ℚ) / (49202400000000 : ℚ))],
    jensenBound := ((81426409833274744574376220696170931803836863159020877737987659166900835414709764070600000000000000000000000 : ℚ) / (950171598252873298966903209775049006753464057951370131742561245159913083018095296108841133290756196747842782673825638309223 : ℚ)),
    jensenFloorQ96 := (6789578685666 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_simplexId_before"
  err.flush

theorem geometryRow055_simplexId_read :
    geometryRowsJson055.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped055.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_vertexIds_before"
  err.flush

theorem geometryRow055_vertexIds_read :
    geometryRowsJson055.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped055.vertexIds := by decide +kernel

noncomputable def geometryRow055_physicalVolumeNumeratorChars : List Char := ['1', '1', '6', '4', '0', '6', '3', '4', '3', '8', '6', '0', '7', '3', '8', '0', '9', '3', '9', '0', '8', '3', '3', '9', '2', '5', '8', '1', '9', '3', '5', '1', '3', '7', '6', '2', '1', '7', '7', '1']
noncomputable def geometryRow055_physicalVolumeDenominatorChars : List Char := ['2', '6', '9', '4', '3', '4', '8', '1', '1', '8', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_physicalVolumeText : String := String.ofList (geometryRow055_physicalVolumeNumeratorChars ++ '/' :: geometryRow055_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_physicalVolume_before_field"
  err.flush

theorem geometryRow055_physicalVolume_field :
    geometryRowsJson055.getObjVal? "physical_volume" = .ok (.str geometryRow055_physicalVolumeText) := by rfl

theorem geometryRow055_physicalVolume_numerator_no_slash :
    geometryRow055_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeNumeratorChars = some (1164063438607380939083392581935137621771 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeDenominatorChars = some (26943481184256000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_nonzero : (26943481184256000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_physicalVolume_parse :
    parseRational geometryRow055_physicalVolumeText = .ok geometryRowsTyped055.physicalVolume :=
  original_rational_fraction_of_chars geometryRow055_physicalVolumeNumeratorChars geometryRow055_physicalVolumeDenominatorChars
    (1164063438607380939083392581935137621771 : Int) (26943481184256000000000000000000000000000000000000000000000000000 : Int)
    geometryRow055_physicalVolume_numerator_no_slash geometryRow055_physicalVolume_numerator_parse
    geometryRow055_physicalVolume_denominator_parse geometryRow055_physicalVolume_denominator_nonzero

theorem geometryRow055_physicalVolume_read :
    rationalField geometryRowsJson055 "physical_volume" = .ok geometryRowsTyped055.physicalVolume :=
  original_rationalField_of_string geometryRowsJson055 "physical_volume" geometryRow055_physicalVolumeText
    geometryRowsTyped055.physicalVolume geometryRow055_physicalVolume_field geometryRow055_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_physicalVolume_complete"
  err.flush

noncomputable def geometryRow055_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow055_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_meanGapText : String := String.ofList (geometryRow055_meanGapNumeratorChars ++ '/' :: geometryRow055_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_meanGap_before_field"
  err.flush

theorem geometryRow055_meanGap_field :
    geometryRowsJson055.getObjVal? "mean_gap" = .ok (.str geometryRow055_meanGapText) := by rfl

theorem geometryRow055_meanGap_numerator_no_slash :
    geometryRow055_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_meanGap_numerator_parse :
    SourceJson.intChars geometryRow055_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_parse :
    SourceJson.intChars geometryRow055_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_meanGap_parse :
    parseRational geometryRow055_meanGapText = .ok geometryRowsTyped055.meanGap :=
  original_rational_fraction_of_chars geometryRow055_meanGapNumeratorChars geometryRow055_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow055_meanGap_numerator_no_slash geometryRow055_meanGap_numerator_parse
    geometryRow055_meanGap_denominator_parse geometryRow055_meanGap_denominator_nonzero

theorem geometryRow055_meanGap_read :
    rationalField geometryRowsJson055 "mean_gap" = .ok geometryRowsTyped055.meanGap :=
  original_rationalField_of_string geometryRowsJson055 "mean_gap" geometryRow055_meanGapText
    geometryRowsTyped055.meanGap geometryRow055_meanGap_field geometryRow055_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_meanGap_complete"
  err.flush

noncomputable def geometryRow055_jensenBoundNumeratorChars : List Char := ['8', '1', '4', '2', '6', '4', '0', '9', '8', '3', '3', '2', '7', '4', '7', '4', '4', '5', '7', '4', '3', '7', '6', '2', '2', '0', '6', '9', '6', '1', '7', '0', '9', '3', '1', '8', '0', '3', '8', '3', '6', '8', '6', '3', '1', '5', '9', '0', '2', '0', '8', '7', '7', '7', '3', '7', '9', '8', '7', '6', '5', '9', '1', '6', '6', '9', '0', '0', '8', '3', '5', '4', '1', '4', '7', '0', '9', '7', '6', '4', '0', '7', '0', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_jensenBoundDenominatorChars : List Char := ['9', '5', '0', '1', '7', '1', '5', '9', '8', '2', '5', '2', '8', '7', '3', '2', '9', '8', '9', '6', '6', '9', '0', '3', '2', '0', '9', '7', '7', '5', '0', '4', '9', '0', '0', '6', '7', '5', '3', '4', '6', '4', '0', '5', '7', '9', '5', '1', '3', '7', '0', '1', '3', '1', '7', '4', '2', '5', '6', '1', '2', '4', '5', '1', '5', '9', '9', '1', '3', '0', '8', '3', '0', '1', '8', '0', '9', '5', '2', '9', '6', '1', '0', '8', '8', '4', '1', '1', '3', '3', '2', '9', '0', '7', '5', '6', '1', '9', '6', '7', '4', '7', '8', '4', '2', '7', '8', '2', '6', '7', '3', '8', '2', '5', '6', '3', '8', '3', '0', '9', '2', '2', '3']
noncomputable def geometryRow055_jensenBoundText : String := String.ofList (geometryRow055_jensenBoundNumeratorChars ++ '/' :: geometryRow055_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_jensenBound_before_field"
  err.flush

theorem geometryRow055_jensenBound_field :
    geometryRowsJson055.getObjVal? "jensen_bound" = .ok (.str geometryRow055_jensenBoundText) := by rfl

theorem geometryRow055_jensenBound_numerator_no_slash :
    geometryRow055_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow055_jensenBoundNumeratorChars = some (81426409833274744574376220696170931803836863159020877737987659166900835414709764070600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow055_jensenBoundDenominatorChars = some (950171598252873298966903209775049006753464057951370131742561245159913083018095296108841133290756196747842782673825638309223 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_nonzero : (950171598252873298966903209775049006753464057951370131742561245159913083018095296108841133290756196747842782673825638309223 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_jensenBound_parse :
    parseRational geometryRow055_jensenBoundText = .ok geometryRowsTyped055.jensenBound :=
  original_rational_fraction_of_chars geometryRow055_jensenBoundNumeratorChars geometryRow055_jensenBoundDenominatorChars
    (81426409833274744574376220696170931803836863159020877737987659166900835414709764070600000000000000000000000 : Int) (950171598252873298966903209775049006753464057951370131742561245159913083018095296108841133290756196747842782673825638309223 : Int)
    geometryRow055_jensenBound_numerator_no_slash geometryRow055_jensenBound_numerator_parse
    geometryRow055_jensenBound_denominator_parse geometryRow055_jensenBound_denominator_nonzero

theorem geometryRow055_jensenBound_read :
    rationalField geometryRowsJson055 "jensen_bound" = .ok geometryRowsTyped055.jensenBound :=
  original_rationalField_of_string geometryRowsJson055 "jensen_bound" geometryRow055_jensenBoundText
    geometryRowsTyped055.jensenBound geometryRow055_jensenBound_field geometryRow055_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_factorMaxima_before"
  err.flush

theorem geometryRow055_factorMaxima_read :
    rationalArrayField geometryRowsJson055 "factor_maxima" = .ok geometryRowsTyped055.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_gapWeightedMeans_before"
  err.flush

theorem geometryRow055_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson055 "gap_weighted_means" = .ok geometryRowsTyped055.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow055_floorChars : List Char := ['6', '7', '8', '9', '5', '7', '8', '6', '8', '5', '6', '6', '6']
noncomputable def geometryRow055_floorText : String := String.ofList geometryRow055_floorChars

theorem geometryRow055_floor_text_read :
    geometryRowsJson055.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow055_floorText := by rfl

theorem geometryRow055_floor_chars_parse :
    SourceJson.intChars geometryRow055_floorChars = some (6789578685666 : Int) := by decide +kernel

theorem geometryRow055_floor_parse :
    parseInteger geometryRow055_floorText = .ok geometryRowsTyped055.jensenFloorQ96 := by
  simp only [geometryRow055_floorText, parseInteger, String.toList_ofList, geometryRow055_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_055 :
    decodeGeometryRow geometryRowsJson055 = .ok geometryRowsTyped055 :=
  original_geometryRow_of_fields geometryRowsJson055 geometryRowsTyped055 geometryRow055_floorText
    geometryRow055_simplexId_read geometryRow055_vertexIds_read
    geometryRow055_physicalVolume_read geometryRow055_meanGap_read
    geometryRow055_factorMaxima_read geometryRow055_gapWeightedMeans_read
    geometryRow055_jensenBound_read geometryRow055_floor_text_read geometryRow055_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_055_original_decoder_complete"
  err.flush

#print axioms geometryRow055_simplexId_read
#print axioms geometryRow055_vertexIds_read
#print axioms geometryRow055_physicalVolume_field
#print axioms geometryRow055_physicalVolume_numerator_no_slash
#print axioms geometryRow055_physicalVolume_numerator_parse
#print axioms geometryRow055_physicalVolume_denominator_parse
#print axioms geometryRow055_physicalVolume_denominator_nonzero
#print axioms geometryRow055_physicalVolume_parse
#print axioms geometryRow055_physicalVolume_read
#print axioms geometryRow055_meanGap_field
#print axioms geometryRow055_meanGap_numerator_no_slash
#print axioms geometryRow055_meanGap_numerator_parse
#print axioms geometryRow055_meanGap_denominator_parse
#print axioms geometryRow055_meanGap_denominator_nonzero
#print axioms geometryRow055_meanGap_parse
#print axioms geometryRow055_meanGap_read
#print axioms geometryRow055_jensenBound_field
#print axioms geometryRow055_jensenBound_numerator_no_slash
#print axioms geometryRow055_jensenBound_numerator_parse
#print axioms geometryRow055_jensenBound_denominator_parse
#print axioms geometryRow055_jensenBound_denominator_nonzero
#print axioms geometryRow055_jensenBound_parse
#print axioms geometryRow055_jensenBound_read
#print axioms geometryRow055_factorMaxima_read
#print axioms geometryRow055_gapWeightedMeans_read
#print axioms geometryRow055_floor_text_read
#print axioms geometryRow055_floor_chars_parse
#print axioms geometryRow055_floor_parse
#print axioms decode_geometry_Rows_055

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
