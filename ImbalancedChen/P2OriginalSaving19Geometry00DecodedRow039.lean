import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900

/-! Original GeometryRow 39: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson039 : SourceJson :=
  (simplicesChunk039Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped039 : GeometryRow :=
  { simplexId := 39,
    vertexIds := #[27, 25, 24, 22, 21, 19, 5, 3, 1],
    physicalVolume := ((1435267245588210338991547529113 : ℚ) / (102208811644800000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((3588091352989 : ℚ) / (39740400000000 : ℚ)), ((3616680544459 : ℚ) / (39740400000000 : ℚ)), ((661117977371 : ℚ) / (5298720000000 : ℚ)), ((7564984743739 : ℚ) / (79480800000000 : ℚ)), ((7031498547131 : ℚ) / (79480800000000 : ℚ)), ((51855680803 : ℚ) / (756960000000 : ℚ)), ((195955315691 : ℚ) / (5677200000000 : ℚ)), ((186495687499 : ℚ) / (5677200000000 : ℚ)), ((1233155620873 : ℚ) / (39740400000000 : ℚ)), ((1233150322153 : ℚ) / (39740400000000 : ℚ))],
    jensenBound := ((45726424729841397642291018677275777003546779601716566471623241810399754977280000000000000000000000000000 : ℚ) / (1315117773091549437726281848063937807976220572985131750990707488226420765038285527957372892827119878454031759244775972207 : ℚ)),
    jensenFloorQ96 := (2754749942414 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_simplexId_before"
  err.flush

theorem geometryRow039_simplexId_read :
    geometryRowsJson039.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped039.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_vertexIds_before"
  err.flush

theorem geometryRow039_vertexIds_read :
    geometryRowsJson039.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped039.vertexIds := by decide +kernel

noncomputable def geometryRow039_physicalVolumeNumeratorChars : List Char := ['1', '4', '3', '5', '2', '6', '7', '2', '4', '5', '5', '8', '8', '2', '1', '0', '3', '3', '8', '9', '9', '1', '5', '4', '7', '5', '2', '9', '1', '1', '3']
noncomputable def geometryRow039_physicalVolumeDenominatorChars : List Char := ['1', '0', '2', '2', '0', '8', '8', '1', '1', '6', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_physicalVolumeText : String := String.ofList (geometryRow039_physicalVolumeNumeratorChars ++ '/' :: geometryRow039_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_physicalVolume_before_field"
  err.flush

theorem geometryRow039_physicalVolume_field :
    geometryRowsJson039.getObjVal? "physical_volume" = .ok (.str geometryRow039_physicalVolumeText) := by rfl

theorem geometryRow039_physicalVolume_numerator_no_slash :
    geometryRow039_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeNumeratorChars = some (1435267245588210338991547529113 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeDenominatorChars = some (102208811644800000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_nonzero : (102208811644800000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_physicalVolume_parse :
    parseRational geometryRow039_physicalVolumeText = .ok geometryRowsTyped039.physicalVolume :=
  original_rational_fraction_of_chars geometryRow039_physicalVolumeNumeratorChars geometryRow039_physicalVolumeDenominatorChars
    (1435267245588210338991547529113 : Int) (102208811644800000000000000000000000000000000000000000000 : Int)
    geometryRow039_physicalVolume_numerator_no_slash geometryRow039_physicalVolume_numerator_parse
    geometryRow039_physicalVolume_denominator_parse geometryRow039_physicalVolume_denominator_nonzero

theorem geometryRow039_physicalVolume_read :
    rationalField geometryRowsJson039 "physical_volume" = .ok geometryRowsTyped039.physicalVolume :=
  original_rationalField_of_string geometryRowsJson039 "physical_volume" geometryRow039_physicalVolumeText
    geometryRowsTyped039.physicalVolume geometryRow039_physicalVolume_field geometryRow039_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_physicalVolume_complete"
  err.flush

noncomputable def geometryRow039_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow039_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_meanGapText : String := String.ofList (geometryRow039_meanGapNumeratorChars ++ '/' :: geometryRow039_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_meanGap_before_field"
  err.flush

theorem geometryRow039_meanGap_field :
    geometryRowsJson039.getObjVal? "mean_gap" = .ok (.str geometryRow039_meanGapText) := by rfl

theorem geometryRow039_meanGap_numerator_no_slash :
    geometryRow039_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_meanGap_numerator_parse :
    SourceJson.intChars geometryRow039_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_parse :
    SourceJson.intChars geometryRow039_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_meanGap_parse :
    parseRational geometryRow039_meanGapText = .ok geometryRowsTyped039.meanGap :=
  original_rational_fraction_of_chars geometryRow039_meanGapNumeratorChars geometryRow039_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow039_meanGap_numerator_no_slash geometryRow039_meanGap_numerator_parse
    geometryRow039_meanGap_denominator_parse geometryRow039_meanGap_denominator_nonzero

theorem geometryRow039_meanGap_read :
    rationalField geometryRowsJson039 "mean_gap" = .ok geometryRowsTyped039.meanGap :=
  original_rationalField_of_string geometryRowsJson039 "mean_gap" geometryRow039_meanGapText
    geometryRowsTyped039.meanGap geometryRow039_meanGap_field geometryRow039_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_meanGap_complete"
  err.flush

noncomputable def geometryRow039_jensenBoundNumeratorChars : List Char := ['4', '5', '7', '2', '6', '4', '2', '4', '7', '2', '9', '8', '4', '1', '3', '9', '7', '6', '4', '2', '2', '9', '1', '0', '1', '8', '6', '7', '7', '2', '7', '5', '7', '7', '7', '0', '0', '3', '5', '4', '6', '7', '7', '9', '6', '0', '1', '7', '1', '6', '5', '6', '6', '4', '7', '1', '6', '2', '3', '2', '4', '1', '8', '1', '0', '3', '9', '9', '7', '5', '4', '9', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_jensenBoundDenominatorChars : List Char := ['1', '3', '1', '5', '1', '1', '7', '7', '7', '3', '0', '9', '1', '5', '4', '9', '4', '3', '7', '7', '2', '6', '2', '8', '1', '8', '4', '8', '0', '6', '3', '9', '3', '7', '8', '0', '7', '9', '7', '6', '2', '2', '0', '5', '7', '2', '9', '8', '5', '1', '3', '1', '7', '5', '0', '9', '9', '0', '7', '0', '7', '4', '8', '8', '2', '2', '6', '4', '2', '0', '7', '6', '5', '0', '3', '8', '2', '8', '5', '5', '2', '7', '9', '5', '7', '3', '7', '2', '8', '9', '2', '8', '2', '7', '1', '1', '9', '8', '7', '8', '4', '5', '4', '0', '3', '1', '7', '5', '9', '2', '4', '4', '7', '7', '5', '9', '7', '2', '2', '0', '7']
noncomputable def geometryRow039_jensenBoundText : String := String.ofList (geometryRow039_jensenBoundNumeratorChars ++ '/' :: geometryRow039_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_jensenBound_before_field"
  err.flush

theorem geometryRow039_jensenBound_field :
    geometryRowsJson039.getObjVal? "jensen_bound" = .ok (.str geometryRow039_jensenBoundText) := by rfl

theorem geometryRow039_jensenBound_numerator_no_slash :
    geometryRow039_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow039_jensenBoundNumeratorChars = some (45726424729841397642291018677275777003546779601716566471623241810399754977280000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow039_jensenBoundDenominatorChars = some (1315117773091549437726281848063937807976220572985131750990707488226420765038285527957372892827119878454031759244775972207 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_nonzero : (1315117773091549437726281848063937807976220572985131750990707488226420765038285527957372892827119878454031759244775972207 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_jensenBound_parse :
    parseRational geometryRow039_jensenBoundText = .ok geometryRowsTyped039.jensenBound :=
  original_rational_fraction_of_chars geometryRow039_jensenBoundNumeratorChars geometryRow039_jensenBoundDenominatorChars
    (45726424729841397642291018677275777003546779601716566471623241810399754977280000000000000000000000000000 : Int) (1315117773091549437726281848063937807976220572985131750990707488226420765038285527957372892827119878454031759244775972207 : Int)
    geometryRow039_jensenBound_numerator_no_slash geometryRow039_jensenBound_numerator_parse
    geometryRow039_jensenBound_denominator_parse geometryRow039_jensenBound_denominator_nonzero

theorem geometryRow039_jensenBound_read :
    rationalField geometryRowsJson039 "jensen_bound" = .ok geometryRowsTyped039.jensenBound :=
  original_rationalField_of_string geometryRowsJson039 "jensen_bound" geometryRow039_jensenBoundText
    geometryRowsTyped039.jensenBound geometryRow039_jensenBound_field geometryRow039_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_factorMaxima_before"
  err.flush

theorem geometryRow039_factorMaxima_read :
    rationalArrayField geometryRowsJson039 "factor_maxima" = .ok geometryRowsTyped039.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_gapWeightedMeans_before"
  err.flush

theorem geometryRow039_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson039 "gap_weighted_means" = .ok geometryRowsTyped039.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow039_floorChars : List Char := ['2', '7', '5', '4', '7', '4', '9', '9', '4', '2', '4', '1', '4']
noncomputable def geometryRow039_floorText : String := String.ofList geometryRow039_floorChars

theorem geometryRow039_floor_text_read :
    geometryRowsJson039.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow039_floorText := by rfl

theorem geometryRow039_floor_chars_parse :
    SourceJson.intChars geometryRow039_floorChars = some (2754749942414 : Int) := by decide +kernel

theorem geometryRow039_floor_parse :
    parseInteger geometryRow039_floorText = .ok geometryRowsTyped039.jensenFloorQ96 := by
  simp only [geometryRow039_floorText, parseInteger, String.toList_ofList, geometryRow039_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_039 :
    decodeGeometryRow geometryRowsJson039 = .ok geometryRowsTyped039 :=
  original_geometryRow_of_fields geometryRowsJson039 geometryRowsTyped039 geometryRow039_floorText
    geometryRow039_simplexId_read geometryRow039_vertexIds_read
    geometryRow039_physicalVolume_read geometryRow039_meanGap_read
    geometryRow039_factorMaxima_read geometryRow039_gapWeightedMeans_read
    geometryRow039_jensenBound_read geometryRow039_floor_text_read geometryRow039_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_039_original_decoder_complete"
  err.flush

#print axioms geometryRow039_simplexId_read
#print axioms geometryRow039_vertexIds_read
#print axioms geometryRow039_physicalVolume_field
#print axioms geometryRow039_physicalVolume_numerator_no_slash
#print axioms geometryRow039_physicalVolume_numerator_parse
#print axioms geometryRow039_physicalVolume_denominator_parse
#print axioms geometryRow039_physicalVolume_denominator_nonzero
#print axioms geometryRow039_physicalVolume_parse
#print axioms geometryRow039_physicalVolume_read
#print axioms geometryRow039_meanGap_field
#print axioms geometryRow039_meanGap_numerator_no_slash
#print axioms geometryRow039_meanGap_numerator_parse
#print axioms geometryRow039_meanGap_denominator_parse
#print axioms geometryRow039_meanGap_denominator_nonzero
#print axioms geometryRow039_meanGap_parse
#print axioms geometryRow039_meanGap_read
#print axioms geometryRow039_jensenBound_field
#print axioms geometryRow039_jensenBound_numerator_no_slash
#print axioms geometryRow039_jensenBound_numerator_parse
#print axioms geometryRow039_jensenBound_denominator_parse
#print axioms geometryRow039_jensenBound_denominator_nonzero
#print axioms geometryRow039_jensenBound_parse
#print axioms geometryRow039_jensenBound_read
#print axioms geometryRow039_factorMaxima_read
#print axioms geometryRow039_gapWeightedMeans_read
#print axioms geometryRow039_floor_text_read
#print axioms geometryRow039_floor_chars_parse
#print axioms geometryRow039_floor_parse
#print axioms decode_geometry_Rows_039

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
