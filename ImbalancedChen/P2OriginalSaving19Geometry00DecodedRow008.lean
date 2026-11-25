import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200

/-! Original GeometryRow 8: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson008 : SourceJson :=
  (simplicesChunk008Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped008 : GeometryRow :=
  { simplexId := 8,
    vertexIds := #[27, 25, 23, 9, 7, 5, 4, 2, 0],
    physicalVolume := ((258368222942787083488728524299833318605983 : ℚ) / (762655035870000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1043299145444233 : ℚ) / (11365754400000000 : ℚ)), ((526131037771139 : ℚ) / (5682877200000000 : ℚ)), ((459581893025207 : ℚ) / (3788584800000000 : ℚ)), ((8783692727589 : ℚ) / (97143200000000 : ℚ)), ((317568327993919 : ℚ) / (3788584800000000 : ℚ)), ((271658716998283 : ℚ) / (3788584800000000 : ℚ)), ((5635409276197 : ℚ) / (157857700000000 : ℚ)), ((1981401142613 : ℚ) / (56828772000000 : ℚ)), ((9782204708737 : ℚ) / (284143860000000 : ℚ)), ((61500370275433 : ℚ) / (1894292400000000 : ℚ))],
    jensenBound := ((52087714996429292718005073626505062416122627818330114040068309009112548571611812895215746974107868326789120000000000000000000 : ℚ) / (68386724103082569960655110036156663950892222838108627842436427017303963996417944811920978359961292749047370401180151206822041194930249957 : ℚ)),
    jensenFloorQ96 := (60345249796045797 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_simplexId_before"
  err.flush

theorem geometryRow008_simplexId_read :
    geometryRowsJson008.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped008.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_vertexIds_before"
  err.flush

theorem geometryRow008_vertexIds_read :
    geometryRowsJson008.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped008.vertexIds := by decide +kernel

noncomputable def geometryRow008_physicalVolumeNumeratorChars : List Char := ['2', '5', '8', '3', '6', '8', '2', '2', '2', '9', '4', '2', '7', '8', '7', '0', '8', '3', '4', '8', '8', '7', '2', '8', '5', '2', '4', '2', '9', '9', '8', '3', '3', '3', '1', '8', '6', '0', '5', '9', '8', '3']
noncomputable def geometryRow008_physicalVolumeDenominatorChars : List Char := ['7', '6', '2', '6', '5', '5', '0', '3', '5', '8', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_physicalVolumeText : String := String.ofList (geometryRow008_physicalVolumeNumeratorChars ++ '/' :: geometryRow008_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_physicalVolume_before_field"
  err.flush

theorem geometryRow008_physicalVolume_field :
    geometryRowsJson008.getObjVal? "physical_volume" = .ok (.str geometryRow008_physicalVolumeText) := by rfl

theorem geometryRow008_physicalVolume_numerator_no_slash :
    geometryRow008_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeNumeratorChars = some (258368222942787083488728524299833318605983 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeDenominatorChars = some (762655035870000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_nonzero : (762655035870000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_physicalVolume_parse :
    parseRational geometryRow008_physicalVolumeText = .ok geometryRowsTyped008.physicalVolume :=
  original_rational_fraction_of_chars geometryRow008_physicalVolumeNumeratorChars geometryRow008_physicalVolumeDenominatorChars
    (258368222942787083488728524299833318605983 : Int) (762655035870000000000000000000000000000000000000000000000000000 : Int)
    geometryRow008_physicalVolume_numerator_no_slash geometryRow008_physicalVolume_numerator_parse
    geometryRow008_physicalVolume_denominator_parse geometryRow008_physicalVolume_denominator_nonzero

theorem geometryRow008_physicalVolume_read :
    rationalField geometryRowsJson008 "physical_volume" = .ok geometryRowsTyped008.physicalVolume :=
  original_rationalField_of_string geometryRowsJson008 "physical_volume" geometryRow008_physicalVolumeText
    geometryRowsTyped008.physicalVolume geometryRow008_physicalVolume_field geometryRow008_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_physicalVolume_complete"
  err.flush

noncomputable def geometryRow008_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow008_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_meanGapText : String := String.ofList (geometryRow008_meanGapNumeratorChars ++ '/' :: geometryRow008_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_meanGap_before_field"
  err.flush

theorem geometryRow008_meanGap_field :
    geometryRowsJson008.getObjVal? "mean_gap" = .ok (.str geometryRow008_meanGapText) := by rfl

theorem geometryRow008_meanGap_numerator_no_slash :
    geometryRow008_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_meanGap_numerator_parse :
    SourceJson.intChars geometryRow008_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_parse :
    SourceJson.intChars geometryRow008_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_meanGap_parse :
    parseRational geometryRow008_meanGapText = .ok geometryRowsTyped008.meanGap :=
  original_rational_fraction_of_chars geometryRow008_meanGapNumeratorChars geometryRow008_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow008_meanGap_numerator_no_slash geometryRow008_meanGap_numerator_parse
    geometryRow008_meanGap_denominator_parse geometryRow008_meanGap_denominator_nonzero

theorem geometryRow008_meanGap_read :
    rationalField geometryRowsJson008 "mean_gap" = .ok geometryRowsTyped008.meanGap :=
  original_rationalField_of_string geometryRowsJson008 "mean_gap" geometryRow008_meanGapText
    geometryRowsTyped008.meanGap geometryRow008_meanGap_field geometryRow008_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_meanGap_complete"
  err.flush

noncomputable def geometryRow008_jensenBoundNumeratorChars : List Char := ['5', '2', '0', '8', '7', '7', '1', '4', '9', '9', '6', '4', '2', '9', '2', '9', '2', '7', '1', '8', '0', '0', '5', '0', '7', '3', '6', '2', '6', '5', '0', '5', '0', '6', '2', '4', '1', '6', '1', '2', '2', '6', '2', '7', '8', '1', '8', '3', '3', '0', '1', '1', '4', '0', '4', '0', '0', '6', '8', '3', '0', '9', '0', '0', '9', '1', '1', '2', '5', '4', '8', '5', '7', '1', '6', '1', '1', '8', '1', '2', '8', '9', '5', '2', '1', '5', '7', '4', '6', '9', '7', '4', '1', '0', '7', '8', '6', '8', '3', '2', '6', '7', '8', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_jensenBoundDenominatorChars : List Char := ['6', '8', '3', '8', '6', '7', '2', '4', '1', '0', '3', '0', '8', '2', '5', '6', '9', '9', '6', '0', '6', '5', '5', '1', '1', '0', '0', '3', '6', '1', '5', '6', '6', '6', '3', '9', '5', '0', '8', '9', '2', '2', '2', '2', '8', '3', '8', '1', '0', '8', '6', '2', '7', '8', '4', '2', '4', '3', '6', '4', '2', '7', '0', '1', '7', '3', '0', '3', '9', '6', '3', '9', '9', '6', '4', '1', '7', '9', '4', '4', '8', '1', '1', '9', '2', '0', '9', '7', '8', '3', '5', '9', '9', '6', '1', '2', '9', '2', '7', '4', '9', '0', '4', '7', '3', '7', '0', '4', '0', '1', '1', '8', '0', '1', '5', '1', '2', '0', '6', '8', '2', '2', '0', '4', '1', '1', '9', '4', '9', '3', '0', '2', '4', '9', '9', '5', '7']
noncomputable def geometryRow008_jensenBoundText : String := String.ofList (geometryRow008_jensenBoundNumeratorChars ++ '/' :: geometryRow008_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_jensenBound_before_field"
  err.flush

theorem geometryRow008_jensenBound_field :
    geometryRowsJson008.getObjVal? "jensen_bound" = .ok (.str geometryRow008_jensenBoundText) := by rfl

theorem geometryRow008_jensenBound_numerator_no_slash :
    geometryRow008_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow008_jensenBoundNumeratorChars = some (52087714996429292718005073626505062416122627818330114040068309009112548571611812895215746974107868326789120000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow008_jensenBoundDenominatorChars = some (68386724103082569960655110036156663950892222838108627842436427017303963996417944811920978359961292749047370401180151206822041194930249957 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_nonzero : (68386724103082569960655110036156663950892222838108627842436427017303963996417944811920978359961292749047370401180151206822041194930249957 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_jensenBound_parse :
    parseRational geometryRow008_jensenBoundText = .ok geometryRowsTyped008.jensenBound :=
  original_rational_fraction_of_chars geometryRow008_jensenBoundNumeratorChars geometryRow008_jensenBoundDenominatorChars
    (52087714996429292718005073626505062416122627818330114040068309009112548571611812895215746974107868326789120000000000000000000 : Int) (68386724103082569960655110036156663950892222838108627842436427017303963996417944811920978359961292749047370401180151206822041194930249957 : Int)
    geometryRow008_jensenBound_numerator_no_slash geometryRow008_jensenBound_numerator_parse
    geometryRow008_jensenBound_denominator_parse geometryRow008_jensenBound_denominator_nonzero

theorem geometryRow008_jensenBound_read :
    rationalField geometryRowsJson008 "jensen_bound" = .ok geometryRowsTyped008.jensenBound :=
  original_rationalField_of_string geometryRowsJson008 "jensen_bound" geometryRow008_jensenBoundText
    geometryRowsTyped008.jensenBound geometryRow008_jensenBound_field geometryRow008_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_factorMaxima_before"
  err.flush

theorem geometryRow008_factorMaxima_read :
    rationalArrayField geometryRowsJson008 "factor_maxima" = .ok geometryRowsTyped008.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_gapWeightedMeans_before"
  err.flush

theorem geometryRow008_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson008 "gap_weighted_means" = .ok geometryRowsTyped008.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow008_floorChars : List Char := ['6', '0', '3', '4', '5', '2', '4', '9', '7', '9', '6', '0', '4', '5', '7', '9', '7']
noncomputable def geometryRow008_floorText : String := String.ofList geometryRow008_floorChars

theorem geometryRow008_floor_text_read :
    geometryRowsJson008.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow008_floorText := by rfl

theorem geometryRow008_floor_chars_parse :
    SourceJson.intChars geometryRow008_floorChars = some (60345249796045797 : Int) := by decide +kernel

theorem geometryRow008_floor_parse :
    parseInteger geometryRow008_floorText = .ok geometryRowsTyped008.jensenFloorQ96 := by
  simp only [geometryRow008_floorText, parseInteger, String.toList_ofList, geometryRow008_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_008 :
    decodeGeometryRow geometryRowsJson008 = .ok geometryRowsTyped008 :=
  original_geometryRow_of_fields geometryRowsJson008 geometryRowsTyped008 geometryRow008_floorText
    geometryRow008_simplexId_read geometryRow008_vertexIds_read
    geometryRow008_physicalVolume_read geometryRow008_meanGap_read
    geometryRow008_factorMaxima_read geometryRow008_gapWeightedMeans_read
    geometryRow008_jensenBound_read geometryRow008_floor_text_read geometryRow008_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_008_original_decoder_complete"
  err.flush

#print axioms geometryRow008_simplexId_read
#print axioms geometryRow008_vertexIds_read
#print axioms geometryRow008_physicalVolume_field
#print axioms geometryRow008_physicalVolume_numerator_no_slash
#print axioms geometryRow008_physicalVolume_numerator_parse
#print axioms geometryRow008_physicalVolume_denominator_parse
#print axioms geometryRow008_physicalVolume_denominator_nonzero
#print axioms geometryRow008_physicalVolume_parse
#print axioms geometryRow008_physicalVolume_read
#print axioms geometryRow008_meanGap_field
#print axioms geometryRow008_meanGap_numerator_no_slash
#print axioms geometryRow008_meanGap_numerator_parse
#print axioms geometryRow008_meanGap_denominator_parse
#print axioms geometryRow008_meanGap_denominator_nonzero
#print axioms geometryRow008_meanGap_parse
#print axioms geometryRow008_meanGap_read
#print axioms geometryRow008_jensenBound_field
#print axioms geometryRow008_jensenBound_numerator_no_slash
#print axioms geometryRow008_jensenBound_numerator_parse
#print axioms geometryRow008_jensenBound_denominator_parse
#print axioms geometryRow008_jensenBound_denominator_nonzero
#print axioms geometryRow008_jensenBound_parse
#print axioms geometryRow008_jensenBound_read
#print axioms geometryRow008_factorMaxima_read
#print axioms geometryRow008_gapWeightedMeans_read
#print axioms geometryRow008_floor_text_read
#print axioms geometryRow008_floor_chars_parse
#print axioms geometryRow008_floor_parse
#print axioms decode_geometry_Rows_008

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
