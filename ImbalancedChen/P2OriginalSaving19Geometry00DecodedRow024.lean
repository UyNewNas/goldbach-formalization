import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600

/-! Original GeometryRow 24: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson024 : SourceJson :=
  (simplicesChunk024Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped024 : GeometryRow :=
  { simplexId := 24,
    vertexIds := #[27, 25, 23, 21, 19, 17, 4, 2, 0],
    physicalVolume := ((68427686134057825058453931867302927 : ℚ) / (601886180207812500000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((12311085652583 : ℚ) / (136936800000000 : ℚ)), ((6209536381099 : ℚ) / (68468400000000 : ℚ)), ((75746372167 : ℚ) / (608608000000 : ℚ)), ((1001878325023 : ℚ) / (10533600000000 : ℚ)), ((4060861786777 : ℚ) / (45645600000000 : ℚ)), ((208797377519 : ℚ) / (3043040000000 : ℚ)), ((128218771119 : ℚ) / (3803800000000 : ℚ)), ((1125447134759 : ℚ) / (34234200000000 : ℚ)), ((1094618748599 : ℚ) / (34234200000000 : ℚ)), ((2117381802553 : ℚ) / (68468400000000 : ℚ))],
    jensenBound := ((169236911715035919510454613216494721325310414738080889344165077114335248240697409536000000000000000000000000 : ℚ) / (548394523674621584828593980465943356115223414471073917734459837202081688786958408498717702958232122953819552339732384519 : ℚ)),
    jensenFloorQ96 := (24450152154923092 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_simplexId_before"
  err.flush

theorem geometryRow024_simplexId_read :
    geometryRowsJson024.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped024.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_vertexIds_before"
  err.flush

theorem geometryRow024_vertexIds_read :
    geometryRowsJson024.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped024.vertexIds := by decide +kernel

noncomputable def geometryRow024_physicalVolumeNumeratorChars : List Char := ['6', '8', '4', '2', '7', '6', '8', '6', '1', '3', '4', '0', '5', '7', '8', '2', '5', '0', '5', '8', '4', '5', '3', '9', '3', '1', '8', '6', '7', '3', '0', '2', '9', '2', '7']
noncomputable def geometryRow024_physicalVolumeDenominatorChars : List Char := ['6', '0', '1', '8', '8', '6', '1', '8', '0', '2', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_physicalVolumeText : String := String.ofList (geometryRow024_physicalVolumeNumeratorChars ++ '/' :: geometryRow024_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_physicalVolume_before_field"
  err.flush

theorem geometryRow024_physicalVolume_field :
    geometryRowsJson024.getObjVal? "physical_volume" = .ok (.str geometryRow024_physicalVolumeText) := by rfl

theorem geometryRow024_physicalVolume_numerator_no_slash :
    geometryRow024_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeNumeratorChars = some (68427686134057825058453931867302927 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeDenominatorChars = some (601886180207812500000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_nonzero : (601886180207812500000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_physicalVolume_parse :
    parseRational geometryRow024_physicalVolumeText = .ok geometryRowsTyped024.physicalVolume :=
  original_rational_fraction_of_chars geometryRow024_physicalVolumeNumeratorChars geometryRow024_physicalVolumeDenominatorChars
    (68427686134057825058453931867302927 : Int) (601886180207812500000000000000000000000000000000000000000 : Int)
    geometryRow024_physicalVolume_numerator_no_slash geometryRow024_physicalVolume_numerator_parse
    geometryRow024_physicalVolume_denominator_parse geometryRow024_physicalVolume_denominator_nonzero

theorem geometryRow024_physicalVolume_read :
    rationalField geometryRowsJson024 "physical_volume" = .ok geometryRowsTyped024.physicalVolume :=
  original_rationalField_of_string geometryRowsJson024 "physical_volume" geometryRow024_physicalVolumeText
    geometryRowsTyped024.physicalVolume geometryRow024_physicalVolume_field geometryRow024_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_physicalVolume_complete"
  err.flush

noncomputable def geometryRow024_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow024_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_meanGapText : String := String.ofList (geometryRow024_meanGapNumeratorChars ++ '/' :: geometryRow024_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_meanGap_before_field"
  err.flush

theorem geometryRow024_meanGap_field :
    geometryRowsJson024.getObjVal? "mean_gap" = .ok (.str geometryRow024_meanGapText) := by rfl

theorem geometryRow024_meanGap_numerator_no_slash :
    geometryRow024_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_meanGap_numerator_parse :
    SourceJson.intChars geometryRow024_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_parse :
    SourceJson.intChars geometryRow024_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_meanGap_parse :
    parseRational geometryRow024_meanGapText = .ok geometryRowsTyped024.meanGap :=
  original_rational_fraction_of_chars geometryRow024_meanGapNumeratorChars geometryRow024_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow024_meanGap_numerator_no_slash geometryRow024_meanGap_numerator_parse
    geometryRow024_meanGap_denominator_parse geometryRow024_meanGap_denominator_nonzero

theorem geometryRow024_meanGap_read :
    rationalField geometryRowsJson024 "mean_gap" = .ok geometryRowsTyped024.meanGap :=
  original_rationalField_of_string geometryRowsJson024 "mean_gap" geometryRow024_meanGapText
    geometryRowsTyped024.meanGap geometryRow024_meanGap_field geometryRow024_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_meanGap_complete"
  err.flush

noncomputable def geometryRow024_jensenBoundNumeratorChars : List Char := ['1', '6', '9', '2', '3', '6', '9', '1', '1', '7', '1', '5', '0', '3', '5', '9', '1', '9', '5', '1', '0', '4', '5', '4', '6', '1', '3', '2', '1', '6', '4', '9', '4', '7', '2', '1', '3', '2', '5', '3', '1', '0', '4', '1', '4', '7', '3', '8', '0', '8', '0', '8', '8', '9', '3', '4', '4', '1', '6', '5', '0', '7', '7', '1', '1', '4', '3', '3', '5', '2', '4', '8', '2', '4', '0', '6', '9', '7', '4', '0', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_jensenBoundDenominatorChars : List Char := ['5', '4', '8', '3', '9', '4', '5', '2', '3', '6', '7', '4', '6', '2', '1', '5', '8', '4', '8', '2', '8', '5', '9', '3', '9', '8', '0', '4', '6', '5', '9', '4', '3', '3', '5', '6', '1', '1', '5', '2', '2', '3', '4', '1', '4', '4', '7', '1', '0', '7', '3', '9', '1', '7', '7', '3', '4', '4', '5', '9', '8', '3', '7', '2', '0', '2', '0', '8', '1', '6', '8', '8', '7', '8', '6', '9', '5', '8', '4', '0', '8', '4', '9', '8', '7', '1', '7', '7', '0', '2', '9', '5', '8', '2', '3', '2', '1', '2', '2', '9', '5', '3', '8', '1', '9', '5', '5', '2', '3', '3', '9', '7', '3', '2', '3', '8', '4', '5', '1', '9']
noncomputable def geometryRow024_jensenBoundText : String := String.ofList (geometryRow024_jensenBoundNumeratorChars ++ '/' :: geometryRow024_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_jensenBound_before_field"
  err.flush

theorem geometryRow024_jensenBound_field :
    geometryRowsJson024.getObjVal? "jensen_bound" = .ok (.str geometryRow024_jensenBoundText) := by rfl

theorem geometryRow024_jensenBound_numerator_no_slash :
    geometryRow024_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow024_jensenBoundNumeratorChars = some (169236911715035919510454613216494721325310414738080889344165077114335248240697409536000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow024_jensenBoundDenominatorChars = some (548394523674621584828593980465943356115223414471073917734459837202081688786958408498717702958232122953819552339732384519 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_nonzero : (548394523674621584828593980465943356115223414471073917734459837202081688786958408498717702958232122953819552339732384519 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_jensenBound_parse :
    parseRational geometryRow024_jensenBoundText = .ok geometryRowsTyped024.jensenBound :=
  original_rational_fraction_of_chars geometryRow024_jensenBoundNumeratorChars geometryRow024_jensenBoundDenominatorChars
    (169236911715035919510454613216494721325310414738080889344165077114335248240697409536000000000000000000000000 : Int) (548394523674621584828593980465943356115223414471073917734459837202081688786958408498717702958232122953819552339732384519 : Int)
    geometryRow024_jensenBound_numerator_no_slash geometryRow024_jensenBound_numerator_parse
    geometryRow024_jensenBound_denominator_parse geometryRow024_jensenBound_denominator_nonzero

theorem geometryRow024_jensenBound_read :
    rationalField geometryRowsJson024 "jensen_bound" = .ok geometryRowsTyped024.jensenBound :=
  original_rationalField_of_string geometryRowsJson024 "jensen_bound" geometryRow024_jensenBoundText
    geometryRowsTyped024.jensenBound geometryRow024_jensenBound_field geometryRow024_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_factorMaxima_before"
  err.flush

theorem geometryRow024_factorMaxima_read :
    rationalArrayField geometryRowsJson024 "factor_maxima" = .ok geometryRowsTyped024.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_gapWeightedMeans_before"
  err.flush

theorem geometryRow024_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson024 "gap_weighted_means" = .ok geometryRowsTyped024.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow024_floorChars : List Char := ['2', '4', '4', '5', '0', '1', '5', '2', '1', '5', '4', '9', '2', '3', '0', '9', '2']
noncomputable def geometryRow024_floorText : String := String.ofList geometryRow024_floorChars

theorem geometryRow024_floor_text_read :
    geometryRowsJson024.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow024_floorText := by rfl

theorem geometryRow024_floor_chars_parse :
    SourceJson.intChars geometryRow024_floorChars = some (24450152154923092 : Int) := by decide +kernel

theorem geometryRow024_floor_parse :
    parseInteger geometryRow024_floorText = .ok geometryRowsTyped024.jensenFloorQ96 := by
  simp only [geometryRow024_floorText, parseInteger, String.toList_ofList, geometryRow024_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_024 :
    decodeGeometryRow geometryRowsJson024 = .ok geometryRowsTyped024 :=
  original_geometryRow_of_fields geometryRowsJson024 geometryRowsTyped024 geometryRow024_floorText
    geometryRow024_simplexId_read geometryRow024_vertexIds_read
    geometryRow024_physicalVolume_read geometryRow024_meanGap_read
    geometryRow024_factorMaxima_read geometryRow024_gapWeightedMeans_read
    geometryRow024_jensenBound_read geometryRow024_floor_text_read geometryRow024_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_024_original_decoder_complete"
  err.flush

#print axioms geometryRow024_simplexId_read
#print axioms geometryRow024_vertexIds_read
#print axioms geometryRow024_physicalVolume_field
#print axioms geometryRow024_physicalVolume_numerator_no_slash
#print axioms geometryRow024_physicalVolume_numerator_parse
#print axioms geometryRow024_physicalVolume_denominator_parse
#print axioms geometryRow024_physicalVolume_denominator_nonzero
#print axioms geometryRow024_physicalVolume_parse
#print axioms geometryRow024_physicalVolume_read
#print axioms geometryRow024_meanGap_field
#print axioms geometryRow024_meanGap_numerator_no_slash
#print axioms geometryRow024_meanGap_numerator_parse
#print axioms geometryRow024_meanGap_denominator_parse
#print axioms geometryRow024_meanGap_denominator_nonzero
#print axioms geometryRow024_meanGap_parse
#print axioms geometryRow024_meanGap_read
#print axioms geometryRow024_jensenBound_field
#print axioms geometryRow024_jensenBound_numerator_no_slash
#print axioms geometryRow024_jensenBound_numerator_parse
#print axioms geometryRow024_jensenBound_denominator_parse
#print axioms geometryRow024_jensenBound_denominator_nonzero
#print axioms geometryRow024_jensenBound_parse
#print axioms geometryRow024_jensenBound_read
#print axioms geometryRow024_factorMaxima_read
#print axioms geometryRow024_gapWeightedMeans_read
#print axioms geometryRow024_floor_text_read
#print axioms geometryRow024_floor_chars_parse
#print axioms geometryRow024_floor_parse
#print axioms decode_geometry_Rows_024

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
