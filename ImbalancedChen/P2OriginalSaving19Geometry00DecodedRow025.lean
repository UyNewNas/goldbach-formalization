import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600

/-! Original GeometryRow 25: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson025 : SourceJson :=
  (simplicesChunk025Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped025 : GeometryRow :=
  { simplexId := 25,
    vertexIds := #[27, 25, 23, 21, 19, 17, 16, 4, 2],
    physicalVolume := ((23717674620953483091251700840683 : ℚ) / (326544151588439941406250000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((10031229 : ℚ) / (104500000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3890569 : ℚ) / (52250000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))],
    gapWeightedMeans := #[((12061195962533 : ℚ) / (136936800000000 : ℚ)), ((3042295768037 : ℚ) / (34234200000000 : ℚ)), ((1720322900771 : ℚ) / (13693680000000 : ℚ)), ((31894254949 : ℚ) / (329175000000 : ℚ)), ((1545895820267 : ℚ) / (17117100000000 : ℚ)), ((459566437223 : ℚ) / (6846840000000 : ℚ)), ((2295794914307 : ℚ) / (68468400000000 : ℚ)), ((746250434561 : ℚ) / (22822800000000 : ℚ)), ((725698177121 : ℚ) / (22822800000000 : ℚ)), ((345955586813 : ℚ) / (11411400000000 : ℚ))],
    jensenBound := ((4423704704460162816697557085547298576373392293342720881081156010015441387815698432000000000000000000000000 : ℚ) / (21214794794533317351162701989089880091943191745578202168459578797910935380333864740969781370435083185140872346042517281 : ℚ)),
    jensenFloorQ96 := (16520640366052400 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_simplexId_before"
  err.flush

theorem geometryRow025_simplexId_read :
    geometryRowsJson025.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped025.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_vertexIds_before"
  err.flush

theorem geometryRow025_vertexIds_read :
    geometryRowsJson025.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped025.vertexIds := by decide +kernel

noncomputable def geometryRow025_physicalVolumeNumeratorChars : List Char := ['2', '3', '7', '1', '7', '6', '7', '4', '6', '2', '0', '9', '5', '3', '4', '8', '3', '0', '9', '1', '2', '5', '1', '7', '0', '0', '8', '4', '0', '6', '8', '3']
noncomputable def geometryRow025_physicalVolumeDenominatorChars : List Char := ['3', '2', '6', '5', '4', '4', '1', '5', '1', '5', '8', '8', '4', '3', '9', '9', '4', '1', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_physicalVolumeText : String := String.ofList (geometryRow025_physicalVolumeNumeratorChars ++ '/' :: geometryRow025_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_physicalVolume_before_field"
  err.flush

theorem geometryRow025_physicalVolume_field :
    geometryRowsJson025.getObjVal? "physical_volume" = .ok (.str geometryRow025_physicalVolumeText) := by rfl

theorem geometryRow025_physicalVolume_numerator_no_slash :
    geometryRow025_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeNumeratorChars = some (23717674620953483091251700840683 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeDenominatorChars = some (326544151588439941406250000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_nonzero : (326544151588439941406250000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_physicalVolume_parse :
    parseRational geometryRow025_physicalVolumeText = .ok geometryRowsTyped025.physicalVolume :=
  original_rational_fraction_of_chars geometryRow025_physicalVolumeNumeratorChars geometryRow025_physicalVolumeDenominatorChars
    (23717674620953483091251700840683 : Int) (326544151588439941406250000000000000000000000000000000 : Int)
    geometryRow025_physicalVolume_numerator_no_slash geometryRow025_physicalVolume_numerator_parse
    geometryRow025_physicalVolume_denominator_parse geometryRow025_physicalVolume_denominator_nonzero

theorem geometryRow025_physicalVolume_read :
    rationalField geometryRowsJson025 "physical_volume" = .ok geometryRowsTyped025.physicalVolume :=
  original_rationalField_of_string geometryRowsJson025 "physical_volume" geometryRow025_physicalVolumeText
    geometryRowsTyped025.physicalVolume geometryRow025_physicalVolume_field geometryRow025_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_physicalVolume_complete"
  err.flush

noncomputable def geometryRow025_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow025_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_meanGapText : String := String.ofList (geometryRow025_meanGapNumeratorChars ++ '/' :: geometryRow025_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_meanGap_before_field"
  err.flush

theorem geometryRow025_meanGap_field :
    geometryRowsJson025.getObjVal? "mean_gap" = .ok (.str geometryRow025_meanGapText) := by rfl

theorem geometryRow025_meanGap_numerator_no_slash :
    geometryRow025_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_meanGap_numerator_parse :
    SourceJson.intChars geometryRow025_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_parse :
    SourceJson.intChars geometryRow025_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_meanGap_parse :
    parseRational geometryRow025_meanGapText = .ok geometryRowsTyped025.meanGap :=
  original_rational_fraction_of_chars geometryRow025_meanGapNumeratorChars geometryRow025_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow025_meanGap_numerator_no_slash geometryRow025_meanGap_numerator_parse
    geometryRow025_meanGap_denominator_parse geometryRow025_meanGap_denominator_nonzero

theorem geometryRow025_meanGap_read :
    rationalField geometryRowsJson025 "mean_gap" = .ok geometryRowsTyped025.meanGap :=
  original_rationalField_of_string geometryRowsJson025 "mean_gap" geometryRow025_meanGapText
    geometryRowsTyped025.meanGap geometryRow025_meanGap_field geometryRow025_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_meanGap_complete"
  err.flush

noncomputable def geometryRow025_jensenBoundNumeratorChars : List Char := ['4', '4', '2', '3', '7', '0', '4', '7', '0', '4', '4', '6', '0', '1', '6', '2', '8', '1', '6', '6', '9', '7', '5', '5', '7', '0', '8', '5', '5', '4', '7', '2', '9', '8', '5', '7', '6', '3', '7', '3', '3', '9', '2', '2', '9', '3', '3', '4', '2', '7', '2', '0', '8', '8', '1', '0', '8', '1', '1', '5', '6', '0', '1', '0', '0', '1', '5', '4', '4', '1', '3', '8', '7', '8', '1', '5', '6', '9', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_jensenBoundDenominatorChars : List Char := ['2', '1', '2', '1', '4', '7', '9', '4', '7', '9', '4', '5', '3', '3', '3', '1', '7', '3', '5', '1', '1', '6', '2', '7', '0', '1', '9', '8', '9', '0', '8', '9', '8', '8', '0', '0', '9', '1', '9', '4', '3', '1', '9', '1', '7', '4', '5', '5', '7', '8', '2', '0', '2', '1', '6', '8', '4', '5', '9', '5', '7', '8', '7', '9', '7', '9', '1', '0', '9', '3', '5', '3', '8', '0', '3', '3', '3', '8', '6', '4', '7', '4', '0', '9', '6', '9', '7', '8', '1', '3', '7', '0', '4', '3', '5', '0', '8', '3', '1', '8', '5', '1', '4', '0', '8', '7', '2', '3', '4', '6', '0', '4', '2', '5', '1', '7', '2', '8', '1']
noncomputable def geometryRow025_jensenBoundText : String := String.ofList (geometryRow025_jensenBoundNumeratorChars ++ '/' :: geometryRow025_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_jensenBound_before_field"
  err.flush

theorem geometryRow025_jensenBound_field :
    geometryRowsJson025.getObjVal? "jensen_bound" = .ok (.str geometryRow025_jensenBoundText) := by rfl

theorem geometryRow025_jensenBound_numerator_no_slash :
    geometryRow025_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow025_jensenBoundNumeratorChars = some (4423704704460162816697557085547298576373392293342720881081156010015441387815698432000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow025_jensenBoundDenominatorChars = some (21214794794533317351162701989089880091943191745578202168459578797910935380333864740969781370435083185140872346042517281 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_nonzero : (21214794794533317351162701989089880091943191745578202168459578797910935380333864740969781370435083185140872346042517281 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_jensenBound_parse :
    parseRational geometryRow025_jensenBoundText = .ok geometryRowsTyped025.jensenBound :=
  original_rational_fraction_of_chars geometryRow025_jensenBoundNumeratorChars geometryRow025_jensenBoundDenominatorChars
    (4423704704460162816697557085547298576373392293342720881081156010015441387815698432000000000000000000000000 : Int) (21214794794533317351162701989089880091943191745578202168459578797910935380333864740969781370435083185140872346042517281 : Int)
    geometryRow025_jensenBound_numerator_no_slash geometryRow025_jensenBound_numerator_parse
    geometryRow025_jensenBound_denominator_parse geometryRow025_jensenBound_denominator_nonzero

theorem geometryRow025_jensenBound_read :
    rationalField geometryRowsJson025 "jensen_bound" = .ok geometryRowsTyped025.jensenBound :=
  original_rationalField_of_string geometryRowsJson025 "jensen_bound" geometryRow025_jensenBoundText
    geometryRowsTyped025.jensenBound geometryRow025_jensenBound_field geometryRow025_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_factorMaxima_before"
  err.flush

theorem geometryRow025_factorMaxima_read :
    rationalArrayField geometryRowsJson025 "factor_maxima" = .ok geometryRowsTyped025.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_gapWeightedMeans_before"
  err.flush

theorem geometryRow025_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson025 "gap_weighted_means" = .ok geometryRowsTyped025.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow025_floorChars : List Char := ['1', '6', '5', '2', '0', '6', '4', '0', '3', '6', '6', '0', '5', '2', '4', '0', '0']
noncomputable def geometryRow025_floorText : String := String.ofList geometryRow025_floorChars

theorem geometryRow025_floor_text_read :
    geometryRowsJson025.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow025_floorText := by rfl

theorem geometryRow025_floor_chars_parse :
    SourceJson.intChars geometryRow025_floorChars = some (16520640366052400 : Int) := by decide +kernel

theorem geometryRow025_floor_parse :
    parseInteger geometryRow025_floorText = .ok geometryRowsTyped025.jensenFloorQ96 := by
  simp only [geometryRow025_floorText, parseInteger, String.toList_ofList, geometryRow025_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_025 :
    decodeGeometryRow geometryRowsJson025 = .ok geometryRowsTyped025 :=
  original_geometryRow_of_fields geometryRowsJson025 geometryRowsTyped025 geometryRow025_floorText
    geometryRow025_simplexId_read geometryRow025_vertexIds_read
    geometryRow025_physicalVolume_read geometryRow025_meanGap_read
    geometryRow025_factorMaxima_read geometryRow025_gapWeightedMeans_read
    geometryRow025_jensenBound_read geometryRow025_floor_text_read geometryRow025_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_025_original_decoder_complete"
  err.flush

#print axioms geometryRow025_simplexId_read
#print axioms geometryRow025_vertexIds_read
#print axioms geometryRow025_physicalVolume_field
#print axioms geometryRow025_physicalVolume_numerator_no_slash
#print axioms geometryRow025_physicalVolume_numerator_parse
#print axioms geometryRow025_physicalVolume_denominator_parse
#print axioms geometryRow025_physicalVolume_denominator_nonzero
#print axioms geometryRow025_physicalVolume_parse
#print axioms geometryRow025_physicalVolume_read
#print axioms geometryRow025_meanGap_field
#print axioms geometryRow025_meanGap_numerator_no_slash
#print axioms geometryRow025_meanGap_numerator_parse
#print axioms geometryRow025_meanGap_denominator_parse
#print axioms geometryRow025_meanGap_denominator_nonzero
#print axioms geometryRow025_meanGap_parse
#print axioms geometryRow025_meanGap_read
#print axioms geometryRow025_jensenBound_field
#print axioms geometryRow025_jensenBound_numerator_no_slash
#print axioms geometryRow025_jensenBound_numerator_parse
#print axioms geometryRow025_jensenBound_denominator_parse
#print axioms geometryRow025_jensenBound_denominator_nonzero
#print axioms geometryRow025_jensenBound_parse
#print axioms geometryRow025_jensenBound_read
#print axioms geometryRow025_factorMaxima_read
#print axioms geometryRow025_gapWeightedMeans_read
#print axioms geometryRow025_floor_text_read
#print axioms geometryRow025_floor_chars_parse
#print axioms geometryRow025_floor_parse
#print axioms decode_geometry_Rows_025

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
