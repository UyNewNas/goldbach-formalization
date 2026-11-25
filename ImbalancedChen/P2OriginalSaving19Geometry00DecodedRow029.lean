import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700

/-! Original GeometryRow 29: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson029 : SourceJson :=
  (simplicesChunk029Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped029 : GeometryRow :=
  { simplexId := 29,
    vertexIds := #[27, 25, 23, 21, 20, 17, 16, 4, 2],
    physicalVolume := ((34097976409780390762194095411 : ℚ) / (228030627965927124023437500000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((10031229 : ℚ) / (104500000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3890569 : ℚ) / (52250000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))],
    gapWeightedMeans := #[((203151703908061 : ℚ) / (2327925600000000 : ℚ)), ((51246871192879 : ℚ) / (581981400000000 : ℚ)), ((29257710726883 : ℚ) / (232792560000000 : ℚ)), ((2176037765597 : ℚ) / (22383900000000 : ℚ)), ((3283022814893 : ℚ) / (36373837500000 : ℚ)), ((7837687986883 : ℚ) / (116396280000000 : ℚ)), ((39153806313679 : ℚ) / (1163962800000000 : ℚ)), ((12728021644357 : ℚ) / (387987600000000 : ℚ)), ((12517189182517 : ℚ) / (387987600000000 : ℚ)), ((5828783102071 : ℚ) / (193993800000000 : ℚ))],
    jensenBound := ((266224837575889126513396977640229681732705096403960251774129799033953317646509293804969900134891520000000000000000000000 : ℚ) / (620120473838711593511788802974147870273292874329849966199807114659572129088349190676745345810651733625813076652283749654870391560531 : ℚ)),
    jensenFloorQ96 := (34013559601133510 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_simplexId_before"
  err.flush

theorem geometryRow029_simplexId_read :
    geometryRowsJson029.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped029.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_vertexIds_before"
  err.flush

theorem geometryRow029_vertexIds_read :
    geometryRowsJson029.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped029.vertexIds := by decide +kernel

noncomputable def geometryRow029_physicalVolumeNumeratorChars : List Char := ['3', '4', '0', '9', '7', '9', '7', '6', '4', '0', '9', '7', '8', '0', '3', '9', '0', '7', '6', '2', '1', '9', '4', '0', '9', '5', '4', '1', '1']
noncomputable def geometryRow029_physicalVolumeDenominatorChars : List Char := ['2', '2', '8', '0', '3', '0', '6', '2', '7', '9', '6', '5', '9', '2', '7', '1', '2', '4', '0', '2', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_physicalVolumeText : String := String.ofList (geometryRow029_physicalVolumeNumeratorChars ++ '/' :: geometryRow029_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_physicalVolume_before_field"
  err.flush

theorem geometryRow029_physicalVolume_field :
    geometryRowsJson029.getObjVal? "physical_volume" = .ok (.str geometryRow029_physicalVolumeText) := by rfl

theorem geometryRow029_physicalVolume_numerator_no_slash :
    geometryRow029_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeNumeratorChars = some (34097976409780390762194095411 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeDenominatorChars = some (228030627965927124023437500000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_nonzero : (228030627965927124023437500000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_physicalVolume_parse :
    parseRational geometryRow029_physicalVolumeText = .ok geometryRowsTyped029.physicalVolume :=
  original_rational_fraction_of_chars geometryRow029_physicalVolumeNumeratorChars geometryRow029_physicalVolumeDenominatorChars
    (34097976409780390762194095411 : Int) (228030627965927124023437500000000000000000000000000 : Int)
    geometryRow029_physicalVolume_numerator_no_slash geometryRow029_physicalVolume_numerator_parse
    geometryRow029_physicalVolume_denominator_parse geometryRow029_physicalVolume_denominator_nonzero

theorem geometryRow029_physicalVolume_read :
    rationalField geometryRowsJson029 "physical_volume" = .ok geometryRowsTyped029.physicalVolume :=
  original_rationalField_of_string geometryRowsJson029 "physical_volume" geometryRow029_physicalVolumeText
    geometryRowsTyped029.physicalVolume geometryRow029_physicalVolume_field geometryRow029_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_physicalVolume_complete"
  err.flush

noncomputable def geometryRow029_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow029_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_meanGapText : String := String.ofList (geometryRow029_meanGapNumeratorChars ++ '/' :: geometryRow029_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_meanGap_before_field"
  err.flush

theorem geometryRow029_meanGap_field :
    geometryRowsJson029.getObjVal? "mean_gap" = .ok (.str geometryRow029_meanGapText) := by rfl

theorem geometryRow029_meanGap_numerator_no_slash :
    geometryRow029_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_meanGap_numerator_parse :
    SourceJson.intChars geometryRow029_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_parse :
    SourceJson.intChars geometryRow029_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_meanGap_parse :
    parseRational geometryRow029_meanGapText = .ok geometryRowsTyped029.meanGap :=
  original_rational_fraction_of_chars geometryRow029_meanGapNumeratorChars geometryRow029_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow029_meanGap_numerator_no_slash geometryRow029_meanGap_numerator_parse
    geometryRow029_meanGap_denominator_parse geometryRow029_meanGap_denominator_nonzero

theorem geometryRow029_meanGap_read :
    rationalField geometryRowsJson029 "mean_gap" = .ok geometryRowsTyped029.meanGap :=
  original_rationalField_of_string geometryRowsJson029 "mean_gap" geometryRow029_meanGapText
    geometryRowsTyped029.meanGap geometryRow029_meanGap_field geometryRow029_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_meanGap_complete"
  err.flush

noncomputable def geometryRow029_jensenBoundNumeratorChars : List Char := ['2', '6', '6', '2', '2', '4', '8', '3', '7', '5', '7', '5', '8', '8', '9', '1', '2', '6', '5', '1', '3', '3', '9', '6', '9', '7', '7', '6', '4', '0', '2', '2', '9', '6', '8', '1', '7', '3', '2', '7', '0', '5', '0', '9', '6', '4', '0', '3', '9', '6', '0', '2', '5', '1', '7', '7', '4', '1', '2', '9', '7', '9', '9', '0', '3', '3', '9', '5', '3', '3', '1', '7', '6', '4', '6', '5', '0', '9', '2', '9', '3', '8', '0', '4', '9', '6', '9', '9', '0', '0', '1', '3', '4', '8', '9', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_jensenBoundDenominatorChars : List Char := ['6', '2', '0', '1', '2', '0', '4', '7', '3', '8', '3', '8', '7', '1', '1', '5', '9', '3', '5', '1', '1', '7', '8', '8', '8', '0', '2', '9', '7', '4', '1', '4', '7', '8', '7', '0', '2', '7', '3', '2', '9', '2', '8', '7', '4', '3', '2', '9', '8', '4', '9', '9', '6', '6', '1', '9', '9', '8', '0', '7', '1', '1', '4', '6', '5', '9', '5', '7', '2', '1', '2', '9', '0', '8', '8', '3', '4', '9', '1', '9', '0', '6', '7', '6', '7', '4', '5', '3', '4', '5', '8', '1', '0', '6', '5', '1', '7', '3', '3', '6', '2', '5', '8', '1', '3', '0', '7', '6', '6', '5', '2', '2', '8', '3', '7', '4', '9', '6', '5', '4', '8', '7', '0', '3', '9', '1', '5', '6', '0', '5', '3', '1']
noncomputable def geometryRow029_jensenBoundText : String := String.ofList (geometryRow029_jensenBoundNumeratorChars ++ '/' :: geometryRow029_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_jensenBound_before_field"
  err.flush

theorem geometryRow029_jensenBound_field :
    geometryRowsJson029.getObjVal? "jensen_bound" = .ok (.str geometryRow029_jensenBoundText) := by rfl

theorem geometryRow029_jensenBound_numerator_no_slash :
    geometryRow029_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow029_jensenBoundNumeratorChars = some (266224837575889126513396977640229681732705096403960251774129799033953317646509293804969900134891520000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow029_jensenBoundDenominatorChars = some (620120473838711593511788802974147870273292874329849966199807114659572129088349190676745345810651733625813076652283749654870391560531 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_nonzero : (620120473838711593511788802974147870273292874329849966199807114659572129088349190676745345810651733625813076652283749654870391560531 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_jensenBound_parse :
    parseRational geometryRow029_jensenBoundText = .ok geometryRowsTyped029.jensenBound :=
  original_rational_fraction_of_chars geometryRow029_jensenBoundNumeratorChars geometryRow029_jensenBoundDenominatorChars
    (266224837575889126513396977640229681732705096403960251774129799033953317646509293804969900134891520000000000000000000000 : Int) (620120473838711593511788802974147870273292874329849966199807114659572129088349190676745345810651733625813076652283749654870391560531 : Int)
    geometryRow029_jensenBound_numerator_no_slash geometryRow029_jensenBound_numerator_parse
    geometryRow029_jensenBound_denominator_parse geometryRow029_jensenBound_denominator_nonzero

theorem geometryRow029_jensenBound_read :
    rationalField geometryRowsJson029 "jensen_bound" = .ok geometryRowsTyped029.jensenBound :=
  original_rationalField_of_string geometryRowsJson029 "jensen_bound" geometryRow029_jensenBoundText
    geometryRowsTyped029.jensenBound geometryRow029_jensenBound_field geometryRow029_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_factorMaxima_before"
  err.flush

theorem geometryRow029_factorMaxima_read :
    rationalArrayField geometryRowsJson029 "factor_maxima" = .ok geometryRowsTyped029.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_gapWeightedMeans_before"
  err.flush

theorem geometryRow029_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson029 "gap_weighted_means" = .ok geometryRowsTyped029.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow029_floorChars : List Char := ['3', '4', '0', '1', '3', '5', '5', '9', '6', '0', '1', '1', '3', '3', '5', '1', '0']
noncomputable def geometryRow029_floorText : String := String.ofList geometryRow029_floorChars

theorem geometryRow029_floor_text_read :
    geometryRowsJson029.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow029_floorText := by rfl

theorem geometryRow029_floor_chars_parse :
    SourceJson.intChars geometryRow029_floorChars = some (34013559601133510 : Int) := by decide +kernel

theorem geometryRow029_floor_parse :
    parseInteger geometryRow029_floorText = .ok geometryRowsTyped029.jensenFloorQ96 := by
  simp only [geometryRow029_floorText, parseInteger, String.toList_ofList, geometryRow029_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_029 :
    decodeGeometryRow geometryRowsJson029 = .ok geometryRowsTyped029 :=
  original_geometryRow_of_fields geometryRowsJson029 geometryRowsTyped029 geometryRow029_floorText
    geometryRow029_simplexId_read geometryRow029_vertexIds_read
    geometryRow029_physicalVolume_read geometryRow029_meanGap_read
    geometryRow029_factorMaxima_read geometryRow029_gapWeightedMeans_read
    geometryRow029_jensenBound_read geometryRow029_floor_text_read geometryRow029_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_029_original_decoder_complete"
  err.flush

#print axioms geometryRow029_simplexId_read
#print axioms geometryRow029_vertexIds_read
#print axioms geometryRow029_physicalVolume_field
#print axioms geometryRow029_physicalVolume_numerator_no_slash
#print axioms geometryRow029_physicalVolume_numerator_parse
#print axioms geometryRow029_physicalVolume_denominator_parse
#print axioms geometryRow029_physicalVolume_denominator_nonzero
#print axioms geometryRow029_physicalVolume_parse
#print axioms geometryRow029_physicalVolume_read
#print axioms geometryRow029_meanGap_field
#print axioms geometryRow029_meanGap_numerator_no_slash
#print axioms geometryRow029_meanGap_numerator_parse
#print axioms geometryRow029_meanGap_denominator_parse
#print axioms geometryRow029_meanGap_denominator_nonzero
#print axioms geometryRow029_meanGap_parse
#print axioms geometryRow029_meanGap_read
#print axioms geometryRow029_jensenBound_field
#print axioms geometryRow029_jensenBound_numerator_no_slash
#print axioms geometryRow029_jensenBound_numerator_parse
#print axioms geometryRow029_jensenBound_denominator_parse
#print axioms geometryRow029_jensenBound_denominator_nonzero
#print axioms geometryRow029_jensenBound_parse
#print axioms geometryRow029_jensenBound_read
#print axioms geometryRow029_factorMaxima_read
#print axioms geometryRow029_gapWeightedMeans_read
#print axioms geometryRow029_floor_text_read
#print axioms geometryRow029_floor_chars_parse
#print axioms geometryRow029_floor_parse
#print axioms decode_geometry_Rows_029

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
