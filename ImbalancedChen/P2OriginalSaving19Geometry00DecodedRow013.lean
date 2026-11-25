import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300

/-! Original GeometryRow 13: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson013 : SourceJson :=
  (simplicesChunk013Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped013 : GeometryRow :=
  { simplexId := 13,
    vertexIds := #[27, 25, 23, 21, 9, 5, 4, 2, 0],
    physicalVolume := ((1456329461698504907604288941691279229211 : ℚ) / (6554066714507812500000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1036736975598001 : ℚ) / (11365754400000000 : ℚ)), ((522849952848023 : ℚ) / (5682877200000000 : ℚ)), ((463827999954271 : ℚ) / (3788584800000000 : ℚ)), ((26999357013659 : ℚ) / (291429600000000 : ℚ)), ((64787497677503 : ℚ) / (757716960000000 : ℚ)), ((267412610069219 : ℚ) / (3788584800000000 : ℚ)), ((33281692291049 : ℚ) / (947146200000000 : ℚ)), ((97477767032251 : ℚ) / (2841438600000000 : ℚ)), ((94685719253731 : ℚ) / (2841438600000000 : ℚ)), ((59409611339167 : ℚ) / (1894292400000000 : ℚ))],
    jensenBound := ((11842790139227445960539869981625129289916300222484783624237901130297276656709141051419788435386563297280000000000000000000000 : ℚ) / (22011290539914671272910648163237735422842085822520061732904147555156036376386490612670509873029126320317242404249777263640118050880939531 : ℚ)),
    jensenFloorQ96 := (42627328010212917 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_simplexId_before"
  err.flush

theorem geometryRow013_simplexId_read :
    geometryRowsJson013.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped013.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_vertexIds_before"
  err.flush

theorem geometryRow013_vertexIds_read :
    geometryRowsJson013.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped013.vertexIds := by decide +kernel

noncomputable def geometryRow013_physicalVolumeNumeratorChars : List Char := ['1', '4', '5', '6', '3', '2', '9', '4', '6', '1', '6', '9', '8', '5', '0', '4', '9', '0', '7', '6', '0', '4', '2', '8', '8', '9', '4', '1', '6', '9', '1', '2', '7', '9', '2', '2', '9', '2', '1', '1']
noncomputable def geometryRow013_physicalVolumeDenominatorChars : List Char := ['6', '5', '5', '4', '0', '6', '6', '7', '1', '4', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_physicalVolumeText : String := String.ofList (geometryRow013_physicalVolumeNumeratorChars ++ '/' :: geometryRow013_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_physicalVolume_before_field"
  err.flush

theorem geometryRow013_physicalVolume_field :
    geometryRowsJson013.getObjVal? "physical_volume" = .ok (.str geometryRow013_physicalVolumeText) := by rfl

theorem geometryRow013_physicalVolume_numerator_no_slash :
    geometryRow013_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeNumeratorChars = some (1456329461698504907604288941691279229211 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeDenominatorChars = some (6554066714507812500000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_nonzero : (6554066714507812500000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_physicalVolume_parse :
    parseRational geometryRow013_physicalVolumeText = .ok geometryRowsTyped013.physicalVolume :=
  original_rational_fraction_of_chars geometryRow013_physicalVolumeNumeratorChars geometryRow013_physicalVolumeDenominatorChars
    (1456329461698504907604288941691279229211 : Int) (6554066714507812500000000000000000000000000000000000000000000 : Int)
    geometryRow013_physicalVolume_numerator_no_slash geometryRow013_physicalVolume_numerator_parse
    geometryRow013_physicalVolume_denominator_parse geometryRow013_physicalVolume_denominator_nonzero

theorem geometryRow013_physicalVolume_read :
    rationalField geometryRowsJson013 "physical_volume" = .ok geometryRowsTyped013.physicalVolume :=
  original_rationalField_of_string geometryRowsJson013 "physical_volume" geometryRow013_physicalVolumeText
    geometryRowsTyped013.physicalVolume geometryRow013_physicalVolume_field geometryRow013_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_physicalVolume_complete"
  err.flush

noncomputable def geometryRow013_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow013_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_meanGapText : String := String.ofList (geometryRow013_meanGapNumeratorChars ++ '/' :: geometryRow013_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_meanGap_before_field"
  err.flush

theorem geometryRow013_meanGap_field :
    geometryRowsJson013.getObjVal? "mean_gap" = .ok (.str geometryRow013_meanGapText) := by rfl

theorem geometryRow013_meanGap_numerator_no_slash :
    geometryRow013_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_meanGap_numerator_parse :
    SourceJson.intChars geometryRow013_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_parse :
    SourceJson.intChars geometryRow013_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_meanGap_parse :
    parseRational geometryRow013_meanGapText = .ok geometryRowsTyped013.meanGap :=
  original_rational_fraction_of_chars geometryRow013_meanGapNumeratorChars geometryRow013_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow013_meanGap_numerator_no_slash geometryRow013_meanGap_numerator_parse
    geometryRow013_meanGap_denominator_parse geometryRow013_meanGap_denominator_nonzero

theorem geometryRow013_meanGap_read :
    rationalField geometryRowsJson013 "mean_gap" = .ok geometryRowsTyped013.meanGap :=
  original_rationalField_of_string geometryRowsJson013 "mean_gap" geometryRow013_meanGapText
    geometryRowsTyped013.meanGap geometryRow013_meanGap_field geometryRow013_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_meanGap_complete"
  err.flush

noncomputable def geometryRow013_jensenBoundNumeratorChars : List Char := ['1', '1', '8', '4', '2', '7', '9', '0', '1', '3', '9', '2', '2', '7', '4', '4', '5', '9', '6', '0', '5', '3', '9', '8', '6', '9', '9', '8', '1', '6', '2', '5', '1', '2', '9', '2', '8', '9', '9', '1', '6', '3', '0', '0', '2', '2', '2', '4', '8', '4', '7', '8', '3', '6', '2', '4', '2', '3', '7', '9', '0', '1', '1', '3', '0', '2', '9', '7', '2', '7', '6', '6', '5', '6', '7', '0', '9', '1', '4', '1', '0', '5', '1', '4', '1', '9', '7', '8', '8', '4', '3', '5', '3', '8', '6', '5', '6', '3', '2', '9', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_jensenBoundDenominatorChars : List Char := ['2', '2', '0', '1', '1', '2', '9', '0', '5', '3', '9', '9', '1', '4', '6', '7', '1', '2', '7', '2', '9', '1', '0', '6', '4', '8', '1', '6', '3', '2', '3', '7', '7', '3', '5', '4', '2', '2', '8', '4', '2', '0', '8', '5', '8', '2', '2', '5', '2', '0', '0', '6', '1', '7', '3', '2', '9', '0', '4', '1', '4', '7', '5', '5', '5', '1', '5', '6', '0', '3', '6', '3', '7', '6', '3', '8', '6', '4', '9', '0', '6', '1', '2', '6', '7', '0', '5', '0', '9', '8', '7', '3', '0', '2', '9', '1', '2', '6', '3', '2', '0', '3', '1', '7', '2', '4', '2', '4', '0', '4', '2', '4', '9', '7', '7', '7', '2', '6', '3', '6', '4', '0', '1', '1', '8', '0', '5', '0', '8', '8', '0', '9', '3', '9', '5', '3', '1']
noncomputable def geometryRow013_jensenBoundText : String := String.ofList (geometryRow013_jensenBoundNumeratorChars ++ '/' :: geometryRow013_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_jensenBound_before_field"
  err.flush

theorem geometryRow013_jensenBound_field :
    geometryRowsJson013.getObjVal? "jensen_bound" = .ok (.str geometryRow013_jensenBoundText) := by rfl

theorem geometryRow013_jensenBound_numerator_no_slash :
    geometryRow013_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow013_jensenBoundNumeratorChars = some (11842790139227445960539869981625129289916300222484783624237901130297276656709141051419788435386563297280000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow013_jensenBoundDenominatorChars = some (22011290539914671272910648163237735422842085822520061732904147555156036376386490612670509873029126320317242404249777263640118050880939531 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_nonzero : (22011290539914671272910648163237735422842085822520061732904147555156036376386490612670509873029126320317242404249777263640118050880939531 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_jensenBound_parse :
    parseRational geometryRow013_jensenBoundText = .ok geometryRowsTyped013.jensenBound :=
  original_rational_fraction_of_chars geometryRow013_jensenBoundNumeratorChars geometryRow013_jensenBoundDenominatorChars
    (11842790139227445960539869981625129289916300222484783624237901130297276656709141051419788435386563297280000000000000000000000 : Int) (22011290539914671272910648163237735422842085822520061732904147555156036376386490612670509873029126320317242404249777263640118050880939531 : Int)
    geometryRow013_jensenBound_numerator_no_slash geometryRow013_jensenBound_numerator_parse
    geometryRow013_jensenBound_denominator_parse geometryRow013_jensenBound_denominator_nonzero

theorem geometryRow013_jensenBound_read :
    rationalField geometryRowsJson013 "jensen_bound" = .ok geometryRowsTyped013.jensenBound :=
  original_rationalField_of_string geometryRowsJson013 "jensen_bound" geometryRow013_jensenBoundText
    geometryRowsTyped013.jensenBound geometryRow013_jensenBound_field geometryRow013_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_factorMaxima_before"
  err.flush

theorem geometryRow013_factorMaxima_read :
    rationalArrayField geometryRowsJson013 "factor_maxima" = .ok geometryRowsTyped013.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_gapWeightedMeans_before"
  err.flush

theorem geometryRow013_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson013 "gap_weighted_means" = .ok geometryRowsTyped013.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow013_floorChars : List Char := ['4', '2', '6', '2', '7', '3', '2', '8', '0', '1', '0', '2', '1', '2', '9', '1', '7']
noncomputable def geometryRow013_floorText : String := String.ofList geometryRow013_floorChars

theorem geometryRow013_floor_text_read :
    geometryRowsJson013.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow013_floorText := by rfl

theorem geometryRow013_floor_chars_parse :
    SourceJson.intChars geometryRow013_floorChars = some (42627328010212917 : Int) := by decide +kernel

theorem geometryRow013_floor_parse :
    parseInteger geometryRow013_floorText = .ok geometryRowsTyped013.jensenFloorQ96 := by
  simp only [geometryRow013_floorText, parseInteger, String.toList_ofList, geometryRow013_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_013 :
    decodeGeometryRow geometryRowsJson013 = .ok geometryRowsTyped013 :=
  original_geometryRow_of_fields geometryRowsJson013 geometryRowsTyped013 geometryRow013_floorText
    geometryRow013_simplexId_read geometryRow013_vertexIds_read
    geometryRow013_physicalVolume_read geometryRow013_meanGap_read
    geometryRow013_factorMaxima_read geometryRow013_gapWeightedMeans_read
    geometryRow013_jensenBound_read geometryRow013_floor_text_read geometryRow013_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_013_original_decoder_complete"
  err.flush

#print axioms geometryRow013_simplexId_read
#print axioms geometryRow013_vertexIds_read
#print axioms geometryRow013_physicalVolume_field
#print axioms geometryRow013_physicalVolume_numerator_no_slash
#print axioms geometryRow013_physicalVolume_numerator_parse
#print axioms geometryRow013_physicalVolume_denominator_parse
#print axioms geometryRow013_physicalVolume_denominator_nonzero
#print axioms geometryRow013_physicalVolume_parse
#print axioms geometryRow013_physicalVolume_read
#print axioms geometryRow013_meanGap_field
#print axioms geometryRow013_meanGap_numerator_no_slash
#print axioms geometryRow013_meanGap_numerator_parse
#print axioms geometryRow013_meanGap_denominator_parse
#print axioms geometryRow013_meanGap_denominator_nonzero
#print axioms geometryRow013_meanGap_parse
#print axioms geometryRow013_meanGap_read
#print axioms geometryRow013_jensenBound_field
#print axioms geometryRow013_jensenBound_numerator_no_slash
#print axioms geometryRow013_jensenBound_numerator_parse
#print axioms geometryRow013_jensenBound_denominator_parse
#print axioms geometryRow013_jensenBound_denominator_nonzero
#print axioms geometryRow013_jensenBound_parse
#print axioms geometryRow013_jensenBound_read
#print axioms geometryRow013_factorMaxima_read
#print axioms geometryRow013_gapWeightedMeans_read
#print axioms geometryRow013_floor_text_read
#print axioms geometryRow013_floor_chars_parse
#print axioms geometryRow013_floor_parse
#print axioms decode_geometry_Rows_013

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
