import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100

/-! Original GeometryRow 5: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson005 : SourceJson :=
  (simplicesChunk005Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped005 : GeometryRow :=
  { simplexId := 5,
    vertexIds := #[27, 25, 11, 10, 8, 6, 5, 3, 1],
    physicalVolume := ((731035324392605081457955368433504265717 : ℚ) / (22496754309120000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2523451807313 : ℚ) / (26493600000000 : ℚ)), ((2542511268293 : ℚ) / (26493600000000 : ℚ)), ((9574344889117 : ℚ) / (79480800000000 : ℚ)), ((353696169829 : ℚ) / (3974040000000 : ℚ)), ((6456758222539 : ℚ) / (79480800000000 : ℚ)), ((5808555078563 : ℚ) / (79480800000000 : ℚ)), ((165316109601 : ℚ) / (4415600000000 : ℚ)), ((274233266609 : ℚ) / (7948080000000 : ℚ)), ((2614953116177 : ℚ) / (79480800000000 : ℚ)), ((2614937220017 : ℚ) / (79480800000000 : ℚ))],
    jensenBound := ((69899651131267094072761218574113316095209297838682095983337596486055308463550415201894400000000000000000000 : ℚ) / (1094617901692272097080272564211430386477815954996360258066913334211015339904279977075967844847042564324791917267746316164059 : ℚ)),
    jensenFloorQ96 := (5059318791476 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_simplexId_before"
  err.flush

theorem geometryRow005_simplexId_read :
    geometryRowsJson005.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped005.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_vertexIds_before"
  err.flush

theorem geometryRow005_vertexIds_read :
    geometryRowsJson005.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped005.vertexIds := by decide +kernel

noncomputable def geometryRow005_physicalVolumeNumeratorChars : List Char := ['7', '3', '1', '0', '3', '5', '3', '2', '4', '3', '9', '2', '6', '0', '5', '0', '8', '1', '4', '5', '7', '9', '5', '5', '3', '6', '8', '4', '3', '3', '5', '0', '4', '2', '6', '5', '7', '1', '7']
noncomputable def geometryRow005_physicalVolumeDenominatorChars : List Char := ['2', '2', '4', '9', '6', '7', '5', '4', '3', '0', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_physicalVolumeText : String := String.ofList (geometryRow005_physicalVolumeNumeratorChars ++ '/' :: geometryRow005_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_physicalVolume_before_field"
  err.flush

theorem geometryRow005_physicalVolume_field :
    geometryRowsJson005.getObjVal? "physical_volume" = .ok (.str geometryRow005_physicalVolumeText) := by rfl

theorem geometryRow005_physicalVolume_numerator_no_slash :
    geometryRow005_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeNumeratorChars = some (731035324392605081457955368433504265717 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeDenominatorChars = some (22496754309120000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_nonzero : (22496754309120000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_physicalVolume_parse :
    parseRational geometryRow005_physicalVolumeText = .ok geometryRowsTyped005.physicalVolume :=
  original_rational_fraction_of_chars geometryRow005_physicalVolumeNumeratorChars geometryRow005_physicalVolumeDenominatorChars
    (731035324392605081457955368433504265717 : Int) (22496754309120000000000000000000000000000000000000000000000000000 : Int)
    geometryRow005_physicalVolume_numerator_no_slash geometryRow005_physicalVolume_numerator_parse
    geometryRow005_physicalVolume_denominator_parse geometryRow005_physicalVolume_denominator_nonzero

theorem geometryRow005_physicalVolume_read :
    rationalField geometryRowsJson005 "physical_volume" = .ok geometryRowsTyped005.physicalVolume :=
  original_rationalField_of_string geometryRowsJson005 "physical_volume" geometryRow005_physicalVolumeText
    geometryRowsTyped005.physicalVolume geometryRow005_physicalVolume_field geometryRow005_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_physicalVolume_complete"
  err.flush

noncomputable def geometryRow005_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow005_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_meanGapText : String := String.ofList (geometryRow005_meanGapNumeratorChars ++ '/' :: geometryRow005_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_meanGap_before_field"
  err.flush

theorem geometryRow005_meanGap_field :
    geometryRowsJson005.getObjVal? "mean_gap" = .ok (.str geometryRow005_meanGapText) := by rfl

theorem geometryRow005_meanGap_numerator_no_slash :
    geometryRow005_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_meanGap_numerator_parse :
    SourceJson.intChars geometryRow005_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_parse :
    SourceJson.intChars geometryRow005_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_meanGap_parse :
    parseRational geometryRow005_meanGapText = .ok geometryRowsTyped005.meanGap :=
  original_rational_fraction_of_chars geometryRow005_meanGapNumeratorChars geometryRow005_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow005_meanGap_numerator_no_slash geometryRow005_meanGap_numerator_parse
    geometryRow005_meanGap_denominator_parse geometryRow005_meanGap_denominator_nonzero

theorem geometryRow005_meanGap_read :
    rationalField geometryRowsJson005 "mean_gap" = .ok geometryRowsTyped005.meanGap :=
  original_rationalField_of_string geometryRowsJson005 "mean_gap" geometryRow005_meanGapText
    geometryRowsTyped005.meanGap geometryRow005_meanGap_field geometryRow005_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_meanGap_complete"
  err.flush

noncomputable def geometryRow005_jensenBoundNumeratorChars : List Char := ['6', '9', '8', '9', '9', '6', '5', '1', '1', '3', '1', '2', '6', '7', '0', '9', '4', '0', '7', '2', '7', '6', '1', '2', '1', '8', '5', '7', '4', '1', '1', '3', '3', '1', '6', '0', '9', '5', '2', '0', '9', '2', '9', '7', '8', '3', '8', '6', '8', '2', '0', '9', '5', '9', '8', '3', '3', '3', '7', '5', '9', '6', '4', '8', '6', '0', '5', '5', '3', '0', '8', '4', '6', '3', '5', '5', '0', '4', '1', '5', '2', '0', '1', '8', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_jensenBoundDenominatorChars : List Char := ['1', '0', '9', '4', '6', '1', '7', '9', '0', '1', '6', '9', '2', '2', '7', '2', '0', '9', '7', '0', '8', '0', '2', '7', '2', '5', '6', '4', '2', '1', '1', '4', '3', '0', '3', '8', '6', '4', '7', '7', '8', '1', '5', '9', '5', '4', '9', '9', '6', '3', '6', '0', '2', '5', '8', '0', '6', '6', '9', '1', '3', '3', '3', '4', '2', '1', '1', '0', '1', '5', '3', '3', '9', '9', '0', '4', '2', '7', '9', '9', '7', '7', '0', '7', '5', '9', '6', '7', '8', '4', '4', '8', '4', '7', '0', '4', '2', '5', '6', '4', '3', '2', '4', '7', '9', '1', '9', '1', '7', '2', '6', '7', '7', '4', '6', '3', '1', '6', '1', '6', '4', '0', '5', '9']
noncomputable def geometryRow005_jensenBoundText : String := String.ofList (geometryRow005_jensenBoundNumeratorChars ++ '/' :: geometryRow005_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_jensenBound_before_field"
  err.flush

theorem geometryRow005_jensenBound_field :
    geometryRowsJson005.getObjVal? "jensen_bound" = .ok (.str geometryRow005_jensenBoundText) := by rfl

theorem geometryRow005_jensenBound_numerator_no_slash :
    geometryRow005_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow005_jensenBoundNumeratorChars = some (69899651131267094072761218574113316095209297838682095983337596486055308463550415201894400000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow005_jensenBoundDenominatorChars = some (1094617901692272097080272564211430386477815954996360258066913334211015339904279977075967844847042564324791917267746316164059 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_nonzero : (1094617901692272097080272564211430386477815954996360258066913334211015339904279977075967844847042564324791917267746316164059 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_jensenBound_parse :
    parseRational geometryRow005_jensenBoundText = .ok geometryRowsTyped005.jensenBound :=
  original_rational_fraction_of_chars geometryRow005_jensenBoundNumeratorChars geometryRow005_jensenBoundDenominatorChars
    (69899651131267094072761218574113316095209297838682095983337596486055308463550415201894400000000000000000000 : Int) (1094617901692272097080272564211430386477815954996360258066913334211015339904279977075967844847042564324791917267746316164059 : Int)
    geometryRow005_jensenBound_numerator_no_slash geometryRow005_jensenBound_numerator_parse
    geometryRow005_jensenBound_denominator_parse geometryRow005_jensenBound_denominator_nonzero

theorem geometryRow005_jensenBound_read :
    rationalField geometryRowsJson005 "jensen_bound" = .ok geometryRowsTyped005.jensenBound :=
  original_rationalField_of_string geometryRowsJson005 "jensen_bound" geometryRow005_jensenBoundText
    geometryRowsTyped005.jensenBound geometryRow005_jensenBound_field geometryRow005_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_factorMaxima_before"
  err.flush

theorem geometryRow005_factorMaxima_read :
    rationalArrayField geometryRowsJson005 "factor_maxima" = .ok geometryRowsTyped005.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_gapWeightedMeans_before"
  err.flush

theorem geometryRow005_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson005 "gap_weighted_means" = .ok geometryRowsTyped005.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow005_floorChars : List Char := ['5', '0', '5', '9', '3', '1', '8', '7', '9', '1', '4', '7', '6']
noncomputable def geometryRow005_floorText : String := String.ofList geometryRow005_floorChars

theorem geometryRow005_floor_text_read :
    geometryRowsJson005.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow005_floorText := by rfl

theorem geometryRow005_floor_chars_parse :
    SourceJson.intChars geometryRow005_floorChars = some (5059318791476 : Int) := by decide +kernel

theorem geometryRow005_floor_parse :
    parseInteger geometryRow005_floorText = .ok geometryRowsTyped005.jensenFloorQ96 := by
  simp only [geometryRow005_floorText, parseInteger, String.toList_ofList, geometryRow005_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_005 :
    decodeGeometryRow geometryRowsJson005 = .ok geometryRowsTyped005 :=
  original_geometryRow_of_fields geometryRowsJson005 geometryRowsTyped005 geometryRow005_floorText
    geometryRow005_simplexId_read geometryRow005_vertexIds_read
    geometryRow005_physicalVolume_read geometryRow005_meanGap_read
    geometryRow005_factorMaxima_read geometryRow005_gapWeightedMeans_read
    geometryRow005_jensenBound_read geometryRow005_floor_text_read geometryRow005_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_005_original_decoder_complete"
  err.flush

#print axioms geometryRow005_simplexId_read
#print axioms geometryRow005_vertexIds_read
#print axioms geometryRow005_physicalVolume_field
#print axioms geometryRow005_physicalVolume_numerator_no_slash
#print axioms geometryRow005_physicalVolume_numerator_parse
#print axioms geometryRow005_physicalVolume_denominator_parse
#print axioms geometryRow005_physicalVolume_denominator_nonzero
#print axioms geometryRow005_physicalVolume_parse
#print axioms geometryRow005_physicalVolume_read
#print axioms geometryRow005_meanGap_field
#print axioms geometryRow005_meanGap_numerator_no_slash
#print axioms geometryRow005_meanGap_numerator_parse
#print axioms geometryRow005_meanGap_denominator_parse
#print axioms geometryRow005_meanGap_denominator_nonzero
#print axioms geometryRow005_meanGap_parse
#print axioms geometryRow005_meanGap_read
#print axioms geometryRow005_jensenBound_field
#print axioms geometryRow005_jensenBound_numerator_no_slash
#print axioms geometryRow005_jensenBound_numerator_parse
#print axioms geometryRow005_jensenBound_denominator_parse
#print axioms geometryRow005_jensenBound_denominator_nonzero
#print axioms geometryRow005_jensenBound_parse
#print axioms geometryRow005_jensenBound_read
#print axioms geometryRow005_factorMaxima_read
#print axioms geometryRow005_gapWeightedMeans_read
#print axioms geometryRow005_floor_text_read
#print axioms geometryRow005_floor_chars_parse
#print axioms geometryRow005_floor_parse
#print axioms decode_geometry_Rows_005

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
