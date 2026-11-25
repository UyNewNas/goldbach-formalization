import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100

/-! Original GeometryRow 4: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson004 : SourceJson :=
  (simplicesChunk004Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped004 : GeometryRow :=
  { simplexId := 4,
    vertexIds := #[27, 25, 11, 9, 8, 6, 5, 3, 1],
    physicalVolume := ((3597634647031377731130362888190328443978219379 : ℚ) / (8098831551283200000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((10838382242351 : ℚ) / (114805600000000 : ℚ)), ((10920973239931 : ℚ) / (114805600000000 : ℚ)), ((124249205703349 : ℚ) / (1033250400000000 : ℚ)), ((2876045408387 : ℚ) / (32289075000000 : ℚ)), ((84155134748179 : ℚ) / (1033250400000000 : ℚ)), ((75728493876491 : ℚ) / (1033250400000000 : ℚ)), ((424993488181 : ℚ) / (11480560000000 : ℚ)), ((18151079112343 : ℚ) / (516625200000000 : ℚ)), ((34646292959177 : ℚ) / (1033250400000000 : ℚ)), ((2246963806147 : ℚ) / (68883360000000 : ℚ))],
    jensenBound := ((167345053604504376052450509202734702717165179166873096943634148276871358279092777079040835993067520000000000000000000 : ℚ) / (192484908569479969944431711434953191361341760175276815901009535357073274738101035769520258502230764144046981002380675637805433299 : ℚ)),
    jensenFloorQ96 := (68880418737607890 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_simplexId_before"
  err.flush

theorem geometryRow004_simplexId_read :
    geometryRowsJson004.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped004.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_vertexIds_before"
  err.flush

theorem geometryRow004_vertexIds_read :
    geometryRowsJson004.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped004.vertexIds := by decide +kernel

noncomputable def geometryRow004_physicalVolumeNumeratorChars : List Char := ['3', '5', '9', '7', '6', '3', '4', '6', '4', '7', '0', '3', '1', '3', '7', '7', '7', '3', '1', '1', '3', '0', '3', '6', '2', '8', '8', '8', '1', '9', '0', '3', '2', '8', '4', '4', '3', '9', '7', '8', '2', '1', '9', '3', '7', '9']
noncomputable def geometryRow004_physicalVolumeDenominatorChars : List Char := ['8', '0', '9', '8', '8', '3', '1', '5', '5', '1', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_physicalVolumeText : String := String.ofList (geometryRow004_physicalVolumeNumeratorChars ++ '/' :: geometryRow004_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_physicalVolume_before_field"
  err.flush

theorem geometryRow004_physicalVolume_field :
    geometryRowsJson004.getObjVal? "physical_volume" = .ok (.str geometryRow004_physicalVolumeText) := by rfl

theorem geometryRow004_physicalVolume_numerator_no_slash :
    geometryRow004_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeNumeratorChars = some (3597634647031377731130362888190328443978219379 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeDenominatorChars = some (8098831551283200000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_nonzero : (8098831551283200000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_physicalVolume_parse :
    parseRational geometryRow004_physicalVolumeText = .ok geometryRowsTyped004.physicalVolume :=
  original_rational_fraction_of_chars geometryRow004_physicalVolumeNumeratorChars geometryRow004_physicalVolumeDenominatorChars
    (3597634647031377731130362888190328443978219379 : Int) (8098831551283200000000000000000000000000000000000000000000000000000 : Int)
    geometryRow004_physicalVolume_numerator_no_slash geometryRow004_physicalVolume_numerator_parse
    geometryRow004_physicalVolume_denominator_parse geometryRow004_physicalVolume_denominator_nonzero

theorem geometryRow004_physicalVolume_read :
    rationalField geometryRowsJson004 "physical_volume" = .ok geometryRowsTyped004.physicalVolume :=
  original_rationalField_of_string geometryRowsJson004 "physical_volume" geometryRow004_physicalVolumeText
    geometryRowsTyped004.physicalVolume geometryRow004_physicalVolume_field geometryRow004_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_physicalVolume_complete"
  err.flush

noncomputable def geometryRow004_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow004_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_meanGapText : String := String.ofList (geometryRow004_meanGapNumeratorChars ++ '/' :: geometryRow004_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_meanGap_before_field"
  err.flush

theorem geometryRow004_meanGap_field :
    geometryRowsJson004.getObjVal? "mean_gap" = .ok (.str geometryRow004_meanGapText) := by rfl

theorem geometryRow004_meanGap_numerator_no_slash :
    geometryRow004_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_meanGap_numerator_parse :
    SourceJson.intChars geometryRow004_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_parse :
    SourceJson.intChars geometryRow004_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_meanGap_parse :
    parseRational geometryRow004_meanGapText = .ok geometryRowsTyped004.meanGap :=
  original_rational_fraction_of_chars geometryRow004_meanGapNumeratorChars geometryRow004_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow004_meanGap_numerator_no_slash geometryRow004_meanGap_numerator_parse
    geometryRow004_meanGap_denominator_parse geometryRow004_meanGap_denominator_nonzero

theorem geometryRow004_meanGap_read :
    rationalField geometryRowsJson004 "mean_gap" = .ok geometryRowsTyped004.meanGap :=
  original_rationalField_of_string geometryRowsJson004 "mean_gap" geometryRow004_meanGapText
    geometryRowsTyped004.meanGap geometryRow004_meanGap_field geometryRow004_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_meanGap_complete"
  err.flush

noncomputable def geometryRow004_jensenBoundNumeratorChars : List Char := ['1', '6', '7', '3', '4', '5', '0', '5', '3', '6', '0', '4', '5', '0', '4', '3', '7', '6', '0', '5', '2', '4', '5', '0', '5', '0', '9', '2', '0', '2', '7', '3', '4', '7', '0', '2', '7', '1', '7', '1', '6', '5', '1', '7', '9', '1', '6', '6', '8', '7', '3', '0', '9', '6', '9', '4', '3', '6', '3', '4', '1', '4', '8', '2', '7', '6', '8', '7', '1', '3', '5', '8', '2', '7', '9', '0', '9', '2', '7', '7', '7', '0', '7', '9', '0', '4', '0', '8', '3', '5', '9', '9', '3', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_jensenBoundDenominatorChars : List Char := ['1', '9', '2', '4', '8', '4', '9', '0', '8', '5', '6', '9', '4', '7', '9', '9', '6', '9', '9', '4', '4', '4', '3', '1', '7', '1', '1', '4', '3', '4', '9', '5', '3', '1', '9', '1', '3', '6', '1', '3', '4', '1', '7', '6', '0', '1', '7', '5', '2', '7', '6', '8', '1', '5', '9', '0', '1', '0', '0', '9', '5', '3', '5', '3', '5', '7', '0', '7', '3', '2', '7', '4', '7', '3', '8', '1', '0', '1', '0', '3', '5', '7', '6', '9', '5', '2', '0', '2', '5', '8', '5', '0', '2', '2', '3', '0', '7', '6', '4', '1', '4', '4', '0', '4', '6', '9', '8', '1', '0', '0', '2', '3', '8', '0', '6', '7', '5', '6', '3', '7', '8', '0', '5', '4', '3', '3', '2', '9', '9']
noncomputable def geometryRow004_jensenBoundText : String := String.ofList (geometryRow004_jensenBoundNumeratorChars ++ '/' :: geometryRow004_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_jensenBound_before_field"
  err.flush

theorem geometryRow004_jensenBound_field :
    geometryRowsJson004.getObjVal? "jensen_bound" = .ok (.str geometryRow004_jensenBoundText) := by rfl

theorem geometryRow004_jensenBound_numerator_no_slash :
    geometryRow004_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow004_jensenBoundNumeratorChars = some (167345053604504376052450509202734702717165179166873096943634148276871358279092777079040835993067520000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow004_jensenBoundDenominatorChars = some (192484908569479969944431711434953191361341760175276815901009535357073274738101035769520258502230764144046981002380675637805433299 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_nonzero : (192484908569479969944431711434953191361341760175276815901009535357073274738101035769520258502230764144046981002380675637805433299 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_jensenBound_parse :
    parseRational geometryRow004_jensenBoundText = .ok geometryRowsTyped004.jensenBound :=
  original_rational_fraction_of_chars geometryRow004_jensenBoundNumeratorChars geometryRow004_jensenBoundDenominatorChars
    (167345053604504376052450509202734702717165179166873096943634148276871358279092777079040835993067520000000000000000000 : Int) (192484908569479969944431711434953191361341760175276815901009535357073274738101035769520258502230764144046981002380675637805433299 : Int)
    geometryRow004_jensenBound_numerator_no_slash geometryRow004_jensenBound_numerator_parse
    geometryRow004_jensenBound_denominator_parse geometryRow004_jensenBound_denominator_nonzero

theorem geometryRow004_jensenBound_read :
    rationalField geometryRowsJson004 "jensen_bound" = .ok geometryRowsTyped004.jensenBound :=
  original_rationalField_of_string geometryRowsJson004 "jensen_bound" geometryRow004_jensenBoundText
    geometryRowsTyped004.jensenBound geometryRow004_jensenBound_field geometryRow004_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_factorMaxima_before"
  err.flush

theorem geometryRow004_factorMaxima_read :
    rationalArrayField geometryRowsJson004 "factor_maxima" = .ok geometryRowsTyped004.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_gapWeightedMeans_before"
  err.flush

theorem geometryRow004_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson004 "gap_weighted_means" = .ok geometryRowsTyped004.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow004_floorChars : List Char := ['6', '8', '8', '8', '0', '4', '1', '8', '7', '3', '7', '6', '0', '7', '8', '9', '0']
noncomputable def geometryRow004_floorText : String := String.ofList geometryRow004_floorChars

theorem geometryRow004_floor_text_read :
    geometryRowsJson004.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow004_floorText := by rfl

theorem geometryRow004_floor_chars_parse :
    SourceJson.intChars geometryRow004_floorChars = some (68880418737607890 : Int) := by decide +kernel

theorem geometryRow004_floor_parse :
    parseInteger geometryRow004_floorText = .ok geometryRowsTyped004.jensenFloorQ96 := by
  simp only [geometryRow004_floorText, parseInteger, String.toList_ofList, geometryRow004_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_004 :
    decodeGeometryRow geometryRowsJson004 = .ok geometryRowsTyped004 :=
  original_geometryRow_of_fields geometryRowsJson004 geometryRowsTyped004 geometryRow004_floorText
    geometryRow004_simplexId_read geometryRow004_vertexIds_read
    geometryRow004_physicalVolume_read geometryRow004_meanGap_read
    geometryRow004_factorMaxima_read geometryRow004_gapWeightedMeans_read
    geometryRow004_jensenBound_read geometryRow004_floor_text_read geometryRow004_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_004_original_decoder_complete"
  err.flush

#print axioms geometryRow004_simplexId_read
#print axioms geometryRow004_vertexIds_read
#print axioms geometryRow004_physicalVolume_field
#print axioms geometryRow004_physicalVolume_numerator_no_slash
#print axioms geometryRow004_physicalVolume_numerator_parse
#print axioms geometryRow004_physicalVolume_denominator_parse
#print axioms geometryRow004_physicalVolume_denominator_nonzero
#print axioms geometryRow004_physicalVolume_parse
#print axioms geometryRow004_physicalVolume_read
#print axioms geometryRow004_meanGap_field
#print axioms geometryRow004_meanGap_numerator_no_slash
#print axioms geometryRow004_meanGap_numerator_parse
#print axioms geometryRow004_meanGap_denominator_parse
#print axioms geometryRow004_meanGap_denominator_nonzero
#print axioms geometryRow004_meanGap_parse
#print axioms geometryRow004_meanGap_read
#print axioms geometryRow004_jensenBound_field
#print axioms geometryRow004_jensenBound_numerator_no_slash
#print axioms geometryRow004_jensenBound_numerator_parse
#print axioms geometryRow004_jensenBound_denominator_parse
#print axioms geometryRow004_jensenBound_denominator_nonzero
#print axioms geometryRow004_jensenBound_parse
#print axioms geometryRow004_jensenBound_read
#print axioms geometryRow004_factorMaxima_read
#print axioms geometryRow004_gapWeightedMeans_read
#print axioms geometryRow004_floor_text_read
#print axioms geometryRow004_floor_chars_parse
#print axioms geometryRow004_floor_parse
#print axioms decode_geometry_Rows_004

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
