import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01100

/-! Original GeometryRow 47: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson047 : SourceJson :=
  (simplicesChunk047Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped047 : GeometryRow :=
  { simplexId := 47,
    vertexIds := #[27, 15, 11, 10, 8, 6, 5, 3, 1],
    physicalVolume := ((39811812245410236107437313369872262962933 : ℚ) / (921467056501555200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2572084188047 : ℚ) / (26493600000000 : ℚ)), ((2591143649027 : ℚ) / (26493600000000 : ℚ)), ((9543298584737 : ℚ) / (79480800000000 : ℚ)), ((388569150637 : ℚ) / (4415600000000 : ℚ)), ((6262228699603 : ℚ) / (79480800000000 : ℚ)), ((5839601382943 : ℚ) / (79480800000000 : ℚ)), ((184881493529 : ℚ) / (4967550000000 : ℚ)), ((348870630853 : ℚ) / (9935100000000 : ℚ)), ((2663585496911 : ℚ) / (79480800000000 : ℚ)), ((2663569600751 : ℚ) / (79480800000000 : ℚ))],
    jensenBound := ((11774113041931388862349727341374616138848925161694075565676114015244938642235317643500000000000000000000000 : ℚ) / (145306752807946921330782311078347474440684746167918369772888580420665063245011221672488877665290478221914066509442953530217 : ℚ)),
    jensenFloorQ96 := (6419807225204 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_simplexId_before"
  err.flush

theorem geometryRow047_simplexId_read :
    geometryRowsJson047.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped047.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_vertexIds_before"
  err.flush

theorem geometryRow047_vertexIds_read :
    geometryRowsJson047.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped047.vertexIds := by decide +kernel

noncomputable def geometryRow047_physicalVolumeNumeratorChars : List Char := ['3', '9', '8', '1', '1', '8', '1', '2', '2', '4', '5', '4', '1', '0', '2', '3', '6', '1', '0', '7', '4', '3', '7', '3', '1', '3', '3', '6', '9', '8', '7', '2', '2', '6', '2', '9', '6', '2', '9', '3', '3']
noncomputable def geometryRow047_physicalVolumeDenominatorChars : List Char := ['9', '2', '1', '4', '6', '7', '0', '5', '6', '5', '0', '1', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_physicalVolumeText : String := String.ofList (geometryRow047_physicalVolumeNumeratorChars ++ '/' :: geometryRow047_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_physicalVolume_before_field"
  err.flush

theorem geometryRow047_physicalVolume_field :
    geometryRowsJson047.getObjVal? "physical_volume" = .ok (.str geometryRow047_physicalVolumeText) := by rfl

theorem geometryRow047_physicalVolume_numerator_no_slash :
    geometryRow047_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeNumeratorChars = some (39811812245410236107437313369872262962933 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeDenominatorChars = some (921467056501555200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_nonzero : (921467056501555200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_physicalVolume_parse :
    parseRational geometryRow047_physicalVolumeText = .ok geometryRowsTyped047.physicalVolume :=
  original_rational_fraction_of_chars geometryRow047_physicalVolumeNumeratorChars geometryRow047_physicalVolumeDenominatorChars
    (39811812245410236107437313369872262962933 : Int) (921467056501555200000000000000000000000000000000000000000000000000 : Int)
    geometryRow047_physicalVolume_numerator_no_slash geometryRow047_physicalVolume_numerator_parse
    geometryRow047_physicalVolume_denominator_parse geometryRow047_physicalVolume_denominator_nonzero

theorem geometryRow047_physicalVolume_read :
    rationalField geometryRowsJson047 "physical_volume" = .ok geometryRowsTyped047.physicalVolume :=
  original_rationalField_of_string geometryRowsJson047 "physical_volume" geometryRow047_physicalVolumeText
    geometryRowsTyped047.physicalVolume geometryRow047_physicalVolume_field geometryRow047_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_physicalVolume_complete"
  err.flush

noncomputable def geometryRow047_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow047_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_meanGapText : String := String.ofList (geometryRow047_meanGapNumeratorChars ++ '/' :: geometryRow047_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_meanGap_before_field"
  err.flush

theorem geometryRow047_meanGap_field :
    geometryRowsJson047.getObjVal? "mean_gap" = .ok (.str geometryRow047_meanGapText) := by rfl

theorem geometryRow047_meanGap_numerator_no_slash :
    geometryRow047_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_meanGap_numerator_parse :
    SourceJson.intChars geometryRow047_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_parse :
    SourceJson.intChars geometryRow047_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_meanGap_parse :
    parseRational geometryRow047_meanGapText = .ok geometryRowsTyped047.meanGap :=
  original_rational_fraction_of_chars geometryRow047_meanGapNumeratorChars geometryRow047_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow047_meanGap_numerator_no_slash geometryRow047_meanGap_numerator_parse
    geometryRow047_meanGap_denominator_parse geometryRow047_meanGap_denominator_nonzero

theorem geometryRow047_meanGap_read :
    rationalField geometryRowsJson047 "mean_gap" = .ok geometryRowsTyped047.meanGap :=
  original_rationalField_of_string geometryRowsJson047 "mean_gap" geometryRow047_meanGapText
    geometryRowsTyped047.meanGap geometryRow047_meanGap_field geometryRow047_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_meanGap_complete"
  err.flush

noncomputable def geometryRow047_jensenBoundNumeratorChars : List Char := ['1', '1', '7', '7', '4', '1', '1', '3', '0', '4', '1', '9', '3', '1', '3', '8', '8', '8', '6', '2', '3', '4', '9', '7', '2', '7', '3', '4', '1', '3', '7', '4', '6', '1', '6', '1', '3', '8', '8', '4', '8', '9', '2', '5', '1', '6', '1', '6', '9', '4', '0', '7', '5', '5', '6', '5', '6', '7', '6', '1', '1', '4', '0', '1', '5', '2', '4', '4', '9', '3', '8', '6', '4', '2', '2', '3', '5', '3', '1', '7', '6', '4', '3', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_jensenBoundDenominatorChars : List Char := ['1', '4', '5', '3', '0', '6', '7', '5', '2', '8', '0', '7', '9', '4', '6', '9', '2', '1', '3', '3', '0', '7', '8', '2', '3', '1', '1', '0', '7', '8', '3', '4', '7', '4', '7', '4', '4', '4', '0', '6', '8', '4', '7', '4', '6', '1', '6', '7', '9', '1', '8', '3', '6', '9', '7', '7', '2', '8', '8', '8', '5', '8', '0', '4', '2', '0', '6', '6', '5', '0', '6', '3', '2', '4', '5', '0', '1', '1', '2', '2', '1', '6', '7', '2', '4', '8', '8', '8', '7', '7', '6', '6', '5', '2', '9', '0', '4', '7', '8', '2', '2', '1', '9', '1', '4', '0', '6', '6', '5', '0', '9', '4', '4', '2', '9', '5', '3', '5', '3', '0', '2', '1', '7']
noncomputable def geometryRow047_jensenBoundText : String := String.ofList (geometryRow047_jensenBoundNumeratorChars ++ '/' :: geometryRow047_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_jensenBound_before_field"
  err.flush

theorem geometryRow047_jensenBound_field :
    geometryRowsJson047.getObjVal? "jensen_bound" = .ok (.str geometryRow047_jensenBoundText) := by rfl

theorem geometryRow047_jensenBound_numerator_no_slash :
    geometryRow047_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow047_jensenBoundNumeratorChars = some (11774113041931388862349727341374616138848925161694075565676114015244938642235317643500000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow047_jensenBoundDenominatorChars = some (145306752807946921330782311078347474440684746167918369772888580420665063245011221672488877665290478221914066509442953530217 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_nonzero : (145306752807946921330782311078347474440684746167918369772888580420665063245011221672488877665290478221914066509442953530217 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_jensenBound_parse :
    parseRational geometryRow047_jensenBoundText = .ok geometryRowsTyped047.jensenBound :=
  original_rational_fraction_of_chars geometryRow047_jensenBoundNumeratorChars geometryRow047_jensenBoundDenominatorChars
    (11774113041931388862349727341374616138848925161694075565676114015244938642235317643500000000000000000000000 : Int) (145306752807946921330782311078347474440684746167918369772888580420665063245011221672488877665290478221914066509442953530217 : Int)
    geometryRow047_jensenBound_numerator_no_slash geometryRow047_jensenBound_numerator_parse
    geometryRow047_jensenBound_denominator_parse geometryRow047_jensenBound_denominator_nonzero

theorem geometryRow047_jensenBound_read :
    rationalField geometryRowsJson047 "jensen_bound" = .ok geometryRowsTyped047.jensenBound :=
  original_rationalField_of_string geometryRowsJson047 "jensen_bound" geometryRow047_jensenBoundText
    geometryRowsTyped047.jensenBound geometryRow047_jensenBound_field geometryRow047_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_factorMaxima_before"
  err.flush

theorem geometryRow047_factorMaxima_read :
    rationalArrayField geometryRowsJson047 "factor_maxima" = .ok geometryRowsTyped047.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_gapWeightedMeans_before"
  err.flush

theorem geometryRow047_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson047 "gap_weighted_means" = .ok geometryRowsTyped047.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow047_floorChars : List Char := ['6', '4', '1', '9', '8', '0', '7', '2', '2', '5', '2', '0', '4']
noncomputable def geometryRow047_floorText : String := String.ofList geometryRow047_floorChars

theorem geometryRow047_floor_text_read :
    geometryRowsJson047.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow047_floorText := by rfl

theorem geometryRow047_floor_chars_parse :
    SourceJson.intChars geometryRow047_floorChars = some (6419807225204 : Int) := by decide +kernel

theorem geometryRow047_floor_parse :
    parseInteger geometryRow047_floorText = .ok geometryRowsTyped047.jensenFloorQ96 := by
  simp only [geometryRow047_floorText, parseInteger, String.toList_ofList, geometryRow047_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_047 :
    decodeGeometryRow geometryRowsJson047 = .ok geometryRowsTyped047 :=
  original_geometryRow_of_fields geometryRowsJson047 geometryRowsTyped047 geometryRow047_floorText
    geometryRow047_simplexId_read geometryRow047_vertexIds_read
    geometryRow047_physicalVolume_read geometryRow047_meanGap_read
    geometryRow047_factorMaxima_read geometryRow047_gapWeightedMeans_read
    geometryRow047_jensenBound_read geometryRow047_floor_text_read geometryRow047_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_047_original_decoder_complete"
  err.flush

#print axioms geometryRow047_simplexId_read
#print axioms geometryRow047_vertexIds_read
#print axioms geometryRow047_physicalVolume_field
#print axioms geometryRow047_physicalVolume_numerator_no_slash
#print axioms geometryRow047_physicalVolume_numerator_parse
#print axioms geometryRow047_physicalVolume_denominator_parse
#print axioms geometryRow047_physicalVolume_denominator_nonzero
#print axioms geometryRow047_physicalVolume_parse
#print axioms geometryRow047_physicalVolume_read
#print axioms geometryRow047_meanGap_field
#print axioms geometryRow047_meanGap_numerator_no_slash
#print axioms geometryRow047_meanGap_numerator_parse
#print axioms geometryRow047_meanGap_denominator_parse
#print axioms geometryRow047_meanGap_denominator_nonzero
#print axioms geometryRow047_meanGap_parse
#print axioms geometryRow047_meanGap_read
#print axioms geometryRow047_jensenBound_field
#print axioms geometryRow047_jensenBound_numerator_no_slash
#print axioms geometryRow047_jensenBound_numerator_parse
#print axioms geometryRow047_jensenBound_denominator_parse
#print axioms geometryRow047_jensenBound_denominator_nonzero
#print axioms geometryRow047_jensenBound_parse
#print axioms geometryRow047_jensenBound_read
#print axioms geometryRow047_factorMaxima_read
#print axioms geometryRow047_gapWeightedMeans_read
#print axioms geometryRow047_floor_text_read
#print axioms geometryRow047_floor_chars_parse
#print axioms geometryRow047_floor_parse
#print axioms decode_geometry_Rows_047

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
