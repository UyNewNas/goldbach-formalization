import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200

/-! Original GeometryRow 49: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson049 : SourceJson :=
  (simplicesChunk049Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped049 : GeometryRow :=
  { simplexId := 49,
    vertexIds := #[27, 26, 24, 10, 8, 6, 5, 3, 1],
    physicalVolume := ((26734276023916289641084193985336494027 : ℚ) / (822738443304960000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((3365581 : ℚ) / (36000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((26366 : ℚ) / (609375 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((4639531798883 : ℚ) / (49202400000000 : ℚ)), ((4674927940703 : ℚ) / (49202400000000 : ℚ)), ((18029889812443 : ℚ) / (147607200000000 : ℚ)), ((104946317173 : ℚ) / (1153181250000 : ℚ)), ((12178656895897 : ℚ) / (147607200000000 : ℚ)), ((10538352984677 : ℚ) / (147607200000000 : ℚ)), ((295788693817 : ℚ) / (8200400000000 : ℚ)), ((2523012411163 : ℚ) / (73803600000000 : ℚ)), ((4809443120099 : ℚ) / (147607200000000 : ℚ)), ((4809433279619 : ℚ) / (147607200000000 : ℚ))],
    jensenBound := ((1871778296444611318533996430492711065603050674621681591685939280833373528801180052440000000000000000000000000 : ℚ) / (27672050799884095091073107968995740536805520934615792931192984787450334929773640573982364207923705754027591055885207115854181 : ℚ)),
    jensenFloorQ96 := (5359109671120 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_simplexId_before"
  err.flush

theorem geometryRow049_simplexId_read :
    geometryRowsJson049.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped049.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_vertexIds_before"
  err.flush

theorem geometryRow049_vertexIds_read :
    geometryRowsJson049.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped049.vertexIds := by decide +kernel

noncomputable def geometryRow049_physicalVolumeNumeratorChars : List Char := ['2', '6', '7', '3', '4', '2', '7', '6', '0', '2', '3', '9', '1', '6', '2', '8', '9', '6', '4', '1', '0', '8', '4', '1', '9', '3', '9', '8', '5', '3', '3', '6', '4', '9', '4', '0', '2', '7']
noncomputable def geometryRow049_physicalVolumeDenominatorChars : List Char := ['8', '2', '2', '7', '3', '8', '4', '4', '3', '3', '0', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_physicalVolumeText : String := String.ofList (geometryRow049_physicalVolumeNumeratorChars ++ '/' :: geometryRow049_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_physicalVolume_before_field"
  err.flush

theorem geometryRow049_physicalVolume_field :
    geometryRowsJson049.getObjVal? "physical_volume" = .ok (.str geometryRow049_physicalVolumeText) := by rfl

theorem geometryRow049_physicalVolume_numerator_no_slash :
    geometryRow049_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeNumeratorChars = some (26734276023916289641084193985336494027 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeDenominatorChars = some (822738443304960000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_nonzero : (822738443304960000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_physicalVolume_parse :
    parseRational geometryRow049_physicalVolumeText = .ok geometryRowsTyped049.physicalVolume :=
  original_rational_fraction_of_chars geometryRow049_physicalVolumeNumeratorChars geometryRow049_physicalVolumeDenominatorChars
    (26734276023916289641084193985336494027 : Int) (822738443304960000000000000000000000000000000000000000000000000 : Int)
    geometryRow049_physicalVolume_numerator_no_slash geometryRow049_physicalVolume_numerator_parse
    geometryRow049_physicalVolume_denominator_parse geometryRow049_physicalVolume_denominator_nonzero

theorem geometryRow049_physicalVolume_read :
    rationalField geometryRowsJson049 "physical_volume" = .ok geometryRowsTyped049.physicalVolume :=
  original_rationalField_of_string geometryRowsJson049 "physical_volume" geometryRow049_physicalVolumeText
    geometryRowsTyped049.physicalVolume geometryRow049_physicalVolume_field geometryRow049_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_physicalVolume_complete"
  err.flush

noncomputable def geometryRow049_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow049_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_meanGapText : String := String.ofList (geometryRow049_meanGapNumeratorChars ++ '/' :: geometryRow049_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_meanGap_before_field"
  err.flush

theorem geometryRow049_meanGap_field :
    geometryRowsJson049.getObjVal? "mean_gap" = .ok (.str geometryRow049_meanGapText) := by rfl

theorem geometryRow049_meanGap_numerator_no_slash :
    geometryRow049_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_meanGap_numerator_parse :
    SourceJson.intChars geometryRow049_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_parse :
    SourceJson.intChars geometryRow049_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_meanGap_parse :
    parseRational geometryRow049_meanGapText = .ok geometryRowsTyped049.meanGap :=
  original_rational_fraction_of_chars geometryRow049_meanGapNumeratorChars geometryRow049_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow049_meanGap_numerator_no_slash geometryRow049_meanGap_numerator_parse
    geometryRow049_meanGap_denominator_parse geometryRow049_meanGap_denominator_nonzero

theorem geometryRow049_meanGap_read :
    rationalField geometryRowsJson049 "mean_gap" = .ok geometryRowsTyped049.meanGap :=
  original_rationalField_of_string geometryRowsJson049 "mean_gap" geometryRow049_meanGapText
    geometryRowsTyped049.meanGap geometryRow049_meanGap_field geometryRow049_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_meanGap_complete"
  err.flush

noncomputable def geometryRow049_jensenBoundNumeratorChars : List Char := ['1', '8', '7', '1', '7', '7', '8', '2', '9', '6', '4', '4', '4', '6', '1', '1', '3', '1', '8', '5', '3', '3', '9', '9', '6', '4', '3', '0', '4', '9', '2', '7', '1', '1', '0', '6', '5', '6', '0', '3', '0', '5', '0', '6', '7', '4', '6', '2', '1', '6', '8', '1', '5', '9', '1', '6', '8', '5', '9', '3', '9', '2', '8', '0', '8', '3', '3', '3', '7', '3', '5', '2', '8', '8', '0', '1', '1', '8', '0', '0', '5', '2', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_jensenBoundDenominatorChars : List Char := ['2', '7', '6', '7', '2', '0', '5', '0', '7', '9', '9', '8', '8', '4', '0', '9', '5', '0', '9', '1', '0', '7', '3', '1', '0', '7', '9', '6', '8', '9', '9', '5', '7', '4', '0', '5', '3', '6', '8', '0', '5', '5', '2', '0', '9', '3', '4', '6', '1', '5', '7', '9', '2', '9', '3', '1', '1', '9', '2', '9', '8', '4', '7', '8', '7', '4', '5', '0', '3', '3', '4', '9', '2', '9', '7', '7', '3', '6', '4', '0', '5', '7', '3', '9', '8', '2', '3', '6', '4', '2', '0', '7', '9', '2', '3', '7', '0', '5', '7', '5', '4', '0', '2', '7', '5', '9', '1', '0', '5', '5', '8', '8', '5', '2', '0', '7', '1', '1', '5', '8', '5', '4', '1', '8', '1']
noncomputable def geometryRow049_jensenBoundText : String := String.ofList (geometryRow049_jensenBoundNumeratorChars ++ '/' :: geometryRow049_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_jensenBound_before_field"
  err.flush

theorem geometryRow049_jensenBound_field :
    geometryRowsJson049.getObjVal? "jensen_bound" = .ok (.str geometryRow049_jensenBoundText) := by rfl

theorem geometryRow049_jensenBound_numerator_no_slash :
    geometryRow049_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow049_jensenBoundNumeratorChars = some (1871778296444611318533996430492711065603050674621681591685939280833373528801180052440000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow049_jensenBoundDenominatorChars = some (27672050799884095091073107968995740536805520934615792931192984787450334929773640573982364207923705754027591055885207115854181 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_nonzero : (27672050799884095091073107968995740536805520934615792931192984787450334929773640573982364207923705754027591055885207115854181 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_jensenBound_parse :
    parseRational geometryRow049_jensenBoundText = .ok geometryRowsTyped049.jensenBound :=
  original_rational_fraction_of_chars geometryRow049_jensenBoundNumeratorChars geometryRow049_jensenBoundDenominatorChars
    (1871778296444611318533996430492711065603050674621681591685939280833373528801180052440000000000000000000000000 : Int) (27672050799884095091073107968995740536805520934615792931192984787450334929773640573982364207923705754027591055885207115854181 : Int)
    geometryRow049_jensenBound_numerator_no_slash geometryRow049_jensenBound_numerator_parse
    geometryRow049_jensenBound_denominator_parse geometryRow049_jensenBound_denominator_nonzero

theorem geometryRow049_jensenBound_read :
    rationalField geometryRowsJson049 "jensen_bound" = .ok geometryRowsTyped049.jensenBound :=
  original_rationalField_of_string geometryRowsJson049 "jensen_bound" geometryRow049_jensenBoundText
    geometryRowsTyped049.jensenBound geometryRow049_jensenBound_field geometryRow049_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_factorMaxima_before"
  err.flush

theorem geometryRow049_factorMaxima_read :
    rationalArrayField geometryRowsJson049 "factor_maxima" = .ok geometryRowsTyped049.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_gapWeightedMeans_before"
  err.flush

theorem geometryRow049_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson049 "gap_weighted_means" = .ok geometryRowsTyped049.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow049_floorChars : List Char := ['5', '3', '5', '9', '1', '0', '9', '6', '7', '1', '1', '2', '0']
noncomputable def geometryRow049_floorText : String := String.ofList geometryRow049_floorChars

theorem geometryRow049_floor_text_read :
    geometryRowsJson049.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow049_floorText := by rfl

theorem geometryRow049_floor_chars_parse :
    SourceJson.intChars geometryRow049_floorChars = some (5359109671120 : Int) := by decide +kernel

theorem geometryRow049_floor_parse :
    parseInteger geometryRow049_floorText = .ok geometryRowsTyped049.jensenFloorQ96 := by
  simp only [geometryRow049_floorText, parseInteger, String.toList_ofList, geometryRow049_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_049 :
    decodeGeometryRow geometryRowsJson049 = .ok geometryRowsTyped049 :=
  original_geometryRow_of_fields geometryRowsJson049 geometryRowsTyped049 geometryRow049_floorText
    geometryRow049_simplexId_read geometryRow049_vertexIds_read
    geometryRow049_physicalVolume_read geometryRow049_meanGap_read
    geometryRow049_factorMaxima_read geometryRow049_gapWeightedMeans_read
    geometryRow049_jensenBound_read geometryRow049_floor_text_read geometryRow049_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_049_original_decoder_complete"
  err.flush

#print axioms geometryRow049_simplexId_read
#print axioms geometryRow049_vertexIds_read
#print axioms geometryRow049_physicalVolume_field
#print axioms geometryRow049_physicalVolume_numerator_no_slash
#print axioms geometryRow049_physicalVolume_numerator_parse
#print axioms geometryRow049_physicalVolume_denominator_parse
#print axioms geometryRow049_physicalVolume_denominator_nonzero
#print axioms geometryRow049_physicalVolume_parse
#print axioms geometryRow049_physicalVolume_read
#print axioms geometryRow049_meanGap_field
#print axioms geometryRow049_meanGap_numerator_no_slash
#print axioms geometryRow049_meanGap_numerator_parse
#print axioms geometryRow049_meanGap_denominator_parse
#print axioms geometryRow049_meanGap_denominator_nonzero
#print axioms geometryRow049_meanGap_parse
#print axioms geometryRow049_meanGap_read
#print axioms geometryRow049_jensenBound_field
#print axioms geometryRow049_jensenBound_numerator_no_slash
#print axioms geometryRow049_jensenBound_numerator_parse
#print axioms geometryRow049_jensenBound_denominator_parse
#print axioms geometryRow049_jensenBound_denominator_nonzero
#print axioms geometryRow049_jensenBound_parse
#print axioms geometryRow049_jensenBound_read
#print axioms geometryRow049_factorMaxima_read
#print axioms geometryRow049_gapWeightedMeans_read
#print axioms geometryRow049_floor_text_read
#print axioms geometryRow049_floor_chars_parse
#print axioms geometryRow049_floor_parse
#print axioms decode_geometry_Rows_049

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
