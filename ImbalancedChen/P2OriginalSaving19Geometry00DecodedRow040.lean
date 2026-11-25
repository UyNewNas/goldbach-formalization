import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000

/-! Original GeometryRow 40: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson040 : SourceJson :=
  (simplicesChunk040Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped040 : GeometryRow :=
  { simplexId := 40,
    vertexIds := #[27, 25, 24, 22, 21, 19, 18, 3, 1],
    physicalVolume := ((599395929226450143325547131 : ℚ) / (45368527680000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((42719199353 : ℚ) / (478800000000 : ℚ)), ((43063647443 : ℚ) / (478800000000 : ℚ)), ((2676931779 : ℚ) / (21280000000 : ℚ)), ((92467716653 : ℚ) / (957600000000 : ℚ)), ((86460703117 : ℚ) / (957600000000 : ℚ)), ((1442959573 : ℚ) / (21280000000 : ℚ)), ((16145814109 : ℚ) / (478800000000 : ℚ)), ((15348014141 : ℚ) / (478800000000 : ℚ)), ((14687024321 : ℚ) / (478800000000 : ℚ)), ((14686960481 : ℚ) / (478800000000 : ℚ))],
    jensenBound := ((35223405837434658723948367269812126305759393897288669593600000000000000000000000000000 : ℚ) / (1012257268353387623367415204595759891892631365432502750692765262377430426307877629433666456098717653639 : ℚ)),
    jensenFloorQ96 := (2756893735654 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_simplexId_before"
  err.flush

theorem geometryRow040_simplexId_read :
    geometryRowsJson040.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped040.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_vertexIds_before"
  err.flush

theorem geometryRow040_vertexIds_read :
    geometryRowsJson040.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped040.vertexIds := by decide +kernel

noncomputable def geometryRow040_physicalVolumeNumeratorChars : List Char := ['5', '9', '9', '3', '9', '5', '9', '2', '9', '2', '2', '6', '4', '5', '0', '1', '4', '3', '3', '2', '5', '5', '4', '7', '1', '3', '1']
noncomputable def geometryRow040_physicalVolumeDenominatorChars : List Char := ['4', '5', '3', '6', '8', '5', '2', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_physicalVolumeText : String := String.ofList (geometryRow040_physicalVolumeNumeratorChars ++ '/' :: geometryRow040_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_physicalVolume_before_field"
  err.flush

theorem geometryRow040_physicalVolume_field :
    geometryRowsJson040.getObjVal? "physical_volume" = .ok (.str geometryRow040_physicalVolumeText) := by rfl

theorem geometryRow040_physicalVolume_numerator_no_slash :
    geometryRow040_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeNumeratorChars = some (599395929226450143325547131 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeDenominatorChars = some (45368527680000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_nonzero : (45368527680000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_physicalVolume_parse :
    parseRational geometryRow040_physicalVolumeText = .ok geometryRowsTyped040.physicalVolume :=
  original_rational_fraction_of_chars geometryRow040_physicalVolumeNumeratorChars geometryRow040_physicalVolumeDenominatorChars
    (599395929226450143325547131 : Int) (45368527680000000000000000000000000000000000000000000 : Int)
    geometryRow040_physicalVolume_numerator_no_slash geometryRow040_physicalVolume_numerator_parse
    geometryRow040_physicalVolume_denominator_parse geometryRow040_physicalVolume_denominator_nonzero

theorem geometryRow040_physicalVolume_read :
    rationalField geometryRowsJson040 "physical_volume" = .ok geometryRowsTyped040.physicalVolume :=
  original_rationalField_of_string geometryRowsJson040 "physical_volume" geometryRow040_physicalVolumeText
    geometryRowsTyped040.physicalVolume geometryRow040_physicalVolume_field geometryRow040_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_physicalVolume_complete"
  err.flush

noncomputable def geometryRow040_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow040_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_meanGapText : String := String.ofList (geometryRow040_meanGapNumeratorChars ++ '/' :: geometryRow040_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_meanGap_before_field"
  err.flush

theorem geometryRow040_meanGap_field :
    geometryRowsJson040.getObjVal? "mean_gap" = .ok (.str geometryRow040_meanGapText) := by rfl

theorem geometryRow040_meanGap_numerator_no_slash :
    geometryRow040_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_meanGap_numerator_parse :
    SourceJson.intChars geometryRow040_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_parse :
    SourceJson.intChars geometryRow040_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_meanGap_parse :
    parseRational geometryRow040_meanGapText = .ok geometryRowsTyped040.meanGap :=
  original_rational_fraction_of_chars geometryRow040_meanGapNumeratorChars geometryRow040_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow040_meanGap_numerator_no_slash geometryRow040_meanGap_numerator_parse
    geometryRow040_meanGap_denominator_parse geometryRow040_meanGap_denominator_nonzero

theorem geometryRow040_meanGap_read :
    rationalField geometryRowsJson040 "mean_gap" = .ok geometryRowsTyped040.meanGap :=
  original_rationalField_of_string geometryRowsJson040 "mean_gap" geometryRow040_meanGapText
    geometryRowsTyped040.meanGap geometryRow040_meanGap_field geometryRow040_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_meanGap_complete"
  err.flush

noncomputable def geometryRow040_jensenBoundNumeratorChars : List Char := ['3', '5', '2', '2', '3', '4', '0', '5', '8', '3', '7', '4', '3', '4', '6', '5', '8', '7', '2', '3', '9', '4', '8', '3', '6', '7', '2', '6', '9', '8', '1', '2', '1', '2', '6', '3', '0', '5', '7', '5', '9', '3', '9', '3', '8', '9', '7', '2', '8', '8', '6', '6', '9', '5', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_jensenBoundDenominatorChars : List Char := ['1', '0', '1', '2', '2', '5', '7', '2', '6', '8', '3', '5', '3', '3', '8', '7', '6', '2', '3', '3', '6', '7', '4', '1', '5', '2', '0', '4', '5', '9', '5', '7', '5', '9', '8', '9', '1', '8', '9', '2', '6', '3', '1', '3', '6', '5', '4', '3', '2', '5', '0', '2', '7', '5', '0', '6', '9', '2', '7', '6', '5', '2', '6', '2', '3', '7', '7', '4', '3', '0', '4', '2', '6', '3', '0', '7', '8', '7', '7', '6', '2', '9', '4', '3', '3', '6', '6', '6', '4', '5', '6', '0', '9', '8', '7', '1', '7', '6', '5', '3', '6', '3', '9']
noncomputable def geometryRow040_jensenBoundText : String := String.ofList (geometryRow040_jensenBoundNumeratorChars ++ '/' :: geometryRow040_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_jensenBound_before_field"
  err.flush

theorem geometryRow040_jensenBound_field :
    geometryRowsJson040.getObjVal? "jensen_bound" = .ok (.str geometryRow040_jensenBoundText) := by rfl

theorem geometryRow040_jensenBound_numerator_no_slash :
    geometryRow040_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow040_jensenBoundNumeratorChars = some (35223405837434658723948367269812126305759393897288669593600000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow040_jensenBoundDenominatorChars = some (1012257268353387623367415204595759891892631365432502750692765262377430426307877629433666456098717653639 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_nonzero : (1012257268353387623367415204595759891892631365432502750692765262377430426307877629433666456098717653639 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_jensenBound_parse :
    parseRational geometryRow040_jensenBoundText = .ok geometryRowsTyped040.jensenBound :=
  original_rational_fraction_of_chars geometryRow040_jensenBoundNumeratorChars geometryRow040_jensenBoundDenominatorChars
    (35223405837434658723948367269812126305759393897288669593600000000000000000000000000000 : Int) (1012257268353387623367415204595759891892631365432502750692765262377430426307877629433666456098717653639 : Int)
    geometryRow040_jensenBound_numerator_no_slash geometryRow040_jensenBound_numerator_parse
    geometryRow040_jensenBound_denominator_parse geometryRow040_jensenBound_denominator_nonzero

theorem geometryRow040_jensenBound_read :
    rationalField geometryRowsJson040 "jensen_bound" = .ok geometryRowsTyped040.jensenBound :=
  original_rationalField_of_string geometryRowsJson040 "jensen_bound" geometryRow040_jensenBoundText
    geometryRowsTyped040.jensenBound geometryRow040_jensenBound_field geometryRow040_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_factorMaxima_before"
  err.flush

theorem geometryRow040_factorMaxima_read :
    rationalArrayField geometryRowsJson040 "factor_maxima" = .ok geometryRowsTyped040.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_gapWeightedMeans_before"
  err.flush

theorem geometryRow040_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson040 "gap_weighted_means" = .ok geometryRowsTyped040.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow040_floorChars : List Char := ['2', '7', '5', '6', '8', '9', '3', '7', '3', '5', '6', '5', '4']
noncomputable def geometryRow040_floorText : String := String.ofList geometryRow040_floorChars

theorem geometryRow040_floor_text_read :
    geometryRowsJson040.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow040_floorText := by rfl

theorem geometryRow040_floor_chars_parse :
    SourceJson.intChars geometryRow040_floorChars = some (2756893735654 : Int) := by decide +kernel

theorem geometryRow040_floor_parse :
    parseInteger geometryRow040_floorText = .ok geometryRowsTyped040.jensenFloorQ96 := by
  simp only [geometryRow040_floorText, parseInteger, String.toList_ofList, geometryRow040_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_040 :
    decodeGeometryRow geometryRowsJson040 = .ok geometryRowsTyped040 :=
  original_geometryRow_of_fields geometryRowsJson040 geometryRowsTyped040 geometryRow040_floorText
    geometryRow040_simplexId_read geometryRow040_vertexIds_read
    geometryRow040_physicalVolume_read geometryRow040_meanGap_read
    geometryRow040_factorMaxima_read geometryRow040_gapWeightedMeans_read
    geometryRow040_jensenBound_read geometryRow040_floor_text_read geometryRow040_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_040_original_decoder_complete"
  err.flush

#print axioms geometryRow040_simplexId_read
#print axioms geometryRow040_vertexIds_read
#print axioms geometryRow040_physicalVolume_field
#print axioms geometryRow040_physicalVolume_numerator_no_slash
#print axioms geometryRow040_physicalVolume_numerator_parse
#print axioms geometryRow040_physicalVolume_denominator_parse
#print axioms geometryRow040_physicalVolume_denominator_nonzero
#print axioms geometryRow040_physicalVolume_parse
#print axioms geometryRow040_physicalVolume_read
#print axioms geometryRow040_meanGap_field
#print axioms geometryRow040_meanGap_numerator_no_slash
#print axioms geometryRow040_meanGap_numerator_parse
#print axioms geometryRow040_meanGap_denominator_parse
#print axioms geometryRow040_meanGap_denominator_nonzero
#print axioms geometryRow040_meanGap_parse
#print axioms geometryRow040_meanGap_read
#print axioms geometryRow040_jensenBound_field
#print axioms geometryRow040_jensenBound_numerator_no_slash
#print axioms geometryRow040_jensenBound_numerator_parse
#print axioms geometryRow040_jensenBound_denominator_parse
#print axioms geometryRow040_jensenBound_denominator_nonzero
#print axioms geometryRow040_jensenBound_parse
#print axioms geometryRow040_jensenBound_read
#print axioms geometryRow040_factorMaxima_read
#print axioms geometryRow040_gapWeightedMeans_read
#print axioms geometryRow040_floor_text_read
#print axioms geometryRow040_floor_chars_parse
#print axioms geometryRow040_floor_parse
#print axioms decode_geometry_Rows_040

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
