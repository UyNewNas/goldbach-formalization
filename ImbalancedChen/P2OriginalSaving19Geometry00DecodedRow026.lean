import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600

/-! Original GeometryRow 26: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson026 : SourceJson :=
  (simplicesChunk026Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped026 : GeometryRow :=
  { simplexId := 26,
    vertexIds := #[27, 25, 23, 21, 19, 17, 16, 12, 2],
    physicalVolume := ((15064908990533198024920432613 : ℚ) / (431290870070457458496093750000000000000000000000000 : ℚ)),
    meanGap := ((164915953 : ℚ) / (198432000000 : ℚ)),
    factorMaxima := #[((39234443 : ℚ) / (416000000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((7359347 : ℚ) / (104000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))],
    gapWeightedMeans := #[((17183097055000847497 : ℚ) / (197476048879200000000 : ℚ)), ((543902458709131631 : ℚ) / (6171126527475000000 : ℚ)), ((2496883790914559539 : ℚ) / (19747604887920000000 : ℚ)), ((374501267665815103 : ℚ) / (3797616324600000000 : ℚ)), ((4525535290364914841 : ℚ) / (49369012219800000000 : ℚ)), ((652001958214573609 : ℚ) / (9873802443960000000 : ℚ)), ((3257071848992018893 : ℚ) / (98738024439600000000 : ℚ)), ((1058269823576080879 : ℚ) / (32912674813200000000 : ℚ)), ((1028631489725725519 : ℚ) / (32912674813200000000 : ℚ)), ((61861772812538519 : ℚ) / (2057042175825000000 : ℚ))],
    jensenBound := ((39246998978543081880969326079717645688664732030369787338888570659753193577049116804893189471288386078598887524410019127336287577387286503882752000000000000000000000000 : ℚ) / (195029754388306622377083202125075336710342068524292675257024107268714187497156982695696499323413931739893432783113089344688470927884205498090289315498975095588673203447188306760253 : ℚ)),
    jensenFloorQ96 := (15943554987400485 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_simplexId_before"
  err.flush

theorem geometryRow026_simplexId_read :
    geometryRowsJson026.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped026.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_vertexIds_before"
  err.flush

theorem geometryRow026_vertexIds_read :
    geometryRowsJson026.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped026.vertexIds := by decide +kernel

noncomputable def geometryRow026_physicalVolumeNumeratorChars : List Char := ['1', '5', '0', '6', '4', '9', '0', '8', '9', '9', '0', '5', '3', '3', '1', '9', '8', '0', '2', '4', '9', '2', '0', '4', '3', '2', '6', '1', '3']
noncomputable def geometryRow026_physicalVolumeDenominatorChars : List Char := ['4', '3', '1', '2', '9', '0', '8', '7', '0', '0', '7', '0', '4', '5', '7', '4', '5', '8', '4', '9', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_physicalVolumeText : String := String.ofList (geometryRow026_physicalVolumeNumeratorChars ++ '/' :: geometryRow026_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_physicalVolume_before_field"
  err.flush

theorem geometryRow026_physicalVolume_field :
    geometryRowsJson026.getObjVal? "physical_volume" = .ok (.str geometryRow026_physicalVolumeText) := by rfl

theorem geometryRow026_physicalVolume_numerator_no_slash :
    geometryRow026_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeNumeratorChars = some (15064908990533198024920432613 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeDenominatorChars = some (431290870070457458496093750000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_nonzero : (431290870070457458496093750000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_physicalVolume_parse :
    parseRational geometryRow026_physicalVolumeText = .ok geometryRowsTyped026.physicalVolume :=
  original_rational_fraction_of_chars geometryRow026_physicalVolumeNumeratorChars geometryRow026_physicalVolumeDenominatorChars
    (15064908990533198024920432613 : Int) (431290870070457458496093750000000000000000000000000 : Int)
    geometryRow026_physicalVolume_numerator_no_slash geometryRow026_physicalVolume_numerator_parse
    geometryRow026_physicalVolume_denominator_parse geometryRow026_physicalVolume_denominator_nonzero

theorem geometryRow026_physicalVolume_read :
    rationalField geometryRowsJson026 "physical_volume" = .ok geometryRowsTyped026.physicalVolume :=
  original_rationalField_of_string geometryRowsJson026 "physical_volume" geometryRow026_physicalVolumeText
    geometryRowsTyped026.physicalVolume geometryRow026_physicalVolume_field geometryRow026_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_physicalVolume_complete"
  err.flush

noncomputable def geometryRow026_meanGapNumeratorChars : List Char := ['1', '6', '4', '9', '1', '5', '9', '5', '3']
noncomputable def geometryRow026_meanGapDenominatorChars : List Char := ['1', '9', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_meanGapText : String := String.ofList (geometryRow026_meanGapNumeratorChars ++ '/' :: geometryRow026_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_meanGap_before_field"
  err.flush

theorem geometryRow026_meanGap_field :
    geometryRowsJson026.getObjVal? "mean_gap" = .ok (.str geometryRow026_meanGapText) := by rfl

theorem geometryRow026_meanGap_numerator_no_slash :
    geometryRow026_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_meanGap_numerator_parse :
    SourceJson.intChars geometryRow026_meanGapNumeratorChars = some (164915953 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_parse :
    SourceJson.intChars geometryRow026_meanGapDenominatorChars = some (198432000000 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_nonzero : (198432000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_meanGap_parse :
    parseRational geometryRow026_meanGapText = .ok geometryRowsTyped026.meanGap :=
  original_rational_fraction_of_chars geometryRow026_meanGapNumeratorChars geometryRow026_meanGapDenominatorChars
    (164915953 : Int) (198432000000 : Int)
    geometryRow026_meanGap_numerator_no_slash geometryRow026_meanGap_numerator_parse
    geometryRow026_meanGap_denominator_parse geometryRow026_meanGap_denominator_nonzero

theorem geometryRow026_meanGap_read :
    rationalField geometryRowsJson026 "mean_gap" = .ok geometryRowsTyped026.meanGap :=
  original_rationalField_of_string geometryRowsJson026 "mean_gap" geometryRow026_meanGapText
    geometryRowsTyped026.meanGap geometryRow026_meanGap_field geometryRow026_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_meanGap_complete"
  err.flush

noncomputable def geometryRow026_jensenBoundNumeratorChars : List Char := ['3', '9', '2', '4', '6', '9', '9', '8', '9', '7', '8', '5', '4', '3', '0', '8', '1', '8', '8', '0', '9', '6', '9', '3', '2', '6', '0', '7', '9', '7', '1', '7', '6', '4', '5', '6', '8', '8', '6', '6', '4', '7', '3', '2', '0', '3', '0', '3', '6', '9', '7', '8', '7', '3', '3', '8', '8', '8', '8', '5', '7', '0', '6', '5', '9', '7', '5', '3', '1', '9', '3', '5', '7', '7', '0', '4', '9', '1', '1', '6', '8', '0', '4', '8', '9', '3', '1', '8', '9', '4', '7', '1', '2', '8', '8', '3', '8', '6', '0', '7', '8', '5', '9', '8', '8', '8', '7', '5', '2', '4', '4', '1', '0', '0', '1', '9', '1', '2', '7', '3', '3', '6', '2', '8', '7', '5', '7', '7', '3', '8', '7', '2', '8', '6', '5', '0', '3', '8', '8', '2', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_jensenBoundDenominatorChars : List Char := ['1', '9', '5', '0', '2', '9', '7', '5', '4', '3', '8', '8', '3', '0', '6', '6', '2', '2', '3', '7', '7', '0', '8', '3', '2', '0', '2', '1', '2', '5', '0', '7', '5', '3', '3', '6', '7', '1', '0', '3', '4', '2', '0', '6', '8', '5', '2', '4', '2', '9', '2', '6', '7', '5', '2', '5', '7', '0', '2', '4', '1', '0', '7', '2', '6', '8', '7', '1', '4', '1', '8', '7', '4', '9', '7', '1', '5', '6', '9', '8', '2', '6', '9', '5', '6', '9', '6', '4', '9', '9', '3', '2', '3', '4', '1', '3', '9', '3', '1', '7', '3', '9', '8', '9', '3', '4', '3', '2', '7', '8', '3', '1', '1', '3', '0', '8', '9', '3', '4', '4', '6', '8', '8', '4', '7', '0', '9', '2', '7', '8', '8', '4', '2', '0', '5', '4', '9', '8', '0', '9', '0', '2', '8', '9', '3', '1', '5', '4', '9', '8', '9', '7', '5', '0', '9', '5', '5', '8', '8', '6', '7', '3', '2', '0', '3', '4', '4', '7', '1', '8', '8', '3', '0', '6', '7', '6', '0', '2', '5', '3']
noncomputable def geometryRow026_jensenBoundText : String := String.ofList (geometryRow026_jensenBoundNumeratorChars ++ '/' :: geometryRow026_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_jensenBound_before_field"
  err.flush

theorem geometryRow026_jensenBound_field :
    geometryRowsJson026.getObjVal? "jensen_bound" = .ok (.str geometryRow026_jensenBoundText) := by rfl

theorem geometryRow026_jensenBound_numerator_no_slash :
    geometryRow026_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow026_jensenBoundNumeratorChars = some (39246998978543081880969326079717645688664732030369787338888570659753193577049116804893189471288386078598887524410019127336287577387286503882752000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow026_jensenBoundDenominatorChars = some (195029754388306622377083202125075336710342068524292675257024107268714187497156982695696499323413931739893432783113089344688470927884205498090289315498975095588673203447188306760253 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_nonzero : (195029754388306622377083202125075336710342068524292675257024107268714187497156982695696499323413931739893432783113089344688470927884205498090289315498975095588673203447188306760253 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_jensenBound_parse :
    parseRational geometryRow026_jensenBoundText = .ok geometryRowsTyped026.jensenBound :=
  original_rational_fraction_of_chars geometryRow026_jensenBoundNumeratorChars geometryRow026_jensenBoundDenominatorChars
    (39246998978543081880969326079717645688664732030369787338888570659753193577049116804893189471288386078598887524410019127336287577387286503882752000000000000000000000000 : Int) (195029754388306622377083202125075336710342068524292675257024107268714187497156982695696499323413931739893432783113089344688470927884205498090289315498975095588673203447188306760253 : Int)
    geometryRow026_jensenBound_numerator_no_slash geometryRow026_jensenBound_numerator_parse
    geometryRow026_jensenBound_denominator_parse geometryRow026_jensenBound_denominator_nonzero

theorem geometryRow026_jensenBound_read :
    rationalField geometryRowsJson026 "jensen_bound" = .ok geometryRowsTyped026.jensenBound :=
  original_rationalField_of_string geometryRowsJson026 "jensen_bound" geometryRow026_jensenBoundText
    geometryRowsTyped026.jensenBound geometryRow026_jensenBound_field geometryRow026_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_factorMaxima_before"
  err.flush

theorem geometryRow026_factorMaxima_read :
    rationalArrayField geometryRowsJson026 "factor_maxima" = .ok geometryRowsTyped026.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_gapWeightedMeans_before"
  err.flush

theorem geometryRow026_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson026 "gap_weighted_means" = .ok geometryRowsTyped026.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow026_floorChars : List Char := ['1', '5', '9', '4', '3', '5', '5', '4', '9', '8', '7', '4', '0', '0', '4', '8', '5']
noncomputable def geometryRow026_floorText : String := String.ofList geometryRow026_floorChars

theorem geometryRow026_floor_text_read :
    geometryRowsJson026.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow026_floorText := by rfl

theorem geometryRow026_floor_chars_parse :
    SourceJson.intChars geometryRow026_floorChars = some (15943554987400485 : Int) := by decide +kernel

theorem geometryRow026_floor_parse :
    parseInteger geometryRow026_floorText = .ok geometryRowsTyped026.jensenFloorQ96 := by
  simp only [geometryRow026_floorText, parseInteger, String.toList_ofList, geometryRow026_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_026 :
    decodeGeometryRow geometryRowsJson026 = .ok geometryRowsTyped026 :=
  original_geometryRow_of_fields geometryRowsJson026 geometryRowsTyped026 geometryRow026_floorText
    geometryRow026_simplexId_read geometryRow026_vertexIds_read
    geometryRow026_physicalVolume_read geometryRow026_meanGap_read
    geometryRow026_factorMaxima_read geometryRow026_gapWeightedMeans_read
    geometryRow026_jensenBound_read geometryRow026_floor_text_read geometryRow026_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_026_original_decoder_complete"
  err.flush

#print axioms geometryRow026_simplexId_read
#print axioms geometryRow026_vertexIds_read
#print axioms geometryRow026_physicalVolume_field
#print axioms geometryRow026_physicalVolume_numerator_no_slash
#print axioms geometryRow026_physicalVolume_numerator_parse
#print axioms geometryRow026_physicalVolume_denominator_parse
#print axioms geometryRow026_physicalVolume_denominator_nonzero
#print axioms geometryRow026_physicalVolume_parse
#print axioms geometryRow026_physicalVolume_read
#print axioms geometryRow026_meanGap_field
#print axioms geometryRow026_meanGap_numerator_no_slash
#print axioms geometryRow026_meanGap_numerator_parse
#print axioms geometryRow026_meanGap_denominator_parse
#print axioms geometryRow026_meanGap_denominator_nonzero
#print axioms geometryRow026_meanGap_parse
#print axioms geometryRow026_meanGap_read
#print axioms geometryRow026_jensenBound_field
#print axioms geometryRow026_jensenBound_numerator_no_slash
#print axioms geometryRow026_jensenBound_numerator_parse
#print axioms geometryRow026_jensenBound_denominator_parse
#print axioms geometryRow026_jensenBound_denominator_nonzero
#print axioms geometryRow026_jensenBound_parse
#print axioms geometryRow026_jensenBound_read
#print axioms geometryRow026_factorMaxima_read
#print axioms geometryRow026_gapWeightedMeans_read
#print axioms geometryRow026_floor_text_read
#print axioms geometryRow026_floor_chars_parse
#print axioms geometryRow026_floor_parse
#print axioms decode_geometry_Rows_026

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
