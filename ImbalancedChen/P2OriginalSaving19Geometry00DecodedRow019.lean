import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400

/-! Original GeometryRow 19: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson019 : SourceJson :=
  (simplicesChunk019Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped019 : GeometryRow :=
  { simplexId := 19,
    vertexIds := #[27, 25, 23, 21, 19, 18, 3, 2, 0],
    physicalVolume := ((120056988629258812332412000817347 : ℚ) / (2303870546250000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((19865249 : ℚ) / (23712000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((8140597 : ℚ) / (228000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((22264759370347029437 : ℚ) / (247298511751200000000 : ℚ)), ((11272324164695253901 : ℚ) / (123649255875600000000 : ℚ)), ((6154706075566283657 : ℚ) / (49459702350240000000 : ℚ)), ((1819017333797814317 : ℚ) / (19022962442400000000 : ℚ)), ((7343332620581922203 : ℚ) / (82432837250400000000 : ℚ)), ((3380092934970656677 : ℚ) / (49459702350240000000 : ℚ)), ((2075507915167048759 : ℚ) / (61824627937800000000 : ℚ)), ((674666494011670717 : ℚ) / (20608209312600000000 : ℚ)), ((243302144856710377 : ℚ) / (7728078492225000000 : ℚ)), ((3843288776785145647 : ℚ) / (123649255875600000000 : ℚ))],
    jensenBound := ((37389405725156709988659285772106982529112298739686065521070427758589149771475631240196678601482265175098458947290072560396491216858042845049651200000000000000000000000000 : ℚ) / (136909671861334124208315972389781397970828220259118054022887970794723944285644125199973622165428196389536421846976925789923356884562225167782639571048799994672678808415903127410965853 : ℚ)),
    jensenFloorQ96 := (21636849119796108 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_simplexId_before"
  err.flush

theorem geometryRow019_simplexId_read :
    geometryRowsJson019.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped019.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_vertexIds_before"
  err.flush

theorem geometryRow019_vertexIds_read :
    geometryRowsJson019.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped019.vertexIds := by decide +kernel

noncomputable def geometryRow019_physicalVolumeNumeratorChars : List Char := ['1', '2', '0', '0', '5', '6', '9', '8', '8', '6', '2', '9', '2', '5', '8', '8', '1', '2', '3', '3', '2', '4', '1', '2', '0', '0', '0', '8', '1', '7', '3', '4', '7']
noncomputable def geometryRow019_physicalVolumeDenominatorChars : List Char := ['2', '3', '0', '3', '8', '7', '0', '5', '4', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_physicalVolumeText : String := String.ofList (geometryRow019_physicalVolumeNumeratorChars ++ '/' :: geometryRow019_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_physicalVolume_before_field"
  err.flush

theorem geometryRow019_physicalVolume_field :
    geometryRowsJson019.getObjVal? "physical_volume" = .ok (.str geometryRow019_physicalVolumeText) := by rfl

theorem geometryRow019_physicalVolume_numerator_no_slash :
    geometryRow019_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeNumeratorChars = some (120056988629258812332412000817347 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeDenominatorChars = some (2303870546250000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_nonzero : (2303870546250000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_physicalVolume_parse :
    parseRational geometryRow019_physicalVolumeText = .ok geometryRowsTyped019.physicalVolume :=
  original_rational_fraction_of_chars geometryRow019_physicalVolumeNumeratorChars geometryRow019_physicalVolumeDenominatorChars
    (120056988629258812332412000817347 : Int) (2303870546250000000000000000000000000000000000000000000 : Int)
    geometryRow019_physicalVolume_numerator_no_slash geometryRow019_physicalVolume_numerator_parse
    geometryRow019_physicalVolume_denominator_parse geometryRow019_physicalVolume_denominator_nonzero

theorem geometryRow019_physicalVolume_read :
    rationalField geometryRowsJson019 "physical_volume" = .ok geometryRowsTyped019.physicalVolume :=
  original_rationalField_of_string geometryRowsJson019 "physical_volume" geometryRow019_physicalVolumeText
    geometryRowsTyped019.physicalVolume geometryRow019_physicalVolume_field geometryRow019_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_physicalVolume_complete"
  err.flush

noncomputable def geometryRow019_meanGapNumeratorChars : List Char := ['1', '9', '8', '6', '5', '2', '4', '9']
noncomputable def geometryRow019_meanGapDenominatorChars : List Char := ['2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_meanGapText : String := String.ofList (geometryRow019_meanGapNumeratorChars ++ '/' :: geometryRow019_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_meanGap_before_field"
  err.flush

theorem geometryRow019_meanGap_field :
    geometryRowsJson019.getObjVal? "mean_gap" = .ok (.str geometryRow019_meanGapText) := by rfl

theorem geometryRow019_meanGap_numerator_no_slash :
    geometryRow019_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_meanGap_numerator_parse :
    SourceJson.intChars geometryRow019_meanGapNumeratorChars = some (19865249 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_parse :
    SourceJson.intChars geometryRow019_meanGapDenominatorChars = some (23712000000 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_nonzero : (23712000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_meanGap_parse :
    parseRational geometryRow019_meanGapText = .ok geometryRowsTyped019.meanGap :=
  original_rational_fraction_of_chars geometryRow019_meanGapNumeratorChars geometryRow019_meanGapDenominatorChars
    (19865249 : Int) (23712000000 : Int)
    geometryRow019_meanGap_numerator_no_slash geometryRow019_meanGap_numerator_parse
    geometryRow019_meanGap_denominator_parse geometryRow019_meanGap_denominator_nonzero

theorem geometryRow019_meanGap_read :
    rationalField geometryRowsJson019 "mean_gap" = .ok geometryRowsTyped019.meanGap :=
  original_rationalField_of_string geometryRowsJson019 "mean_gap" geometryRow019_meanGapText
    geometryRowsTyped019.meanGap geometryRow019_meanGap_field geometryRow019_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_meanGap_complete"
  err.flush

noncomputable def geometryRow019_jensenBoundNumeratorChars : List Char := ['3', '7', '3', '8', '9', '4', '0', '5', '7', '2', '5', '1', '5', '6', '7', '0', '9', '9', '8', '8', '6', '5', '9', '2', '8', '5', '7', '7', '2', '1', '0', '6', '9', '8', '2', '5', '2', '9', '1', '1', '2', '2', '9', '8', '7', '3', '9', '6', '8', '6', '0', '6', '5', '5', '2', '1', '0', '7', '0', '4', '2', '7', '7', '5', '8', '5', '8', '9', '1', '4', '9', '7', '7', '1', '4', '7', '5', '6', '3', '1', '2', '4', '0', '1', '9', '6', '6', '7', '8', '6', '0', '1', '4', '8', '2', '2', '6', '5', '1', '7', '5', '0', '9', '8', '4', '5', '8', '9', '4', '7', '2', '9', '0', '0', '7', '2', '5', '6', '0', '3', '9', '6', '4', '9', '1', '2', '1', '6', '8', '5', '8', '0', '4', '2', '8', '4', '5', '0', '4', '9', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_jensenBoundDenominatorChars : List Char := ['1', '3', '6', '9', '0', '9', '6', '7', '1', '8', '6', '1', '3', '3', '4', '1', '2', '4', '2', '0', '8', '3', '1', '5', '9', '7', '2', '3', '8', '9', '7', '8', '1', '3', '9', '7', '9', '7', '0', '8', '2', '8', '2', '2', '0', '2', '5', '9', '1', '1', '8', '0', '5', '4', '0', '2', '2', '8', '8', '7', '9', '7', '0', '7', '9', '4', '7', '2', '3', '9', '4', '4', '2', '8', '5', '6', '4', '4', '1', '2', '5', '1', '9', '9', '9', '7', '3', '6', '2', '2', '1', '6', '5', '4', '2', '8', '1', '9', '6', '3', '8', '9', '5', '3', '6', '4', '2', '1', '8', '4', '6', '9', '7', '6', '9', '2', '5', '7', '8', '9', '9', '2', '3', '3', '5', '6', '8', '8', '4', '5', '6', '2', '2', '2', '5', '1', '6', '7', '7', '8', '2', '6', '3', '9', '5', '7', '1', '0', '4', '8', '7', '9', '9', '9', '9', '4', '6', '7', '2', '6', '7', '8', '8', '0', '8', '4', '1', '5', '9', '0', '3', '1', '2', '7', '4', '1', '0', '9', '6', '5', '8', '5', '3']
noncomputable def geometryRow019_jensenBoundText : String := String.ofList (geometryRow019_jensenBoundNumeratorChars ++ '/' :: geometryRow019_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_jensenBound_before_field"
  err.flush

theorem geometryRow019_jensenBound_field :
    geometryRowsJson019.getObjVal? "jensen_bound" = .ok (.str geometryRow019_jensenBoundText) := by rfl

theorem geometryRow019_jensenBound_numerator_no_slash :
    geometryRow019_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow019_jensenBoundNumeratorChars = some (37389405725156709988659285772106982529112298739686065521070427758589149771475631240196678601482265175098458947290072560396491216858042845049651200000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow019_jensenBoundDenominatorChars = some (136909671861334124208315972389781397970828220259118054022887970794723944285644125199973622165428196389536421846976925789923356884562225167782639571048799994672678808415903127410965853 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_nonzero : (136909671861334124208315972389781397970828220259118054022887970794723944285644125199973622165428196389536421846976925789923356884562225167782639571048799994672678808415903127410965853 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_jensenBound_parse :
    parseRational geometryRow019_jensenBoundText = .ok geometryRowsTyped019.jensenBound :=
  original_rational_fraction_of_chars geometryRow019_jensenBoundNumeratorChars geometryRow019_jensenBoundDenominatorChars
    (37389405725156709988659285772106982529112298739686065521070427758589149771475631240196678601482265175098458947290072560396491216858042845049651200000000000000000000000000 : Int) (136909671861334124208315972389781397970828220259118054022887970794723944285644125199973622165428196389536421846976925789923356884562225167782639571048799994672678808415903127410965853 : Int)
    geometryRow019_jensenBound_numerator_no_slash geometryRow019_jensenBound_numerator_parse
    geometryRow019_jensenBound_denominator_parse geometryRow019_jensenBound_denominator_nonzero

theorem geometryRow019_jensenBound_read :
    rationalField geometryRowsJson019 "jensen_bound" = .ok geometryRowsTyped019.jensenBound :=
  original_rationalField_of_string geometryRowsJson019 "jensen_bound" geometryRow019_jensenBoundText
    geometryRowsTyped019.jensenBound geometryRow019_jensenBound_field geometryRow019_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_factorMaxima_before"
  err.flush

theorem geometryRow019_factorMaxima_read :
    rationalArrayField geometryRowsJson019 "factor_maxima" = .ok geometryRowsTyped019.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_gapWeightedMeans_before"
  err.flush

theorem geometryRow019_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson019 "gap_weighted_means" = .ok geometryRowsTyped019.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow019_floorChars : List Char := ['2', '1', '6', '3', '6', '8', '4', '9', '1', '1', '9', '7', '9', '6', '1', '0', '8']
noncomputable def geometryRow019_floorText : String := String.ofList geometryRow019_floorChars

theorem geometryRow019_floor_text_read :
    geometryRowsJson019.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow019_floorText := by rfl

theorem geometryRow019_floor_chars_parse :
    SourceJson.intChars geometryRow019_floorChars = some (21636849119796108 : Int) := by decide +kernel

theorem geometryRow019_floor_parse :
    parseInteger geometryRow019_floorText = .ok geometryRowsTyped019.jensenFloorQ96 := by
  simp only [geometryRow019_floorText, parseInteger, String.toList_ofList, geometryRow019_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_019 :
    decodeGeometryRow geometryRowsJson019 = .ok geometryRowsTyped019 :=
  original_geometryRow_of_fields geometryRowsJson019 geometryRowsTyped019 geometryRow019_floorText
    geometryRow019_simplexId_read geometryRow019_vertexIds_read
    geometryRow019_physicalVolume_read geometryRow019_meanGap_read
    geometryRow019_factorMaxima_read geometryRow019_gapWeightedMeans_read
    geometryRow019_jensenBound_read geometryRow019_floor_text_read geometryRow019_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_019_original_decoder_complete"
  err.flush

#print axioms geometryRow019_simplexId_read
#print axioms geometryRow019_vertexIds_read
#print axioms geometryRow019_physicalVolume_field
#print axioms geometryRow019_physicalVolume_numerator_no_slash
#print axioms geometryRow019_physicalVolume_numerator_parse
#print axioms geometryRow019_physicalVolume_denominator_parse
#print axioms geometryRow019_physicalVolume_denominator_nonzero
#print axioms geometryRow019_physicalVolume_parse
#print axioms geometryRow019_physicalVolume_read
#print axioms geometryRow019_meanGap_field
#print axioms geometryRow019_meanGap_numerator_no_slash
#print axioms geometryRow019_meanGap_numerator_parse
#print axioms geometryRow019_meanGap_denominator_parse
#print axioms geometryRow019_meanGap_denominator_nonzero
#print axioms geometryRow019_meanGap_parse
#print axioms geometryRow019_meanGap_read
#print axioms geometryRow019_jensenBound_field
#print axioms geometryRow019_jensenBound_numerator_no_slash
#print axioms geometryRow019_jensenBound_numerator_parse
#print axioms geometryRow019_jensenBound_denominator_parse
#print axioms geometryRow019_jensenBound_denominator_nonzero
#print axioms geometryRow019_jensenBound_parse
#print axioms geometryRow019_jensenBound_read
#print axioms geometryRow019_factorMaxima_read
#print axioms geometryRow019_gapWeightedMeans_read
#print axioms geometryRow019_floor_text_read
#print axioms geometryRow019_floor_chars_parse
#print axioms geometryRow019_floor_parse
#print axioms decode_geometry_Rows_019

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
