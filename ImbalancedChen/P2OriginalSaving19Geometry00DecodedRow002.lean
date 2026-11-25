import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000

/-! Original GeometryRow 2: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson002 : SourceJson :=
  (simplicesChunk002Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped002 : GeometryRow :=
  { simplexId := 2,
    vertexIds := #[27, 25, 11, 9, 7, 5, 4, 2, 0],
    physicalVolume := ((6939348704700313419566100996434862557187457829 : ℚ) / (18612850368752640000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((118628487712297 : ℚ) / (1262861600000000 : ℚ)), ((59812184417151 : ℚ) / (631430800000000 : ℚ)), ((1366339008573241 : ℚ) / (11365754400000000 : ℚ)), ((112784147789597 : ℚ) / (1262861600000000 : ℚ)), ((309373230498719 : ℚ) / (3788584800000000 : ℚ)), ((827382821497229 : ℚ) / (11365754400000000 : ℚ)), ((104482022467351 : ℚ) / (2841438600000000 : ℚ)), ((190628979347 : ℚ) / (5464305000000 : ℚ)), ((188228960033 : ℚ) / (5464305000000 : ℚ)), ((184615135085879 : ℚ) / (5682877200000000 : ℚ))],
    jensenBound := ((155250243714682791822465894328974525803799189888080353063872641627780797090987733076590030659895804674668800000000000000000000 : ℚ) / (193712951315668674133828366806141361807320508001423280035514659184527785248639627386239434682310181745394739157950139800371353278718279851 : ℚ)),
    jensenFloorQ96 := (63497001392343764 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_simplexId_before"
  err.flush

theorem geometryRow002_simplexId_read :
    geometryRowsJson002.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped002.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_vertexIds_before"
  err.flush

theorem geometryRow002_vertexIds_read :
    geometryRowsJson002.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped002.vertexIds := by decide +kernel

noncomputable def geometryRow002_physicalVolumeNumeratorChars : List Char := ['6', '9', '3', '9', '3', '4', '8', '7', '0', '4', '7', '0', '0', '3', '1', '3', '4', '1', '9', '5', '6', '6', '1', '0', '0', '9', '9', '6', '4', '3', '4', '8', '6', '2', '5', '5', '7', '1', '8', '7', '4', '5', '7', '8', '2', '9']
noncomputable def geometryRow002_physicalVolumeDenominatorChars : List Char := ['1', '8', '6', '1', '2', '8', '5', '0', '3', '6', '8', '7', '5', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_physicalVolumeText : String := String.ofList (geometryRow002_physicalVolumeNumeratorChars ++ '/' :: geometryRow002_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_physicalVolume_before_field"
  err.flush

theorem geometryRow002_physicalVolume_field :
    geometryRowsJson002.getObjVal? "physical_volume" = .ok (.str geometryRow002_physicalVolumeText) := by rfl

theorem geometryRow002_physicalVolume_numerator_no_slash :
    geometryRow002_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeNumeratorChars = some (6939348704700313419566100996434862557187457829 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeDenominatorChars = some (18612850368752640000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_nonzero : (18612850368752640000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_physicalVolume_parse :
    parseRational geometryRow002_physicalVolumeText = .ok geometryRowsTyped002.physicalVolume :=
  original_rational_fraction_of_chars geometryRow002_physicalVolumeNumeratorChars geometryRow002_physicalVolumeDenominatorChars
    (6939348704700313419566100996434862557187457829 : Int) (18612850368752640000000000000000000000000000000000000000000000000000 : Int)
    geometryRow002_physicalVolume_numerator_no_slash geometryRow002_physicalVolume_numerator_parse
    geometryRow002_physicalVolume_denominator_parse geometryRow002_physicalVolume_denominator_nonzero

theorem geometryRow002_physicalVolume_read :
    rationalField geometryRowsJson002 "physical_volume" = .ok geometryRowsTyped002.physicalVolume :=
  original_rationalField_of_string geometryRowsJson002 "physical_volume" geometryRow002_physicalVolumeText
    geometryRowsTyped002.physicalVolume geometryRow002_physicalVolume_field geometryRow002_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_physicalVolume_complete"
  err.flush

noncomputable def geometryRow002_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow002_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_meanGapText : String := String.ofList (geometryRow002_meanGapNumeratorChars ++ '/' :: geometryRow002_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_meanGap_before_field"
  err.flush

theorem geometryRow002_meanGap_field :
    geometryRowsJson002.getObjVal? "mean_gap" = .ok (.str geometryRow002_meanGapText) := by rfl

theorem geometryRow002_meanGap_numerator_no_slash :
    geometryRow002_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_meanGap_numerator_parse :
    SourceJson.intChars geometryRow002_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_parse :
    SourceJson.intChars geometryRow002_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_meanGap_parse :
    parseRational geometryRow002_meanGapText = .ok geometryRowsTyped002.meanGap :=
  original_rational_fraction_of_chars geometryRow002_meanGapNumeratorChars geometryRow002_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow002_meanGap_numerator_no_slash geometryRow002_meanGap_numerator_parse
    geometryRow002_meanGap_denominator_parse geometryRow002_meanGap_denominator_nonzero

theorem geometryRow002_meanGap_read :
    rationalField geometryRowsJson002 "mean_gap" = .ok geometryRowsTyped002.meanGap :=
  original_rationalField_of_string geometryRowsJson002 "mean_gap" geometryRow002_meanGapText
    geometryRowsTyped002.meanGap geometryRow002_meanGap_field geometryRow002_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_meanGap_complete"
  err.flush

noncomputable def geometryRow002_jensenBoundNumeratorChars : List Char := ['1', '5', '5', '2', '5', '0', '2', '4', '3', '7', '1', '4', '6', '8', '2', '7', '9', '1', '8', '2', '2', '4', '6', '5', '8', '9', '4', '3', '2', '8', '9', '7', '4', '5', '2', '5', '8', '0', '3', '7', '9', '9', '1', '8', '9', '8', '8', '8', '0', '8', '0', '3', '5', '3', '0', '6', '3', '8', '7', '2', '6', '4', '1', '6', '2', '7', '7', '8', '0', '7', '9', '7', '0', '9', '0', '9', '8', '7', '7', '3', '3', '0', '7', '6', '5', '9', '0', '0', '3', '0', '6', '5', '9', '8', '9', '5', '8', '0', '4', '6', '7', '4', '6', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_jensenBoundDenominatorChars : List Char := ['1', '9', '3', '7', '1', '2', '9', '5', '1', '3', '1', '5', '6', '6', '8', '6', '7', '4', '1', '3', '3', '8', '2', '8', '3', '6', '6', '8', '0', '6', '1', '4', '1', '3', '6', '1', '8', '0', '7', '3', '2', '0', '5', '0', '8', '0', '0', '1', '4', '2', '3', '2', '8', '0', '0', '3', '5', '5', '1', '4', '6', '5', '9', '1', '8', '4', '5', '2', '7', '7', '8', '5', '2', '4', '8', '6', '3', '9', '6', '2', '7', '3', '8', '6', '2', '3', '9', '4', '3', '4', '6', '8', '2', '3', '1', '0', '1', '8', '1', '7', '4', '5', '3', '9', '4', '7', '3', '9', '1', '5', '7', '9', '5', '0', '1', '3', '9', '8', '0', '0', '3', '7', '1', '3', '5', '3', '2', '7', '8', '7', '1', '8', '2', '7', '9', '8', '5', '1']
noncomputable def geometryRow002_jensenBoundText : String := String.ofList (geometryRow002_jensenBoundNumeratorChars ++ '/' :: geometryRow002_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_jensenBound_before_field"
  err.flush

theorem geometryRow002_jensenBound_field :
    geometryRowsJson002.getObjVal? "jensen_bound" = .ok (.str geometryRow002_jensenBoundText) := by rfl

theorem geometryRow002_jensenBound_numerator_no_slash :
    geometryRow002_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow002_jensenBoundNumeratorChars = some (155250243714682791822465894328974525803799189888080353063872641627780797090987733076590030659895804674668800000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow002_jensenBoundDenominatorChars = some (193712951315668674133828366806141361807320508001423280035514659184527785248639627386239434682310181745394739157950139800371353278718279851 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_nonzero : (193712951315668674133828366806141361807320508001423280035514659184527785248639627386239434682310181745394739157950139800371353278718279851 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_jensenBound_parse :
    parseRational geometryRow002_jensenBoundText = .ok geometryRowsTyped002.jensenBound :=
  original_rational_fraction_of_chars geometryRow002_jensenBoundNumeratorChars geometryRow002_jensenBoundDenominatorChars
    (155250243714682791822465894328974525803799189888080353063872641627780797090987733076590030659895804674668800000000000000000000 : Int) (193712951315668674133828366806141361807320508001423280035514659184527785248639627386239434682310181745394739157950139800371353278718279851 : Int)
    geometryRow002_jensenBound_numerator_no_slash geometryRow002_jensenBound_numerator_parse
    geometryRow002_jensenBound_denominator_parse geometryRow002_jensenBound_denominator_nonzero

theorem geometryRow002_jensenBound_read :
    rationalField geometryRowsJson002 "jensen_bound" = .ok geometryRowsTyped002.jensenBound :=
  original_rationalField_of_string geometryRowsJson002 "jensen_bound" geometryRow002_jensenBoundText
    geometryRowsTyped002.jensenBound geometryRow002_jensenBound_field geometryRow002_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_factorMaxima_before"
  err.flush

theorem geometryRow002_factorMaxima_read :
    rationalArrayField geometryRowsJson002 "factor_maxima" = .ok geometryRowsTyped002.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_gapWeightedMeans_before"
  err.flush

theorem geometryRow002_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson002 "gap_weighted_means" = .ok geometryRowsTyped002.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow002_floorChars : List Char := ['6', '3', '4', '9', '7', '0', '0', '1', '3', '9', '2', '3', '4', '3', '7', '6', '4']
noncomputable def geometryRow002_floorText : String := String.ofList geometryRow002_floorChars

theorem geometryRow002_floor_text_read :
    geometryRowsJson002.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow002_floorText := by rfl

theorem geometryRow002_floor_chars_parse :
    SourceJson.intChars geometryRow002_floorChars = some (63497001392343764 : Int) := by decide +kernel

theorem geometryRow002_floor_parse :
    parseInteger geometryRow002_floorText = .ok geometryRowsTyped002.jensenFloorQ96 := by
  simp only [geometryRow002_floorText, parseInteger, String.toList_ofList, geometryRow002_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_002 :
    decodeGeometryRow geometryRowsJson002 = .ok geometryRowsTyped002 :=
  original_geometryRow_of_fields geometryRowsJson002 geometryRowsTyped002 geometryRow002_floorText
    geometryRow002_simplexId_read geometryRow002_vertexIds_read
    geometryRow002_physicalVolume_read geometryRow002_meanGap_read
    geometryRow002_factorMaxima_read geometryRow002_gapWeightedMeans_read
    geometryRow002_jensenBound_read geometryRow002_floor_text_read geometryRow002_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_002_original_decoder_complete"
  err.flush

#print axioms geometryRow002_simplexId_read
#print axioms geometryRow002_vertexIds_read
#print axioms geometryRow002_physicalVolume_field
#print axioms geometryRow002_physicalVolume_numerator_no_slash
#print axioms geometryRow002_physicalVolume_numerator_parse
#print axioms geometryRow002_physicalVolume_denominator_parse
#print axioms geometryRow002_physicalVolume_denominator_nonzero
#print axioms geometryRow002_physicalVolume_parse
#print axioms geometryRow002_physicalVolume_read
#print axioms geometryRow002_meanGap_field
#print axioms geometryRow002_meanGap_numerator_no_slash
#print axioms geometryRow002_meanGap_numerator_parse
#print axioms geometryRow002_meanGap_denominator_parse
#print axioms geometryRow002_meanGap_denominator_nonzero
#print axioms geometryRow002_meanGap_parse
#print axioms geometryRow002_meanGap_read
#print axioms geometryRow002_jensenBound_field
#print axioms geometryRow002_jensenBound_numerator_no_slash
#print axioms geometryRow002_jensenBound_numerator_parse
#print axioms geometryRow002_jensenBound_denominator_parse
#print axioms geometryRow002_jensenBound_denominator_nonzero
#print axioms geometryRow002_jensenBound_parse
#print axioms geometryRow002_jensenBound_read
#print axioms geometryRow002_factorMaxima_read
#print axioms geometryRow002_gapWeightedMeans_read
#print axioms geometryRow002_floor_text_read
#print axioms geometryRow002_floor_chars_parse
#print axioms geometryRow002_floor_parse
#print axioms decode_geometry_Rows_002

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
