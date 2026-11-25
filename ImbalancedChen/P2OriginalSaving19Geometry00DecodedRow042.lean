import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000

/-! Original GeometryRow 42: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson042 : SourceJson :=
  (simplicesChunk042Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped042 : GeometryRow :=
  { simplexId := 42,
    vertexIds := #[27, 15, 11, 9, 7, 5, 3, 1, 0],
    physicalVolume := ((1074997574167536527760661718475475072337471 : ℚ) / (18659707894156492800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((5563786263003 : ℚ) / (57402800000000 : ℚ)), ((5605081761793 : ℚ) / (57402800000000 : ℚ)), ((20601702277171 : ℚ) / (172208400000000 : ℚ)), ((11315858401997 : ℚ) / (129156300000000 : ℚ)), ((13643606838899 : ℚ) / (172208400000000 : ℚ)), ((12727914319469 : ℚ) / (172208400000000 : ℚ)), ((18775007388461 : ℚ) / (516625200000000 : ℚ)), ((18231799503731 : ℚ) / (516625200000000 : ℚ)), ((17757012268991 : ℚ) / (516625200000000 : ℚ)), ((3457205090429 : ℚ) / (103325040000000 : ℚ))],
    jensenBound := ((2657890789938045244426964453656215729997828754904310325198117888879263903835923372342687975000000000000000000000 : ℚ) / (24724892364910546075095639615607447909803791330225386759666401412858941524424616660263612195091185833482279820206398675271150119 : ℚ)),
    jensenFloorQ96 := (8516914870344 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_simplexId_before"
  err.flush

theorem geometryRow042_simplexId_read :
    geometryRowsJson042.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped042.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_vertexIds_before"
  err.flush

theorem geometryRow042_vertexIds_read :
    geometryRowsJson042.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped042.vertexIds := by decide +kernel

noncomputable def geometryRow042_physicalVolumeNumeratorChars : List Char := ['1', '0', '7', '4', '9', '9', '7', '5', '7', '4', '1', '6', '7', '5', '3', '6', '5', '2', '7', '7', '6', '0', '6', '6', '1', '7', '1', '8', '4', '7', '5', '4', '7', '5', '0', '7', '2', '3', '3', '7', '4', '7', '1']
noncomputable def geometryRow042_physicalVolumeDenominatorChars : List Char := ['1', '8', '6', '5', '9', '7', '0', '7', '8', '9', '4', '1', '5', '6', '4', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_physicalVolumeText : String := String.ofList (geometryRow042_physicalVolumeNumeratorChars ++ '/' :: geometryRow042_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_physicalVolume_before_field"
  err.flush

theorem geometryRow042_physicalVolume_field :
    geometryRowsJson042.getObjVal? "physical_volume" = .ok (.str geometryRow042_physicalVolumeText) := by rfl

theorem geometryRow042_physicalVolume_numerator_no_slash :
    geometryRow042_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeNumeratorChars = some (1074997574167536527760661718475475072337471 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeDenominatorChars = some (18659707894156492800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_nonzero : (18659707894156492800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_physicalVolume_parse :
    parseRational geometryRow042_physicalVolumeText = .ok geometryRowsTyped042.physicalVolume :=
  original_rational_fraction_of_chars geometryRow042_physicalVolumeNumeratorChars geometryRow042_physicalVolumeDenominatorChars
    (1074997574167536527760661718475475072337471 : Int) (18659707894156492800000000000000000000000000000000000000000000000000 : Int)
    geometryRow042_physicalVolume_numerator_no_slash geometryRow042_physicalVolume_numerator_parse
    geometryRow042_physicalVolume_denominator_parse geometryRow042_physicalVolume_denominator_nonzero

theorem geometryRow042_physicalVolume_read :
    rationalField geometryRowsJson042 "physical_volume" = .ok geometryRowsTyped042.physicalVolume :=
  original_rationalField_of_string geometryRowsJson042 "physical_volume" geometryRow042_physicalVolumeText
    geometryRowsTyped042.physicalVolume geometryRow042_physicalVolume_field geometryRow042_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_physicalVolume_complete"
  err.flush

noncomputable def geometryRow042_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow042_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_meanGapText : String := String.ofList (geometryRow042_meanGapNumeratorChars ++ '/' :: geometryRow042_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_meanGap_before_field"
  err.flush

theorem geometryRow042_meanGap_field :
    geometryRowsJson042.getObjVal? "mean_gap" = .ok (.str geometryRow042_meanGapText) := by rfl

theorem geometryRow042_meanGap_numerator_no_slash :
    geometryRow042_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_meanGap_numerator_parse :
    SourceJson.intChars geometryRow042_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_parse :
    SourceJson.intChars geometryRow042_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_meanGap_parse :
    parseRational geometryRow042_meanGapText = .ok geometryRowsTyped042.meanGap :=
  original_rational_fraction_of_chars geometryRow042_meanGapNumeratorChars geometryRow042_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow042_meanGap_numerator_no_slash geometryRow042_meanGap_numerator_parse
    geometryRow042_meanGap_denominator_parse geometryRow042_meanGap_denominator_nonzero

theorem geometryRow042_meanGap_read :
    rationalField geometryRowsJson042 "mean_gap" = .ok geometryRowsTyped042.meanGap :=
  original_rationalField_of_string geometryRowsJson042 "mean_gap" geometryRow042_meanGapText
    geometryRowsTyped042.meanGap geometryRow042_meanGap_field geometryRow042_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_meanGap_complete"
  err.flush

noncomputable def geometryRow042_jensenBoundNumeratorChars : List Char := ['2', '6', '5', '7', '8', '9', '0', '7', '8', '9', '9', '3', '8', '0', '4', '5', '2', '4', '4', '4', '2', '6', '9', '6', '4', '4', '5', '3', '6', '5', '6', '2', '1', '5', '7', '2', '9', '9', '9', '7', '8', '2', '8', '7', '5', '4', '9', '0', '4', '3', '1', '0', '3', '2', '5', '1', '9', '8', '1', '1', '7', '8', '8', '8', '8', '7', '9', '2', '6', '3', '9', '0', '3', '8', '3', '5', '9', '2', '3', '3', '7', '2', '3', '4', '2', '6', '8', '7', '9', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_jensenBoundDenominatorChars : List Char := ['2', '4', '7', '2', '4', '8', '9', '2', '3', '6', '4', '9', '1', '0', '5', '4', '6', '0', '7', '5', '0', '9', '5', '6', '3', '9', '6', '1', '5', '6', '0', '7', '4', '4', '7', '9', '0', '9', '8', '0', '3', '7', '9', '1', '3', '3', '0', '2', '2', '5', '3', '8', '6', '7', '5', '9', '6', '6', '6', '4', '0', '1', '4', '1', '2', '8', '5', '8', '9', '4', '1', '5', '2', '4', '4', '2', '4', '6', '1', '6', '6', '6', '0', '2', '6', '3', '6', '1', '2', '1', '9', '5', '0', '9', '1', '1', '8', '5', '8', '3', '3', '4', '8', '2', '2', '7', '9', '8', '2', '0', '2', '0', '6', '3', '9', '8', '6', '7', '5', '2', '7', '1', '1', '5', '0', '1', '1', '9']
noncomputable def geometryRow042_jensenBoundText : String := String.ofList (geometryRow042_jensenBoundNumeratorChars ++ '/' :: geometryRow042_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_jensenBound_before_field"
  err.flush

theorem geometryRow042_jensenBound_field :
    geometryRowsJson042.getObjVal? "jensen_bound" = .ok (.str geometryRow042_jensenBoundText) := by rfl

theorem geometryRow042_jensenBound_numerator_no_slash :
    geometryRow042_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow042_jensenBoundNumeratorChars = some (2657890789938045244426964453656215729997828754904310325198117888879263903835923372342687975000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow042_jensenBoundDenominatorChars = some (24724892364910546075095639615607447909803791330225386759666401412858941524424616660263612195091185833482279820206398675271150119 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_nonzero : (24724892364910546075095639615607447909803791330225386759666401412858941524424616660263612195091185833482279820206398675271150119 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_jensenBound_parse :
    parseRational geometryRow042_jensenBoundText = .ok geometryRowsTyped042.jensenBound :=
  original_rational_fraction_of_chars geometryRow042_jensenBoundNumeratorChars geometryRow042_jensenBoundDenominatorChars
    (2657890789938045244426964453656215729997828754904310325198117888879263903835923372342687975000000000000000000000 : Int) (24724892364910546075095639615607447909803791330225386759666401412858941524424616660263612195091185833482279820206398675271150119 : Int)
    geometryRow042_jensenBound_numerator_no_slash geometryRow042_jensenBound_numerator_parse
    geometryRow042_jensenBound_denominator_parse geometryRow042_jensenBound_denominator_nonzero

theorem geometryRow042_jensenBound_read :
    rationalField geometryRowsJson042 "jensen_bound" = .ok geometryRowsTyped042.jensenBound :=
  original_rationalField_of_string geometryRowsJson042 "jensen_bound" geometryRow042_jensenBoundText
    geometryRowsTyped042.jensenBound geometryRow042_jensenBound_field geometryRow042_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_factorMaxima_before"
  err.flush

theorem geometryRow042_factorMaxima_read :
    rationalArrayField geometryRowsJson042 "factor_maxima" = .ok geometryRowsTyped042.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_gapWeightedMeans_before"
  err.flush

theorem geometryRow042_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson042 "gap_weighted_means" = .ok geometryRowsTyped042.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow042_floorChars : List Char := ['8', '5', '1', '6', '9', '1', '4', '8', '7', '0', '3', '4', '4']
noncomputable def geometryRow042_floorText : String := String.ofList geometryRow042_floorChars

theorem geometryRow042_floor_text_read :
    geometryRowsJson042.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow042_floorText := by rfl

theorem geometryRow042_floor_chars_parse :
    SourceJson.intChars geometryRow042_floorChars = some (8516914870344 : Int) := by decide +kernel

theorem geometryRow042_floor_parse :
    parseInteger geometryRow042_floorText = .ok geometryRowsTyped042.jensenFloorQ96 := by
  simp only [geometryRow042_floorText, parseInteger, String.toList_ofList, geometryRow042_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_042 :
    decodeGeometryRow geometryRowsJson042 = .ok geometryRowsTyped042 :=
  original_geometryRow_of_fields geometryRowsJson042 geometryRowsTyped042 geometryRow042_floorText
    geometryRow042_simplexId_read geometryRow042_vertexIds_read
    geometryRow042_physicalVolume_read geometryRow042_meanGap_read
    geometryRow042_factorMaxima_read geometryRow042_gapWeightedMeans_read
    geometryRow042_jensenBound_read geometryRow042_floor_text_read geometryRow042_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_042_original_decoder_complete"
  err.flush

#print axioms geometryRow042_simplexId_read
#print axioms geometryRow042_vertexIds_read
#print axioms geometryRow042_physicalVolume_field
#print axioms geometryRow042_physicalVolume_numerator_no_slash
#print axioms geometryRow042_physicalVolume_numerator_parse
#print axioms geometryRow042_physicalVolume_denominator_parse
#print axioms geometryRow042_physicalVolume_denominator_nonzero
#print axioms geometryRow042_physicalVolume_parse
#print axioms geometryRow042_physicalVolume_read
#print axioms geometryRow042_meanGap_field
#print axioms geometryRow042_meanGap_numerator_no_slash
#print axioms geometryRow042_meanGap_numerator_parse
#print axioms geometryRow042_meanGap_denominator_parse
#print axioms geometryRow042_meanGap_denominator_nonzero
#print axioms geometryRow042_meanGap_parse
#print axioms geometryRow042_meanGap_read
#print axioms geometryRow042_jensenBound_field
#print axioms geometryRow042_jensenBound_numerator_no_slash
#print axioms geometryRow042_jensenBound_numerator_parse
#print axioms geometryRow042_jensenBound_denominator_parse
#print axioms geometryRow042_jensenBound_denominator_nonzero
#print axioms geometryRow042_jensenBound_parse
#print axioms geometryRow042_jensenBound_read
#print axioms geometryRow042_factorMaxima_read
#print axioms geometryRow042_gapWeightedMeans_read
#print axioms geometryRow042_floor_text_read
#print axioms geometryRow042_floor_chars_parse
#print axioms geometryRow042_floor_parse
#print axioms decode_geometry_Rows_042

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
