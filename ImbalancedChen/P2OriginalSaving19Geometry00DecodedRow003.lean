import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000

/-! Original GeometryRow 3: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson003 : SourceJson :=
  (simplicesChunk003Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped003 : GeometryRow :=
  { simplexId := 3,
    vertexIds := #[27, 25, 11, 9, 7, 6, 5, 3, 1],
    physicalVolume := ((6579638820975569522770293280488195056813 : ℚ) / (151853091586560000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((3227973942283 : ℚ) / (34441680000000 : ℚ)), ((3252751241557 : ℚ) / (34441680000000 : ℚ)), ((124249205703349 : ℚ) / (1033250400000000 : ℚ)), ((3653092001563 : ℚ) / (41330016000000 : ℚ)), ((84155134748179 : ℚ) / (1033250400000000 : ℚ)), ((75728493876491 : ℚ) / (1033250400000000 : ℚ)), ((424993488181 : ℚ) / (11480560000000 : ℚ)), ((18151079112343 : ℚ) / (516625200000000 : ℚ)), ((17676257435923 : ℚ) / (516625200000000 : ℚ)), ((5735101686919 : ℚ) / (172208400000000 : ℚ))],
    jensenBound := ((674894239729546126284625671023664040912962960381893199987626484065102755116345142604049206476800000000000000000 : ℚ) / (8109084687671433360281486861040773664898427656496769856410756683911118145053894188737483701775893813923739383769557504503165167 : ℚ)),
    jensenFloorQ96 := (6593916892559 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_simplexId_before"
  err.flush

theorem geometryRow003_simplexId_read :
    geometryRowsJson003.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped003.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_vertexIds_before"
  err.flush

theorem geometryRow003_vertexIds_read :
    geometryRowsJson003.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped003.vertexIds := by decide +kernel

noncomputable def geometryRow003_physicalVolumeNumeratorChars : List Char := ['6', '5', '7', '9', '6', '3', '8', '8', '2', '0', '9', '7', '5', '5', '6', '9', '5', '2', '2', '7', '7', '0', '2', '9', '3', '2', '8', '0', '4', '8', '8', '1', '9', '5', '0', '5', '6', '8', '1', '3']
noncomputable def geometryRow003_physicalVolumeDenominatorChars : List Char := ['1', '5', '1', '8', '5', '3', '0', '9', '1', '5', '8', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_physicalVolumeText : String := String.ofList (geometryRow003_physicalVolumeNumeratorChars ++ '/' :: geometryRow003_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_physicalVolume_before_field"
  err.flush

theorem geometryRow003_physicalVolume_field :
    geometryRowsJson003.getObjVal? "physical_volume" = .ok (.str geometryRow003_physicalVolumeText) := by rfl

theorem geometryRow003_physicalVolume_numerator_no_slash :
    geometryRow003_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeNumeratorChars = some (6579638820975569522770293280488195056813 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeDenominatorChars = some (151853091586560000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_nonzero : (151853091586560000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_physicalVolume_parse :
    parseRational geometryRow003_physicalVolumeText = .ok geometryRowsTyped003.physicalVolume :=
  original_rational_fraction_of_chars geometryRow003_physicalVolumeNumeratorChars geometryRow003_physicalVolumeDenominatorChars
    (6579638820975569522770293280488195056813 : Int) (151853091586560000000000000000000000000000000000000000000000000000 : Int)
    geometryRow003_physicalVolume_numerator_no_slash geometryRow003_physicalVolume_numerator_parse
    geometryRow003_physicalVolume_denominator_parse geometryRow003_physicalVolume_denominator_nonzero

theorem geometryRow003_physicalVolume_read :
    rationalField geometryRowsJson003 "physical_volume" = .ok geometryRowsTyped003.physicalVolume :=
  original_rationalField_of_string geometryRowsJson003 "physical_volume" geometryRow003_physicalVolumeText
    geometryRowsTyped003.physicalVolume geometryRow003_physicalVolume_field geometryRow003_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_physicalVolume_complete"
  err.flush

noncomputable def geometryRow003_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow003_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_meanGapText : String := String.ofList (geometryRow003_meanGapNumeratorChars ++ '/' :: geometryRow003_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_meanGap_before_field"
  err.flush

theorem geometryRow003_meanGap_field :
    geometryRowsJson003.getObjVal? "mean_gap" = .ok (.str geometryRow003_meanGapText) := by rfl

theorem geometryRow003_meanGap_numerator_no_slash :
    geometryRow003_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_meanGap_numerator_parse :
    SourceJson.intChars geometryRow003_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_parse :
    SourceJson.intChars geometryRow003_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_meanGap_parse :
    parseRational geometryRow003_meanGapText = .ok geometryRowsTyped003.meanGap :=
  original_rational_fraction_of_chars geometryRow003_meanGapNumeratorChars geometryRow003_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow003_meanGap_numerator_no_slash geometryRow003_meanGap_numerator_parse
    geometryRow003_meanGap_denominator_parse geometryRow003_meanGap_denominator_nonzero

theorem geometryRow003_meanGap_read :
    rationalField geometryRowsJson003 "mean_gap" = .ok geometryRowsTyped003.meanGap :=
  original_rationalField_of_string geometryRowsJson003 "mean_gap" geometryRow003_meanGapText
    geometryRowsTyped003.meanGap geometryRow003_meanGap_field geometryRow003_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_meanGap_complete"
  err.flush

noncomputable def geometryRow003_jensenBoundNumeratorChars : List Char := ['6', '7', '4', '8', '9', '4', '2', '3', '9', '7', '2', '9', '5', '4', '6', '1', '2', '6', '2', '8', '4', '6', '2', '5', '6', '7', '1', '0', '2', '3', '6', '6', '4', '0', '4', '0', '9', '1', '2', '9', '6', '2', '9', '6', '0', '3', '8', '1', '8', '9', '3', '1', '9', '9', '9', '8', '7', '6', '2', '6', '4', '8', '4', '0', '6', '5', '1', '0', '2', '7', '5', '5', '1', '1', '6', '3', '4', '5', '1', '4', '2', '6', '0', '4', '0', '4', '9', '2', '0', '6', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_jensenBoundDenominatorChars : List Char := ['8', '1', '0', '9', '0', '8', '4', '6', '8', '7', '6', '7', '1', '4', '3', '3', '3', '6', '0', '2', '8', '1', '4', '8', '6', '8', '6', '1', '0', '4', '0', '7', '7', '3', '6', '6', '4', '8', '9', '8', '4', '2', '7', '6', '5', '6', '4', '9', '6', '7', '6', '9', '8', '5', '6', '4', '1', '0', '7', '5', '6', '6', '8', '3', '9', '1', '1', '1', '1', '8', '1', '4', '5', '0', '5', '3', '8', '9', '4', '1', '8', '8', '7', '3', '7', '4', '8', '3', '7', '0', '1', '7', '7', '5', '8', '9', '3', '8', '1', '3', '9', '2', '3', '7', '3', '9', '3', '8', '3', '7', '6', '9', '5', '5', '7', '5', '0', '4', '5', '0', '3', '1', '6', '5', '1', '6', '7']
noncomputable def geometryRow003_jensenBoundText : String := String.ofList (geometryRow003_jensenBoundNumeratorChars ++ '/' :: geometryRow003_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_jensenBound_before_field"
  err.flush

theorem geometryRow003_jensenBound_field :
    geometryRowsJson003.getObjVal? "jensen_bound" = .ok (.str geometryRow003_jensenBoundText) := by rfl

theorem geometryRow003_jensenBound_numerator_no_slash :
    geometryRow003_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow003_jensenBoundNumeratorChars = some (674894239729546126284625671023664040912962960381893199987626484065102755116345142604049206476800000000000000000 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow003_jensenBoundDenominatorChars = some (8109084687671433360281486861040773664898427656496769856410756683911118145053894188737483701775893813923739383769557504503165167 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_nonzero : (8109084687671433360281486861040773664898427656496769856410756683911118145053894188737483701775893813923739383769557504503165167 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_jensenBound_parse :
    parseRational geometryRow003_jensenBoundText = .ok geometryRowsTyped003.jensenBound :=
  original_rational_fraction_of_chars geometryRow003_jensenBoundNumeratorChars geometryRow003_jensenBoundDenominatorChars
    (674894239729546126284625671023664040912962960381893199987626484065102755116345142604049206476800000000000000000 : Int) (8109084687671433360281486861040773664898427656496769856410756683911118145053894188737483701775893813923739383769557504503165167 : Int)
    geometryRow003_jensenBound_numerator_no_slash geometryRow003_jensenBound_numerator_parse
    geometryRow003_jensenBound_denominator_parse geometryRow003_jensenBound_denominator_nonzero

theorem geometryRow003_jensenBound_read :
    rationalField geometryRowsJson003 "jensen_bound" = .ok geometryRowsTyped003.jensenBound :=
  original_rationalField_of_string geometryRowsJson003 "jensen_bound" geometryRow003_jensenBoundText
    geometryRowsTyped003.jensenBound geometryRow003_jensenBound_field geometryRow003_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_factorMaxima_before"
  err.flush

theorem geometryRow003_factorMaxima_read :
    rationalArrayField geometryRowsJson003 "factor_maxima" = .ok geometryRowsTyped003.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_gapWeightedMeans_before"
  err.flush

theorem geometryRow003_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson003 "gap_weighted_means" = .ok geometryRowsTyped003.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow003_floorChars : List Char := ['6', '5', '9', '3', '9', '1', '6', '8', '9', '2', '5', '5', '9']
noncomputable def geometryRow003_floorText : String := String.ofList geometryRow003_floorChars

theorem geometryRow003_floor_text_read :
    geometryRowsJson003.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow003_floorText := by rfl

theorem geometryRow003_floor_chars_parse :
    SourceJson.intChars geometryRow003_floorChars = some (6593916892559 : Int) := by decide +kernel

theorem geometryRow003_floor_parse :
    parseInteger geometryRow003_floorText = .ok geometryRowsTyped003.jensenFloorQ96 := by
  simp only [geometryRow003_floorText, parseInteger, String.toList_ofList, geometryRow003_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_003 :
    decodeGeometryRow geometryRowsJson003 = .ok geometryRowsTyped003 :=
  original_geometryRow_of_fields geometryRowsJson003 geometryRowsTyped003 geometryRow003_floorText
    geometryRow003_simplexId_read geometryRow003_vertexIds_read
    geometryRow003_physicalVolume_read geometryRow003_meanGap_read
    geometryRow003_factorMaxima_read geometryRow003_gapWeightedMeans_read
    geometryRow003_jensenBound_read geometryRow003_floor_text_read geometryRow003_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_003_original_decoder_complete"
  err.flush

#print axioms geometryRow003_simplexId_read
#print axioms geometryRow003_vertexIds_read
#print axioms geometryRow003_physicalVolume_field
#print axioms geometryRow003_physicalVolume_numerator_no_slash
#print axioms geometryRow003_physicalVolume_numerator_parse
#print axioms geometryRow003_physicalVolume_denominator_parse
#print axioms geometryRow003_physicalVolume_denominator_nonzero
#print axioms geometryRow003_physicalVolume_parse
#print axioms geometryRow003_physicalVolume_read
#print axioms geometryRow003_meanGap_field
#print axioms geometryRow003_meanGap_numerator_no_slash
#print axioms geometryRow003_meanGap_numerator_parse
#print axioms geometryRow003_meanGap_denominator_parse
#print axioms geometryRow003_meanGap_denominator_nonzero
#print axioms geometryRow003_meanGap_parse
#print axioms geometryRow003_meanGap_read
#print axioms geometryRow003_jensenBound_field
#print axioms geometryRow003_jensenBound_numerator_no_slash
#print axioms geometryRow003_jensenBound_numerator_parse
#print axioms geometryRow003_jensenBound_denominator_parse
#print axioms geometryRow003_jensenBound_denominator_nonzero
#print axioms geometryRow003_jensenBound_parse
#print axioms geometryRow003_jensenBound_read
#print axioms geometryRow003_factorMaxima_read
#print axioms geometryRow003_gapWeightedMeans_read
#print axioms geometryRow003_floor_text_read
#print axioms geometryRow003_floor_chars_parse
#print axioms geometryRow003_floor_parse
#print axioms decode_geometry_Rows_003

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
