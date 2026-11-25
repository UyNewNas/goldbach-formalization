import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00700

/-! Original GeometryRow 28: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson028 : SourceJson :=
  (simplicesChunk028Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped028 : GeometryRow :=
  { simplexId := 28,
    vertexIds := #[27, 25, 23, 21, 20, 17, 4, 2, 0],
    physicalVolume := ((98375817396265502268997012491959 : ℚ) / (420306053466796875000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((3890569 : ℚ) / (104500000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((207399828638911 : ℚ) / (2327925600000000 : ℚ)), ((104617804751183 : ℚ) / (1163962800000000 : ℚ)), ((6441157503923 : ℚ) / (51731680000000 : ℚ)), ((17089758957911 : ℚ) / (179071200000000 : ℚ)), ((68991859907489 : ℚ) / (775975200000000 : ℚ)), ((142427702119 : ℚ) / (2069267200000 : ℚ)), ((2186679818493 : ℚ) / (64664600000000 : ℚ)), ((19195247676133 : ℚ) / (581981400000000 : ℚ)), ((18878998983373 : ℚ) / (581981400000000 : ℚ)), ((35680719400901 : ℚ) / (1163962800000000 : ℚ))],
    jensenBound := ((140481626532446757354819616186794065248399106285618534081993316192623017997312576820096168934506496000000000000000000000 : ℚ) / (221195557423457130281368309339131032353769204408375824305065579185202025011955742521995557939645420455675490382767377434277104636721 : ℚ)),
    jensenFloorQ96 := (50317923500938118 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_simplexId_before"
  err.flush

theorem geometryRow028_simplexId_read :
    geometryRowsJson028.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped028.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_vertexIds_before"
  err.flush

theorem geometryRow028_vertexIds_read :
    geometryRowsJson028.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped028.vertexIds := by decide +kernel

noncomputable def geometryRow028_physicalVolumeNumeratorChars : List Char := ['9', '8', '3', '7', '5', '8', '1', '7', '3', '9', '6', '2', '6', '5', '5', '0', '2', '2', '6', '8', '9', '9', '7', '0', '1', '2', '4', '9', '1', '9', '5', '9']
noncomputable def geometryRow028_physicalVolumeDenominatorChars : List Char := ['4', '2', '0', '3', '0', '6', '0', '5', '3', '4', '6', '6', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_physicalVolumeText : String := String.ofList (geometryRow028_physicalVolumeNumeratorChars ++ '/' :: geometryRow028_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_physicalVolume_before_field"
  err.flush

theorem geometryRow028_physicalVolume_field :
    geometryRowsJson028.getObjVal? "physical_volume" = .ok (.str geometryRow028_physicalVolumeText) := by rfl

theorem geometryRow028_physicalVolume_numerator_no_slash :
    geometryRow028_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeNumeratorChars = some (98375817396265502268997012491959 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeDenominatorChars = some (420306053466796875000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_nonzero : (420306053466796875000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_physicalVolume_parse :
    parseRational geometryRow028_physicalVolumeText = .ok geometryRowsTyped028.physicalVolume :=
  original_rational_fraction_of_chars geometryRow028_physicalVolumeNumeratorChars geometryRow028_physicalVolumeDenominatorChars
    (98375817396265502268997012491959 : Int) (420306053466796875000000000000000000000000000000000000 : Int)
    geometryRow028_physicalVolume_numerator_no_slash geometryRow028_physicalVolume_numerator_parse
    geometryRow028_physicalVolume_denominator_parse geometryRow028_physicalVolume_denominator_nonzero

theorem geometryRow028_physicalVolume_read :
    rationalField geometryRowsJson028 "physical_volume" = .ok geometryRowsTyped028.physicalVolume :=
  original_rationalField_of_string geometryRowsJson028 "physical_volume" geometryRow028_physicalVolumeText
    geometryRowsTyped028.physicalVolume geometryRow028_physicalVolume_field geometryRow028_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_physicalVolume_complete"
  err.flush

noncomputable def geometryRow028_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow028_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_meanGapText : String := String.ofList (geometryRow028_meanGapNumeratorChars ++ '/' :: geometryRow028_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_meanGap_before_field"
  err.flush

theorem geometryRow028_meanGap_field :
    geometryRowsJson028.getObjVal? "mean_gap" = .ok (.str geometryRow028_meanGapText) := by rfl

theorem geometryRow028_meanGap_numerator_no_slash :
    geometryRow028_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_meanGap_numerator_parse :
    SourceJson.intChars geometryRow028_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_parse :
    SourceJson.intChars geometryRow028_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_meanGap_parse :
    parseRational geometryRow028_meanGapText = .ok geometryRowsTyped028.meanGap :=
  original_rational_fraction_of_chars geometryRow028_meanGapNumeratorChars geometryRow028_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow028_meanGap_numerator_no_slash geometryRow028_meanGap_numerator_parse
    geometryRow028_meanGap_denominator_parse geometryRow028_meanGap_denominator_nonzero

theorem geometryRow028_meanGap_read :
    rationalField geometryRowsJson028 "mean_gap" = .ok geometryRowsTyped028.meanGap :=
  original_rationalField_of_string geometryRowsJson028 "mean_gap" geometryRow028_meanGapText
    geometryRowsTyped028.meanGap geometryRow028_meanGap_field geometryRow028_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_meanGap_complete"
  err.flush

noncomputable def geometryRow028_jensenBoundNumeratorChars : List Char := ['1', '4', '0', '4', '8', '1', '6', '2', '6', '5', '3', '2', '4', '4', '6', '7', '5', '7', '3', '5', '4', '8', '1', '9', '6', '1', '6', '1', '8', '6', '7', '9', '4', '0', '6', '5', '2', '4', '8', '3', '9', '9', '1', '0', '6', '2', '8', '5', '6', '1', '8', '5', '3', '4', '0', '8', '1', '9', '9', '3', '3', '1', '6', '1', '9', '2', '6', '2', '3', '0', '1', '7', '9', '9', '7', '3', '1', '2', '5', '7', '6', '8', '2', '0', '0', '9', '6', '1', '6', '8', '9', '3', '4', '5', '0', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_jensenBoundDenominatorChars : List Char := ['2', '2', '1', '1', '9', '5', '5', '5', '7', '4', '2', '3', '4', '5', '7', '1', '3', '0', '2', '8', '1', '3', '6', '8', '3', '0', '9', '3', '3', '9', '1', '3', '1', '0', '3', '2', '3', '5', '3', '7', '6', '9', '2', '0', '4', '4', '0', '8', '3', '7', '5', '8', '2', '4', '3', '0', '5', '0', '6', '5', '5', '7', '9', '1', '8', '5', '2', '0', '2', '0', '2', '5', '0', '1', '1', '9', '5', '5', '7', '4', '2', '5', '2', '1', '9', '9', '5', '5', '5', '7', '9', '3', '9', '6', '4', '5', '4', '2', '0', '4', '5', '5', '6', '7', '5', '4', '9', '0', '3', '8', '2', '7', '6', '7', '3', '7', '7', '4', '3', '4', '2', '7', '7', '1', '0', '4', '6', '3', '6', '7', '2', '1']
noncomputable def geometryRow028_jensenBoundText : String := String.ofList (geometryRow028_jensenBoundNumeratorChars ++ '/' :: geometryRow028_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_jensenBound_before_field"
  err.flush

theorem geometryRow028_jensenBound_field :
    geometryRowsJson028.getObjVal? "jensen_bound" = .ok (.str geometryRow028_jensenBoundText) := by rfl

theorem geometryRow028_jensenBound_numerator_no_slash :
    geometryRow028_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow028_jensenBoundNumeratorChars = some (140481626532446757354819616186794065248399106285618534081993316192623017997312576820096168934506496000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow028_jensenBoundDenominatorChars = some (221195557423457130281368309339131032353769204408375824305065579185202025011955742521995557939645420455675490382767377434277104636721 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_nonzero : (221195557423457130281368309339131032353769204408375824305065579185202025011955742521995557939645420455675490382767377434277104636721 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_jensenBound_parse :
    parseRational geometryRow028_jensenBoundText = .ok geometryRowsTyped028.jensenBound :=
  original_rational_fraction_of_chars geometryRow028_jensenBoundNumeratorChars geometryRow028_jensenBoundDenominatorChars
    (140481626532446757354819616186794065248399106285618534081993316192623017997312576820096168934506496000000000000000000000 : Int) (221195557423457130281368309339131032353769204408375824305065579185202025011955742521995557939645420455675490382767377434277104636721 : Int)
    geometryRow028_jensenBound_numerator_no_slash geometryRow028_jensenBound_numerator_parse
    geometryRow028_jensenBound_denominator_parse geometryRow028_jensenBound_denominator_nonzero

theorem geometryRow028_jensenBound_read :
    rationalField geometryRowsJson028 "jensen_bound" = .ok geometryRowsTyped028.jensenBound :=
  original_rationalField_of_string geometryRowsJson028 "jensen_bound" geometryRow028_jensenBoundText
    geometryRowsTyped028.jensenBound geometryRow028_jensenBound_field geometryRow028_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_factorMaxima_before"
  err.flush

theorem geometryRow028_factorMaxima_read :
    rationalArrayField geometryRowsJson028 "factor_maxima" = .ok geometryRowsTyped028.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_gapWeightedMeans_before"
  err.flush

theorem geometryRow028_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson028 "gap_weighted_means" = .ok geometryRowsTyped028.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow028_floorChars : List Char := ['5', '0', '3', '1', '7', '9', '2', '3', '5', '0', '0', '9', '3', '8', '1', '1', '8']
noncomputable def geometryRow028_floorText : String := String.ofList geometryRow028_floorChars

theorem geometryRow028_floor_text_read :
    geometryRowsJson028.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow028_floorText := by rfl

theorem geometryRow028_floor_chars_parse :
    SourceJson.intChars geometryRow028_floorChars = some (50317923500938118 : Int) := by decide +kernel

theorem geometryRow028_floor_parse :
    parseInteger geometryRow028_floorText = .ok geometryRowsTyped028.jensenFloorQ96 := by
  simp only [geometryRow028_floorText, parseInteger, String.toList_ofList, geometryRow028_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_028 :
    decodeGeometryRow geometryRowsJson028 = .ok geometryRowsTyped028 :=
  original_geometryRow_of_fields geometryRowsJson028 geometryRowsTyped028 geometryRow028_floorText
    geometryRow028_simplexId_read geometryRow028_vertexIds_read
    geometryRow028_physicalVolume_read geometryRow028_meanGap_read
    geometryRow028_factorMaxima_read geometryRow028_gapWeightedMeans_read
    geometryRow028_jensenBound_read geometryRow028_floor_text_read geometryRow028_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_028_original_decoder_complete"
  err.flush

#print axioms geometryRow028_simplexId_read
#print axioms geometryRow028_vertexIds_read
#print axioms geometryRow028_physicalVolume_field
#print axioms geometryRow028_physicalVolume_numerator_no_slash
#print axioms geometryRow028_physicalVolume_numerator_parse
#print axioms geometryRow028_physicalVolume_denominator_parse
#print axioms geometryRow028_physicalVolume_denominator_nonzero
#print axioms geometryRow028_physicalVolume_parse
#print axioms geometryRow028_physicalVolume_read
#print axioms geometryRow028_meanGap_field
#print axioms geometryRow028_meanGap_numerator_no_slash
#print axioms geometryRow028_meanGap_numerator_parse
#print axioms geometryRow028_meanGap_denominator_parse
#print axioms geometryRow028_meanGap_denominator_nonzero
#print axioms geometryRow028_meanGap_parse
#print axioms geometryRow028_meanGap_read
#print axioms geometryRow028_jensenBound_field
#print axioms geometryRow028_jensenBound_numerator_no_slash
#print axioms geometryRow028_jensenBound_numerator_parse
#print axioms geometryRow028_jensenBound_denominator_parse
#print axioms geometryRow028_jensenBound_denominator_nonzero
#print axioms geometryRow028_jensenBound_parse
#print axioms geometryRow028_jensenBound_read
#print axioms geometryRow028_factorMaxima_read
#print axioms geometryRow028_gapWeightedMeans_read
#print axioms geometryRow028_floor_text_read
#print axioms geometryRow028_floor_chars_parse
#print axioms geometryRow028_floor_parse
#print axioms decode_geometry_Rows_028

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
