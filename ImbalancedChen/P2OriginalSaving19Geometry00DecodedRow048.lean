import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200

/-! Original GeometryRow 48: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson048 : SourceJson :=
  (simplicesChunk048Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped048 : GeometryRow :=
  { simplexId := 48,
    vertexIds := #[27, 15, 14, 10, 8, 6, 5, 3, 1],
    physicalVolume := ((13270280461614728267185808561756681781551 : ℚ) / (307155685500518400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((26366 : ℚ) / (609375 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((33618175220081 : ℚ) / (344416800000000 : ℚ)), ((33865948212821 : ℚ) / (344416800000000 : ℚ)), ((124787135820101 : ℚ) / (1033250400000000 : ℚ)), ((7622362891009 : ℚ) / (86104200000000 : ℚ)), ((80684718876319 : ℚ) / (1033250400000000 : ℚ)), ((75190563759739 : ℚ) / (1033250400000000 : ℚ)), ((18775007830021 : ℚ) / (516625200000000 : ℚ)), ((18231813192091 : ℚ) / (516625200000000 : ℚ)), ((34807623351953 : ℚ) / (1033250400000000 : ℚ)), ((34807485585233 : ℚ) / (1033250400000000 : ℚ))],
    jensenBound := ((221743420461507271411417314998174871622371266458716684339120603115383484133772820985637126335208000000000000000000000000 : ℚ) / (2724635791487366458443723820715035063399873548500484428227076792141157025524671110067159701076707042172864124542659539924967739164762091 : ℚ)),
    jensenFloorQ96 := (6447953083374 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_simplexId_before"
  err.flush

theorem geometryRow048_simplexId_read :
    geometryRowsJson048.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped048.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_vertexIds_before"
  err.flush

theorem geometryRow048_vertexIds_read :
    geometryRowsJson048.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped048.vertexIds := by decide +kernel

noncomputable def geometryRow048_physicalVolumeNumeratorChars : List Char := ['1', '3', '2', '7', '0', '2', '8', '0', '4', '6', '1', '6', '1', '4', '7', '2', '8', '2', '6', '7', '1', '8', '5', '8', '0', '8', '5', '6', '1', '7', '5', '6', '6', '8', '1', '7', '8', '1', '5', '5', '1']
noncomputable def geometryRow048_physicalVolumeDenominatorChars : List Char := ['3', '0', '7', '1', '5', '5', '6', '8', '5', '5', '0', '0', '5', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_physicalVolumeText : String := String.ofList (geometryRow048_physicalVolumeNumeratorChars ++ '/' :: geometryRow048_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_physicalVolume_before_field"
  err.flush

theorem geometryRow048_physicalVolume_field :
    geometryRowsJson048.getObjVal? "physical_volume" = .ok (.str geometryRow048_physicalVolumeText) := by rfl

theorem geometryRow048_physicalVolume_numerator_no_slash :
    geometryRow048_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeNumeratorChars = some (13270280461614728267185808561756681781551 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeDenominatorChars = some (307155685500518400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_nonzero : (307155685500518400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_physicalVolume_parse :
    parseRational geometryRow048_physicalVolumeText = .ok geometryRowsTyped048.physicalVolume :=
  original_rational_fraction_of_chars geometryRow048_physicalVolumeNumeratorChars geometryRow048_physicalVolumeDenominatorChars
    (13270280461614728267185808561756681781551 : Int) (307155685500518400000000000000000000000000000000000000000000000000 : Int)
    geometryRow048_physicalVolume_numerator_no_slash geometryRow048_physicalVolume_numerator_parse
    geometryRow048_physicalVolume_denominator_parse geometryRow048_physicalVolume_denominator_nonzero

theorem geometryRow048_physicalVolume_read :
    rationalField geometryRowsJson048 "physical_volume" = .ok geometryRowsTyped048.physicalVolume :=
  original_rationalField_of_string geometryRowsJson048 "physical_volume" geometryRow048_physicalVolumeText
    geometryRowsTyped048.physicalVolume geometryRow048_physicalVolume_field geometryRow048_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_physicalVolume_complete"
  err.flush

noncomputable def geometryRow048_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow048_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_meanGapText : String := String.ofList (geometryRow048_meanGapNumeratorChars ++ '/' :: geometryRow048_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_meanGap_before_field"
  err.flush

theorem geometryRow048_meanGap_field :
    geometryRowsJson048.getObjVal? "mean_gap" = .ok (.str geometryRow048_meanGapText) := by rfl

theorem geometryRow048_meanGap_numerator_no_slash :
    geometryRow048_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_meanGap_numerator_parse :
    SourceJson.intChars geometryRow048_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_parse :
    SourceJson.intChars geometryRow048_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_meanGap_parse :
    parseRational geometryRow048_meanGapText = .ok geometryRowsTyped048.meanGap :=
  original_rational_fraction_of_chars geometryRow048_meanGapNumeratorChars geometryRow048_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow048_meanGap_numerator_no_slash geometryRow048_meanGap_numerator_parse
    geometryRow048_meanGap_denominator_parse geometryRow048_meanGap_denominator_nonzero

theorem geometryRow048_meanGap_read :
    rationalField geometryRowsJson048 "mean_gap" = .ok geometryRowsTyped048.meanGap :=
  original_rationalField_of_string geometryRowsJson048 "mean_gap" geometryRow048_meanGapText
    geometryRowsTyped048.meanGap geometryRow048_meanGap_field geometryRow048_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_meanGap_complete"
  err.flush

noncomputable def geometryRow048_jensenBoundNumeratorChars : List Char := ['2', '2', '1', '7', '4', '3', '4', '2', '0', '4', '6', '1', '5', '0', '7', '2', '7', '1', '4', '1', '1', '4', '1', '7', '3', '1', '4', '9', '9', '8', '1', '7', '4', '8', '7', '1', '6', '2', '2', '3', '7', '1', '2', '6', '6', '4', '5', '8', '7', '1', '6', '6', '8', '4', '3', '3', '9', '1', '2', '0', '6', '0', '3', '1', '1', '5', '3', '8', '3', '4', '8', '4', '1', '3', '3', '7', '7', '2', '8', '2', '0', '9', '8', '5', '6', '3', '7', '1', '2', '6', '3', '3', '5', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_jensenBoundDenominatorChars : List Char := ['2', '7', '2', '4', '6', '3', '5', '7', '9', '1', '4', '8', '7', '3', '6', '6', '4', '5', '8', '4', '4', '3', '7', '2', '3', '8', '2', '0', '7', '1', '5', '0', '3', '5', '0', '6', '3', '3', '9', '9', '8', '7', '3', '5', '4', '8', '5', '0', '0', '4', '8', '4', '4', '2', '8', '2', '2', '7', '0', '7', '6', '7', '9', '2', '1', '4', '1', '1', '5', '7', '0', '2', '5', '5', '2', '4', '6', '7', '1', '1', '1', '0', '0', '6', '7', '1', '5', '9', '7', '0', '1', '0', '7', '6', '7', '0', '7', '0', '4', '2', '1', '7', '2', '8', '6', '4', '1', '2', '4', '5', '4', '2', '6', '5', '9', '5', '3', '9', '9', '2', '4', '9', '6', '7', '7', '3', '9', '1', '6', '4', '7', '6', '2', '0', '9', '1']
noncomputable def geometryRow048_jensenBoundText : String := String.ofList (geometryRow048_jensenBoundNumeratorChars ++ '/' :: geometryRow048_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_jensenBound_before_field"
  err.flush

theorem geometryRow048_jensenBound_field :
    geometryRowsJson048.getObjVal? "jensen_bound" = .ok (.str geometryRow048_jensenBoundText) := by rfl

theorem geometryRow048_jensenBound_numerator_no_slash :
    geometryRow048_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow048_jensenBoundNumeratorChars = some (221743420461507271411417314998174871622371266458716684339120603115383484133772820985637126335208000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow048_jensenBoundDenominatorChars = some (2724635791487366458443723820715035063399873548500484428227076792141157025524671110067159701076707042172864124542659539924967739164762091 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_nonzero : (2724635791487366458443723820715035063399873548500484428227076792141157025524671110067159701076707042172864124542659539924967739164762091 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_jensenBound_parse :
    parseRational geometryRow048_jensenBoundText = .ok geometryRowsTyped048.jensenBound :=
  original_rational_fraction_of_chars geometryRow048_jensenBoundNumeratorChars geometryRow048_jensenBoundDenominatorChars
    (221743420461507271411417314998174871622371266458716684339120603115383484133772820985637126335208000000000000000000000000 : Int) (2724635791487366458443723820715035063399873548500484428227076792141157025524671110067159701076707042172864124542659539924967739164762091 : Int)
    geometryRow048_jensenBound_numerator_no_slash geometryRow048_jensenBound_numerator_parse
    geometryRow048_jensenBound_denominator_parse geometryRow048_jensenBound_denominator_nonzero

theorem geometryRow048_jensenBound_read :
    rationalField geometryRowsJson048 "jensen_bound" = .ok geometryRowsTyped048.jensenBound :=
  original_rationalField_of_string geometryRowsJson048 "jensen_bound" geometryRow048_jensenBoundText
    geometryRowsTyped048.jensenBound geometryRow048_jensenBound_field geometryRow048_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_factorMaxima_before"
  err.flush

theorem geometryRow048_factorMaxima_read :
    rationalArrayField geometryRowsJson048 "factor_maxima" = .ok geometryRowsTyped048.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_gapWeightedMeans_before"
  err.flush

theorem geometryRow048_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson048 "gap_weighted_means" = .ok geometryRowsTyped048.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow048_floorChars : List Char := ['6', '4', '4', '7', '9', '5', '3', '0', '8', '3', '3', '7', '4']
noncomputable def geometryRow048_floorText : String := String.ofList geometryRow048_floorChars

theorem geometryRow048_floor_text_read :
    geometryRowsJson048.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow048_floorText := by rfl

theorem geometryRow048_floor_chars_parse :
    SourceJson.intChars geometryRow048_floorChars = some (6447953083374 : Int) := by decide +kernel

theorem geometryRow048_floor_parse :
    parseInteger geometryRow048_floorText = .ok geometryRowsTyped048.jensenFloorQ96 := by
  simp only [geometryRow048_floorText, parseInteger, String.toList_ofList, geometryRow048_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_048 :
    decodeGeometryRow geometryRowsJson048 = .ok geometryRowsTyped048 :=
  original_geometryRow_of_fields geometryRowsJson048 geometryRowsTyped048 geometryRow048_floorText
    geometryRow048_simplexId_read geometryRow048_vertexIds_read
    geometryRow048_physicalVolume_read geometryRow048_meanGap_read
    geometryRow048_factorMaxima_read geometryRow048_gapWeightedMeans_read
    geometryRow048_jensenBound_read geometryRow048_floor_text_read geometryRow048_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_048_original_decoder_complete"
  err.flush

#print axioms geometryRow048_simplexId_read
#print axioms geometryRow048_vertexIds_read
#print axioms geometryRow048_physicalVolume_field
#print axioms geometryRow048_physicalVolume_numerator_no_slash
#print axioms geometryRow048_physicalVolume_numerator_parse
#print axioms geometryRow048_physicalVolume_denominator_parse
#print axioms geometryRow048_physicalVolume_denominator_nonzero
#print axioms geometryRow048_physicalVolume_parse
#print axioms geometryRow048_physicalVolume_read
#print axioms geometryRow048_meanGap_field
#print axioms geometryRow048_meanGap_numerator_no_slash
#print axioms geometryRow048_meanGap_numerator_parse
#print axioms geometryRow048_meanGap_denominator_parse
#print axioms geometryRow048_meanGap_denominator_nonzero
#print axioms geometryRow048_meanGap_parse
#print axioms geometryRow048_meanGap_read
#print axioms geometryRow048_jensenBound_field
#print axioms geometryRow048_jensenBound_numerator_no_slash
#print axioms geometryRow048_jensenBound_numerator_parse
#print axioms geometryRow048_jensenBound_denominator_parse
#print axioms geometryRow048_jensenBound_denominator_nonzero
#print axioms geometryRow048_jensenBound_parse
#print axioms geometryRow048_jensenBound_read
#print axioms geometryRow048_factorMaxima_read
#print axioms geometryRow048_gapWeightedMeans_read
#print axioms geometryRow048_floor_text_read
#print axioms geometryRow048_floor_chars_parse
#print axioms geometryRow048_floor_parse
#print axioms decode_geometry_Rows_048

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
