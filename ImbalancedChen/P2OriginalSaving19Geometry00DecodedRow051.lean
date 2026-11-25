import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01200

/-! Original GeometryRow 51: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson051 : SourceJson :=
  (simplicesChunk051Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped051 : GeometryRow :=
  { simplexId := 51,
    vertexIds := #[27, 26, 24, 22, 21, 8, 5, 3, 1],
    physicalVolume := ((2895550772252448218861764197365047 : ℚ) / (149516890177536000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1039772135021 : ℚ) / (11354400000000 : ℚ)), ((1047940475441 : ℚ) / (11354400000000 : ℚ)), ((1412034530603 : ℚ) / (11354400000000 : ℚ)), ((133899691387 : ℚ) / (1419300000000 : ℚ)), ((980468827537 : ℚ) / (11354400000000 : ℚ)), ((785522607637 : ℚ) / (11354400000000 : ℚ)), ((195512219693 : ℚ) / (5677200000000 : ℚ)), ((21198053477 : ℚ) / (630800000000 : ℚ)), ((119065715369 : ℚ) / (3784800000000 : ℚ)), ((39688487683 : ℚ) / (1261600000000 : ℚ))],
    jensenBound := ((5654248587941921007494860269171908431547424978854673222205569177600000000000000000000000000000 : ℚ) / (123909477631712809173088950816972430839678927116529419363639697766997732319149841262735406791717847772509501041 : ℚ)),
    jensenFloorQ96 := (3615346740085 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_simplexId_before"
  err.flush

theorem geometryRow051_simplexId_read :
    geometryRowsJson051.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped051.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_vertexIds_before"
  err.flush

theorem geometryRow051_vertexIds_read :
    geometryRowsJson051.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped051.vertexIds := by decide +kernel

noncomputable def geometryRow051_physicalVolumeNumeratorChars : List Char := ['2', '8', '9', '5', '5', '5', '0', '7', '7', '2', '2', '5', '2', '4', '4', '8', '2', '1', '8', '8', '6', '1', '7', '6', '4', '1', '9', '7', '3', '6', '5', '0', '4', '7']
noncomputable def geometryRow051_physicalVolumeDenominatorChars : List Char := ['1', '4', '9', '5', '1', '6', '8', '9', '0', '1', '7', '7', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_physicalVolumeText : String := String.ofList (geometryRow051_physicalVolumeNumeratorChars ++ '/' :: geometryRow051_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_physicalVolume_before_field"
  err.flush

theorem geometryRow051_physicalVolume_field :
    geometryRowsJson051.getObjVal? "physical_volume" = .ok (.str geometryRow051_physicalVolumeText) := by rfl

theorem geometryRow051_physicalVolume_numerator_no_slash :
    geometryRow051_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeNumeratorChars = some (2895550772252448218861764197365047 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeDenominatorChars = some (149516890177536000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_nonzero : (149516890177536000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_physicalVolume_parse :
    parseRational geometryRow051_physicalVolumeText = .ok geometryRowsTyped051.physicalVolume :=
  original_rational_fraction_of_chars geometryRow051_physicalVolumeNumeratorChars geometryRow051_physicalVolumeDenominatorChars
    (2895550772252448218861764197365047 : Int) (149516890177536000000000000000000000000000000000000000000000 : Int)
    geometryRow051_physicalVolume_numerator_no_slash geometryRow051_physicalVolume_numerator_parse
    geometryRow051_physicalVolume_denominator_parse geometryRow051_physicalVolume_denominator_nonzero

theorem geometryRow051_physicalVolume_read :
    rationalField geometryRowsJson051 "physical_volume" = .ok geometryRowsTyped051.physicalVolume :=
  original_rationalField_of_string geometryRowsJson051 "physical_volume" geometryRow051_physicalVolumeText
    geometryRowsTyped051.physicalVolume geometryRow051_physicalVolume_field geometryRow051_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_physicalVolume_complete"
  err.flush

noncomputable def geometryRow051_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow051_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_meanGapText : String := String.ofList (geometryRow051_meanGapNumeratorChars ++ '/' :: geometryRow051_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_meanGap_before_field"
  err.flush

theorem geometryRow051_meanGap_field :
    geometryRowsJson051.getObjVal? "mean_gap" = .ok (.str geometryRow051_meanGapText) := by rfl

theorem geometryRow051_meanGap_numerator_no_slash :
    geometryRow051_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_meanGap_numerator_parse :
    SourceJson.intChars geometryRow051_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_parse :
    SourceJson.intChars geometryRow051_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_meanGap_parse :
    parseRational geometryRow051_meanGapText = .ok geometryRowsTyped051.meanGap :=
  original_rational_fraction_of_chars geometryRow051_meanGapNumeratorChars geometryRow051_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow051_meanGap_numerator_no_slash geometryRow051_meanGap_numerator_parse
    geometryRow051_meanGap_denominator_parse geometryRow051_meanGap_denominator_nonzero

theorem geometryRow051_meanGap_read :
    rationalField geometryRowsJson051 "mean_gap" = .ok geometryRowsTyped051.meanGap :=
  original_rationalField_of_string geometryRowsJson051 "mean_gap" geometryRow051_meanGapText
    geometryRowsTyped051.meanGap geometryRow051_meanGap_field geometryRow051_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_meanGap_complete"
  err.flush

noncomputable def geometryRow051_jensenBoundNumeratorChars : List Char := ['5', '6', '5', '4', '2', '4', '8', '5', '8', '7', '9', '4', '1', '9', '2', '1', '0', '0', '7', '4', '9', '4', '8', '6', '0', '2', '6', '9', '1', '7', '1', '9', '0', '8', '4', '3', '1', '5', '4', '7', '4', '2', '4', '9', '7', '8', '8', '5', '4', '6', '7', '3', '2', '2', '2', '2', '0', '5', '5', '6', '9', '1', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_jensenBoundDenominatorChars : List Char := ['1', '2', '3', '9', '0', '9', '4', '7', '7', '6', '3', '1', '7', '1', '2', '8', '0', '9', '1', '7', '3', '0', '8', '8', '9', '5', '0', '8', '1', '6', '9', '7', '2', '4', '3', '0', '8', '3', '9', '6', '7', '8', '9', '2', '7', '1', '1', '6', '5', '2', '9', '4', '1', '9', '3', '6', '3', '6', '3', '9', '6', '9', '7', '7', '6', '6', '9', '9', '7', '7', '3', '2', '3', '1', '9', '1', '4', '9', '8', '4', '1', '2', '6', '2', '7', '3', '5', '4', '0', '6', '7', '9', '1', '7', '1', '7', '8', '4', '7', '7', '7', '2', '5', '0', '9', '5', '0', '1', '0', '4', '1']
noncomputable def geometryRow051_jensenBoundText : String := String.ofList (geometryRow051_jensenBoundNumeratorChars ++ '/' :: geometryRow051_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_jensenBound_before_field"
  err.flush

theorem geometryRow051_jensenBound_field :
    geometryRowsJson051.getObjVal? "jensen_bound" = .ok (.str geometryRow051_jensenBoundText) := by rfl

theorem geometryRow051_jensenBound_numerator_no_slash :
    geometryRow051_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow051_jensenBoundNumeratorChars = some (5654248587941921007494860269171908431547424978854673222205569177600000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow051_jensenBoundDenominatorChars = some (123909477631712809173088950816972430839678927116529419363639697766997732319149841262735406791717847772509501041 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_nonzero : (123909477631712809173088950816972430839678927116529419363639697766997732319149841262735406791717847772509501041 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_jensenBound_parse :
    parseRational geometryRow051_jensenBoundText = .ok geometryRowsTyped051.jensenBound :=
  original_rational_fraction_of_chars geometryRow051_jensenBoundNumeratorChars geometryRow051_jensenBoundDenominatorChars
    (5654248587941921007494860269171908431547424978854673222205569177600000000000000000000000000000 : Int) (123909477631712809173088950816972430839678927116529419363639697766997732319149841262735406791717847772509501041 : Int)
    geometryRow051_jensenBound_numerator_no_slash geometryRow051_jensenBound_numerator_parse
    geometryRow051_jensenBound_denominator_parse geometryRow051_jensenBound_denominator_nonzero

theorem geometryRow051_jensenBound_read :
    rationalField geometryRowsJson051 "jensen_bound" = .ok geometryRowsTyped051.jensenBound :=
  original_rationalField_of_string geometryRowsJson051 "jensen_bound" geometryRow051_jensenBoundText
    geometryRowsTyped051.jensenBound geometryRow051_jensenBound_field geometryRow051_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_factorMaxima_before"
  err.flush

theorem geometryRow051_factorMaxima_read :
    rationalArrayField geometryRowsJson051 "factor_maxima" = .ok geometryRowsTyped051.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_gapWeightedMeans_before"
  err.flush

theorem geometryRow051_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson051 "gap_weighted_means" = .ok geometryRowsTyped051.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow051_floorChars : List Char := ['3', '6', '1', '5', '3', '4', '6', '7', '4', '0', '0', '8', '5']
noncomputable def geometryRow051_floorText : String := String.ofList geometryRow051_floorChars

theorem geometryRow051_floor_text_read :
    geometryRowsJson051.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow051_floorText := by rfl

theorem geometryRow051_floor_chars_parse :
    SourceJson.intChars geometryRow051_floorChars = some (3615346740085 : Int) := by decide +kernel

theorem geometryRow051_floor_parse :
    parseInteger geometryRow051_floorText = .ok geometryRowsTyped051.jensenFloorQ96 := by
  simp only [geometryRow051_floorText, parseInteger, String.toList_ofList, geometryRow051_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_051 :
    decodeGeometryRow geometryRowsJson051 = .ok geometryRowsTyped051 :=
  original_geometryRow_of_fields geometryRowsJson051 geometryRowsTyped051 geometryRow051_floorText
    geometryRow051_simplexId_read geometryRow051_vertexIds_read
    geometryRow051_physicalVolume_read geometryRow051_meanGap_read
    geometryRow051_factorMaxima_read geometryRow051_gapWeightedMeans_read
    geometryRow051_jensenBound_read geometryRow051_floor_text_read geometryRow051_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_051_original_decoder_complete"
  err.flush

#print axioms geometryRow051_simplexId_read
#print axioms geometryRow051_vertexIds_read
#print axioms geometryRow051_physicalVolume_field
#print axioms geometryRow051_physicalVolume_numerator_no_slash
#print axioms geometryRow051_physicalVolume_numerator_parse
#print axioms geometryRow051_physicalVolume_denominator_parse
#print axioms geometryRow051_physicalVolume_denominator_nonzero
#print axioms geometryRow051_physicalVolume_parse
#print axioms geometryRow051_physicalVolume_read
#print axioms geometryRow051_meanGap_field
#print axioms geometryRow051_meanGap_numerator_no_slash
#print axioms geometryRow051_meanGap_numerator_parse
#print axioms geometryRow051_meanGap_denominator_parse
#print axioms geometryRow051_meanGap_denominator_nonzero
#print axioms geometryRow051_meanGap_parse
#print axioms geometryRow051_meanGap_read
#print axioms geometryRow051_jensenBound_field
#print axioms geometryRow051_jensenBound_numerator_no_slash
#print axioms geometryRow051_jensenBound_numerator_parse
#print axioms geometryRow051_jensenBound_denominator_parse
#print axioms geometryRow051_jensenBound_denominator_nonzero
#print axioms geometryRow051_jensenBound_parse
#print axioms geometryRow051_jensenBound_read
#print axioms geometryRow051_factorMaxima_read
#print axioms geometryRow051_gapWeightedMeans_read
#print axioms geometryRow051_floor_text_read
#print axioms geometryRow051_floor_chars_parse
#print axioms geometryRow051_floor_parse
#print axioms decode_geometry_Rows_051

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
