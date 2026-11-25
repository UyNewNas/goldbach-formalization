import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900

/-! Original GeometryRow 38: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson038 : SourceJson :=
  (simplicesChunk038Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped038 : GeometryRow :=
  { simplexId := 38,
    vertexIds := #[27, 25, 24, 22, 21, 8, 5, 3, 1],
    physicalVolume := ((2262221448900352316096587712478587 : ℚ) / (116810070451200000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1450004667103 : ℚ) / (15896160000000 : ℚ)), ((1461440343691 : ℚ) / (15896160000000 : ℚ)), ((1092993814469 : ℚ) / (8831200000000 : ℚ)), ((932568233777 : ℚ) / (9935100000000 : ℚ)), ((1380223728043 : ℚ) / (15896160000000 : ℚ)), ((616217293051 : ℚ) / (8831200000000 : ℚ)), ((1396964498123 : ℚ) / (39740400000000 : ℚ)), ((1330747100779 : ℚ) / (39740400000000 : ℚ)), ((99636991397 : ℚ) / (3179232000000 : ℚ)), ((498182837497 : ℚ) / (15896160000000 : ℚ))],
    jensenBound := ((7690936573973245866308710165931674725171728639650304953429835043330859089612767232000000000000000000000 : ℚ) / (169520588167773089058950036871074983787767865331853161776470871266916468800307004938226731761924647855209754575120461621 : ℚ)),
    jensenFloorQ96 := (3594482412759 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_simplexId_before"
  err.flush

theorem geometryRow038_simplexId_read :
    geometryRowsJson038.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped038.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_vertexIds_before"
  err.flush

theorem geometryRow038_vertexIds_read :
    geometryRowsJson038.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped038.vertexIds := by decide +kernel

noncomputable def geometryRow038_physicalVolumeNumeratorChars : List Char := ['2', '2', '6', '2', '2', '2', '1', '4', '4', '8', '9', '0', '0', '3', '5', '2', '3', '1', '6', '0', '9', '6', '5', '8', '7', '7', '1', '2', '4', '7', '8', '5', '8', '7']
noncomputable def geometryRow038_physicalVolumeDenominatorChars : List Char := ['1', '1', '6', '8', '1', '0', '0', '7', '0', '4', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_physicalVolumeText : String := String.ofList (geometryRow038_physicalVolumeNumeratorChars ++ '/' :: geometryRow038_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_physicalVolume_before_field"
  err.flush

theorem geometryRow038_physicalVolume_field :
    geometryRowsJson038.getObjVal? "physical_volume" = .ok (.str geometryRow038_physicalVolumeText) := by rfl

theorem geometryRow038_physicalVolume_numerator_no_slash :
    geometryRow038_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeNumeratorChars = some (2262221448900352316096587712478587 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeDenominatorChars = some (116810070451200000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_nonzero : (116810070451200000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_physicalVolume_parse :
    parseRational geometryRow038_physicalVolumeText = .ok geometryRowsTyped038.physicalVolume :=
  original_rational_fraction_of_chars geometryRow038_physicalVolumeNumeratorChars geometryRow038_physicalVolumeDenominatorChars
    (2262221448900352316096587712478587 : Int) (116810070451200000000000000000000000000000000000000000000000 : Int)
    geometryRow038_physicalVolume_numerator_no_slash geometryRow038_physicalVolume_numerator_parse
    geometryRow038_physicalVolume_denominator_parse geometryRow038_physicalVolume_denominator_nonzero

theorem geometryRow038_physicalVolume_read :
    rationalField geometryRowsJson038 "physical_volume" = .ok geometryRowsTyped038.physicalVolume :=
  original_rationalField_of_string geometryRowsJson038 "physical_volume" geometryRow038_physicalVolumeText
    geometryRowsTyped038.physicalVolume geometryRow038_physicalVolume_field geometryRow038_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_physicalVolume_complete"
  err.flush

noncomputable def geometryRow038_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow038_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_meanGapText : String := String.ofList (geometryRow038_meanGapNumeratorChars ++ '/' :: geometryRow038_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_meanGap_before_field"
  err.flush

theorem geometryRow038_meanGap_field :
    geometryRowsJson038.getObjVal? "mean_gap" = .ok (.str geometryRow038_meanGapText) := by rfl

theorem geometryRow038_meanGap_numerator_no_slash :
    geometryRow038_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_meanGap_numerator_parse :
    SourceJson.intChars geometryRow038_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_parse :
    SourceJson.intChars geometryRow038_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_meanGap_parse :
    parseRational geometryRow038_meanGapText = .ok geometryRowsTyped038.meanGap :=
  original_rational_fraction_of_chars geometryRow038_meanGapNumeratorChars geometryRow038_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow038_meanGap_numerator_no_slash geometryRow038_meanGap_numerator_parse
    geometryRow038_meanGap_denominator_parse geometryRow038_meanGap_denominator_nonzero

theorem geometryRow038_meanGap_read :
    rationalField geometryRowsJson038 "mean_gap" = .ok geometryRowsTyped038.meanGap :=
  original_rationalField_of_string geometryRowsJson038 "mean_gap" geometryRow038_meanGapText
    geometryRowsTyped038.meanGap geometryRow038_meanGap_field geometryRow038_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_meanGap_complete"
  err.flush

noncomputable def geometryRow038_jensenBoundNumeratorChars : List Char := ['7', '6', '9', '0', '9', '3', '6', '5', '7', '3', '9', '7', '3', '2', '4', '5', '8', '6', '6', '3', '0', '8', '7', '1', '0', '1', '6', '5', '9', '3', '1', '6', '7', '4', '7', '2', '5', '1', '7', '1', '7', '2', '8', '6', '3', '9', '6', '5', '0', '3', '0', '4', '9', '5', '3', '4', '2', '9', '8', '3', '5', '0', '4', '3', '3', '3', '0', '8', '5', '9', '0', '8', '9', '6', '1', '2', '7', '6', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_jensenBoundDenominatorChars : List Char := ['1', '6', '9', '5', '2', '0', '5', '8', '8', '1', '6', '7', '7', '7', '3', '0', '8', '9', '0', '5', '8', '9', '5', '0', '0', '3', '6', '8', '7', '1', '0', '7', '4', '9', '8', '3', '7', '8', '7', '7', '6', '7', '8', '6', '5', '3', '3', '1', '8', '5', '3', '1', '6', '1', '7', '7', '6', '4', '7', '0', '8', '7', '1', '2', '6', '6', '9', '1', '6', '4', '6', '8', '8', '0', '0', '3', '0', '7', '0', '0', '4', '9', '3', '8', '2', '2', '6', '7', '3', '1', '7', '6', '1', '9', '2', '4', '6', '4', '7', '8', '5', '5', '2', '0', '9', '7', '5', '4', '5', '7', '5', '1', '2', '0', '4', '6', '1', '6', '2', '1']
noncomputable def geometryRow038_jensenBoundText : String := String.ofList (geometryRow038_jensenBoundNumeratorChars ++ '/' :: geometryRow038_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_jensenBound_before_field"
  err.flush

theorem geometryRow038_jensenBound_field :
    geometryRowsJson038.getObjVal? "jensen_bound" = .ok (.str geometryRow038_jensenBoundText) := by rfl

theorem geometryRow038_jensenBound_numerator_no_slash :
    geometryRow038_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow038_jensenBoundNumeratorChars = some (7690936573973245866308710165931674725171728639650304953429835043330859089612767232000000000000000000000 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow038_jensenBoundDenominatorChars = some (169520588167773089058950036871074983787767865331853161776470871266916468800307004938226731761924647855209754575120461621 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_nonzero : (169520588167773089058950036871074983787767865331853161776470871266916468800307004938226731761924647855209754575120461621 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_jensenBound_parse :
    parseRational geometryRow038_jensenBoundText = .ok geometryRowsTyped038.jensenBound :=
  original_rational_fraction_of_chars geometryRow038_jensenBoundNumeratorChars geometryRow038_jensenBoundDenominatorChars
    (7690936573973245866308710165931674725171728639650304953429835043330859089612767232000000000000000000000 : Int) (169520588167773089058950036871074983787767865331853161776470871266916468800307004938226731761924647855209754575120461621 : Int)
    geometryRow038_jensenBound_numerator_no_slash geometryRow038_jensenBound_numerator_parse
    geometryRow038_jensenBound_denominator_parse geometryRow038_jensenBound_denominator_nonzero

theorem geometryRow038_jensenBound_read :
    rationalField geometryRowsJson038 "jensen_bound" = .ok geometryRowsTyped038.jensenBound :=
  original_rationalField_of_string geometryRowsJson038 "jensen_bound" geometryRow038_jensenBoundText
    geometryRowsTyped038.jensenBound geometryRow038_jensenBound_field geometryRow038_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_factorMaxima_before"
  err.flush

theorem geometryRow038_factorMaxima_read :
    rationalArrayField geometryRowsJson038 "factor_maxima" = .ok geometryRowsTyped038.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_gapWeightedMeans_before"
  err.flush

theorem geometryRow038_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson038 "gap_weighted_means" = .ok geometryRowsTyped038.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow038_floorChars : List Char := ['3', '5', '9', '4', '4', '8', '2', '4', '1', '2', '7', '5', '9']
noncomputable def geometryRow038_floorText : String := String.ofList geometryRow038_floorChars

theorem geometryRow038_floor_text_read :
    geometryRowsJson038.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow038_floorText := by rfl

theorem geometryRow038_floor_chars_parse :
    SourceJson.intChars geometryRow038_floorChars = some (3594482412759 : Int) := by decide +kernel

theorem geometryRow038_floor_parse :
    parseInteger geometryRow038_floorText = .ok geometryRowsTyped038.jensenFloorQ96 := by
  simp only [geometryRow038_floorText, parseInteger, String.toList_ofList, geometryRow038_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_038 :
    decodeGeometryRow geometryRowsJson038 = .ok geometryRowsTyped038 :=
  original_geometryRow_of_fields geometryRowsJson038 geometryRowsTyped038 geometryRow038_floorText
    geometryRow038_simplexId_read geometryRow038_vertexIds_read
    geometryRow038_physicalVolume_read geometryRow038_meanGap_read
    geometryRow038_factorMaxima_read geometryRow038_gapWeightedMeans_read
    geometryRow038_jensenBound_read geometryRow038_floor_text_read geometryRow038_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_038_original_decoder_complete"
  err.flush

#print axioms geometryRow038_simplexId_read
#print axioms geometryRow038_vertexIds_read
#print axioms geometryRow038_physicalVolume_field
#print axioms geometryRow038_physicalVolume_numerator_no_slash
#print axioms geometryRow038_physicalVolume_numerator_parse
#print axioms geometryRow038_physicalVolume_denominator_parse
#print axioms geometryRow038_physicalVolume_denominator_nonzero
#print axioms geometryRow038_physicalVolume_parse
#print axioms geometryRow038_physicalVolume_read
#print axioms geometryRow038_meanGap_field
#print axioms geometryRow038_meanGap_numerator_no_slash
#print axioms geometryRow038_meanGap_numerator_parse
#print axioms geometryRow038_meanGap_denominator_parse
#print axioms geometryRow038_meanGap_denominator_nonzero
#print axioms geometryRow038_meanGap_parse
#print axioms geometryRow038_meanGap_read
#print axioms geometryRow038_jensenBound_field
#print axioms geometryRow038_jensenBound_numerator_no_slash
#print axioms geometryRow038_jensenBound_numerator_parse
#print axioms geometryRow038_jensenBound_denominator_parse
#print axioms geometryRow038_jensenBound_denominator_nonzero
#print axioms geometryRow038_jensenBound_parse
#print axioms geometryRow038_jensenBound_read
#print axioms geometryRow038_factorMaxima_read
#print axioms geometryRow038_gapWeightedMeans_read
#print axioms geometryRow038_floor_text_read
#print axioms geometryRow038_floor_chars_parse
#print axioms geometryRow038_floor_parse
#print axioms decode_geometry_Rows_038

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
