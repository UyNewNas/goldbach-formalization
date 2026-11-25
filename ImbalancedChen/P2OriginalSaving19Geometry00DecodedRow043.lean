import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock01000

/-! Original GeometryRow 43: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson043 : SourceJson :=
  (simplicesChunk043Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped043 : GeometryRow :=
  { simplexId := 43,
    vertexIds := #[27, 15, 11, 9, 7, 5, 3, 2, 0],
    physicalVolume := ((352755081366086541573898189426991877197812320047 : ℚ) / (1552487696793820200960000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((19865249 : ℚ) / (23712000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1490621 : ℚ) / (16800000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((656143104600660085247 : ℚ) / (6841925491783200000000 : ℚ)), ((55323891594516360001 : ℚ) / (570160457648600000000 : ℚ)), ((2459095033010743734119 : ℚ) / (20525776475349600000000 : ℚ)), ((1823006622156579292429 : ℚ) / (20525776475349600000000 : ℚ)), ((542765855900006953157 : ℚ) / (6841925491783200000000 : ℚ)), ((1496582629566287591011 : ℚ) / (20525776475349600000000 : ℚ)), ((373696034062866699929 : ℚ) / (10262888237674800000000 : ℚ)), ((27915774936457073243 : ℚ) / (789452941359600000000 : ℚ)), ((27289332947913618313 : ℚ) / (789452941359600000000 : ℚ)), ((17064775740208313737 : ℚ) / (513144411883740000000 : ℚ))],
    jensenBound := ((20423697136124956026650379485918148649505531401407338059527185992600446274241246676168135754916272718665570588681967225509425355198628935600919728063813896953744086546875000000000000000000 : ℚ) / (22737301766205676220936737859633764873930707711089850856735971453047820727318419389733971934624273979368781817664054162401625141166470462796235466764737344058300861699033730416619912161831932647716331 : ℚ)),
    jensenFloorQ96 := (71166403669235882 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_simplexId_before"
  err.flush

theorem geometryRow043_simplexId_read :
    geometryRowsJson043.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped043.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_vertexIds_before"
  err.flush

theorem geometryRow043_vertexIds_read :
    geometryRowsJson043.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped043.vertexIds := by decide +kernel

noncomputable def geometryRow043_physicalVolumeNumeratorChars : List Char := ['3', '5', '2', '7', '5', '5', '0', '8', '1', '3', '6', '6', '0', '8', '6', '5', '4', '1', '5', '7', '3', '8', '9', '8', '1', '8', '9', '4', '2', '6', '9', '9', '1', '8', '7', '7', '1', '9', '7', '8', '1', '2', '3', '2', '0', '0', '4', '7']
noncomputable def geometryRow043_physicalVolumeDenominatorChars : List Char := ['1', '5', '5', '2', '4', '8', '7', '6', '9', '6', '7', '9', '3', '8', '2', '0', '2', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_physicalVolumeText : String := String.ofList (geometryRow043_physicalVolumeNumeratorChars ++ '/' :: geometryRow043_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_physicalVolume_before_field"
  err.flush

theorem geometryRow043_physicalVolume_field :
    geometryRowsJson043.getObjVal? "physical_volume" = .ok (.str geometryRow043_physicalVolumeText) := by rfl

theorem geometryRow043_physicalVolume_numerator_no_slash :
    geometryRow043_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeNumeratorChars = some (352755081366086541573898189426991877197812320047 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeDenominatorChars = some (1552487696793820200960000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_nonzero : (1552487696793820200960000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_physicalVolume_parse :
    parseRational geometryRow043_physicalVolumeText = .ok geometryRowsTyped043.physicalVolume :=
  original_rational_fraction_of_chars geometryRow043_physicalVolumeNumeratorChars geometryRow043_physicalVolumeDenominatorChars
    (352755081366086541573898189426991877197812320047 : Int) (1552487696793820200960000000000000000000000000000000000000000000000000 : Int)
    geometryRow043_physicalVolume_numerator_no_slash geometryRow043_physicalVolume_numerator_parse
    geometryRow043_physicalVolume_denominator_parse geometryRow043_physicalVolume_denominator_nonzero

theorem geometryRow043_physicalVolume_read :
    rationalField geometryRowsJson043 "physical_volume" = .ok geometryRowsTyped043.physicalVolume :=
  original_rationalField_of_string geometryRowsJson043 "physical_volume" geometryRow043_physicalVolumeText
    geometryRowsTyped043.physicalVolume geometryRow043_physicalVolume_field geometryRow043_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_physicalVolume_complete"
  err.flush

noncomputable def geometryRow043_meanGapNumeratorChars : List Char := ['1', '9', '8', '6', '5', '2', '4', '9']
noncomputable def geometryRow043_meanGapDenominatorChars : List Char := ['2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_meanGapText : String := String.ofList (geometryRow043_meanGapNumeratorChars ++ '/' :: geometryRow043_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_meanGap_before_field"
  err.flush

theorem geometryRow043_meanGap_field :
    geometryRowsJson043.getObjVal? "mean_gap" = .ok (.str geometryRow043_meanGapText) := by rfl

theorem geometryRow043_meanGap_numerator_no_slash :
    geometryRow043_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_meanGap_numerator_parse :
    SourceJson.intChars geometryRow043_meanGapNumeratorChars = some (19865249 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_parse :
    SourceJson.intChars geometryRow043_meanGapDenominatorChars = some (23712000000 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_nonzero : (23712000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_meanGap_parse :
    parseRational geometryRow043_meanGapText = .ok geometryRowsTyped043.meanGap :=
  original_rational_fraction_of_chars geometryRow043_meanGapNumeratorChars geometryRow043_meanGapDenominatorChars
    (19865249 : Int) (23712000000 : Int)
    geometryRow043_meanGap_numerator_no_slash geometryRow043_meanGap_numerator_parse
    geometryRow043_meanGap_denominator_parse geometryRow043_meanGap_denominator_nonzero

theorem geometryRow043_meanGap_read :
    rationalField geometryRowsJson043 "mean_gap" = .ok geometryRowsTyped043.meanGap :=
  original_rationalField_of_string geometryRowsJson043 "mean_gap" geometryRow043_meanGapText
    geometryRowsTyped043.meanGap geometryRow043_meanGap_field geometryRow043_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_meanGap_complete"
  err.flush

noncomputable def geometryRow043_jensenBoundNumeratorChars : List Char := ['2', '0', '4', '2', '3', '6', '9', '7', '1', '3', '6', '1', '2', '4', '9', '5', '6', '0', '2', '6', '6', '5', '0', '3', '7', '9', '4', '8', '5', '9', '1', '8', '1', '4', '8', '6', '4', '9', '5', '0', '5', '5', '3', '1', '4', '0', '1', '4', '0', '7', '3', '3', '8', '0', '5', '9', '5', '2', '7', '1', '8', '5', '9', '9', '2', '6', '0', '0', '4', '4', '6', '2', '7', '4', '2', '4', '1', '2', '4', '6', '6', '7', '6', '1', '6', '8', '1', '3', '5', '7', '5', '4', '9', '1', '6', '2', '7', '2', '7', '1', '8', '6', '6', '5', '5', '7', '0', '5', '8', '8', '6', '8', '1', '9', '6', '7', '2', '2', '5', '5', '0', '9', '4', '2', '5', '3', '5', '5', '1', '9', '8', '6', '2', '8', '9', '3', '5', '6', '0', '0', '9', '1', '9', '7', '2', '8', '0', '6', '3', '8', '1', '3', '8', '9', '6', '9', '5', '3', '7', '4', '4', '0', '8', '6', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_jensenBoundDenominatorChars : List Char := ['2', '2', '7', '3', '7', '3', '0', '1', '7', '6', '6', '2', '0', '5', '6', '7', '6', '2', '2', '0', '9', '3', '6', '7', '3', '7', '8', '5', '9', '6', '3', '3', '7', '6', '4', '8', '7', '3', '9', '3', '0', '7', '0', '7', '7', '1', '1', '0', '8', '9', '8', '5', '0', '8', '5', '6', '7', '3', '5', '9', '7', '1', '4', '5', '3', '0', '4', '7', '8', '2', '0', '7', '2', '7', '3', '1', '8', '4', '1', '9', '3', '8', '9', '7', '3', '3', '9', '7', '1', '9', '3', '4', '6', '2', '4', '2', '7', '3', '9', '7', '9', '3', '6', '8', '7', '8', '1', '8', '1', '7', '6', '6', '4', '0', '5', '4', '1', '6', '2', '4', '0', '1', '6', '2', '5', '1', '4', '1', '1', '6', '6', '4', '7', '0', '4', '6', '2', '7', '9', '6', '2', '3', '5', '4', '6', '6', '7', '6', '4', '7', '3', '7', '3', '4', '4', '0', '5', '8', '3', '0', '0', '8', '6', '1', '6', '9', '9', '0', '3', '3', '7', '3', '0', '4', '1', '6', '6', '1', '9', '9', '1', '2', '1', '6', '1', '8', '3', '1', '9', '3', '2', '6', '4', '7', '7', '1', '6', '3', '3', '1']
noncomputable def geometryRow043_jensenBoundText : String := String.ofList (geometryRow043_jensenBoundNumeratorChars ++ '/' :: geometryRow043_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_jensenBound_before_field"
  err.flush

theorem geometryRow043_jensenBound_field :
    geometryRowsJson043.getObjVal? "jensen_bound" = .ok (.str geometryRow043_jensenBoundText) := by rfl

theorem geometryRow043_jensenBound_numerator_no_slash :
    geometryRow043_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow043_jensenBoundNumeratorChars = some (20423697136124956026650379485918148649505531401407338059527185992600446274241246676168135754916272718665570588681967225509425355198628935600919728063813896953744086546875000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow043_jensenBoundDenominatorChars = some (22737301766205676220936737859633764873930707711089850856735971453047820727318419389733971934624273979368781817664054162401625141166470462796235466764737344058300861699033730416619912161831932647716331 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_nonzero : (22737301766205676220936737859633764873930707711089850856735971453047820727318419389733971934624273979368781817664054162401625141166470462796235466764737344058300861699033730416619912161831932647716331 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_jensenBound_parse :
    parseRational geometryRow043_jensenBoundText = .ok geometryRowsTyped043.jensenBound :=
  original_rational_fraction_of_chars geometryRow043_jensenBoundNumeratorChars geometryRow043_jensenBoundDenominatorChars
    (20423697136124956026650379485918148649505531401407338059527185992600446274241246676168135754916272718665570588681967225509425355198628935600919728063813896953744086546875000000000000000000 : Int) (22737301766205676220936737859633764873930707711089850856735971453047820727318419389733971934624273979368781817664054162401625141166470462796235466764737344058300861699033730416619912161831932647716331 : Int)
    geometryRow043_jensenBound_numerator_no_slash geometryRow043_jensenBound_numerator_parse
    geometryRow043_jensenBound_denominator_parse geometryRow043_jensenBound_denominator_nonzero

theorem geometryRow043_jensenBound_read :
    rationalField geometryRowsJson043 "jensen_bound" = .ok geometryRowsTyped043.jensenBound :=
  original_rationalField_of_string geometryRowsJson043 "jensen_bound" geometryRow043_jensenBoundText
    geometryRowsTyped043.jensenBound geometryRow043_jensenBound_field geometryRow043_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_factorMaxima_before"
  err.flush

theorem geometryRow043_factorMaxima_read :
    rationalArrayField geometryRowsJson043 "factor_maxima" = .ok geometryRowsTyped043.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_gapWeightedMeans_before"
  err.flush

theorem geometryRow043_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson043 "gap_weighted_means" = .ok geometryRowsTyped043.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow043_floorChars : List Char := ['7', '1', '1', '6', '6', '4', '0', '3', '6', '6', '9', '2', '3', '5', '8', '8', '2']
noncomputable def geometryRow043_floorText : String := String.ofList geometryRow043_floorChars

theorem geometryRow043_floor_text_read :
    geometryRowsJson043.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow043_floorText := by rfl

theorem geometryRow043_floor_chars_parse :
    SourceJson.intChars geometryRow043_floorChars = some (71166403669235882 : Int) := by decide +kernel

theorem geometryRow043_floor_parse :
    parseInteger geometryRow043_floorText = .ok geometryRowsTyped043.jensenFloorQ96 := by
  simp only [geometryRow043_floorText, parseInteger, String.toList_ofList, geometryRow043_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_043 :
    decodeGeometryRow geometryRowsJson043 = .ok geometryRowsTyped043 :=
  original_geometryRow_of_fields geometryRowsJson043 geometryRowsTyped043 geometryRow043_floorText
    geometryRow043_simplexId_read geometryRow043_vertexIds_read
    geometryRow043_physicalVolume_read geometryRow043_meanGap_read
    geometryRow043_factorMaxima_read geometryRow043_gapWeightedMeans_read
    geometryRow043_jensenBound_read geometryRow043_floor_text_read geometryRow043_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_043_original_decoder_complete"
  err.flush

#print axioms geometryRow043_simplexId_read
#print axioms geometryRow043_vertexIds_read
#print axioms geometryRow043_physicalVolume_field
#print axioms geometryRow043_physicalVolume_numerator_no_slash
#print axioms geometryRow043_physicalVolume_numerator_parse
#print axioms geometryRow043_physicalVolume_denominator_parse
#print axioms geometryRow043_physicalVolume_denominator_nonzero
#print axioms geometryRow043_physicalVolume_parse
#print axioms geometryRow043_physicalVolume_read
#print axioms geometryRow043_meanGap_field
#print axioms geometryRow043_meanGap_numerator_no_slash
#print axioms geometryRow043_meanGap_numerator_parse
#print axioms geometryRow043_meanGap_denominator_parse
#print axioms geometryRow043_meanGap_denominator_nonzero
#print axioms geometryRow043_meanGap_parse
#print axioms geometryRow043_meanGap_read
#print axioms geometryRow043_jensenBound_field
#print axioms geometryRow043_jensenBound_numerator_no_slash
#print axioms geometryRow043_jensenBound_numerator_parse
#print axioms geometryRow043_jensenBound_denominator_parse
#print axioms geometryRow043_jensenBound_denominator_nonzero
#print axioms geometryRow043_jensenBound_parse
#print axioms geometryRow043_jensenBound_read
#print axioms geometryRow043_factorMaxima_read
#print axioms geometryRow043_gapWeightedMeans_read
#print axioms geometryRow043_floor_text_read
#print axioms geometryRow043_floor_chars_parse
#print axioms geometryRow043_floor_parse
#print axioms decode_geometry_Rows_043

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
