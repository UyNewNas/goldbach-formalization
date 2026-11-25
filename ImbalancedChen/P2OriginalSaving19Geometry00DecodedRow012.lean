import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00300

/-! Original GeometryRow 12: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson012 : SourceJson :=
  (simplicesChunk012Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped012 : GeometryRow :=
  { simplexId := 12,
    vertexIds := #[27, 25, 23, 21, 9, 5, 3, 2, 0],
    physicalVolume := ((1359379192682495073070501315800520568977 : ℚ) / (13346463127725000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((19865249 : ℚ) / (23712000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1874913283651996491019 : ℚ) / (20525776475349600000000 : ℚ)), ((949072033626302597657 : ℚ) / (10262888237674800000000 : ℚ)), ((2512522823934078556127 : ℚ) / (20525776475349600000000 : ℚ)), ((147081545161860113123 : ℚ) / (1578905882719200000000 : ℚ)), ((39054236450208229711 : ℚ) / (456128366118880000000 : ℚ)), ((1443154838642952769003 : ℚ) / (20525776475349600000000 : ℚ)), ((179609403168764829503 : ℚ) / (5131444118837400000000 : ℚ)), ((19481578135422865671 : ℚ) / (570160457648600000000 : ℚ)), ((84236951779548545417 : ℚ) / (2565722059418700000000 : ℚ)), ((107827559264010865553 : ℚ) / (3420962745891600000000 : ℚ))],
    jensenBound := ((186743438332163528141783289885135811719816225465661315127831268501822571211226851592051029192191356296665420068267354086973342592605867510582154359214027360872521583820800000000000000000000000 : ℚ) / (392639520027817475479012222306125696209635230418194596285291778060564144774590547741999367203626233733085372776434501322789627122801056567367208876225111908060857576461883782830402172449777641009111912049 : ℚ)),
    jensenFloorQ96 := (37681737894353939 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_simplexId_before"
  err.flush

theorem geometryRow012_simplexId_read :
    geometryRowsJson012.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped012.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_vertexIds_before"
  err.flush

theorem geometryRow012_vertexIds_read :
    geometryRowsJson012.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped012.vertexIds := by decide +kernel

noncomputable def geometryRow012_physicalVolumeNumeratorChars : List Char := ['1', '3', '5', '9', '3', '7', '9', '1', '9', '2', '6', '8', '2', '4', '9', '5', '0', '7', '3', '0', '7', '0', '5', '0', '1', '3', '1', '5', '8', '0', '0', '5', '2', '0', '5', '6', '8', '9', '7', '7']
noncomputable def geometryRow012_physicalVolumeDenominatorChars : List Char := ['1', '3', '3', '4', '6', '4', '6', '3', '1', '2', '7', '7', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_physicalVolumeText : String := String.ofList (geometryRow012_physicalVolumeNumeratorChars ++ '/' :: geometryRow012_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_physicalVolume_before_field"
  err.flush

theorem geometryRow012_physicalVolume_field :
    geometryRowsJson012.getObjVal? "physical_volume" = .ok (.str geometryRow012_physicalVolumeText) := by rfl

theorem geometryRow012_physicalVolume_numerator_no_slash :
    geometryRow012_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeNumeratorChars = some (1359379192682495073070501315800520568977 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeDenominatorChars = some (13346463127725000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_nonzero : (13346463127725000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_physicalVolume_parse :
    parseRational geometryRow012_physicalVolumeText = .ok geometryRowsTyped012.physicalVolume :=
  original_rational_fraction_of_chars geometryRow012_physicalVolumeNumeratorChars geometryRow012_physicalVolumeDenominatorChars
    (1359379192682495073070501315800520568977 : Int) (13346463127725000000000000000000000000000000000000000000000000 : Int)
    geometryRow012_physicalVolume_numerator_no_slash geometryRow012_physicalVolume_numerator_parse
    geometryRow012_physicalVolume_denominator_parse geometryRow012_physicalVolume_denominator_nonzero

theorem geometryRow012_physicalVolume_read :
    rationalField geometryRowsJson012 "physical_volume" = .ok geometryRowsTyped012.physicalVolume :=
  original_rationalField_of_string geometryRowsJson012 "physical_volume" geometryRow012_physicalVolumeText
    geometryRowsTyped012.physicalVolume geometryRow012_physicalVolume_field geometryRow012_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_physicalVolume_complete"
  err.flush

noncomputable def geometryRow012_meanGapNumeratorChars : List Char := ['1', '9', '8', '6', '5', '2', '4', '9']
noncomputable def geometryRow012_meanGapDenominatorChars : List Char := ['2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_meanGapText : String := String.ofList (geometryRow012_meanGapNumeratorChars ++ '/' :: geometryRow012_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_meanGap_before_field"
  err.flush

theorem geometryRow012_meanGap_field :
    geometryRowsJson012.getObjVal? "mean_gap" = .ok (.str geometryRow012_meanGapText) := by rfl

theorem geometryRow012_meanGap_numerator_no_slash :
    geometryRow012_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_meanGap_numerator_parse :
    SourceJson.intChars geometryRow012_meanGapNumeratorChars = some (19865249 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_parse :
    SourceJson.intChars geometryRow012_meanGapDenominatorChars = some (23712000000 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_nonzero : (23712000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_meanGap_parse :
    parseRational geometryRow012_meanGapText = .ok geometryRowsTyped012.meanGap :=
  original_rational_fraction_of_chars geometryRow012_meanGapNumeratorChars geometryRow012_meanGapDenominatorChars
    (19865249 : Int) (23712000000 : Int)
    geometryRow012_meanGap_numerator_no_slash geometryRow012_meanGap_numerator_parse
    geometryRow012_meanGap_denominator_parse geometryRow012_meanGap_denominator_nonzero

theorem geometryRow012_meanGap_read :
    rationalField geometryRowsJson012 "mean_gap" = .ok geometryRowsTyped012.meanGap :=
  original_rationalField_of_string geometryRowsJson012 "mean_gap" geometryRow012_meanGapText
    geometryRowsTyped012.meanGap geometryRow012_meanGap_field geometryRow012_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_meanGap_complete"
  err.flush

noncomputable def geometryRow012_jensenBoundNumeratorChars : List Char := ['1', '8', '6', '7', '4', '3', '4', '3', '8', '3', '3', '2', '1', '6', '3', '5', '2', '8', '1', '4', '1', '7', '8', '3', '2', '8', '9', '8', '8', '5', '1', '3', '5', '8', '1', '1', '7', '1', '9', '8', '1', '6', '2', '2', '5', '4', '6', '5', '6', '6', '1', '3', '1', '5', '1', '2', '7', '8', '3', '1', '2', '6', '8', '5', '0', '1', '8', '2', '2', '5', '7', '1', '2', '1', '1', '2', '2', '6', '8', '5', '1', '5', '9', '2', '0', '5', '1', '0', '2', '9', '1', '9', '2', '1', '9', '1', '3', '5', '6', '2', '9', '6', '6', '6', '5', '4', '2', '0', '0', '6', '8', '2', '6', '7', '3', '5', '4', '0', '8', '6', '9', '7', '3', '3', '4', '2', '5', '9', '2', '6', '0', '5', '8', '6', '7', '5', '1', '0', '5', '8', '2', '1', '5', '4', '3', '5', '9', '2', '1', '4', '0', '2', '7', '3', '6', '0', '8', '7', '2', '5', '2', '1', '5', '8', '3', '8', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_jensenBoundDenominatorChars : List Char := ['3', '9', '2', '6', '3', '9', '5', '2', '0', '0', '2', '7', '8', '1', '7', '4', '7', '5', '4', '7', '9', '0', '1', '2', '2', '2', '2', '3', '0', '6', '1', '2', '5', '6', '9', '6', '2', '0', '9', '6', '3', '5', '2', '3', '0', '4', '1', '8', '1', '9', '4', '5', '9', '6', '2', '8', '5', '2', '9', '1', '7', '7', '8', '0', '6', '0', '5', '6', '4', '1', '4', '4', '7', '7', '4', '5', '9', '0', '5', '4', '7', '7', '4', '1', '9', '9', '9', '3', '6', '7', '2', '0', '3', '6', '2', '6', '2', '3', '3', '7', '3', '3', '0', '8', '5', '3', '7', '2', '7', '7', '6', '4', '3', '4', '5', '0', '1', '3', '2', '2', '7', '8', '9', '6', '2', '7', '1', '2', '2', '8', '0', '1', '0', '5', '6', '5', '6', '7', '3', '6', '7', '2', '0', '8', '8', '7', '6', '2', '2', '5', '1', '1', '1', '9', '0', '8', '0', '6', '0', '8', '5', '7', '5', '7', '6', '4', '6', '1', '8', '8', '3', '7', '8', '2', '8', '3', '0', '4', '0', '2', '1', '7', '2', '4', '4', '9', '7', '7', '7', '6', '4', '1', '0', '0', '9', '1', '1', '1', '9', '1', '2', '0', '4', '9']
noncomputable def geometryRow012_jensenBoundText : String := String.ofList (geometryRow012_jensenBoundNumeratorChars ++ '/' :: geometryRow012_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_jensenBound_before_field"
  err.flush

theorem geometryRow012_jensenBound_field :
    geometryRowsJson012.getObjVal? "jensen_bound" = .ok (.str geometryRow012_jensenBoundText) := by rfl

theorem geometryRow012_jensenBound_numerator_no_slash :
    geometryRow012_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow012_jensenBoundNumeratorChars = some (186743438332163528141783289885135811719816225465661315127831268501822571211226851592051029192191356296665420068267354086973342592605867510582154359214027360872521583820800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow012_jensenBoundDenominatorChars = some (392639520027817475479012222306125696209635230418194596285291778060564144774590547741999367203626233733085372776434501322789627122801056567367208876225111908060857576461883782830402172449777641009111912049 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_nonzero : (392639520027817475479012222306125696209635230418194596285291778060564144774590547741999367203626233733085372776434501322789627122801056567367208876225111908060857576461883782830402172449777641009111912049 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_jensenBound_parse :
    parseRational geometryRow012_jensenBoundText = .ok geometryRowsTyped012.jensenBound :=
  original_rational_fraction_of_chars geometryRow012_jensenBoundNumeratorChars geometryRow012_jensenBoundDenominatorChars
    (186743438332163528141783289885135811719816225465661315127831268501822571211226851592051029192191356296665420068267354086973342592605867510582154359214027360872521583820800000000000000000000000 : Int) (392639520027817475479012222306125696209635230418194596285291778060564144774590547741999367203626233733085372776434501322789627122801056567367208876225111908060857576461883782830402172449777641009111912049 : Int)
    geometryRow012_jensenBound_numerator_no_slash geometryRow012_jensenBound_numerator_parse
    geometryRow012_jensenBound_denominator_parse geometryRow012_jensenBound_denominator_nonzero

theorem geometryRow012_jensenBound_read :
    rationalField geometryRowsJson012 "jensen_bound" = .ok geometryRowsTyped012.jensenBound :=
  original_rationalField_of_string geometryRowsJson012 "jensen_bound" geometryRow012_jensenBoundText
    geometryRowsTyped012.jensenBound geometryRow012_jensenBound_field geometryRow012_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_factorMaxima_before"
  err.flush

theorem geometryRow012_factorMaxima_read :
    rationalArrayField geometryRowsJson012 "factor_maxima" = .ok geometryRowsTyped012.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_gapWeightedMeans_before"
  err.flush

theorem geometryRow012_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson012 "gap_weighted_means" = .ok geometryRowsTyped012.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow012_floorChars : List Char := ['3', '7', '6', '8', '1', '7', '3', '7', '8', '9', '4', '3', '5', '3', '9', '3', '9']
noncomputable def geometryRow012_floorText : String := String.ofList geometryRow012_floorChars

theorem geometryRow012_floor_text_read :
    geometryRowsJson012.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow012_floorText := by rfl

theorem geometryRow012_floor_chars_parse :
    SourceJson.intChars geometryRow012_floorChars = some (37681737894353939 : Int) := by decide +kernel

theorem geometryRow012_floor_parse :
    parseInteger geometryRow012_floorText = .ok geometryRowsTyped012.jensenFloorQ96 := by
  simp only [geometryRow012_floorText, parseInteger, String.toList_ofList, geometryRow012_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_012 :
    decodeGeometryRow geometryRowsJson012 = .ok geometryRowsTyped012 :=
  original_geometryRow_of_fields geometryRowsJson012 geometryRowsTyped012 geometryRow012_floorText
    geometryRow012_simplexId_read geometryRow012_vertexIds_read
    geometryRow012_physicalVolume_read geometryRow012_meanGap_read
    geometryRow012_factorMaxima_read geometryRow012_gapWeightedMeans_read
    geometryRow012_jensenBound_read geometryRow012_floor_text_read geometryRow012_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_012_original_decoder_complete"
  err.flush

#print axioms geometryRow012_simplexId_read
#print axioms geometryRow012_vertexIds_read
#print axioms geometryRow012_physicalVolume_field
#print axioms geometryRow012_physicalVolume_numerator_no_slash
#print axioms geometryRow012_physicalVolume_numerator_parse
#print axioms geometryRow012_physicalVolume_denominator_parse
#print axioms geometryRow012_physicalVolume_denominator_nonzero
#print axioms geometryRow012_physicalVolume_parse
#print axioms geometryRow012_physicalVolume_read
#print axioms geometryRow012_meanGap_field
#print axioms geometryRow012_meanGap_numerator_no_slash
#print axioms geometryRow012_meanGap_numerator_parse
#print axioms geometryRow012_meanGap_denominator_parse
#print axioms geometryRow012_meanGap_denominator_nonzero
#print axioms geometryRow012_meanGap_parse
#print axioms geometryRow012_meanGap_read
#print axioms geometryRow012_jensenBound_field
#print axioms geometryRow012_jensenBound_numerator_no_slash
#print axioms geometryRow012_jensenBound_numerator_parse
#print axioms geometryRow012_jensenBound_denominator_parse
#print axioms geometryRow012_jensenBound_denominator_nonzero
#print axioms geometryRow012_jensenBound_parse
#print axioms geometryRow012_jensenBound_read
#print axioms geometryRow012_factorMaxima_read
#print axioms geometryRow012_gapWeightedMeans_read
#print axioms geometryRow012_floor_text_read
#print axioms geometryRow012_floor_chars_parse
#print axioms geometryRow012_floor_parse
#print axioms decode_geometry_Rows_012

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
