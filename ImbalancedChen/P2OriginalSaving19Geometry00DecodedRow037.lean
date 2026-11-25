import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00900

/-! Original GeometryRow 37: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson037 : SourceJson :=
  (simplicesChunk037Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped037 : GeometryRow :=
  { simplexId := 37,
    vertexIds := #[27, 25, 24, 22, 8, 6, 5, 3, 1],
    physicalVolume := ((1149686281548322114640184779933847827 : ℚ) / (38936690150400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((7295917933859 : ℚ) / (79480800000000 : ℚ)), ((7353096316799 : ℚ) / (79480800000000 : ℚ)), ((3249288387959 : ℚ) / (26493600000000 : ℚ)), ((72837425527 : ℚ) / (794808000000 : ℚ)), ((6767499890699 : ℚ) / (79480800000000 : ℚ)), ((1878344934601 : ℚ) / (26493600000000 : ℚ)), ((1419234289709 : ℚ) / (39740400000000 : ℚ)), ((270603378473 : ℚ) / (7948080000000 : ℚ)), ((2578648936097 : ℚ) / (79480800000000 : ℚ)), ((2578638338657 : ℚ) / (79480800000000 : ℚ))],
    jensenBound := ((22360091133793313184695765686889663288592341102650668704443704608230695194591232000000000000000000000 : ℚ) / (349311549104694465410857899990434976799098154828664997244639678933993154882954285936301578839746281975640170050181057 : ℚ)),
    jensenFloorQ96 := (5071544123641 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_simplexId_before"
  err.flush

theorem geometryRow037_simplexId_read :
    geometryRowsJson037.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped037.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_vertexIds_before"
  err.flush

theorem geometryRow037_vertexIds_read :
    geometryRowsJson037.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped037.vertexIds := by decide +kernel

noncomputable def geometryRow037_physicalVolumeNumeratorChars : List Char := ['1', '1', '4', '9', '6', '8', '6', '2', '8', '1', '5', '4', '8', '3', '2', '2', '1', '1', '4', '6', '4', '0', '1', '8', '4', '7', '7', '9', '9', '3', '3', '8', '4', '7', '8', '2', '7']
noncomputable def geometryRow037_physicalVolumeDenominatorChars : List Char := ['3', '8', '9', '3', '6', '6', '9', '0', '1', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_physicalVolumeText : String := String.ofList (geometryRow037_physicalVolumeNumeratorChars ++ '/' :: geometryRow037_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_physicalVolume_before_field"
  err.flush

theorem geometryRow037_physicalVolume_field :
    geometryRowsJson037.getObjVal? "physical_volume" = .ok (.str geometryRow037_physicalVolumeText) := by rfl

theorem geometryRow037_physicalVolume_numerator_no_slash :
    geometryRow037_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeNumeratorChars = some (1149686281548322114640184779933847827 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeDenominatorChars = some (38936690150400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_nonzero : (38936690150400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_physicalVolume_parse :
    parseRational geometryRow037_physicalVolumeText = .ok geometryRowsTyped037.physicalVolume :=
  original_rational_fraction_of_chars geometryRow037_physicalVolumeNumeratorChars geometryRow037_physicalVolumeDenominatorChars
    (1149686281548322114640184779933847827 : Int) (38936690150400000000000000000000000000000000000000000000000000 : Int)
    geometryRow037_physicalVolume_numerator_no_slash geometryRow037_physicalVolume_numerator_parse
    geometryRow037_physicalVolume_denominator_parse geometryRow037_physicalVolume_denominator_nonzero

theorem geometryRow037_physicalVolume_read :
    rationalField geometryRowsJson037 "physical_volume" = .ok geometryRowsTyped037.physicalVolume :=
  original_rationalField_of_string geometryRowsJson037 "physical_volume" geometryRow037_physicalVolumeText
    geometryRowsTyped037.physicalVolume geometryRow037_physicalVolume_field geometryRow037_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_physicalVolume_complete"
  err.flush

noncomputable def geometryRow037_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow037_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_meanGapText : String := String.ofList (geometryRow037_meanGapNumeratorChars ++ '/' :: geometryRow037_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_meanGap_before_field"
  err.flush

theorem geometryRow037_meanGap_field :
    geometryRowsJson037.getObjVal? "mean_gap" = .ok (.str geometryRow037_meanGapText) := by rfl

theorem geometryRow037_meanGap_numerator_no_slash :
    geometryRow037_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_meanGap_numerator_parse :
    SourceJson.intChars geometryRow037_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_parse :
    SourceJson.intChars geometryRow037_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_meanGap_parse :
    parseRational geometryRow037_meanGapText = .ok geometryRowsTyped037.meanGap :=
  original_rational_fraction_of_chars geometryRow037_meanGapNumeratorChars geometryRow037_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow037_meanGap_numerator_no_slash geometryRow037_meanGap_numerator_parse
    geometryRow037_meanGap_denominator_parse geometryRow037_meanGap_denominator_nonzero

theorem geometryRow037_meanGap_read :
    rationalField geometryRowsJson037 "mean_gap" = .ok geometryRowsTyped037.meanGap :=
  original_rationalField_of_string geometryRowsJson037 "mean_gap" geometryRow037_meanGapText
    geometryRowsTyped037.meanGap geometryRow037_meanGap_field geometryRow037_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_meanGap_complete"
  err.flush

noncomputable def geometryRow037_jensenBoundNumeratorChars : List Char := ['2', '2', '3', '6', '0', '0', '9', '1', '1', '3', '3', '7', '9', '3', '3', '1', '3', '1', '8', '4', '6', '9', '5', '7', '6', '5', '6', '8', '6', '8', '8', '9', '6', '6', '3', '2', '8', '8', '5', '9', '2', '3', '4', '1', '1', '0', '2', '6', '5', '0', '6', '6', '8', '7', '0', '4', '4', '4', '3', '7', '0', '4', '6', '0', '8', '2', '3', '0', '6', '9', '5', '1', '9', '4', '5', '9', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_jensenBoundDenominatorChars : List Char := ['3', '4', '9', '3', '1', '1', '5', '4', '9', '1', '0', '4', '6', '9', '4', '4', '6', '5', '4', '1', '0', '8', '5', '7', '8', '9', '9', '9', '9', '0', '4', '3', '4', '9', '7', '6', '7', '9', '9', '0', '9', '8', '1', '5', '4', '8', '2', '8', '6', '6', '4', '9', '9', '7', '2', '4', '4', '6', '3', '9', '6', '7', '8', '9', '3', '3', '9', '9', '3', '1', '5', '4', '8', '8', '2', '9', '5', '4', '2', '8', '5', '9', '3', '6', '3', '0', '1', '5', '7', '8', '8', '3', '9', '7', '4', '6', '2', '8', '1', '9', '7', '5', '6', '4', '0', '1', '7', '0', '0', '5', '0', '1', '8', '1', '0', '5', '7']
noncomputable def geometryRow037_jensenBoundText : String := String.ofList (geometryRow037_jensenBoundNumeratorChars ++ '/' :: geometryRow037_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_jensenBound_before_field"
  err.flush

theorem geometryRow037_jensenBound_field :
    geometryRowsJson037.getObjVal? "jensen_bound" = .ok (.str geometryRow037_jensenBoundText) := by rfl

theorem geometryRow037_jensenBound_numerator_no_slash :
    geometryRow037_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow037_jensenBoundNumeratorChars = some (22360091133793313184695765686889663288592341102650668704443704608230695194591232000000000000000000000 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow037_jensenBoundDenominatorChars = some (349311549104694465410857899990434976799098154828664997244639678933993154882954285936301578839746281975640170050181057 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_nonzero : (349311549104694465410857899990434976799098154828664997244639678933993154882954285936301578839746281975640170050181057 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_jensenBound_parse :
    parseRational geometryRow037_jensenBoundText = .ok geometryRowsTyped037.jensenBound :=
  original_rational_fraction_of_chars geometryRow037_jensenBoundNumeratorChars geometryRow037_jensenBoundDenominatorChars
    (22360091133793313184695765686889663288592341102650668704443704608230695194591232000000000000000000000 : Int) (349311549104694465410857899990434976799098154828664997244639678933993154882954285936301578839746281975640170050181057 : Int)
    geometryRow037_jensenBound_numerator_no_slash geometryRow037_jensenBound_numerator_parse
    geometryRow037_jensenBound_denominator_parse geometryRow037_jensenBound_denominator_nonzero

theorem geometryRow037_jensenBound_read :
    rationalField geometryRowsJson037 "jensen_bound" = .ok geometryRowsTyped037.jensenBound :=
  original_rationalField_of_string geometryRowsJson037 "jensen_bound" geometryRow037_jensenBoundText
    geometryRowsTyped037.jensenBound geometryRow037_jensenBound_field geometryRow037_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_factorMaxima_before"
  err.flush

theorem geometryRow037_factorMaxima_read :
    rationalArrayField geometryRowsJson037 "factor_maxima" = .ok geometryRowsTyped037.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_gapWeightedMeans_before"
  err.flush

theorem geometryRow037_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson037 "gap_weighted_means" = .ok geometryRowsTyped037.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow037_floorChars : List Char := ['5', '0', '7', '1', '5', '4', '4', '1', '2', '3', '6', '4', '1']
noncomputable def geometryRow037_floorText : String := String.ofList geometryRow037_floorChars

theorem geometryRow037_floor_text_read :
    geometryRowsJson037.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow037_floorText := by rfl

theorem geometryRow037_floor_chars_parse :
    SourceJson.intChars geometryRow037_floorChars = some (5071544123641 : Int) := by decide +kernel

theorem geometryRow037_floor_parse :
    parseInteger geometryRow037_floorText = .ok geometryRowsTyped037.jensenFloorQ96 := by
  simp only [geometryRow037_floorText, parseInteger, String.toList_ofList, geometryRow037_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_037 :
    decodeGeometryRow geometryRowsJson037 = .ok geometryRowsTyped037 :=
  original_geometryRow_of_fields geometryRowsJson037 geometryRowsTyped037 geometryRow037_floorText
    geometryRow037_simplexId_read geometryRow037_vertexIds_read
    geometryRow037_physicalVolume_read geometryRow037_meanGap_read
    geometryRow037_factorMaxima_read geometryRow037_gapWeightedMeans_read
    geometryRow037_jensenBound_read geometryRow037_floor_text_read geometryRow037_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_037_original_decoder_complete"
  err.flush

#print axioms geometryRow037_simplexId_read
#print axioms geometryRow037_vertexIds_read
#print axioms geometryRow037_physicalVolume_field
#print axioms geometryRow037_physicalVolume_numerator_no_slash
#print axioms geometryRow037_physicalVolume_numerator_parse
#print axioms geometryRow037_physicalVolume_denominator_parse
#print axioms geometryRow037_physicalVolume_denominator_nonzero
#print axioms geometryRow037_physicalVolume_parse
#print axioms geometryRow037_physicalVolume_read
#print axioms geometryRow037_meanGap_field
#print axioms geometryRow037_meanGap_numerator_no_slash
#print axioms geometryRow037_meanGap_numerator_parse
#print axioms geometryRow037_meanGap_denominator_parse
#print axioms geometryRow037_meanGap_denominator_nonzero
#print axioms geometryRow037_meanGap_parse
#print axioms geometryRow037_meanGap_read
#print axioms geometryRow037_jensenBound_field
#print axioms geometryRow037_jensenBound_numerator_no_slash
#print axioms geometryRow037_jensenBound_numerator_parse
#print axioms geometryRow037_jensenBound_denominator_parse
#print axioms geometryRow037_jensenBound_denominator_nonzero
#print axioms geometryRow037_jensenBound_parse
#print axioms geometryRow037_jensenBound_read
#print axioms geometryRow037_factorMaxima_read
#print axioms geometryRow037_gapWeightedMeans_read
#print axioms geometryRow037_floor_text_read
#print axioms geometryRow037_floor_chars_parse
#print axioms geometryRow037_floor_parse
#print axioms decode_geometry_Rows_037

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
