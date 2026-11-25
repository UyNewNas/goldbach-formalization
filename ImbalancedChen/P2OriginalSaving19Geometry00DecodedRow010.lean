import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200

/-! Original GeometryRow 10: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson010 : SourceJson :=
  (simplicesChunk010Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped010 : GeometryRow :=
  { simplexId := 10,
    vertexIds := #[27, 25, 23, 9, 8, 6, 5, 3, 1],
    physicalVolume := ((1473432105974770601707203747632376600516163 : ℚ) / (3650314701600000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((7333165021163 : ℚ) / (79480800000000 : ℚ)), ((7390343404103 : ℚ) / (79480800000000 : ℚ)), ((9644391141533 : ℚ) / (79480800000000 : ℚ)), ((1791962767087 : ℚ) / (19870200000000 : ℚ)), ((6645397025983 : ℚ) / (79480800000000 : ℚ)), ((5738508826147 : ℚ) / (79480800000000 : ℚ)), ((285709742179 : ℚ) / (7948080000000 : ℚ)), ((465146494117 : ℚ) / (13246800000000 : ℚ)), ((887834904503 : ℚ) / (26493600000000 : ℚ)), ((518211160133 : ℚ) / (15896160000000 : ℚ))],
    jensenBound := ((194934210159748935414530877210375403788001659344622808652673912870385870715174781431316480000000000000000000 : ℚ) / (236072260226909626826668523710634101122231495166398513392044077697414769486041995844780326161561263980113603586804578533 : ℚ)),
    jensenFloorQ96 := (65421830024762350 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_simplexId_before"
  err.flush

theorem geometryRow010_simplexId_read :
    geometryRowsJson010.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped010.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_vertexIds_before"
  err.flush

theorem geometryRow010_vertexIds_read :
    geometryRowsJson010.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped010.vertexIds := by decide +kernel

noncomputable def geometryRow010_physicalVolumeNumeratorChars : List Char := ['1', '4', '7', '3', '4', '3', '2', '1', '0', '5', '9', '7', '4', '7', '7', '0', '6', '0', '1', '7', '0', '7', '2', '0', '3', '7', '4', '7', '6', '3', '2', '3', '7', '6', '6', '0', '0', '5', '1', '6', '1', '6', '3']
noncomputable def geometryRow010_physicalVolumeDenominatorChars : List Char := ['3', '6', '5', '0', '3', '1', '4', '7', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_physicalVolumeText : String := String.ofList (geometryRow010_physicalVolumeNumeratorChars ++ '/' :: geometryRow010_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_physicalVolume_before_field"
  err.flush

theorem geometryRow010_physicalVolume_field :
    geometryRowsJson010.getObjVal? "physical_volume" = .ok (.str geometryRow010_physicalVolumeText) := by rfl

theorem geometryRow010_physicalVolume_numerator_no_slash :
    geometryRow010_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeNumeratorChars = some (1473432105974770601707203747632376600516163 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeDenominatorChars = some (3650314701600000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_nonzero : (3650314701600000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_physicalVolume_parse :
    parseRational geometryRow010_physicalVolumeText = .ok geometryRowsTyped010.physicalVolume :=
  original_rational_fraction_of_chars geometryRow010_physicalVolumeNumeratorChars geometryRow010_physicalVolumeDenominatorChars
    (1473432105974770601707203747632376600516163 : Int) (3650314701600000000000000000000000000000000000000000000000000000 : Int)
    geometryRow010_physicalVolume_numerator_no_slash geometryRow010_physicalVolume_numerator_parse
    geometryRow010_physicalVolume_denominator_parse geometryRow010_physicalVolume_denominator_nonzero

theorem geometryRow010_physicalVolume_read :
    rationalField geometryRowsJson010 "physical_volume" = .ok geometryRowsTyped010.physicalVolume :=
  original_rationalField_of_string geometryRowsJson010 "physical_volume" geometryRow010_physicalVolumeText
    geometryRowsTyped010.physicalVolume geometryRow010_physicalVolume_field geometryRow010_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_physicalVolume_complete"
  err.flush

noncomputable def geometryRow010_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow010_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_meanGapText : String := String.ofList (geometryRow010_meanGapNumeratorChars ++ '/' :: geometryRow010_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_meanGap_before_field"
  err.flush

theorem geometryRow010_meanGap_field :
    geometryRowsJson010.getObjVal? "mean_gap" = .ok (.str geometryRow010_meanGapText) := by rfl

theorem geometryRow010_meanGap_numerator_no_slash :
    geometryRow010_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_meanGap_numerator_parse :
    SourceJson.intChars geometryRow010_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_parse :
    SourceJson.intChars geometryRow010_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_meanGap_parse :
    parseRational geometryRow010_meanGapText = .ok geometryRowsTyped010.meanGap :=
  original_rational_fraction_of_chars geometryRow010_meanGapNumeratorChars geometryRow010_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow010_meanGap_numerator_no_slash geometryRow010_meanGap_numerator_parse
    geometryRow010_meanGap_denominator_parse geometryRow010_meanGap_denominator_nonzero

theorem geometryRow010_meanGap_read :
    rationalField geometryRowsJson010 "mean_gap" = .ok geometryRowsTyped010.meanGap :=
  original_rationalField_of_string geometryRowsJson010 "mean_gap" geometryRow010_meanGapText
    geometryRowsTyped010.meanGap geometryRow010_meanGap_field geometryRow010_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_meanGap_complete"
  err.flush

noncomputable def geometryRow010_jensenBoundNumeratorChars : List Char := ['1', '9', '4', '9', '3', '4', '2', '1', '0', '1', '5', '9', '7', '4', '8', '9', '3', '5', '4', '1', '4', '5', '3', '0', '8', '7', '7', '2', '1', '0', '3', '7', '5', '4', '0', '3', '7', '8', '8', '0', '0', '1', '6', '5', '9', '3', '4', '4', '6', '2', '2', '8', '0', '8', '6', '5', '2', '6', '7', '3', '9', '1', '2', '8', '7', '0', '3', '8', '5', '8', '7', '0', '7', '1', '5', '1', '7', '4', '7', '8', '1', '4', '3', '1', '3', '1', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_jensenBoundDenominatorChars : List Char := ['2', '3', '6', '0', '7', '2', '2', '6', '0', '2', '2', '6', '9', '0', '9', '6', '2', '6', '8', '2', '6', '6', '6', '8', '5', '2', '3', '7', '1', '0', '6', '3', '4', '1', '0', '1', '1', '2', '2', '2', '3', '1', '4', '9', '5', '1', '6', '6', '3', '9', '8', '5', '1', '3', '3', '9', '2', '0', '4', '4', '0', '7', '7', '6', '9', '7', '4', '1', '4', '7', '6', '9', '4', '8', '6', '0', '4', '1', '9', '9', '5', '8', '4', '4', '7', '8', '0', '3', '2', '6', '1', '6', '1', '5', '6', '1', '2', '6', '3', '9', '8', '0', '1', '1', '3', '6', '0', '3', '5', '8', '6', '8', '0', '4', '5', '7', '8', '5', '3', '3']
noncomputable def geometryRow010_jensenBoundText : String := String.ofList (geometryRow010_jensenBoundNumeratorChars ++ '/' :: geometryRow010_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_jensenBound_before_field"
  err.flush

theorem geometryRow010_jensenBound_field :
    geometryRowsJson010.getObjVal? "jensen_bound" = .ok (.str geometryRow010_jensenBoundText) := by rfl

theorem geometryRow010_jensenBound_numerator_no_slash :
    geometryRow010_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow010_jensenBoundNumeratorChars = some (194934210159748935414530877210375403788001659344622808652673912870385870715174781431316480000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow010_jensenBoundDenominatorChars = some (236072260226909626826668523710634101122231495166398513392044077697414769486041995844780326161561263980113603586804578533 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_nonzero : (236072260226909626826668523710634101122231495166398513392044077697414769486041995844780326161561263980113603586804578533 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_jensenBound_parse :
    parseRational geometryRow010_jensenBoundText = .ok geometryRowsTyped010.jensenBound :=
  original_rational_fraction_of_chars geometryRow010_jensenBoundNumeratorChars geometryRow010_jensenBoundDenominatorChars
    (194934210159748935414530877210375403788001659344622808652673912870385870715174781431316480000000000000000000 : Int) (236072260226909626826668523710634101122231495166398513392044077697414769486041995844780326161561263980113603586804578533 : Int)
    geometryRow010_jensenBound_numerator_no_slash geometryRow010_jensenBound_numerator_parse
    geometryRow010_jensenBound_denominator_parse geometryRow010_jensenBound_denominator_nonzero

theorem geometryRow010_jensenBound_read :
    rationalField geometryRowsJson010 "jensen_bound" = .ok geometryRowsTyped010.jensenBound :=
  original_rationalField_of_string geometryRowsJson010 "jensen_bound" geometryRow010_jensenBoundText
    geometryRowsTyped010.jensenBound geometryRow010_jensenBound_field geometryRow010_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_factorMaxima_before"
  err.flush

theorem geometryRow010_factorMaxima_read :
    rationalArrayField geometryRowsJson010 "factor_maxima" = .ok geometryRowsTyped010.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_gapWeightedMeans_before"
  err.flush

theorem geometryRow010_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson010 "gap_weighted_means" = .ok geometryRowsTyped010.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow010_floorChars : List Char := ['6', '5', '4', '2', '1', '8', '3', '0', '0', '2', '4', '7', '6', '2', '3', '5', '0']
noncomputable def geometryRow010_floorText : String := String.ofList geometryRow010_floorChars

theorem geometryRow010_floor_text_read :
    geometryRowsJson010.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow010_floorText := by rfl

theorem geometryRow010_floor_chars_parse :
    SourceJson.intChars geometryRow010_floorChars = some (65421830024762350 : Int) := by decide +kernel

theorem geometryRow010_floor_parse :
    parseInteger geometryRow010_floorText = .ok geometryRowsTyped010.jensenFloorQ96 := by
  simp only [geometryRow010_floorText, parseInteger, String.toList_ofList, geometryRow010_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_010 :
    decodeGeometryRow geometryRowsJson010 = .ok geometryRowsTyped010 :=
  original_geometryRow_of_fields geometryRowsJson010 geometryRowsTyped010 geometryRow010_floorText
    geometryRow010_simplexId_read geometryRow010_vertexIds_read
    geometryRow010_physicalVolume_read geometryRow010_meanGap_read
    geometryRow010_factorMaxima_read geometryRow010_gapWeightedMeans_read
    geometryRow010_jensenBound_read geometryRow010_floor_text_read geometryRow010_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_010_original_decoder_complete"
  err.flush

#print axioms geometryRow010_simplexId_read
#print axioms geometryRow010_vertexIds_read
#print axioms geometryRow010_physicalVolume_field
#print axioms geometryRow010_physicalVolume_numerator_no_slash
#print axioms geometryRow010_physicalVolume_numerator_parse
#print axioms geometryRow010_physicalVolume_denominator_parse
#print axioms geometryRow010_physicalVolume_denominator_nonzero
#print axioms geometryRow010_physicalVolume_parse
#print axioms geometryRow010_physicalVolume_read
#print axioms geometryRow010_meanGap_field
#print axioms geometryRow010_meanGap_numerator_no_slash
#print axioms geometryRow010_meanGap_numerator_parse
#print axioms geometryRow010_meanGap_denominator_parse
#print axioms geometryRow010_meanGap_denominator_nonzero
#print axioms geometryRow010_meanGap_parse
#print axioms geometryRow010_meanGap_read
#print axioms geometryRow010_jensenBound_field
#print axioms geometryRow010_jensenBound_numerator_no_slash
#print axioms geometryRow010_jensenBound_numerator_parse
#print axioms geometryRow010_jensenBound_denominator_parse
#print axioms geometryRow010_jensenBound_denominator_nonzero
#print axioms geometryRow010_jensenBound_parse
#print axioms geometryRow010_jensenBound_read
#print axioms geometryRow010_factorMaxima_read
#print axioms geometryRow010_gapWeightedMeans_read
#print axioms geometryRow010_floor_text_read
#print axioms geometryRow010_floor_chars_parse
#print axioms geometryRow010_floor_parse
#print axioms decode_geometry_Rows_010

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
