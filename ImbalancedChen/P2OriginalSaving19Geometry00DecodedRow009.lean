import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00200

/-! Original GeometryRow 9: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson009 : SourceJson :=
  (simplicesChunk009Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped009 : GeometryRow :=
  { simplexId := 9,
    vertexIds := #[27, 25, 23, 9, 7, 6, 5, 3, 1],
    physicalVolume := ((2694729186173204974744848452456221661 : ℚ) / (68443400655000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((546743 : ℚ) / (1368000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((3859259 : ℚ) / (48000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((145576805173 : ℚ) / (1589616000000 : ℚ)), ((733601864159 : ℚ) / (7948080000000 : ℚ)), ((9644391141533 : ℚ) / (79480800000000 : ℚ)), ((1422706320911 : ℚ) / (15896160000000 : ℚ)), ((6645397025983 : ℚ) / (79480800000000 : ℚ)), ((5738508826147 : ℚ) / (79480800000000 : ℚ)), ((285709742179 : ℚ) / (7948080000000 : ℚ)), ((465146494117 : ℚ) / (13246800000000 : ℚ)), ((452971579337 : ℚ) / (13246800000000 : ℚ)), ((1322687632229 : ℚ) / (39740400000000 : ℚ))],
    jensenBound := ((12130884469467397674018546301851947704094036765190429772646241165691784830066194225561600000000000000000 : ℚ) / (153429095114949037468310150523886208523443278751127579302924771275809726888376821943106447522802438854101386202048550131 : ℚ)),
    jensenFloorQ96 := (6264181415321 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_simplexId_before"
  err.flush

theorem geometryRow009_simplexId_read :
    geometryRowsJson009.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped009.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_vertexIds_before"
  err.flush

theorem geometryRow009_vertexIds_read :
    geometryRowsJson009.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped009.vertexIds := by decide +kernel

noncomputable def geometryRow009_physicalVolumeNumeratorChars : List Char := ['2', '6', '9', '4', '7', '2', '9', '1', '8', '6', '1', '7', '3', '2', '0', '4', '9', '7', '4', '7', '4', '4', '8', '4', '8', '4', '5', '2', '4', '5', '6', '2', '2', '1', '6', '6', '1']
noncomputable def geometryRow009_physicalVolumeDenominatorChars : List Char := ['6', '8', '4', '4', '3', '4', '0', '0', '6', '5', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_physicalVolumeText : String := String.ofList (geometryRow009_physicalVolumeNumeratorChars ++ '/' :: geometryRow009_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_physicalVolume_before_field"
  err.flush

theorem geometryRow009_physicalVolume_field :
    geometryRowsJson009.getObjVal? "physical_volume" = .ok (.str geometryRow009_physicalVolumeText) := by rfl

theorem geometryRow009_physicalVolume_numerator_no_slash :
    geometryRow009_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeNumeratorChars = some (2694729186173204974744848452456221661 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeDenominatorChars = some (68443400655000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_nonzero : (68443400655000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_physicalVolume_parse :
    parseRational geometryRow009_physicalVolumeText = .ok geometryRowsTyped009.physicalVolume :=
  original_rational_fraction_of_chars geometryRow009_physicalVolumeNumeratorChars geometryRow009_physicalVolumeDenominatorChars
    (2694729186173204974744848452456221661 : Int) (68443400655000000000000000000000000000000000000000000000000000 : Int)
    geometryRow009_physicalVolume_numerator_no_slash geometryRow009_physicalVolume_numerator_parse
    geometryRow009_physicalVolume_denominator_parse geometryRow009_physicalVolume_denominator_nonzero

theorem geometryRow009_physicalVolume_read :
    rationalField geometryRowsJson009 "physical_volume" = .ok geometryRowsTyped009.physicalVolume :=
  original_rationalField_of_string geometryRowsJson009 "physical_volume" geometryRow009_physicalVolumeText
    geometryRowsTyped009.physicalVolume geometryRow009_physicalVolume_field geometryRow009_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_physicalVolume_complete"
  err.flush

noncomputable def geometryRow009_meanGapNumeratorChars : List Char := ['5', '4', '6', '7', '4', '3']
noncomputable def geometryRow009_meanGapDenominatorChars : List Char := ['1', '3', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_meanGapText : String := String.ofList (geometryRow009_meanGapNumeratorChars ++ '/' :: geometryRow009_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_meanGap_before_field"
  err.flush

theorem geometryRow009_meanGap_field :
    geometryRowsJson009.getObjVal? "mean_gap" = .ok (.str geometryRow009_meanGapText) := by rfl

theorem geometryRow009_meanGap_numerator_no_slash :
    geometryRow009_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_meanGap_numerator_parse :
    SourceJson.intChars geometryRow009_meanGapNumeratorChars = some (546743 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_parse :
    SourceJson.intChars geometryRow009_meanGapDenominatorChars = some (1368000000 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_nonzero : (1368000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_meanGap_parse :
    parseRational geometryRow009_meanGapText = .ok geometryRowsTyped009.meanGap :=
  original_rational_fraction_of_chars geometryRow009_meanGapNumeratorChars geometryRow009_meanGapDenominatorChars
    (546743 : Int) (1368000000 : Int)
    geometryRow009_meanGap_numerator_no_slash geometryRow009_meanGap_numerator_parse
    geometryRow009_meanGap_denominator_parse geometryRow009_meanGap_denominator_nonzero

theorem geometryRow009_meanGap_read :
    rationalField geometryRowsJson009 "mean_gap" = .ok geometryRowsTyped009.meanGap :=
  original_rationalField_of_string geometryRowsJson009 "mean_gap" geometryRow009_meanGapText
    geometryRowsTyped009.meanGap geometryRow009_meanGap_field geometryRow009_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_meanGap_complete"
  err.flush

noncomputable def geometryRow009_jensenBoundNumeratorChars : List Char := ['1', '2', '1', '3', '0', '8', '8', '4', '4', '6', '9', '4', '6', '7', '3', '9', '7', '6', '7', '4', '0', '1', '8', '5', '4', '6', '3', '0', '1', '8', '5', '1', '9', '4', '7', '7', '0', '4', '0', '9', '4', '0', '3', '6', '7', '6', '5', '1', '9', '0', '4', '2', '9', '7', '7', '2', '6', '4', '6', '2', '4', '1', '1', '6', '5', '6', '9', '1', '7', '8', '4', '8', '3', '0', '0', '6', '6', '1', '9', '4', '2', '2', '5', '5', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_jensenBoundDenominatorChars : List Char := ['1', '5', '3', '4', '2', '9', '0', '9', '5', '1', '1', '4', '9', '4', '9', '0', '3', '7', '4', '6', '8', '3', '1', '0', '1', '5', '0', '5', '2', '3', '8', '8', '6', '2', '0', '8', '5', '2', '3', '4', '4', '3', '2', '7', '8', '7', '5', '1', '1', '2', '7', '5', '7', '9', '3', '0', '2', '9', '2', '4', '7', '7', '1', '2', '7', '5', '8', '0', '9', '7', '2', '6', '8', '8', '8', '3', '7', '6', '8', '2', '1', '9', '4', '3', '1', '0', '6', '4', '4', '7', '5', '2', '2', '8', '0', '2', '4', '3', '8', '8', '5', '4', '1', '0', '1', '3', '8', '6', '2', '0', '2', '0', '4', '8', '5', '5', '0', '1', '3', '1']
noncomputable def geometryRow009_jensenBoundText : String := String.ofList (geometryRow009_jensenBoundNumeratorChars ++ '/' :: geometryRow009_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_jensenBound_before_field"
  err.flush

theorem geometryRow009_jensenBound_field :
    geometryRowsJson009.getObjVal? "jensen_bound" = .ok (.str geometryRow009_jensenBoundText) := by rfl

theorem geometryRow009_jensenBound_numerator_no_slash :
    geometryRow009_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow009_jensenBoundNumeratorChars = some (12130884469467397674018546301851947704094036765190429772646241165691784830066194225561600000000000000000 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow009_jensenBoundDenominatorChars = some (153429095114949037468310150523886208523443278751127579302924771275809726888376821943106447522802438854101386202048550131 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_nonzero : (153429095114949037468310150523886208523443278751127579302924771275809726888376821943106447522802438854101386202048550131 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_jensenBound_parse :
    parseRational geometryRow009_jensenBoundText = .ok geometryRowsTyped009.jensenBound :=
  original_rational_fraction_of_chars geometryRow009_jensenBoundNumeratorChars geometryRow009_jensenBoundDenominatorChars
    (12130884469467397674018546301851947704094036765190429772646241165691784830066194225561600000000000000000 : Int) (153429095114949037468310150523886208523443278751127579302924771275809726888376821943106447522802438854101386202048550131 : Int)
    geometryRow009_jensenBound_numerator_no_slash geometryRow009_jensenBound_numerator_parse
    geometryRow009_jensenBound_denominator_parse geometryRow009_jensenBound_denominator_nonzero

theorem geometryRow009_jensenBound_read :
    rationalField geometryRowsJson009 "jensen_bound" = .ok geometryRowsTyped009.jensenBound :=
  original_rationalField_of_string geometryRowsJson009 "jensen_bound" geometryRow009_jensenBoundText
    geometryRowsTyped009.jensenBound geometryRow009_jensenBound_field geometryRow009_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_factorMaxima_before"
  err.flush

theorem geometryRow009_factorMaxima_read :
    rationalArrayField geometryRowsJson009 "factor_maxima" = .ok geometryRowsTyped009.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_gapWeightedMeans_before"
  err.flush

theorem geometryRow009_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson009 "gap_weighted_means" = .ok geometryRowsTyped009.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow009_floorChars : List Char := ['6', '2', '6', '4', '1', '8', '1', '4', '1', '5', '3', '2', '1']
noncomputable def geometryRow009_floorText : String := String.ofList geometryRow009_floorChars

theorem geometryRow009_floor_text_read :
    geometryRowsJson009.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow009_floorText := by rfl

theorem geometryRow009_floor_chars_parse :
    SourceJson.intChars geometryRow009_floorChars = some (6264181415321 : Int) := by decide +kernel

theorem geometryRow009_floor_parse :
    parseInteger geometryRow009_floorText = .ok geometryRowsTyped009.jensenFloorQ96 := by
  simp only [geometryRow009_floorText, parseInteger, String.toList_ofList, geometryRow009_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_009 :
    decodeGeometryRow geometryRowsJson009 = .ok geometryRowsTyped009 :=
  original_geometryRow_of_fields geometryRowsJson009 geometryRowsTyped009 geometryRow009_floorText
    geometryRow009_simplexId_read geometryRow009_vertexIds_read
    geometryRow009_physicalVolume_read geometryRow009_meanGap_read
    geometryRow009_factorMaxima_read geometryRow009_gapWeightedMeans_read
    geometryRow009_jensenBound_read geometryRow009_floor_text_read geometryRow009_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_009_original_decoder_complete"
  err.flush

#print axioms geometryRow009_simplexId_read
#print axioms geometryRow009_vertexIds_read
#print axioms geometryRow009_physicalVolume_field
#print axioms geometryRow009_physicalVolume_numerator_no_slash
#print axioms geometryRow009_physicalVolume_numerator_parse
#print axioms geometryRow009_physicalVolume_denominator_parse
#print axioms geometryRow009_physicalVolume_denominator_nonzero
#print axioms geometryRow009_physicalVolume_parse
#print axioms geometryRow009_physicalVolume_read
#print axioms geometryRow009_meanGap_field
#print axioms geometryRow009_meanGap_numerator_no_slash
#print axioms geometryRow009_meanGap_numerator_parse
#print axioms geometryRow009_meanGap_denominator_parse
#print axioms geometryRow009_meanGap_denominator_nonzero
#print axioms geometryRow009_meanGap_parse
#print axioms geometryRow009_meanGap_read
#print axioms geometryRow009_jensenBound_field
#print axioms geometryRow009_jensenBound_numerator_no_slash
#print axioms geometryRow009_jensenBound_numerator_parse
#print axioms geometryRow009_jensenBound_denominator_parse
#print axioms geometryRow009_jensenBound_denominator_nonzero
#print axioms geometryRow009_jensenBound_parse
#print axioms geometryRow009_jensenBound_read
#print axioms geometryRow009_factorMaxima_read
#print axioms geometryRow009_gapWeightedMeans_read
#print axioms geometryRow009_floor_text_read
#print axioms geometryRow009_floor_chars_parse
#print axioms geometryRow009_floor_parse
#print axioms decode_geometry_Rows_009

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
