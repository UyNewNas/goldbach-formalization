import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00600

/-! Original GeometryRow 27: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson027 : SourceJson :=
  (simplicesChunk027Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped027 : GeometryRow :=
  { simplexId := 27,
    vertexIds := #[27, 25, 23, 21, 20, 9, 4, 2, 0],
    physicalVolume := ((12197875235847933870715965041288897 : ℚ) / (47054671875000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1640269 : ℚ) / (3744000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((207659805827239 : ℚ) / (2327925600000000 : ℚ)), ((104747793345347 : ℚ) / (1163962800000000 : ℚ)), ((95838031081349 : ℚ) / (775975200000000 : ℚ)), ((1878138572287 : ℚ) / (19896800000000 : ℚ)), ((13495305296777 : ℚ) / (155195040000000 : ℚ)), ((54189719772121 : ℚ) / (775975200000000 : ℚ)), ((1124006657001 : ℚ) / (32332300000000 : ℚ)), ((9873624567857 : ℚ) / (290990700000000 : ℚ)), ((9715500221477 : ℚ) / (290990700000000 : ℚ)), ((11908016310763 : ℚ) / (387987600000000 : ℚ))],
    jensenBound := ((7293223730636648896505671105088964031317910143525270032184100512524655205111676947077471308317982720000000000000000000000 : ℚ) / (11028940530241401816081542182954345651871661435188552712236535288000841476132149437302728822176040453469717988931876328285550295266203 : ℚ)),
    jensenFloorQ96 := (52392041955377387 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_simplexId_before"
  err.flush

theorem geometryRow027_simplexId_read :
    geometryRowsJson027.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped027.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_vertexIds_before"
  err.flush

theorem geometryRow027_vertexIds_read :
    geometryRowsJson027.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped027.vertexIds := by decide +kernel

noncomputable def geometryRow027_physicalVolumeNumeratorChars : List Char := ['1', '2', '1', '9', '7', '8', '7', '5', '2', '3', '5', '8', '4', '7', '9', '3', '3', '8', '7', '0', '7', '1', '5', '9', '6', '5', '0', '4', '1', '2', '8', '8', '8', '9', '7']
noncomputable def geometryRow027_physicalVolumeDenominatorChars : List Char := ['4', '7', '0', '5', '4', '6', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_physicalVolumeText : String := String.ofList (geometryRow027_physicalVolumeNumeratorChars ++ '/' :: geometryRow027_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_physicalVolume_before_field"
  err.flush

theorem geometryRow027_physicalVolume_field :
    geometryRowsJson027.getObjVal? "physical_volume" = .ok (.str geometryRow027_physicalVolumeText) := by rfl

theorem geometryRow027_physicalVolume_numerator_no_slash :
    geometryRow027_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeNumeratorChars = some (12197875235847933870715965041288897 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeDenominatorChars = some (47054671875000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_nonzero : (47054671875000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_physicalVolume_parse :
    parseRational geometryRow027_physicalVolumeText = .ok geometryRowsTyped027.physicalVolume :=
  original_rational_fraction_of_chars geometryRow027_physicalVolumeNumeratorChars geometryRow027_physicalVolumeDenominatorChars
    (12197875235847933870715965041288897 : Int) (47054671875000000000000000000000000000000000000000000000 : Int)
    geometryRow027_physicalVolume_numerator_no_slash geometryRow027_physicalVolume_numerator_parse
    geometryRow027_physicalVolume_denominator_parse geometryRow027_physicalVolume_denominator_nonzero

theorem geometryRow027_physicalVolume_read :
    rationalField geometryRowsJson027 "physical_volume" = .ok geometryRowsTyped027.physicalVolume :=
  original_rationalField_of_string geometryRowsJson027 "physical_volume" geometryRow027_physicalVolumeText
    geometryRowsTyped027.physicalVolume geometryRow027_physicalVolume_field geometryRow027_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_physicalVolume_complete"
  err.flush

noncomputable def geometryRow027_meanGapNumeratorChars : List Char := ['1', '6', '4', '0', '2', '6', '9']
noncomputable def geometryRow027_meanGapDenominatorChars : List Char := ['3', '7', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_meanGapText : String := String.ofList (geometryRow027_meanGapNumeratorChars ++ '/' :: geometryRow027_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_meanGap_before_field"
  err.flush

theorem geometryRow027_meanGap_field :
    geometryRowsJson027.getObjVal? "mean_gap" = .ok (.str geometryRow027_meanGapText) := by rfl

theorem geometryRow027_meanGap_numerator_no_slash :
    geometryRow027_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_meanGap_numerator_parse :
    SourceJson.intChars geometryRow027_meanGapNumeratorChars = some (1640269 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_parse :
    SourceJson.intChars geometryRow027_meanGapDenominatorChars = some (3744000000 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_nonzero : (3744000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_meanGap_parse :
    parseRational geometryRow027_meanGapText = .ok geometryRowsTyped027.meanGap :=
  original_rational_fraction_of_chars geometryRow027_meanGapNumeratorChars geometryRow027_meanGapDenominatorChars
    (1640269 : Int) (3744000000 : Int)
    geometryRow027_meanGap_numerator_no_slash geometryRow027_meanGap_numerator_parse
    geometryRow027_meanGap_denominator_parse geometryRow027_meanGap_denominator_nonzero

theorem geometryRow027_meanGap_read :
    rationalField geometryRowsJson027 "mean_gap" = .ok geometryRowsTyped027.meanGap :=
  original_rationalField_of_string geometryRowsJson027 "mean_gap" geometryRow027_meanGapText
    geometryRowsTyped027.meanGap geometryRow027_meanGap_field geometryRow027_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_meanGap_complete"
  err.flush

noncomputable def geometryRow027_jensenBoundNumeratorChars : List Char := ['7', '2', '9', '3', '2', '2', '3', '7', '3', '0', '6', '3', '6', '6', '4', '8', '8', '9', '6', '5', '0', '5', '6', '7', '1', '1', '0', '5', '0', '8', '8', '9', '6', '4', '0', '3', '1', '3', '1', '7', '9', '1', '0', '1', '4', '3', '5', '2', '5', '2', '7', '0', '0', '3', '2', '1', '8', '4', '1', '0', '0', '5', '1', '2', '5', '2', '4', '6', '5', '5', '2', '0', '5', '1', '1', '1', '6', '7', '6', '9', '4', '7', '0', '7', '7', '4', '7', '1', '3', '0', '8', '3', '1', '7', '9', '8', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_jensenBoundDenominatorChars : List Char := ['1', '1', '0', '2', '8', '9', '4', '0', '5', '3', '0', '2', '4', '1', '4', '0', '1', '8', '1', '6', '0', '8', '1', '5', '4', '2', '1', '8', '2', '9', '5', '4', '3', '4', '5', '6', '5', '1', '8', '7', '1', '6', '6', '1', '4', '3', '5', '1', '8', '8', '5', '5', '2', '7', '1', '2', '2', '3', '6', '5', '3', '5', '2', '8', '8', '0', '0', '0', '8', '4', '1', '4', '7', '6', '1', '3', '2', '1', '4', '9', '4', '3', '7', '3', '0', '2', '7', '2', '8', '8', '2', '2', '1', '7', '6', '0', '4', '0', '4', '5', '3', '4', '6', '9', '7', '1', '7', '9', '8', '8', '9', '3', '1', '8', '7', '6', '3', '2', '8', '2', '8', '5', '5', '5', '0', '2', '9', '5', '2', '6', '6', '2', '0', '3']
noncomputable def geometryRow027_jensenBoundText : String := String.ofList (geometryRow027_jensenBoundNumeratorChars ++ '/' :: geometryRow027_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_jensenBound_before_field"
  err.flush

theorem geometryRow027_jensenBound_field :
    geometryRowsJson027.getObjVal? "jensen_bound" = .ok (.str geometryRow027_jensenBoundText) := by rfl

theorem geometryRow027_jensenBound_numerator_no_slash :
    geometryRow027_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow027_jensenBoundNumeratorChars = some (7293223730636648896505671105088964031317910143525270032184100512524655205111676947077471308317982720000000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow027_jensenBoundDenominatorChars = some (11028940530241401816081542182954345651871661435188552712236535288000841476132149437302728822176040453469717988931876328285550295266203 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_nonzero : (11028940530241401816081542182954345651871661435188552712236535288000841476132149437302728822176040453469717988931876328285550295266203 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_jensenBound_parse :
    parseRational geometryRow027_jensenBoundText = .ok geometryRowsTyped027.jensenBound :=
  original_rational_fraction_of_chars geometryRow027_jensenBoundNumeratorChars geometryRow027_jensenBoundDenominatorChars
    (7293223730636648896505671105088964031317910143525270032184100512524655205111676947077471308317982720000000000000000000000 : Int) (11028940530241401816081542182954345651871661435188552712236535288000841476132149437302728822176040453469717988931876328285550295266203 : Int)
    geometryRow027_jensenBound_numerator_no_slash geometryRow027_jensenBound_numerator_parse
    geometryRow027_jensenBound_denominator_parse geometryRow027_jensenBound_denominator_nonzero

theorem geometryRow027_jensenBound_read :
    rationalField geometryRowsJson027 "jensen_bound" = .ok geometryRowsTyped027.jensenBound :=
  original_rationalField_of_string geometryRowsJson027 "jensen_bound" geometryRow027_jensenBoundText
    geometryRowsTyped027.jensenBound geometryRow027_jensenBound_field geometryRow027_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_factorMaxima_before"
  err.flush

theorem geometryRow027_factorMaxima_read :
    rationalArrayField geometryRowsJson027 "factor_maxima" = .ok geometryRowsTyped027.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_gapWeightedMeans_before"
  err.flush

theorem geometryRow027_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson027 "gap_weighted_means" = .ok geometryRowsTyped027.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow027_floorChars : List Char := ['5', '2', '3', '9', '2', '0', '4', '1', '9', '5', '5', '3', '7', '7', '3', '8', '7']
noncomputable def geometryRow027_floorText : String := String.ofList geometryRow027_floorChars

theorem geometryRow027_floor_text_read :
    geometryRowsJson027.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow027_floorText := by rfl

theorem geometryRow027_floor_chars_parse :
    SourceJson.intChars geometryRow027_floorChars = some (52392041955377387 : Int) := by decide +kernel

theorem geometryRow027_floor_parse :
    parseInteger geometryRow027_floorText = .ok geometryRowsTyped027.jensenFloorQ96 := by
  simp only [geometryRow027_floorText, parseInteger, String.toList_ofList, geometryRow027_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_027 :
    decodeGeometryRow geometryRowsJson027 = .ok geometryRowsTyped027 :=
  original_geometryRow_of_fields geometryRowsJson027 geometryRowsTyped027 geometryRow027_floorText
    geometryRow027_simplexId_read geometryRow027_vertexIds_read
    geometryRow027_physicalVolume_read geometryRow027_meanGap_read
    geometryRow027_factorMaxima_read geometryRow027_gapWeightedMeans_read
    geometryRow027_jensenBound_read geometryRow027_floor_text_read geometryRow027_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_027_original_decoder_complete"
  err.flush

#print axioms geometryRow027_simplexId_read
#print axioms geometryRow027_vertexIds_read
#print axioms geometryRow027_physicalVolume_field
#print axioms geometryRow027_physicalVolume_numerator_no_slash
#print axioms geometryRow027_physicalVolume_numerator_parse
#print axioms geometryRow027_physicalVolume_denominator_parse
#print axioms geometryRow027_physicalVolume_denominator_nonzero
#print axioms geometryRow027_physicalVolume_parse
#print axioms geometryRow027_physicalVolume_read
#print axioms geometryRow027_meanGap_field
#print axioms geometryRow027_meanGap_numerator_no_slash
#print axioms geometryRow027_meanGap_numerator_parse
#print axioms geometryRow027_meanGap_denominator_parse
#print axioms geometryRow027_meanGap_denominator_nonzero
#print axioms geometryRow027_meanGap_parse
#print axioms geometryRow027_meanGap_read
#print axioms geometryRow027_jensenBound_field
#print axioms geometryRow027_jensenBound_numerator_no_slash
#print axioms geometryRow027_jensenBound_numerator_parse
#print axioms geometryRow027_jensenBound_denominator_parse
#print axioms geometryRow027_jensenBound_denominator_nonzero
#print axioms geometryRow027_jensenBound_parse
#print axioms geometryRow027_jensenBound_read
#print axioms geometryRow027_factorMaxima_read
#print axioms geometryRow027_gapWeightedMeans_read
#print axioms geometryRow027_floor_text_read
#print axioms geometryRow027_floor_chars_parse
#print axioms geometryRow027_floor_parse
#print axioms decode_geometry_Rows_027

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
