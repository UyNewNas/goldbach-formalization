import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows054

/-! Original simplices typed block 55, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson108 : SourceJson :=
  (SimplicesBlock055.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped108 : GeometryRow :=
  { simplexId := 108,
    vertexIds := #[39, 37, 36, 24, 23, 10, 8, 3, 1],
    physicalVolume := ((11192324743721618015311710085741783 : ℚ) / (16288874496000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((106641281919 : ℚ) / (1175720000000 : ℚ)), ((107829748107 : ℚ) / (1175720000000 : ℚ)), ((23776139437 : ℚ) / (162792000000 : ℚ)), ((597972660287 : ℚ) / (5290740000000 : ℚ)), ((2066199293 : ℚ) / (38902500000 : ℚ)), ((492839028337 : ℚ) / (10581480000000 : ℚ)), ((2151808027 : ℚ) / (55692000000 : ℚ)), ((100798339561 : ℚ) / (2645370000000 : ℚ)), ((370918708039 : ℚ) / (10581480000000 : ℚ)), ((14836691887 : ℚ) / (423259200000 : ℚ))],
    jensenBound := ((17228577791730299114800535055948036397082835517679594637692818148631215323236000000000000 : ℚ) / (6859194969457214911925943538275691798133147269153068481675123108190182541999803267390750328318703187907 : ℚ)),
    jensenFloorQ96 := (199001277445954 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_simplexId_before"
  err.flush

theorem geometryRow108_simplexId_read :
    geometryRowsJson108.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped108.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_vertexIds_before"
  err.flush

theorem geometryRow108_vertexIds_read :
    geometryRowsJson108.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped108.vertexIds := by decide +kernel

noncomputable def geometryRow108_physicalVolumeNumeratorChars : List Char := ['1', '1', '1', '9', '2', '3', '2', '4', '7', '4', '3', '7', '2', '1', '6', '1', '8', '0', '1', '5', '3', '1', '1', '7', '1', '0', '0', '8', '5', '7', '4', '1', '7', '8', '3']
noncomputable def geometryRow108_physicalVolumeDenominatorChars : List Char := ['1', '6', '2', '8', '8', '8', '7', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow108_physicalVolumeText : String := String.ofList (geometryRow108_physicalVolumeNumeratorChars ++ '/' :: geometryRow108_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_physicalVolume_before_field"
  err.flush

theorem geometryRow108_physicalVolume_field :
    geometryRowsJson108.getObjVal? "physical_volume" = .ok (.str geometryRow108_physicalVolumeText) := by rfl

theorem geometryRow108_physicalVolume_numerator_no_slash :
    geometryRow108_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow108_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow108_physicalVolumeNumeratorChars = some (11192324743721618015311710085741783 : Int) := by decide +kernel

theorem geometryRow108_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow108_physicalVolumeDenominatorChars = some (16288874496000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow108_physicalVolume_denominator_nonzero : (16288874496000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow108_physicalVolume_parse :
    parseRational geometryRow108_physicalVolumeText = .ok geometryRowsTyped108.physicalVolume :=
  original_rational_fraction_of_chars geometryRow108_physicalVolumeNumeratorChars geometryRow108_physicalVolumeDenominatorChars
    (11192324743721618015311710085741783 : Int) (16288874496000000000000000000000000000000000000000000000000 : Int)
    geometryRow108_physicalVolume_numerator_no_slash geometryRow108_physicalVolume_numerator_parse
    geometryRow108_physicalVolume_denominator_parse geometryRow108_physicalVolume_denominator_nonzero

theorem geometryRow108_physicalVolume_read :
    rationalField geometryRowsJson108 "physical_volume" = .ok geometryRowsTyped108.physicalVolume :=
  original_rationalField_of_string geometryRowsJson108 "physical_volume" geometryRow108_physicalVolumeText
    geometryRowsTyped108.physicalVolume geometryRow108_physicalVolume_field geometryRow108_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_physicalVolume_complete"
  err.flush

noncomputable def geometryRow108_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow108_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow108_meanGapText : String := String.ofList (geometryRow108_meanGapNumeratorChars ++ '/' :: geometryRow108_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_meanGap_before_field"
  err.flush

theorem geometryRow108_meanGap_field :
    geometryRowsJson108.getObjVal? "mean_gap" = .ok (.str geometryRow108_meanGapText) := by rfl

theorem geometryRow108_meanGap_numerator_no_slash :
    geometryRow108_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow108_meanGap_numerator_parse :
    SourceJson.intChars geometryRow108_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow108_meanGap_denominator_parse :
    SourceJson.intChars geometryRow108_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow108_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow108_meanGap_parse :
    parseRational geometryRow108_meanGapText = .ok geometryRowsTyped108.meanGap :=
  original_rational_fraction_of_chars geometryRow108_meanGapNumeratorChars geometryRow108_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow108_meanGap_numerator_no_slash geometryRow108_meanGap_numerator_parse
    geometryRow108_meanGap_denominator_parse geometryRow108_meanGap_denominator_nonzero

theorem geometryRow108_meanGap_read :
    rationalField geometryRowsJson108 "mean_gap" = .ok geometryRowsTyped108.meanGap :=
  original_rationalField_of_string geometryRowsJson108 "mean_gap" geometryRow108_meanGapText
    geometryRowsTyped108.meanGap geometryRow108_meanGap_field geometryRow108_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_meanGap_complete"
  err.flush

noncomputable def geometryRow108_jensenBoundNumeratorChars : List Char := ['1', '7', '2', '2', '8', '5', '7', '7', '7', '9', '1', '7', '3', '0', '2', '9', '9', '1', '1', '4', '8', '0', '0', '5', '3', '5', '0', '5', '5', '9', '4', '8', '0', '3', '6', '3', '9', '7', '0', '8', '2', '8', '3', '5', '5', '1', '7', '6', '7', '9', '5', '9', '4', '6', '3', '7', '6', '9', '2', '8', '1', '8', '1', '4', '8', '6', '3', '1', '2', '1', '5', '3', '2', '3', '2', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow108_jensenBoundDenominatorChars : List Char := ['6', '8', '5', '9', '1', '9', '4', '9', '6', '9', '4', '5', '7', '2', '1', '4', '9', '1', '1', '9', '2', '5', '9', '4', '3', '5', '3', '8', '2', '7', '5', '6', '9', '1', '7', '9', '8', '1', '3', '3', '1', '4', '7', '2', '6', '9', '1', '5', '3', '0', '6', '8', '4', '8', '1', '6', '7', '5', '1', '2', '3', '1', '0', '8', '1', '9', '0', '1', '8', '2', '5', '4', '1', '9', '9', '9', '8', '0', '3', '2', '6', '7', '3', '9', '0', '7', '5', '0', '3', '2', '8', '3', '1', '8', '7', '0', '3', '1', '8', '7', '9', '0', '7']
noncomputable def geometryRow108_jensenBoundText : String := String.ofList (geometryRow108_jensenBoundNumeratorChars ++ '/' :: geometryRow108_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_jensenBound_before_field"
  err.flush

theorem geometryRow108_jensenBound_field :
    geometryRowsJson108.getObjVal? "jensen_bound" = .ok (.str geometryRow108_jensenBoundText) := by rfl

theorem geometryRow108_jensenBound_numerator_no_slash :
    geometryRow108_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow108_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow108_jensenBoundNumeratorChars = some (17228577791730299114800535055948036397082835517679594637692818148631215323236000000000000 : Int) := by decide +kernel

theorem geometryRow108_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow108_jensenBoundDenominatorChars = some (6859194969457214911925943538275691798133147269153068481675123108190182541999803267390750328318703187907 : Int) := by decide +kernel

theorem geometryRow108_jensenBound_denominator_nonzero : (6859194969457214911925943538275691798133147269153068481675123108190182541999803267390750328318703187907 : Int) ≠ 0 := by decide +kernel

theorem geometryRow108_jensenBound_parse :
    parseRational geometryRow108_jensenBoundText = .ok geometryRowsTyped108.jensenBound :=
  original_rational_fraction_of_chars geometryRow108_jensenBoundNumeratorChars geometryRow108_jensenBoundDenominatorChars
    (17228577791730299114800535055948036397082835517679594637692818148631215323236000000000000 : Int) (6859194969457214911925943538275691798133147269153068481675123108190182541999803267390750328318703187907 : Int)
    geometryRow108_jensenBound_numerator_no_slash geometryRow108_jensenBound_numerator_parse
    geometryRow108_jensenBound_denominator_parse geometryRow108_jensenBound_denominator_nonzero

theorem geometryRow108_jensenBound_read :
    rationalField geometryRowsJson108 "jensen_bound" = .ok geometryRowsTyped108.jensenBound :=
  original_rationalField_of_string geometryRowsJson108 "jensen_bound" geometryRow108_jensenBoundText
    geometryRowsTyped108.jensenBound geometryRow108_jensenBound_field geometryRow108_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_factorMaxima_before"
  err.flush

theorem geometryRow108_factorMaxima_read :
    rationalArrayField geometryRowsJson108 "factor_maxima" = .ok geometryRowsTyped108.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_gapWeightedMeans_before"
  err.flush

theorem geometryRow108_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson108 "gap_weighted_means" = .ok geometryRowsTyped108.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow108_floorChars : List Char := ['1', '9', '9', '0', '0', '1', '2', '7', '7', '4', '4', '5', '9', '5', '4']
noncomputable def geometryRow108_floorText : String := String.ofList geometryRow108_floorChars

theorem geometryRow108_floor_text_read :
    geometryRowsJson108.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow108_floorText := by rfl

theorem geometryRow108_floor_chars_parse :
    SourceJson.intChars geometryRow108_floorChars = some (199001277445954 : Int) := by decide +kernel

theorem geometryRow108_floor_parse :
    parseInteger geometryRow108_floorText = .ok geometryRowsTyped108.jensenFloorQ96 := by
  simp only [geometryRow108_floorText, parseInteger, String.toList_ofList, geometryRow108_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_108 :
    decodeGeometryRow geometryRowsJson108 = .ok geometryRowsTyped108 :=
  original_geometryRow_of_fields geometryRowsJson108 geometryRowsTyped108 geometryRow108_floorText
    geometryRow108_simplexId_read geometryRow108_vertexIds_read
    geometryRow108_physicalVolume_read geometryRow108_meanGap_read
    geometryRow108_factorMaxima_read geometryRow108_gapWeightedMeans_read
    geometryRow108_jensenBound_read geometryRow108_floor_text_read geometryRow108_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_108_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson109 : SourceJson :=
  (SimplicesBlock055.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped109 : GeometryRow :=
  { simplexId := 109,
    vertexIds := #[39, 37, 36, 24, 23, 21, 8, 3, 1],
    physicalVolume := ((11463155666616324387713548118012212067 : ℚ) / (74643767377920000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((48801452020899 : ℚ) / (552588400000000 : ℚ)), ((49360031129259 : ℚ) / (552588400000000 : ℚ)), ((56055038464003 : ℚ) / (382561200000000 : ℚ)), ((278478003761533 : ℚ) / (2486647800000000 : ℚ)), ((15411951983947 : ℚ) / (292546800000000 : ℚ)), ((228635784061697 : ℚ) / (4973295600000000 : ℚ)), ((2046353093389 : ℚ) / (52350480000000 : ℚ)), ((38349593087107 : ℚ) / (994659120000000 : ℚ)), ((181824526156733 : ℚ) / (4973295600000000 : ℚ)), ((181823863050653 : ℚ) / (4973295600000000 : ℚ))],
    jensenBound := ((6481259340606382258083041410931434993374577778635801957040046733036353744065131358236731062937600000000000000000000000 : ℚ) / (11865792870539702234823909650398255481371464209022386894777261281810976191567089499835319214649478889257342795658437908677240221028297 : ℚ)),
    jensenFloorQ96 := (43275512554206 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_simplexId_before"
  err.flush

theorem geometryRow109_simplexId_read :
    geometryRowsJson109.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped109.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_vertexIds_before"
  err.flush

theorem geometryRow109_vertexIds_read :
    geometryRowsJson109.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped109.vertexIds := by decide +kernel

noncomputable def geometryRow109_physicalVolumeNumeratorChars : List Char := ['1', '1', '4', '6', '3', '1', '5', '5', '6', '6', '6', '6', '1', '6', '3', '2', '4', '3', '8', '7', '7', '1', '3', '5', '4', '8', '1', '1', '8', '0', '1', '2', '2', '1', '2', '0', '6', '7']
noncomputable def geometryRow109_physicalVolumeDenominatorChars : List Char := ['7', '4', '6', '4', '3', '7', '6', '7', '3', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow109_physicalVolumeText : String := String.ofList (geometryRow109_physicalVolumeNumeratorChars ++ '/' :: geometryRow109_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_physicalVolume_before_field"
  err.flush

theorem geometryRow109_physicalVolume_field :
    geometryRowsJson109.getObjVal? "physical_volume" = .ok (.str geometryRow109_physicalVolumeText) := by rfl

theorem geometryRow109_physicalVolume_numerator_no_slash :
    geometryRow109_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow109_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow109_physicalVolumeNumeratorChars = some (11463155666616324387713548118012212067 : Int) := by decide +kernel

theorem geometryRow109_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow109_physicalVolumeDenominatorChars = some (74643767377920000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow109_physicalVolume_denominator_nonzero : (74643767377920000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow109_physicalVolume_parse :
    parseRational geometryRow109_physicalVolumeText = .ok geometryRowsTyped109.physicalVolume :=
  original_rational_fraction_of_chars geometryRow109_physicalVolumeNumeratorChars geometryRow109_physicalVolumeDenominatorChars
    (11463155666616324387713548118012212067 : Int) (74643767377920000000000000000000000000000000000000000000000000 : Int)
    geometryRow109_physicalVolume_numerator_no_slash geometryRow109_physicalVolume_numerator_parse
    geometryRow109_physicalVolume_denominator_parse geometryRow109_physicalVolume_denominator_nonzero

theorem geometryRow109_physicalVolume_read :
    rationalField geometryRowsJson109 "physical_volume" = .ok geometryRowsTyped109.physicalVolume :=
  original_rationalField_of_string geometryRowsJson109 "physical_volume" geometryRow109_physicalVolumeText
    geometryRowsTyped109.physicalVolume geometryRow109_physicalVolume_field geometryRow109_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_physicalVolume_complete"
  err.flush

noncomputable def geometryRow109_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow109_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow109_meanGapText : String := String.ofList (geometryRow109_meanGapNumeratorChars ++ '/' :: geometryRow109_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_meanGap_before_field"
  err.flush

theorem geometryRow109_meanGap_field :
    geometryRowsJson109.getObjVal? "mean_gap" = .ok (.str geometryRow109_meanGapText) := by rfl

theorem geometryRow109_meanGap_numerator_no_slash :
    geometryRow109_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow109_meanGap_numerator_parse :
    SourceJson.intChars geometryRow109_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow109_meanGap_denominator_parse :
    SourceJson.intChars geometryRow109_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow109_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow109_meanGap_parse :
    parseRational geometryRow109_meanGapText = .ok geometryRowsTyped109.meanGap :=
  original_rational_fraction_of_chars geometryRow109_meanGapNumeratorChars geometryRow109_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow109_meanGap_numerator_no_slash geometryRow109_meanGap_numerator_parse
    geometryRow109_meanGap_denominator_parse geometryRow109_meanGap_denominator_nonzero

theorem geometryRow109_meanGap_read :
    rationalField geometryRowsJson109 "mean_gap" = .ok geometryRowsTyped109.meanGap :=
  original_rationalField_of_string geometryRowsJson109 "mean_gap" geometryRow109_meanGapText
    geometryRowsTyped109.meanGap geometryRow109_meanGap_field geometryRow109_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_meanGap_complete"
  err.flush

noncomputable def geometryRow109_jensenBoundNumeratorChars : List Char := ['6', '4', '8', '1', '2', '5', '9', '3', '4', '0', '6', '0', '6', '3', '8', '2', '2', '5', '8', '0', '8', '3', '0', '4', '1', '4', '1', '0', '9', '3', '1', '4', '3', '4', '9', '9', '3', '3', '7', '4', '5', '7', '7', '7', '7', '8', '6', '3', '5', '8', '0', '1', '9', '5', '7', '0', '4', '0', '0', '4', '6', '7', '3', '3', '0', '3', '6', '3', '5', '3', '7', '4', '4', '0', '6', '5', '1', '3', '1', '3', '5', '8', '2', '3', '6', '7', '3', '1', '0', '6', '2', '9', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow109_jensenBoundDenominatorChars : List Char := ['1', '1', '8', '6', '5', '7', '9', '2', '8', '7', '0', '5', '3', '9', '7', '0', '2', '2', '3', '4', '8', '2', '3', '9', '0', '9', '6', '5', '0', '3', '9', '8', '2', '5', '5', '4', '8', '1', '3', '7', '1', '4', '6', '4', '2', '0', '9', '0', '2', '2', '3', '8', '6', '8', '9', '4', '7', '7', '7', '2', '6', '1', '2', '8', '1', '8', '1', '0', '9', '7', '6', '1', '9', '1', '5', '6', '7', '0', '8', '9', '4', '9', '9', '8', '3', '5', '3', '1', '9', '2', '1', '4', '6', '4', '9', '4', '7', '8', '8', '8', '9', '2', '5', '7', '3', '4', '2', '7', '9', '5', '6', '5', '8', '4', '3', '7', '9', '0', '8', '6', '7', '7', '2', '4', '0', '2', '2', '1', '0', '2', '8', '2', '9', '7']
noncomputable def geometryRow109_jensenBoundText : String := String.ofList (geometryRow109_jensenBoundNumeratorChars ++ '/' :: geometryRow109_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_jensenBound_before_field"
  err.flush

theorem geometryRow109_jensenBound_field :
    geometryRowsJson109.getObjVal? "jensen_bound" = .ok (.str geometryRow109_jensenBoundText) := by rfl

theorem geometryRow109_jensenBound_numerator_no_slash :
    geometryRow109_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow109_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow109_jensenBoundNumeratorChars = some (6481259340606382258083041410931434993374577778635801957040046733036353744065131358236731062937600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow109_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow109_jensenBoundDenominatorChars = some (11865792870539702234823909650398255481371464209022386894777261281810976191567089499835319214649478889257342795658437908677240221028297 : Int) := by decide +kernel

theorem geometryRow109_jensenBound_denominator_nonzero : (11865792870539702234823909650398255481371464209022386894777261281810976191567089499835319214649478889257342795658437908677240221028297 : Int) ≠ 0 := by decide +kernel

theorem geometryRow109_jensenBound_parse :
    parseRational geometryRow109_jensenBoundText = .ok geometryRowsTyped109.jensenBound :=
  original_rational_fraction_of_chars geometryRow109_jensenBoundNumeratorChars geometryRow109_jensenBoundDenominatorChars
    (6481259340606382258083041410931434993374577778635801957040046733036353744065131358236731062937600000000000000000000000 : Int) (11865792870539702234823909650398255481371464209022386894777261281810976191567089499835319214649478889257342795658437908677240221028297 : Int)
    geometryRow109_jensenBound_numerator_no_slash geometryRow109_jensenBound_numerator_parse
    geometryRow109_jensenBound_denominator_parse geometryRow109_jensenBound_denominator_nonzero

theorem geometryRow109_jensenBound_read :
    rationalField geometryRowsJson109 "jensen_bound" = .ok geometryRowsTyped109.jensenBound :=
  original_rationalField_of_string geometryRowsJson109 "jensen_bound" geometryRow109_jensenBoundText
    geometryRowsTyped109.jensenBound geometryRow109_jensenBound_field geometryRow109_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_factorMaxima_before"
  err.flush

theorem geometryRow109_factorMaxima_read :
    rationalArrayField geometryRowsJson109 "factor_maxima" = .ok geometryRowsTyped109.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_gapWeightedMeans_before"
  err.flush

theorem geometryRow109_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson109 "gap_weighted_means" = .ok geometryRowsTyped109.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow109_floorChars : List Char := ['4', '3', '2', '7', '5', '5', '1', '2', '5', '5', '4', '2', '0', '6']
noncomputable def geometryRow109_floorText : String := String.ofList geometryRow109_floorChars

theorem geometryRow109_floor_text_read :
    geometryRowsJson109.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow109_floorText := by rfl

theorem geometryRow109_floor_chars_parse :
    SourceJson.intChars geometryRow109_floorChars = some (43275512554206 : Int) := by decide +kernel

theorem geometryRow109_floor_parse :
    parseInteger geometryRow109_floorText = .ok geometryRowsTyped109.jensenFloorQ96 := by
  simp only [geometryRow109_floorText, parseInteger, String.toList_ofList, geometryRow109_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_109 :
    decodeGeometryRow geometryRowsJson109 = .ok geometryRowsTyped109 :=
  original_geometryRow_of_fields geometryRowsJson109 geometryRowsTyped109 geometryRow109_floorText
    geometryRow109_simplexId_read geometryRow109_vertexIds_read
    geometryRow109_physicalVolume_read geometryRow109_meanGap_read
    geometryRow109_factorMaxima_read geometryRow109_gapWeightedMeans_read
    geometryRow109_jensenBound_read geometryRow109_floor_text_read geometryRow109_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_109_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock055 : List SourceJson := [geometryRowsJson108, geometryRowsJson109]
noncomputable def geometryRowsTypedBlock055 : List (GeometryRow) := [geometryRowsTyped108, geometryRowsTyped109]
noncomputable def geometryRowsTypedThroughBlock055 : List (GeometryRow) := geometryRowsTypedThroughBlock054 ++ geometryRowsTypedBlock055

theorem geometry_Rows_block_055_push_eq (acc : List SourceJson) :
    SimplicesBlock055.blockPush acc = [geometryRowsJson109, geometryRowsJson108] ++ acc := by rfl

theorem geometry_Rows_block_055_reverse (acc : List SourceJson) :
    (SimplicesBlock055.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock055 := by
  rw [geometry_Rows_block_055_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_055 :
    geometryRowsJsonBlock055.mapM decodeGeometryRow = .ok geometryRowsTypedBlock055 := by
  simp only [geometryRowsJsonBlock055, geometryRowsTypedBlock055, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_108, decode_geometry_Rows_109]
  rfl

theorem decode_geometry_Rows_through_block_055 :
    SimplicesValue.arrayAcc056.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock055 := by
  change (SimplicesBlock055.blockPush SimplicesValue.arrayAcc055).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_055_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_054, decode_geometry_Rows_block_055]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_055_complete"
  err.flush

#print axioms geometryRow108_simplexId_read
#print axioms geometryRow108_vertexIds_read
#print axioms geometryRow108_physicalVolume_field
#print axioms geometryRow108_physicalVolume_numerator_no_slash
#print axioms geometryRow108_physicalVolume_numerator_parse
#print axioms geometryRow108_physicalVolume_denominator_parse
#print axioms geometryRow108_physicalVolume_denominator_nonzero
#print axioms geometryRow108_physicalVolume_parse
#print axioms geometryRow108_physicalVolume_read
#print axioms geometryRow108_meanGap_field
#print axioms geometryRow108_meanGap_numerator_no_slash
#print axioms geometryRow108_meanGap_numerator_parse
#print axioms geometryRow108_meanGap_denominator_parse
#print axioms geometryRow108_meanGap_denominator_nonzero
#print axioms geometryRow108_meanGap_parse
#print axioms geometryRow108_meanGap_read
#print axioms geometryRow108_jensenBound_field
#print axioms geometryRow108_jensenBound_numerator_no_slash
#print axioms geometryRow108_jensenBound_numerator_parse
#print axioms geometryRow108_jensenBound_denominator_parse
#print axioms geometryRow108_jensenBound_denominator_nonzero
#print axioms geometryRow108_jensenBound_parse
#print axioms geometryRow108_jensenBound_read
#print axioms geometryRow108_factorMaxima_read
#print axioms geometryRow108_gapWeightedMeans_read
#print axioms geometryRow108_floor_text_read
#print axioms geometryRow108_floor_chars_parse
#print axioms geometryRow108_floor_parse
#print axioms decode_geometry_Rows_108
#print axioms geometryRow109_simplexId_read
#print axioms geometryRow109_vertexIds_read
#print axioms geometryRow109_physicalVolume_field
#print axioms geometryRow109_physicalVolume_numerator_no_slash
#print axioms geometryRow109_physicalVolume_numerator_parse
#print axioms geometryRow109_physicalVolume_denominator_parse
#print axioms geometryRow109_physicalVolume_denominator_nonzero
#print axioms geometryRow109_physicalVolume_parse
#print axioms geometryRow109_physicalVolume_read
#print axioms geometryRow109_meanGap_field
#print axioms geometryRow109_meanGap_numerator_no_slash
#print axioms geometryRow109_meanGap_numerator_parse
#print axioms geometryRow109_meanGap_denominator_parse
#print axioms geometryRow109_meanGap_denominator_nonzero
#print axioms geometryRow109_meanGap_parse
#print axioms geometryRow109_meanGap_read
#print axioms geometryRow109_jensenBound_field
#print axioms geometryRow109_jensenBound_numerator_no_slash
#print axioms geometryRow109_jensenBound_numerator_parse
#print axioms geometryRow109_jensenBound_denominator_parse
#print axioms geometryRow109_jensenBound_denominator_nonzero
#print axioms geometryRow109_jensenBound_parse
#print axioms geometryRow109_jensenBound_read
#print axioms geometryRow109_factorMaxima_read
#print axioms geometryRow109_gapWeightedMeans_read
#print axioms geometryRow109_floor_text_read
#print axioms geometryRow109_floor_chars_parse
#print axioms geometryRow109_floor_parse
#print axioms decode_geometry_Rows_109
#print axioms geometry_Rows_block_055_push_eq
#print axioms geometry_Rows_block_055_reverse
#print axioms decode_geometry_Rows_block_055
#print axioms decode_geometry_Rows_through_block_055

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
