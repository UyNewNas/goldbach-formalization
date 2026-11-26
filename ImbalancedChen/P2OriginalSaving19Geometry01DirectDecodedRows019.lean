import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows018

/-! Original simplices typed block 19, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson038 : SourceJson :=
  (SimplicesBlock019.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped038 : GeometryRow :=
  { simplexId := 38,
    vertexIds := #[39, 35, 24, 23, 10, 7, 6, 2, 0],
    physicalVolume := ((6976445881081079602441779538190889692342294087 : ℚ) / (372691364806656000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((273526391 : ℚ) / (3325000000 : ℚ)), ((3878345109 : ℚ) / (46550000000 : ℚ)), ((3201388597 : ℚ) / (22344000000 : ℚ)), ((23234199883 : ℚ) / (209475000000 : ℚ)), ((16714847351 : ℚ) / (279300000000 : ℚ)), ((27478919801 : ℚ) / (558600000000 : ℚ)), ((1164583471 : ℚ) / (29400000000 : ℚ)), ((21828811679 : ℚ) / (558600000000 : ℚ)), ((10496954627 : ℚ) / (279300000000 : ℚ)), ((57760143031 : ℚ) / (1675800000000 : ℚ))],
    jensenBound := ((3456669025050394389275393845313024160921548596833689860392471486185333618164062500000000 : ℚ) / (50782430625072601280372184816287349305376458649267472030497440674619862187225638497912979880827957 : ℚ)),
    jensenFloorQ96 := (5392919005722065680 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_simplexId_before"
  err.flush

theorem geometryRow038_simplexId_read :
    geometryRowsJson038.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped038.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_vertexIds_before"
  err.flush

theorem geometryRow038_vertexIds_read :
    geometryRowsJson038.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped038.vertexIds := by decide +kernel

noncomputable def geometryRow038_physicalVolumeNumeratorChars : List Char := ['6', '9', '7', '6', '4', '4', '5', '8', '8', '1', '0', '8', '1', '0', '7', '9', '6', '0', '2', '4', '4', '1', '7', '7', '9', '5', '3', '8', '1', '9', '0', '8', '8', '9', '6', '9', '2', '3', '4', '2', '2', '9', '4', '0', '8', '7']
noncomputable def geometryRow038_physicalVolumeDenominatorChars : List Char := ['3', '7', '2', '6', '9', '1', '3', '6', '4', '8', '0', '6', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_physicalVolumeText : String := String.ofList (geometryRow038_physicalVolumeNumeratorChars ++ '/' :: geometryRow038_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_physicalVolume_before_field"
  err.flush

theorem geometryRow038_physicalVolume_field :
    geometryRowsJson038.getObjVal? "physical_volume" = .ok (.str geometryRow038_physicalVolumeText) := by rfl

theorem geometryRow038_physicalVolume_numerator_no_slash :
    geometryRow038_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeNumeratorChars = some (6976445881081079602441779538190889692342294087 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeDenominatorChars = some (372691364806656000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_nonzero : (372691364806656000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_physicalVolume_parse :
    parseRational geometryRow038_physicalVolumeText = .ok geometryRowsTyped038.physicalVolume :=
  original_rational_fraction_of_chars geometryRow038_physicalVolumeNumeratorChars geometryRow038_physicalVolumeDenominatorChars
    (6976445881081079602441779538190889692342294087 : Int) (372691364806656000000000000000000000000000000000000000000000000000 : Int)
    geometryRow038_physicalVolume_numerator_no_slash geometryRow038_physicalVolume_numerator_parse
    geometryRow038_physicalVolume_denominator_parse geometryRow038_physicalVolume_denominator_nonzero

theorem geometryRow038_physicalVolume_read :
    rationalField geometryRowsJson038 "physical_volume" = .ok geometryRowsTyped038.physicalVolume :=
  original_rationalField_of_string geometryRowsJson038 "physical_volume" geometryRow038_physicalVolumeText
    geometryRowsTyped038.physicalVolume geometryRow038_physicalVolume_field geometryRow038_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_physicalVolume_complete"
  err.flush

noncomputable def geometryRow038_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow038_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_meanGapText : String := String.ofList (geometryRow038_meanGapNumeratorChars ++ '/' :: geometryRow038_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_meanGap_before_field"
  err.flush

theorem geometryRow038_meanGap_field :
    geometryRowsJson038.getObjVal? "mean_gap" = .ok (.str geometryRow038_meanGapText) := by rfl

theorem geometryRow038_meanGap_numerator_no_slash :
    geometryRow038_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_meanGap_numerator_parse :
    SourceJson.intChars geometryRow038_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_parse :
    SourceJson.intChars geometryRow038_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_meanGap_parse :
    parseRational geometryRow038_meanGapText = .ok geometryRowsTyped038.meanGap :=
  original_rational_fraction_of_chars geometryRow038_meanGapNumeratorChars geometryRow038_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow038_meanGap_numerator_no_slash geometryRow038_meanGap_numerator_parse
    geometryRow038_meanGap_denominator_parse geometryRow038_meanGap_denominator_nonzero

theorem geometryRow038_meanGap_read :
    rationalField geometryRowsJson038 "mean_gap" = .ok geometryRowsTyped038.meanGap :=
  original_rationalField_of_string geometryRowsJson038 "mean_gap" geometryRow038_meanGapText
    geometryRowsTyped038.meanGap geometryRow038_meanGap_field geometryRow038_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_meanGap_complete"
  err.flush

noncomputable def geometryRow038_jensenBoundNumeratorChars : List Char := ['3', '4', '5', '6', '6', '6', '9', '0', '2', '5', '0', '5', '0', '3', '9', '4', '3', '8', '9', '2', '7', '5', '3', '9', '3', '8', '4', '5', '3', '1', '3', '0', '2', '4', '1', '6', '0', '9', '2', '1', '5', '4', '8', '5', '9', '6', '8', '3', '3', '6', '8', '9', '8', '6', '0', '3', '9', '2', '4', '7', '1', '4', '8', '6', '1', '8', '5', '3', '3', '3', '6', '1', '8', '1', '6', '4', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_jensenBoundDenominatorChars : List Char := ['5', '0', '7', '8', '2', '4', '3', '0', '6', '2', '5', '0', '7', '2', '6', '0', '1', '2', '8', '0', '3', '7', '2', '1', '8', '4', '8', '1', '6', '2', '8', '7', '3', '4', '9', '3', '0', '5', '3', '7', '6', '4', '5', '8', '6', '4', '9', '2', '6', '7', '4', '7', '2', '0', '3', '0', '4', '9', '7', '4', '4', '0', '6', '7', '4', '6', '1', '9', '8', '6', '2', '1', '8', '7', '2', '2', '5', '6', '3', '8', '4', '9', '7', '9', '1', '2', '9', '7', '9', '8', '8', '0', '8', '2', '7', '9', '5', '7']
noncomputable def geometryRow038_jensenBoundText : String := String.ofList (geometryRow038_jensenBoundNumeratorChars ++ '/' :: geometryRow038_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_jensenBound_before_field"
  err.flush

theorem geometryRow038_jensenBound_field :
    geometryRowsJson038.getObjVal? "jensen_bound" = .ok (.str geometryRow038_jensenBoundText) := by rfl

theorem geometryRow038_jensenBound_numerator_no_slash :
    geometryRow038_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow038_jensenBoundNumeratorChars = some (3456669025050394389275393845313024160921548596833689860392471486185333618164062500000000 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow038_jensenBoundDenominatorChars = some (50782430625072601280372184816287349305376458649267472030497440674619862187225638497912979880827957 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_nonzero : (50782430625072601280372184816287349305376458649267472030497440674619862187225638497912979880827957 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_jensenBound_parse :
    parseRational geometryRow038_jensenBoundText = .ok geometryRowsTyped038.jensenBound :=
  original_rational_fraction_of_chars geometryRow038_jensenBoundNumeratorChars geometryRow038_jensenBoundDenominatorChars
    (3456669025050394389275393845313024160921548596833689860392471486185333618164062500000000 : Int) (50782430625072601280372184816287349305376458649267472030497440674619862187225638497912979880827957 : Int)
    geometryRow038_jensenBound_numerator_no_slash geometryRow038_jensenBound_numerator_parse
    geometryRow038_jensenBound_denominator_parse geometryRow038_jensenBound_denominator_nonzero

theorem geometryRow038_jensenBound_read :
    rationalField geometryRowsJson038 "jensen_bound" = .ok geometryRowsTyped038.jensenBound :=
  original_rationalField_of_string geometryRowsJson038 "jensen_bound" geometryRow038_jensenBoundText
    geometryRowsTyped038.jensenBound geometryRow038_jensenBound_field geometryRow038_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_factorMaxima_before"
  err.flush

theorem geometryRow038_factorMaxima_read :
    rationalArrayField geometryRowsJson038 "factor_maxima" = .ok geometryRowsTyped038.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_gapWeightedMeans_before"
  err.flush

theorem geometryRow038_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson038 "gap_weighted_means" = .ok geometryRowsTyped038.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow038_floorChars : List Char := ['5', '3', '9', '2', '9', '1', '9', '0', '0', '5', '7', '2', '2', '0', '6', '5', '6', '8', '0']
noncomputable def geometryRow038_floorText : String := String.ofList geometryRow038_floorChars

theorem geometryRow038_floor_text_read :
    geometryRowsJson038.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow038_floorText := by rfl

theorem geometryRow038_floor_chars_parse :
    SourceJson.intChars geometryRow038_floorChars = some (5392919005722065680 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY01_TYPED Row_038_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson039 : SourceJson :=
  (SimplicesBlock019.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped039 : GeometryRow :=
  { simplexId := 39,
    vertexIds := #[39, 35, 24, 23, 21, 8, 3, 1, 0],
    physicalVolume := ((208911525039292802667235548166014943457 : ℚ) / (1244062789632000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((917758068679 : ℚ) / (11051768000000 : ℚ)), ((4644648254231 : ℚ) / (55258840000000 : ℚ)), ((684813166783 : ℚ) / (4782015000000 : ℚ)), ((22424178006187 : ℚ) / (207220650000000 : ℚ)), ((8762847342463 : ℚ) / (146273400000000 : ℚ)), ((30643198829927 : ℚ) / (621661950000000 : ℚ)), ((5175512438653 : ℚ) / (130876200000000 : ℚ)), ((97006947116197 : ℚ) / (2486647800000000 : ℚ)), ((23011348313329 : ℚ) / (621661950000000 : ℚ)), ((23011223980939 : ℚ) / (621661950000000 : ℚ))],
    jensenBound := ((2610785360548484382197248648628824187696292680569231680202471637446780799505989435284995949189784882812500000000000 : ℚ) / (4672905519223673743331847351598114380803354068497958930752516473185425371401135982563094032383480092865439024727202284866396800559 : ℚ)),
    jensenFloorQ96 := (44265334701173 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_simplexId_before"
  err.flush

theorem geometryRow039_simplexId_read :
    geometryRowsJson039.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped039.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_vertexIds_before"
  err.flush

theorem geometryRow039_vertexIds_read :
    geometryRowsJson039.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped039.vertexIds := by decide +kernel

noncomputable def geometryRow039_physicalVolumeNumeratorChars : List Char := ['2', '0', '8', '9', '1', '1', '5', '2', '5', '0', '3', '9', '2', '9', '2', '8', '0', '2', '6', '6', '7', '2', '3', '5', '5', '4', '8', '1', '6', '6', '0', '1', '4', '9', '4', '3', '4', '5', '7']
noncomputable def geometryRow039_physicalVolumeDenominatorChars : List Char := ['1', '2', '4', '4', '0', '6', '2', '7', '8', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_physicalVolumeText : String := String.ofList (geometryRow039_physicalVolumeNumeratorChars ++ '/' :: geometryRow039_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_physicalVolume_before_field"
  err.flush

theorem geometryRow039_physicalVolume_field :
    geometryRowsJson039.getObjVal? "physical_volume" = .ok (.str geometryRow039_physicalVolumeText) := by rfl

theorem geometryRow039_physicalVolume_numerator_no_slash :
    geometryRow039_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeNumeratorChars = some (208911525039292802667235548166014943457 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeDenominatorChars = some (1244062789632000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_nonzero : (1244062789632000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_physicalVolume_parse :
    parseRational geometryRow039_physicalVolumeText = .ok geometryRowsTyped039.physicalVolume :=
  original_rational_fraction_of_chars geometryRow039_physicalVolumeNumeratorChars geometryRow039_physicalVolumeDenominatorChars
    (208911525039292802667235548166014943457 : Int) (1244062789632000000000000000000000000000000000000000000000000000 : Int)
    geometryRow039_physicalVolume_numerator_no_slash geometryRow039_physicalVolume_numerator_parse
    geometryRow039_physicalVolume_denominator_parse geometryRow039_physicalVolume_denominator_nonzero

theorem geometryRow039_physicalVolume_read :
    rationalField geometryRowsJson039 "physical_volume" = .ok geometryRowsTyped039.physicalVolume :=
  original_rationalField_of_string geometryRowsJson039 "physical_volume" geometryRow039_physicalVolumeText
    geometryRowsTyped039.physicalVolume geometryRow039_physicalVolume_field geometryRow039_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_physicalVolume_complete"
  err.flush

noncomputable def geometryRow039_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow039_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_meanGapText : String := String.ofList (geometryRow039_meanGapNumeratorChars ++ '/' :: geometryRow039_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_meanGap_before_field"
  err.flush

theorem geometryRow039_meanGap_field :
    geometryRowsJson039.getObjVal? "mean_gap" = .ok (.str geometryRow039_meanGapText) := by rfl

theorem geometryRow039_meanGap_numerator_no_slash :
    geometryRow039_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_meanGap_numerator_parse :
    SourceJson.intChars geometryRow039_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_parse :
    SourceJson.intChars geometryRow039_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_meanGap_parse :
    parseRational geometryRow039_meanGapText = .ok geometryRowsTyped039.meanGap :=
  original_rational_fraction_of_chars geometryRow039_meanGapNumeratorChars geometryRow039_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow039_meanGap_numerator_no_slash geometryRow039_meanGap_numerator_parse
    geometryRow039_meanGap_denominator_parse geometryRow039_meanGap_denominator_nonzero

theorem geometryRow039_meanGap_read :
    rationalField geometryRowsJson039 "mean_gap" = .ok geometryRowsTyped039.meanGap :=
  original_rationalField_of_string geometryRowsJson039 "mean_gap" geometryRow039_meanGapText
    geometryRowsTyped039.meanGap geometryRow039_meanGap_field geometryRow039_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_meanGap_complete"
  err.flush

noncomputable def geometryRow039_jensenBoundNumeratorChars : List Char := ['2', '6', '1', '0', '7', '8', '5', '3', '6', '0', '5', '4', '8', '4', '8', '4', '3', '8', '2', '1', '9', '7', '2', '4', '8', '6', '4', '8', '6', '2', '8', '8', '2', '4', '1', '8', '7', '6', '9', '6', '2', '9', '2', '6', '8', '0', '5', '6', '9', '2', '3', '1', '6', '8', '0', '2', '0', '2', '4', '7', '1', '6', '3', '7', '4', '4', '6', '7', '8', '0', '7', '9', '9', '5', '0', '5', '9', '8', '9', '4', '3', '5', '2', '8', '4', '9', '9', '5', '9', '4', '9', '1', '8', '9', '7', '8', '4', '8', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_jensenBoundDenominatorChars : List Char := ['4', '6', '7', '2', '9', '0', '5', '5', '1', '9', '2', '2', '3', '6', '7', '3', '7', '4', '3', '3', '3', '1', '8', '4', '7', '3', '5', '1', '5', '9', '8', '1', '1', '4', '3', '8', '0', '8', '0', '3', '3', '5', '4', '0', '6', '8', '4', '9', '7', '9', '5', '8', '9', '3', '0', '7', '5', '2', '5', '1', '6', '4', '7', '3', '1', '8', '5', '4', '2', '5', '3', '7', '1', '4', '0', '1', '1', '3', '5', '9', '8', '2', '5', '6', '3', '0', '9', '4', '0', '3', '2', '3', '8', '3', '4', '8', '0', '0', '9', '2', '8', '6', '5', '4', '3', '9', '0', '2', '4', '7', '2', '7', '2', '0', '2', '2', '8', '4', '8', '6', '6', '3', '9', '6', '8', '0', '0', '5', '5', '9']
noncomputable def geometryRow039_jensenBoundText : String := String.ofList (geometryRow039_jensenBoundNumeratorChars ++ '/' :: geometryRow039_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_jensenBound_before_field"
  err.flush

theorem geometryRow039_jensenBound_field :
    geometryRowsJson039.getObjVal? "jensen_bound" = .ok (.str geometryRow039_jensenBoundText) := by rfl

theorem geometryRow039_jensenBound_numerator_no_slash :
    geometryRow039_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow039_jensenBoundNumeratorChars = some (2610785360548484382197248648628824187696292680569231680202471637446780799505989435284995949189784882812500000000000 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow039_jensenBoundDenominatorChars = some (4672905519223673743331847351598114380803354068497958930752516473185425371401135982563094032383480092865439024727202284866396800559 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_nonzero : (4672905519223673743331847351598114380803354068497958930752516473185425371401135982563094032383480092865439024727202284866396800559 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_jensenBound_parse :
    parseRational geometryRow039_jensenBoundText = .ok geometryRowsTyped039.jensenBound :=
  original_rational_fraction_of_chars geometryRow039_jensenBoundNumeratorChars geometryRow039_jensenBoundDenominatorChars
    (2610785360548484382197248648628824187696292680569231680202471637446780799505989435284995949189784882812500000000000 : Int) (4672905519223673743331847351598114380803354068497958930752516473185425371401135982563094032383480092865439024727202284866396800559 : Int)
    geometryRow039_jensenBound_numerator_no_slash geometryRow039_jensenBound_numerator_parse
    geometryRow039_jensenBound_denominator_parse geometryRow039_jensenBound_denominator_nonzero

theorem geometryRow039_jensenBound_read :
    rationalField geometryRowsJson039 "jensen_bound" = .ok geometryRowsTyped039.jensenBound :=
  original_rationalField_of_string geometryRowsJson039 "jensen_bound" geometryRow039_jensenBoundText
    geometryRowsTyped039.jensenBound geometryRow039_jensenBound_field geometryRow039_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_factorMaxima_before"
  err.flush

theorem geometryRow039_factorMaxima_read :
    rationalArrayField geometryRowsJson039 "factor_maxima" = .ok geometryRowsTyped039.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_gapWeightedMeans_before"
  err.flush

theorem geometryRow039_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson039 "gap_weighted_means" = .ok geometryRowsTyped039.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow039_floorChars : List Char := ['4', '4', '2', '6', '5', '3', '3', '4', '7', '0', '1', '1', '7', '3']
noncomputable def geometryRow039_floorText : String := String.ofList geometryRow039_floorChars

theorem geometryRow039_floor_text_read :
    geometryRowsJson039.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow039_floorText := by rfl

theorem geometryRow039_floor_chars_parse :
    SourceJson.intChars geometryRow039_floorChars = some (44265334701173 : Int) := by decide +kernel

theorem geometryRow039_floor_parse :
    parseInteger geometryRow039_floorText = .ok geometryRowsTyped039.jensenFloorQ96 := by
  simp only [geometryRow039_floorText, parseInteger, String.toList_ofList, geometryRow039_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_039 :
    decodeGeometryRow geometryRowsJson039 = .ok geometryRowsTyped039 :=
  original_geometryRow_of_fields geometryRowsJson039 geometryRowsTyped039 geometryRow039_floorText
    geometryRow039_simplexId_read geometryRow039_vertexIds_read
    geometryRow039_physicalVolume_read geometryRow039_meanGap_read
    geometryRow039_factorMaxima_read geometryRow039_gapWeightedMeans_read
    geometryRow039_jensenBound_read geometryRow039_floor_text_read geometryRow039_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_039_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock019 : List SourceJson := [geometryRowsJson038, geometryRowsJson039]
noncomputable def geometryRowsTypedBlock019 : List (GeometryRow) := [geometryRowsTyped038, geometryRowsTyped039]
noncomputable def geometryRowsTypedThroughBlock019 : List (GeometryRow) := geometryRowsTypedThroughBlock018 ++ geometryRowsTypedBlock019

theorem geometry_Rows_block_019_push_eq (acc : List SourceJson) :
    SimplicesBlock019.blockPush acc = [geometryRowsJson039, geometryRowsJson038] ++ acc := by rfl

theorem geometry_Rows_block_019_reverse (acc : List SourceJson) :
    (SimplicesBlock019.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock019 := by
  rw [geometry_Rows_block_019_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_019 :
    geometryRowsJsonBlock019.mapM decodeGeometryRow = .ok geometryRowsTypedBlock019 := by
  simp only [geometryRowsJsonBlock019, geometryRowsTypedBlock019, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_038, decode_geometry_Rows_039]
  rfl

theorem decode_geometry_Rows_through_block_019 :
    SimplicesValue.arrayAcc020.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock019 := by
  change (SimplicesBlock019.blockPush SimplicesValue.arrayAcc019).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_019_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_018, decode_geometry_Rows_block_019]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_019_complete"
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
#print axioms geometryRow039_simplexId_read
#print axioms geometryRow039_vertexIds_read
#print axioms geometryRow039_physicalVolume_field
#print axioms geometryRow039_physicalVolume_numerator_no_slash
#print axioms geometryRow039_physicalVolume_numerator_parse
#print axioms geometryRow039_physicalVolume_denominator_parse
#print axioms geometryRow039_physicalVolume_denominator_nonzero
#print axioms geometryRow039_physicalVolume_parse
#print axioms geometryRow039_physicalVolume_read
#print axioms geometryRow039_meanGap_field
#print axioms geometryRow039_meanGap_numerator_no_slash
#print axioms geometryRow039_meanGap_numerator_parse
#print axioms geometryRow039_meanGap_denominator_parse
#print axioms geometryRow039_meanGap_denominator_nonzero
#print axioms geometryRow039_meanGap_parse
#print axioms geometryRow039_meanGap_read
#print axioms geometryRow039_jensenBound_field
#print axioms geometryRow039_jensenBound_numerator_no_slash
#print axioms geometryRow039_jensenBound_numerator_parse
#print axioms geometryRow039_jensenBound_denominator_parse
#print axioms geometryRow039_jensenBound_denominator_nonzero
#print axioms geometryRow039_jensenBound_parse
#print axioms geometryRow039_jensenBound_read
#print axioms geometryRow039_factorMaxima_read
#print axioms geometryRow039_gapWeightedMeans_read
#print axioms geometryRow039_floor_text_read
#print axioms geometryRow039_floor_chars_parse
#print axioms geometryRow039_floor_parse
#print axioms decode_geometry_Rows_039
#print axioms geometry_Rows_block_019_push_eq
#print axioms geometry_Rows_block_019_reverse
#print axioms decode_geometry_Rows_block_019
#print axioms decode_geometry_Rows_through_block_019

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
