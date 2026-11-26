import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows028

/-! Original simplices typed block 29, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson057 : SourceJson :=
  (SimplicesBlock029.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped057 : GeometryRow :=
  { simplexId := 57,
    vertexIds := #[39, 35, 24, 22, 19, 18, 7, 6, 0],
    physicalVolume := ((428736751928002710014670849468270964472477 : ℚ) / (2255880281776128000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((1668108750577 : ℚ) / (22184400000000 : ℚ)), ((1672967126197 : ℚ) / (22184400000000 : ℚ)), ((129076692403 : ℚ) / (887376000000 : ℚ)), ((3577836936353 : ℚ) / (33276600000000 : ℚ)), ((1268538788983 : ℚ) / (22184400000000 : ℚ)), ((1075015547429 : ℚ) / (22184400000000 : ℚ)), ((938431938391 : ℚ) / (22184400000000 : ℚ)), ((914738571071 : ℚ) / (22184400000000 : ℚ)), ((304912364037 : ℚ) / (7394800000000 : ℚ)), ((2554361417639 : ℚ) / (66553200000000 : ℚ))],
    jensenBound := ((1841681067015332880482469732596142187398963732678625235400851932272051437027067648000000000000000000000 : ℚ) / (13506304485391453397281633757096660416577157305198595229832655087865785685844788062880485692724518518448925389107385113 : ℚ)),
    jensenFloorQ96 := (10803325738343 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_simplexId_before"
  err.flush

theorem geometryRow057_simplexId_read :
    geometryRowsJson057.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped057.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_vertexIds_before"
  err.flush

theorem geometryRow057_vertexIds_read :
    geometryRowsJson057.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped057.vertexIds := by decide +kernel

noncomputable def geometryRow057_physicalVolumeNumeratorChars : List Char := ['4', '2', '8', '7', '3', '6', '7', '5', '1', '9', '2', '8', '0', '0', '2', '7', '1', '0', '0', '1', '4', '6', '7', '0', '8', '4', '9', '4', '6', '8', '2', '7', '0', '9', '6', '4', '4', '7', '2', '4', '7', '7']
noncomputable def geometryRow057_physicalVolumeDenominatorChars : List Char := ['2', '2', '5', '5', '8', '8', '0', '2', '8', '1', '7', '7', '6', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow057_physicalVolumeText : String := String.ofList (geometryRow057_physicalVolumeNumeratorChars ++ '/' :: geometryRow057_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_physicalVolume_before_field"
  err.flush

theorem geometryRow057_physicalVolume_field :
    geometryRowsJson057.getObjVal? "physical_volume" = .ok (.str geometryRow057_physicalVolumeText) := by rfl

theorem geometryRow057_physicalVolume_numerator_no_slash :
    geometryRow057_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow057_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow057_physicalVolumeNumeratorChars = some (428736751928002710014670849468270964472477 : Int) := by decide +kernel

theorem geometryRow057_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow057_physicalVolumeDenominatorChars = some (2255880281776128000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow057_physicalVolume_denominator_nonzero : (2255880281776128000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow057_physicalVolume_parse :
    parseRational geometryRow057_physicalVolumeText = .ok geometryRowsTyped057.physicalVolume :=
  original_rational_fraction_of_chars geometryRow057_physicalVolumeNumeratorChars geometryRow057_physicalVolumeDenominatorChars
    (428736751928002710014670849468270964472477 : Int) (2255880281776128000000000000000000000000000000000000000000000000000 : Int)
    geometryRow057_physicalVolume_numerator_no_slash geometryRow057_physicalVolume_numerator_parse
    geometryRow057_physicalVolume_denominator_parse geometryRow057_physicalVolume_denominator_nonzero

theorem geometryRow057_physicalVolume_read :
    rationalField geometryRowsJson057 "physical_volume" = .ok geometryRowsTyped057.physicalVolume :=
  original_rationalField_of_string geometryRowsJson057 "physical_volume" geometryRow057_physicalVolumeText
    geometryRowsTyped057.physicalVolume geometryRow057_physicalVolume_field geometryRow057_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_physicalVolume_complete"
  err.flush

noncomputable def geometryRow057_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow057_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow057_meanGapText : String := String.ofList (geometryRow057_meanGapNumeratorChars ++ '/' :: geometryRow057_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_meanGap_before_field"
  err.flush

theorem geometryRow057_meanGap_field :
    geometryRowsJson057.getObjVal? "mean_gap" = .ok (.str geometryRow057_meanGapText) := by rfl

theorem geometryRow057_meanGap_numerator_no_slash :
    geometryRow057_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow057_meanGap_numerator_parse :
    SourceJson.intChars geometryRow057_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow057_meanGap_denominator_parse :
    SourceJson.intChars geometryRow057_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow057_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow057_meanGap_parse :
    parseRational geometryRow057_meanGapText = .ok geometryRowsTyped057.meanGap :=
  original_rational_fraction_of_chars geometryRow057_meanGapNumeratorChars geometryRow057_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow057_meanGap_numerator_no_slash geometryRow057_meanGap_numerator_parse
    geometryRow057_meanGap_denominator_parse geometryRow057_meanGap_denominator_nonzero

theorem geometryRow057_meanGap_read :
    rationalField geometryRowsJson057 "mean_gap" = .ok geometryRowsTyped057.meanGap :=
  original_rationalField_of_string geometryRowsJson057 "mean_gap" geometryRow057_meanGapText
    geometryRowsTyped057.meanGap geometryRow057_meanGap_field geometryRow057_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_meanGap_complete"
  err.flush

noncomputable def geometryRow057_jensenBoundNumeratorChars : List Char := ['1', '8', '4', '1', '6', '8', '1', '0', '6', '7', '0', '1', '5', '3', '3', '2', '8', '8', '0', '4', '8', '2', '4', '6', '9', '7', '3', '2', '5', '9', '6', '1', '4', '2', '1', '8', '7', '3', '9', '8', '9', '6', '3', '7', '3', '2', '6', '7', '8', '6', '2', '5', '2', '3', '5', '4', '0', '0', '8', '5', '1', '9', '3', '2', '2', '7', '2', '0', '5', '1', '4', '3', '7', '0', '2', '7', '0', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow057_jensenBoundDenominatorChars : List Char := ['1', '3', '5', '0', '6', '3', '0', '4', '4', '8', '5', '3', '9', '1', '4', '5', '3', '3', '9', '7', '2', '8', '1', '6', '3', '3', '7', '5', '7', '0', '9', '6', '6', '6', '0', '4', '1', '6', '5', '7', '7', '1', '5', '7', '3', '0', '5', '1', '9', '8', '5', '9', '5', '2', '2', '9', '8', '3', '2', '6', '5', '5', '0', '8', '7', '8', '6', '5', '7', '8', '5', '6', '8', '5', '8', '4', '4', '7', '8', '8', '0', '6', '2', '8', '8', '0', '4', '8', '5', '6', '9', '2', '7', '2', '4', '5', '1', '8', '5', '1', '8', '4', '4', '8', '9', '2', '5', '3', '8', '9', '1', '0', '7', '3', '8', '5', '1', '1', '3']
noncomputable def geometryRow057_jensenBoundText : String := String.ofList (geometryRow057_jensenBoundNumeratorChars ++ '/' :: geometryRow057_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_jensenBound_before_field"
  err.flush

theorem geometryRow057_jensenBound_field :
    geometryRowsJson057.getObjVal? "jensen_bound" = .ok (.str geometryRow057_jensenBoundText) := by rfl

theorem geometryRow057_jensenBound_numerator_no_slash :
    geometryRow057_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow057_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow057_jensenBoundNumeratorChars = some (1841681067015332880482469732596142187398963732678625235400851932272051437027067648000000000000000000000 : Int) := by decide +kernel

theorem geometryRow057_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow057_jensenBoundDenominatorChars = some (13506304485391453397281633757096660416577157305198595229832655087865785685844788062880485692724518518448925389107385113 : Int) := by decide +kernel

theorem geometryRow057_jensenBound_denominator_nonzero : (13506304485391453397281633757096660416577157305198595229832655087865785685844788062880485692724518518448925389107385113 : Int) ≠ 0 := by decide +kernel

theorem geometryRow057_jensenBound_parse :
    parseRational geometryRow057_jensenBoundText = .ok geometryRowsTyped057.jensenBound :=
  original_rational_fraction_of_chars geometryRow057_jensenBoundNumeratorChars geometryRow057_jensenBoundDenominatorChars
    (1841681067015332880482469732596142187398963732678625235400851932272051437027067648000000000000000000000 : Int) (13506304485391453397281633757096660416577157305198595229832655087865785685844788062880485692724518518448925389107385113 : Int)
    geometryRow057_jensenBound_numerator_no_slash geometryRow057_jensenBound_numerator_parse
    geometryRow057_jensenBound_denominator_parse geometryRow057_jensenBound_denominator_nonzero

theorem geometryRow057_jensenBound_read :
    rationalField geometryRowsJson057 "jensen_bound" = .ok geometryRowsTyped057.jensenBound :=
  original_rationalField_of_string geometryRowsJson057 "jensen_bound" geometryRow057_jensenBoundText
    geometryRowsTyped057.jensenBound geometryRow057_jensenBound_field geometryRow057_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_factorMaxima_before"
  err.flush

theorem geometryRow057_factorMaxima_read :
    rationalArrayField geometryRowsJson057 "factor_maxima" = .ok geometryRowsTyped057.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_gapWeightedMeans_before"
  err.flush

theorem geometryRow057_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson057 "gap_weighted_means" = .ok geometryRowsTyped057.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow057_floorChars : List Char := ['1', '0', '8', '0', '3', '3', '2', '5', '7', '3', '8', '3', '4', '3']
noncomputable def geometryRow057_floorText : String := String.ofList geometryRow057_floorChars

theorem geometryRow057_floor_text_read :
    geometryRowsJson057.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow057_floorText := by rfl

theorem geometryRow057_floor_chars_parse :
    SourceJson.intChars geometryRow057_floorChars = some (10803325738343 : Int) := by decide +kernel

theorem geometryRow057_floor_parse :
    parseInteger geometryRow057_floorText = .ok geometryRowsTyped057.jensenFloorQ96 := by
  simp only [geometryRow057_floorText, parseInteger, String.toList_ofList, geometryRow057_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_057 :
    decodeGeometryRow geometryRowsJson057 = .ok geometryRowsTyped057 :=
  original_geometryRow_of_fields geometryRowsJson057 geometryRowsTyped057 geometryRow057_floorText
    geometryRow057_simplexId_read geometryRow057_vertexIds_read
    geometryRow057_physicalVolume_read geometryRow057_meanGap_read
    geometryRow057_factorMaxima_read geometryRow057_gapWeightedMeans_read
    geometryRow057_jensenBound_read geometryRow057_floor_text_read geometryRow057_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_057_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson058 : SourceJson :=
  (SimplicesBlock029.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped058 : GeometryRow :=
  { simplexId := 58,
    vertexIds := #[39, 35, 24, 22, 19, 18, 15, 7, 0],
    physicalVolume := ((149895441514388194366066828290101867170937 : ℚ) / (2320334004112588800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((4868627741923 : ℚ) / (66553200000000 : ℚ)), ((4883202868783 : ℚ) / (66553200000000 : ℚ)), ((29145277756811 : ℚ) / (199659600000000 : ℚ)), ((1770537912361 : ℚ) / (16638300000000 : ℚ)), ((11264812319203 : ℚ) / (199659600000000 : ℚ)), ((9719162407249 : ℚ) / (199659600000000 : ℚ)), ((8573416819409 : ℚ) / (199659600000000 : ℚ)), ((8360176513529 : ℚ) / (199659600000000 : ℚ)), ((8360163202889 : ℚ) / (199659600000000 : ℚ)), ((7986672888839 : ℚ) / (199659600000000 : ℚ))],
    jensenBound := ((2664123388471242356668429879916074005164381079389453070063613439381890231850802003346212000000000000000000000000 : ℚ) / (58437942782327996489445812864029637982536156797650201657951894640136356618425538778376643064005199073083390301191073594075552793 : ℚ)),
    jensenFloorQ96 := (3611927298092 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_simplexId_before"
  err.flush

theorem geometryRow058_simplexId_read :
    geometryRowsJson058.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped058.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_vertexIds_before"
  err.flush

theorem geometryRow058_vertexIds_read :
    geometryRowsJson058.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped058.vertexIds := by decide +kernel

noncomputable def geometryRow058_physicalVolumeNumeratorChars : List Char := ['1', '4', '9', '8', '9', '5', '4', '4', '1', '5', '1', '4', '3', '8', '8', '1', '9', '4', '3', '6', '6', '0', '6', '6', '8', '2', '8', '2', '9', '0', '1', '0', '1', '8', '6', '7', '1', '7', '0', '9', '3', '7']
noncomputable def geometryRow058_physicalVolumeDenominatorChars : List Char := ['2', '3', '2', '0', '3', '3', '4', '0', '0', '4', '1', '1', '2', '5', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow058_physicalVolumeText : String := String.ofList (geometryRow058_physicalVolumeNumeratorChars ++ '/' :: geometryRow058_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_physicalVolume_before_field"
  err.flush

theorem geometryRow058_physicalVolume_field :
    geometryRowsJson058.getObjVal? "physical_volume" = .ok (.str geometryRow058_physicalVolumeText) := by rfl

theorem geometryRow058_physicalVolume_numerator_no_slash :
    geometryRow058_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow058_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow058_physicalVolumeNumeratorChars = some (149895441514388194366066828290101867170937 : Int) := by decide +kernel

theorem geometryRow058_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow058_physicalVolumeDenominatorChars = some (2320334004112588800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow058_physicalVolume_denominator_nonzero : (2320334004112588800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow058_physicalVolume_parse :
    parseRational geometryRow058_physicalVolumeText = .ok geometryRowsTyped058.physicalVolume :=
  original_rational_fraction_of_chars geometryRow058_physicalVolumeNumeratorChars geometryRow058_physicalVolumeDenominatorChars
    (149895441514388194366066828290101867170937 : Int) (2320334004112588800000000000000000000000000000000000000000000000000 : Int)
    geometryRow058_physicalVolume_numerator_no_slash geometryRow058_physicalVolume_numerator_parse
    geometryRow058_physicalVolume_denominator_parse geometryRow058_physicalVolume_denominator_nonzero

theorem geometryRow058_physicalVolume_read :
    rationalField geometryRowsJson058 "physical_volume" = .ok geometryRowsTyped058.physicalVolume :=
  original_rationalField_of_string geometryRowsJson058 "physical_volume" geometryRow058_physicalVolumeText
    geometryRowsTyped058.physicalVolume geometryRow058_physicalVolume_field geometryRow058_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_physicalVolume_complete"
  err.flush

noncomputable def geometryRow058_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow058_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow058_meanGapText : String := String.ofList (geometryRow058_meanGapNumeratorChars ++ '/' :: geometryRow058_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_meanGap_before_field"
  err.flush

theorem geometryRow058_meanGap_field :
    geometryRowsJson058.getObjVal? "mean_gap" = .ok (.str geometryRow058_meanGapText) := by rfl

theorem geometryRow058_meanGap_numerator_no_slash :
    geometryRow058_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow058_meanGap_numerator_parse :
    SourceJson.intChars geometryRow058_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow058_meanGap_denominator_parse :
    SourceJson.intChars geometryRow058_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow058_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow058_meanGap_parse :
    parseRational geometryRow058_meanGapText = .ok geometryRowsTyped058.meanGap :=
  original_rational_fraction_of_chars geometryRow058_meanGapNumeratorChars geometryRow058_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow058_meanGap_numerator_no_slash geometryRow058_meanGap_numerator_parse
    geometryRow058_meanGap_denominator_parse geometryRow058_meanGap_denominator_nonzero

theorem geometryRow058_meanGap_read :
    rationalField geometryRowsJson058 "mean_gap" = .ok geometryRowsTyped058.meanGap :=
  original_rationalField_of_string geometryRowsJson058 "mean_gap" geometryRow058_meanGapText
    geometryRowsTyped058.meanGap geometryRow058_meanGap_field geometryRow058_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_meanGap_complete"
  err.flush

noncomputable def geometryRow058_jensenBoundNumeratorChars : List Char := ['2', '6', '6', '4', '1', '2', '3', '3', '8', '8', '4', '7', '1', '2', '4', '2', '3', '5', '6', '6', '6', '8', '4', '2', '9', '8', '7', '9', '9', '1', '6', '0', '7', '4', '0', '0', '5', '1', '6', '4', '3', '8', '1', '0', '7', '9', '3', '8', '9', '4', '5', '3', '0', '7', '0', '0', '6', '3', '6', '1', '3', '4', '3', '9', '3', '8', '1', '8', '9', '0', '2', '3', '1', '8', '5', '0', '8', '0', '2', '0', '0', '3', '3', '4', '6', '2', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow058_jensenBoundDenominatorChars : List Char := ['5', '8', '4', '3', '7', '9', '4', '2', '7', '8', '2', '3', '2', '7', '9', '9', '6', '4', '8', '9', '4', '4', '5', '8', '1', '2', '8', '6', '4', '0', '2', '9', '6', '3', '7', '9', '8', '2', '5', '3', '6', '1', '5', '6', '7', '9', '7', '6', '5', '0', '2', '0', '1', '6', '5', '7', '9', '5', '1', '8', '9', '4', '6', '4', '0', '1', '3', '6', '3', '5', '6', '6', '1', '8', '4', '2', '5', '5', '3', '8', '7', '7', '8', '3', '7', '6', '6', '4', '3', '0', '6', '4', '0', '0', '5', '1', '9', '9', '0', '7', '3', '0', '8', '3', '3', '9', '0', '3', '0', '1', '1', '9', '1', '0', '7', '3', '5', '9', '4', '0', '7', '5', '5', '5', '2', '7', '9', '3']
noncomputable def geometryRow058_jensenBoundText : String := String.ofList (geometryRow058_jensenBoundNumeratorChars ++ '/' :: geometryRow058_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_jensenBound_before_field"
  err.flush

theorem geometryRow058_jensenBound_field :
    geometryRowsJson058.getObjVal? "jensen_bound" = .ok (.str geometryRow058_jensenBoundText) := by rfl

theorem geometryRow058_jensenBound_numerator_no_slash :
    geometryRow058_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow058_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow058_jensenBoundNumeratorChars = some (2664123388471242356668429879916074005164381079389453070063613439381890231850802003346212000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow058_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow058_jensenBoundDenominatorChars = some (58437942782327996489445812864029637982536156797650201657951894640136356618425538778376643064005199073083390301191073594075552793 : Int) := by decide +kernel

theorem geometryRow058_jensenBound_denominator_nonzero : (58437942782327996489445812864029637982536156797650201657951894640136356618425538778376643064005199073083390301191073594075552793 : Int) ≠ 0 := by decide +kernel

theorem geometryRow058_jensenBound_parse :
    parseRational geometryRow058_jensenBoundText = .ok geometryRowsTyped058.jensenBound :=
  original_rational_fraction_of_chars geometryRow058_jensenBoundNumeratorChars geometryRow058_jensenBoundDenominatorChars
    (2664123388471242356668429879916074005164381079389453070063613439381890231850802003346212000000000000000000000000 : Int) (58437942782327996489445812864029637982536156797650201657951894640136356618425538778376643064005199073083390301191073594075552793 : Int)
    geometryRow058_jensenBound_numerator_no_slash geometryRow058_jensenBound_numerator_parse
    geometryRow058_jensenBound_denominator_parse geometryRow058_jensenBound_denominator_nonzero

theorem geometryRow058_jensenBound_read :
    rationalField geometryRowsJson058 "jensen_bound" = .ok geometryRowsTyped058.jensenBound :=
  original_rationalField_of_string geometryRowsJson058 "jensen_bound" geometryRow058_jensenBoundText
    geometryRowsTyped058.jensenBound geometryRow058_jensenBound_field geometryRow058_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_factorMaxima_before"
  err.flush

theorem geometryRow058_factorMaxima_read :
    rationalArrayField geometryRowsJson058 "factor_maxima" = .ok geometryRowsTyped058.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_gapWeightedMeans_before"
  err.flush

theorem geometryRow058_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson058 "gap_weighted_means" = .ok geometryRowsTyped058.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow058_floorChars : List Char := ['3', '6', '1', '1', '9', '2', '7', '2', '9', '8', '0', '9', '2']
noncomputable def geometryRow058_floorText : String := String.ofList geometryRow058_floorChars

theorem geometryRow058_floor_text_read :
    geometryRowsJson058.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow058_floorText := by rfl

theorem geometryRow058_floor_chars_parse :
    SourceJson.intChars geometryRow058_floorChars = some (3611927298092 : Int) := by decide +kernel

theorem geometryRow058_floor_parse :
    parseInteger geometryRow058_floorText = .ok geometryRowsTyped058.jensenFloorQ96 := by
  simp only [geometryRow058_floorText, parseInteger, String.toList_ofList, geometryRow058_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_058 :
    decodeGeometryRow geometryRowsJson058 = .ok geometryRowsTyped058 :=
  original_geometryRow_of_fields geometryRowsJson058 geometryRowsTyped058 geometryRow058_floorText
    geometryRow058_simplexId_read geometryRow058_vertexIds_read
    geometryRow058_physicalVolume_read geometryRow058_meanGap_read
    geometryRow058_factorMaxima_read geometryRow058_gapWeightedMeans_read
    geometryRow058_jensenBound_read geometryRow058_floor_text_read geometryRow058_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_058_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock029 : List SourceJson := [geometryRowsJson057, geometryRowsJson058]
noncomputable def geometryRowsTypedBlock029 : List (GeometryRow) := [geometryRowsTyped057, geometryRowsTyped058]
noncomputable def geometryRowsTypedThroughBlock029 : List (GeometryRow) := geometryRowsTypedThroughBlock028 ++ geometryRowsTypedBlock029

theorem geometry_Rows_block_029_push_eq (acc : List SourceJson) :
    SimplicesBlock029.blockPush acc = [geometryRowsJson058, geometryRowsJson057] ++ acc := by rfl

theorem geometry_Rows_block_029_reverse (acc : List SourceJson) :
    (SimplicesBlock029.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock029 := by
  rw [geometry_Rows_block_029_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_029 :
    geometryRowsJsonBlock029.mapM decodeGeometryRow = .ok geometryRowsTypedBlock029 := by
  simp only [geometryRowsJsonBlock029, geometryRowsTypedBlock029, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_057, decode_geometry_Rows_058]
  rfl

theorem decode_geometry_Rows_through_block_029 :
    SimplicesValue.arrayAcc030.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock029 := by
  change (SimplicesBlock029.blockPush SimplicesValue.arrayAcc029).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_029_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_028, decode_geometry_Rows_block_029]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_029_complete"
  err.flush

#print axioms geometryRow057_simplexId_read
#print axioms geometryRow057_vertexIds_read
#print axioms geometryRow057_physicalVolume_field
#print axioms geometryRow057_physicalVolume_numerator_no_slash
#print axioms geometryRow057_physicalVolume_numerator_parse
#print axioms geometryRow057_physicalVolume_denominator_parse
#print axioms geometryRow057_physicalVolume_denominator_nonzero
#print axioms geometryRow057_physicalVolume_parse
#print axioms geometryRow057_physicalVolume_read
#print axioms geometryRow057_meanGap_field
#print axioms geometryRow057_meanGap_numerator_no_slash
#print axioms geometryRow057_meanGap_numerator_parse
#print axioms geometryRow057_meanGap_denominator_parse
#print axioms geometryRow057_meanGap_denominator_nonzero
#print axioms geometryRow057_meanGap_parse
#print axioms geometryRow057_meanGap_read
#print axioms geometryRow057_jensenBound_field
#print axioms geometryRow057_jensenBound_numerator_no_slash
#print axioms geometryRow057_jensenBound_numerator_parse
#print axioms geometryRow057_jensenBound_denominator_parse
#print axioms geometryRow057_jensenBound_denominator_nonzero
#print axioms geometryRow057_jensenBound_parse
#print axioms geometryRow057_jensenBound_read
#print axioms geometryRow057_factorMaxima_read
#print axioms geometryRow057_gapWeightedMeans_read
#print axioms geometryRow057_floor_text_read
#print axioms geometryRow057_floor_chars_parse
#print axioms geometryRow057_floor_parse
#print axioms decode_geometry_Rows_057
#print axioms geometryRow058_simplexId_read
#print axioms geometryRow058_vertexIds_read
#print axioms geometryRow058_physicalVolume_field
#print axioms geometryRow058_physicalVolume_numerator_no_slash
#print axioms geometryRow058_physicalVolume_numerator_parse
#print axioms geometryRow058_physicalVolume_denominator_parse
#print axioms geometryRow058_physicalVolume_denominator_nonzero
#print axioms geometryRow058_physicalVolume_parse
#print axioms geometryRow058_physicalVolume_read
#print axioms geometryRow058_meanGap_field
#print axioms geometryRow058_meanGap_numerator_no_slash
#print axioms geometryRow058_meanGap_numerator_parse
#print axioms geometryRow058_meanGap_denominator_parse
#print axioms geometryRow058_meanGap_denominator_nonzero
#print axioms geometryRow058_meanGap_parse
#print axioms geometryRow058_meanGap_read
#print axioms geometryRow058_jensenBound_field
#print axioms geometryRow058_jensenBound_numerator_no_slash
#print axioms geometryRow058_jensenBound_numerator_parse
#print axioms geometryRow058_jensenBound_denominator_parse
#print axioms geometryRow058_jensenBound_denominator_nonzero
#print axioms geometryRow058_jensenBound_parse
#print axioms geometryRow058_jensenBound_read
#print axioms geometryRow058_factorMaxima_read
#print axioms geometryRow058_gapWeightedMeans_read
#print axioms geometryRow058_floor_text_read
#print axioms geometryRow058_floor_chars_parse
#print axioms geometryRow058_floor_parse
#print axioms decode_geometry_Rows_058
#print axioms geometry_Rows_block_029_push_eq
#print axioms geometry_Rows_block_029_reverse
#print axioms decode_geometry_Rows_block_029
#print axioms decode_geometry_Rows_through_block_029

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
