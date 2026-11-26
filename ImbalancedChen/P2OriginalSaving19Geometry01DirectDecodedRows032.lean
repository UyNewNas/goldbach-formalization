import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows031

/-! Original simplices typed block 32, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson063 : SourceJson :=
  (SimplicesBlock032.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped063 : GeometryRow :=
  { simplexId := 63,
    vertexIds := #[39, 35, 34, 29, 28, 10, 8, 3, 1],
    physicalVolume := ((302495678750644647287045844275278639 : ℚ) / (154014842880000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((613946036023 : ℚ) / (7425600000000 : ℚ)), ((621452138263 : ℚ) / (7425600000000 : ℚ)), ((41612197307 : ℚ) / (285600000000 : ℚ)), ((285641975803 : ℚ) / (2475200000000 : ℚ)), ((29089254983 : ℚ) / (436800000000 : ℚ)), ((174230239129 : ℚ) / (3712800000000 : ℚ)), ((1135181951507 : ℚ) / (29702400000000 : ℚ)), ((1073555613097 : ℚ) / (29702400000000 : ℚ)), ((80006416111 : ℚ) / (2475200000000 : ℚ)), ((240018258253 : ℚ) / (7425600000000 : ℚ))],
    jensenBound := ((162156658064856687373017040304755346504126497510228915305910865575280640000000000000000000000000 : ℚ) / (19286919763418483020068276840601112601149114469922348049609357247850599481449721550479329782099052718978314839 : ℚ)),
    jensenFloorQ96 := (666118499766877 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_simplexId_before"
  err.flush

theorem geometryRow063_simplexId_read :
    geometryRowsJson063.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped063.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_vertexIds_before"
  err.flush

theorem geometryRow063_vertexIds_read :
    geometryRowsJson063.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped063.vertexIds := by decide +kernel

noncomputable def geometryRow063_physicalVolumeNumeratorChars : List Char := ['3', '0', '2', '4', '9', '5', '6', '7', '8', '7', '5', '0', '6', '4', '4', '6', '4', '7', '2', '8', '7', '0', '4', '5', '8', '4', '4', '2', '7', '5', '2', '7', '8', '6', '3', '9']
noncomputable def geometryRow063_physicalVolumeDenominatorChars : List Char := ['1', '5', '4', '0', '1', '4', '8', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow063_physicalVolumeText : String := String.ofList (geometryRow063_physicalVolumeNumeratorChars ++ '/' :: geometryRow063_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_physicalVolume_before_field"
  err.flush

theorem geometryRow063_physicalVolume_field :
    geometryRowsJson063.getObjVal? "physical_volume" = .ok (.str geometryRow063_physicalVolumeText) := by rfl

theorem geometryRow063_physicalVolume_numerator_no_slash :
    geometryRow063_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow063_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow063_physicalVolumeNumeratorChars = some (302495678750644647287045844275278639 : Int) := by decide +kernel

theorem geometryRow063_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow063_physicalVolumeDenominatorChars = some (154014842880000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow063_physicalVolume_denominator_nonzero : (154014842880000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow063_physicalVolume_parse :
    parseRational geometryRow063_physicalVolumeText = .ok geometryRowsTyped063.physicalVolume :=
  original_rational_fraction_of_chars geometryRow063_physicalVolumeNumeratorChars geometryRow063_physicalVolumeDenominatorChars
    (302495678750644647287045844275278639 : Int) (154014842880000000000000000000000000000000000000000000000000 : Int)
    geometryRow063_physicalVolume_numerator_no_slash geometryRow063_physicalVolume_numerator_parse
    geometryRow063_physicalVolume_denominator_parse geometryRow063_physicalVolume_denominator_nonzero

theorem geometryRow063_physicalVolume_read :
    rationalField geometryRowsJson063 "physical_volume" = .ok geometryRowsTyped063.physicalVolume :=
  original_rationalField_of_string geometryRowsJson063 "physical_volume" geometryRow063_physicalVolumeText
    geometryRowsTyped063.physicalVolume geometryRow063_physicalVolume_field geometryRow063_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_physicalVolume_complete"
  err.flush

noncomputable def geometryRow063_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow063_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow063_meanGapText : String := String.ofList (geometryRow063_meanGapNumeratorChars ++ '/' :: geometryRow063_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_meanGap_before_field"
  err.flush

theorem geometryRow063_meanGap_field :
    geometryRowsJson063.getObjVal? "mean_gap" = .ok (.str geometryRow063_meanGapText) := by rfl

theorem geometryRow063_meanGap_numerator_no_slash :
    geometryRow063_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow063_meanGap_numerator_parse :
    SourceJson.intChars geometryRow063_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow063_meanGap_denominator_parse :
    SourceJson.intChars geometryRow063_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow063_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow063_meanGap_parse :
    parseRational geometryRow063_meanGapText = .ok geometryRowsTyped063.meanGap :=
  original_rational_fraction_of_chars geometryRow063_meanGapNumeratorChars geometryRow063_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow063_meanGap_numerator_no_slash geometryRow063_meanGap_numerator_parse
    geometryRow063_meanGap_denominator_parse geometryRow063_meanGap_denominator_nonzero

theorem geometryRow063_meanGap_read :
    rationalField geometryRowsJson063 "mean_gap" = .ok geometryRowsTyped063.meanGap :=
  original_rationalField_of_string geometryRowsJson063 "mean_gap" geometryRow063_meanGapText
    geometryRowsTyped063.meanGap geometryRow063_meanGap_field geometryRow063_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_meanGap_complete"
  err.flush

noncomputable def geometryRow063_jensenBoundNumeratorChars : List Char := ['1', '6', '2', '1', '5', '6', '6', '5', '8', '0', '6', '4', '8', '5', '6', '6', '8', '7', '3', '7', '3', '0', '1', '7', '0', '4', '0', '3', '0', '4', '7', '5', '5', '3', '4', '6', '5', '0', '4', '1', '2', '6', '4', '9', '7', '5', '1', '0', '2', '2', '8', '9', '1', '5', '3', '0', '5', '9', '1', '0', '8', '6', '5', '5', '7', '5', '2', '8', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow063_jensenBoundDenominatorChars : List Char := ['1', '9', '2', '8', '6', '9', '1', '9', '7', '6', '3', '4', '1', '8', '4', '8', '3', '0', '2', '0', '0', '6', '8', '2', '7', '6', '8', '4', '0', '6', '0', '1', '1', '1', '2', '6', '0', '1', '1', '4', '9', '1', '1', '4', '4', '6', '9', '9', '2', '2', '3', '4', '8', '0', '4', '9', '6', '0', '9', '3', '5', '7', '2', '4', '7', '8', '5', '0', '5', '9', '9', '4', '8', '1', '4', '4', '9', '7', '2', '1', '5', '5', '0', '4', '7', '9', '3', '2', '9', '7', '8', '2', '0', '9', '9', '0', '5', '2', '7', '1', '8', '9', '7', '8', '3', '1', '4', '8', '3', '9']
noncomputable def geometryRow063_jensenBoundText : String := String.ofList (geometryRow063_jensenBoundNumeratorChars ++ '/' :: geometryRow063_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_jensenBound_before_field"
  err.flush

theorem geometryRow063_jensenBound_field :
    geometryRowsJson063.getObjVal? "jensen_bound" = .ok (.str geometryRow063_jensenBoundText) := by rfl

theorem geometryRow063_jensenBound_numerator_no_slash :
    geometryRow063_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow063_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow063_jensenBoundNumeratorChars = some (162156658064856687373017040304755346504126497510228915305910865575280640000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow063_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow063_jensenBoundDenominatorChars = some (19286919763418483020068276840601112601149114469922348049609357247850599481449721550479329782099052718978314839 : Int) := by decide +kernel

theorem geometryRow063_jensenBound_denominator_nonzero : (19286919763418483020068276840601112601149114469922348049609357247850599481449721550479329782099052718978314839 : Int) ≠ 0 := by decide +kernel

theorem geometryRow063_jensenBound_parse :
    parseRational geometryRow063_jensenBoundText = .ok geometryRowsTyped063.jensenBound :=
  original_rational_fraction_of_chars geometryRow063_jensenBoundNumeratorChars geometryRow063_jensenBoundDenominatorChars
    (162156658064856687373017040304755346504126497510228915305910865575280640000000000000000000000000 : Int) (19286919763418483020068276840601112601149114469922348049609357247850599481449721550479329782099052718978314839 : Int)
    geometryRow063_jensenBound_numerator_no_slash geometryRow063_jensenBound_numerator_parse
    geometryRow063_jensenBound_denominator_parse geometryRow063_jensenBound_denominator_nonzero

theorem geometryRow063_jensenBound_read :
    rationalField geometryRowsJson063 "jensen_bound" = .ok geometryRowsTyped063.jensenBound :=
  original_rationalField_of_string geometryRowsJson063 "jensen_bound" geometryRow063_jensenBoundText
    geometryRowsTyped063.jensenBound geometryRow063_jensenBound_field geometryRow063_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_factorMaxima_before"
  err.flush

theorem geometryRow063_factorMaxima_read :
    rationalArrayField geometryRowsJson063 "factor_maxima" = .ok geometryRowsTyped063.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_gapWeightedMeans_before"
  err.flush

theorem geometryRow063_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson063 "gap_weighted_means" = .ok geometryRowsTyped063.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow063_floorChars : List Char := ['6', '6', '6', '1', '1', '8', '4', '9', '9', '7', '6', '6', '8', '7', '7']
noncomputable def geometryRow063_floorText : String := String.ofList geometryRow063_floorChars

theorem geometryRow063_floor_text_read :
    geometryRowsJson063.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow063_floorText := by rfl

theorem geometryRow063_floor_chars_parse :
    SourceJson.intChars geometryRow063_floorChars = some (666118499766877 : Int) := by decide +kernel

theorem geometryRow063_floor_parse :
    parseInteger geometryRow063_floorText = .ok geometryRowsTyped063.jensenFloorQ96 := by
  simp only [geometryRow063_floorText, parseInteger, String.toList_ofList, geometryRow063_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_063 :
    decodeGeometryRow geometryRowsJson063 = .ok geometryRowsTyped063 :=
  original_geometryRow_of_fields geometryRowsJson063 geometryRowsTyped063 geometryRow063_floorText
    geometryRow063_simplexId_read geometryRow063_vertexIds_read
    geometryRow063_physicalVolume_read geometryRow063_meanGap_read
    geometryRow063_factorMaxima_read geometryRow063_gapWeightedMeans_read
    geometryRow063_jensenBound_read geometryRow063_floor_text_read geometryRow063_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_063_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson064 : SourceJson :=
  (SimplicesBlock032.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped064 : GeometryRow :=
  { simplexId := 64,
    vertexIds := #[39, 35, 34, 29, 11, 10, 8, 3, 1],
    physicalVolume := ((621377717412233384890486362146179 : ℚ) / (267386880000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1244827197071 : ℚ) / (14851200000000 : ℚ)), ((1259839401551 : ℚ) / (14851200000000 : ℚ)), ((27596720213 : ℚ) / (190400000000 : ℚ)), ((565638909931 : ℚ) / (4950400000000 : ℚ)), ((18839401197 : ℚ) / (291200000000 : ℚ)), ((118035173311 : ℚ) / (2475200000000 : ℚ)), ((297143821853 : ℚ) / (7425600000000 : ℚ)), ((527016263621 : ℚ) / (14851200000000 : ℚ)), ((485683538341 : ℚ) / (14851200000000 : ℚ)), ((161893852727 : ℚ) / (4950400000000 : ℚ))],
    jensenBound := ((2113935202033650223598327919872034610534286652970048459381259833170009784320000000000000000000000000 : ℚ) / (223435794896227883150894947236379322449410409002477316028003201603269439637456197714373521552962184856477821432837 : ℚ)),
    jensenFloorQ96 := (749580888814757 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_simplexId_before"
  err.flush

theorem geometryRow064_simplexId_read :
    geometryRowsJson064.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped064.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_vertexIds_before"
  err.flush

theorem geometryRow064_vertexIds_read :
    geometryRowsJson064.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped064.vertexIds := by decide +kernel

noncomputable def geometryRow064_physicalVolumeNumeratorChars : List Char := ['6', '2', '1', '3', '7', '7', '7', '1', '7', '4', '1', '2', '2', '3', '3', '3', '8', '4', '8', '9', '0', '4', '8', '6', '3', '6', '2', '1', '4', '6', '1', '7', '9']
noncomputable def geometryRow064_physicalVolumeDenominatorChars : List Char := ['2', '6', '7', '3', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow064_physicalVolumeText : String := String.ofList (geometryRow064_physicalVolumeNumeratorChars ++ '/' :: geometryRow064_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_physicalVolume_before_field"
  err.flush

theorem geometryRow064_physicalVolume_field :
    geometryRowsJson064.getObjVal? "physical_volume" = .ok (.str geometryRow064_physicalVolumeText) := by rfl

theorem geometryRow064_physicalVolume_numerator_no_slash :
    geometryRow064_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow064_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow064_physicalVolumeNumeratorChars = some (621377717412233384890486362146179 : Int) := by decide +kernel

theorem geometryRow064_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow064_physicalVolumeDenominatorChars = some (267386880000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow064_physicalVolume_denominator_nonzero : (267386880000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow064_physicalVolume_parse :
    parseRational geometryRow064_physicalVolumeText = .ok geometryRowsTyped064.physicalVolume :=
  original_rational_fraction_of_chars geometryRow064_physicalVolumeNumeratorChars geometryRow064_physicalVolumeDenominatorChars
    (621377717412233384890486362146179 : Int) (267386880000000000000000000000000000000000000000000000000 : Int)
    geometryRow064_physicalVolume_numerator_no_slash geometryRow064_physicalVolume_numerator_parse
    geometryRow064_physicalVolume_denominator_parse geometryRow064_physicalVolume_denominator_nonzero

theorem geometryRow064_physicalVolume_read :
    rationalField geometryRowsJson064 "physical_volume" = .ok geometryRowsTyped064.physicalVolume :=
  original_rationalField_of_string geometryRowsJson064 "physical_volume" geometryRow064_physicalVolumeText
    geometryRowsTyped064.physicalVolume geometryRow064_physicalVolume_field geometryRow064_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_physicalVolume_complete"
  err.flush

noncomputable def geometryRow064_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow064_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow064_meanGapText : String := String.ofList (geometryRow064_meanGapNumeratorChars ++ '/' :: geometryRow064_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_meanGap_before_field"
  err.flush

theorem geometryRow064_meanGap_field :
    geometryRowsJson064.getObjVal? "mean_gap" = .ok (.str geometryRow064_meanGapText) := by rfl

theorem geometryRow064_meanGap_numerator_no_slash :
    geometryRow064_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow064_meanGap_numerator_parse :
    SourceJson.intChars geometryRow064_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow064_meanGap_denominator_parse :
    SourceJson.intChars geometryRow064_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow064_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow064_meanGap_parse :
    parseRational geometryRow064_meanGapText = .ok geometryRowsTyped064.meanGap :=
  original_rational_fraction_of_chars geometryRow064_meanGapNumeratorChars geometryRow064_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow064_meanGap_numerator_no_slash geometryRow064_meanGap_numerator_parse
    geometryRow064_meanGap_denominator_parse geometryRow064_meanGap_denominator_nonzero

theorem geometryRow064_meanGap_read :
    rationalField geometryRowsJson064 "mean_gap" = .ok geometryRowsTyped064.meanGap :=
  original_rationalField_of_string geometryRowsJson064 "mean_gap" geometryRow064_meanGapText
    geometryRowsTyped064.meanGap geometryRow064_meanGap_field geometryRow064_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_meanGap_complete"
  err.flush

noncomputable def geometryRow064_jensenBoundNumeratorChars : List Char := ['2', '1', '1', '3', '9', '3', '5', '2', '0', '2', '0', '3', '3', '6', '5', '0', '2', '2', '3', '5', '9', '8', '3', '2', '7', '9', '1', '9', '8', '7', '2', '0', '3', '4', '6', '1', '0', '5', '3', '4', '2', '8', '6', '6', '5', '2', '9', '7', '0', '0', '4', '8', '4', '5', '9', '3', '8', '1', '2', '5', '9', '8', '3', '3', '1', '7', '0', '0', '0', '9', '7', '8', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow064_jensenBoundDenominatorChars : List Char := ['2', '2', '3', '4', '3', '5', '7', '9', '4', '8', '9', '6', '2', '2', '7', '8', '8', '3', '1', '5', '0', '8', '9', '4', '9', '4', '7', '2', '3', '6', '3', '7', '9', '3', '2', '2', '4', '4', '9', '4', '1', '0', '4', '0', '9', '0', '0', '2', '4', '7', '7', '3', '1', '6', '0', '2', '8', '0', '0', '3', '2', '0', '1', '6', '0', '3', '2', '6', '9', '4', '3', '9', '6', '3', '7', '4', '5', '6', '1', '9', '7', '7', '1', '4', '3', '7', '3', '5', '2', '1', '5', '5', '2', '9', '6', '2', '1', '8', '4', '8', '5', '6', '4', '7', '7', '8', '2', '1', '4', '3', '2', '8', '3', '7']
noncomputable def geometryRow064_jensenBoundText : String := String.ofList (geometryRow064_jensenBoundNumeratorChars ++ '/' :: geometryRow064_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_jensenBound_before_field"
  err.flush

theorem geometryRow064_jensenBound_field :
    geometryRowsJson064.getObjVal? "jensen_bound" = .ok (.str geometryRow064_jensenBoundText) := by rfl

theorem geometryRow064_jensenBound_numerator_no_slash :
    geometryRow064_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow064_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow064_jensenBoundNumeratorChars = some (2113935202033650223598327919872034610534286652970048459381259833170009784320000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow064_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow064_jensenBoundDenominatorChars = some (223435794896227883150894947236379322449410409002477316028003201603269439637456197714373521552962184856477821432837 : Int) := by decide +kernel

theorem geometryRow064_jensenBound_denominator_nonzero : (223435794896227883150894947236379322449410409002477316028003201603269439637456197714373521552962184856477821432837 : Int) ≠ 0 := by decide +kernel

theorem geometryRow064_jensenBound_parse :
    parseRational geometryRow064_jensenBoundText = .ok geometryRowsTyped064.jensenBound :=
  original_rational_fraction_of_chars geometryRow064_jensenBoundNumeratorChars geometryRow064_jensenBoundDenominatorChars
    (2113935202033650223598327919872034610534286652970048459381259833170009784320000000000000000000000000 : Int) (223435794896227883150894947236379322449410409002477316028003201603269439637456197714373521552962184856477821432837 : Int)
    geometryRow064_jensenBound_numerator_no_slash geometryRow064_jensenBound_numerator_parse
    geometryRow064_jensenBound_denominator_parse geometryRow064_jensenBound_denominator_nonzero

theorem geometryRow064_jensenBound_read :
    rationalField geometryRowsJson064 "jensen_bound" = .ok geometryRowsTyped064.jensenBound :=
  original_rationalField_of_string geometryRowsJson064 "jensen_bound" geometryRow064_jensenBoundText
    geometryRowsTyped064.jensenBound geometryRow064_jensenBound_field geometryRow064_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_factorMaxima_before"
  err.flush

theorem geometryRow064_factorMaxima_read :
    rationalArrayField geometryRowsJson064 "factor_maxima" = .ok geometryRowsTyped064.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_gapWeightedMeans_before"
  err.flush

theorem geometryRow064_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson064 "gap_weighted_means" = .ok geometryRowsTyped064.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow064_floorChars : List Char := ['7', '4', '9', '5', '8', '0', '8', '8', '8', '8', '1', '4', '7', '5', '7']
noncomputable def geometryRow064_floorText : String := String.ofList geometryRow064_floorChars

theorem geometryRow064_floor_text_read :
    geometryRowsJson064.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow064_floorText := by rfl

theorem geometryRow064_floor_chars_parse :
    SourceJson.intChars geometryRow064_floorChars = some (749580888814757 : Int) := by decide +kernel

theorem geometryRow064_floor_parse :
    parseInteger geometryRow064_floorText = .ok geometryRowsTyped064.jensenFloorQ96 := by
  simp only [geometryRow064_floorText, parseInteger, String.toList_ofList, geometryRow064_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_064 :
    decodeGeometryRow geometryRowsJson064 = .ok geometryRowsTyped064 :=
  original_geometryRow_of_fields geometryRowsJson064 geometryRowsTyped064 geometryRow064_floorText
    geometryRow064_simplexId_read geometryRow064_vertexIds_read
    geometryRow064_physicalVolume_read geometryRow064_meanGap_read
    geometryRow064_factorMaxima_read geometryRow064_gapWeightedMeans_read
    geometryRow064_jensenBound_read geometryRow064_floor_text_read geometryRow064_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_064_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock032 : List SourceJson := [geometryRowsJson063, geometryRowsJson064]
noncomputable def geometryRowsTypedBlock032 : List (GeometryRow) := [geometryRowsTyped063, geometryRowsTyped064]
noncomputable def geometryRowsTypedThroughBlock032 : List (GeometryRow) := geometryRowsTypedThroughBlock031 ++ geometryRowsTypedBlock032

theorem geometry_Rows_block_032_push_eq (acc : List SourceJson) :
    SimplicesBlock032.blockPush acc = [geometryRowsJson064, geometryRowsJson063] ++ acc := by rfl

theorem geometry_Rows_block_032_reverse (acc : List SourceJson) :
    (SimplicesBlock032.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock032 := by
  rw [geometry_Rows_block_032_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_032 :
    geometryRowsJsonBlock032.mapM decodeGeometryRow = .ok geometryRowsTypedBlock032 := by
  simp only [geometryRowsJsonBlock032, geometryRowsTypedBlock032, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_063, decode_geometry_Rows_064]
  rfl

theorem decode_geometry_Rows_through_block_032 :
    SimplicesValue.arrayAcc033.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock032 := by
  change (SimplicesBlock032.blockPush SimplicesValue.arrayAcc032).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_032_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_031, decode_geometry_Rows_block_032]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_032_complete"
  err.flush

#print axioms geometryRow063_simplexId_read
#print axioms geometryRow063_vertexIds_read
#print axioms geometryRow063_physicalVolume_field
#print axioms geometryRow063_physicalVolume_numerator_no_slash
#print axioms geometryRow063_physicalVolume_numerator_parse
#print axioms geometryRow063_physicalVolume_denominator_parse
#print axioms geometryRow063_physicalVolume_denominator_nonzero
#print axioms geometryRow063_physicalVolume_parse
#print axioms geometryRow063_physicalVolume_read
#print axioms geometryRow063_meanGap_field
#print axioms geometryRow063_meanGap_numerator_no_slash
#print axioms geometryRow063_meanGap_numerator_parse
#print axioms geometryRow063_meanGap_denominator_parse
#print axioms geometryRow063_meanGap_denominator_nonzero
#print axioms geometryRow063_meanGap_parse
#print axioms geometryRow063_meanGap_read
#print axioms geometryRow063_jensenBound_field
#print axioms geometryRow063_jensenBound_numerator_no_slash
#print axioms geometryRow063_jensenBound_numerator_parse
#print axioms geometryRow063_jensenBound_denominator_parse
#print axioms geometryRow063_jensenBound_denominator_nonzero
#print axioms geometryRow063_jensenBound_parse
#print axioms geometryRow063_jensenBound_read
#print axioms geometryRow063_factorMaxima_read
#print axioms geometryRow063_gapWeightedMeans_read
#print axioms geometryRow063_floor_text_read
#print axioms geometryRow063_floor_chars_parse
#print axioms geometryRow063_floor_parse
#print axioms decode_geometry_Rows_063
#print axioms geometryRow064_simplexId_read
#print axioms geometryRow064_vertexIds_read
#print axioms geometryRow064_physicalVolume_field
#print axioms geometryRow064_physicalVolume_numerator_no_slash
#print axioms geometryRow064_physicalVolume_numerator_parse
#print axioms geometryRow064_physicalVolume_denominator_parse
#print axioms geometryRow064_physicalVolume_denominator_nonzero
#print axioms geometryRow064_physicalVolume_parse
#print axioms geometryRow064_physicalVolume_read
#print axioms geometryRow064_meanGap_field
#print axioms geometryRow064_meanGap_numerator_no_slash
#print axioms geometryRow064_meanGap_numerator_parse
#print axioms geometryRow064_meanGap_denominator_parse
#print axioms geometryRow064_meanGap_denominator_nonzero
#print axioms geometryRow064_meanGap_parse
#print axioms geometryRow064_meanGap_read
#print axioms geometryRow064_jensenBound_field
#print axioms geometryRow064_jensenBound_numerator_no_slash
#print axioms geometryRow064_jensenBound_numerator_parse
#print axioms geometryRow064_jensenBound_denominator_parse
#print axioms geometryRow064_jensenBound_denominator_nonzero
#print axioms geometryRow064_jensenBound_parse
#print axioms geometryRow064_jensenBound_read
#print axioms geometryRow064_factorMaxima_read
#print axioms geometryRow064_gapWeightedMeans_read
#print axioms geometryRow064_floor_text_read
#print axioms geometryRow064_floor_chars_parse
#print axioms geometryRow064_floor_parse
#print axioms decode_geometry_Rows_064
#print axioms geometry_Rows_block_032_push_eq
#print axioms geometry_Rows_block_032_reverse
#print axioms decode_geometry_Rows_block_032
#print axioms decode_geometry_Rows_through_block_032

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
