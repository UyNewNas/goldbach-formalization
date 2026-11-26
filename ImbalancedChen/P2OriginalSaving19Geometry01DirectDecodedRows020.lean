import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows019

/-! Original simplices typed block 20, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson040 : SourceJson :=
  (SimplicesBlock020.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped040 : GeometryRow :=
  { simplexId := 40,
    vertexIds := #[39, 35, 24, 23, 21, 8, 3, 2, 0],
    physicalVolume := ((46166611876702508220524981471206839577846711 : ℚ) / (52250637164544000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((1108356092994801919 : ℚ) / (13565546311616000000 : ℚ)), ((276690178828721749101 : ℚ) / (3323558846345920000000 : ℚ)), ((330126244904542605749 : ℚ) / (2300925355162560000000 : ℚ)), ((2737542571681194902717 : ℚ) / (24926691347594400000000 : ℚ)), ((527820608438954022799 : ℚ) / (8797655769739200000000 : ℚ)), ((7171377298736799548279 : ℚ) / (149560148085566400000000 : ℚ)), ((311995710176161105429 : ℚ) / (7871586741345600000000 : ℚ)), ((5848058228414525708671 : ℚ) / (149560148085566400000000 : ℚ)), ((5575360160384653671013 : ℚ) / (149560148085566400000000 : ℚ)), ((5496113853053846195323 : ℚ) / (149560148085566400000000 : ℚ))],
    jensenBound := ((379228656673470494508757441684612660705264752542079707357365747628679984381733372981661461079038590361130430114667107094416680401132927556872254907746147795753304468487940341760000000000000000000 : ℚ) / (61288631888083970154223232413037545743918569747324556551359129592030093070774801222611719974108132593628328285504824240189187252353502874195854122095440115788596495227473582669139234028706752353765860969771 : ℚ)),
    jensenFloorQ96 := (490231038210423539 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_simplexId_before"
  err.flush

theorem geometryRow040_simplexId_read :
    geometryRowsJson040.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped040.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_vertexIds_before"
  err.flush

theorem geometryRow040_vertexIds_read :
    geometryRowsJson040.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped040.vertexIds := by decide +kernel

noncomputable def geometryRow040_physicalVolumeNumeratorChars : List Char := ['4', '6', '1', '6', '6', '6', '1', '1', '8', '7', '6', '7', '0', '2', '5', '0', '8', '2', '2', '0', '5', '2', '4', '9', '8', '1', '4', '7', '1', '2', '0', '6', '8', '3', '9', '5', '7', '7', '8', '4', '6', '7', '1', '1']
noncomputable def geometryRow040_physicalVolumeDenominatorChars : List Char := ['5', '2', '2', '5', '0', '6', '3', '7', '1', '6', '4', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_physicalVolumeText : String := String.ofList (geometryRow040_physicalVolumeNumeratorChars ++ '/' :: geometryRow040_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_physicalVolume_before_field"
  err.flush

theorem geometryRow040_physicalVolume_field :
    geometryRowsJson040.getObjVal? "physical_volume" = .ok (.str geometryRow040_physicalVolumeText) := by rfl

theorem geometryRow040_physicalVolume_numerator_no_slash :
    geometryRow040_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeNumeratorChars = some (46166611876702508220524981471206839577846711 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeDenominatorChars = some (52250637164544000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_nonzero : (52250637164544000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_physicalVolume_parse :
    parseRational geometryRow040_physicalVolumeText = .ok geometryRowsTyped040.physicalVolume :=
  original_rational_fraction_of_chars geometryRow040_physicalVolumeNumeratorChars geometryRow040_physicalVolumeDenominatorChars
    (46166611876702508220524981471206839577846711 : Int) (52250637164544000000000000000000000000000000000000000000000000000 : Int)
    geometryRow040_physicalVolume_numerator_no_slash geometryRow040_physicalVolume_numerator_parse
    geometryRow040_physicalVolume_denominator_parse geometryRow040_physicalVolume_denominator_nonzero

theorem geometryRow040_physicalVolume_read :
    rationalField geometryRowsJson040 "physical_volume" = .ok geometryRowsTyped040.physicalVolume :=
  original_rationalField_of_string geometryRowsJson040 "physical_volume" geometryRow040_physicalVolumeText
    geometryRowsTyped040.physicalVolume geometryRow040_physicalVolume_field geometryRow040_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_physicalVolume_complete"
  err.flush

noncomputable def geometryRow040_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow040_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow040_meanGapText : String := String.ofList (geometryRow040_meanGapNumeratorChars ++ '/' :: geometryRow040_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_meanGap_before_field"
  err.flush

theorem geometryRow040_meanGap_field :
    geometryRowsJson040.getObjVal? "mean_gap" = .ok (.str geometryRow040_meanGapText) := by rfl

theorem geometryRow040_meanGap_numerator_no_slash :
    geometryRow040_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_meanGap_numerator_parse :
    SourceJson.intChars geometryRow040_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_parse :
    SourceJson.intChars geometryRow040_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_meanGap_parse :
    parseRational geometryRow040_meanGapText = .ok geometryRowsTyped040.meanGap :=
  original_rational_fraction_of_chars geometryRow040_meanGapNumeratorChars geometryRow040_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow040_meanGap_numerator_no_slash geometryRow040_meanGap_numerator_parse
    geometryRow040_meanGap_denominator_parse geometryRow040_meanGap_denominator_nonzero

theorem geometryRow040_meanGap_read :
    rationalField geometryRowsJson040 "mean_gap" = .ok geometryRowsTyped040.meanGap :=
  original_rationalField_of_string geometryRowsJson040 "mean_gap" geometryRow040_meanGapText
    geometryRowsTyped040.meanGap geometryRow040_meanGap_field geometryRow040_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_meanGap_complete"
  err.flush

noncomputable def geometryRow040_jensenBoundNumeratorChars : List Char := ['3', '7', '9', '2', '2', '8', '6', '5', '6', '6', '7', '3', '4', '7', '0', '4', '9', '4', '5', '0', '8', '7', '5', '7', '4', '4', '1', '6', '8', '4', '6', '1', '2', '6', '6', '0', '7', '0', '5', '2', '6', '4', '7', '5', '2', '5', '4', '2', '0', '7', '9', '7', '0', '7', '3', '5', '7', '3', '6', '5', '7', '4', '7', '6', '2', '8', '6', '7', '9', '9', '8', '4', '3', '8', '1', '7', '3', '3', '3', '7', '2', '9', '8', '1', '6', '6', '1', '4', '6', '1', '0', '7', '9', '0', '3', '8', '5', '9', '0', '3', '6', '1', '1', '3', '0', '4', '3', '0', '1', '1', '4', '6', '6', '7', '1', '0', '7', '0', '9', '4', '4', '1', '6', '6', '8', '0', '4', '0', '1', '1', '3', '2', '9', '2', '7', '5', '5', '6', '8', '7', '2', '2', '5', '4', '9', '0', '7', '7', '4', '6', '1', '4', '7', '7', '9', '5', '7', '5', '3', '3', '0', '4', '4', '6', '8', '4', '8', '7', '9', '4', '0', '3', '4', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_jensenBoundDenominatorChars : List Char := ['6', '1', '2', '8', '8', '6', '3', '1', '8', '8', '8', '0', '8', '3', '9', '7', '0', '1', '5', '4', '2', '2', '3', '2', '3', '2', '4', '1', '3', '0', '3', '7', '5', '4', '5', '7', '4', '3', '9', '1', '8', '5', '6', '9', '7', '4', '7', '3', '2', '4', '5', '5', '6', '5', '5', '1', '3', '5', '9', '1', '2', '9', '5', '9', '2', '0', '3', '0', '0', '9', '3', '0', '7', '0', '7', '7', '4', '8', '0', '1', '2', '2', '2', '6', '1', '1', '7', '1', '9', '9', '7', '4', '1', '0', '8', '1', '3', '2', '5', '9', '3', '6', '2', '8', '3', '2', '8', '2', '8', '5', '5', '0', '4', '8', '2', '4', '2', '4', '0', '1', '8', '9', '1', '8', '7', '2', '5', '2', '3', '5', '3', '5', '0', '2', '8', '7', '4', '1', '9', '5', '8', '5', '4', '1', '2', '2', '0', '9', '5', '4', '4', '0', '1', '1', '5', '7', '8', '8', '5', '9', '6', '4', '9', '5', '2', '2', '7', '4', '7', '3', '5', '8', '2', '6', '6', '9', '1', '3', '9', '2', '3', '4', '0', '2', '8', '7', '0', '6', '7', '5', '2', '3', '5', '3', '7', '6', '5', '8', '6', '0', '9', '6', '9', '7', '7', '1']
noncomputable def geometryRow040_jensenBoundText : String := String.ofList (geometryRow040_jensenBoundNumeratorChars ++ '/' :: geometryRow040_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_jensenBound_before_field"
  err.flush

theorem geometryRow040_jensenBound_field :
    geometryRowsJson040.getObjVal? "jensen_bound" = .ok (.str geometryRow040_jensenBoundText) := by rfl

theorem geometryRow040_jensenBound_numerator_no_slash :
    geometryRow040_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow040_jensenBoundNumeratorChars = some (379228656673470494508757441684612660705264752542079707357365747628679984381733372981661461079038590361130430114667107094416680401132927556872254907746147795753304468487940341760000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow040_jensenBoundDenominatorChars = some (61288631888083970154223232413037545743918569747324556551359129592030093070774801222611719974108132593628328285504824240189187252353502874195854122095440115788596495227473582669139234028706752353765860969771 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_nonzero : (61288631888083970154223232413037545743918569747324556551359129592030093070774801222611719974108132593628328285504824240189187252353502874195854122095440115788596495227473582669139234028706752353765860969771 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_jensenBound_parse :
    parseRational geometryRow040_jensenBoundText = .ok geometryRowsTyped040.jensenBound :=
  original_rational_fraction_of_chars geometryRow040_jensenBoundNumeratorChars geometryRow040_jensenBoundDenominatorChars
    (379228656673470494508757441684612660705264752542079707357365747628679984381733372981661461079038590361130430114667107094416680401132927556872254907746147795753304468487940341760000000000000000000 : Int) (61288631888083970154223232413037545743918569747324556551359129592030093070774801222611719974108132593628328285504824240189187252353502874195854122095440115788596495227473582669139234028706752353765860969771 : Int)
    geometryRow040_jensenBound_numerator_no_slash geometryRow040_jensenBound_numerator_parse
    geometryRow040_jensenBound_denominator_parse geometryRow040_jensenBound_denominator_nonzero

theorem geometryRow040_jensenBound_read :
    rationalField geometryRowsJson040 "jensen_bound" = .ok geometryRowsTyped040.jensenBound :=
  original_rationalField_of_string geometryRowsJson040 "jensen_bound" geometryRow040_jensenBoundText
    geometryRowsTyped040.jensenBound geometryRow040_jensenBound_field geometryRow040_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_factorMaxima_before"
  err.flush

theorem geometryRow040_factorMaxima_read :
    rationalArrayField geometryRowsJson040 "factor_maxima" = .ok geometryRowsTyped040.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_gapWeightedMeans_before"
  err.flush

theorem geometryRow040_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson040 "gap_weighted_means" = .ok geometryRowsTyped040.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow040_floorChars : List Char := ['4', '9', '0', '2', '3', '1', '0', '3', '8', '2', '1', '0', '4', '2', '3', '5', '3', '9']
noncomputable def geometryRow040_floorText : String := String.ofList geometryRow040_floorChars

theorem geometryRow040_floor_text_read :
    geometryRowsJson040.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow040_floorText := by rfl

theorem geometryRow040_floor_chars_parse :
    SourceJson.intChars geometryRow040_floorChars = some (490231038210423539 : Int) := by decide +kernel

theorem geometryRow040_floor_parse :
    parseInteger geometryRow040_floorText = .ok geometryRowsTyped040.jensenFloorQ96 := by
  simp only [geometryRow040_floorText, parseInteger, String.toList_ofList, geometryRow040_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_040 :
    decodeGeometryRow geometryRowsJson040 = .ok geometryRowsTyped040 :=
  original_geometryRow_of_fields geometryRowsJson040 geometryRowsTyped040 geometryRow040_floorText
    geometryRow040_simplexId_read geometryRow040_vertexIds_read
    geometryRow040_physicalVolume_read geometryRow040_meanGap_read
    geometryRow040_factorMaxima_read geometryRow040_gapWeightedMeans_read
    geometryRow040_jensenBound_read geometryRow040_floor_text_read geometryRow040_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_040_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson041 : SourceJson :=
  (SimplicesBlock020.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped041 : GeometryRow :=
  { simplexId := 41,
    vertexIds := #[39, 35, 24, 23, 21, 8, 6, 2, 0],
    physicalVolume := ((8906251488348812199422512615469039878478487437 : ℚ) / (3459203488016640000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((2639319101453 : ℚ) / (32505200000000 : ℚ)), ((18714626614051 : ℚ) / (227536400000000 : ℚ)), ((22644365513953 : ℚ) / (157525200000000 : ℚ)), ((37353237906359 : ℚ) / (341304600000000 : ℚ)), ((122123342553881 : ℚ) / (2047827600000000 : ℚ)), ((98149527596063 : ℚ) / (2047827600000000 : ℚ)), ((4306189451791 : ℚ) / (107780400000000 : ℚ)), ((80724126110209 : ℚ) / (2047827600000000 : ℚ)), ((78018569115187 : ℚ) / (2047827600000000 : ℚ)), ((2982819686731 : ℚ) / (81913104000000 : ℚ))],
    jensenBound := ((16158518257084269807057998492723487849792594174384888649503202245909106379026668919096647792689076633600000000000000000000 : ℚ) / (1761335160816948042981643118686229649206550575878150054143914799424062493011234200541267075941762071024641404428404818444363690730863 : ℚ)),
    jensenFloorQ96 := (726840489500129520 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_simplexId_before"
  err.flush

theorem geometryRow041_simplexId_read :
    geometryRowsJson041.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped041.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_vertexIds_before"
  err.flush

theorem geometryRow041_vertexIds_read :
    geometryRowsJson041.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped041.vertexIds := by decide +kernel

noncomputable def geometryRow041_physicalVolumeNumeratorChars : List Char := ['8', '9', '0', '6', '2', '5', '1', '4', '8', '8', '3', '4', '8', '8', '1', '2', '1', '9', '9', '4', '2', '2', '5', '1', '2', '6', '1', '5', '4', '6', '9', '0', '3', '9', '8', '7', '8', '4', '7', '8', '4', '8', '7', '4', '3', '7']
noncomputable def geometryRow041_physicalVolumeDenominatorChars : List Char := ['3', '4', '5', '9', '2', '0', '3', '4', '8', '8', '0', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_physicalVolumeText : String := String.ofList (geometryRow041_physicalVolumeNumeratorChars ++ '/' :: geometryRow041_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_physicalVolume_before_field"
  err.flush

theorem geometryRow041_physicalVolume_field :
    geometryRowsJson041.getObjVal? "physical_volume" = .ok (.str geometryRow041_physicalVolumeText) := by rfl

theorem geometryRow041_physicalVolume_numerator_no_slash :
    geometryRow041_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeNumeratorChars = some (8906251488348812199422512615469039878478487437 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeDenominatorChars = some (3459203488016640000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_nonzero : (3459203488016640000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_physicalVolume_parse :
    parseRational geometryRow041_physicalVolumeText = .ok geometryRowsTyped041.physicalVolume :=
  original_rational_fraction_of_chars geometryRow041_physicalVolumeNumeratorChars geometryRow041_physicalVolumeDenominatorChars
    (8906251488348812199422512615469039878478487437 : Int) (3459203488016640000000000000000000000000000000000000000000000000000 : Int)
    geometryRow041_physicalVolume_numerator_no_slash geometryRow041_physicalVolume_numerator_parse
    geometryRow041_physicalVolume_denominator_parse geometryRow041_physicalVolume_denominator_nonzero

theorem geometryRow041_physicalVolume_read :
    rationalField geometryRowsJson041 "physical_volume" = .ok geometryRowsTyped041.physicalVolume :=
  original_rationalField_of_string geometryRowsJson041 "physical_volume" geometryRow041_physicalVolumeText
    geometryRowsTyped041.physicalVolume geometryRow041_physicalVolume_field geometryRow041_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_physicalVolume_complete"
  err.flush

noncomputable def geometryRow041_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow041_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_meanGapText : String := String.ofList (geometryRow041_meanGapNumeratorChars ++ '/' :: geometryRow041_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_meanGap_before_field"
  err.flush

theorem geometryRow041_meanGap_field :
    geometryRowsJson041.getObjVal? "mean_gap" = .ok (.str geometryRow041_meanGapText) := by rfl

theorem geometryRow041_meanGap_numerator_no_slash :
    geometryRow041_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_meanGap_numerator_parse :
    SourceJson.intChars geometryRow041_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_parse :
    SourceJson.intChars geometryRow041_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_meanGap_parse :
    parseRational geometryRow041_meanGapText = .ok geometryRowsTyped041.meanGap :=
  original_rational_fraction_of_chars geometryRow041_meanGapNumeratorChars geometryRow041_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow041_meanGap_numerator_no_slash geometryRow041_meanGap_numerator_parse
    geometryRow041_meanGap_denominator_parse geometryRow041_meanGap_denominator_nonzero

theorem geometryRow041_meanGap_read :
    rationalField geometryRowsJson041 "mean_gap" = .ok geometryRowsTyped041.meanGap :=
  original_rationalField_of_string geometryRowsJson041 "mean_gap" geometryRow041_meanGapText
    geometryRowsTyped041.meanGap geometryRow041_meanGap_field geometryRow041_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_meanGap_complete"
  err.flush

noncomputable def geometryRow041_jensenBoundNumeratorChars : List Char := ['1', '6', '1', '5', '8', '5', '1', '8', '2', '5', '7', '0', '8', '4', '2', '6', '9', '8', '0', '7', '0', '5', '7', '9', '9', '8', '4', '9', '2', '7', '2', '3', '4', '8', '7', '8', '4', '9', '7', '9', '2', '5', '9', '4', '1', '7', '4', '3', '8', '4', '8', '8', '8', '6', '4', '9', '5', '0', '3', '2', '0', '2', '2', '4', '5', '9', '0', '9', '1', '0', '6', '3', '7', '9', '0', '2', '6', '6', '6', '8', '9', '1', '9', '0', '9', '6', '6', '4', '7', '7', '9', '2', '6', '8', '9', '0', '7', '6', '6', '3', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_jensenBoundDenominatorChars : List Char := ['1', '7', '6', '1', '3', '3', '5', '1', '6', '0', '8', '1', '6', '9', '4', '8', '0', '4', '2', '9', '8', '1', '6', '4', '3', '1', '1', '8', '6', '8', '6', '2', '2', '9', '6', '4', '9', '2', '0', '6', '5', '5', '0', '5', '7', '5', '8', '7', '8', '1', '5', '0', '0', '5', '4', '1', '4', '3', '9', '1', '4', '7', '9', '9', '4', '2', '4', '0', '6', '2', '4', '9', '3', '0', '1', '1', '2', '3', '4', '2', '0', '0', '5', '4', '1', '2', '6', '7', '0', '7', '5', '9', '4', '1', '7', '6', '2', '0', '7', '1', '0', '2', '4', '6', '4', '1', '4', '0', '4', '4', '2', '8', '4', '0', '4', '8', '1', '8', '4', '4', '4', '3', '6', '3', '6', '9', '0', '7', '3', '0', '8', '6', '3']
noncomputable def geometryRow041_jensenBoundText : String := String.ofList (geometryRow041_jensenBoundNumeratorChars ++ '/' :: geometryRow041_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_jensenBound_before_field"
  err.flush

theorem geometryRow041_jensenBound_field :
    geometryRowsJson041.getObjVal? "jensen_bound" = .ok (.str geometryRow041_jensenBoundText) := by rfl

theorem geometryRow041_jensenBound_numerator_no_slash :
    geometryRow041_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow041_jensenBoundNumeratorChars = some (16158518257084269807057998492723487849792594174384888649503202245909106379026668919096647792689076633600000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow041_jensenBoundDenominatorChars = some (1761335160816948042981643118686229649206550575878150054143914799424062493011234200541267075941762071024641404428404818444363690730863 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_nonzero : (1761335160816948042981643118686229649206550575878150054143914799424062493011234200541267075941762071024641404428404818444363690730863 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_jensenBound_parse :
    parseRational geometryRow041_jensenBoundText = .ok geometryRowsTyped041.jensenBound :=
  original_rational_fraction_of_chars geometryRow041_jensenBoundNumeratorChars geometryRow041_jensenBoundDenominatorChars
    (16158518257084269807057998492723487849792594174384888649503202245909106379026668919096647792689076633600000000000000000000 : Int) (1761335160816948042981643118686229649206550575878150054143914799424062493011234200541267075941762071024641404428404818444363690730863 : Int)
    geometryRow041_jensenBound_numerator_no_slash geometryRow041_jensenBound_numerator_parse
    geometryRow041_jensenBound_denominator_parse geometryRow041_jensenBound_denominator_nonzero

theorem geometryRow041_jensenBound_read :
    rationalField geometryRowsJson041 "jensen_bound" = .ok geometryRowsTyped041.jensenBound :=
  original_rationalField_of_string geometryRowsJson041 "jensen_bound" geometryRow041_jensenBoundText
    geometryRowsTyped041.jensenBound geometryRow041_jensenBound_field geometryRow041_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_factorMaxima_before"
  err.flush

theorem geometryRow041_factorMaxima_read :
    rationalArrayField geometryRowsJson041 "factor_maxima" = .ok geometryRowsTyped041.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_gapWeightedMeans_before"
  err.flush

theorem geometryRow041_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson041 "gap_weighted_means" = .ok geometryRowsTyped041.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow041_floorChars : List Char := ['7', '2', '6', '8', '4', '0', '4', '8', '9', '5', '0', '0', '1', '2', '9', '5', '2', '0']
noncomputable def geometryRow041_floorText : String := String.ofList geometryRow041_floorChars

theorem geometryRow041_floor_text_read :
    geometryRowsJson041.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow041_floorText := by rfl

theorem geometryRow041_floor_chars_parse :
    SourceJson.intChars geometryRow041_floorChars = some (726840489500129520 : Int) := by decide +kernel

theorem geometryRow041_floor_parse :
    parseInteger geometryRow041_floorText = .ok geometryRowsTyped041.jensenFloorQ96 := by
  simp only [geometryRow041_floorText, parseInteger, String.toList_ofList, geometryRow041_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_041 :
    decodeGeometryRow geometryRowsJson041 = .ok geometryRowsTyped041 :=
  original_geometryRow_of_fields geometryRowsJson041 geometryRowsTyped041 geometryRow041_floorText
    geometryRow041_simplexId_read geometryRow041_vertexIds_read
    geometryRow041_physicalVolume_read geometryRow041_meanGap_read
    geometryRow041_factorMaxima_read geometryRow041_gapWeightedMeans_read
    geometryRow041_jensenBound_read geometryRow041_floor_text_read geometryRow041_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_041_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock020 : List SourceJson := [geometryRowsJson040, geometryRowsJson041]
noncomputable def geometryRowsTypedBlock020 : List (GeometryRow) := [geometryRowsTyped040, geometryRowsTyped041]
noncomputable def geometryRowsTypedThroughBlock020 : List (GeometryRow) := geometryRowsTypedThroughBlock019 ++ geometryRowsTypedBlock020

theorem geometry_Rows_block_020_push_eq (acc : List SourceJson) :
    SimplicesBlock020.blockPush acc = [geometryRowsJson041, geometryRowsJson040] ++ acc := by rfl

theorem geometry_Rows_block_020_reverse (acc : List SourceJson) :
    (SimplicesBlock020.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock020 := by
  rw [geometry_Rows_block_020_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_020 :
    geometryRowsJsonBlock020.mapM decodeGeometryRow = .ok geometryRowsTypedBlock020 := by
  simp only [geometryRowsJsonBlock020, geometryRowsTypedBlock020, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_040, decode_geometry_Rows_041]
  rfl

theorem decode_geometry_Rows_through_block_020 :
    SimplicesValue.arrayAcc021.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock020 := by
  change (SimplicesBlock020.blockPush SimplicesValue.arrayAcc020).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_020_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_019, decode_geometry_Rows_block_020]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_020_complete"
  err.flush

#print axioms geometryRow040_simplexId_read
#print axioms geometryRow040_vertexIds_read
#print axioms geometryRow040_physicalVolume_field
#print axioms geometryRow040_physicalVolume_numerator_no_slash
#print axioms geometryRow040_physicalVolume_numerator_parse
#print axioms geometryRow040_physicalVolume_denominator_parse
#print axioms geometryRow040_physicalVolume_denominator_nonzero
#print axioms geometryRow040_physicalVolume_parse
#print axioms geometryRow040_physicalVolume_read
#print axioms geometryRow040_meanGap_field
#print axioms geometryRow040_meanGap_numerator_no_slash
#print axioms geometryRow040_meanGap_numerator_parse
#print axioms geometryRow040_meanGap_denominator_parse
#print axioms geometryRow040_meanGap_denominator_nonzero
#print axioms geometryRow040_meanGap_parse
#print axioms geometryRow040_meanGap_read
#print axioms geometryRow040_jensenBound_field
#print axioms geometryRow040_jensenBound_numerator_no_slash
#print axioms geometryRow040_jensenBound_numerator_parse
#print axioms geometryRow040_jensenBound_denominator_parse
#print axioms geometryRow040_jensenBound_denominator_nonzero
#print axioms geometryRow040_jensenBound_parse
#print axioms geometryRow040_jensenBound_read
#print axioms geometryRow040_factorMaxima_read
#print axioms geometryRow040_gapWeightedMeans_read
#print axioms geometryRow040_floor_text_read
#print axioms geometryRow040_floor_chars_parse
#print axioms geometryRow040_floor_parse
#print axioms decode_geometry_Rows_040
#print axioms geometryRow041_simplexId_read
#print axioms geometryRow041_vertexIds_read
#print axioms geometryRow041_physicalVolume_field
#print axioms geometryRow041_physicalVolume_numerator_no_slash
#print axioms geometryRow041_physicalVolume_numerator_parse
#print axioms geometryRow041_physicalVolume_denominator_parse
#print axioms geometryRow041_physicalVolume_denominator_nonzero
#print axioms geometryRow041_physicalVolume_parse
#print axioms geometryRow041_physicalVolume_read
#print axioms geometryRow041_meanGap_field
#print axioms geometryRow041_meanGap_numerator_no_slash
#print axioms geometryRow041_meanGap_numerator_parse
#print axioms geometryRow041_meanGap_denominator_parse
#print axioms geometryRow041_meanGap_denominator_nonzero
#print axioms geometryRow041_meanGap_parse
#print axioms geometryRow041_meanGap_read
#print axioms geometryRow041_jensenBound_field
#print axioms geometryRow041_jensenBound_numerator_no_slash
#print axioms geometryRow041_jensenBound_numerator_parse
#print axioms geometryRow041_jensenBound_denominator_parse
#print axioms geometryRow041_jensenBound_denominator_nonzero
#print axioms geometryRow041_jensenBound_parse
#print axioms geometryRow041_jensenBound_read
#print axioms geometryRow041_factorMaxima_read
#print axioms geometryRow041_gapWeightedMeans_read
#print axioms geometryRow041_floor_text_read
#print axioms geometryRow041_floor_chars_parse
#print axioms geometryRow041_floor_parse
#print axioms decode_geometry_Rows_041
#print axioms geometry_Rows_block_020_push_eq
#print axioms geometry_Rows_block_020_reverse
#print axioms decode_geometry_Rows_block_020
#print axioms decode_geometry_Rows_through_block_020

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
