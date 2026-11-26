import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows017

/-! Original simplices typed block 18, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson036 : SourceJson :=
  (SimplicesBlock018.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped036 : GeometryRow :=
  { simplexId := 36,
    vertexIds := #[39, 35, 24, 23, 10, 8, 3, 2, 0],
    physicalVolume := ((6439409972872703338266456862094220686477 : ℚ) / (1628887449600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((606787066796485613 : ℚ) / (7215716123200000000 : ℚ)), ((30279687128878356627 : ℚ) / (353570090036800000000 : ℚ)), ((35003930729768262779 : ℚ) / (244779293102400000000 : ℚ)), ((58793537200907586199 : ℚ) / (530355135055200000000 : ℚ)), ((11310760699613961293 : ℚ) / (187184165313600000000 : ℚ)), ((154501104335664526693 : ℚ) / (3182130810331200000000 : ℚ)), ((6562533756023473967 : ℚ) / (167480568964800000000 : ℚ)), ((122988986791413339533 : ℚ) / (3182130810331200000000 : ℚ)), ((113830507593808999223 : ℚ) / (3182130810331200000000 : ℚ)), ((112144415948472669953 : ℚ) / (3182130810331200000000 : ℚ))],
    jensenBound := ((20161422553848899390421660489283304076313183888774402231876483581428642325826088487709464615610673130636605300490783191909376751840126769223203172064608387072000000000000000000000000 : ℚ) / (711409513389821687601334032779330048001060849190104474866133837723320136039072415042334975485139588587962709863814219648160496907500309878815501243635006874519293961379459500049569963406417923 : ℚ)),
    jensenFloorQ96 := (2245334694786144614 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_simplexId_before"
  err.flush

theorem geometryRow036_simplexId_read :
    geometryRowsJson036.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped036.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_vertexIds_before"
  err.flush

theorem geometryRow036_vertexIds_read :
    geometryRowsJson036.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped036.vertexIds := by decide +kernel

noncomputable def geometryRow036_physicalVolumeNumeratorChars : List Char := ['6', '4', '3', '9', '4', '0', '9', '9', '7', '2', '8', '7', '2', '7', '0', '3', '3', '3', '8', '2', '6', '6', '4', '5', '6', '8', '6', '2', '0', '9', '4', '2', '2', '0', '6', '8', '6', '4', '7', '7']
noncomputable def geometryRow036_physicalVolumeDenominatorChars : List Char := ['1', '6', '2', '8', '8', '8', '7', '4', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_physicalVolumeText : String := String.ofList (geometryRow036_physicalVolumeNumeratorChars ++ '/' :: geometryRow036_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_physicalVolume_before_field"
  err.flush

theorem geometryRow036_physicalVolume_field :
    geometryRowsJson036.getObjVal? "physical_volume" = .ok (.str geometryRow036_physicalVolumeText) := by rfl

theorem geometryRow036_physicalVolume_numerator_no_slash :
    geometryRow036_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeNumeratorChars = some (6439409972872703338266456862094220686477 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeDenominatorChars = some (1628887449600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_nonzero : (1628887449600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_physicalVolume_parse :
    parseRational geometryRow036_physicalVolumeText = .ok geometryRowsTyped036.physicalVolume :=
  original_rational_fraction_of_chars geometryRow036_physicalVolumeNumeratorChars geometryRow036_physicalVolumeDenominatorChars
    (6439409972872703338266456862094220686477 : Int) (1628887449600000000000000000000000000000000000000000000000000 : Int)
    geometryRow036_physicalVolume_numerator_no_slash geometryRow036_physicalVolume_numerator_parse
    geometryRow036_physicalVolume_denominator_parse geometryRow036_physicalVolume_denominator_nonzero

theorem geometryRow036_physicalVolume_read :
    rationalField geometryRowsJson036 "physical_volume" = .ok geometryRowsTyped036.physicalVolume :=
  original_rationalField_of_string geometryRowsJson036 "physical_volume" geometryRow036_physicalVolumeText
    geometryRowsTyped036.physicalVolume geometryRow036_physicalVolume_field geometryRow036_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_physicalVolume_complete"
  err.flush

noncomputable def geometryRow036_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow036_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow036_meanGapText : String := String.ofList (geometryRow036_meanGapNumeratorChars ++ '/' :: geometryRow036_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_meanGap_before_field"
  err.flush

theorem geometryRow036_meanGap_field :
    geometryRowsJson036.getObjVal? "mean_gap" = .ok (.str geometryRow036_meanGapText) := by rfl

theorem geometryRow036_meanGap_numerator_no_slash :
    geometryRow036_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_meanGap_numerator_parse :
    SourceJson.intChars geometryRow036_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_parse :
    SourceJson.intChars geometryRow036_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_meanGap_parse :
    parseRational geometryRow036_meanGapText = .ok geometryRowsTyped036.meanGap :=
  original_rational_fraction_of_chars geometryRow036_meanGapNumeratorChars geometryRow036_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow036_meanGap_numerator_no_slash geometryRow036_meanGap_numerator_parse
    geometryRow036_meanGap_denominator_parse geometryRow036_meanGap_denominator_nonzero

theorem geometryRow036_meanGap_read :
    rationalField geometryRowsJson036 "mean_gap" = .ok geometryRowsTyped036.meanGap :=
  original_rationalField_of_string geometryRowsJson036 "mean_gap" geometryRow036_meanGapText
    geometryRowsTyped036.meanGap geometryRow036_meanGap_field geometryRow036_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_meanGap_complete"
  err.flush

noncomputable def geometryRow036_jensenBoundNumeratorChars : List Char := ['2', '0', '1', '6', '1', '4', '2', '2', '5', '5', '3', '8', '4', '8', '8', '9', '9', '3', '9', '0', '4', '2', '1', '6', '6', '0', '4', '8', '9', '2', '8', '3', '3', '0', '4', '0', '7', '6', '3', '1', '3', '1', '8', '3', '8', '8', '8', '7', '7', '4', '4', '0', '2', '2', '3', '1', '8', '7', '6', '4', '8', '3', '5', '8', '1', '4', '2', '8', '6', '4', '2', '3', '2', '5', '8', '2', '6', '0', '8', '8', '4', '8', '7', '7', '0', '9', '4', '6', '4', '6', '1', '5', '6', '1', '0', '6', '7', '3', '1', '3', '0', '6', '3', '6', '6', '0', '5', '3', '0', '0', '4', '9', '0', '7', '8', '3', '1', '9', '1', '9', '0', '9', '3', '7', '6', '7', '5', '1', '8', '4', '0', '1', '2', '6', '7', '6', '9', '2', '2', '3', '2', '0', '3', '1', '7', '2', '0', '6', '4', '6', '0', '8', '3', '8', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_jensenBoundDenominatorChars : List Char := ['7', '1', '1', '4', '0', '9', '5', '1', '3', '3', '8', '9', '8', '2', '1', '6', '8', '7', '6', '0', '1', '3', '3', '4', '0', '3', '2', '7', '7', '9', '3', '3', '0', '0', '4', '8', '0', '0', '1', '0', '6', '0', '8', '4', '9', '1', '9', '0', '1', '0', '4', '4', '7', '4', '8', '6', '6', '1', '3', '3', '8', '3', '7', '7', '2', '3', '3', '2', '0', '1', '3', '6', '0', '3', '9', '0', '7', '2', '4', '1', '5', '0', '4', '2', '3', '3', '4', '9', '7', '5', '4', '8', '5', '1', '3', '9', '5', '8', '8', '5', '8', '7', '9', '6', '2', '7', '0', '9', '8', '6', '3', '8', '1', '4', '2', '1', '9', '6', '4', '8', '1', '6', '0', '4', '9', '6', '9', '0', '7', '5', '0', '0', '3', '0', '9', '8', '7', '8', '8', '1', '5', '5', '0', '1', '2', '4', '3', '6', '3', '5', '0', '0', '6', '8', '7', '4', '5', '1', '9', '2', '9', '3', '9', '6', '1', '3', '7', '9', '4', '5', '9', '5', '0', '0', '0', '4', '9', '5', '6', '9', '9', '6', '3', '4', '0', '6', '4', '1', '7', '9', '2', '3']
noncomputable def geometryRow036_jensenBoundText : String := String.ofList (geometryRow036_jensenBoundNumeratorChars ++ '/' :: geometryRow036_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_jensenBound_before_field"
  err.flush

theorem geometryRow036_jensenBound_field :
    geometryRowsJson036.getObjVal? "jensen_bound" = .ok (.str geometryRow036_jensenBoundText) := by rfl

theorem geometryRow036_jensenBound_numerator_no_slash :
    geometryRow036_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow036_jensenBoundNumeratorChars = some (20161422553848899390421660489283304076313183888774402231876483581428642325826088487709464615610673130636605300490783191909376751840126769223203172064608387072000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow036_jensenBoundDenominatorChars = some (711409513389821687601334032779330048001060849190104474866133837723320136039072415042334975485139588587962709863814219648160496907500309878815501243635006874519293961379459500049569963406417923 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_nonzero : (711409513389821687601334032779330048001060849190104474866133837723320136039072415042334975485139588587962709863814219648160496907500309878815501243635006874519293961379459500049569963406417923 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_jensenBound_parse :
    parseRational geometryRow036_jensenBoundText = .ok geometryRowsTyped036.jensenBound :=
  original_rational_fraction_of_chars geometryRow036_jensenBoundNumeratorChars geometryRow036_jensenBoundDenominatorChars
    (20161422553848899390421660489283304076313183888774402231876483581428642325826088487709464615610673130636605300490783191909376751840126769223203172064608387072000000000000000000000000 : Int) (711409513389821687601334032779330048001060849190104474866133837723320136039072415042334975485139588587962709863814219648160496907500309878815501243635006874519293961379459500049569963406417923 : Int)
    geometryRow036_jensenBound_numerator_no_slash geometryRow036_jensenBound_numerator_parse
    geometryRow036_jensenBound_denominator_parse geometryRow036_jensenBound_denominator_nonzero

theorem geometryRow036_jensenBound_read :
    rationalField geometryRowsJson036 "jensen_bound" = .ok geometryRowsTyped036.jensenBound :=
  original_rationalField_of_string geometryRowsJson036 "jensen_bound" geometryRow036_jensenBoundText
    geometryRowsTyped036.jensenBound geometryRow036_jensenBound_field geometryRow036_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_factorMaxima_before"
  err.flush

theorem geometryRow036_factorMaxima_read :
    rationalArrayField geometryRowsJson036 "factor_maxima" = .ok geometryRowsTyped036.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_gapWeightedMeans_before"
  err.flush

theorem geometryRow036_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson036 "gap_weighted_means" = .ok geometryRowsTyped036.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow036_floorChars : List Char := ['2', '2', '4', '5', '3', '3', '4', '6', '9', '4', '7', '8', '6', '1', '4', '4', '6', '1', '4']
noncomputable def geometryRow036_floorText : String := String.ofList geometryRow036_floorChars

theorem geometryRow036_floor_text_read :
    geometryRowsJson036.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow036_floorText := by rfl

theorem geometryRow036_floor_chars_parse :
    SourceJson.intChars geometryRow036_floorChars = some (2245334694786144614 : Int) := by decide +kernel

theorem geometryRow036_floor_parse :
    parseInteger geometryRow036_floorText = .ok geometryRowsTyped036.jensenFloorQ96 := by
  simp only [geometryRow036_floorText, parseInteger, String.toList_ofList, geometryRow036_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_036 :
    decodeGeometryRow geometryRowsJson036 = .ok geometryRowsTyped036 :=
  original_geometryRow_of_fields geometryRowsJson036 geometryRowsTyped036 geometryRow036_floorText
    geometryRow036_simplexId_read geometryRow036_vertexIds_read
    geometryRow036_physicalVolume_read geometryRow036_meanGap_read
    geometryRow036_factorMaxima_read geometryRow036_gapWeightedMeans_read
    geometryRow036_jensenBound_read geometryRow036_floor_text_read geometryRow036_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_036_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson037 : SourceJson :=
  (SimplicesBlock018.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped037 : GeometryRow :=
  { simplexId := 37,
    vertexIds := #[39, 35, 24, 23, 10, 8, 6, 2, 0],
    physicalVolume := ((25352275569932477389301098847813784150991 : ℚ) / (2200794624000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((14451932167 : ℚ) / (172900000000 : ℚ)), ((102436891679 : ℚ) / (1210300000000 : ℚ)), ((48020830817 : ℚ) / (335160000000 : ℚ)), ((50140779079 : ℚ) / (453862500000 : ℚ)), ((654278773669 : ℚ) / (10892700000000 : ℚ)), ((1057279026239 : ℚ) / (21785400000000 : ℚ)), ((22646228567 : ℚ) / (573300000000 : ℚ)), ((106115498627 : ℚ) / (2723175000000 : ℚ)), ((797163042121 : ℚ) / (21785400000000 : ℚ)), ((760481372473 : ℚ) / (21785400000000 : ℚ))],
    jensenBound := ((6554078386468182835370441709306091964889803611957087127807357033547687278711771132812500000000000000 : ℚ) / (156184563277976349509828771928875372171319042504876037278747915695489737986902029233868822931905724117227213951 : ℚ)),
    jensenFloorQ96 := (3324704930090557271 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_simplexId_before"
  err.flush

theorem geometryRow037_simplexId_read :
    geometryRowsJson037.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped037.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_vertexIds_before"
  err.flush

theorem geometryRow037_vertexIds_read :
    geometryRowsJson037.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped037.vertexIds := by decide +kernel

noncomputable def geometryRow037_physicalVolumeNumeratorChars : List Char := ['2', '5', '3', '5', '2', '2', '7', '5', '5', '6', '9', '9', '3', '2', '4', '7', '7', '3', '8', '9', '3', '0', '1', '0', '9', '8', '8', '4', '7', '8', '1', '3', '7', '8', '4', '1', '5', '0', '9', '9', '1']
noncomputable def geometryRow037_physicalVolumeDenominatorChars : List Char := ['2', '2', '0', '0', '7', '9', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_physicalVolumeText : String := String.ofList (geometryRow037_physicalVolumeNumeratorChars ++ '/' :: geometryRow037_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_physicalVolume_before_field"
  err.flush

theorem geometryRow037_physicalVolume_field :
    geometryRowsJson037.getObjVal? "physical_volume" = .ok (.str geometryRow037_physicalVolumeText) := by rfl

theorem geometryRow037_physicalVolume_numerator_no_slash :
    geometryRow037_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeNumeratorChars = some (25352275569932477389301098847813784150991 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeDenominatorChars = some (2200794624000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_nonzero : (2200794624000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_physicalVolume_parse :
    parseRational geometryRow037_physicalVolumeText = .ok geometryRowsTyped037.physicalVolume :=
  original_rational_fraction_of_chars geometryRow037_physicalVolumeNumeratorChars geometryRow037_physicalVolumeDenominatorChars
    (25352275569932477389301098847813784150991 : Int) (2200794624000000000000000000000000000000000000000000000000000 : Int)
    geometryRow037_physicalVolume_numerator_no_slash geometryRow037_physicalVolume_numerator_parse
    geometryRow037_physicalVolume_denominator_parse geometryRow037_physicalVolume_denominator_nonzero

theorem geometryRow037_physicalVolume_read :
    rationalField geometryRowsJson037 "physical_volume" = .ok geometryRowsTyped037.physicalVolume :=
  original_rationalField_of_string geometryRowsJson037 "physical_volume" geometryRow037_physicalVolumeText
    geometryRowsTyped037.physicalVolume geometryRow037_physicalVolume_field geometryRow037_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_physicalVolume_complete"
  err.flush

noncomputable def geometryRow037_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow037_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_meanGapText : String := String.ofList (geometryRow037_meanGapNumeratorChars ++ '/' :: geometryRow037_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_meanGap_before_field"
  err.flush

theorem geometryRow037_meanGap_field :
    geometryRowsJson037.getObjVal? "mean_gap" = .ok (.str geometryRow037_meanGapText) := by rfl

theorem geometryRow037_meanGap_numerator_no_slash :
    geometryRow037_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_meanGap_numerator_parse :
    SourceJson.intChars geometryRow037_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_parse :
    SourceJson.intChars geometryRow037_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_meanGap_parse :
    parseRational geometryRow037_meanGapText = .ok geometryRowsTyped037.meanGap :=
  original_rational_fraction_of_chars geometryRow037_meanGapNumeratorChars geometryRow037_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow037_meanGap_numerator_no_slash geometryRow037_meanGap_numerator_parse
    geometryRow037_meanGap_denominator_parse geometryRow037_meanGap_denominator_nonzero

theorem geometryRow037_meanGap_read :
    rationalField geometryRowsJson037 "mean_gap" = .ok geometryRowsTyped037.meanGap :=
  original_rationalField_of_string geometryRowsJson037 "mean_gap" geometryRow037_meanGapText
    geometryRowsTyped037.meanGap geometryRow037_meanGap_field geometryRow037_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_meanGap_complete"
  err.flush

noncomputable def geometryRow037_jensenBoundNumeratorChars : List Char := ['6', '5', '5', '4', '0', '7', '8', '3', '8', '6', '4', '6', '8', '1', '8', '2', '8', '3', '5', '3', '7', '0', '4', '4', '1', '7', '0', '9', '3', '0', '6', '0', '9', '1', '9', '6', '4', '8', '8', '9', '8', '0', '3', '6', '1', '1', '9', '5', '7', '0', '8', '7', '1', '2', '7', '8', '0', '7', '3', '5', '7', '0', '3', '3', '5', '4', '7', '6', '8', '7', '2', '7', '8', '7', '1', '1', '7', '7', '1', '1', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_jensenBoundDenominatorChars : List Char := ['1', '5', '6', '1', '8', '4', '5', '6', '3', '2', '7', '7', '9', '7', '6', '3', '4', '9', '5', '0', '9', '8', '2', '8', '7', '7', '1', '9', '2', '8', '8', '7', '5', '3', '7', '2', '1', '7', '1', '3', '1', '9', '0', '4', '2', '5', '0', '4', '8', '7', '6', '0', '3', '7', '2', '7', '8', '7', '4', '7', '9', '1', '5', '6', '9', '5', '4', '8', '9', '7', '3', '7', '9', '8', '6', '9', '0', '2', '0', '2', '9', '2', '3', '3', '8', '6', '8', '8', '2', '2', '9', '3', '1', '9', '0', '5', '7', '2', '4', '1', '1', '7', '2', '2', '7', '2', '1', '3', '9', '5', '1']
noncomputable def geometryRow037_jensenBoundText : String := String.ofList (geometryRow037_jensenBoundNumeratorChars ++ '/' :: geometryRow037_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_jensenBound_before_field"
  err.flush

theorem geometryRow037_jensenBound_field :
    geometryRowsJson037.getObjVal? "jensen_bound" = .ok (.str geometryRow037_jensenBoundText) := by rfl

theorem geometryRow037_jensenBound_numerator_no_slash :
    geometryRow037_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow037_jensenBoundNumeratorChars = some (6554078386468182835370441709306091964889803611957087127807357033547687278711771132812500000000000000 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow037_jensenBoundDenominatorChars = some (156184563277976349509828771928875372171319042504876037278747915695489737986902029233868822931905724117227213951 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_nonzero : (156184563277976349509828771928875372171319042504876037278747915695489737986902029233868822931905724117227213951 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_jensenBound_parse :
    parseRational geometryRow037_jensenBoundText = .ok geometryRowsTyped037.jensenBound :=
  original_rational_fraction_of_chars geometryRow037_jensenBoundNumeratorChars geometryRow037_jensenBoundDenominatorChars
    (6554078386468182835370441709306091964889803611957087127807357033547687278711771132812500000000000000 : Int) (156184563277976349509828771928875372171319042504876037278747915695489737986902029233868822931905724117227213951 : Int)
    geometryRow037_jensenBound_numerator_no_slash geometryRow037_jensenBound_numerator_parse
    geometryRow037_jensenBound_denominator_parse geometryRow037_jensenBound_denominator_nonzero

theorem geometryRow037_jensenBound_read :
    rationalField geometryRowsJson037 "jensen_bound" = .ok geometryRowsTyped037.jensenBound :=
  original_rationalField_of_string geometryRowsJson037 "jensen_bound" geometryRow037_jensenBoundText
    geometryRowsTyped037.jensenBound geometryRow037_jensenBound_field geometryRow037_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_factorMaxima_before"
  err.flush

theorem geometryRow037_factorMaxima_read :
    rationalArrayField geometryRowsJson037 "factor_maxima" = .ok geometryRowsTyped037.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_gapWeightedMeans_before"
  err.flush

theorem geometryRow037_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson037 "gap_weighted_means" = .ok geometryRowsTyped037.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow037_floorChars : List Char := ['3', '3', '2', '4', '7', '0', '4', '9', '3', '0', '0', '9', '0', '5', '5', '7', '2', '7', '1']
noncomputable def geometryRow037_floorText : String := String.ofList geometryRow037_floorChars

theorem geometryRow037_floor_text_read :
    geometryRowsJson037.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow037_floorText := by rfl

theorem geometryRow037_floor_chars_parse :
    SourceJson.intChars geometryRow037_floorChars = some (3324704930090557271 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY01_TYPED Row_037_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock018 : List SourceJson := [geometryRowsJson036, geometryRowsJson037]
noncomputable def geometryRowsTypedBlock018 : List (GeometryRow) := [geometryRowsTyped036, geometryRowsTyped037]
noncomputable def geometryRowsTypedThroughBlock018 : List (GeometryRow) := geometryRowsTypedThroughBlock017 ++ geometryRowsTypedBlock018

theorem geometry_Rows_block_018_push_eq (acc : List SourceJson) :
    SimplicesBlock018.blockPush acc = [geometryRowsJson037, geometryRowsJson036] ++ acc := by rfl

theorem geometry_Rows_block_018_reverse (acc : List SourceJson) :
    (SimplicesBlock018.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock018 := by
  rw [geometry_Rows_block_018_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_018 :
    geometryRowsJsonBlock018.mapM decodeGeometryRow = .ok geometryRowsTypedBlock018 := by
  simp only [geometryRowsJsonBlock018, geometryRowsTypedBlock018, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_036, decode_geometry_Rows_037]
  rfl

theorem decode_geometry_Rows_through_block_018 :
    SimplicesValue.arrayAcc019.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock018 := by
  change (SimplicesBlock018.blockPush SimplicesValue.arrayAcc018).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_018_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_017, decode_geometry_Rows_block_018]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_018_complete"
  err.flush

#print axioms geometryRow036_simplexId_read
#print axioms geometryRow036_vertexIds_read
#print axioms geometryRow036_physicalVolume_field
#print axioms geometryRow036_physicalVolume_numerator_no_slash
#print axioms geometryRow036_physicalVolume_numerator_parse
#print axioms geometryRow036_physicalVolume_denominator_parse
#print axioms geometryRow036_physicalVolume_denominator_nonzero
#print axioms geometryRow036_physicalVolume_parse
#print axioms geometryRow036_physicalVolume_read
#print axioms geometryRow036_meanGap_field
#print axioms geometryRow036_meanGap_numerator_no_slash
#print axioms geometryRow036_meanGap_numerator_parse
#print axioms geometryRow036_meanGap_denominator_parse
#print axioms geometryRow036_meanGap_denominator_nonzero
#print axioms geometryRow036_meanGap_parse
#print axioms geometryRow036_meanGap_read
#print axioms geometryRow036_jensenBound_field
#print axioms geometryRow036_jensenBound_numerator_no_slash
#print axioms geometryRow036_jensenBound_numerator_parse
#print axioms geometryRow036_jensenBound_denominator_parse
#print axioms geometryRow036_jensenBound_denominator_nonzero
#print axioms geometryRow036_jensenBound_parse
#print axioms geometryRow036_jensenBound_read
#print axioms geometryRow036_factorMaxima_read
#print axioms geometryRow036_gapWeightedMeans_read
#print axioms geometryRow036_floor_text_read
#print axioms geometryRow036_floor_chars_parse
#print axioms geometryRow036_floor_parse
#print axioms decode_geometry_Rows_036
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
#print axioms geometry_Rows_block_018_push_eq
#print axioms geometry_Rows_block_018_reverse
#print axioms decode_geometry_Rows_block_018
#print axioms decode_geometry_Rows_through_block_018

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
