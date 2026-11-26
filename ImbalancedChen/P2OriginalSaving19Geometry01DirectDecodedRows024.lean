import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows023

/-! Original simplices typed block 24, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson047 : SourceJson :=
  (SimplicesBlock024.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped047 : GeometryRow :=
  { simplexId := 47,
    vertexIds := #[39, 35, 24, 23, 21, 20, 19, 15, 0],
    physicalVolume := ((2300160002270499429498548984034229053249979 : ℚ) / (345574929296498098176000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((91924997 : ℚ) / (407826000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((14244339923633974660489 : ℚ) / (199443628357097040000000 : ℚ)), ((14305157310010555125127 : ℚ) / (199443628357097040000000 : ℚ)), ((17543255939764175798683 : ℚ) / (119666177014258224000000 : ℚ)), ((2183593870382819306857 : ℚ) / (20775377953864275000000 : ℚ)), ((166996437032904185878547 : ℚ) / (2991654425356455600000000 : ℚ)), ((143508135843974625808181 : ℚ) / (2991654425356455600000000 : ℚ)), ((6815649729464562516331 : ℚ) / (157455496071392400000000 : ℚ)), ((127899898494242251211869 : ℚ) / (2991654425356455600000000 : ℚ)), ((126311762873453022986917 : ℚ) / (2991654425356455600000000 : ℚ)), ((125974386059126541630007 : ℚ) / (2991654425356455600000000 : ℚ))],
    jensenBound := ((70197149520294614709195589272942789834014879838173612394695647554395811639807705781658347721954507992118350201944631331322021431407403674658853493852755267535505827874547208335693885157500000000000000000000000 : ℚ) / (8134176428969046053912384847475548598868377909434000597355437287391660261646156573848230853586045847785432454425177231073090578077978496485326064096198493330422952866061954031284406516776263556312519988749997635823098844089 : ℚ)),
    jensenFloorQ96 := (683731317951866 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_simplexId_before"
  err.flush

theorem geometryRow047_simplexId_read :
    geometryRowsJson047.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped047.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_vertexIds_before"
  err.flush

theorem geometryRow047_vertexIds_read :
    geometryRowsJson047.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped047.vertexIds := by decide +kernel

noncomputable def geometryRow047_physicalVolumeNumeratorChars : List Char := ['2', '3', '0', '0', '1', '6', '0', '0', '0', '2', '2', '7', '0', '4', '9', '9', '4', '2', '9', '4', '9', '8', '5', '4', '8', '9', '8', '4', '0', '3', '4', '2', '2', '9', '0', '5', '3', '2', '4', '9', '9', '7', '9']
noncomputable def geometryRow047_physicalVolumeDenominatorChars : List Char := ['3', '4', '5', '5', '7', '4', '9', '2', '9', '2', '9', '6', '4', '9', '8', '0', '9', '8', '1', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_physicalVolumeText : String := String.ofList (geometryRow047_physicalVolumeNumeratorChars ++ '/' :: geometryRow047_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_physicalVolume_before_field"
  err.flush

theorem geometryRow047_physicalVolume_field :
    geometryRowsJson047.getObjVal? "physical_volume" = .ok (.str geometryRow047_physicalVolumeText) := by rfl

theorem geometryRow047_physicalVolume_numerator_no_slash :
    geometryRow047_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeNumeratorChars = some (2300160002270499429498548984034229053249979 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeDenominatorChars = some (345574929296498098176000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_nonzero : (345574929296498098176000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_physicalVolume_parse :
    parseRational geometryRow047_physicalVolumeText = .ok geometryRowsTyped047.physicalVolume :=
  original_rational_fraction_of_chars geometryRow047_physicalVolumeNumeratorChars geometryRow047_physicalVolumeDenominatorChars
    (2300160002270499429498548984034229053249979 : Int) (345574929296498098176000000000000000000000000000000000000000000000 : Int)
    geometryRow047_physicalVolume_numerator_no_slash geometryRow047_physicalVolume_numerator_parse
    geometryRow047_physicalVolume_denominator_parse geometryRow047_physicalVolume_denominator_nonzero

theorem geometryRow047_physicalVolume_read :
    rationalField geometryRowsJson047 "physical_volume" = .ok geometryRowsTyped047.physicalVolume :=
  original_rationalField_of_string geometryRowsJson047 "physical_volume" geometryRow047_physicalVolumeText
    geometryRowsTyped047.physicalVolume geometryRow047_physicalVolume_field geometryRow047_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_physicalVolume_complete"
  err.flush

noncomputable def geometryRow047_meanGapNumeratorChars : List Char := ['9', '1', '9', '2', '4', '9', '9', '7']
noncomputable def geometryRow047_meanGapDenominatorChars : List Char := ['4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_meanGapText : String := String.ofList (geometryRow047_meanGapNumeratorChars ++ '/' :: geometryRow047_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_meanGap_before_field"
  err.flush

theorem geometryRow047_meanGap_field :
    geometryRowsJson047.getObjVal? "mean_gap" = .ok (.str geometryRow047_meanGapText) := by rfl

theorem geometryRow047_meanGap_numerator_no_slash :
    geometryRow047_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_meanGap_numerator_parse :
    SourceJson.intChars geometryRow047_meanGapNumeratorChars = some (91924997 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_parse :
    SourceJson.intChars geometryRow047_meanGapDenominatorChars = some (407826000000 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_nonzero : (407826000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_meanGap_parse :
    parseRational geometryRow047_meanGapText = .ok geometryRowsTyped047.meanGap :=
  original_rational_fraction_of_chars geometryRow047_meanGapNumeratorChars geometryRow047_meanGapDenominatorChars
    (91924997 : Int) (407826000000 : Int)
    geometryRow047_meanGap_numerator_no_slash geometryRow047_meanGap_numerator_parse
    geometryRow047_meanGap_denominator_parse geometryRow047_meanGap_denominator_nonzero

theorem geometryRow047_meanGap_read :
    rationalField geometryRowsJson047 "mean_gap" = .ok geometryRowsTyped047.meanGap :=
  original_rationalField_of_string geometryRowsJson047 "mean_gap" geometryRow047_meanGapText
    geometryRowsTyped047.meanGap geometryRow047_meanGap_field geometryRow047_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_meanGap_complete"
  err.flush

noncomputable def geometryRow047_jensenBoundNumeratorChars : List Char := ['7', '0', '1', '9', '7', '1', '4', '9', '5', '2', '0', '2', '9', '4', '6', '1', '4', '7', '0', '9', '1', '9', '5', '5', '8', '9', '2', '7', '2', '9', '4', '2', '7', '8', '9', '8', '3', '4', '0', '1', '4', '8', '7', '9', '8', '3', '8', '1', '7', '3', '6', '1', '2', '3', '9', '4', '6', '9', '5', '6', '4', '7', '5', '5', '4', '3', '9', '5', '8', '1', '1', '6', '3', '9', '8', '0', '7', '7', '0', '5', '7', '8', '1', '6', '5', '8', '3', '4', '7', '7', '2', '1', '9', '5', '4', '5', '0', '7', '9', '9', '2', '1', '1', '8', '3', '5', '0', '2', '0', '1', '9', '4', '4', '6', '3', '1', '3', '3', '1', '3', '2', '2', '0', '2', '1', '4', '3', '1', '4', '0', '7', '4', '0', '3', '6', '7', '4', '6', '5', '8', '8', '5', '3', '4', '9', '3', '8', '5', '2', '7', '5', '5', '2', '6', '7', '5', '3', '5', '5', '0', '5', '8', '2', '7', '8', '7', '4', '5', '4', '7', '2', '0', '8', '3', '3', '5', '6', '9', '3', '8', '8', '5', '1', '5', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_jensenBoundDenominatorChars : List Char := ['8', '1', '3', '4', '1', '7', '6', '4', '2', '8', '9', '6', '9', '0', '4', '6', '0', '5', '3', '9', '1', '2', '3', '8', '4', '8', '4', '7', '4', '7', '5', '5', '4', '8', '5', '9', '8', '8', '6', '8', '3', '7', '7', '9', '0', '9', '4', '3', '4', '0', '0', '0', '5', '9', '7', '3', '5', '5', '4', '3', '7', '2', '8', '7', '3', '9', '1', '6', '6', '0', '2', '6', '1', '6', '4', '6', '1', '5', '6', '5', '7', '3', '8', '4', '8', '2', '3', '0', '8', '5', '3', '5', '8', '6', '0', '4', '5', '8', '4', '7', '7', '8', '5', '4', '3', '2', '4', '5', '4', '4', '2', '5', '1', '7', '7', '2', '3', '1', '0', '7', '3', '0', '9', '0', '5', '7', '8', '0', '7', '7', '9', '7', '8', '4', '9', '6', '4', '8', '5', '3', '2', '6', '0', '6', '4', '0', '9', '6', '1', '9', '8', '4', '9', '3', '3', '3', '0', '4', '2', '2', '9', '5', '2', '8', '6', '6', '0', '6', '1', '9', '5', '4', '0', '3', '1', '2', '8', '4', '4', '0', '6', '5', '1', '6', '7', '7', '6', '2', '6', '3', '5', '5', '6', '3', '1', '2', '5', '1', '9', '9', '8', '8', '7', '4', '9', '9', '9', '7', '6', '3', '5', '8', '2', '3', '0', '9', '8', '8', '4', '4', '0', '8', '9']
noncomputable def geometryRow047_jensenBoundText : String := String.ofList (geometryRow047_jensenBoundNumeratorChars ++ '/' :: geometryRow047_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_jensenBound_before_field"
  err.flush

theorem geometryRow047_jensenBound_field :
    geometryRowsJson047.getObjVal? "jensen_bound" = .ok (.str geometryRow047_jensenBoundText) := by rfl

theorem geometryRow047_jensenBound_numerator_no_slash :
    geometryRow047_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow047_jensenBoundNumeratorChars = some (70197149520294614709195589272942789834014879838173612394695647554395811639807705781658347721954507992118350201944631331322021431407403674658853493852755267535505827874547208335693885157500000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow047_jensenBoundDenominatorChars = some (8134176428969046053912384847475548598868377909434000597355437287391660261646156573848230853586045847785432454425177231073090578077978496485326064096198493330422952866061954031284406516776263556312519988749997635823098844089 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_nonzero : (8134176428969046053912384847475548598868377909434000597355437287391660261646156573848230853586045847785432454425177231073090578077978496485326064096198493330422952866061954031284406516776263556312519988749997635823098844089 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_jensenBound_parse :
    parseRational geometryRow047_jensenBoundText = .ok geometryRowsTyped047.jensenBound :=
  original_rational_fraction_of_chars geometryRow047_jensenBoundNumeratorChars geometryRow047_jensenBoundDenominatorChars
    (70197149520294614709195589272942789834014879838173612394695647554395811639807705781658347721954507992118350201944631331322021431407403674658853493852755267535505827874547208335693885157500000000000000000000000 : Int) (8134176428969046053912384847475548598868377909434000597355437287391660261646156573848230853586045847785432454425177231073090578077978496485326064096198493330422952866061954031284406516776263556312519988749997635823098844089 : Int)
    geometryRow047_jensenBound_numerator_no_slash geometryRow047_jensenBound_numerator_parse
    geometryRow047_jensenBound_denominator_parse geometryRow047_jensenBound_denominator_nonzero

theorem geometryRow047_jensenBound_read :
    rationalField geometryRowsJson047 "jensen_bound" = .ok geometryRowsTyped047.jensenBound :=
  original_rationalField_of_string geometryRowsJson047 "jensen_bound" geometryRow047_jensenBoundText
    geometryRowsTyped047.jensenBound geometryRow047_jensenBound_field geometryRow047_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_factorMaxima_before"
  err.flush

theorem geometryRow047_factorMaxima_read :
    rationalArrayField geometryRowsJson047 "factor_maxima" = .ok geometryRowsTyped047.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_gapWeightedMeans_before"
  err.flush

theorem geometryRow047_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson047 "gap_weighted_means" = .ok geometryRowsTyped047.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow047_floorChars : List Char := ['6', '8', '3', '7', '3', '1', '3', '1', '7', '9', '5', '1', '8', '6', '6']
noncomputable def geometryRow047_floorText : String := String.ofList geometryRow047_floorChars

theorem geometryRow047_floor_text_read :
    geometryRowsJson047.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow047_floorText := by rfl

theorem geometryRow047_floor_chars_parse :
    SourceJson.intChars geometryRow047_floorChars = some (683731317951866 : Int) := by decide +kernel

theorem geometryRow047_floor_parse :
    parseInteger geometryRow047_floorText = .ok geometryRowsTyped047.jensenFloorQ96 := by
  simp only [geometryRow047_floorText, parseInteger, String.toList_ofList, geometryRow047_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_047 :
    decodeGeometryRow geometryRowsJson047 = .ok geometryRowsTyped047 :=
  original_geometryRow_of_fields geometryRowsJson047 geometryRowsTyped047 geometryRow047_floorText
    geometryRow047_simplexId_read geometryRow047_vertexIds_read
    geometryRow047_physicalVolume_read geometryRow047_meanGap_read
    geometryRow047_factorMaxima_read geometryRow047_gapWeightedMeans_read
    geometryRow047_jensenBound_read geometryRow047_floor_text_read geometryRow047_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_047_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson048 : SourceJson :=
  (SimplicesBlock024.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped048 : GeometryRow :=
  { simplexId := 48,
    vertexIds := #[39, 35, 24, 23, 21, 19, 6, 2, 0],
    physicalVolume := ((345840704122066156927137178731997571230538231 : ℚ) / (695814096445440000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((34630061 : ℚ) / (49039200000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((469079767362384420737 : ℚ) / (6017935814445800000000 : ℚ)), ((133178738751953141669 : ℚ) / (1685022028044824000000 : ℚ)), ((6842585317890540262133 : ℚ) / (47391244538760675000000 : ℚ)), ((6859997629768945081463 : ℚ) / (63188326051680900000000 : ℚ)), ((22295169449247554750927 : ℚ) / (379129956310085400000000 : ℚ)), ((2269084226840147849767 : ℚ) / (47391244538760675000000 : ℚ)), ((811841002482271222999 : ℚ) / (19954208226846600000000 : ℚ)), ((15222535955588640855451 : ℚ) / (379129956310085400000000 : ℚ)), ((7527883813267480598279 : ℚ) / (189564978155042700000000 : ℚ)), ((7203918387570874258637 : ℚ) / (189564978155042700000000 : ℚ))],
    jensenBound := ((7200830825232860428147176255972412577544710039417418303703663819626831952903752728088531699792592167630243184261388691741564524153873077380640804107555265758574179951687414288048905273437500000000000 : ℚ) / (3437981937171988346294649968714331456021829196594946752412255751365443090440641977251528620596964967386823374746185271235534574815955537224376514510504615487471233213818710616586261854846909738818013186342628239 : ℚ)),
    jensenFloorQ96 := (165942871511582641 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_simplexId_before"
  err.flush

theorem geometryRow048_simplexId_read :
    geometryRowsJson048.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped048.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_vertexIds_before"
  err.flush

theorem geometryRow048_vertexIds_read :
    geometryRowsJson048.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped048.vertexIds := by decide +kernel

noncomputable def geometryRow048_physicalVolumeNumeratorChars : List Char := ['3', '4', '5', '8', '4', '0', '7', '0', '4', '1', '2', '2', '0', '6', '6', '1', '5', '6', '9', '2', '7', '1', '3', '7', '1', '7', '8', '7', '3', '1', '9', '9', '7', '5', '7', '1', '2', '3', '0', '5', '3', '8', '2', '3', '1']
noncomputable def geometryRow048_physicalVolumeDenominatorChars : List Char := ['6', '9', '5', '8', '1', '4', '0', '9', '6', '4', '4', '5', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_physicalVolumeText : String := String.ofList (geometryRow048_physicalVolumeNumeratorChars ++ '/' :: geometryRow048_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_physicalVolume_before_field"
  err.flush

theorem geometryRow048_physicalVolume_field :
    geometryRowsJson048.getObjVal? "physical_volume" = .ok (.str geometryRow048_physicalVolumeText) := by rfl

theorem geometryRow048_physicalVolume_numerator_no_slash :
    geometryRow048_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeNumeratorChars = some (345840704122066156927137178731997571230538231 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeDenominatorChars = some (695814096445440000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_nonzero : (695814096445440000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_physicalVolume_parse :
    parseRational geometryRow048_physicalVolumeText = .ok geometryRowsTyped048.physicalVolume :=
  original_rational_fraction_of_chars geometryRow048_physicalVolumeNumeratorChars geometryRow048_physicalVolumeDenominatorChars
    (345840704122066156927137178731997571230538231 : Int) (695814096445440000000000000000000000000000000000000000000000000000 : Int)
    geometryRow048_physicalVolume_numerator_no_slash geometryRow048_physicalVolume_numerator_parse
    geometryRow048_physicalVolume_denominator_parse geometryRow048_physicalVolume_denominator_nonzero

theorem geometryRow048_physicalVolume_read :
    rationalField geometryRowsJson048 "physical_volume" = .ok geometryRowsTyped048.physicalVolume :=
  original_rationalField_of_string geometryRowsJson048 "physical_volume" geometryRow048_physicalVolumeText
    geometryRowsTyped048.physicalVolume geometryRow048_physicalVolume_field geometryRow048_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_physicalVolume_complete"
  err.flush

noncomputable def geometryRow048_meanGapNumeratorChars : List Char := ['3', '4', '6', '3', '0', '0', '6', '1']
noncomputable def geometryRow048_meanGapDenominatorChars : List Char := ['4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_meanGapText : String := String.ofList (geometryRow048_meanGapNumeratorChars ++ '/' :: geometryRow048_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_meanGap_before_field"
  err.flush

theorem geometryRow048_meanGap_field :
    geometryRowsJson048.getObjVal? "mean_gap" = .ok (.str geometryRow048_meanGapText) := by rfl

theorem geometryRow048_meanGap_numerator_no_slash :
    geometryRow048_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_meanGap_numerator_parse :
    SourceJson.intChars geometryRow048_meanGapNumeratorChars = some (34630061 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_parse :
    SourceJson.intChars geometryRow048_meanGapDenominatorChars = some (49039200000 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_nonzero : (49039200000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_meanGap_parse :
    parseRational geometryRow048_meanGapText = .ok geometryRowsTyped048.meanGap :=
  original_rational_fraction_of_chars geometryRow048_meanGapNumeratorChars geometryRow048_meanGapDenominatorChars
    (34630061 : Int) (49039200000 : Int)
    geometryRow048_meanGap_numerator_no_slash geometryRow048_meanGap_numerator_parse
    geometryRow048_meanGap_denominator_parse geometryRow048_meanGap_denominator_nonzero

theorem geometryRow048_meanGap_read :
    rationalField geometryRowsJson048 "mean_gap" = .ok geometryRowsTyped048.meanGap :=
  original_rationalField_of_string geometryRowsJson048 "mean_gap" geometryRow048_meanGapText
    geometryRowsTyped048.meanGap geometryRow048_meanGap_field geometryRow048_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_meanGap_complete"
  err.flush

noncomputable def geometryRow048_jensenBoundNumeratorChars : List Char := ['7', '2', '0', '0', '8', '3', '0', '8', '2', '5', '2', '3', '2', '8', '6', '0', '4', '2', '8', '1', '4', '7', '1', '7', '6', '2', '5', '5', '9', '7', '2', '4', '1', '2', '5', '7', '7', '5', '4', '4', '7', '1', '0', '0', '3', '9', '4', '1', '7', '4', '1', '8', '3', '0', '3', '7', '0', '3', '6', '6', '3', '8', '1', '9', '6', '2', '6', '8', '3', '1', '9', '5', '2', '9', '0', '3', '7', '5', '2', '7', '2', '8', '0', '8', '8', '5', '3', '1', '6', '9', '9', '7', '9', '2', '5', '9', '2', '1', '6', '7', '6', '3', '0', '2', '4', '3', '1', '8', '4', '2', '6', '1', '3', '8', '8', '6', '9', '1', '7', '4', '1', '5', '6', '4', '5', '2', '4', '1', '5', '3', '8', '7', '3', '0', '7', '7', '3', '8', '0', '6', '4', '0', '8', '0', '4', '1', '0', '7', '5', '5', '5', '2', '6', '5', '7', '5', '8', '5', '7', '4', '1', '7', '9', '9', '5', '1', '6', '8', '7', '4', '1', '4', '2', '8', '8', '0', '4', '8', '9', '0', '5', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_jensenBoundDenominatorChars : List Char := ['3', '4', '3', '7', '9', '8', '1', '9', '3', '7', '1', '7', '1', '9', '8', '8', '3', '4', '6', '2', '9', '4', '6', '4', '9', '9', '6', '8', '7', '1', '4', '3', '3', '1', '4', '5', '6', '0', '2', '1', '8', '2', '9', '1', '9', '6', '5', '9', '4', '9', '4', '6', '7', '5', '2', '4', '1', '2', '2', '5', '5', '7', '5', '1', '3', '6', '5', '4', '4', '3', '0', '9', '0', '4', '4', '0', '6', '4', '1', '9', '7', '7', '2', '5', '1', '5', '2', '8', '6', '2', '0', '5', '9', '6', '9', '6', '4', '9', '6', '7', '3', '8', '6', '8', '2', '3', '3', '7', '4', '7', '4', '6', '1', '8', '5', '2', '7', '1', '2', '3', '5', '5', '3', '4', '5', '7', '4', '8', '1', '5', '9', '5', '5', '5', '3', '7', '2', '2', '4', '3', '7', '6', '5', '1', '4', '5', '1', '0', '5', '0', '4', '6', '1', '5', '4', '8', '7', '4', '7', '1', '2', '3', '3', '2', '1', '3', '8', '1', '8', '7', '1', '0', '6', '1', '6', '5', '8', '6', '2', '6', '1', '8', '5', '4', '8', '4', '6', '9', '0', '9', '7', '3', '8', '8', '1', '8', '0', '1', '3', '1', '8', '6', '3', '4', '2', '6', '2', '8', '2', '3', '9']
noncomputable def geometryRow048_jensenBoundText : String := String.ofList (geometryRow048_jensenBoundNumeratorChars ++ '/' :: geometryRow048_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_jensenBound_before_field"
  err.flush

theorem geometryRow048_jensenBound_field :
    geometryRowsJson048.getObjVal? "jensen_bound" = .ok (.str geometryRow048_jensenBoundText) := by rfl

theorem geometryRow048_jensenBound_numerator_no_slash :
    geometryRow048_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow048_jensenBoundNumeratorChars = some (7200830825232860428147176255972412577544710039417418303703663819626831952903752728088531699792592167630243184261388691741564524153873077380640804107555265758574179951687414288048905273437500000000000 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow048_jensenBoundDenominatorChars = some (3437981937171988346294649968714331456021829196594946752412255751365443090440641977251528620596964967386823374746185271235534574815955537224376514510504615487471233213818710616586261854846909738818013186342628239 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_nonzero : (3437981937171988346294649968714331456021829196594946752412255751365443090440641977251528620596964967386823374746185271235534574815955537224376514510504615487471233213818710616586261854846909738818013186342628239 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_jensenBound_parse :
    parseRational geometryRow048_jensenBoundText = .ok geometryRowsTyped048.jensenBound :=
  original_rational_fraction_of_chars geometryRow048_jensenBoundNumeratorChars geometryRow048_jensenBoundDenominatorChars
    (7200830825232860428147176255972412577544710039417418303703663819626831952903752728088531699792592167630243184261388691741564524153873077380640804107555265758574179951687414288048905273437500000000000 : Int) (3437981937171988346294649968714331456021829196594946752412255751365443090440641977251528620596964967386823374746185271235534574815955537224376514510504615487471233213818710616586261854846909738818013186342628239 : Int)
    geometryRow048_jensenBound_numerator_no_slash geometryRow048_jensenBound_numerator_parse
    geometryRow048_jensenBound_denominator_parse geometryRow048_jensenBound_denominator_nonzero

theorem geometryRow048_jensenBound_read :
    rationalField geometryRowsJson048 "jensen_bound" = .ok geometryRowsTyped048.jensenBound :=
  original_rationalField_of_string geometryRowsJson048 "jensen_bound" geometryRow048_jensenBoundText
    geometryRowsTyped048.jensenBound geometryRow048_jensenBound_field geometryRow048_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_factorMaxima_before"
  err.flush

theorem geometryRow048_factorMaxima_read :
    rationalArrayField geometryRowsJson048 "factor_maxima" = .ok geometryRowsTyped048.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_gapWeightedMeans_before"
  err.flush

theorem geometryRow048_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson048 "gap_weighted_means" = .ok geometryRowsTyped048.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow048_floorChars : List Char := ['1', '6', '5', '9', '4', '2', '8', '7', '1', '5', '1', '1', '5', '8', '2', '6', '4', '1']
noncomputable def geometryRow048_floorText : String := String.ofList geometryRow048_floorChars

theorem geometryRow048_floor_text_read :
    geometryRowsJson048.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow048_floorText := by rfl

theorem geometryRow048_floor_chars_parse :
    SourceJson.intChars geometryRow048_floorChars = some (165942871511582641 : Int) := by decide +kernel

theorem geometryRow048_floor_parse :
    parseInteger geometryRow048_floorText = .ok geometryRowsTyped048.jensenFloorQ96 := by
  simp only [geometryRow048_floorText, parseInteger, String.toList_ofList, geometryRow048_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_048 :
    decodeGeometryRow geometryRowsJson048 = .ok geometryRowsTyped048 :=
  original_geometryRow_of_fields geometryRowsJson048 geometryRowsTyped048 geometryRow048_floorText
    geometryRow048_simplexId_read geometryRow048_vertexIds_read
    geometryRow048_physicalVolume_read geometryRow048_meanGap_read
    geometryRow048_factorMaxima_read geometryRow048_gapWeightedMeans_read
    geometryRow048_jensenBound_read geometryRow048_floor_text_read geometryRow048_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_048_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock024 : List SourceJson := [geometryRowsJson047, geometryRowsJson048]
noncomputable def geometryRowsTypedBlock024 : List (GeometryRow) := [geometryRowsTyped047, geometryRowsTyped048]
noncomputable def geometryRowsTypedThroughBlock024 : List (GeometryRow) := geometryRowsTypedThroughBlock023 ++ geometryRowsTypedBlock024

theorem geometry_Rows_block_024_push_eq (acc : List SourceJson) :
    SimplicesBlock024.blockPush acc = [geometryRowsJson048, geometryRowsJson047] ++ acc := by rfl

theorem geometry_Rows_block_024_reverse (acc : List SourceJson) :
    (SimplicesBlock024.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock024 := by
  rw [geometry_Rows_block_024_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_024 :
    geometryRowsJsonBlock024.mapM decodeGeometryRow = .ok geometryRowsTypedBlock024 := by
  simp only [geometryRowsJsonBlock024, geometryRowsTypedBlock024, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_047, decode_geometry_Rows_048]
  rfl

theorem decode_geometry_Rows_through_block_024 :
    SimplicesValue.arrayAcc025.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock024 := by
  change (SimplicesBlock024.blockPush SimplicesValue.arrayAcc024).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_024_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_023, decode_geometry_Rows_block_024]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_024_complete"
  err.flush

#print axioms geometryRow047_simplexId_read
#print axioms geometryRow047_vertexIds_read
#print axioms geometryRow047_physicalVolume_field
#print axioms geometryRow047_physicalVolume_numerator_no_slash
#print axioms geometryRow047_physicalVolume_numerator_parse
#print axioms geometryRow047_physicalVolume_denominator_parse
#print axioms geometryRow047_physicalVolume_denominator_nonzero
#print axioms geometryRow047_physicalVolume_parse
#print axioms geometryRow047_physicalVolume_read
#print axioms geometryRow047_meanGap_field
#print axioms geometryRow047_meanGap_numerator_no_slash
#print axioms geometryRow047_meanGap_numerator_parse
#print axioms geometryRow047_meanGap_denominator_parse
#print axioms geometryRow047_meanGap_denominator_nonzero
#print axioms geometryRow047_meanGap_parse
#print axioms geometryRow047_meanGap_read
#print axioms geometryRow047_jensenBound_field
#print axioms geometryRow047_jensenBound_numerator_no_slash
#print axioms geometryRow047_jensenBound_numerator_parse
#print axioms geometryRow047_jensenBound_denominator_parse
#print axioms geometryRow047_jensenBound_denominator_nonzero
#print axioms geometryRow047_jensenBound_parse
#print axioms geometryRow047_jensenBound_read
#print axioms geometryRow047_factorMaxima_read
#print axioms geometryRow047_gapWeightedMeans_read
#print axioms geometryRow047_floor_text_read
#print axioms geometryRow047_floor_chars_parse
#print axioms geometryRow047_floor_parse
#print axioms decode_geometry_Rows_047
#print axioms geometryRow048_simplexId_read
#print axioms geometryRow048_vertexIds_read
#print axioms geometryRow048_physicalVolume_field
#print axioms geometryRow048_physicalVolume_numerator_no_slash
#print axioms geometryRow048_physicalVolume_numerator_parse
#print axioms geometryRow048_physicalVolume_denominator_parse
#print axioms geometryRow048_physicalVolume_denominator_nonzero
#print axioms geometryRow048_physicalVolume_parse
#print axioms geometryRow048_physicalVolume_read
#print axioms geometryRow048_meanGap_field
#print axioms geometryRow048_meanGap_numerator_no_slash
#print axioms geometryRow048_meanGap_numerator_parse
#print axioms geometryRow048_meanGap_denominator_parse
#print axioms geometryRow048_meanGap_denominator_nonzero
#print axioms geometryRow048_meanGap_parse
#print axioms geometryRow048_meanGap_read
#print axioms geometryRow048_jensenBound_field
#print axioms geometryRow048_jensenBound_numerator_no_slash
#print axioms geometryRow048_jensenBound_numerator_parse
#print axioms geometryRow048_jensenBound_denominator_parse
#print axioms geometryRow048_jensenBound_denominator_nonzero
#print axioms geometryRow048_jensenBound_parse
#print axioms geometryRow048_jensenBound_read
#print axioms geometryRow048_factorMaxima_read
#print axioms geometryRow048_gapWeightedMeans_read
#print axioms geometryRow048_floor_text_read
#print axioms geometryRow048_floor_chars_parse
#print axioms geometryRow048_floor_parse
#print axioms decode_geometry_Rows_048
#print axioms geometry_Rows_block_024_push_eq
#print axioms geometry_Rows_block_024_reverse
#print axioms decode_geometry_Rows_block_024
#print axioms decode_geometry_Rows_through_block_024

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
