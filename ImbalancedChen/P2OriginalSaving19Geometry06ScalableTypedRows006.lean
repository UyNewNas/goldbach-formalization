import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock006

/-! Local typed certificates for original cell 06, rows 48 through 55.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson048 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped048 : GeometryRow :=
  { simplexId := 48,
    vertexIds := #[32, 30, 28, 16, 14, 13, 4, 1, 0],
    physicalVolume := ((40661449873921838071275448878615067982143 : ℚ) / (6484925070086400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((105487333353193579604519237 : ℚ) / (1182409062560002292400000000 : ℚ)), ((360847519329066068084141 : ℚ) / (3928269310830572400000000 : ℚ)), ((2395514057058763917705743 : ℚ) / (20563635870608735520000000 : ℚ)), ((71315920835663107875031469 : ℚ) / (788272708373334861600000000 : ℚ)), ((23629187340563629124350543 : ℚ) / (262757569457778287200000000 : ℚ)), ((15594305452970857117431089 : ℚ) / (214983465920000416800000000 : ℚ)), ((3801408850531028349687191 : ℚ) / (107491732960000208400000000 : ℚ)), ((3777327808703623261763861 : ℚ) / (107491732960000208400000000 : ℚ)), ((3660401770715099004789701 : ℚ) / (107491732960000208400000000 : ℚ)), ((123010238455880389494127 : ℚ) / (3928269310830572400000000 : ℚ))],
    jensenBound := ((26679472627804963646865958155549668628760749526091175074567581546225370206204302798044881920461083731265565418847813972185134526965763310950899959219443068016693289082312890600650838364770158886108145468508733440000000000000000000000 : ℚ) / (360292230600827744564846554648638175240027422582029826337757553535911047054049437928895949757605941041609135044979982422959325070785223927810013241354346592650049191690740564657649247783985556638141277100159145046930320312328951122345215025222967 : ℚ)),
    jensenFloorQ96 := (5866808700330998 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_simplexId_before"
  err.flush

theorem geometryRow048_simplexId_read :
    geometryRowsJson048.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped048.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_vertexIds_before"
  err.flush

theorem geometryRow048_vertexIds_read :
    geometryRowsJson048.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped048.vertexIds := by decide +kernel

noncomputable def geometryRow048_physicalVolumeNumeratorChars : List Char := ['4', '0', '6', '6', '1', '4', '4', '9', '8', '7', '3', '9', '2', '1', '8', '3', '8', '0', '7', '1', '2', '7', '5', '4', '4', '8', '8', '7', '8', '6', '1', '5', '0', '6', '7', '9', '8', '2', '1', '4', '3']
noncomputable def geometryRow048_physicalVolumeDenominatorChars : List Char := ['6', '4', '8', '4', '9', '2', '5', '0', '7', '0', '0', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_physicalVolumeText : String := String.ofList (geometryRow048_physicalVolumeNumeratorChars ++ '/' :: geometryRow048_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_physicalVolume_before_field"
  err.flush

theorem geometryRow048_physicalVolume_field :
    geometryRowsJson048.getObjVal? "physical_volume" = .ok (.str geometryRow048_physicalVolumeText) := by rfl

theorem geometryRow048_physicalVolume_numerator_no_slash :
    geometryRow048_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeNumeratorChars = some (40661449873921838071275448878615067982143 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeDenominatorChars = some (6484925070086400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_nonzero : (6484925070086400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_physicalVolume_parse :
    parseRational geometryRow048_physicalVolumeText = .ok geometryRowsTyped048.physicalVolume :=
  original_rational_fraction_of_chars geometryRow048_physicalVolumeNumeratorChars geometryRow048_physicalVolumeDenominatorChars
    (40661449873921838071275448878615067982143 : Int) (6484925070086400000000000000000000000000000000000000000000000000 : Int)
    geometryRow048_physicalVolume_numerator_no_slash geometryRow048_physicalVolume_numerator_parse
    geometryRow048_physicalVolume_denominator_parse geometryRow048_physicalVolume_denominator_nonzero

theorem geometryRow048_physicalVolume_read :
    rationalField geometryRowsJson048 "physical_volume" = .ok geometryRowsTyped048.physicalVolume :=
  original_rationalField_of_string geometryRowsJson048 "physical_volume" geometryRow048_physicalVolumeText
    geometryRowsTyped048.physicalVolume geometryRow048_physicalVolume_field geometryRow048_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_physicalVolume_complete"
  err.flush

noncomputable def geometryRow048_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow048_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_meanGapText : String := String.ofList (geometryRow048_meanGapNumeratorChars ++ '/' :: geometryRow048_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_meanGap_before_field"
  err.flush

theorem geometryRow048_meanGap_field :
    geometryRowsJson048.getObjVal? "mean_gap" = .ok (.str geometryRow048_meanGapText) := by rfl

theorem geometryRow048_meanGap_numerator_no_slash :
    geometryRow048_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_meanGap_numerator_parse :
    SourceJson.intChars geometryRow048_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_parse :
    SourceJson.intChars geometryRow048_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_meanGap_parse :
    parseRational geometryRow048_meanGapText = .ok geometryRowsTyped048.meanGap :=
  original_rational_fraction_of_chars geometryRow048_meanGapNumeratorChars geometryRow048_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow048_meanGap_numerator_no_slash geometryRow048_meanGap_numerator_parse
    geometryRow048_meanGap_denominator_parse geometryRow048_meanGap_denominator_nonzero

theorem geometryRow048_meanGap_read :
    rationalField geometryRowsJson048 "mean_gap" = .ok geometryRowsTyped048.meanGap :=
  original_rationalField_of_string geometryRowsJson048 "mean_gap" geometryRow048_meanGapText
    geometryRowsTyped048.meanGap geometryRow048_meanGap_field geometryRow048_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_meanGap_complete"
  err.flush

noncomputable def geometryRow048_jensenBoundNumeratorChars : List Char := ['2', '6', '6', '7', '9', '4', '7', '2', '6', '2', '7', '8', '0', '4', '9', '6', '3', '6', '4', '6', '8', '6', '5', '9', '5', '8', '1', '5', '5', '5', '4', '9', '6', '6', '8', '6', '2', '8', '7', '6', '0', '7', '4', '9', '5', '2', '6', '0', '9', '1', '1', '7', '5', '0', '7', '4', '5', '6', '7', '5', '8', '1', '5', '4', '6', '2', '2', '5', '3', '7', '0', '2', '0', '6', '2', '0', '4', '3', '0', '2', '7', '9', '8', '0', '4', '4', '8', '8', '1', '9', '2', '0', '4', '6', '1', '0', '8', '3', '7', '3', '1', '2', '6', '5', '5', '6', '5', '4', '1', '8', '8', '4', '7', '8', '1', '3', '9', '7', '2', '1', '8', '5', '1', '3', '4', '5', '2', '6', '9', '6', '5', '7', '6', '3', '3', '1', '0', '9', '5', '0', '8', '9', '9', '9', '5', '9', '2', '1', '9', '4', '4', '3', '0', '6', '8', '0', '1', '6', '6', '9', '3', '2', '8', '9', '0', '8', '2', '3', '1', '2', '8', '9', '0', '6', '0', '0', '6', '5', '0', '8', '3', '8', '3', '6', '4', '7', '7', '0', '1', '5', '8', '8', '8', '6', '1', '0', '8', '1', '4', '5', '4', '6', '8', '5', '0', '8', '7', '3', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_jensenBoundDenominatorChars : List Char := ['3', '6', '0', '2', '9', '2', '2', '3', '0', '6', '0', '0', '8', '2', '7', '7', '4', '4', '5', '6', '4', '8', '4', '6', '5', '5', '4', '6', '4', '8', '6', '3', '8', '1', '7', '5', '2', '4', '0', '0', '2', '7', '4', '2', '2', '5', '8', '2', '0', '2', '9', '8', '2', '6', '3', '3', '7', '7', '5', '7', '5', '5', '3', '5', '3', '5', '9', '1', '1', '0', '4', '7', '0', '5', '4', '0', '4', '9', '4', '3', '7', '9', '2', '8', '8', '9', '5', '9', '4', '9', '7', '5', '7', '6', '0', '5', '9', '4', '1', '0', '4', '1', '6', '0', '9', '1', '3', '5', '0', '4', '4', '9', '7', '9', '9', '8', '2', '4', '2', '2', '9', '5', '9', '3', '2', '5', '0', '7', '0', '7', '8', '5', '2', '2', '3', '9', '2', '7', '8', '1', '0', '0', '1', '3', '2', '4', '1', '3', '5', '4', '3', '4', '6', '5', '9', '2', '6', '5', '0', '0', '4', '9', '1', '9', '1', '6', '9', '0', '7', '4', '0', '5', '6', '4', '6', '5', '7', '6', '4', '9', '2', '4', '7', '7', '8', '3', '9', '8', '5', '5', '5', '6', '6', '3', '8', '1', '4', '1', '2', '7', '7', '1', '0', '0', '1', '5', '9', '1', '4', '5', '0', '4', '6', '9', '3', '0', '3', '2', '0', '3', '1', '2', '3', '2', '8', '9', '5', '1', '1', '2', '2', '3', '4', '5', '2', '1', '5', '0', '2', '5', '2', '2', '2', '9', '6', '7']
noncomputable def geometryRow048_jensenBoundText : String := String.ofList (geometryRow048_jensenBoundNumeratorChars ++ '/' :: geometryRow048_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_jensenBound_before_field"
  err.flush

theorem geometryRow048_jensenBound_field :
    geometryRowsJson048.getObjVal? "jensen_bound" = .ok (.str geometryRow048_jensenBoundText) := by rfl

theorem geometryRow048_jensenBound_numerator_no_slash :
    geometryRow048_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow048_jensenBoundNumeratorChars = some (26679472627804963646865958155549668628760749526091175074567581546225370206204302798044881920461083731265565418847813972185134526965763310950899959219443068016693289082312890600650838364770158886108145468508733440000000000000000000000 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow048_jensenBoundDenominatorChars = some (360292230600827744564846554648638175240027422582029826337757553535911047054049437928895949757605941041609135044979982422959325070785223927810013241354346592650049191690740564657649247783985556638141277100159145046930320312328951122345215025222967 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_nonzero : (360292230600827744564846554648638175240027422582029826337757553535911047054049437928895949757605941041609135044979982422959325070785223927810013241354346592650049191690740564657649247783985556638141277100159145046930320312328951122345215025222967 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_jensenBound_parse :
    parseRational geometryRow048_jensenBoundText = .ok geometryRowsTyped048.jensenBound :=
  original_rational_fraction_of_chars geometryRow048_jensenBoundNumeratorChars geometryRow048_jensenBoundDenominatorChars
    (26679472627804963646865958155549668628760749526091175074567581546225370206204302798044881920461083731265565418847813972185134526965763310950899959219443068016693289082312890600650838364770158886108145468508733440000000000000000000000 : Int) (360292230600827744564846554648638175240027422582029826337757553535911047054049437928895949757605941041609135044979982422959325070785223927810013241354346592650049191690740564657649247783985556638141277100159145046930320312328951122345215025222967 : Int)
    geometryRow048_jensenBound_numerator_no_slash geometryRow048_jensenBound_numerator_parse
    geometryRow048_jensenBound_denominator_parse geometryRow048_jensenBound_denominator_nonzero

theorem geometryRow048_jensenBound_read :
    rationalField geometryRowsJson048 "jensen_bound" = .ok geometryRowsTyped048.jensenBound :=
  original_rationalField_of_string geometryRowsJson048 "jensen_bound" geometryRow048_jensenBoundText
    geometryRowsTyped048.jensenBound geometryRow048_jensenBound_field geometryRow048_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_factorMaxima_before"
  err.flush

theorem geometryRow048_factorMaxima_read :
    rationalArrayField geometryRowsJson048 "factor_maxima" = .ok geometryRowsTyped048.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_gapWeightedMeans_before"
  err.flush

theorem geometryRow048_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson048 "gap_weighted_means" = .ok geometryRowsTyped048.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow048_floorChars : List Char := ['5', '8', '6', '6', '8', '0', '8', '7', '0', '0', '3', '3', '0', '9', '9', '8']
noncomputable def geometryRow048_floorText : String := String.ofList geometryRow048_floorChars

theorem geometryRow048_floor_text_read :
    geometryRowsJson048.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow048_floorText := by rfl

theorem geometryRow048_floor_chars_parse :
    SourceJson.intChars geometryRow048_floorChars = some (5866808700330998 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_048_original_decoder_complete"
  err.flush

theorem geometryRow048_shape :
    geometryRowsTyped048.simplexId = 48 ∧
    geometryRowsTyped048.vertexIds.size = 9 ∧ geometryRowsTyped048.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped048.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped048.factorMaxima.size = 10 ∧ geometryRowsTyped048.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson049 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped049 : GeometryRow :=
  { simplexId := 49,
    vertexIds := #[32, 30, 28, 16, 14, 13, 10, 1, 0],
    physicalVolume := ((2912300047056675578570102402892802538626867 : ℚ) / (38909550420518400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((38514957739180596370693 : ℚ) / (428690437344615600000000 : ℚ)), ((5624309746456716127567 : ℚ) / (61241491049230800000000 : ℚ)), ((871626053128738303171 : ℚ) / (7455485866862880000000 : ℚ)), ((8535269046819624773387 : ℚ) / (95264541632136800000000 : ℚ)), ((25450502742753572207201 : ℚ) / (285793624896410400000000 : ℚ)), ((5728271000209854574501 : ℚ) / (77943715880839200000000 : ℚ)), ((1435435292081325806689 : ℚ) / (38971857940419600000000 : ℚ)), ((1349511979213764303829 : ℚ) / (38971857940419600000000 : ℚ)), ((1307119649901141190789 : ℚ) / (38971857940419600000000 : ℚ)), ((1917295099588809032549 : ℚ) / (61241491049230800000000 : ℚ))],
    jensenBound := ((26340643308218526251965716426376394878856670652289908542566709696200204923730546239500094201827560557152021263934783603280222103441046036644126675256897487073386763733435474247680000000000000000000000 : ℚ) / (45102333208781614359641142165217737482853873569384442444654628903202193373406712518025339086624378077880170604365582213021640201738669505745057641132931960032630996546967587544035561740715160342382438431282522003 : ℚ)),
    jensenFloorQ96 := (46270793998468233 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_simplexId_before"
  err.flush

theorem geometryRow049_simplexId_read :
    geometryRowsJson049.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped049.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_vertexIds_before"
  err.flush

theorem geometryRow049_vertexIds_read :
    geometryRowsJson049.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped049.vertexIds := by decide +kernel

noncomputable def geometryRow049_physicalVolumeNumeratorChars : List Char := ['2', '9', '1', '2', '3', '0', '0', '0', '4', '7', '0', '5', '6', '6', '7', '5', '5', '7', '8', '5', '7', '0', '1', '0', '2', '4', '0', '2', '8', '9', '2', '8', '0', '2', '5', '3', '8', '6', '2', '6', '8', '6', '7']
noncomputable def geometryRow049_physicalVolumeDenominatorChars : List Char := ['3', '8', '9', '0', '9', '5', '5', '0', '4', '2', '0', '5', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_physicalVolumeText : String := String.ofList (geometryRow049_physicalVolumeNumeratorChars ++ '/' :: geometryRow049_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_physicalVolume_before_field"
  err.flush

theorem geometryRow049_physicalVolume_field :
    geometryRowsJson049.getObjVal? "physical_volume" = .ok (.str geometryRow049_physicalVolumeText) := by rfl

theorem geometryRow049_physicalVolume_numerator_no_slash :
    geometryRow049_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeNumeratorChars = some (2912300047056675578570102402892802538626867 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeDenominatorChars = some (38909550420518400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_nonzero : (38909550420518400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_physicalVolume_parse :
    parseRational geometryRow049_physicalVolumeText = .ok geometryRowsTyped049.physicalVolume :=
  original_rational_fraction_of_chars geometryRow049_physicalVolumeNumeratorChars geometryRow049_physicalVolumeDenominatorChars
    (2912300047056675578570102402892802538626867 : Int) (38909550420518400000000000000000000000000000000000000000000000000 : Int)
    geometryRow049_physicalVolume_numerator_no_slash geometryRow049_physicalVolume_numerator_parse
    geometryRow049_physicalVolume_denominator_parse geometryRow049_physicalVolume_denominator_nonzero

theorem geometryRow049_physicalVolume_read :
    rationalField geometryRowsJson049 "physical_volume" = .ok geometryRowsTyped049.physicalVolume :=
  original_rationalField_of_string geometryRowsJson049 "physical_volume" geometryRow049_physicalVolumeText
    geometryRowsTyped049.physicalVolume geometryRow049_physicalVolume_field geometryRow049_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_physicalVolume_complete"
  err.flush

noncomputable def geometryRow049_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow049_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_meanGapText : String := String.ofList (geometryRow049_meanGapNumeratorChars ++ '/' :: geometryRow049_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_meanGap_before_field"
  err.flush

theorem geometryRow049_meanGap_field :
    geometryRowsJson049.getObjVal? "mean_gap" = .ok (.str geometryRow049_meanGapText) := by rfl

theorem geometryRow049_meanGap_numerator_no_slash :
    geometryRow049_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_meanGap_numerator_parse :
    SourceJson.intChars geometryRow049_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_parse :
    SourceJson.intChars geometryRow049_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_meanGap_parse :
    parseRational geometryRow049_meanGapText = .ok geometryRowsTyped049.meanGap :=
  original_rational_fraction_of_chars geometryRow049_meanGapNumeratorChars geometryRow049_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow049_meanGap_numerator_no_slash geometryRow049_meanGap_numerator_parse
    geometryRow049_meanGap_denominator_parse geometryRow049_meanGap_denominator_nonzero

theorem geometryRow049_meanGap_read :
    rationalField geometryRowsJson049 "mean_gap" = .ok geometryRowsTyped049.meanGap :=
  original_rationalField_of_string geometryRowsJson049 "mean_gap" geometryRow049_meanGapText
    geometryRowsTyped049.meanGap geometryRow049_meanGap_field geometryRow049_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_meanGap_complete"
  err.flush

noncomputable def geometryRow049_jensenBoundNumeratorChars : List Char := ['2', '6', '3', '4', '0', '6', '4', '3', '3', '0', '8', '2', '1', '8', '5', '2', '6', '2', '5', '1', '9', '6', '5', '7', '1', '6', '4', '2', '6', '3', '7', '6', '3', '9', '4', '8', '7', '8', '8', '5', '6', '6', '7', '0', '6', '5', '2', '2', '8', '9', '9', '0', '8', '5', '4', '2', '5', '6', '6', '7', '0', '9', '6', '9', '6', '2', '0', '0', '2', '0', '4', '9', '2', '3', '7', '3', '0', '5', '4', '6', '2', '3', '9', '5', '0', '0', '0', '9', '4', '2', '0', '1', '8', '2', '7', '5', '6', '0', '5', '5', '7', '1', '5', '2', '0', '2', '1', '2', '6', '3', '9', '3', '4', '7', '8', '3', '6', '0', '3', '2', '8', '0', '2', '2', '2', '1', '0', '3', '4', '4', '1', '0', '4', '6', '0', '3', '6', '6', '4', '4', '1', '2', '6', '6', '7', '5', '2', '5', '6', '8', '9', '7', '4', '8', '7', '0', '7', '3', '3', '8', '6', '7', '6', '3', '7', '3', '3', '4', '3', '5', '4', '7', '4', '2', '4', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_jensenBoundDenominatorChars : List Char := ['4', '5', '1', '0', '2', '3', '3', '3', '2', '0', '8', '7', '8', '1', '6', '1', '4', '3', '5', '9', '6', '4', '1', '1', '4', '2', '1', '6', '5', '2', '1', '7', '7', '3', '7', '4', '8', '2', '8', '5', '3', '8', '7', '3', '5', '6', '9', '3', '8', '4', '4', '4', '2', '4', '4', '4', '6', '5', '4', '6', '2', '8', '9', '0', '3', '2', '0', '2', '1', '9', '3', '3', '7', '3', '4', '0', '6', '7', '1', '2', '5', '1', '8', '0', '2', '5', '3', '3', '9', '0', '8', '6', '6', '2', '4', '3', '7', '8', '0', '7', '7', '8', '8', '0', '1', '7', '0', '6', '0', '4', '3', '6', '5', '5', '8', '2', '2', '1', '3', '0', '2', '1', '6', '4', '0', '2', '0', '1', '7', '3', '8', '6', '6', '9', '5', '0', '5', '7', '4', '5', '0', '5', '7', '6', '4', '1', '1', '3', '2', '9', '3', '1', '9', '6', '0', '0', '3', '2', '6', '3', '0', '9', '9', '6', '5', '4', '6', '9', '6', '7', '5', '8', '7', '5', '4', '4', '0', '3', '5', '5', '6', '1', '7', '4', '0', '7', '1', '5', '1', '6', '0', '3', '4', '2', '3', '8', '2', '4', '3', '8', '4', '3', '1', '2', '8', '2', '5', '2', '2', '0', '0', '3']
noncomputable def geometryRow049_jensenBoundText : String := String.ofList (geometryRow049_jensenBoundNumeratorChars ++ '/' :: geometryRow049_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_jensenBound_before_field"
  err.flush

theorem geometryRow049_jensenBound_field :
    geometryRowsJson049.getObjVal? "jensen_bound" = .ok (.str geometryRow049_jensenBoundText) := by rfl

theorem geometryRow049_jensenBound_numerator_no_slash :
    geometryRow049_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow049_jensenBoundNumeratorChars = some (26340643308218526251965716426376394878856670652289908542566709696200204923730546239500094201827560557152021263934783603280222103441046036644126675256897487073386763733435474247680000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow049_jensenBoundDenominatorChars = some (45102333208781614359641142165217737482853873569384442444654628903202193373406712518025339086624378077880170604365582213021640201738669505745057641132931960032630996546967587544035561740715160342382438431282522003 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_nonzero : (45102333208781614359641142165217737482853873569384442444654628903202193373406712518025339086624378077880170604365582213021640201738669505745057641132931960032630996546967587544035561740715160342382438431282522003 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_jensenBound_parse :
    parseRational geometryRow049_jensenBoundText = .ok geometryRowsTyped049.jensenBound :=
  original_rational_fraction_of_chars geometryRow049_jensenBoundNumeratorChars geometryRow049_jensenBoundDenominatorChars
    (26340643308218526251965716426376394878856670652289908542566709696200204923730546239500094201827560557152021263934783603280222103441046036644126675256897487073386763733435474247680000000000000000000000 : Int) (45102333208781614359641142165217737482853873569384442444654628903202193373406712518025339086624378077880170604365582213021640201738669505745057641132931960032630996546967587544035561740715160342382438431282522003 : Int)
    geometryRow049_jensenBound_numerator_no_slash geometryRow049_jensenBound_numerator_parse
    geometryRow049_jensenBound_denominator_parse geometryRow049_jensenBound_denominator_nonzero

theorem geometryRow049_jensenBound_read :
    rationalField geometryRowsJson049 "jensen_bound" = .ok geometryRowsTyped049.jensenBound :=
  original_rationalField_of_string geometryRowsJson049 "jensen_bound" geometryRow049_jensenBoundText
    geometryRowsTyped049.jensenBound geometryRow049_jensenBound_field geometryRow049_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_factorMaxima_before"
  err.flush

theorem geometryRow049_factorMaxima_read :
    rationalArrayField geometryRowsJson049 "factor_maxima" = .ok geometryRowsTyped049.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_gapWeightedMeans_before"
  err.flush

theorem geometryRow049_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson049 "gap_weighted_means" = .ok geometryRowsTyped049.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow049_floorChars : List Char := ['4', '6', '2', '7', '0', '7', '9', '3', '9', '9', '8', '4', '6', '8', '2', '3', '3']
noncomputable def geometryRow049_floorText : String := String.ofList geometryRow049_floorChars

theorem geometryRow049_floor_text_read :
    geometryRowsJson049.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow049_floorText := by rfl

theorem geometryRow049_floor_chars_parse :
    SourceJson.intChars geometryRow049_floorChars = some (46270793998468233 : Int) := by decide +kernel

theorem geometryRow049_floor_parse :
    parseInteger geometryRow049_floorText = .ok geometryRowsTyped049.jensenFloorQ96 := by
  simp only [geometryRow049_floorText, parseInteger, String.toList_ofList, geometryRow049_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_049 :
    decodeGeometryRow geometryRowsJson049 = .ok geometryRowsTyped049 :=
  original_geometryRow_of_fields geometryRowsJson049 geometryRowsTyped049 geometryRow049_floorText
    geometryRow049_simplexId_read geometryRow049_vertexIds_read
    geometryRow049_physicalVolume_read geometryRow049_meanGap_read
    geometryRow049_factorMaxima_read geometryRow049_gapWeightedMeans_read
    geometryRow049_jensenBound_read geometryRow049_floor_text_read geometryRow049_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_049_original_decoder_complete"
  err.flush

theorem geometryRow049_shape :
    geometryRowsTyped049.simplexId = 49 ∧
    geometryRowsTyped049.vertexIds.size = 9 ∧ geometryRowsTyped049.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped049.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped049.factorMaxima.size = 10 ∧ geometryRowsTyped049.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson050 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped050 : GeometryRow :=
  { simplexId := 50,
    vertexIds := #[32, 30, 28, 16, 14, 13, 10, 8, 0],
    physicalVolume := ((64445807166116119504242151809973656355348087 : ℚ) / (85759825416652800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((38082237284771 : ℚ) / (427165200000000 : ℚ)), ((38646437469263 : ℚ) / (427165200000000 : ℚ)), ((2610515682487 : ℚ) / (22286880000000 : ℚ)), ((227912253624743 : ℚ) / (2562991200000000 : ℚ)), ((226519487061863 : ℚ) / (2562991200000000 : ℚ)), ((17386161719761 : ℚ) / (232999200000000 : ℚ)), ((4341938470369 : ℚ) / (116499600000000 : ℚ)), ((587774704897 : ℚ) / (16642800000000 : ℚ)), ((569671204177 : ℚ) / (16642800000000 : ℚ)), ((39536289028783 : ℚ) / (1281495600000000 : ℚ))],
    jensenBound := ((13202347967194484702782640971251001021066345347361158840096139251504019204794325512749857627176960000000000000000000000 : ℚ) / (4609793364719772178723955870746221861161067344026662771646042229057985673812305318416974286684454391934595655967127927919380795359 : ℚ)),
    jensenFloorQ96 := (226907734806533548 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_simplexId_before"
  err.flush

theorem geometryRow050_simplexId_read :
    geometryRowsJson050.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped050.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_vertexIds_before"
  err.flush

theorem geometryRow050_vertexIds_read :
    geometryRowsJson050.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped050.vertexIds := by decide +kernel

noncomputable def geometryRow050_physicalVolumeNumeratorChars : List Char := ['6', '4', '4', '4', '5', '8', '0', '7', '1', '6', '6', '1', '1', '6', '1', '1', '9', '5', '0', '4', '2', '4', '2', '1', '5', '1', '8', '0', '9', '9', '7', '3', '6', '5', '6', '3', '5', '5', '3', '4', '8', '0', '8', '7']
noncomputable def geometryRow050_physicalVolumeDenominatorChars : List Char := ['8', '5', '7', '5', '9', '8', '2', '5', '4', '1', '6', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_physicalVolumeText : String := String.ofList (geometryRow050_physicalVolumeNumeratorChars ++ '/' :: geometryRow050_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_physicalVolume_before_field"
  err.flush

theorem geometryRow050_physicalVolume_field :
    geometryRowsJson050.getObjVal? "physical_volume" = .ok (.str geometryRow050_physicalVolumeText) := by rfl

theorem geometryRow050_physicalVolume_numerator_no_slash :
    geometryRow050_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeNumeratorChars = some (64445807166116119504242151809973656355348087 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeDenominatorChars = some (85759825416652800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_nonzero : (85759825416652800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_physicalVolume_parse :
    parseRational geometryRow050_physicalVolumeText = .ok geometryRowsTyped050.physicalVolume :=
  original_rational_fraction_of_chars geometryRow050_physicalVolumeNumeratorChars geometryRow050_physicalVolumeDenominatorChars
    (64445807166116119504242151809973656355348087 : Int) (85759825416652800000000000000000000000000000000000000000000000000 : Int)
    geometryRow050_physicalVolume_numerator_no_slash geometryRow050_physicalVolume_numerator_parse
    geometryRow050_physicalVolume_denominator_parse geometryRow050_physicalVolume_denominator_nonzero

theorem geometryRow050_physicalVolume_read :
    rationalField geometryRowsJson050 "physical_volume" = .ok geometryRowsTyped050.physicalVolume :=
  original_rationalField_of_string geometryRowsJson050 "physical_volume" geometryRow050_physicalVolumeText
    geometryRowsTyped050.physicalVolume geometryRow050_physicalVolume_field geometryRow050_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_physicalVolume_complete"
  err.flush

noncomputable def geometryRow050_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow050_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_meanGapText : String := String.ofList (geometryRow050_meanGapNumeratorChars ++ '/' :: geometryRow050_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_meanGap_before_field"
  err.flush

theorem geometryRow050_meanGap_field :
    geometryRowsJson050.getObjVal? "mean_gap" = .ok (.str geometryRow050_meanGapText) := by rfl

theorem geometryRow050_meanGap_numerator_no_slash :
    geometryRow050_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_meanGap_numerator_parse :
    SourceJson.intChars geometryRow050_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_parse :
    SourceJson.intChars geometryRow050_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_meanGap_parse :
    parseRational geometryRow050_meanGapText = .ok geometryRowsTyped050.meanGap :=
  original_rational_fraction_of_chars geometryRow050_meanGapNumeratorChars geometryRow050_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow050_meanGap_numerator_no_slash geometryRow050_meanGap_numerator_parse
    geometryRow050_meanGap_denominator_parse geometryRow050_meanGap_denominator_nonzero

theorem geometryRow050_meanGap_read :
    rationalField geometryRowsJson050 "mean_gap" = .ok geometryRowsTyped050.meanGap :=
  original_rationalField_of_string geometryRowsJson050 "mean_gap" geometryRow050_meanGapText
    geometryRowsTyped050.meanGap geometryRow050_meanGap_field geometryRow050_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_meanGap_complete"
  err.flush

noncomputable def geometryRow050_jensenBoundNumeratorChars : List Char := ['1', '3', '2', '0', '2', '3', '4', '7', '9', '6', '7', '1', '9', '4', '4', '8', '4', '7', '0', '2', '7', '8', '2', '6', '4', '0', '9', '7', '1', '2', '5', '1', '0', '0', '1', '0', '2', '1', '0', '6', '6', '3', '4', '5', '3', '4', '7', '3', '6', '1', '1', '5', '8', '8', '4', '0', '0', '9', '6', '1', '3', '9', '2', '5', '1', '5', '0', '4', '0', '1', '9', '2', '0', '4', '7', '9', '4', '3', '2', '5', '5', '1', '2', '7', '4', '9', '8', '5', '7', '6', '2', '7', '1', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_jensenBoundDenominatorChars : List Char := ['4', '6', '0', '9', '7', '9', '3', '3', '6', '4', '7', '1', '9', '7', '7', '2', '1', '7', '8', '7', '2', '3', '9', '5', '5', '8', '7', '0', '7', '4', '6', '2', '2', '1', '8', '6', '1', '1', '6', '1', '0', '6', '7', '3', '4', '4', '0', '2', '6', '6', '6', '2', '7', '7', '1', '6', '4', '6', '0', '4', '2', '2', '2', '9', '0', '5', '7', '9', '8', '5', '6', '7', '3', '8', '1', '2', '3', '0', '5', '3', '1', '8', '4', '1', '6', '9', '7', '4', '2', '8', '6', '6', '8', '4', '4', '5', '4', '3', '9', '1', '9', '3', '4', '5', '9', '5', '6', '5', '5', '9', '6', '7', '1', '2', '7', '9', '2', '7', '9', '1', '9', '3', '8', '0', '7', '9', '5', '3', '5', '9']
noncomputable def geometryRow050_jensenBoundText : String := String.ofList (geometryRow050_jensenBoundNumeratorChars ++ '/' :: geometryRow050_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_jensenBound_before_field"
  err.flush

theorem geometryRow050_jensenBound_field :
    geometryRowsJson050.getObjVal? "jensen_bound" = .ok (.str geometryRow050_jensenBoundText) := by rfl

theorem geometryRow050_jensenBound_numerator_no_slash :
    geometryRow050_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow050_jensenBoundNumeratorChars = some (13202347967194484702782640971251001021066345347361158840096139251504019204794325512749857627176960000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow050_jensenBoundDenominatorChars = some (4609793364719772178723955870746221861161067344026662771646042229057985673812305318416974286684454391934595655967127927919380795359 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_nonzero : (4609793364719772178723955870746221861161067344026662771646042229057985673812305318416974286684454391934595655967127927919380795359 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_jensenBound_parse :
    parseRational geometryRow050_jensenBoundText = .ok geometryRowsTyped050.jensenBound :=
  original_rational_fraction_of_chars geometryRow050_jensenBoundNumeratorChars geometryRow050_jensenBoundDenominatorChars
    (13202347967194484702782640971251001021066345347361158840096139251504019204794325512749857627176960000000000000000000000 : Int) (4609793364719772178723955870746221861161067344026662771646042229057985673812305318416974286684454391934595655967127927919380795359 : Int)
    geometryRow050_jensenBound_numerator_no_slash geometryRow050_jensenBound_numerator_parse
    geometryRow050_jensenBound_denominator_parse geometryRow050_jensenBound_denominator_nonzero

theorem geometryRow050_jensenBound_read :
    rationalField geometryRowsJson050 "jensen_bound" = .ok geometryRowsTyped050.jensenBound :=
  original_rationalField_of_string geometryRowsJson050 "jensen_bound" geometryRow050_jensenBoundText
    geometryRowsTyped050.jensenBound geometryRow050_jensenBound_field geometryRow050_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_factorMaxima_before"
  err.flush

theorem geometryRow050_factorMaxima_read :
    rationalArrayField geometryRowsJson050 "factor_maxima" = .ok geometryRowsTyped050.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_gapWeightedMeans_before"
  err.flush

theorem geometryRow050_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson050 "gap_weighted_means" = .ok geometryRowsTyped050.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow050_floorChars : List Char := ['2', '2', '6', '9', '0', '7', '7', '3', '4', '8', '0', '6', '5', '3', '3', '5', '4', '8']
noncomputable def geometryRow050_floorText : String := String.ofList geometryRow050_floorChars

theorem geometryRow050_floor_text_read :
    geometryRowsJson050.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow050_floorText := by rfl

theorem geometryRow050_floor_chars_parse :
    SourceJson.intChars geometryRow050_floorChars = some (226907734806533548 : Int) := by decide +kernel

theorem geometryRow050_floor_parse :
    parseInteger geometryRow050_floorText = .ok geometryRowsTyped050.jensenFloorQ96 := by
  simp only [geometryRow050_floorText, parseInteger, String.toList_ofList, geometryRow050_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_050 :
    decodeGeometryRow geometryRowsJson050 = .ok geometryRowsTyped050 :=
  original_geometryRow_of_fields geometryRowsJson050 geometryRowsTyped050 geometryRow050_floorText
    geometryRow050_simplexId_read geometryRow050_vertexIds_read
    geometryRow050_physicalVolume_read geometryRow050_meanGap_read
    geometryRow050_factorMaxima_read geometryRow050_gapWeightedMeans_read
    geometryRow050_jensenBound_read geometryRow050_floor_text_read geometryRow050_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_050_original_decoder_complete"
  err.flush

theorem geometryRow050_shape :
    geometryRowsTyped050.simplexId = 50 ∧
    geometryRowsTyped050.vertexIds.size = 9 ∧ geometryRowsTyped050.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped050.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped050.factorMaxima.size = 10 ∧ geometryRowsTyped050.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson051 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped051 : GeometryRow :=
  { simplexId := 51,
    vertexIds := #[32, 30, 28, 27, 15, 4, 2, 1, 0],
    physicalVolume := ((3488140894012437547756827575462811967 : ℚ) / (41096449672298496000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1133902280579 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((7328233 : ℚ) / (196000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((95389799401922721067972141 : ℚ) / (1088010760698950596200000000 : ℚ)), ((657847409483658535144811 : ℚ) / (7229307380059472400000000 : ℚ)), ((11336749503709680516005209 : ℚ) / (96712067617684497440000000 : ℚ)), ((404062276505371183156847087 : ℚ) / (4352043042795802384800000000 : ℚ)), ((401697313242828367390187567 : ℚ) / (4352043042795802384800000000 : ℚ)), ((3137579599559477929575301 : ℚ) / (43960030735311135200000000 : ℚ)), ((6779942779438932898190161 : ℚ) / (197820138308900108400000000 : ℚ)), ((6738464576523810162084331 : ℚ) / (197820138308900108400000000 : ℚ)), ((6630939870389786440555051 : ℚ) / (197820138308900108400000000 : ℚ)), ((224302393771749401061017 : ℚ) / (7229307380059472400000000 : ℚ))],
    jensenBound := ((3232050895172899894336524616620215654710068538526522928841455088367043382588423983041212615057086993142165500877672633805062279977874641585281603574599190156358354433192909185400072504329124212966919720004096000000000000000000000000 : ℚ) / (2238004379396192803017169805644720288178169613299436907652553971042050302097937508809373971111507884965101532182791071921955306862573087950617101312685869089071368215757248956963958294715840730132340788233525782074054206115944934731743769963163915097 : ℚ)),
    jensenFloorQ96 := (114418656162 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_simplexId_before"
  err.flush

theorem geometryRow051_simplexId_read :
    geometryRowsJson051.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped051.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_vertexIds_before"
  err.flush

theorem geometryRow051_vertexIds_read :
    geometryRowsJson051.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped051.vertexIds := by decide +kernel

noncomputable def geometryRow051_physicalVolumeNumeratorChars : List Char := ['3', '4', '8', '8', '1', '4', '0', '8', '9', '4', '0', '1', '2', '4', '3', '7', '5', '4', '7', '7', '5', '6', '8', '2', '7', '5', '7', '5', '4', '6', '2', '8', '1', '1', '9', '6', '7']
noncomputable def geometryRow051_physicalVolumeDenominatorChars : List Char := ['4', '1', '0', '9', '6', '4', '4', '9', '6', '7', '2', '2', '9', '8', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_physicalVolumeText : String := String.ofList (geometryRow051_physicalVolumeNumeratorChars ++ '/' :: geometryRow051_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_physicalVolume_before_field"
  err.flush

theorem geometryRow051_physicalVolume_field :
    geometryRowsJson051.getObjVal? "physical_volume" = .ok (.str geometryRow051_physicalVolumeText) := by rfl

theorem geometryRow051_physicalVolume_numerator_no_slash :
    geometryRow051_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeNumeratorChars = some (3488140894012437547756827575462811967 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeDenominatorChars = some (41096449672298496000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_nonzero : (41096449672298496000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_physicalVolume_parse :
    parseRational geometryRow051_physicalVolumeText = .ok geometryRowsTyped051.physicalVolume :=
  original_rational_fraction_of_chars geometryRow051_physicalVolumeNumeratorChars geometryRow051_physicalVolumeDenominatorChars
    (3488140894012437547756827575462811967 : Int) (41096449672298496000000000000000000000000000000000000000000000000 : Int)
    geometryRow051_physicalVolume_numerator_no_slash geometryRow051_physicalVolume_numerator_parse
    geometryRow051_physicalVolume_denominator_parse geometryRow051_physicalVolume_denominator_nonzero

theorem geometryRow051_physicalVolume_read :
    rationalField geometryRowsJson051 "physical_volume" = .ok geometryRowsTyped051.physicalVolume :=
  original_rationalField_of_string geometryRowsJson051 "physical_volume" geometryRow051_physicalVolumeText
    geometryRowsTyped051.physicalVolume geometryRow051_physicalVolume_field geometryRow051_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_physicalVolume_complete"
  err.flush

noncomputable def geometryRow051_meanGapNumeratorChars : List Char := ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9']
noncomputable def geometryRow051_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_meanGapText : String := String.ofList (geometryRow051_meanGapNumeratorChars ++ '/' :: geometryRow051_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_meanGap_before_field"
  err.flush

theorem geometryRow051_meanGap_field :
    geometryRowsJson051.getObjVal? "mean_gap" = .ok (.str geometryRow051_meanGapText) := by rfl

theorem geometryRow051_meanGap_numerator_no_slash :
    geometryRow051_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_meanGap_numerator_parse :
    SourceJson.intChars geometryRow051_meanGapNumeratorChars = some (1133902280579 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_parse :
    SourceJson.intChars geometryRow051_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_meanGap_parse :
    parseRational geometryRow051_meanGapText = .ok geometryRowsTyped051.meanGap :=
  original_rational_fraction_of_chars geometryRow051_meanGapNumeratorChars geometryRow051_meanGapDenominatorChars
    (1133902280579 : Int) (383811120000000 : Int)
    geometryRow051_meanGap_numerator_no_slash geometryRow051_meanGap_numerator_parse
    geometryRow051_meanGap_denominator_parse geometryRow051_meanGap_denominator_nonzero

theorem geometryRow051_meanGap_read :
    rationalField geometryRowsJson051 "mean_gap" = .ok geometryRowsTyped051.meanGap :=
  original_rationalField_of_string geometryRowsJson051 "mean_gap" geometryRow051_meanGapText
    geometryRowsTyped051.meanGap geometryRow051_meanGap_field geometryRow051_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_meanGap_complete"
  err.flush

noncomputable def geometryRow051_jensenBoundNumeratorChars : List Char := ['3', '2', '3', '2', '0', '5', '0', '8', '9', '5', '1', '7', '2', '8', '9', '9', '8', '9', '4', '3', '3', '6', '5', '2', '4', '6', '1', '6', '6', '2', '0', '2', '1', '5', '6', '5', '4', '7', '1', '0', '0', '6', '8', '5', '3', '8', '5', '2', '6', '5', '2', '2', '9', '2', '8', '8', '4', '1', '4', '5', '5', '0', '8', '8', '3', '6', '7', '0', '4', '3', '3', '8', '2', '5', '8', '8', '4', '2', '3', '9', '8', '3', '0', '4', '1', '2', '1', '2', '6', '1', '5', '0', '5', '7', '0', '8', '6', '9', '9', '3', '1', '4', '2', '1', '6', '5', '5', '0', '0', '8', '7', '7', '6', '7', '2', '6', '3', '3', '8', '0', '5', '0', '6', '2', '2', '7', '9', '9', '7', '7', '8', '7', '4', '6', '4', '1', '5', '8', '5', '2', '8', '1', '6', '0', '3', '5', '7', '4', '5', '9', '9', '1', '9', '0', '1', '5', '6', '3', '5', '8', '3', '5', '4', '4', '3', '3', '1', '9', '2', '9', '0', '9', '1', '8', '5', '4', '0', '0', '0', '7', '2', '5', '0', '4', '3', '2', '9', '1', '2', '4', '2', '1', '2', '9', '6', '6', '9', '1', '9', '7', '2', '0', '0', '0', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_jensenBoundDenominatorChars : List Char := ['2', '2', '3', '8', '0', '0', '4', '3', '7', '9', '3', '9', '6', '1', '9', '2', '8', '0', '3', '0', '1', '7', '1', '6', '9', '8', '0', '5', '6', '4', '4', '7', '2', '0', '2', '8', '8', '1', '7', '8', '1', '6', '9', '6', '1', '3', '2', '9', '9', '4', '3', '6', '9', '0', '7', '6', '5', '2', '5', '5', '3', '9', '7', '1', '0', '4', '2', '0', '5', '0', '3', '0', '2', '0', '9', '7', '9', '3', '7', '5', '0', '8', '8', '0', '9', '3', '7', '3', '9', '7', '1', '1', '1', '1', '5', '0', '7', '8', '8', '4', '9', '6', '5', '1', '0', '1', '5', '3', '2', '1', '8', '2', '7', '9', '1', '0', '7', '1', '9', '2', '1', '9', '5', '5', '3', '0', '6', '8', '6', '2', '5', '7', '3', '0', '8', '7', '9', '5', '0', '6', '1', '7', '1', '0', '1', '3', '1', '2', '6', '8', '5', '8', '6', '9', '0', '8', '9', '0', '7', '1', '3', '6', '8', '2', '1', '5', '7', '5', '7', '2', '4', '8', '9', '5', '6', '9', '6', '3', '9', '5', '8', '2', '9', '4', '7', '1', '5', '8', '4', '0', '7', '3', '0', '1', '3', '2', '3', '4', '0', '7', '8', '8', '2', '3', '3', '5', '2', '5', '7', '8', '2', '0', '7', '4', '0', '5', '4', '2', '0', '6', '1', '1', '5', '9', '4', '4', '9', '3', '4', '7', '3', '1', '7', '4', '3', '7', '6', '9', '9', '6', '3', '1', '6', '3', '9', '1', '5', '0', '9', '7']
noncomputable def geometryRow051_jensenBoundText : String := String.ofList (geometryRow051_jensenBoundNumeratorChars ++ '/' :: geometryRow051_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_jensenBound_before_field"
  err.flush

theorem geometryRow051_jensenBound_field :
    geometryRowsJson051.getObjVal? "jensen_bound" = .ok (.str geometryRow051_jensenBoundText) := by rfl

theorem geometryRow051_jensenBound_numerator_no_slash :
    geometryRow051_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow051_jensenBoundNumeratorChars = some (3232050895172899894336524616620215654710068538526522928841455088367043382588423983041212615057086993142165500877672633805062279977874641585281603574599190156358354433192909185400072504329124212966919720004096000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow051_jensenBoundDenominatorChars = some (2238004379396192803017169805644720288178169613299436907652553971042050302097937508809373971111507884965101532182791071921955306862573087950617101312685869089071368215757248956963958294715840730132340788233525782074054206115944934731743769963163915097 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_nonzero : (2238004379396192803017169805644720288178169613299436907652553971042050302097937508809373971111507884965101532182791071921955306862573087950617101312685869089071368215757248956963958294715840730132340788233525782074054206115944934731743769963163915097 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_jensenBound_parse :
    parseRational geometryRow051_jensenBoundText = .ok geometryRowsTyped051.jensenBound :=
  original_rational_fraction_of_chars geometryRow051_jensenBoundNumeratorChars geometryRow051_jensenBoundDenominatorChars
    (3232050895172899894336524616620215654710068538526522928841455088367043382588423983041212615057086993142165500877672633805062279977874641585281603574599190156358354433192909185400072504329124212966919720004096000000000000000000000000 : Int) (2238004379396192803017169805644720288178169613299436907652553971042050302097937508809373971111507884965101532182791071921955306862573087950617101312685869089071368215757248956963958294715840730132340788233525782074054206115944934731743769963163915097 : Int)
    geometryRow051_jensenBound_numerator_no_slash geometryRow051_jensenBound_numerator_parse
    geometryRow051_jensenBound_denominator_parse geometryRow051_jensenBound_denominator_nonzero

theorem geometryRow051_jensenBound_read :
    rationalField geometryRowsJson051 "jensen_bound" = .ok geometryRowsTyped051.jensenBound :=
  original_rationalField_of_string geometryRowsJson051 "jensen_bound" geometryRow051_jensenBoundText
    geometryRowsTyped051.jensenBound geometryRow051_jensenBound_field geometryRow051_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_factorMaxima_before"
  err.flush

theorem geometryRow051_factorMaxima_read :
    rationalArrayField geometryRowsJson051 "factor_maxima" = .ok geometryRowsTyped051.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_gapWeightedMeans_before"
  err.flush

theorem geometryRow051_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson051 "gap_weighted_means" = .ok geometryRowsTyped051.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow051_floorChars : List Char := ['1', '1', '4', '4', '1', '8', '6', '5', '6', '1', '6', '2']
noncomputable def geometryRow051_floorText : String := String.ofList geometryRow051_floorChars

theorem geometryRow051_floor_text_read :
    geometryRowsJson051.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow051_floorText := by rfl

theorem geometryRow051_floor_chars_parse :
    SourceJson.intChars geometryRow051_floorChars = some (114418656162 : Int) := by decide +kernel

theorem geometryRow051_floor_parse :
    parseInteger geometryRow051_floorText = .ok geometryRowsTyped051.jensenFloorQ96 := by
  simp only [geometryRow051_floorText, parseInteger, String.toList_ofList, geometryRow051_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_051 :
    decodeGeometryRow geometryRowsJson051 = .ok geometryRowsTyped051 :=
  original_geometryRow_of_fields geometryRowsJson051 geometryRowsTyped051 geometryRow051_floorText
    geometryRow051_simplexId_read geometryRow051_vertexIds_read
    geometryRow051_physicalVolume_read geometryRow051_meanGap_read
    geometryRow051_factorMaxima_read geometryRow051_gapWeightedMeans_read
    geometryRow051_jensenBound_read geometryRow051_floor_text_read geometryRow051_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_051_original_decoder_complete"
  err.flush

theorem geometryRow051_shape :
    geometryRowsTyped051.simplexId = 51 ∧
    geometryRowsTyped051.vertexIds.size = 9 ∧ geometryRowsTyped051.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped051.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped051.factorMaxima.size = 10 ∧ geometryRowsTyped051.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson052 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped052 : GeometryRow :=
  { simplexId := 52,
    vertexIds := #[32, 30, 28, 27, 15, 13, 4, 1, 0],
    physicalVolume := ((34530032423838608876394741873929420887 : ℚ) / (44949241829076480000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1557344871202309974557681 : ℚ) / (17647896456119437200000000 : ℚ)), ((5328996694372493438993 : ℚ) / (58630885236277200000000 : ℚ)), ((4015258295301386819573 : ℚ) / (34102215374143840000000 : ℚ)), ((3248734583402965417387961 : ℚ) / (35295792912238874400000000 : ℚ)), ((3229554338001224200881401 : ℚ) / (35295792912238874400000000 : ℚ)), ((25561343191393146379363 : ℚ) / (356523160729685600000000 : ℚ)), ((55346570068470766174183 : ℚ) / (1604354223283585200000000 : ℚ)), ((54987151533733376802193 : ℚ) / (1604354223283585200000000 : ℚ)), ((54115108283394156422353 : ℚ) / (1604354223283585200000000 : ℚ)), ((1817044649559861496571 : ℚ) / (58630885236277200000000 : ℚ))],
    jensenBound := ((2336578879833052999916392940364134543973923623321263908732021524471996427640760990324146468836652773652364039463043704752168078124014392715305925998721836842025968028681401653513620632371200000000000000000000000 : ℚ) / (243123878503821280889839981892520564291773001032373104170221216390543533250527761724361216683237288725661230440918663587102859170285135506394146155688484348121912944007269684783745994551823377652580836530122641133953760200957049 : ℚ)),
    jensenFloorQ96 := (761434262887 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_simplexId_before"
  err.flush

theorem geometryRow052_simplexId_read :
    geometryRowsJson052.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped052.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_vertexIds_before"
  err.flush

theorem geometryRow052_vertexIds_read :
    geometryRowsJson052.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped052.vertexIds := by decide +kernel

noncomputable def geometryRow052_physicalVolumeNumeratorChars : List Char := ['3', '4', '5', '3', '0', '0', '3', '2', '4', '2', '3', '8', '3', '8', '6', '0', '8', '8', '7', '6', '3', '9', '4', '7', '4', '1', '8', '7', '3', '9', '2', '9', '4', '2', '0', '8', '8', '7']
noncomputable def geometryRow052_physicalVolumeDenominatorChars : List Char := ['4', '4', '9', '4', '9', '2', '4', '1', '8', '2', '9', '0', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_physicalVolumeText : String := String.ofList (geometryRow052_physicalVolumeNumeratorChars ++ '/' :: geometryRow052_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_physicalVolume_before_field"
  err.flush

theorem geometryRow052_physicalVolume_field :
    geometryRowsJson052.getObjVal? "physical_volume" = .ok (.str geometryRow052_physicalVolumeText) := by rfl

theorem geometryRow052_physicalVolume_numerator_no_slash :
    geometryRow052_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeNumeratorChars = some (34530032423838608876394741873929420887 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeDenominatorChars = some (44949241829076480000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_nonzero : (44949241829076480000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_physicalVolume_parse :
    parseRational geometryRow052_physicalVolumeText = .ok geometryRowsTyped052.physicalVolume :=
  original_rational_fraction_of_chars geometryRow052_physicalVolumeNumeratorChars geometryRow052_physicalVolumeDenominatorChars
    (34530032423838608876394741873929420887 : Int) (44949241829076480000000000000000000000000000000000000000000000000 : Int)
    geometryRow052_physicalVolume_numerator_no_slash geometryRow052_physicalVolume_numerator_parse
    geometryRow052_physicalVolume_denominator_parse geometryRow052_physicalVolume_denominator_nonzero

theorem geometryRow052_physicalVolume_read :
    rationalField geometryRowsJson052 "physical_volume" = .ok geometryRowsTyped052.physicalVolume :=
  original_rationalField_of_string geometryRowsJson052 "physical_volume" geometryRow052_physicalVolumeText
    geometryRowsTyped052.physicalVolume geometryRow052_physicalVolume_field geometryRow052_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_physicalVolume_complete"
  err.flush

noncomputable def geometryRow052_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow052_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_meanGapText : String := String.ofList (geometryRow052_meanGapNumeratorChars ++ '/' :: geometryRow052_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_meanGap_before_field"
  err.flush

theorem geometryRow052_meanGap_field :
    geometryRowsJson052.getObjVal? "mean_gap" = .ok (.str geometryRow052_meanGapText) := by rfl

theorem geometryRow052_meanGap_numerator_no_slash :
    geometryRow052_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_meanGap_numerator_parse :
    SourceJson.intChars geometryRow052_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_parse :
    SourceJson.intChars geometryRow052_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_meanGap_parse :
    parseRational geometryRow052_meanGapText = .ok geometryRowsTyped052.meanGap :=
  original_rational_fraction_of_chars geometryRow052_meanGapNumeratorChars geometryRow052_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow052_meanGap_numerator_no_slash geometryRow052_meanGap_numerator_parse
    geometryRow052_meanGap_denominator_parse geometryRow052_meanGap_denominator_nonzero

theorem geometryRow052_meanGap_read :
    rationalField geometryRowsJson052 "mean_gap" = .ok geometryRowsTyped052.meanGap :=
  original_rationalField_of_string geometryRowsJson052 "mean_gap" geometryRow052_meanGapText
    geometryRowsTyped052.meanGap geometryRow052_meanGap_field geometryRow052_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_meanGap_complete"
  err.flush

noncomputable def geometryRow052_jensenBoundNumeratorChars : List Char := ['2', '3', '3', '6', '5', '7', '8', '8', '7', '9', '8', '3', '3', '0', '5', '2', '9', '9', '9', '9', '1', '6', '3', '9', '2', '9', '4', '0', '3', '6', '4', '1', '3', '4', '5', '4', '3', '9', '7', '3', '9', '2', '3', '6', '2', '3', '3', '2', '1', '2', '6', '3', '9', '0', '8', '7', '3', '2', '0', '2', '1', '5', '2', '4', '4', '7', '1', '9', '9', '6', '4', '2', '7', '6', '4', '0', '7', '6', '0', '9', '9', '0', '3', '2', '4', '1', '4', '6', '4', '6', '8', '8', '3', '6', '6', '5', '2', '7', '7', '3', '6', '5', '2', '3', '6', '4', '0', '3', '9', '4', '6', '3', '0', '4', '3', '7', '0', '4', '7', '5', '2', '1', '6', '8', '0', '7', '8', '1', '2', '4', '0', '1', '4', '3', '9', '2', '7', '1', '5', '3', '0', '5', '9', '2', '5', '9', '9', '8', '7', '2', '1', '8', '3', '6', '8', '4', '2', '0', '2', '5', '9', '6', '8', '0', '2', '8', '6', '8', '1', '4', '0', '1', '6', '5', '3', '5', '1', '3', '6', '2', '0', '6', '3', '2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_jensenBoundDenominatorChars : List Char := ['2', '4', '3', '1', '2', '3', '8', '7', '8', '5', '0', '3', '8', '2', '1', '2', '8', '0', '8', '8', '9', '8', '3', '9', '9', '8', '1', '8', '9', '2', '5', '2', '0', '5', '6', '4', '2', '9', '1', '7', '7', '3', '0', '0', '1', '0', '3', '2', '3', '7', '3', '1', '0', '4', '1', '7', '0', '2', '2', '1', '2', '1', '6', '3', '9', '0', '5', '4', '3', '5', '3', '3', '2', '5', '0', '5', '2', '7', '7', '6', '1', '7', '2', '4', '3', '6', '1', '2', '1', '6', '6', '8', '3', '2', '3', '7', '2', '8', '8', '7', '2', '5', '6', '6', '1', '2', '3', '0', '4', '4', '0', '9', '1', '8', '6', '6', '3', '5', '8', '7', '1', '0', '2', '8', '5', '9', '1', '7', '0', '2', '8', '5', '1', '3', '5', '5', '0', '6', '3', '9', '4', '1', '4', '6', '1', '5', '5', '6', '8', '8', '4', '8', '4', '3', '4', '8', '1', '2', '1', '9', '1', '2', '9', '4', '4', '0', '0', '7', '2', '6', '9', '6', '8', '4', '7', '8', '3', '7', '4', '5', '9', '9', '4', '5', '5', '1', '8', '2', '3', '3', '7', '7', '6', '5', '2', '5', '8', '0', '8', '3', '6', '5', '3', '0', '1', '2', '2', '6', '4', '1', '1', '3', '3', '9', '5', '3', '7', '6', '0', '2', '0', '0', '9', '5', '7', '0', '4', '9']
noncomputable def geometryRow052_jensenBoundText : String := String.ofList (geometryRow052_jensenBoundNumeratorChars ++ '/' :: geometryRow052_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_jensenBound_before_field"
  err.flush

theorem geometryRow052_jensenBound_field :
    geometryRowsJson052.getObjVal? "jensen_bound" = .ok (.str geometryRow052_jensenBoundText) := by rfl

theorem geometryRow052_jensenBound_numerator_no_slash :
    geometryRow052_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow052_jensenBoundNumeratorChars = some (2336578879833052999916392940364134543973923623321263908732021524471996427640760990324146468836652773652364039463043704752168078124014392715305925998721836842025968028681401653513620632371200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow052_jensenBoundDenominatorChars = some (243123878503821280889839981892520564291773001032373104170221216390543533250527761724361216683237288725661230440918663587102859170285135506394146155688484348121912944007269684783745994551823377652580836530122641133953760200957049 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_nonzero : (243123878503821280889839981892520564291773001032373104170221216390543533250527761724361216683237288725661230440918663587102859170285135506394146155688484348121912944007269684783745994551823377652580836530122641133953760200957049 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_jensenBound_parse :
    parseRational geometryRow052_jensenBoundText = .ok geometryRowsTyped052.jensenBound :=
  original_rational_fraction_of_chars geometryRow052_jensenBoundNumeratorChars geometryRow052_jensenBoundDenominatorChars
    (2336578879833052999916392940364134543973923623321263908732021524471996427640760990324146468836652773652364039463043704752168078124014392715305925998721836842025968028681401653513620632371200000000000000000000000 : Int) (243123878503821280889839981892520564291773001032373104170221216390543533250527761724361216683237288725661230440918663587102859170285135506394146155688484348121912944007269684783745994551823377652580836530122641133953760200957049 : Int)
    geometryRow052_jensenBound_numerator_no_slash geometryRow052_jensenBound_numerator_parse
    geometryRow052_jensenBound_denominator_parse geometryRow052_jensenBound_denominator_nonzero

theorem geometryRow052_jensenBound_read :
    rationalField geometryRowsJson052 "jensen_bound" = .ok geometryRowsTyped052.jensenBound :=
  original_rationalField_of_string geometryRowsJson052 "jensen_bound" geometryRow052_jensenBoundText
    geometryRowsTyped052.jensenBound geometryRow052_jensenBound_field geometryRow052_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_factorMaxima_before"
  err.flush

theorem geometryRow052_factorMaxima_read :
    rationalArrayField geometryRowsJson052 "factor_maxima" = .ok geometryRowsTyped052.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_gapWeightedMeans_before"
  err.flush

theorem geometryRow052_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson052 "gap_weighted_means" = .ok geometryRowsTyped052.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow052_floorChars : List Char := ['7', '6', '1', '4', '3', '4', '2', '6', '2', '8', '8', '7']
noncomputable def geometryRow052_floorText : String := String.ofList geometryRow052_floorChars

theorem geometryRow052_floor_text_read :
    geometryRowsJson052.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow052_floorText := by rfl

theorem geometryRow052_floor_chars_parse :
    SourceJson.intChars geometryRow052_floorChars = some (761434262887 : Int) := by decide +kernel

theorem geometryRow052_floor_parse :
    parseInteger geometryRow052_floorText = .ok geometryRowsTyped052.jensenFloorQ96 := by
  simp only [geometryRow052_floorText, parseInteger, String.toList_ofList, geometryRow052_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_052 :
    decodeGeometryRow geometryRowsJson052 = .ok geometryRowsTyped052 :=
  original_geometryRow_of_fields geometryRowsJson052 geometryRowsTyped052 geometryRow052_floorText
    geometryRow052_simplexId_read geometryRow052_vertexIds_read
    geometryRow052_physicalVolume_read geometryRow052_meanGap_read
    geometryRow052_factorMaxima_read geometryRow052_gapWeightedMeans_read
    geometryRow052_jensenBound_read geometryRow052_floor_text_read geometryRow052_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_052_original_decoder_complete"
  err.flush

theorem geometryRow052_shape :
    geometryRowsTyped052.simplexId = 52 ∧
    geometryRowsTyped052.vertexIds.size = 9 ∧ geometryRowsTyped052.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped052.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped052.factorMaxima.size = 10 ∧ geometryRowsTyped052.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson053 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped053 : GeometryRow :=
  { simplexId := 53,
    vertexIds := #[32, 30, 28, 27, 15, 13, 10, 1, 0],
    physicalVolume := ((57515087852123786739719705888170269121 : ℚ) / (6271987231964160000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((568652953992193633009 : ℚ) / (6398364736486800000000 : ℚ)), ((83059612800625564891 : ℚ) / (914052105212400000000 : ℚ)), ((876556158094624663 : ℚ) / (7418393897376000000 : ℚ)), ((1166644922853139982509 : ℚ) / (12796729472973600000000 : ℚ)), ((1159690994597678693869 : ℚ) / (12796729472973600000000 : ℚ)), ((28172711986871765501 : ℚ) / (387779680999200000000 : ℚ)), ((20920135998049435157 : ℚ) / (581669521498800000000 : ℚ)), ((19637698492563442577 : ℚ) / (581669521498800000000 : ℚ)), ((19321533288651729617 : ℚ) / (581669521498800000000 : ℚ)), ((28321241840555342377 : ℚ) / (914052105212400000000 : ℚ))],
    jensenBound := ((4432142249841549597889115212043204763982696474032581692060990488064077347617858600665267308832396911913036599386102175793454816962753372574444288219175976960000000000000000000000 : ℚ) / (58531717762217760564985540493966665666416322065454981967427650303310597201490021306071316362933130185979313824802082938147267977786382838605752950746618345161921985073659156107148497875043466017 : ℚ)),
    jensenFloorQ96 := (5999319683104 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_simplexId_before"
  err.flush

theorem geometryRow053_simplexId_read :
    geometryRowsJson053.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped053.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_vertexIds_before"
  err.flush

theorem geometryRow053_vertexIds_read :
    geometryRowsJson053.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped053.vertexIds := by decide +kernel

noncomputable def geometryRow053_physicalVolumeNumeratorChars : List Char := ['5', '7', '5', '1', '5', '0', '8', '7', '8', '5', '2', '1', '2', '3', '7', '8', '6', '7', '3', '9', '7', '1', '9', '7', '0', '5', '8', '8', '8', '1', '7', '0', '2', '6', '9', '1', '2', '1']
noncomputable def geometryRow053_physicalVolumeDenominatorChars : List Char := ['6', '2', '7', '1', '9', '8', '7', '2', '3', '1', '9', '6', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_physicalVolumeText : String := String.ofList (geometryRow053_physicalVolumeNumeratorChars ++ '/' :: geometryRow053_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_physicalVolume_before_field"
  err.flush

theorem geometryRow053_physicalVolume_field :
    geometryRowsJson053.getObjVal? "physical_volume" = .ok (.str geometryRow053_physicalVolumeText) := by rfl

theorem geometryRow053_physicalVolume_numerator_no_slash :
    geometryRow053_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeNumeratorChars = some (57515087852123786739719705888170269121 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeDenominatorChars = some (6271987231964160000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_nonzero : (6271987231964160000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_physicalVolume_parse :
    parseRational geometryRow053_physicalVolumeText = .ok geometryRowsTyped053.physicalVolume :=
  original_rational_fraction_of_chars geometryRow053_physicalVolumeNumeratorChars geometryRow053_physicalVolumeDenominatorChars
    (57515087852123786739719705888170269121 : Int) (6271987231964160000000000000000000000000000000000000000000000000 : Int)
    geometryRow053_physicalVolume_numerator_no_slash geometryRow053_physicalVolume_numerator_parse
    geometryRow053_physicalVolume_denominator_parse geometryRow053_physicalVolume_denominator_nonzero

theorem geometryRow053_physicalVolume_read :
    rationalField geometryRowsJson053 "physical_volume" = .ok geometryRowsTyped053.physicalVolume :=
  original_rationalField_of_string geometryRowsJson053 "physical_volume" geometryRow053_physicalVolumeText
    geometryRowsTyped053.physicalVolume geometryRow053_physicalVolume_field geometryRow053_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_physicalVolume_complete"
  err.flush

noncomputable def geometryRow053_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow053_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_meanGapText : String := String.ofList (geometryRow053_meanGapNumeratorChars ++ '/' :: geometryRow053_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_meanGap_before_field"
  err.flush

theorem geometryRow053_meanGap_field :
    geometryRowsJson053.getObjVal? "mean_gap" = .ok (.str geometryRow053_meanGapText) := by rfl

theorem geometryRow053_meanGap_numerator_no_slash :
    geometryRow053_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_meanGap_numerator_parse :
    SourceJson.intChars geometryRow053_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_parse :
    SourceJson.intChars geometryRow053_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_meanGap_parse :
    parseRational geometryRow053_meanGapText = .ok geometryRowsTyped053.meanGap :=
  original_rational_fraction_of_chars geometryRow053_meanGapNumeratorChars geometryRow053_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow053_meanGap_numerator_no_slash geometryRow053_meanGap_numerator_parse
    geometryRow053_meanGap_denominator_parse geometryRow053_meanGap_denominator_nonzero

theorem geometryRow053_meanGap_read :
    rationalField geometryRowsJson053 "mean_gap" = .ok geometryRowsTyped053.meanGap :=
  original_rationalField_of_string geometryRowsJson053 "mean_gap" geometryRow053_meanGapText
    geometryRowsTyped053.meanGap geometryRow053_meanGap_field geometryRow053_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_meanGap_complete"
  err.flush

noncomputable def geometryRow053_jensenBoundNumeratorChars : List Char := ['4', '4', '3', '2', '1', '4', '2', '2', '4', '9', '8', '4', '1', '5', '4', '9', '5', '9', '7', '8', '8', '9', '1', '1', '5', '2', '1', '2', '0', '4', '3', '2', '0', '4', '7', '6', '3', '9', '8', '2', '6', '9', '6', '4', '7', '4', '0', '3', '2', '5', '8', '1', '6', '9', '2', '0', '6', '0', '9', '9', '0', '4', '8', '8', '0', '6', '4', '0', '7', '7', '3', '4', '7', '6', '1', '7', '8', '5', '8', '6', '0', '0', '6', '6', '5', '2', '6', '7', '3', '0', '8', '8', '3', '2', '3', '9', '6', '9', '1', '1', '9', '1', '3', '0', '3', '6', '5', '9', '9', '3', '8', '6', '1', '0', '2', '1', '7', '5', '7', '9', '3', '4', '5', '4', '8', '1', '6', '9', '6', '2', '7', '5', '3', '3', '7', '2', '5', '7', '4', '4', '4', '4', '2', '8', '8', '2', '1', '9', '1', '7', '5', '9', '7', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_jensenBoundDenominatorChars : List Char := ['5', '8', '5', '3', '1', '7', '1', '7', '7', '6', '2', '2', '1', '7', '7', '6', '0', '5', '6', '4', '9', '8', '5', '5', '4', '0', '4', '9', '3', '9', '6', '6', '6', '6', '5', '6', '6', '6', '4', '1', '6', '3', '2', '2', '0', '6', '5', '4', '5', '4', '9', '8', '1', '9', '6', '7', '4', '2', '7', '6', '5', '0', '3', '0', '3', '3', '1', '0', '5', '9', '7', '2', '0', '1', '4', '9', '0', '0', '2', '1', '3', '0', '6', '0', '7', '1', '3', '1', '6', '3', '6', '2', '9', '3', '3', '1', '3', '0', '1', '8', '5', '9', '7', '9', '3', '1', '3', '8', '2', '4', '8', '0', '2', '0', '8', '2', '9', '3', '8', '1', '4', '7', '2', '6', '7', '9', '7', '7', '7', '8', '6', '3', '8', '2', '8', '3', '8', '6', '0', '5', '7', '5', '2', '9', '5', '0', '7', '4', '6', '6', '1', '8', '3', '4', '5', '1', '6', '1', '9', '2', '1', '9', '8', '5', '0', '7', '3', '6', '5', '9', '1', '5', '6', '1', '0', '7', '1', '4', '8', '4', '9', '7', '8', '7', '5', '0', '4', '3', '4', '6', '6', '0', '1', '7']
noncomputable def geometryRow053_jensenBoundText : String := String.ofList (geometryRow053_jensenBoundNumeratorChars ++ '/' :: geometryRow053_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_jensenBound_before_field"
  err.flush

theorem geometryRow053_jensenBound_field :
    geometryRowsJson053.getObjVal? "jensen_bound" = .ok (.str geometryRow053_jensenBoundText) := by rfl

theorem geometryRow053_jensenBound_numerator_no_slash :
    geometryRow053_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow053_jensenBoundNumeratorChars = some (4432142249841549597889115212043204763982696474032581692060990488064077347617858600665267308832396911913036599386102175793454816962753372574444288219175976960000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow053_jensenBoundDenominatorChars = some (58531717762217760564985540493966665666416322065454981967427650303310597201490021306071316362933130185979313824802082938147267977786382838605752950746618345161921985073659156107148497875043466017 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_nonzero : (58531717762217760564985540493966665666416322065454981967427650303310597201490021306071316362933130185979313824802082938147267977786382838605752950746618345161921985073659156107148497875043466017 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_jensenBound_parse :
    parseRational geometryRow053_jensenBoundText = .ok geometryRowsTyped053.jensenBound :=
  original_rational_fraction_of_chars geometryRow053_jensenBoundNumeratorChars geometryRow053_jensenBoundDenominatorChars
    (4432142249841549597889115212043204763982696474032581692060990488064077347617858600665267308832396911913036599386102175793454816962753372574444288219175976960000000000000000000000 : Int) (58531717762217760564985540493966665666416322065454981967427650303310597201490021306071316362933130185979313824802082938147267977786382838605752950746618345161921985073659156107148497875043466017 : Int)
    geometryRow053_jensenBound_numerator_no_slash geometryRow053_jensenBound_numerator_parse
    geometryRow053_jensenBound_denominator_parse geometryRow053_jensenBound_denominator_nonzero

theorem geometryRow053_jensenBound_read :
    rationalField geometryRowsJson053 "jensen_bound" = .ok geometryRowsTyped053.jensenBound :=
  original_rationalField_of_string geometryRowsJson053 "jensen_bound" geometryRow053_jensenBoundText
    geometryRowsTyped053.jensenBound geometryRow053_jensenBound_field geometryRow053_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_factorMaxima_before"
  err.flush

theorem geometryRow053_factorMaxima_read :
    rationalArrayField geometryRowsJson053 "factor_maxima" = .ok geometryRowsTyped053.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_gapWeightedMeans_before"
  err.flush

theorem geometryRow053_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson053 "gap_weighted_means" = .ok geometryRowsTyped053.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow053_floorChars : List Char := ['5', '9', '9', '9', '3', '1', '9', '6', '8', '3', '1', '0', '4']
noncomputable def geometryRow053_floorText : String := String.ofList geometryRow053_floorChars

theorem geometryRow053_floor_text_read :
    geometryRowsJson053.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow053_floorText := by rfl

theorem geometryRow053_floor_chars_parse :
    SourceJson.intChars geometryRow053_floorChars = some (5999319683104 : Int) := by decide +kernel

theorem geometryRow053_floor_parse :
    parseInteger geometryRow053_floorText = .ok geometryRowsTyped053.jensenFloorQ96 := by
  simp only [geometryRow053_floorText, parseInteger, String.toList_ofList, geometryRow053_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_053 :
    decodeGeometryRow geometryRowsJson053 = .ok geometryRowsTyped053 :=
  original_geometryRow_of_fields geometryRowsJson053 geometryRowsTyped053 geometryRow053_floorText
    geometryRow053_simplexId_read geometryRow053_vertexIds_read
    geometryRow053_physicalVolume_read geometryRow053_meanGap_read
    geometryRow053_factorMaxima_read geometryRow053_gapWeightedMeans_read
    geometryRow053_jensenBound_read geometryRow053_floor_text_read geometryRow053_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_053_original_decoder_complete"
  err.flush

theorem geometryRow053_shape :
    geometryRowsTyped053.simplexId = 53 ∧
    geometryRowsTyped053.vertexIds.size = 9 ∧ geometryRowsTyped053.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped053.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped053.factorMaxima.size = 10 ∧ geometryRowsTyped053.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson054 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped054 : GeometryRow :=
  { simplexId := 54,
    vertexIds := #[32, 30, 28, 27, 15, 13, 10, 8, 0],
    physicalVolume := ((1272741888187753727146806895244471695981 : ℚ) / (13823971858206720000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((562216488623 : ℚ) / (6375600000000 : ℚ)), ((570637386899 : ℚ) / (6375600000000 : ℚ)), ((39378431893 : ℚ) / (332640000000 : ℚ)), ((3461809447289 : ℚ) / (38253600000000 : ℚ)), ((3441021886649 : ℚ) / (38253600000000 : ℚ)), ((256570056283 : ℚ) / (3477600000000 : ℚ)), ((9042517171 : ℚ) / (248400000000 : ℚ)), ((59901865927 : ℚ) / (1738800000000 : ℚ)), ((58956744967 : ℚ) / (1738800000000 : ℚ)), ((583918753459 : ℚ) / (19126800000000 : ℚ))],
    jensenBound := ((267095370828247754954318837854906037807998170475024582891117194084799974604800000000000000000000000 : ℚ) / (720003149322594682460315228623725214398411172332449889145427942670168433481203167105226825314924397208421009462643 : ℚ)),
    jensenFloorQ96 := (29390809563399 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_simplexId_before"
  err.flush

theorem geometryRow054_simplexId_read :
    geometryRowsJson054.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped054.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_vertexIds_before"
  err.flush

theorem geometryRow054_vertexIds_read :
    geometryRowsJson054.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped054.vertexIds := by decide +kernel

noncomputable def geometryRow054_physicalVolumeNumeratorChars : List Char := ['1', '2', '7', '2', '7', '4', '1', '8', '8', '8', '1', '8', '7', '7', '5', '3', '7', '2', '7', '1', '4', '6', '8', '0', '6', '8', '9', '5', '2', '4', '4', '4', '7', '1', '6', '9', '5', '9', '8', '1']
noncomputable def geometryRow054_physicalVolumeDenominatorChars : List Char := ['1', '3', '8', '2', '3', '9', '7', '1', '8', '5', '8', '2', '0', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_physicalVolumeText : String := String.ofList (geometryRow054_physicalVolumeNumeratorChars ++ '/' :: geometryRow054_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_physicalVolume_before_field"
  err.flush

theorem geometryRow054_physicalVolume_field :
    geometryRowsJson054.getObjVal? "physical_volume" = .ok (.str geometryRow054_physicalVolumeText) := by rfl

theorem geometryRow054_physicalVolume_numerator_no_slash :
    geometryRow054_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeNumeratorChars = some (1272741888187753727146806895244471695981 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeDenominatorChars = some (13823971858206720000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_nonzero : (13823971858206720000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_physicalVolume_parse :
    parseRational geometryRow054_physicalVolumeText = .ok geometryRowsTyped054.physicalVolume :=
  original_rational_fraction_of_chars geometryRow054_physicalVolumeNumeratorChars geometryRow054_physicalVolumeDenominatorChars
    (1272741888187753727146806895244471695981 : Int) (13823971858206720000000000000000000000000000000000000000000000000 : Int)
    geometryRow054_physicalVolume_numerator_no_slash geometryRow054_physicalVolume_numerator_parse
    geometryRow054_physicalVolume_denominator_parse geometryRow054_physicalVolume_denominator_nonzero

theorem geometryRow054_physicalVolume_read :
    rationalField geometryRowsJson054 "physical_volume" = .ok geometryRowsTyped054.physicalVolume :=
  original_rationalField_of_string geometryRowsJson054 "physical_volume" geometryRow054_physicalVolumeText
    geometryRowsTyped054.physicalVolume geometryRow054_physicalVolume_field geometryRow054_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_physicalVolume_complete"
  err.flush

noncomputable def geometryRow054_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow054_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_meanGapText : String := String.ofList (geometryRow054_meanGapNumeratorChars ++ '/' :: geometryRow054_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_meanGap_before_field"
  err.flush

theorem geometryRow054_meanGap_field :
    geometryRowsJson054.getObjVal? "mean_gap" = .ok (.str geometryRow054_meanGapText) := by rfl

theorem geometryRow054_meanGap_numerator_no_slash :
    geometryRow054_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_meanGap_numerator_parse :
    SourceJson.intChars geometryRow054_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_parse :
    SourceJson.intChars geometryRow054_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_meanGap_parse :
    parseRational geometryRow054_meanGapText = .ok geometryRowsTyped054.meanGap :=
  original_rational_fraction_of_chars geometryRow054_meanGapNumeratorChars geometryRow054_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow054_meanGap_numerator_no_slash geometryRow054_meanGap_numerator_parse
    geometryRow054_meanGap_denominator_parse geometryRow054_meanGap_denominator_nonzero

theorem geometryRow054_meanGap_read :
    rationalField geometryRowsJson054 "mean_gap" = .ok geometryRowsTyped054.meanGap :=
  original_rationalField_of_string geometryRowsJson054 "mean_gap" geometryRow054_meanGapText
    geometryRowsTyped054.meanGap geometryRow054_meanGap_field geometryRow054_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_meanGap_complete"
  err.flush

noncomputable def geometryRow054_jensenBoundNumeratorChars : List Char := ['2', '6', '7', '0', '9', '5', '3', '7', '0', '8', '2', '8', '2', '4', '7', '7', '5', '4', '9', '5', '4', '3', '1', '8', '8', '3', '7', '8', '5', '4', '9', '0', '6', '0', '3', '7', '8', '0', '7', '9', '9', '8', '1', '7', '0', '4', '7', '5', '0', '2', '4', '5', '8', '2', '8', '9', '1', '1', '1', '7', '1', '9', '4', '0', '8', '4', '7', '9', '9', '9', '7', '4', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_jensenBoundDenominatorChars : List Char := ['7', '2', '0', '0', '0', '3', '1', '4', '9', '3', '2', '2', '5', '9', '4', '6', '8', '2', '4', '6', '0', '3', '1', '5', '2', '2', '8', '6', '2', '3', '7', '2', '5', '2', '1', '4', '3', '9', '8', '4', '1', '1', '1', '7', '2', '3', '3', '2', '4', '4', '9', '8', '8', '9', '1', '4', '5', '4', '2', '7', '9', '4', '2', '6', '7', '0', '1', '6', '8', '4', '3', '3', '4', '8', '1', '2', '0', '3', '1', '6', '7', '1', '0', '5', '2', '2', '6', '8', '2', '5', '3', '1', '4', '9', '2', '4', '3', '9', '7', '2', '0', '8', '4', '2', '1', '0', '0', '9', '4', '6', '2', '6', '4', '3']
noncomputable def geometryRow054_jensenBoundText : String := String.ofList (geometryRow054_jensenBoundNumeratorChars ++ '/' :: geometryRow054_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_jensenBound_before_field"
  err.flush

theorem geometryRow054_jensenBound_field :
    geometryRowsJson054.getObjVal? "jensen_bound" = .ok (.str geometryRow054_jensenBoundText) := by rfl

theorem geometryRow054_jensenBound_numerator_no_slash :
    geometryRow054_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow054_jensenBoundNumeratorChars = some (267095370828247754954318837854906037807998170475024582891117194084799974604800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow054_jensenBoundDenominatorChars = some (720003149322594682460315228623725214398411172332449889145427942670168433481203167105226825314924397208421009462643 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_nonzero : (720003149322594682460315228623725214398411172332449889145427942670168433481203167105226825314924397208421009462643 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_jensenBound_parse :
    parseRational geometryRow054_jensenBoundText = .ok geometryRowsTyped054.jensenBound :=
  original_rational_fraction_of_chars geometryRow054_jensenBoundNumeratorChars geometryRow054_jensenBoundDenominatorChars
    (267095370828247754954318837854906037807998170475024582891117194084799974604800000000000000000000000 : Int) (720003149322594682460315228623725214398411172332449889145427942670168433481203167105226825314924397208421009462643 : Int)
    geometryRow054_jensenBound_numerator_no_slash geometryRow054_jensenBound_numerator_parse
    geometryRow054_jensenBound_denominator_parse geometryRow054_jensenBound_denominator_nonzero

theorem geometryRow054_jensenBound_read :
    rationalField geometryRowsJson054 "jensen_bound" = .ok geometryRowsTyped054.jensenBound :=
  original_rationalField_of_string geometryRowsJson054 "jensen_bound" geometryRow054_jensenBoundText
    geometryRowsTyped054.jensenBound geometryRow054_jensenBound_field geometryRow054_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_factorMaxima_before"
  err.flush

theorem geometryRow054_factorMaxima_read :
    rationalArrayField geometryRowsJson054 "factor_maxima" = .ok geometryRowsTyped054.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_gapWeightedMeans_before"
  err.flush

theorem geometryRow054_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson054 "gap_weighted_means" = .ok geometryRowsTyped054.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow054_floorChars : List Char := ['2', '9', '3', '9', '0', '8', '0', '9', '5', '6', '3', '3', '9', '9']
noncomputable def geometryRow054_floorText : String := String.ofList geometryRow054_floorChars

theorem geometryRow054_floor_text_read :
    geometryRowsJson054.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow054_floorText := by rfl

theorem geometryRow054_floor_chars_parse :
    SourceJson.intChars geometryRow054_floorChars = some (29390809563399 : Int) := by decide +kernel

theorem geometryRow054_floor_parse :
    parseInteger geometryRow054_floorText = .ok geometryRowsTyped054.jensenFloorQ96 := by
  simp only [geometryRow054_floorText, parseInteger, String.toList_ofList, geometryRow054_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_054 :
    decodeGeometryRow geometryRowsJson054 = .ok geometryRowsTyped054 :=
  original_geometryRow_of_fields geometryRowsJson054 geometryRowsTyped054 geometryRow054_floorText
    geometryRow054_simplexId_read geometryRow054_vertexIds_read
    geometryRow054_physicalVolume_read geometryRow054_meanGap_read
    geometryRow054_factorMaxima_read geometryRow054_gapWeightedMeans_read
    geometryRow054_jensenBound_read geometryRow054_floor_text_read geometryRow054_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_054_original_decoder_complete"
  err.flush

theorem geometryRow054_shape :
    geometryRowsTyped054.simplexId = 54 ∧
    geometryRowsTyped054.vertexIds.size = 9 ∧ geometryRowsTyped054.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped054.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped054.factorMaxima.size = 10 ∧ geometryRowsTyped054.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson055 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped055 : GeometryRow :=
  { simplexId := 55,
    vertexIds := #[32, 30, 28, 27, 23, 13, 4, 1, 0],
    physicalVolume := ((651515980268091631735945095516583139 : ℚ) / (1170553172632200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((759717234448597552519423 : ℚ) / (8823948228059718600000000 : ℚ)), ((2601524256978414710329 : ℚ) / (29315442618138600000000 : ℚ)), ((9111747509389060150919 : ℚ) / (76729984591823640000000 : ℚ)), ((137900820984239207287439 : ℚ) / (1470658038009953100000000 : ℚ)), ((137101644092499989932999 : ℚ) / (1470658038009953100000000 : ℚ)), ((56703669483315663190733 : ℚ) / (802177111641792600000000 : ℚ)), ((14176089889650741123707 : ℚ) / (401088555820896300000000 : ℚ)), ((26919175731940705529599 : ℚ) / (802177111641792600000000 : ℚ)), ((26483154106771095339679 : ℚ) / (802177111641792600000000 : ℚ)), ((887530961377320078563 : ℚ) / (29315442618138600000000 : ℚ))],
    jensenBound := ((2170949549454125682222781050614524668460480966113753248796882725040016129089778253589286356045165923008579280948490999734893426550356428475491745246412523866573739017922593548175009280000000000000000000000 : ℚ) / (294007463450454993009867246845268844395553854119327818952366445191435107555849211688872982260143155660317791495889065906944095616735394245277455749303644497274494362400633193634559366007526774423598845640583067848024923401 : ℚ)),
    jensenFloorQ96 := (585020331442 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_simplexId_before"
  err.flush

theorem geometryRow055_simplexId_read :
    geometryRowsJson055.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped055.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_vertexIds_before"
  err.flush

theorem geometryRow055_vertexIds_read :
    geometryRowsJson055.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped055.vertexIds := by decide +kernel

noncomputable def geometryRow055_physicalVolumeNumeratorChars : List Char := ['6', '5', '1', '5', '1', '5', '9', '8', '0', '2', '6', '8', '0', '9', '1', '6', '3', '1', '7', '3', '5', '9', '4', '5', '0', '9', '5', '5', '1', '6', '5', '8', '3', '1', '3', '9']
noncomputable def geometryRow055_physicalVolumeDenominatorChars : List Char := ['1', '1', '7', '0', '5', '5', '3', '1', '7', '2', '6', '3', '2', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_physicalVolumeText : String := String.ofList (geometryRow055_physicalVolumeNumeratorChars ++ '/' :: geometryRow055_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_physicalVolume_before_field"
  err.flush

theorem geometryRow055_physicalVolume_field :
    geometryRowsJson055.getObjVal? "physical_volume" = .ok (.str geometryRow055_physicalVolumeText) := by rfl

theorem geometryRow055_physicalVolume_numerator_no_slash :
    geometryRow055_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeNumeratorChars = some (651515980268091631735945095516583139 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeDenominatorChars = some (1170553172632200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_nonzero : (1170553172632200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_physicalVolume_parse :
    parseRational geometryRow055_physicalVolumeText = .ok geometryRowsTyped055.physicalVolume :=
  original_rational_fraction_of_chars geometryRow055_physicalVolumeNumeratorChars geometryRow055_physicalVolumeDenominatorChars
    (651515980268091631735945095516583139 : Int) (1170553172632200000000000000000000000000000000000000000000000000 : Int)
    geometryRow055_physicalVolume_numerator_no_slash geometryRow055_physicalVolume_numerator_parse
    geometryRow055_physicalVolume_denominator_parse geometryRow055_physicalVolume_denominator_nonzero

theorem geometryRow055_physicalVolume_read :
    rationalField geometryRowsJson055 "physical_volume" = .ok geometryRowsTyped055.physicalVolume :=
  original_rationalField_of_string geometryRowsJson055 "physical_volume" geometryRow055_physicalVolumeText
    geometryRowsTyped055.physicalVolume geometryRow055_physicalVolume_field geometryRow055_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_physicalVolume_complete"
  err.flush

noncomputable def geometryRow055_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow055_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_meanGapText : String := String.ofList (geometryRow055_meanGapNumeratorChars ++ '/' :: geometryRow055_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_meanGap_before_field"
  err.flush

theorem geometryRow055_meanGap_field :
    geometryRowsJson055.getObjVal? "mean_gap" = .ok (.str geometryRow055_meanGapText) := by rfl

theorem geometryRow055_meanGap_numerator_no_slash :
    geometryRow055_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_meanGap_numerator_parse :
    SourceJson.intChars geometryRow055_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_parse :
    SourceJson.intChars geometryRow055_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_meanGap_parse :
    parseRational geometryRow055_meanGapText = .ok geometryRowsTyped055.meanGap :=
  original_rational_fraction_of_chars geometryRow055_meanGapNumeratorChars geometryRow055_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow055_meanGap_numerator_no_slash geometryRow055_meanGap_numerator_parse
    geometryRow055_meanGap_denominator_parse geometryRow055_meanGap_denominator_nonzero

theorem geometryRow055_meanGap_read :
    rationalField geometryRowsJson055 "mean_gap" = .ok geometryRowsTyped055.meanGap :=
  original_rationalField_of_string geometryRowsJson055 "mean_gap" geometryRow055_meanGapText
    geometryRowsTyped055.meanGap geometryRow055_meanGap_field geometryRow055_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_meanGap_complete"
  err.flush

noncomputable def geometryRow055_jensenBoundNumeratorChars : List Char := ['2', '1', '7', '0', '9', '4', '9', '5', '4', '9', '4', '5', '4', '1', '2', '5', '6', '8', '2', '2', '2', '2', '7', '8', '1', '0', '5', '0', '6', '1', '4', '5', '2', '4', '6', '6', '8', '4', '6', '0', '4', '8', '0', '9', '6', '6', '1', '1', '3', '7', '5', '3', '2', '4', '8', '7', '9', '6', '8', '8', '2', '7', '2', '5', '0', '4', '0', '0', '1', '6', '1', '2', '9', '0', '8', '9', '7', '7', '8', '2', '5', '3', '5', '8', '9', '2', '8', '6', '3', '5', '6', '0', '4', '5', '1', '6', '5', '9', '2', '3', '0', '0', '8', '5', '7', '9', '2', '8', '0', '9', '4', '8', '4', '9', '0', '9', '9', '9', '7', '3', '4', '8', '9', '3', '4', '2', '6', '5', '5', '0', '3', '5', '6', '4', '2', '8', '4', '7', '5', '4', '9', '1', '7', '4', '5', '2', '4', '6', '4', '1', '2', '5', '2', '3', '8', '6', '6', '5', '7', '3', '7', '3', '9', '0', '1', '7', '9', '2', '2', '5', '9', '3', '5', '4', '8', '1', '7', '5', '0', '0', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_jensenBoundDenominatorChars : List Char := ['2', '9', '4', '0', '0', '7', '4', '6', '3', '4', '5', '0', '4', '5', '4', '9', '9', '3', '0', '0', '9', '8', '6', '7', '2', '4', '6', '8', '4', '5', '2', '6', '8', '8', '4', '4', '3', '9', '5', '5', '5', '3', '8', '5', '4', '1', '1', '9', '3', '2', '7', '8', '1', '8', '9', '5', '2', '3', '6', '6', '4', '4', '5', '1', '9', '1', '4', '3', '5', '1', '0', '7', '5', '5', '5', '8', '4', '9', '2', '1', '1', '6', '8', '8', '8', '7', '2', '9', '8', '2', '2', '6', '0', '1', '4', '3', '1', '5', '5', '6', '6', '0', '3', '1', '7', '7', '9', '1', '4', '9', '5', '8', '8', '9', '0', '6', '5', '9', '0', '6', '9', '4', '4', '0', '9', '5', '6', '1', '6', '7', '3', '5', '3', '9', '4', '2', '4', '5', '2', '7', '7', '4', '5', '5', '7', '4', '9', '3', '0', '3', '6', '4', '4', '4', '9', '7', '2', '7', '4', '4', '9', '4', '3', '6', '2', '4', '0', '0', '6', '3', '3', '1', '9', '3', '6', '3', '4', '5', '5', '9', '3', '6', '6', '0', '0', '7', '5', '2', '6', '7', '7', '4', '4', '2', '3', '5', '9', '8', '8', '4', '5', '6', '4', '0', '5', '8', '3', '0', '6', '7', '8', '4', '8', '0', '2', '4', '9', '2', '3', '4', '0', '1']
noncomputable def geometryRow055_jensenBoundText : String := String.ofList (geometryRow055_jensenBoundNumeratorChars ++ '/' :: geometryRow055_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_jensenBound_before_field"
  err.flush

theorem geometryRow055_jensenBound_field :
    geometryRowsJson055.getObjVal? "jensen_bound" = .ok (.str geometryRow055_jensenBoundText) := by rfl

theorem geometryRow055_jensenBound_numerator_no_slash :
    geometryRow055_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow055_jensenBoundNumeratorChars = some (2170949549454125682222781050614524668460480966113753248796882725040016129089778253589286356045165923008579280948490999734893426550356428475491745246412523866573739017922593548175009280000000000000000000000 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow055_jensenBoundDenominatorChars = some (294007463450454993009867246845268844395553854119327818952366445191435107555849211688872982260143155660317791495889065906944095616735394245277455749303644497274494362400633193634559366007526774423598845640583067848024923401 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_nonzero : (294007463450454993009867246845268844395553854119327818952366445191435107555849211688872982260143155660317791495889065906944095616735394245277455749303644497274494362400633193634559366007526774423598845640583067848024923401 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_jensenBound_parse :
    parseRational geometryRow055_jensenBoundText = .ok geometryRowsTyped055.jensenBound :=
  original_rational_fraction_of_chars geometryRow055_jensenBoundNumeratorChars geometryRow055_jensenBoundDenominatorChars
    (2170949549454125682222781050614524668460480966113753248796882725040016129089778253589286356045165923008579280948490999734893426550356428475491745246412523866573739017922593548175009280000000000000000000000 : Int) (294007463450454993009867246845268844395553854119327818952366445191435107555849211688872982260143155660317791495889065906944095616735394245277455749303644497274494362400633193634559366007526774423598845640583067848024923401 : Int)
    geometryRow055_jensenBound_numerator_no_slash geometryRow055_jensenBound_numerator_parse
    geometryRow055_jensenBound_denominator_parse geometryRow055_jensenBound_denominator_nonzero

theorem geometryRow055_jensenBound_read :
    rationalField geometryRowsJson055 "jensen_bound" = .ok geometryRowsTyped055.jensenBound :=
  original_rationalField_of_string geometryRowsJson055 "jensen_bound" geometryRow055_jensenBoundText
    geometryRowsTyped055.jensenBound geometryRow055_jensenBound_field geometryRow055_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_factorMaxima_before"
  err.flush

theorem geometryRow055_factorMaxima_read :
    rationalArrayField geometryRowsJson055 "factor_maxima" = .ok geometryRowsTyped055.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_gapWeightedMeans_before"
  err.flush

theorem geometryRow055_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson055 "gap_weighted_means" = .ok geometryRowsTyped055.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow055_floorChars : List Char := ['5', '8', '5', '0', '2', '0', '3', '3', '1', '4', '4', '2']
noncomputable def geometryRow055_floorText : String := String.ofList geometryRow055_floorChars

theorem geometryRow055_floor_text_read :
    geometryRowsJson055.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow055_floorText := by rfl

theorem geometryRow055_floor_chars_parse :
    SourceJson.intChars geometryRow055_floorChars = some (585020331442 : Int) := by decide +kernel

theorem geometryRow055_floor_parse :
    parseInteger geometryRow055_floorText = .ok geometryRowsTyped055.jensenFloorQ96 := by
  simp only [geometryRow055_floorText, parseInteger, String.toList_ofList, geometryRow055_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_055 :
    decodeGeometryRow geometryRowsJson055 = .ok geometryRowsTyped055 :=
  original_geometryRow_of_fields geometryRowsJson055 geometryRowsTyped055 geometryRow055_floorText
    geometryRow055_simplexId_read geometryRow055_vertexIds_read
    geometryRow055_physicalVolume_read geometryRow055_meanGap_read
    geometryRow055_factorMaxima_read geometryRow055_gapWeightedMeans_read
    geometryRow055_jensenBound_read geometryRow055_floor_text_read geometryRow055_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_055_original_decoder_complete"
  err.flush

theorem geometryRow055_shape :
    geometryRowsTyped055.simplexId = 55 ∧
    geometryRowsTyped055.vertexIds.size = 9 ∧ geometryRowsTyped055.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped055.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped055.factorMaxima.size = 10 ∧ geometryRowsTyped055.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock006 : List SourceJson := [geometryRowsJson048, geometryRowsJson049, geometryRowsJson050, geometryRowsJson051, geometryRowsJson052, geometryRowsJson053, geometryRowsJson054, geometryRowsJson055]
noncomputable def geometryRowsTypedBlock006 : List GeometryRow := [geometryRowsTyped048, geometryRowsTyped049, geometryRowsTyped050, geometryRowsTyped051, geometryRowsTyped052, geometryRowsTyped053, geometryRowsTyped054, geometryRowsTyped055]

theorem geometry_Rows_block_006_push_eq (acc : List SourceJson) :
    SimplicesBlock006.blockPush acc = [geometryRowsJson055, geometryRowsJson054, geometryRowsJson053, geometryRowsJson052, geometryRowsJson051, geometryRowsJson050, geometryRowsJson049, geometryRowsJson048] ++ acc := by rfl

theorem geometry_Rows_block_006_reverse (acc : List SourceJson) :
    (SimplicesBlock006.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock006 := by
  rw [geometry_Rows_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_006 :
    geometryRowsJsonBlock006.mapM decodeGeometryRow = .ok geometryRowsTypedBlock006 := by
  simp only [geometryRowsJsonBlock006, geometryRowsTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_048, decode_geometry_Rows_049, decode_geometry_Rows_050, decode_geometry_Rows_051, decode_geometry_Rows_052, decode_geometry_Rows_053, decode_geometry_Rows_054, decode_geometry_Rows_055]
  rfl

theorem geometry_Rows_block_006_length : geometryRowsTypedBlock006.length = 8 := by rfl

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
#print axioms geometryRow048_shape
#print axioms geometryRow049_simplexId_read
#print axioms geometryRow049_vertexIds_read
#print axioms geometryRow049_physicalVolume_field
#print axioms geometryRow049_physicalVolume_numerator_no_slash
#print axioms geometryRow049_physicalVolume_numerator_parse
#print axioms geometryRow049_physicalVolume_denominator_parse
#print axioms geometryRow049_physicalVolume_denominator_nonzero
#print axioms geometryRow049_physicalVolume_parse
#print axioms geometryRow049_physicalVolume_read
#print axioms geometryRow049_meanGap_field
#print axioms geometryRow049_meanGap_numerator_no_slash
#print axioms geometryRow049_meanGap_numerator_parse
#print axioms geometryRow049_meanGap_denominator_parse
#print axioms geometryRow049_meanGap_denominator_nonzero
#print axioms geometryRow049_meanGap_parse
#print axioms geometryRow049_meanGap_read
#print axioms geometryRow049_jensenBound_field
#print axioms geometryRow049_jensenBound_numerator_no_slash
#print axioms geometryRow049_jensenBound_numerator_parse
#print axioms geometryRow049_jensenBound_denominator_parse
#print axioms geometryRow049_jensenBound_denominator_nonzero
#print axioms geometryRow049_jensenBound_parse
#print axioms geometryRow049_jensenBound_read
#print axioms geometryRow049_factorMaxima_read
#print axioms geometryRow049_gapWeightedMeans_read
#print axioms geometryRow049_floor_text_read
#print axioms geometryRow049_floor_chars_parse
#print axioms geometryRow049_floor_parse
#print axioms decode_geometry_Rows_049
#print axioms geometryRow049_shape
#print axioms geometryRow050_simplexId_read
#print axioms geometryRow050_vertexIds_read
#print axioms geometryRow050_physicalVolume_field
#print axioms geometryRow050_physicalVolume_numerator_no_slash
#print axioms geometryRow050_physicalVolume_numerator_parse
#print axioms geometryRow050_physicalVolume_denominator_parse
#print axioms geometryRow050_physicalVolume_denominator_nonzero
#print axioms geometryRow050_physicalVolume_parse
#print axioms geometryRow050_physicalVolume_read
#print axioms geometryRow050_meanGap_field
#print axioms geometryRow050_meanGap_numerator_no_slash
#print axioms geometryRow050_meanGap_numerator_parse
#print axioms geometryRow050_meanGap_denominator_parse
#print axioms geometryRow050_meanGap_denominator_nonzero
#print axioms geometryRow050_meanGap_parse
#print axioms geometryRow050_meanGap_read
#print axioms geometryRow050_jensenBound_field
#print axioms geometryRow050_jensenBound_numerator_no_slash
#print axioms geometryRow050_jensenBound_numerator_parse
#print axioms geometryRow050_jensenBound_denominator_parse
#print axioms geometryRow050_jensenBound_denominator_nonzero
#print axioms geometryRow050_jensenBound_parse
#print axioms geometryRow050_jensenBound_read
#print axioms geometryRow050_factorMaxima_read
#print axioms geometryRow050_gapWeightedMeans_read
#print axioms geometryRow050_floor_text_read
#print axioms geometryRow050_floor_chars_parse
#print axioms geometryRow050_floor_parse
#print axioms decode_geometry_Rows_050
#print axioms geometryRow050_shape
#print axioms geometryRow051_simplexId_read
#print axioms geometryRow051_vertexIds_read
#print axioms geometryRow051_physicalVolume_field
#print axioms geometryRow051_physicalVolume_numerator_no_slash
#print axioms geometryRow051_physicalVolume_numerator_parse
#print axioms geometryRow051_physicalVolume_denominator_parse
#print axioms geometryRow051_physicalVolume_denominator_nonzero
#print axioms geometryRow051_physicalVolume_parse
#print axioms geometryRow051_physicalVolume_read
#print axioms geometryRow051_meanGap_field
#print axioms geometryRow051_meanGap_numerator_no_slash
#print axioms geometryRow051_meanGap_numerator_parse
#print axioms geometryRow051_meanGap_denominator_parse
#print axioms geometryRow051_meanGap_denominator_nonzero
#print axioms geometryRow051_meanGap_parse
#print axioms geometryRow051_meanGap_read
#print axioms geometryRow051_jensenBound_field
#print axioms geometryRow051_jensenBound_numerator_no_slash
#print axioms geometryRow051_jensenBound_numerator_parse
#print axioms geometryRow051_jensenBound_denominator_parse
#print axioms geometryRow051_jensenBound_denominator_nonzero
#print axioms geometryRow051_jensenBound_parse
#print axioms geometryRow051_jensenBound_read
#print axioms geometryRow051_factorMaxima_read
#print axioms geometryRow051_gapWeightedMeans_read
#print axioms geometryRow051_floor_text_read
#print axioms geometryRow051_floor_chars_parse
#print axioms geometryRow051_floor_parse
#print axioms decode_geometry_Rows_051
#print axioms geometryRow051_shape
#print axioms geometryRow052_simplexId_read
#print axioms geometryRow052_vertexIds_read
#print axioms geometryRow052_physicalVolume_field
#print axioms geometryRow052_physicalVolume_numerator_no_slash
#print axioms geometryRow052_physicalVolume_numerator_parse
#print axioms geometryRow052_physicalVolume_denominator_parse
#print axioms geometryRow052_physicalVolume_denominator_nonzero
#print axioms geometryRow052_physicalVolume_parse
#print axioms geometryRow052_physicalVolume_read
#print axioms geometryRow052_meanGap_field
#print axioms geometryRow052_meanGap_numerator_no_slash
#print axioms geometryRow052_meanGap_numerator_parse
#print axioms geometryRow052_meanGap_denominator_parse
#print axioms geometryRow052_meanGap_denominator_nonzero
#print axioms geometryRow052_meanGap_parse
#print axioms geometryRow052_meanGap_read
#print axioms geometryRow052_jensenBound_field
#print axioms geometryRow052_jensenBound_numerator_no_slash
#print axioms geometryRow052_jensenBound_numerator_parse
#print axioms geometryRow052_jensenBound_denominator_parse
#print axioms geometryRow052_jensenBound_denominator_nonzero
#print axioms geometryRow052_jensenBound_parse
#print axioms geometryRow052_jensenBound_read
#print axioms geometryRow052_factorMaxima_read
#print axioms geometryRow052_gapWeightedMeans_read
#print axioms geometryRow052_floor_text_read
#print axioms geometryRow052_floor_chars_parse
#print axioms geometryRow052_floor_parse
#print axioms decode_geometry_Rows_052
#print axioms geometryRow052_shape
#print axioms geometryRow053_simplexId_read
#print axioms geometryRow053_vertexIds_read
#print axioms geometryRow053_physicalVolume_field
#print axioms geometryRow053_physicalVolume_numerator_no_slash
#print axioms geometryRow053_physicalVolume_numerator_parse
#print axioms geometryRow053_physicalVolume_denominator_parse
#print axioms geometryRow053_physicalVolume_denominator_nonzero
#print axioms geometryRow053_physicalVolume_parse
#print axioms geometryRow053_physicalVolume_read
#print axioms geometryRow053_meanGap_field
#print axioms geometryRow053_meanGap_numerator_no_slash
#print axioms geometryRow053_meanGap_numerator_parse
#print axioms geometryRow053_meanGap_denominator_parse
#print axioms geometryRow053_meanGap_denominator_nonzero
#print axioms geometryRow053_meanGap_parse
#print axioms geometryRow053_meanGap_read
#print axioms geometryRow053_jensenBound_field
#print axioms geometryRow053_jensenBound_numerator_no_slash
#print axioms geometryRow053_jensenBound_numerator_parse
#print axioms geometryRow053_jensenBound_denominator_parse
#print axioms geometryRow053_jensenBound_denominator_nonzero
#print axioms geometryRow053_jensenBound_parse
#print axioms geometryRow053_jensenBound_read
#print axioms geometryRow053_factorMaxima_read
#print axioms geometryRow053_gapWeightedMeans_read
#print axioms geometryRow053_floor_text_read
#print axioms geometryRow053_floor_chars_parse
#print axioms geometryRow053_floor_parse
#print axioms decode_geometry_Rows_053
#print axioms geometryRow053_shape
#print axioms geometryRow054_simplexId_read
#print axioms geometryRow054_vertexIds_read
#print axioms geometryRow054_physicalVolume_field
#print axioms geometryRow054_physicalVolume_numerator_no_slash
#print axioms geometryRow054_physicalVolume_numerator_parse
#print axioms geometryRow054_physicalVolume_denominator_parse
#print axioms geometryRow054_physicalVolume_denominator_nonzero
#print axioms geometryRow054_physicalVolume_parse
#print axioms geometryRow054_physicalVolume_read
#print axioms geometryRow054_meanGap_field
#print axioms geometryRow054_meanGap_numerator_no_slash
#print axioms geometryRow054_meanGap_numerator_parse
#print axioms geometryRow054_meanGap_denominator_parse
#print axioms geometryRow054_meanGap_denominator_nonzero
#print axioms geometryRow054_meanGap_parse
#print axioms geometryRow054_meanGap_read
#print axioms geometryRow054_jensenBound_field
#print axioms geometryRow054_jensenBound_numerator_no_slash
#print axioms geometryRow054_jensenBound_numerator_parse
#print axioms geometryRow054_jensenBound_denominator_parse
#print axioms geometryRow054_jensenBound_denominator_nonzero
#print axioms geometryRow054_jensenBound_parse
#print axioms geometryRow054_jensenBound_read
#print axioms geometryRow054_factorMaxima_read
#print axioms geometryRow054_gapWeightedMeans_read
#print axioms geometryRow054_floor_text_read
#print axioms geometryRow054_floor_chars_parse
#print axioms geometryRow054_floor_parse
#print axioms decode_geometry_Rows_054
#print axioms geometryRow054_shape
#print axioms geometryRow055_simplexId_read
#print axioms geometryRow055_vertexIds_read
#print axioms geometryRow055_physicalVolume_field
#print axioms geometryRow055_physicalVolume_numerator_no_slash
#print axioms geometryRow055_physicalVolume_numerator_parse
#print axioms geometryRow055_physicalVolume_denominator_parse
#print axioms geometryRow055_physicalVolume_denominator_nonzero
#print axioms geometryRow055_physicalVolume_parse
#print axioms geometryRow055_physicalVolume_read
#print axioms geometryRow055_meanGap_field
#print axioms geometryRow055_meanGap_numerator_no_slash
#print axioms geometryRow055_meanGap_numerator_parse
#print axioms geometryRow055_meanGap_denominator_parse
#print axioms geometryRow055_meanGap_denominator_nonzero
#print axioms geometryRow055_meanGap_parse
#print axioms geometryRow055_meanGap_read
#print axioms geometryRow055_jensenBound_field
#print axioms geometryRow055_jensenBound_numerator_no_slash
#print axioms geometryRow055_jensenBound_numerator_parse
#print axioms geometryRow055_jensenBound_denominator_parse
#print axioms geometryRow055_jensenBound_denominator_nonzero
#print axioms geometryRow055_jensenBound_parse
#print axioms geometryRow055_jensenBound_read
#print axioms geometryRow055_factorMaxima_read
#print axioms geometryRow055_gapWeightedMeans_read
#print axioms geometryRow055_floor_text_read
#print axioms geometryRow055_floor_chars_parse
#print axioms geometryRow055_floor_parse
#print axioms decode_geometry_Rows_055
#print axioms geometryRow055_shape
#print axioms geometry_Rows_block_006_push_eq
#print axioms geometry_Rows_block_006_reverse
#print axioms decode_geometry_Rows_block_006
#print axioms geometry_Rows_block_006_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
