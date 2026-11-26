import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock004

/-! Local typed certificates for original cell 05, rows 32 through 39.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson032 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped032 : GeometryRow :=
  { simplexId := 32,
    vertexIds := #[27, 25, 23, 21, 19, 18, 16, 4, 0],
    physicalVolume := ((996407860937359750472545069054729 : ℚ) / (32419110937500000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((641632495179637 : ℚ) / (7377148800000000 : ℚ)), ((80676673460099 : ℚ) / (922143600000000 : ℚ)), ((91355193609931 : ℚ) / (737714880000000 : ℚ)), ((175217434009099 : ℚ) / (1844287200000000 : ℚ)), ((168995033239241 : ℚ) / (1844287200000000 : ℚ)), ((25812238032823 : ℚ) / (368857440000000 : ℚ)), ((139117115139073 : ℚ) / (3688574400000000 : ℚ)), ((38571111829879 : ℚ) / (1229524800000000 : ℚ)), ((37545674471479 : ℚ) / (1229524800000000 : ℚ)), ((3059149157817 : ℚ) / (102460400000000 : ℚ))],
    jensenBound := ((1087457981316801871531208458446520359973978632933567876914642359614276368535229911911879200619888640000000000000000000000 : ℚ) / (19237581370065364130581426952356677611790921934322686612312584807931702877006532815404699867437539827422073632748665114970870247895533 : ℚ)),
    jensenFloorQ96 := (4478593021327850 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_simplexId_before"
  err.flush

theorem geometryRow032_simplexId_read :
    geometryRowsJson032.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped032.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_vertexIds_before"
  err.flush

theorem geometryRow032_vertexIds_read :
    geometryRowsJson032.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped032.vertexIds := by decide +kernel

noncomputable def geometryRow032_physicalVolumeNumeratorChars : List Char := ['9', '9', '6', '4', '0', '7', '8', '6', '0', '9', '3', '7', '3', '5', '9', '7', '5', '0', '4', '7', '2', '5', '4', '5', '0', '6', '9', '0', '5', '4', '7', '2', '9']
noncomputable def geometryRow032_physicalVolumeDenominatorChars : List Char := ['3', '2', '4', '1', '9', '1', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_physicalVolumeText : String := String.ofList (geometryRow032_physicalVolumeNumeratorChars ++ '/' :: geometryRow032_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_physicalVolume_before_field"
  err.flush

theorem geometryRow032_physicalVolume_field :
    geometryRowsJson032.getObjVal? "physical_volume" = .ok (.str geometryRow032_physicalVolumeText) := by rfl

theorem geometryRow032_physicalVolume_numerator_no_slash :
    geometryRow032_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeNumeratorChars = some (996407860937359750472545069054729 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeDenominatorChars = some (32419110937500000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_nonzero : (32419110937500000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_physicalVolume_parse :
    parseRational geometryRow032_physicalVolumeText = .ok geometryRowsTyped032.physicalVolume :=
  original_rational_fraction_of_chars geometryRow032_physicalVolumeNumeratorChars geometryRow032_physicalVolumeDenominatorChars
    (996407860937359750472545069054729 : Int) (32419110937500000000000000000000000000000000000000000000 : Int)
    geometryRow032_physicalVolume_numerator_no_slash geometryRow032_physicalVolume_numerator_parse
    geometryRow032_physicalVolume_denominator_parse geometryRow032_physicalVolume_denominator_nonzero

theorem geometryRow032_physicalVolume_read :
    rationalField geometryRowsJson032 "physical_volume" = .ok geometryRowsTyped032.physicalVolume :=
  original_rationalField_of_string geometryRowsJson032 "physical_volume" geometryRow032_physicalVolumeText
    geometryRowsTyped032.physicalVolume geometryRow032_physicalVolume_field geometryRow032_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_physicalVolume_complete"
  err.flush

noncomputable def geometryRow032_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow032_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_meanGapText : String := String.ofList (geometryRow032_meanGapNumeratorChars ++ '/' :: geometryRow032_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_meanGap_before_field"
  err.flush

theorem geometryRow032_meanGap_field :
    geometryRowsJson032.getObjVal? "mean_gap" = .ok (.str geometryRow032_meanGapText) := by rfl

theorem geometryRow032_meanGap_numerator_no_slash :
    geometryRow032_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_meanGap_numerator_parse :
    SourceJson.intChars geometryRow032_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_parse :
    SourceJson.intChars geometryRow032_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_meanGap_parse :
    parseRational geometryRow032_meanGapText = .ok geometryRowsTyped032.meanGap :=
  original_rational_fraction_of_chars geometryRow032_meanGapNumeratorChars geometryRow032_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow032_meanGap_numerator_no_slash geometryRow032_meanGap_numerator_parse
    geometryRow032_meanGap_denominator_parse geometryRow032_meanGap_denominator_nonzero

theorem geometryRow032_meanGap_read :
    rationalField geometryRowsJson032 "mean_gap" = .ok geometryRowsTyped032.meanGap :=
  original_rationalField_of_string geometryRowsJson032 "mean_gap" geometryRow032_meanGapText
    geometryRowsTyped032.meanGap geometryRow032_meanGap_field geometryRow032_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_meanGap_complete"
  err.flush

noncomputable def geometryRow032_jensenBoundNumeratorChars : List Char := ['1', '0', '8', '7', '4', '5', '7', '9', '8', '1', '3', '1', '6', '8', '0', '1', '8', '7', '1', '5', '3', '1', '2', '0', '8', '4', '5', '8', '4', '4', '6', '5', '2', '0', '3', '5', '9', '9', '7', '3', '9', '7', '8', '6', '3', '2', '9', '3', '3', '5', '6', '7', '8', '7', '6', '9', '1', '4', '6', '4', '2', '3', '5', '9', '6', '1', '4', '2', '7', '6', '3', '6', '8', '5', '3', '5', '2', '2', '9', '9', '1', '1', '9', '1', '1', '8', '7', '9', '2', '0', '0', '6', '1', '9', '8', '8', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_jensenBoundDenominatorChars : List Char := ['1', '9', '2', '3', '7', '5', '8', '1', '3', '7', '0', '0', '6', '5', '3', '6', '4', '1', '3', '0', '5', '8', '1', '4', '2', '6', '9', '5', '2', '3', '5', '6', '6', '7', '7', '6', '1', '1', '7', '9', '0', '9', '2', '1', '9', '3', '4', '3', '2', '2', '6', '8', '6', '6', '1', '2', '3', '1', '2', '5', '8', '4', '8', '0', '7', '9', '3', '1', '7', '0', '2', '8', '7', '7', '0', '0', '6', '5', '3', '2', '8', '1', '5', '4', '0', '4', '6', '9', '9', '8', '6', '7', '4', '3', '7', '5', '3', '9', '8', '2', '7', '4', '2', '2', '0', '7', '3', '6', '3', '2', '7', '4', '8', '6', '6', '5', '1', '1', '4', '9', '7', '0', '8', '7', '0', '2', '4', '7', '8', '9', '5', '5', '3', '3']
noncomputable def geometryRow032_jensenBoundText : String := String.ofList (geometryRow032_jensenBoundNumeratorChars ++ '/' :: geometryRow032_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_jensenBound_before_field"
  err.flush

theorem geometryRow032_jensenBound_field :
    geometryRowsJson032.getObjVal? "jensen_bound" = .ok (.str geometryRow032_jensenBoundText) := by rfl

theorem geometryRow032_jensenBound_numerator_no_slash :
    geometryRow032_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow032_jensenBoundNumeratorChars = some (1087457981316801871531208458446520359973978632933567876914642359614276368535229911911879200619888640000000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow032_jensenBoundDenominatorChars = some (19237581370065364130581426952356677611790921934322686612312584807931702877006532815404699867437539827422073632748665114970870247895533 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_nonzero : (19237581370065364130581426952356677611790921934322686612312584807931702877006532815404699867437539827422073632748665114970870247895533 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_jensenBound_parse :
    parseRational geometryRow032_jensenBoundText = .ok geometryRowsTyped032.jensenBound :=
  original_rational_fraction_of_chars geometryRow032_jensenBoundNumeratorChars geometryRow032_jensenBoundDenominatorChars
    (1087457981316801871531208458446520359973978632933567876914642359614276368535229911911879200619888640000000000000000000000 : Int) (19237581370065364130581426952356677611790921934322686612312584807931702877006532815404699867437539827422073632748665114970870247895533 : Int)
    geometryRow032_jensenBound_numerator_no_slash geometryRow032_jensenBound_numerator_parse
    geometryRow032_jensenBound_denominator_parse geometryRow032_jensenBound_denominator_nonzero

theorem geometryRow032_jensenBound_read :
    rationalField geometryRowsJson032 "jensen_bound" = .ok geometryRowsTyped032.jensenBound :=
  original_rationalField_of_string geometryRowsJson032 "jensen_bound" geometryRow032_jensenBoundText
    geometryRowsTyped032.jensenBound geometryRow032_jensenBound_field geometryRow032_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_factorMaxima_before"
  err.flush

theorem geometryRow032_factorMaxima_read :
    rationalArrayField geometryRowsJson032 "factor_maxima" = .ok geometryRowsTyped032.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_gapWeightedMeans_before"
  err.flush

theorem geometryRow032_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson032 "gap_weighted_means" = .ok geometryRowsTyped032.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow032_floorChars : List Char := ['4', '4', '7', '8', '5', '9', '3', '0', '2', '1', '3', '2', '7', '8', '5', '0']
noncomputable def geometryRow032_floorText : String := String.ofList geometryRow032_floorChars

theorem geometryRow032_floor_text_read :
    geometryRowsJson032.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow032_floorText := by rfl

theorem geometryRow032_floor_chars_parse :
    SourceJson.intChars geometryRow032_floorChars = some (4478593021327850 : Int) := by decide +kernel

theorem geometryRow032_floor_parse :
    parseInteger geometryRow032_floorText = .ok geometryRowsTyped032.jensenFloorQ96 := by
  simp only [geometryRow032_floorText, parseInteger, String.toList_ofList, geometryRow032_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_032 :
    decodeGeometryRow geometryRowsJson032 = .ok geometryRowsTyped032 :=
  original_geometryRow_of_fields geometryRowsJson032 geometryRowsTyped032 geometryRow032_floorText
    geometryRow032_simplexId_read geometryRow032_vertexIds_read
    geometryRow032_physicalVolume_read geometryRow032_meanGap_read
    geometryRow032_factorMaxima_read geometryRow032_gapWeightedMeans_read
    geometryRow032_jensenBound_read geometryRow032_floor_text_read geometryRow032_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_032_original_decoder_complete"
  err.flush

theorem geometryRow032_shape :
    geometryRowsTyped032.simplexId = 32 ∧
    geometryRowsTyped032.vertexIds.size = 9 ∧ geometryRowsTyped032.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped032.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped032.factorMaxima.size = 10 ∧ geometryRowsTyped032.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson033 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped033 : GeometryRow :=
  { simplexId := 33,
    vertexIds := #[27, 25, 23, 21, 19, 18, 16, 14, 4],
    physicalVolume := ((632960657845306101123349661156659 : ℚ) / (36905684326171875000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((51871037 : ℚ) / (97920000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((515597 : ℚ) / (12000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((79744283914219916844823 : ℚ) / (929318013158313600000000 : ℚ)), ((10051264603216057124027 : ℚ) / (116164751644789200000000 : ℚ)), ((58177879938062477463797 : ℚ) / (464659006579156800000000 : ℚ)), ((22560203478594176020297 : ℚ) / (232329503289578400000000 : ℚ)), ((21649989075456385811699 : ℚ) / (232329503289578400000000 : ℚ)), ((3169012106629557355969 : ℚ) / (46465900657915680000000 : ℚ)), ((987328558337460010379 : ℚ) / (27332882739950400000000 : ℚ)), ((4830280966606802859269 : ℚ) / (154886335526385600000000 : ℚ)), ((4701104040078413254469 : ℚ) / (154886335526385600000000 : ℚ)), ((1143686267532985323683 : ℚ) / (38721583881596400000000 : ℚ))],
    jensenBound := ((116085480472440609371068622500854641257054608239166745594343307319734886415006093143203305097382558152612790284537361675824956196528666363873204965786393578336654542983179791430997508096000000000000000000000 : ℚ) / (1850732338558790198049702287298161342860312981614422920269263894800394233122806355245157047142365766909291259665048627632239013915605978038822169187677314007317186005848371894323260697115556710687257813802156981359500643 : ℚ)),
    jensenFloorQ96 := (4969513484364300 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_simplexId_before"
  err.flush

theorem geometryRow033_simplexId_read :
    geometryRowsJson033.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped033.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_vertexIds_before"
  err.flush

theorem geometryRow033_vertexIds_read :
    geometryRowsJson033.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped033.vertexIds := by decide +kernel

noncomputable def geometryRow033_physicalVolumeNumeratorChars : List Char := ['6', '3', '2', '9', '6', '0', '6', '5', '7', '8', '4', '5', '3', '0', '6', '1', '0', '1', '1', '2', '3', '3', '4', '9', '6', '6', '1', '1', '5', '6', '6', '5', '9']
noncomputable def geometryRow033_physicalVolumeDenominatorChars : List Char := ['3', '6', '9', '0', '5', '6', '8', '4', '3', '2', '6', '1', '7', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_physicalVolumeText : String := String.ofList (geometryRow033_physicalVolumeNumeratorChars ++ '/' :: geometryRow033_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_physicalVolume_before_field"
  err.flush

theorem geometryRow033_physicalVolume_field :
    geometryRowsJson033.getObjVal? "physical_volume" = .ok (.str geometryRow033_physicalVolumeText) := by rfl

theorem geometryRow033_physicalVolume_numerator_no_slash :
    geometryRow033_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeNumeratorChars = some (632960657845306101123349661156659 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeDenominatorChars = some (36905684326171875000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_nonzero : (36905684326171875000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_physicalVolume_parse :
    parseRational geometryRow033_physicalVolumeText = .ok geometryRowsTyped033.physicalVolume :=
  original_rational_fraction_of_chars geometryRow033_physicalVolumeNumeratorChars geometryRow033_physicalVolumeDenominatorChars
    (632960657845306101123349661156659 : Int) (36905684326171875000000000000000000000000000000000000000 : Int)
    geometryRow033_physicalVolume_numerator_no_slash geometryRow033_physicalVolume_numerator_parse
    geometryRow033_physicalVolume_denominator_parse geometryRow033_physicalVolume_denominator_nonzero

theorem geometryRow033_physicalVolume_read :
    rationalField geometryRowsJson033 "physical_volume" = .ok geometryRowsTyped033.physicalVolume :=
  original_rationalField_of_string geometryRowsJson033 "physical_volume" geometryRow033_physicalVolumeText
    geometryRowsTyped033.physicalVolume geometryRow033_physicalVolume_field geometryRow033_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_physicalVolume_complete"
  err.flush

noncomputable def geometryRow033_meanGapNumeratorChars : List Char := ['5', '1', '8', '7', '1', '0', '3', '7']
noncomputable def geometryRow033_meanGapDenominatorChars : List Char := ['9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_meanGapText : String := String.ofList (geometryRow033_meanGapNumeratorChars ++ '/' :: geometryRow033_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_meanGap_before_field"
  err.flush

theorem geometryRow033_meanGap_field :
    geometryRowsJson033.getObjVal? "mean_gap" = .ok (.str geometryRow033_meanGapText) := by rfl

theorem geometryRow033_meanGap_numerator_no_slash :
    geometryRow033_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_meanGap_numerator_parse :
    SourceJson.intChars geometryRow033_meanGapNumeratorChars = some (51871037 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_parse :
    SourceJson.intChars geometryRow033_meanGapDenominatorChars = some (97920000000 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_nonzero : (97920000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_meanGap_parse :
    parseRational geometryRow033_meanGapText = .ok geometryRowsTyped033.meanGap :=
  original_rational_fraction_of_chars geometryRow033_meanGapNumeratorChars geometryRow033_meanGapDenominatorChars
    (51871037 : Int) (97920000000 : Int)
    geometryRow033_meanGap_numerator_no_slash geometryRow033_meanGap_numerator_parse
    geometryRow033_meanGap_denominator_parse geometryRow033_meanGap_denominator_nonzero

theorem geometryRow033_meanGap_read :
    rationalField geometryRowsJson033 "mean_gap" = .ok geometryRowsTyped033.meanGap :=
  original_rationalField_of_string geometryRowsJson033 "mean_gap" geometryRow033_meanGapText
    geometryRowsTyped033.meanGap geometryRow033_meanGap_field geometryRow033_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_meanGap_complete"
  err.flush

noncomputable def geometryRow033_jensenBoundNumeratorChars : List Char := ['1', '1', '6', '0', '8', '5', '4', '8', '0', '4', '7', '2', '4', '4', '0', '6', '0', '9', '3', '7', '1', '0', '6', '8', '6', '2', '2', '5', '0', '0', '8', '5', '4', '6', '4', '1', '2', '5', '7', '0', '5', '4', '6', '0', '8', '2', '3', '9', '1', '6', '6', '7', '4', '5', '5', '9', '4', '3', '4', '3', '3', '0', '7', '3', '1', '9', '7', '3', '4', '8', '8', '6', '4', '1', '5', '0', '0', '6', '0', '9', '3', '1', '4', '3', '2', '0', '3', '3', '0', '5', '0', '9', '7', '3', '8', '2', '5', '5', '8', '1', '5', '2', '6', '1', '2', '7', '9', '0', '2', '8', '4', '5', '3', '7', '3', '6', '1', '6', '7', '5', '8', '2', '4', '9', '5', '6', '1', '9', '6', '5', '2', '8', '6', '6', '6', '3', '6', '3', '8', '7', '3', '2', '0', '4', '9', '6', '5', '7', '8', '6', '3', '9', '3', '5', '7', '8', '3', '3', '6', '6', '5', '4', '5', '4', '2', '9', '8', '3', '1', '7', '9', '7', '9', '1', '4', '3', '0', '9', '9', '7', '5', '0', '8', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_jensenBoundDenominatorChars : List Char := ['1', '8', '5', '0', '7', '3', '2', '3', '3', '8', '5', '5', '8', '7', '9', '0', '1', '9', '8', '0', '4', '9', '7', '0', '2', '2', '8', '7', '2', '9', '8', '1', '6', '1', '3', '4', '2', '8', '6', '0', '3', '1', '2', '9', '8', '1', '6', '1', '4', '4', '2', '2', '9', '2', '0', '2', '6', '9', '2', '6', '3', '8', '9', '4', '8', '0', '0', '3', '9', '4', '2', '3', '3', '1', '2', '2', '8', '0', '6', '3', '5', '5', '2', '4', '5', '1', '5', '7', '0', '4', '7', '1', '4', '2', '3', '6', '5', '7', '6', '6', '9', '0', '9', '2', '9', '1', '2', '5', '9', '6', '6', '5', '0', '4', '8', '6', '2', '7', '6', '3', '2', '2', '3', '9', '0', '1', '3', '9', '1', '5', '6', '0', '5', '9', '7', '8', '0', '3', '8', '8', '2', '2', '1', '6', '9', '1', '8', '7', '6', '7', '7', '3', '1', '4', '0', '0', '7', '3', '1', '7', '1', '8', '6', '0', '0', '5', '8', '4', '8', '3', '7', '1', '8', '9', '4', '3', '2', '3', '2', '6', '0', '6', '9', '7', '1', '1', '5', '5', '5', '6', '7', '1', '0', '6', '8', '7', '2', '5', '7', '8', '1', '3', '8', '0', '2', '1', '5', '6', '9', '8', '1', '3', '5', '9', '5', '0', '0', '6', '4', '3']
noncomputable def geometryRow033_jensenBoundText : String := String.ofList (geometryRow033_jensenBoundNumeratorChars ++ '/' :: geometryRow033_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_jensenBound_before_field"
  err.flush

theorem geometryRow033_jensenBound_field :
    geometryRowsJson033.getObjVal? "jensen_bound" = .ok (.str geometryRow033_jensenBoundText) := by rfl

theorem geometryRow033_jensenBound_numerator_no_slash :
    geometryRow033_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow033_jensenBoundNumeratorChars = some (116085480472440609371068622500854641257054608239166745594343307319734886415006093143203305097382558152612790284537361675824956196528666363873204965786393578336654542983179791430997508096000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow033_jensenBoundDenominatorChars = some (1850732338558790198049702287298161342860312981614422920269263894800394233122806355245157047142365766909291259665048627632239013915605978038822169187677314007317186005848371894323260697115556710687257813802156981359500643 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_nonzero : (1850732338558790198049702287298161342860312981614422920269263894800394233122806355245157047142365766909291259665048627632239013915605978038822169187677314007317186005848371894323260697115556710687257813802156981359500643 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_jensenBound_parse :
    parseRational geometryRow033_jensenBoundText = .ok geometryRowsTyped033.jensenBound :=
  original_rational_fraction_of_chars geometryRow033_jensenBoundNumeratorChars geometryRow033_jensenBoundDenominatorChars
    (116085480472440609371068622500854641257054608239166745594343307319734886415006093143203305097382558152612790284537361675824956196528666363873204965786393578336654542983179791430997508096000000000000000000000 : Int) (1850732338558790198049702287298161342860312981614422920269263894800394233122806355245157047142365766909291259665048627632239013915605978038822169187677314007317186005848371894323260697115556710687257813802156981359500643 : Int)
    geometryRow033_jensenBound_numerator_no_slash geometryRow033_jensenBound_numerator_parse
    geometryRow033_jensenBound_denominator_parse geometryRow033_jensenBound_denominator_nonzero

theorem geometryRow033_jensenBound_read :
    rationalField geometryRowsJson033 "jensen_bound" = .ok geometryRowsTyped033.jensenBound :=
  original_rationalField_of_string geometryRowsJson033 "jensen_bound" geometryRow033_jensenBoundText
    geometryRowsTyped033.jensenBound geometryRow033_jensenBound_field geometryRow033_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_factorMaxima_before"
  err.flush

theorem geometryRow033_factorMaxima_read :
    rationalArrayField geometryRowsJson033 "factor_maxima" = .ok geometryRowsTyped033.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_gapWeightedMeans_before"
  err.flush

theorem geometryRow033_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson033 "gap_weighted_means" = .ok geometryRowsTyped033.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow033_floorChars : List Char := ['4', '9', '6', '9', '5', '1', '3', '4', '8', '4', '3', '6', '4', '3', '0', '0']
noncomputable def geometryRow033_floorText : String := String.ofList geometryRow033_floorChars

theorem geometryRow033_floor_text_read :
    geometryRowsJson033.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow033_floorText := by rfl

theorem geometryRow033_floor_chars_parse :
    SourceJson.intChars geometryRow033_floorChars = some (4969513484364300 : Int) := by decide +kernel

theorem geometryRow033_floor_parse :
    parseInteger geometryRow033_floorText = .ok geometryRowsTyped033.jensenFloorQ96 := by
  simp only [geometryRow033_floorText, parseInteger, String.toList_ofList, geometryRow033_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_033 :
    decodeGeometryRow geometryRowsJson033 = .ok geometryRowsTyped033 :=
  original_geometryRow_of_fields geometryRowsJson033 geometryRowsTyped033 geometryRow033_floorText
    geometryRow033_simplexId_read geometryRow033_vertexIds_read
    geometryRow033_physicalVolume_read geometryRow033_meanGap_read
    geometryRow033_factorMaxima_read geometryRow033_gapWeightedMeans_read
    geometryRow033_jensenBound_read geometryRow033_floor_text_read geometryRow033_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_033_original_decoder_complete"
  err.flush

theorem geometryRow033_shape :
    geometryRowsTyped033.simplexId = 33 ∧
    geometryRowsTyped033.vertexIds.size = 9 ∧ geometryRowsTyped033.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped033.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped033.factorMaxima.size = 10 ∧ geometryRowsTyped033.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson034 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped034 : GeometryRow :=
  { simplexId := 34,
    vertexIds := #[27, 25, 23, 21, 20, 6, 4, 2, 0],
    physicalVolume := ((40256509351163747279804034730429601 : ℚ) / (3385973586240000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((3175527458033 : ℚ) / (35107200000000 : ℚ)), ((199595024483 : ℚ) / (2194200000000 : ℚ)), ((998212450637 : ℚ) / (8191680000000 : ℚ)), ((2822078460641 : ℚ) / (30718800000000 : ℚ)), ((151392357863 : ℚ) / (1706600000000 : ℚ)), ((29538855503 : ℚ) / (409584000000 : ℚ)), ((1510600520693 : ℚ) / (40958400000000 : ℚ)), ((567226071133 : ℚ) / (17553600000000 : ℚ)), ((557687902813 : ℚ) / (17553600000000 : ℚ)), ((68054807201 : ℚ) / (2194200000000 : ℚ))],
    jensenBound := ((856920067333053192978401717608132691880576822626397531913905768940343132160000000000000000000000 : ℚ) / (43795517528083373179522630953732495575511425908732612622733105847642852434615119138804912234152296997956521033851 : ℚ)),
    jensenFloorQ96 := (1550208929780 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_simplexId_before"
  err.flush

theorem geometryRow034_simplexId_read :
    geometryRowsJson034.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped034.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_vertexIds_before"
  err.flush

theorem geometryRow034_vertexIds_read :
    geometryRowsJson034.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped034.vertexIds := by decide +kernel

noncomputable def geometryRow034_physicalVolumeNumeratorChars : List Char := ['4', '0', '2', '5', '6', '5', '0', '9', '3', '5', '1', '1', '6', '3', '7', '4', '7', '2', '7', '9', '8', '0', '4', '0', '3', '4', '7', '3', '0', '4', '2', '9', '6', '0', '1']
noncomputable def geometryRow034_physicalVolumeDenominatorChars : List Char := ['3', '3', '8', '5', '9', '7', '3', '5', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_physicalVolumeText : String := String.ofList (geometryRow034_physicalVolumeNumeratorChars ++ '/' :: geometryRow034_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_physicalVolume_before_field"
  err.flush

theorem geometryRow034_physicalVolume_field :
    geometryRowsJson034.getObjVal? "physical_volume" = .ok (.str geometryRow034_physicalVolumeText) := by rfl

theorem geometryRow034_physicalVolume_numerator_no_slash :
    geometryRow034_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeNumeratorChars = some (40256509351163747279804034730429601 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeDenominatorChars = some (3385973586240000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_nonzero : (3385973586240000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_physicalVolume_parse :
    parseRational geometryRow034_physicalVolumeText = .ok geometryRowsTyped034.physicalVolume :=
  original_rational_fraction_of_chars geometryRow034_physicalVolumeNumeratorChars geometryRow034_physicalVolumeDenominatorChars
    (40256509351163747279804034730429601 : Int) (3385973586240000000000000000000000000000000000000000000000000 : Int)
    geometryRow034_physicalVolume_numerator_no_slash geometryRow034_physicalVolume_numerator_parse
    geometryRow034_physicalVolume_denominator_parse geometryRow034_physicalVolume_denominator_nonzero

theorem geometryRow034_physicalVolume_read :
    rationalField geometryRowsJson034 "physical_volume" = .ok geometryRowsTyped034.physicalVolume :=
  original_rationalField_of_string geometryRowsJson034 "physical_volume" geometryRow034_physicalVolumeText
    geometryRowsTyped034.physicalVolume geometryRow034_physicalVolume_field geometryRow034_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_physicalVolume_complete"
  err.flush

noncomputable def geometryRow034_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow034_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_meanGapText : String := String.ofList (geometryRow034_meanGapNumeratorChars ++ '/' :: geometryRow034_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_meanGap_before_field"
  err.flush

theorem geometryRow034_meanGap_field :
    geometryRowsJson034.getObjVal? "mean_gap" = .ok (.str geometryRow034_meanGapText) := by rfl

theorem geometryRow034_meanGap_numerator_no_slash :
    geometryRow034_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_meanGap_numerator_parse :
    SourceJson.intChars geometryRow034_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_parse :
    SourceJson.intChars geometryRow034_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_meanGap_parse :
    parseRational geometryRow034_meanGapText = .ok geometryRowsTyped034.meanGap :=
  original_rational_fraction_of_chars geometryRow034_meanGapNumeratorChars geometryRow034_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow034_meanGap_numerator_no_slash geometryRow034_meanGap_numerator_parse
    geometryRow034_meanGap_denominator_parse geometryRow034_meanGap_denominator_nonzero

theorem geometryRow034_meanGap_read :
    rationalField geometryRowsJson034 "mean_gap" = .ok geometryRowsTyped034.meanGap :=
  original_rationalField_of_string geometryRowsJson034 "mean_gap" geometryRow034_meanGapText
    geometryRowsTyped034.meanGap geometryRow034_meanGap_field geometryRow034_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_meanGap_complete"
  err.flush

noncomputable def geometryRow034_jensenBoundNumeratorChars : List Char := ['8', '5', '6', '9', '2', '0', '0', '6', '7', '3', '3', '3', '0', '5', '3', '1', '9', '2', '9', '7', '8', '4', '0', '1', '7', '1', '7', '6', '0', '8', '1', '3', '2', '6', '9', '1', '8', '8', '0', '5', '7', '6', '8', '2', '2', '6', '2', '6', '3', '9', '7', '5', '3', '1', '9', '1', '3', '9', '0', '5', '7', '6', '8', '9', '4', '0', '3', '4', '3', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_jensenBoundDenominatorChars : List Char := ['4', '3', '7', '9', '5', '5', '1', '7', '5', '2', '8', '0', '8', '3', '3', '7', '3', '1', '7', '9', '5', '2', '2', '6', '3', '0', '9', '5', '3', '7', '3', '2', '4', '9', '5', '5', '7', '5', '5', '1', '1', '4', '2', '5', '9', '0', '8', '7', '3', '2', '6', '1', '2', '6', '2', '2', '7', '3', '3', '1', '0', '5', '8', '4', '7', '6', '4', '2', '8', '5', '2', '4', '3', '4', '6', '1', '5', '1', '1', '9', '1', '3', '8', '8', '0', '4', '9', '1', '2', '2', '3', '4', '1', '5', '2', '2', '9', '6', '9', '9', '7', '9', '5', '6', '5', '2', '1', '0', '3', '3', '8', '5', '1']
noncomputable def geometryRow034_jensenBoundText : String := String.ofList (geometryRow034_jensenBoundNumeratorChars ++ '/' :: geometryRow034_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_jensenBound_before_field"
  err.flush

theorem geometryRow034_jensenBound_field :
    geometryRowsJson034.getObjVal? "jensen_bound" = .ok (.str geometryRow034_jensenBoundText) := by rfl

theorem geometryRow034_jensenBound_numerator_no_slash :
    geometryRow034_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow034_jensenBoundNumeratorChars = some (856920067333053192978401717608132691880576822626397531913905768940343132160000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow034_jensenBoundDenominatorChars = some (43795517528083373179522630953732495575511425908732612622733105847642852434615119138804912234152296997956521033851 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_nonzero : (43795517528083373179522630953732495575511425908732612622733105847642852434615119138804912234152296997956521033851 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_jensenBound_parse :
    parseRational geometryRow034_jensenBoundText = .ok geometryRowsTyped034.jensenBound :=
  original_rational_fraction_of_chars geometryRow034_jensenBoundNumeratorChars geometryRow034_jensenBoundDenominatorChars
    (856920067333053192978401717608132691880576822626397531913905768940343132160000000000000000000000 : Int) (43795517528083373179522630953732495575511425908732612622733105847642852434615119138804912234152296997956521033851 : Int)
    geometryRow034_jensenBound_numerator_no_slash geometryRow034_jensenBound_numerator_parse
    geometryRow034_jensenBound_denominator_parse geometryRow034_jensenBound_denominator_nonzero

theorem geometryRow034_jensenBound_read :
    rationalField geometryRowsJson034 "jensen_bound" = .ok geometryRowsTyped034.jensenBound :=
  original_rationalField_of_string geometryRowsJson034 "jensen_bound" geometryRow034_jensenBoundText
    geometryRowsTyped034.jensenBound geometryRow034_jensenBound_field geometryRow034_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_factorMaxima_before"
  err.flush

theorem geometryRow034_factorMaxima_read :
    rationalArrayField geometryRowsJson034 "factor_maxima" = .ok geometryRowsTyped034.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_gapWeightedMeans_before"
  err.flush

theorem geometryRow034_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson034 "gap_weighted_means" = .ok geometryRowsTyped034.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow034_floorChars : List Char := ['1', '5', '5', '0', '2', '0', '8', '9', '2', '9', '7', '8', '0']
noncomputable def geometryRow034_floorText : String := String.ofList geometryRow034_floorChars

theorem geometryRow034_floor_text_read :
    geometryRowsJson034.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow034_floorText := by rfl

theorem geometryRow034_floor_chars_parse :
    SourceJson.intChars geometryRow034_floorChars = some (1550208929780 : Int) := by decide +kernel

theorem geometryRow034_floor_parse :
    parseInteger geometryRow034_floorText = .ok geometryRowsTyped034.jensenFloorQ96 := by
  simp only [geometryRow034_floorText, parseInteger, String.toList_ofList, geometryRow034_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_034 :
    decodeGeometryRow geometryRowsJson034 = .ok geometryRowsTyped034 :=
  original_geometryRow_of_fields geometryRowsJson034 geometryRowsTyped034 geometryRow034_floorText
    geometryRow034_simplexId_read geometryRow034_vertexIds_read
    geometryRow034_physicalVolume_read geometryRow034_meanGap_read
    geometryRow034_factorMaxima_read geometryRow034_gapWeightedMeans_read
    geometryRow034_jensenBound_read geometryRow034_floor_text_read geometryRow034_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_034_original_decoder_complete"
  err.flush

theorem geometryRow034_shape :
    geometryRowsTyped034.simplexId = 34 ∧
    geometryRowsTyped034.vertexIds.size = 9 ∧ geometryRowsTyped034.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped034.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped034.factorMaxima.size = 10 ∧ geometryRowsTyped034.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson035 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped035 : GeometryRow :=
  { simplexId := 35,
    vertexIds := #[27, 25, 23, 21, 20, 18, 6, 4, 0],
    physicalVolume := ((212493815754578258778386226773077 : ℚ) / (27187721938125000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2531241 : ℚ) / (26500000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((115033435547501 : ℚ) / (1298966400000000 : ℚ)), ((14462396761777 : ℚ) / (162370800000000 : ℚ)), ((111834191427893 : ℚ) / (909276480000000 : ℚ)), ((212850959838569 : ℚ) / (2273191200000000 : ℚ)), ((204904115708491 : ℚ) / (2273191200000000 : ℚ)), ((32156676097313 : ℚ) / (454638240000000 : ℚ)), ((167876032195223 : ℚ) / (4546382400000000 : ℚ)), ((6932171875687 : ℚ) / (216494400000000 : ℚ)), ((6814534466407 : ℚ) / (216494400000000 : ℚ)), ((1644503572073 : ℚ) / (54123600000000 : ℚ))],
    jensenBound := ((34751564705519962791662757952106177581158884376169062088051686341564520717381573678360585830400000000000000000000000 : ℚ) / (2556744829602020151632610797752952694110194333573718031161020886265964203533935952398576557445404761782702023979245363968314150829807 : ℚ)),
    jensenFloorQ96 := (1076878139826 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_simplexId_before"
  err.flush

theorem geometryRow035_simplexId_read :
    geometryRowsJson035.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped035.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_vertexIds_before"
  err.flush

theorem geometryRow035_vertexIds_read :
    geometryRowsJson035.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped035.vertexIds := by decide +kernel

noncomputable def geometryRow035_physicalVolumeNumeratorChars : List Char := ['2', '1', '2', '4', '9', '3', '8', '1', '5', '7', '5', '4', '5', '7', '8', '2', '5', '8', '7', '7', '8', '3', '8', '6', '2', '2', '6', '7', '7', '3', '0', '7', '7']
noncomputable def geometryRow035_physicalVolumeDenominatorChars : List Char := ['2', '7', '1', '8', '7', '7', '2', '1', '9', '3', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_physicalVolumeText : String := String.ofList (geometryRow035_physicalVolumeNumeratorChars ++ '/' :: geometryRow035_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_physicalVolume_before_field"
  err.flush

theorem geometryRow035_physicalVolume_field :
    geometryRowsJson035.getObjVal? "physical_volume" = .ok (.str geometryRow035_physicalVolumeText) := by rfl

theorem geometryRow035_physicalVolume_numerator_no_slash :
    geometryRow035_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeNumeratorChars = some (212493815754578258778386226773077 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeDenominatorChars = some (27187721938125000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_nonzero : (27187721938125000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_physicalVolume_parse :
    parseRational geometryRow035_physicalVolumeText = .ok geometryRowsTyped035.physicalVolume :=
  original_rational_fraction_of_chars geometryRow035_physicalVolumeNumeratorChars geometryRow035_physicalVolumeDenominatorChars
    (212493815754578258778386226773077 : Int) (27187721938125000000000000000000000000000000000000000000000 : Int)
    geometryRow035_physicalVolume_numerator_no_slash geometryRow035_physicalVolume_numerator_parse
    geometryRow035_physicalVolume_denominator_parse geometryRow035_physicalVolume_denominator_nonzero

theorem geometryRow035_physicalVolume_read :
    rationalField geometryRowsJson035 "physical_volume" = .ok geometryRowsTyped035.physicalVolume :=
  original_rationalField_of_string geometryRowsJson035 "physical_volume" geometryRow035_physicalVolumeText
    geometryRowsTyped035.physicalVolume geometryRow035_physicalVolume_field geometryRow035_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_physicalVolume_complete"
  err.flush

noncomputable def geometryRow035_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow035_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_meanGapText : String := String.ofList (geometryRow035_meanGapNumeratorChars ++ '/' :: geometryRow035_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_meanGap_before_field"
  err.flush

theorem geometryRow035_meanGap_field :
    geometryRowsJson035.getObjVal? "mean_gap" = .ok (.str geometryRow035_meanGapText) := by rfl

theorem geometryRow035_meanGap_numerator_no_slash :
    geometryRow035_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_meanGap_numerator_parse :
    SourceJson.intChars geometryRow035_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_parse :
    SourceJson.intChars geometryRow035_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_meanGap_parse :
    parseRational geometryRow035_meanGapText = .ok geometryRowsTyped035.meanGap :=
  original_rational_fraction_of_chars geometryRow035_meanGapNumeratorChars geometryRow035_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow035_meanGap_numerator_no_slash geometryRow035_meanGap_numerator_parse
    geometryRow035_meanGap_denominator_parse geometryRow035_meanGap_denominator_nonzero

theorem geometryRow035_meanGap_read :
    rationalField geometryRowsJson035 "mean_gap" = .ok geometryRowsTyped035.meanGap :=
  original_rationalField_of_string geometryRowsJson035 "mean_gap" geometryRow035_meanGapText
    geometryRowsTyped035.meanGap geometryRow035_meanGap_field geometryRow035_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_meanGap_complete"
  err.flush

noncomputable def geometryRow035_jensenBoundNumeratorChars : List Char := ['3', '4', '7', '5', '1', '5', '6', '4', '7', '0', '5', '5', '1', '9', '9', '6', '2', '7', '9', '1', '6', '6', '2', '7', '5', '7', '9', '5', '2', '1', '0', '6', '1', '7', '7', '5', '8', '1', '1', '5', '8', '8', '8', '4', '3', '7', '6', '1', '6', '9', '0', '6', '2', '0', '8', '8', '0', '5', '1', '6', '8', '6', '3', '4', '1', '5', '6', '4', '5', '2', '0', '7', '1', '7', '3', '8', '1', '5', '7', '3', '6', '7', '8', '3', '6', '0', '5', '8', '5', '8', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_jensenBoundDenominatorChars : List Char := ['2', '5', '5', '6', '7', '4', '4', '8', '2', '9', '6', '0', '2', '0', '2', '0', '1', '5', '1', '6', '3', '2', '6', '1', '0', '7', '9', '7', '7', '5', '2', '9', '5', '2', '6', '9', '4', '1', '1', '0', '1', '9', '4', '3', '3', '3', '5', '7', '3', '7', '1', '8', '0', '3', '1', '1', '6', '1', '0', '2', '0', '8', '8', '6', '2', '6', '5', '9', '6', '4', '2', '0', '3', '5', '3', '3', '9', '3', '5', '9', '5', '2', '3', '9', '8', '5', '7', '6', '5', '5', '7', '4', '4', '5', '4', '0', '4', '7', '6', '1', '7', '8', '2', '7', '0', '2', '0', '2', '3', '9', '7', '9', '2', '4', '5', '3', '6', '3', '9', '6', '8', '3', '1', '4', '1', '5', '0', '8', '2', '9', '8', '0', '7']
noncomputable def geometryRow035_jensenBoundText : String := String.ofList (geometryRow035_jensenBoundNumeratorChars ++ '/' :: geometryRow035_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_jensenBound_before_field"
  err.flush

theorem geometryRow035_jensenBound_field :
    geometryRowsJson035.getObjVal? "jensen_bound" = .ok (.str geometryRow035_jensenBoundText) := by rfl

theorem geometryRow035_jensenBound_numerator_no_slash :
    geometryRow035_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow035_jensenBoundNumeratorChars = some (34751564705519962791662757952106177581158884376169062088051686341564520717381573678360585830400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow035_jensenBoundDenominatorChars = some (2556744829602020151632610797752952694110194333573718031161020886265964203533935952398576557445404761782702023979245363968314150829807 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_nonzero : (2556744829602020151632610797752952694110194333573718031161020886265964203533935952398576557445404761782702023979245363968314150829807 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_jensenBound_parse :
    parseRational geometryRow035_jensenBoundText = .ok geometryRowsTyped035.jensenBound :=
  original_rational_fraction_of_chars geometryRow035_jensenBoundNumeratorChars geometryRow035_jensenBoundDenominatorChars
    (34751564705519962791662757952106177581158884376169062088051686341564520717381573678360585830400000000000000000000000 : Int) (2556744829602020151632610797752952694110194333573718031161020886265964203533935952398576557445404761782702023979245363968314150829807 : Int)
    geometryRow035_jensenBound_numerator_no_slash geometryRow035_jensenBound_numerator_parse
    geometryRow035_jensenBound_denominator_parse geometryRow035_jensenBound_denominator_nonzero

theorem geometryRow035_jensenBound_read :
    rationalField geometryRowsJson035 "jensen_bound" = .ok geometryRowsTyped035.jensenBound :=
  original_rationalField_of_string geometryRowsJson035 "jensen_bound" geometryRow035_jensenBoundText
    geometryRowsTyped035.jensenBound geometryRow035_jensenBound_field geometryRow035_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_factorMaxima_before"
  err.flush

theorem geometryRow035_factorMaxima_read :
    rationalArrayField geometryRowsJson035 "factor_maxima" = .ok geometryRowsTyped035.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_gapWeightedMeans_before"
  err.flush

theorem geometryRow035_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson035 "gap_weighted_means" = .ok geometryRowsTyped035.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow035_floorChars : List Char := ['1', '0', '7', '6', '8', '7', '8', '1', '3', '9', '8', '2', '6']
noncomputable def geometryRow035_floorText : String := String.ofList geometryRow035_floorChars

theorem geometryRow035_floor_text_read :
    geometryRowsJson035.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow035_floorText := by rfl

theorem geometryRow035_floor_chars_parse :
    SourceJson.intChars geometryRow035_floorChars = some (1076878139826 : Int) := by decide +kernel

theorem geometryRow035_floor_parse :
    parseInteger geometryRow035_floorText = .ok geometryRowsTyped035.jensenFloorQ96 := by
  simp only [geometryRow035_floorText, parseInteger, String.toList_ofList, geometryRow035_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_035 :
    decodeGeometryRow geometryRowsJson035 = .ok geometryRowsTyped035 :=
  original_geometryRow_of_fields geometryRowsJson035 geometryRowsTyped035 geometryRow035_floorText
    geometryRow035_simplexId_read geometryRow035_vertexIds_read
    geometryRow035_physicalVolume_read geometryRow035_meanGap_read
    geometryRow035_factorMaxima_read geometryRow035_gapWeightedMeans_read
    geometryRow035_jensenBound_read geometryRow035_floor_text_read geometryRow035_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_035_original_decoder_complete"
  err.flush

theorem geometryRow035_shape :
    geometryRowsTyped035.simplexId = 35 ∧
    geometryRowsTyped035.vertexIds.size = 9 ∧ geometryRowsTyped035.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped035.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped035.factorMaxima.size = 10 ∧ geometryRowsTyped035.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson036 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped036 : GeometryRow :=
  { simplexId := 36,
    vertexIds := #[27, 25, 23, 21, 20, 18, 16, 4, 0],
    physicalVolume := ((62788764939289990711027353733 : ℚ) / (8905831347656250000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((2137391381257 : ℚ) / (24508800000000 : ℚ)), ((268744060739 : ℚ) / (3063600000000 : ℚ)), ((2125251376417 : ℚ) / (17156160000000 : ℚ)), ((4073266210873 : ℚ) / (42890400000000 : ℚ)), ((3941021903027 : ℚ) / (42890400000000 : ℚ)), ((120359602673 : ℚ) / (1715616000000 : ℚ)), ((3192106622611 : ℚ) / (85780800000000 : ℚ)), ((127274192899 : ℚ) / (4084800000000 : ℚ)), ((125054619139 : ℚ) / (4084800000000 : ℚ)), ((30569330411 : ℚ) / (1021200000000 : ℚ))],
    jensenBound := ((25228160410378454461686702644710923479427948033338125506280087521721319424000000000000000000000 : ℚ) / (1936854045323665251271531649625354177733934034001838903617442609179416882195120829664853202333684373505160743943 : ℚ)),
    jensenFloorQ96 := (1031972851932 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_simplexId_before"
  err.flush

theorem geometryRow036_simplexId_read :
    geometryRowsJson036.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped036.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_vertexIds_before"
  err.flush

theorem geometryRow036_vertexIds_read :
    geometryRowsJson036.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped036.vertexIds := by decide +kernel

noncomputable def geometryRow036_physicalVolumeNumeratorChars : List Char := ['6', '2', '7', '8', '8', '7', '6', '4', '9', '3', '9', '2', '8', '9', '9', '9', '0', '7', '1', '1', '0', '2', '7', '3', '5', '3', '7', '3', '3']
noncomputable def geometryRow036_physicalVolumeDenominatorChars : List Char := ['8', '9', '0', '5', '8', '3', '1', '3', '4', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_physicalVolumeText : String := String.ofList (geometryRow036_physicalVolumeNumeratorChars ++ '/' :: geometryRow036_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_physicalVolume_before_field"
  err.flush

theorem geometryRow036_physicalVolume_field :
    geometryRowsJson036.getObjVal? "physical_volume" = .ok (.str geometryRow036_physicalVolumeText) := by rfl

theorem geometryRow036_physicalVolume_numerator_no_slash :
    geometryRow036_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeNumeratorChars = some (62788764939289990711027353733 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeDenominatorChars = some (8905831347656250000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_nonzero : (8905831347656250000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_physicalVolume_parse :
    parseRational geometryRow036_physicalVolumeText = .ok geometryRowsTyped036.physicalVolume :=
  original_rational_fraction_of_chars geometryRow036_physicalVolumeNumeratorChars geometryRow036_physicalVolumeDenominatorChars
    (62788764939289990711027353733 : Int) (8905831347656250000000000000000000000000000000000000000 : Int)
    geometryRow036_physicalVolume_numerator_no_slash geometryRow036_physicalVolume_numerator_parse
    geometryRow036_physicalVolume_denominator_parse geometryRow036_physicalVolume_denominator_nonzero

theorem geometryRow036_physicalVolume_read :
    rationalField geometryRowsJson036 "physical_volume" = .ok geometryRowsTyped036.physicalVolume :=
  original_rationalField_of_string geometryRowsJson036 "physical_volume" geometryRow036_physicalVolumeText
    geometryRowsTyped036.physicalVolume geometryRow036_physicalVolume_field geometryRow036_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_physicalVolume_complete"
  err.flush

noncomputable def geometryRow036_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow036_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_meanGapText : String := String.ofList (geometryRow036_meanGapNumeratorChars ++ '/' :: geometryRow036_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_meanGap_before_field"
  err.flush

theorem geometryRow036_meanGap_field :
    geometryRowsJson036.getObjVal? "mean_gap" = .ok (.str geometryRow036_meanGapText) := by rfl

theorem geometryRow036_meanGap_numerator_no_slash :
    geometryRow036_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_meanGap_numerator_parse :
    SourceJson.intChars geometryRow036_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_parse :
    SourceJson.intChars geometryRow036_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_meanGap_parse :
    parseRational geometryRow036_meanGapText = .ok geometryRowsTyped036.meanGap :=
  original_rational_fraction_of_chars geometryRow036_meanGapNumeratorChars geometryRow036_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow036_meanGap_numerator_no_slash geometryRow036_meanGap_numerator_parse
    geometryRow036_meanGap_denominator_parse geometryRow036_meanGap_denominator_nonzero

theorem geometryRow036_meanGap_read :
    rationalField geometryRowsJson036 "mean_gap" = .ok geometryRowsTyped036.meanGap :=
  original_rationalField_of_string geometryRowsJson036 "mean_gap" geometryRow036_meanGapText
    geometryRowsTyped036.meanGap geometryRow036_meanGap_field geometryRow036_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_meanGap_complete"
  err.flush

noncomputable def geometryRow036_jensenBoundNumeratorChars : List Char := ['2', '5', '2', '2', '8', '1', '6', '0', '4', '1', '0', '3', '7', '8', '4', '5', '4', '4', '6', '1', '6', '8', '6', '7', '0', '2', '6', '4', '4', '7', '1', '0', '9', '2', '3', '4', '7', '9', '4', '2', '7', '9', '4', '8', '0', '3', '3', '3', '3', '8', '1', '2', '5', '5', '0', '6', '2', '8', '0', '0', '8', '7', '5', '2', '1', '7', '2', '1', '3', '1', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_jensenBoundDenominatorChars : List Char := ['1', '9', '3', '6', '8', '5', '4', '0', '4', '5', '3', '2', '3', '6', '6', '5', '2', '5', '1', '2', '7', '1', '5', '3', '1', '6', '4', '9', '6', '2', '5', '3', '5', '4', '1', '7', '7', '7', '3', '3', '9', '3', '4', '0', '3', '4', '0', '0', '1', '8', '3', '8', '9', '0', '3', '6', '1', '7', '4', '4', '2', '6', '0', '9', '1', '7', '9', '4', '1', '6', '8', '8', '2', '1', '9', '5', '1', '2', '0', '8', '2', '9', '6', '6', '4', '8', '5', '3', '2', '0', '2', '3', '3', '3', '6', '8', '4', '3', '7', '3', '5', '0', '5', '1', '6', '0', '7', '4', '3', '9', '4', '3']
noncomputable def geometryRow036_jensenBoundText : String := String.ofList (geometryRow036_jensenBoundNumeratorChars ++ '/' :: geometryRow036_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_jensenBound_before_field"
  err.flush

theorem geometryRow036_jensenBound_field :
    geometryRowsJson036.getObjVal? "jensen_bound" = .ok (.str geometryRow036_jensenBoundText) := by rfl

theorem geometryRow036_jensenBound_numerator_no_slash :
    geometryRow036_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow036_jensenBoundNumeratorChars = some (25228160410378454461686702644710923479427948033338125506280087521721319424000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow036_jensenBoundDenominatorChars = some (1936854045323665251271531649625354177733934034001838903617442609179416882195120829664853202333684373505160743943 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_nonzero : (1936854045323665251271531649625354177733934034001838903617442609179416882195120829664853202333684373505160743943 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_jensenBound_parse :
    parseRational geometryRow036_jensenBoundText = .ok geometryRowsTyped036.jensenBound :=
  original_rational_fraction_of_chars geometryRow036_jensenBoundNumeratorChars geometryRow036_jensenBoundDenominatorChars
    (25228160410378454461686702644710923479427948033338125506280087521721319424000000000000000000000 : Int) (1936854045323665251271531649625354177733934034001838903617442609179416882195120829664853202333684373505160743943 : Int)
    geometryRow036_jensenBound_numerator_no_slash geometryRow036_jensenBound_numerator_parse
    geometryRow036_jensenBound_denominator_parse geometryRow036_jensenBound_denominator_nonzero

theorem geometryRow036_jensenBound_read :
    rationalField geometryRowsJson036 "jensen_bound" = .ok geometryRowsTyped036.jensenBound :=
  original_rationalField_of_string geometryRowsJson036 "jensen_bound" geometryRow036_jensenBoundText
    geometryRowsTyped036.jensenBound geometryRow036_jensenBound_field geometryRow036_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_factorMaxima_before"
  err.flush

theorem geometryRow036_factorMaxima_read :
    rationalArrayField geometryRowsJson036 "factor_maxima" = .ok geometryRowsTyped036.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_gapWeightedMeans_before"
  err.flush

theorem geometryRow036_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson036 "gap_weighted_means" = .ok geometryRowsTyped036.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow036_floorChars : List Char := ['1', '0', '3', '1', '9', '7', '2', '8', '5', '1', '9', '3', '2']
noncomputable def geometryRow036_floorText : String := String.ofList geometryRow036_floorChars

theorem geometryRow036_floor_text_read :
    geometryRowsJson036.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow036_floorText := by rfl

theorem geometryRow036_floor_chars_parse :
    SourceJson.intChars geometryRow036_floorChars = some (1031972851932 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_036_original_decoder_complete"
  err.flush

theorem geometryRow036_shape :
    geometryRowsTyped036.simplexId = 36 ∧
    geometryRowsTyped036.vertexIds.size = 9 ∧ geometryRowsTyped036.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped036.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped036.factorMaxima.size = 10 ∧ geometryRowsTyped036.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson037 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped037 : GeometryRow :=
  { simplexId := 37,
    vertexIds := #[27, 25, 23, 21, 20, 18, 16, 14, 4],
    physicalVolume := ((39886094358869935313038134343 : ℚ) / (10138334793090820312500000000000000000000000000000000000 : ℚ)),
    meanGap := ((51871037 : ℚ) / (97920000000 : ℚ)),
    factorMaxima := #[((2409379 : ℚ) / (25600000 : ℚ)), ((1546863 : ℚ) / (16000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2390621 : ℚ) / (32000000 : ℚ)), ((515597 : ℚ) / (12000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((1171823 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((13016947302496793464387 : ℚ) / (151284327723446400000000 : ℚ)), ((1640667338336982267443 : ℚ) / (18910540965430800000000 : ℚ)), ((9473956856019825320153 : ℚ) / (75642163861723200000000 : ℚ)), ((524459650345675239139 : ℚ) / (5403011704408800000000 : ℚ)), ((504861829571334208673 : ℚ) / (5403011704408800000000 : ℚ)), ((517220226453455093797 : ℚ) / (7564216386172320000000 : ℚ)), ((158488366349170086071 : ℚ) / (4449539050689600000000 : ℚ)), ((780960551903908638041 : ℚ) / (25214054620574400000000 : ℚ)), ((767259892381035132761 : ℚ) / (25214054620574400000000 : ℚ)), ((186672036642263341147 : ℚ) / (6303513655143600000000 : ℚ))],
    jensenBound := ((13178328581635724246191371629762140684371440304562163273836086067212092265927053175550692322008163910982622307438440888873275463739613893847471904422931904793127025639424000000000000000000000 : ℚ) / (911340525549405417823018798688500308859307689219178360893208320805941270517985706490730305697673125579950919327393497650799906689192213244102327245231320633109668740534091572735674681778142696838797949130681 : ℚ)),
    jensenFloorQ96 := (1145669186501 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_simplexId_before"
  err.flush

theorem geometryRow037_simplexId_read :
    geometryRowsJson037.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped037.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_vertexIds_before"
  err.flush

theorem geometryRow037_vertexIds_read :
    geometryRowsJson037.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped037.vertexIds := by decide +kernel

noncomputable def geometryRow037_physicalVolumeNumeratorChars : List Char := ['3', '9', '8', '8', '6', '0', '9', '4', '3', '5', '8', '8', '6', '9', '9', '3', '5', '3', '1', '3', '0', '3', '8', '1', '3', '4', '3', '4', '3']
noncomputable def geometryRow037_physicalVolumeDenominatorChars : List Char := ['1', '0', '1', '3', '8', '3', '3', '4', '7', '9', '3', '0', '9', '0', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_physicalVolumeText : String := String.ofList (geometryRow037_physicalVolumeNumeratorChars ++ '/' :: geometryRow037_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_physicalVolume_before_field"
  err.flush

theorem geometryRow037_physicalVolume_field :
    geometryRowsJson037.getObjVal? "physical_volume" = .ok (.str geometryRow037_physicalVolumeText) := by rfl

theorem geometryRow037_physicalVolume_numerator_no_slash :
    geometryRow037_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeNumeratorChars = some (39886094358869935313038134343 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeDenominatorChars = some (10138334793090820312500000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_nonzero : (10138334793090820312500000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_physicalVolume_parse :
    parseRational geometryRow037_physicalVolumeText = .ok geometryRowsTyped037.physicalVolume :=
  original_rational_fraction_of_chars geometryRow037_physicalVolumeNumeratorChars geometryRow037_physicalVolumeDenominatorChars
    (39886094358869935313038134343 : Int) (10138334793090820312500000000000000000000000000000000000 : Int)
    geometryRow037_physicalVolume_numerator_no_slash geometryRow037_physicalVolume_numerator_parse
    geometryRow037_physicalVolume_denominator_parse geometryRow037_physicalVolume_denominator_nonzero

theorem geometryRow037_physicalVolume_read :
    rationalField geometryRowsJson037 "physical_volume" = .ok geometryRowsTyped037.physicalVolume :=
  original_rationalField_of_string geometryRowsJson037 "physical_volume" geometryRow037_physicalVolumeText
    geometryRowsTyped037.physicalVolume geometryRow037_physicalVolume_field geometryRow037_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_physicalVolume_complete"
  err.flush

noncomputable def geometryRow037_meanGapNumeratorChars : List Char := ['5', '1', '8', '7', '1', '0', '3', '7']
noncomputable def geometryRow037_meanGapDenominatorChars : List Char := ['9', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_meanGapText : String := String.ofList (geometryRow037_meanGapNumeratorChars ++ '/' :: geometryRow037_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_meanGap_before_field"
  err.flush

theorem geometryRow037_meanGap_field :
    geometryRowsJson037.getObjVal? "mean_gap" = .ok (.str geometryRow037_meanGapText) := by rfl

theorem geometryRow037_meanGap_numerator_no_slash :
    geometryRow037_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_meanGap_numerator_parse :
    SourceJson.intChars geometryRow037_meanGapNumeratorChars = some (51871037 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_parse :
    SourceJson.intChars geometryRow037_meanGapDenominatorChars = some (97920000000 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_nonzero : (97920000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_meanGap_parse :
    parseRational geometryRow037_meanGapText = .ok geometryRowsTyped037.meanGap :=
  original_rational_fraction_of_chars geometryRow037_meanGapNumeratorChars geometryRow037_meanGapDenominatorChars
    (51871037 : Int) (97920000000 : Int)
    geometryRow037_meanGap_numerator_no_slash geometryRow037_meanGap_numerator_parse
    geometryRow037_meanGap_denominator_parse geometryRow037_meanGap_denominator_nonzero

theorem geometryRow037_meanGap_read :
    rationalField geometryRowsJson037 "mean_gap" = .ok geometryRowsTyped037.meanGap :=
  original_rationalField_of_string geometryRowsJson037 "mean_gap" geometryRow037_meanGapText
    geometryRowsTyped037.meanGap geometryRow037_meanGap_field geometryRow037_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_meanGap_complete"
  err.flush

noncomputable def geometryRow037_jensenBoundNumeratorChars : List Char := ['1', '3', '1', '7', '8', '3', '2', '8', '5', '8', '1', '6', '3', '5', '7', '2', '4', '2', '4', '6', '1', '9', '1', '3', '7', '1', '6', '2', '9', '7', '6', '2', '1', '4', '0', '6', '8', '4', '3', '7', '1', '4', '4', '0', '3', '0', '4', '5', '6', '2', '1', '6', '3', '2', '7', '3', '8', '3', '6', '0', '8', '6', '0', '6', '7', '2', '1', '2', '0', '9', '2', '2', '6', '5', '9', '2', '7', '0', '5', '3', '1', '7', '5', '5', '5', '0', '6', '9', '2', '3', '2', '2', '0', '0', '8', '1', '6', '3', '9', '1', '0', '9', '8', '2', '6', '2', '2', '3', '0', '7', '4', '3', '8', '4', '4', '0', '8', '8', '8', '8', '7', '3', '2', '7', '5', '4', '6', '3', '7', '3', '9', '6', '1', '3', '8', '9', '3', '8', '4', '7', '4', '7', '1', '9', '0', '4', '4', '2', '2', '9', '3', '1', '9', '0', '4', '7', '9', '3', '1', '2', '7', '0', '2', '5', '6', '3', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_jensenBoundDenominatorChars : List Char := ['9', '1', '1', '3', '4', '0', '5', '2', '5', '5', '4', '9', '4', '0', '5', '4', '1', '7', '8', '2', '3', '0', '1', '8', '7', '9', '8', '6', '8', '8', '5', '0', '0', '3', '0', '8', '8', '5', '9', '3', '0', '7', '6', '8', '9', '2', '1', '9', '1', '7', '8', '3', '6', '0', '8', '9', '3', '2', '0', '8', '3', '2', '0', '8', '0', '5', '9', '4', '1', '2', '7', '0', '5', '1', '7', '9', '8', '5', '7', '0', '6', '4', '9', '0', '7', '3', '0', '3', '0', '5', '6', '9', '7', '6', '7', '3', '1', '2', '5', '5', '7', '9', '9', '5', '0', '9', '1', '9', '3', '2', '7', '3', '9', '3', '4', '9', '7', '6', '5', '0', '7', '9', '9', '9', '0', '6', '6', '8', '9', '1', '9', '2', '2', '1', '3', '2', '4', '4', '1', '0', '2', '3', '2', '7', '2', '4', '5', '2', '3', '1', '3', '2', '0', '6', '3', '3', '1', '0', '9', '6', '6', '8', '7', '4', '0', '5', '3', '4', '0', '9', '1', '5', '7', '2', '7', '3', '5', '6', '7', '4', '6', '8', '1', '7', '7', '8', '1', '4', '2', '6', '9', '6', '8', '3', '8', '7', '9', '7', '9', '4', '9', '1', '3', '0', '6', '8', '1']
noncomputable def geometryRow037_jensenBoundText : String := String.ofList (geometryRow037_jensenBoundNumeratorChars ++ '/' :: geometryRow037_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_jensenBound_before_field"
  err.flush

theorem geometryRow037_jensenBound_field :
    geometryRowsJson037.getObjVal? "jensen_bound" = .ok (.str geometryRow037_jensenBoundText) := by rfl

theorem geometryRow037_jensenBound_numerator_no_slash :
    geometryRow037_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow037_jensenBoundNumeratorChars = some (13178328581635724246191371629762140684371440304562163273836086067212092265927053175550692322008163910982622307438440888873275463739613893847471904422931904793127025639424000000000000000000000 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow037_jensenBoundDenominatorChars = some (911340525549405417823018798688500308859307689219178360893208320805941270517985706490730305697673125579950919327393497650799906689192213244102327245231320633109668740534091572735674681778142696838797949130681 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_nonzero : (911340525549405417823018798688500308859307689219178360893208320805941270517985706490730305697673125579950919327393497650799906689192213244102327245231320633109668740534091572735674681778142696838797949130681 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_jensenBound_parse :
    parseRational geometryRow037_jensenBoundText = .ok geometryRowsTyped037.jensenBound :=
  original_rational_fraction_of_chars geometryRow037_jensenBoundNumeratorChars geometryRow037_jensenBoundDenominatorChars
    (13178328581635724246191371629762140684371440304562163273836086067212092265927053175550692322008163910982622307438440888873275463739613893847471904422931904793127025639424000000000000000000000 : Int) (911340525549405417823018798688500308859307689219178360893208320805941270517985706490730305697673125579950919327393497650799906689192213244102327245231320633109668740534091572735674681778142696838797949130681 : Int)
    geometryRow037_jensenBound_numerator_no_slash geometryRow037_jensenBound_numerator_parse
    geometryRow037_jensenBound_denominator_parse geometryRow037_jensenBound_denominator_nonzero

theorem geometryRow037_jensenBound_read :
    rationalField geometryRowsJson037 "jensen_bound" = .ok geometryRowsTyped037.jensenBound :=
  original_rationalField_of_string geometryRowsJson037 "jensen_bound" geometryRow037_jensenBoundText
    geometryRowsTyped037.jensenBound geometryRow037_jensenBound_field geometryRow037_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_factorMaxima_before"
  err.flush

theorem geometryRow037_factorMaxima_read :
    rationalArrayField geometryRowsJson037 "factor_maxima" = .ok geometryRowsTyped037.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_gapWeightedMeans_before"
  err.flush

theorem geometryRow037_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson037 "gap_weighted_means" = .ok geometryRowsTyped037.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow037_floorChars : List Char := ['1', '1', '4', '5', '6', '6', '9', '1', '8', '6', '5', '0', '1']
noncomputable def geometryRow037_floorText : String := String.ofList geometryRow037_floorChars

theorem geometryRow037_floor_text_read :
    geometryRowsJson037.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow037_floorText := by rfl

theorem geometryRow037_floor_chars_parse :
    SourceJson.intChars geometryRow037_floorChars = some (1145669186501 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_037_original_decoder_complete"
  err.flush

theorem geometryRow037_shape :
    geometryRowsTyped037.simplexId = 37 ∧
    geometryRowsTyped037.vertexIds.size = 9 ∧ geometryRowsTyped037.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped037.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped037.factorMaxima.size = 10 ∧ geometryRowsTyped037.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson038 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped038 : GeometryRow :=
  { simplexId := 38,
    vertexIds := #[27, 25, 23, 22, 11, 6, 4, 2, 0],
    physicalVolume := ((80235687090693261314664746691916613552873 : ℚ) / (552590889274368000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((374406951233767 : ℚ) / (4177756800000000 : ℚ)), ((23534256896467 : ℚ) / (261109800000000 : ℚ)), ((3367411672297 : ℚ) / (27851712000000 : ℚ)), ((5291476996633 : ℚ) / (58024400000000 : ℚ)), ((3759531512609 : ℚ) / (43518300000000 : ℚ)), ((2543941042591 : ℚ) / (34814640000000 : ℚ)), ((26633020161421 : ℚ) / (696292800000000 : ℚ)), ((70358336393747 : ℚ) / (2088878400000000 : ℚ)), ((69223433622227 : ℚ) / (2088878400000000 : ℚ)), ((2675335017083 : ℚ) / (87036600000000 : ℚ))],
    jensenBound := ((350397689838516354158844531415319831749293067675388956093056110937571060097595703377817025547468800000000000000000000000 : ℚ) / (1563316227905122523104119577922142154315847758078416876762537959820231669643084117754920755053843572637799115953224625457771250336391 : ℚ)),
    jensenFloorQ96 := (17757997147096458 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_simplexId_before"
  err.flush

theorem geometryRow038_simplexId_read :
    geometryRowsJson038.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped038.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_vertexIds_before"
  err.flush

theorem geometryRow038_vertexIds_read :
    geometryRowsJson038.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped038.vertexIds := by decide +kernel

noncomputable def geometryRow038_physicalVolumeNumeratorChars : List Char := ['8', '0', '2', '3', '5', '6', '8', '7', '0', '9', '0', '6', '9', '3', '2', '6', '1', '3', '1', '4', '6', '6', '4', '7', '4', '6', '6', '9', '1', '9', '1', '6', '6', '1', '3', '5', '5', '2', '8', '7', '3']
noncomputable def geometryRow038_physicalVolumeDenominatorChars : List Char := ['5', '5', '2', '5', '9', '0', '8', '8', '9', '2', '7', '4', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_physicalVolumeText : String := String.ofList (geometryRow038_physicalVolumeNumeratorChars ++ '/' :: geometryRow038_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_physicalVolume_before_field"
  err.flush

theorem geometryRow038_physicalVolume_field :
    geometryRowsJson038.getObjVal? "physical_volume" = .ok (.str geometryRow038_physicalVolumeText) := by rfl

theorem geometryRow038_physicalVolume_numerator_no_slash :
    geometryRow038_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeNumeratorChars = some (80235687090693261314664746691916613552873 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeDenominatorChars = some (552590889274368000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_nonzero : (552590889274368000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_physicalVolume_parse :
    parseRational geometryRow038_physicalVolumeText = .ok geometryRowsTyped038.physicalVolume :=
  original_rational_fraction_of_chars geometryRow038_physicalVolumeNumeratorChars geometryRow038_physicalVolumeDenominatorChars
    (80235687090693261314664746691916613552873 : Int) (552590889274368000000000000000000000000000000000000000000000000 : Int)
    geometryRow038_physicalVolume_numerator_no_slash geometryRow038_physicalVolume_numerator_parse
    geometryRow038_physicalVolume_denominator_parse geometryRow038_physicalVolume_denominator_nonzero

theorem geometryRow038_physicalVolume_read :
    rationalField geometryRowsJson038 "physical_volume" = .ok geometryRowsTyped038.physicalVolume :=
  original_rationalField_of_string geometryRowsJson038 "physical_volume" geometryRow038_physicalVolumeText
    geometryRowsTyped038.physicalVolume geometryRow038_physicalVolume_field geometryRow038_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_physicalVolume_complete"
  err.flush

noncomputable def geometryRow038_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow038_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_meanGapText : String := String.ofList (geometryRow038_meanGapNumeratorChars ++ '/' :: geometryRow038_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_meanGap_before_field"
  err.flush

theorem geometryRow038_meanGap_field :
    geometryRowsJson038.getObjVal? "mean_gap" = .ok (.str geometryRow038_meanGapText) := by rfl

theorem geometryRow038_meanGap_numerator_no_slash :
    geometryRow038_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_meanGap_numerator_parse :
    SourceJson.intChars geometryRow038_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_parse :
    SourceJson.intChars geometryRow038_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_meanGap_parse :
    parseRational geometryRow038_meanGapText = .ok geometryRowsTyped038.meanGap :=
  original_rational_fraction_of_chars geometryRow038_meanGapNumeratorChars geometryRow038_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow038_meanGap_numerator_no_slash geometryRow038_meanGap_numerator_parse
    geometryRow038_meanGap_denominator_parse geometryRow038_meanGap_denominator_nonzero

theorem geometryRow038_meanGap_read :
    rationalField geometryRowsJson038 "mean_gap" = .ok geometryRowsTyped038.meanGap :=
  original_rationalField_of_string geometryRowsJson038 "mean_gap" geometryRow038_meanGapText
    geometryRowsTyped038.meanGap geometryRow038_meanGap_field geometryRow038_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_meanGap_complete"
  err.flush

noncomputable def geometryRow038_jensenBoundNumeratorChars : List Char := ['3', '5', '0', '3', '9', '7', '6', '8', '9', '8', '3', '8', '5', '1', '6', '3', '5', '4', '1', '5', '8', '8', '4', '4', '5', '3', '1', '4', '1', '5', '3', '1', '9', '8', '3', '1', '7', '4', '9', '2', '9', '3', '0', '6', '7', '6', '7', '5', '3', '8', '8', '9', '5', '6', '0', '9', '3', '0', '5', '6', '1', '1', '0', '9', '3', '7', '5', '7', '1', '0', '6', '0', '0', '9', '7', '5', '9', '5', '7', '0', '3', '3', '7', '7', '8', '1', '7', '0', '2', '5', '5', '4', '7', '4', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_jensenBoundDenominatorChars : List Char := ['1', '5', '6', '3', '3', '1', '6', '2', '2', '7', '9', '0', '5', '1', '2', '2', '5', '2', '3', '1', '0', '4', '1', '1', '9', '5', '7', '7', '9', '2', '2', '1', '4', '2', '1', '5', '4', '3', '1', '5', '8', '4', '7', '7', '5', '8', '0', '7', '8', '4', '1', '6', '8', '7', '6', '7', '6', '2', '5', '3', '7', '9', '5', '9', '8', '2', '0', '2', '3', '1', '6', '6', '9', '6', '4', '3', '0', '8', '4', '1', '1', '7', '7', '5', '4', '9', '2', '0', '7', '5', '5', '0', '5', '3', '8', '4', '3', '5', '7', '2', '6', '3', '7', '7', '9', '9', '1', '1', '5', '9', '5', '3', '2', '2', '4', '6', '2', '5', '4', '5', '7', '7', '7', '1', '2', '5', '0', '3', '3', '6', '3', '9', '1']
noncomputable def geometryRow038_jensenBoundText : String := String.ofList (geometryRow038_jensenBoundNumeratorChars ++ '/' :: geometryRow038_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_jensenBound_before_field"
  err.flush

theorem geometryRow038_jensenBound_field :
    geometryRowsJson038.getObjVal? "jensen_bound" = .ok (.str geometryRow038_jensenBoundText) := by rfl

theorem geometryRow038_jensenBound_numerator_no_slash :
    geometryRow038_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow038_jensenBoundNumeratorChars = some (350397689838516354158844531415319831749293067675388956093056110937571060097595703377817025547468800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow038_jensenBoundDenominatorChars = some (1563316227905122523104119577922142154315847758078416876762537959820231669643084117754920755053843572637799115953224625457771250336391 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_nonzero : (1563316227905122523104119577922142154315847758078416876762537959820231669643084117754920755053843572637799115953224625457771250336391 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_jensenBound_parse :
    parseRational geometryRow038_jensenBoundText = .ok geometryRowsTyped038.jensenBound :=
  original_rational_fraction_of_chars geometryRow038_jensenBoundNumeratorChars geometryRow038_jensenBoundDenominatorChars
    (350397689838516354158844531415319831749293067675388956093056110937571060097595703377817025547468800000000000000000000000 : Int) (1563316227905122523104119577922142154315847758078416876762537959820231669643084117754920755053843572637799115953224625457771250336391 : Int)
    geometryRow038_jensenBound_numerator_no_slash geometryRow038_jensenBound_numerator_parse
    geometryRow038_jensenBound_denominator_parse geometryRow038_jensenBound_denominator_nonzero

theorem geometryRow038_jensenBound_read :
    rationalField geometryRowsJson038 "jensen_bound" = .ok geometryRowsTyped038.jensenBound :=
  original_rationalField_of_string geometryRowsJson038 "jensen_bound" geometryRow038_jensenBoundText
    geometryRowsTyped038.jensenBound geometryRow038_jensenBound_field geometryRow038_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_factorMaxima_before"
  err.flush

theorem geometryRow038_factorMaxima_read :
    rationalArrayField geometryRowsJson038 "factor_maxima" = .ok geometryRowsTyped038.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_gapWeightedMeans_before"
  err.flush

theorem geometryRow038_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson038 "gap_weighted_means" = .ok geometryRowsTyped038.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow038_floorChars : List Char := ['1', '7', '7', '5', '7', '9', '9', '7', '1', '4', '7', '0', '9', '6', '4', '5', '8']
noncomputable def geometryRow038_floorText : String := String.ofList geometryRow038_floorChars

theorem geometryRow038_floor_text_read :
    geometryRowsJson038.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow038_floorText := by rfl

theorem geometryRow038_floor_chars_parse :
    SourceJson.intChars geometryRow038_floorChars = some (17757997147096458 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_038_original_decoder_complete"
  err.flush

theorem geometryRow038_shape :
    geometryRowsTyped038.simplexId = 38 ∧
    geometryRowsTyped038.vertexIds.size = 9 ∧ geometryRowsTyped038.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped038.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped038.factorMaxima.size = 10 ∧ geometryRowsTyped038.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson039 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped039 : GeometryRow :=
  { simplexId := 39,
    vertexIds := #[27, 25, 23, 22, 20, 6, 4, 2, 0],
    physicalVolume := ((3301358347870338501369876930519915291251 : ℚ) / (25183178547660000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((53419955575681 : ℚ) / (596822400000000 : ℚ)), ((3357864715531 : ℚ) / (37301400000000 : ℚ)), ((5658973789983 : ℚ) / (46419520000000 : ℚ)), ((48167248509937 : ℚ) / (522219600000000 : ℚ)), ((7689024471173 : ℚ) / (87036600000000 : ℚ)), ((33453003873 : ℚ) / (464195200000 : ℚ)), ((25972643636101 : ℚ) / (696292800000000 : ℚ)), ((9768172402541 : ℚ) / (298411200000000 : ℚ)), ((9606043435181 : ℚ) / (298411200000000 : ℚ)), ((1145181488857 : ℚ) / (37301400000000 : ℚ))],
    jensenBound := ((51219101777547940464991191584587921838657364114008979249512405345792401067891998988947161088000000000000000000000 : ℚ) / (238777612658440276920188848280319544483417985772073663816203284129243031738426204886385936480591952967851313211092569957657999 : ℚ)),
    jensenFloorQ96 := (16994873490384452 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_simplexId_before"
  err.flush

theorem geometryRow039_simplexId_read :
    geometryRowsJson039.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped039.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_vertexIds_before"
  err.flush

theorem geometryRow039_vertexIds_read :
    geometryRowsJson039.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped039.vertexIds := by decide +kernel

noncomputable def geometryRow039_physicalVolumeNumeratorChars : List Char := ['3', '3', '0', '1', '3', '5', '8', '3', '4', '7', '8', '7', '0', '3', '3', '8', '5', '0', '1', '3', '6', '9', '8', '7', '6', '9', '3', '0', '5', '1', '9', '9', '1', '5', '2', '9', '1', '2', '5', '1']
noncomputable def geometryRow039_physicalVolumeDenominatorChars : List Char := ['2', '5', '1', '8', '3', '1', '7', '8', '5', '4', '7', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_physicalVolumeText : String := String.ofList (geometryRow039_physicalVolumeNumeratorChars ++ '/' :: geometryRow039_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_physicalVolume_before_field"
  err.flush

theorem geometryRow039_physicalVolume_field :
    geometryRowsJson039.getObjVal? "physical_volume" = .ok (.str geometryRow039_physicalVolumeText) := by rfl

theorem geometryRow039_physicalVolume_numerator_no_slash :
    geometryRow039_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeNumeratorChars = some (3301358347870338501369876930519915291251 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeDenominatorChars = some (25183178547660000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_nonzero : (25183178547660000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_physicalVolume_parse :
    parseRational geometryRow039_physicalVolumeText = .ok geometryRowsTyped039.physicalVolume :=
  original_rational_fraction_of_chars geometryRow039_physicalVolumeNumeratorChars geometryRow039_physicalVolumeDenominatorChars
    (3301358347870338501369876930519915291251 : Int) (25183178547660000000000000000000000000000000000000000000000000 : Int)
    geometryRow039_physicalVolume_numerator_no_slash geometryRow039_physicalVolume_numerator_parse
    geometryRow039_physicalVolume_denominator_parse geometryRow039_physicalVolume_denominator_nonzero

theorem geometryRow039_physicalVolume_read :
    rationalField geometryRowsJson039 "physical_volume" = .ok geometryRowsTyped039.physicalVolume :=
  original_rationalField_of_string geometryRowsJson039 "physical_volume" geometryRow039_physicalVolumeText
    geometryRowsTyped039.physicalVolume geometryRow039_physicalVolume_field geometryRow039_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_physicalVolume_complete"
  err.flush

noncomputable def geometryRow039_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow039_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_meanGapText : String := String.ofList (geometryRow039_meanGapNumeratorChars ++ '/' :: geometryRow039_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_meanGap_before_field"
  err.flush

theorem geometryRow039_meanGap_field :
    geometryRowsJson039.getObjVal? "mean_gap" = .ok (.str geometryRow039_meanGapText) := by rfl

theorem geometryRow039_meanGap_numerator_no_slash :
    geometryRow039_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_meanGap_numerator_parse :
    SourceJson.intChars geometryRow039_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_parse :
    SourceJson.intChars geometryRow039_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_meanGap_parse :
    parseRational geometryRow039_meanGapText = .ok geometryRowsTyped039.meanGap :=
  original_rational_fraction_of_chars geometryRow039_meanGapNumeratorChars geometryRow039_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow039_meanGap_numerator_no_slash geometryRow039_meanGap_numerator_parse
    geometryRow039_meanGap_denominator_parse geometryRow039_meanGap_denominator_nonzero

theorem geometryRow039_meanGap_read :
    rationalField geometryRowsJson039 "mean_gap" = .ok geometryRowsTyped039.meanGap :=
  original_rationalField_of_string geometryRowsJson039 "mean_gap" geometryRow039_meanGapText
    geometryRowsTyped039.meanGap geometryRow039_meanGap_field geometryRow039_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_meanGap_complete"
  err.flush

noncomputable def geometryRow039_jensenBoundNumeratorChars : List Char := ['5', '1', '2', '1', '9', '1', '0', '1', '7', '7', '7', '5', '4', '7', '9', '4', '0', '4', '6', '4', '9', '9', '1', '1', '9', '1', '5', '8', '4', '5', '8', '7', '9', '2', '1', '8', '3', '8', '6', '5', '7', '3', '6', '4', '1', '1', '4', '0', '0', '8', '9', '7', '9', '2', '4', '9', '5', '1', '2', '4', '0', '5', '3', '4', '5', '7', '9', '2', '4', '0', '1', '0', '6', '7', '8', '9', '1', '9', '9', '8', '9', '8', '8', '9', '4', '7', '1', '6', '1', '0', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_jensenBoundDenominatorChars : List Char := ['2', '3', '8', '7', '7', '7', '6', '1', '2', '6', '5', '8', '4', '4', '0', '2', '7', '6', '9', '2', '0', '1', '8', '8', '8', '4', '8', '2', '8', '0', '3', '1', '9', '5', '4', '4', '4', '8', '3', '4', '1', '7', '9', '8', '5', '7', '7', '2', '0', '7', '3', '6', '6', '3', '8', '1', '6', '2', '0', '3', '2', '8', '4', '1', '2', '9', '2', '4', '3', '0', '3', '1', '7', '3', '8', '4', '2', '6', '2', '0', '4', '8', '8', '6', '3', '8', '5', '9', '3', '6', '4', '8', '0', '5', '9', '1', '9', '5', '2', '9', '6', '7', '8', '5', '1', '3', '1', '3', '2', '1', '1', '0', '9', '2', '5', '6', '9', '9', '5', '7', '6', '5', '7', '9', '9', '9']
noncomputable def geometryRow039_jensenBoundText : String := String.ofList (geometryRow039_jensenBoundNumeratorChars ++ '/' :: geometryRow039_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_jensenBound_before_field"
  err.flush

theorem geometryRow039_jensenBound_field :
    geometryRowsJson039.getObjVal? "jensen_bound" = .ok (.str geometryRow039_jensenBoundText) := by rfl

theorem geometryRow039_jensenBound_numerator_no_slash :
    geometryRow039_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow039_jensenBoundNumeratorChars = some (51219101777547940464991191584587921838657364114008979249512405345792401067891998988947161088000000000000000000000 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow039_jensenBoundDenominatorChars = some (238777612658440276920188848280319544483417985772073663816203284129243031738426204886385936480591952967851313211092569957657999 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_nonzero : (238777612658440276920188848280319544483417985772073663816203284129243031738426204886385936480591952967851313211092569957657999 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_jensenBound_parse :
    parseRational geometryRow039_jensenBoundText = .ok geometryRowsTyped039.jensenBound :=
  original_rational_fraction_of_chars geometryRow039_jensenBoundNumeratorChars geometryRow039_jensenBoundDenominatorChars
    (51219101777547940464991191584587921838657364114008979249512405345792401067891998988947161088000000000000000000000 : Int) (238777612658440276920188848280319544483417985772073663816203284129243031738426204886385936480591952967851313211092569957657999 : Int)
    geometryRow039_jensenBound_numerator_no_slash geometryRow039_jensenBound_numerator_parse
    geometryRow039_jensenBound_denominator_parse geometryRow039_jensenBound_denominator_nonzero

theorem geometryRow039_jensenBound_read :
    rationalField geometryRowsJson039 "jensen_bound" = .ok geometryRowsTyped039.jensenBound :=
  original_rationalField_of_string geometryRowsJson039 "jensen_bound" geometryRow039_jensenBoundText
    geometryRowsTyped039.jensenBound geometryRow039_jensenBound_field geometryRow039_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_factorMaxima_before"
  err.flush

theorem geometryRow039_factorMaxima_read :
    rationalArrayField geometryRowsJson039 "factor_maxima" = .ok geometryRowsTyped039.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_gapWeightedMeans_before"
  err.flush

theorem geometryRow039_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson039 "gap_weighted_means" = .ok geometryRowsTyped039.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow039_floorChars : List Char := ['1', '6', '9', '9', '4', '8', '7', '3', '4', '9', '0', '3', '8', '4', '4', '5', '2']
noncomputable def geometryRow039_floorText : String := String.ofList geometryRow039_floorChars

theorem geometryRow039_floor_text_read :
    geometryRowsJson039.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow039_floorText := by rfl

theorem geometryRow039_floor_chars_parse :
    SourceJson.intChars geometryRow039_floorChars = some (16994873490384452 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_039_original_decoder_complete"
  err.flush

theorem geometryRow039_shape :
    geometryRowsTyped039.simplexId = 39 ∧
    geometryRowsTyped039.vertexIds.size = 9 ∧ geometryRowsTyped039.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped039.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped039.factorMaxima.size = 10 ∧ geometryRowsTyped039.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock004 : List SourceJson := [geometryRowsJson032, geometryRowsJson033, geometryRowsJson034, geometryRowsJson035, geometryRowsJson036, geometryRowsJson037, geometryRowsJson038, geometryRowsJson039]
noncomputable def geometryRowsTypedBlock004 : List GeometryRow := [geometryRowsTyped032, geometryRowsTyped033, geometryRowsTyped034, geometryRowsTyped035, geometryRowsTyped036, geometryRowsTyped037, geometryRowsTyped038, geometryRowsTyped039]

theorem geometry_Rows_block_004_push_eq (acc : List SourceJson) :
    SimplicesBlock004.blockPush acc = [geometryRowsJson039, geometryRowsJson038, geometryRowsJson037, geometryRowsJson036, geometryRowsJson035, geometryRowsJson034, geometryRowsJson033, geometryRowsJson032] ++ acc := by rfl

theorem geometry_Rows_block_004_reverse (acc : List SourceJson) :
    (SimplicesBlock004.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock004 := by
  rw [geometry_Rows_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_004 :
    geometryRowsJsonBlock004.mapM decodeGeometryRow = .ok geometryRowsTypedBlock004 := by
  simp only [geometryRowsJsonBlock004, geometryRowsTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_032, decode_geometry_Rows_033, decode_geometry_Rows_034, decode_geometry_Rows_035, decode_geometry_Rows_036, decode_geometry_Rows_037, decode_geometry_Rows_038, decode_geometry_Rows_039]
  rfl

theorem geometry_Rows_block_004_length : geometryRowsTypedBlock004.length = 8 := by rfl

#print axioms geometryRow032_simplexId_read
#print axioms geometryRow032_vertexIds_read
#print axioms geometryRow032_physicalVolume_field
#print axioms geometryRow032_physicalVolume_numerator_no_slash
#print axioms geometryRow032_physicalVolume_numerator_parse
#print axioms geometryRow032_physicalVolume_denominator_parse
#print axioms geometryRow032_physicalVolume_denominator_nonzero
#print axioms geometryRow032_physicalVolume_parse
#print axioms geometryRow032_physicalVolume_read
#print axioms geometryRow032_meanGap_field
#print axioms geometryRow032_meanGap_numerator_no_slash
#print axioms geometryRow032_meanGap_numerator_parse
#print axioms geometryRow032_meanGap_denominator_parse
#print axioms geometryRow032_meanGap_denominator_nonzero
#print axioms geometryRow032_meanGap_parse
#print axioms geometryRow032_meanGap_read
#print axioms geometryRow032_jensenBound_field
#print axioms geometryRow032_jensenBound_numerator_no_slash
#print axioms geometryRow032_jensenBound_numerator_parse
#print axioms geometryRow032_jensenBound_denominator_parse
#print axioms geometryRow032_jensenBound_denominator_nonzero
#print axioms geometryRow032_jensenBound_parse
#print axioms geometryRow032_jensenBound_read
#print axioms geometryRow032_factorMaxima_read
#print axioms geometryRow032_gapWeightedMeans_read
#print axioms geometryRow032_floor_text_read
#print axioms geometryRow032_floor_chars_parse
#print axioms geometryRow032_floor_parse
#print axioms decode_geometry_Rows_032
#print axioms geometryRow032_shape
#print axioms geometryRow033_simplexId_read
#print axioms geometryRow033_vertexIds_read
#print axioms geometryRow033_physicalVolume_field
#print axioms geometryRow033_physicalVolume_numerator_no_slash
#print axioms geometryRow033_physicalVolume_numerator_parse
#print axioms geometryRow033_physicalVolume_denominator_parse
#print axioms geometryRow033_physicalVolume_denominator_nonzero
#print axioms geometryRow033_physicalVolume_parse
#print axioms geometryRow033_physicalVolume_read
#print axioms geometryRow033_meanGap_field
#print axioms geometryRow033_meanGap_numerator_no_slash
#print axioms geometryRow033_meanGap_numerator_parse
#print axioms geometryRow033_meanGap_denominator_parse
#print axioms geometryRow033_meanGap_denominator_nonzero
#print axioms geometryRow033_meanGap_parse
#print axioms geometryRow033_meanGap_read
#print axioms geometryRow033_jensenBound_field
#print axioms geometryRow033_jensenBound_numerator_no_slash
#print axioms geometryRow033_jensenBound_numerator_parse
#print axioms geometryRow033_jensenBound_denominator_parse
#print axioms geometryRow033_jensenBound_denominator_nonzero
#print axioms geometryRow033_jensenBound_parse
#print axioms geometryRow033_jensenBound_read
#print axioms geometryRow033_factorMaxima_read
#print axioms geometryRow033_gapWeightedMeans_read
#print axioms geometryRow033_floor_text_read
#print axioms geometryRow033_floor_chars_parse
#print axioms geometryRow033_floor_parse
#print axioms decode_geometry_Rows_033
#print axioms geometryRow033_shape
#print axioms geometryRow034_simplexId_read
#print axioms geometryRow034_vertexIds_read
#print axioms geometryRow034_physicalVolume_field
#print axioms geometryRow034_physicalVolume_numerator_no_slash
#print axioms geometryRow034_physicalVolume_numerator_parse
#print axioms geometryRow034_physicalVolume_denominator_parse
#print axioms geometryRow034_physicalVolume_denominator_nonzero
#print axioms geometryRow034_physicalVolume_parse
#print axioms geometryRow034_physicalVolume_read
#print axioms geometryRow034_meanGap_field
#print axioms geometryRow034_meanGap_numerator_no_slash
#print axioms geometryRow034_meanGap_numerator_parse
#print axioms geometryRow034_meanGap_denominator_parse
#print axioms geometryRow034_meanGap_denominator_nonzero
#print axioms geometryRow034_meanGap_parse
#print axioms geometryRow034_meanGap_read
#print axioms geometryRow034_jensenBound_field
#print axioms geometryRow034_jensenBound_numerator_no_slash
#print axioms geometryRow034_jensenBound_numerator_parse
#print axioms geometryRow034_jensenBound_denominator_parse
#print axioms geometryRow034_jensenBound_denominator_nonzero
#print axioms geometryRow034_jensenBound_parse
#print axioms geometryRow034_jensenBound_read
#print axioms geometryRow034_factorMaxima_read
#print axioms geometryRow034_gapWeightedMeans_read
#print axioms geometryRow034_floor_text_read
#print axioms geometryRow034_floor_chars_parse
#print axioms geometryRow034_floor_parse
#print axioms decode_geometry_Rows_034
#print axioms geometryRow034_shape
#print axioms geometryRow035_simplexId_read
#print axioms geometryRow035_vertexIds_read
#print axioms geometryRow035_physicalVolume_field
#print axioms geometryRow035_physicalVolume_numerator_no_slash
#print axioms geometryRow035_physicalVolume_numerator_parse
#print axioms geometryRow035_physicalVolume_denominator_parse
#print axioms geometryRow035_physicalVolume_denominator_nonzero
#print axioms geometryRow035_physicalVolume_parse
#print axioms geometryRow035_physicalVolume_read
#print axioms geometryRow035_meanGap_field
#print axioms geometryRow035_meanGap_numerator_no_slash
#print axioms geometryRow035_meanGap_numerator_parse
#print axioms geometryRow035_meanGap_denominator_parse
#print axioms geometryRow035_meanGap_denominator_nonzero
#print axioms geometryRow035_meanGap_parse
#print axioms geometryRow035_meanGap_read
#print axioms geometryRow035_jensenBound_field
#print axioms geometryRow035_jensenBound_numerator_no_slash
#print axioms geometryRow035_jensenBound_numerator_parse
#print axioms geometryRow035_jensenBound_denominator_parse
#print axioms geometryRow035_jensenBound_denominator_nonzero
#print axioms geometryRow035_jensenBound_parse
#print axioms geometryRow035_jensenBound_read
#print axioms geometryRow035_factorMaxima_read
#print axioms geometryRow035_gapWeightedMeans_read
#print axioms geometryRow035_floor_text_read
#print axioms geometryRow035_floor_chars_parse
#print axioms geometryRow035_floor_parse
#print axioms decode_geometry_Rows_035
#print axioms geometryRow035_shape
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
#print axioms geometryRow036_shape
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
#print axioms geometryRow037_shape
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
#print axioms geometryRow038_shape
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
#print axioms geometryRow039_shape
#print axioms geometry_Rows_block_004_push_eq
#print axioms geometry_Rows_block_004_reverse
#print axioms decode_geometry_Rows_block_004
#print axioms geometry_Rows_block_004_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
