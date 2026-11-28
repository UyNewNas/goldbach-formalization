import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock003

/-! Local typed certificates for original cell 06, rows 24 through 31.
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

noncomputable def geometryRowsJson024 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped024 : GeometryRow :=
  { simplexId := 24,
    vertexIds := #[32, 30, 20, 16, 15, 13, 10, 8, 0],
    physicalVolume := ((346708611976473366642235269854063764794143 : ℚ) / (2369823747121152000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((28617713587 : ℚ) / (318780000000 : ℚ)), ((18149224063 : ℚ) / (199237500000 : ℚ)), ((96586253803 : ℚ) / (831600000000 : ℚ)), ((1677990944149 : ℚ) / (19126800000000 : ℚ)), ((1650165625243 : ℚ) / (19126800000000 : ℚ)), ((26434751017 : ℚ) / (347760000000 : ℚ)), ((940056031 : ℚ) / (24840000000 : ℚ)), ((624081679 : ℚ) / (17388000000 : ℚ)), ((3073152347 : ℚ) / (86940000000 : ℚ)), ((1160266673 : ℚ) / (37357031250 : ℚ))],
    jensenBound := ((4047692698487320844752956870279441835538712004895888708883405263847029591953125000000000 : ℚ) / (7681353844054821942832076131858083668400008622145444528326922846784207767237379244630248516452783789723 : ℚ)),
    jensenFloorQ96 := (41749314174839 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_simplexId_before"
  err.flush

theorem geometryRow024_simplexId_read :
    geometryRowsJson024.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped024.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_vertexIds_before"
  err.flush

theorem geometryRow024_vertexIds_read :
    geometryRowsJson024.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped024.vertexIds := by decide +kernel

noncomputable def geometryRow024_physicalVolumeNumeratorChars : List Char := ['3', '4', '6', '7', '0', '8', '6', '1', '1', '9', '7', '6', '4', '7', '3', '3', '6', '6', '6', '4', '2', '2', '3', '5', '2', '6', '9', '8', '5', '4', '0', '6', '3', '7', '6', '4', '7', '9', '4', '1', '4', '3']
noncomputable def geometryRow024_physicalVolumeDenominatorChars : List Char := ['2', '3', '6', '9', '8', '2', '3', '7', '4', '7', '1', '2', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_physicalVolumeText : String := String.ofList (geometryRow024_physicalVolumeNumeratorChars ++ '/' :: geometryRow024_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_physicalVolume_before_field"
  err.flush

theorem geometryRow024_physicalVolume_field :
    geometryRowsJson024.getObjVal? "physical_volume" = .ok (.str geometryRow024_physicalVolumeText) := by rfl

theorem geometryRow024_physicalVolume_numerator_no_slash :
    geometryRow024_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeNumeratorChars = some (346708611976473366642235269854063764794143 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow024_physicalVolumeDenominatorChars = some (2369823747121152000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow024_physicalVolume_denominator_nonzero : (2369823747121152000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_physicalVolume_parse :
    parseRational geometryRow024_physicalVolumeText = .ok geometryRowsTyped024.physicalVolume :=
  original_rational_fraction_of_chars geometryRow024_physicalVolumeNumeratorChars geometryRow024_physicalVolumeDenominatorChars
    (346708611976473366642235269854063764794143 : Int) (2369823747121152000000000000000000000000000000000000000000000000000 : Int)
    geometryRow024_physicalVolume_numerator_no_slash geometryRow024_physicalVolume_numerator_parse
    geometryRow024_physicalVolume_denominator_parse geometryRow024_physicalVolume_denominator_nonzero

theorem geometryRow024_physicalVolume_read :
    rationalField geometryRowsJson024 "physical_volume" = .ok geometryRowsTyped024.physicalVolume :=
  original_rationalField_of_string geometryRowsJson024 "physical_volume" geometryRow024_physicalVolumeText
    geometryRowsTyped024.physicalVolume geometryRow024_physicalVolume_field geometryRow024_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_physicalVolume_complete"
  err.flush

noncomputable def geometryRow024_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow024_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_meanGapText : String := String.ofList (geometryRow024_meanGapNumeratorChars ++ '/' :: geometryRow024_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_meanGap_before_field"
  err.flush

theorem geometryRow024_meanGap_field :
    geometryRowsJson024.getObjVal? "mean_gap" = .ok (.str geometryRow024_meanGapText) := by rfl

theorem geometryRow024_meanGap_numerator_no_slash :
    geometryRow024_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_meanGap_numerator_parse :
    SourceJson.intChars geometryRow024_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_parse :
    SourceJson.intChars geometryRow024_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow024_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_meanGap_parse :
    parseRational geometryRow024_meanGapText = .ok geometryRowsTyped024.meanGap :=
  original_rational_fraction_of_chars geometryRow024_meanGapNumeratorChars geometryRow024_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow024_meanGap_numerator_no_slash geometryRow024_meanGap_numerator_parse
    geometryRow024_meanGap_denominator_parse geometryRow024_meanGap_denominator_nonzero

theorem geometryRow024_meanGap_read :
    rationalField geometryRowsJson024 "mean_gap" = .ok geometryRowsTyped024.meanGap :=
  original_rationalField_of_string geometryRowsJson024 "mean_gap" geometryRow024_meanGapText
    geometryRowsTyped024.meanGap geometryRow024_meanGap_field geometryRow024_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_meanGap_complete"
  err.flush

noncomputable def geometryRow024_jensenBoundNumeratorChars : List Char := ['4', '0', '4', '7', '6', '9', '2', '6', '9', '8', '4', '8', '7', '3', '2', '0', '8', '4', '4', '7', '5', '2', '9', '5', '6', '8', '7', '0', '2', '7', '9', '4', '4', '1', '8', '3', '5', '5', '3', '8', '7', '1', '2', '0', '0', '4', '8', '9', '5', '8', '8', '8', '7', '0', '8', '8', '8', '3', '4', '0', '5', '2', '6', '3', '8', '4', '7', '0', '2', '9', '5', '9', '1', '9', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow024_jensenBoundDenominatorChars : List Char := ['7', '6', '8', '1', '3', '5', '3', '8', '4', '4', '0', '5', '4', '8', '2', '1', '9', '4', '2', '8', '3', '2', '0', '7', '6', '1', '3', '1', '8', '5', '8', '0', '8', '3', '6', '6', '8', '4', '0', '0', '0', '0', '8', '6', '2', '2', '1', '4', '5', '4', '4', '4', '5', '2', '8', '3', '2', '6', '9', '2', '2', '8', '4', '6', '7', '8', '4', '2', '0', '7', '7', '6', '7', '2', '3', '7', '3', '7', '9', '2', '4', '4', '6', '3', '0', '2', '4', '8', '5', '1', '6', '4', '5', '2', '7', '8', '3', '7', '8', '9', '7', '2', '3']
noncomputable def geometryRow024_jensenBoundText : String := String.ofList (geometryRow024_jensenBoundNumeratorChars ++ '/' :: geometryRow024_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_jensenBound_before_field"
  err.flush

theorem geometryRow024_jensenBound_field :
    geometryRowsJson024.getObjVal? "jensen_bound" = .ok (.str geometryRow024_jensenBoundText) := by rfl

theorem geometryRow024_jensenBound_numerator_no_slash :
    geometryRow024_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow024_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow024_jensenBoundNumeratorChars = some (4047692698487320844752956870279441835538712004895888708883405263847029591953125000000000 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow024_jensenBoundDenominatorChars = some (7681353844054821942832076131858083668400008622145444528326922846784207767237379244630248516452783789723 : Int) := by decide +kernel

theorem geometryRow024_jensenBound_denominator_nonzero : (7681353844054821942832076131858083668400008622145444528326922846784207767237379244630248516452783789723 : Int) ≠ 0 := by decide +kernel

theorem geometryRow024_jensenBound_parse :
    parseRational geometryRow024_jensenBoundText = .ok geometryRowsTyped024.jensenBound :=
  original_rational_fraction_of_chars geometryRow024_jensenBoundNumeratorChars geometryRow024_jensenBoundDenominatorChars
    (4047692698487320844752956870279441835538712004895888708883405263847029591953125000000000 : Int) (7681353844054821942832076131858083668400008622145444528326922846784207767237379244630248516452783789723 : Int)
    geometryRow024_jensenBound_numerator_no_slash geometryRow024_jensenBound_numerator_parse
    geometryRow024_jensenBound_denominator_parse geometryRow024_jensenBound_denominator_nonzero

theorem geometryRow024_jensenBound_read :
    rationalField geometryRowsJson024 "jensen_bound" = .ok geometryRowsTyped024.jensenBound :=
  original_rationalField_of_string geometryRowsJson024 "jensen_bound" geometryRow024_jensenBoundText
    geometryRowsTyped024.jensenBound geometryRow024_jensenBound_field geometryRow024_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_factorMaxima_before"
  err.flush

theorem geometryRow024_factorMaxima_read :
    rationalArrayField geometryRowsJson024 "factor_maxima" = .ok geometryRowsTyped024.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_gapWeightedMeans_before"
  err.flush

theorem geometryRow024_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson024 "gap_weighted_means" = .ok geometryRowsTyped024.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow024_floorChars : List Char := ['4', '1', '7', '4', '9', '3', '1', '4', '1', '7', '4', '8', '3', '9']
noncomputable def geometryRow024_floorText : String := String.ofList geometryRow024_floorChars

theorem geometryRow024_floor_text_read :
    geometryRowsJson024.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow024_floorText := by rfl

theorem geometryRow024_floor_chars_parse :
    SourceJson.intChars geometryRow024_floorChars = some (41749314174839 : Int) := by decide +kernel

theorem geometryRow024_floor_parse :
    parseInteger geometryRow024_floorText = .ok geometryRowsTyped024.jensenFloorQ96 := by
  simp only [geometryRow024_floorText, parseInteger, String.toList_ofList, geometryRow024_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_024 :
    decodeGeometryRow geometryRowsJson024 = .ok geometryRowsTyped024 :=
  original_geometryRow_of_fields geometryRowsJson024 geometryRowsTyped024 geometryRow024_floorText
    geometryRow024_simplexId_read geometryRow024_vertexIds_read
    geometryRow024_physicalVolume_read geometryRow024_meanGap_read
    geometryRow024_factorMaxima_read geometryRow024_gapWeightedMeans_read
    geometryRow024_jensenBound_read geometryRow024_floor_text_read geometryRow024_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_024_original_decoder_complete"
  err.flush

theorem geometryRow024_shape :
    geometryRowsTyped024.simplexId = 24 ∧
    geometryRowsTyped024.vertexIds.size = 9 ∧ geometryRowsTyped024.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped024.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped024.factorMaxima.size = 10 ∧ geometryRowsTyped024.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson025 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped025 : GeometryRow :=
  { simplexId := 25,
    vertexIds := #[32, 30, 20, 16, 14, 4, 3, 1, 0],
    physicalVolume := ((95855092119950721714189155438487723509311267 : ℚ) / (24513223914263347200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1544234459 : ℚ) / (521482500000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7056988761991821688051139 : ℚ) / (79421043871685466720000000 : ℚ)), ((326856432681132180458623 : ℚ) / (3545582315700244050000000 : ℚ)), ((713432178755657209669727 : ℚ) / (6204769052475427087500000 : ℚ)), ((17914011408372514964846089 : ℚ) / (198552609679213666800000000 : ℚ)), ((5875053567450152954520961 : ℚ) / (66184203226404555600000000 : ℚ)), ((264219925155913227970997 : ℚ) / (3610047448712975760000000 : ℚ)), ((4173824203838797708847 : ℚ) / (115521518358815224320000 : ℚ)), ((8503306257099451865707 : ℚ) / (236724422866424640000000 : ℚ)), ((249767181133836635275409 : ℚ) / (7220094897425951520000000 : ℚ)), ((37138048019973630613267 : ℚ) / (1181860771900081350000000 : ℚ))],
    jensenBound := ((81444616201450605879048262920512593317992799841656416650517482147757909192729029185038515501040007883658402996783348761805437433122455999133908916522673120195521493556320902878212863403853501371238599172096000000000000000 : ℚ) / (1369566528698675700926853648548658813532130341688944768488470471404211013224917802891386243434718189760353321200515334586174416021460573045100494166229584537414449519102365258083329981499597191110244342164645746191922075629051590325099 : ℚ)),
    jensenFloorQ96 := (4711496048645113 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_simplexId_before"
  err.flush

theorem geometryRow025_simplexId_read :
    geometryRowsJson025.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped025.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_vertexIds_before"
  err.flush

theorem geometryRow025_vertexIds_read :
    geometryRowsJson025.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped025.vertexIds := by decide +kernel

noncomputable def geometryRow025_physicalVolumeNumeratorChars : List Char := ['9', '5', '8', '5', '5', '0', '9', '2', '1', '1', '9', '9', '5', '0', '7', '2', '1', '7', '1', '4', '1', '8', '9', '1', '5', '5', '4', '3', '8', '4', '8', '7', '7', '2', '3', '5', '0', '9', '3', '1', '1', '2', '6', '7']
noncomputable def geometryRow025_physicalVolumeDenominatorChars : List Char := ['2', '4', '5', '1', '3', '2', '2', '3', '9', '1', '4', '2', '6', '3', '3', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_physicalVolumeText : String := String.ofList (geometryRow025_physicalVolumeNumeratorChars ++ '/' :: geometryRow025_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_physicalVolume_before_field"
  err.flush

theorem geometryRow025_physicalVolume_field :
    geometryRowsJson025.getObjVal? "physical_volume" = .ok (.str geometryRow025_physicalVolumeText) := by rfl

theorem geometryRow025_physicalVolume_numerator_no_slash :
    geometryRow025_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeNumeratorChars = some (95855092119950721714189155438487723509311267 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow025_physicalVolumeDenominatorChars = some (24513223914263347200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow025_physicalVolume_denominator_nonzero : (24513223914263347200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_physicalVolume_parse :
    parseRational geometryRow025_physicalVolumeText = .ok geometryRowsTyped025.physicalVolume :=
  original_rational_fraction_of_chars geometryRow025_physicalVolumeNumeratorChars geometryRow025_physicalVolumeDenominatorChars
    (95855092119950721714189155438487723509311267 : Int) (24513223914263347200000000000000000000000000000000000000000000000000 : Int)
    geometryRow025_physicalVolume_numerator_no_slash geometryRow025_physicalVolume_numerator_parse
    geometryRow025_physicalVolume_denominator_parse geometryRow025_physicalVolume_denominator_nonzero

theorem geometryRow025_physicalVolume_read :
    rationalField geometryRowsJson025 "physical_volume" = .ok geometryRowsTyped025.physicalVolume :=
  original_rationalField_of_string geometryRowsJson025 "physical_volume" geometryRow025_physicalVolumeText
    geometryRowsTyped025.physicalVolume geometryRow025_physicalVolume_field geometryRow025_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_physicalVolume_complete"
  err.flush

noncomputable def geometryRow025_meanGapNumeratorChars : List Char := ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9']
noncomputable def geometryRow025_meanGapDenominatorChars : List Char := ['5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_meanGapText : String := String.ofList (geometryRow025_meanGapNumeratorChars ++ '/' :: geometryRow025_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_meanGap_before_field"
  err.flush

theorem geometryRow025_meanGap_field :
    geometryRowsJson025.getObjVal? "mean_gap" = .ok (.str geometryRow025_meanGapText) := by rfl

theorem geometryRow025_meanGap_numerator_no_slash :
    geometryRow025_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_meanGap_numerator_parse :
    SourceJson.intChars geometryRow025_meanGapNumeratorChars = some (1544234459 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_parse :
    SourceJson.intChars geometryRow025_meanGapDenominatorChars = some (521482500000 : Int) := by decide +kernel

theorem geometryRow025_meanGap_denominator_nonzero : (521482500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_meanGap_parse :
    parseRational geometryRow025_meanGapText = .ok geometryRowsTyped025.meanGap :=
  original_rational_fraction_of_chars geometryRow025_meanGapNumeratorChars geometryRow025_meanGapDenominatorChars
    (1544234459 : Int) (521482500000 : Int)
    geometryRow025_meanGap_numerator_no_slash geometryRow025_meanGap_numerator_parse
    geometryRow025_meanGap_denominator_parse geometryRow025_meanGap_denominator_nonzero

theorem geometryRow025_meanGap_read :
    rationalField geometryRowsJson025 "mean_gap" = .ok geometryRowsTyped025.meanGap :=
  original_rationalField_of_string geometryRowsJson025 "mean_gap" geometryRow025_meanGapText
    geometryRowsTyped025.meanGap geometryRow025_meanGap_field geometryRow025_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_meanGap_complete"
  err.flush

noncomputable def geometryRow025_jensenBoundNumeratorChars : List Char := ['8', '1', '4', '4', '4', '6', '1', '6', '2', '0', '1', '4', '5', '0', '6', '0', '5', '8', '7', '9', '0', '4', '8', '2', '6', '2', '9', '2', '0', '5', '1', '2', '5', '9', '3', '3', '1', '7', '9', '9', '2', '7', '9', '9', '8', '4', '1', '6', '5', '6', '4', '1', '6', '6', '5', '0', '5', '1', '7', '4', '8', '2', '1', '4', '7', '7', '5', '7', '9', '0', '9', '1', '9', '2', '7', '2', '9', '0', '2', '9', '1', '8', '5', '0', '3', '8', '5', '1', '5', '5', '0', '1', '0', '4', '0', '0', '0', '7', '8', '8', '3', '6', '5', '8', '4', '0', '2', '9', '9', '6', '7', '8', '3', '3', '4', '8', '7', '6', '1', '8', '0', '5', '4', '3', '7', '4', '3', '3', '1', '2', '2', '4', '5', '5', '9', '9', '9', '1', '3', '3', '9', '0', '8', '9', '1', '6', '5', '2', '2', '6', '7', '3', '1', '2', '0', '1', '9', '5', '5', '2', '1', '4', '9', '3', '5', '5', '6', '3', '2', '0', '9', '0', '2', '8', '7', '8', '2', '1', '2', '8', '6', '3', '4', '0', '3', '8', '5', '3', '5', '0', '1', '3', '7', '1', '2', '3', '8', '5', '9', '9', '1', '7', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow025_jensenBoundDenominatorChars : List Char := ['1', '3', '6', '9', '5', '6', '6', '5', '2', '8', '6', '9', '8', '6', '7', '5', '7', '0', '0', '9', '2', '6', '8', '5', '3', '6', '4', '8', '5', '4', '8', '6', '5', '8', '8', '1', '3', '5', '3', '2', '1', '3', '0', '3', '4', '1', '6', '8', '8', '9', '4', '4', '7', '6', '8', '4', '8', '8', '4', '7', '0', '4', '7', '1', '4', '0', '4', '2', '1', '1', '0', '1', '3', '2', '2', '4', '9', '1', '7', '8', '0', '2', '8', '9', '1', '3', '8', '6', '2', '4', '3', '4', '3', '4', '7', '1', '8', '1', '8', '9', '7', '6', '0', '3', '5', '3', '3', '2', '1', '2', '0', '0', '5', '1', '5', '3', '3', '4', '5', '8', '6', '1', '7', '4', '4', '1', '6', '0', '2', '1', '4', '6', '0', '5', '7', '3', '0', '4', '5', '1', '0', '0', '4', '9', '4', '1', '6', '6', '2', '2', '9', '5', '8', '4', '5', '3', '7', '4', '1', '4', '4', '4', '9', '5', '1', '9', '1', '0', '2', '3', '6', '5', '2', '5', '8', '0', '8', '3', '3', '2', '9', '9', '8', '1', '4', '9', '9', '5', '9', '7', '1', '9', '1', '1', '1', '0', '2', '4', '4', '3', '4', '2', '1', '6', '4', '6', '4', '5', '7', '4', '6', '1', '9', '1', '9', '2', '2', '0', '7', '5', '6', '2', '9', '0', '5', '1', '5', '9', '0', '3', '2', '5', '0', '9', '9']
noncomputable def geometryRow025_jensenBoundText : String := String.ofList (geometryRow025_jensenBoundNumeratorChars ++ '/' :: geometryRow025_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_jensenBound_before_field"
  err.flush

theorem geometryRow025_jensenBound_field :
    geometryRowsJson025.getObjVal? "jensen_bound" = .ok (.str geometryRow025_jensenBoundText) := by rfl

theorem geometryRow025_jensenBound_numerator_no_slash :
    geometryRow025_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow025_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow025_jensenBoundNumeratorChars = some (81444616201450605879048262920512593317992799841656416650517482147757909192729029185038515501040007883658402996783348761805437433122455999133908916522673120195521493556320902878212863403853501371238599172096000000000000000 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow025_jensenBoundDenominatorChars = some (1369566528698675700926853648548658813532130341688944768488470471404211013224917802891386243434718189760353321200515334586174416021460573045100494166229584537414449519102365258083329981499597191110244342164645746191922075629051590325099 : Int) := by decide +kernel

theorem geometryRow025_jensenBound_denominator_nonzero : (1369566528698675700926853648548658813532130341688944768488470471404211013224917802891386243434718189760353321200515334586174416021460573045100494166229584537414449519102365258083329981499597191110244342164645746191922075629051590325099 : Int) ≠ 0 := by decide +kernel

theorem geometryRow025_jensenBound_parse :
    parseRational geometryRow025_jensenBoundText = .ok geometryRowsTyped025.jensenBound :=
  original_rational_fraction_of_chars geometryRow025_jensenBoundNumeratorChars geometryRow025_jensenBoundDenominatorChars
    (81444616201450605879048262920512593317992799841656416650517482147757909192729029185038515501040007883658402996783348761805437433122455999133908916522673120195521493556320902878212863403853501371238599172096000000000000000 : Int) (1369566528698675700926853648548658813532130341688944768488470471404211013224917802891386243434718189760353321200515334586174416021460573045100494166229584537414449519102365258083329981499597191110244342164645746191922075629051590325099 : Int)
    geometryRow025_jensenBound_numerator_no_slash geometryRow025_jensenBound_numerator_parse
    geometryRow025_jensenBound_denominator_parse geometryRow025_jensenBound_denominator_nonzero

theorem geometryRow025_jensenBound_read :
    rationalField geometryRowsJson025 "jensen_bound" = .ok geometryRowsTyped025.jensenBound :=
  original_rationalField_of_string geometryRowsJson025 "jensen_bound" geometryRow025_jensenBoundText
    geometryRowsTyped025.jensenBound geometryRow025_jensenBound_field geometryRow025_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_factorMaxima_before"
  err.flush

theorem geometryRow025_factorMaxima_read :
    rationalArrayField geometryRowsJson025 "factor_maxima" = .ok geometryRowsTyped025.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_gapWeightedMeans_before"
  err.flush

theorem geometryRow025_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson025 "gap_weighted_means" = .ok geometryRowsTyped025.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow025_floorChars : List Char := ['4', '7', '1', '1', '4', '9', '6', '0', '4', '8', '6', '4', '5', '1', '1', '3']
noncomputable def geometryRow025_floorText : String := String.ofList geometryRow025_floorChars

theorem geometryRow025_floor_text_read :
    geometryRowsJson025.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow025_floorText := by rfl

theorem geometryRow025_floor_chars_parse :
    SourceJson.intChars geometryRow025_floorChars = some (4711496048645113 : Int) := by decide +kernel

theorem geometryRow025_floor_parse :
    parseInteger geometryRow025_floorText = .ok geometryRowsTyped025.jensenFloorQ96 := by
  simp only [geometryRow025_floorText, parseInteger, String.toList_ofList, geometryRow025_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_025 :
    decodeGeometryRow geometryRowsJson025 = .ok geometryRowsTyped025 :=
  original_geometryRow_of_fields geometryRowsJson025 geometryRowsTyped025 geometryRow025_floorText
    geometryRow025_simplexId_read geometryRow025_vertexIds_read
    geometryRow025_physicalVolume_read geometryRow025_meanGap_read
    geometryRow025_factorMaxima_read geometryRow025_gapWeightedMeans_read
    geometryRow025_jensenBound_read geometryRow025_floor_text_read geometryRow025_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_025_original_decoder_complete"
  err.flush

theorem geometryRow025_shape :
    geometryRowsTyped025.simplexId = 25 ∧
    geometryRowsTyped025.vertexIds.size = 9 ∧ geometryRowsTyped025.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped025.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped025.factorMaxima.size = 10 ∧ geometryRowsTyped025.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson026 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped026 : GeometryRow :=
  { simplexId := 26,
    vertexIds := #[32, 30, 20, 16, 14, 12, 3, 1, 0],
    physicalVolume := ((2539974951808520187853958938777381435686001 : ℚ) / (76009996633374720000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((24277423 : ℚ) / (10864218750 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1788174574762994570344387 : ℚ) / (19977673892065021440000000 : ℚ)), ((93966724495675051522189 : ℚ) / (1019269076125766400000000 : ℚ)), ((11527494015519173593788781 : ℚ) / (99888369460325107200000000 : ℚ)), ((8924485374996186243263941 : ℚ) / (99888369460325107200000000 : ℚ)), ((2926389867188851207300439 : ℚ) / (33296123153441702400000000 : ℚ)), ((134641094080178495019947 : ℚ) / (1816152172005911040000000 : ℚ)), ((27304874756900635386937 : ℚ) / (726460868802364416000000 : ℚ)), ((128619961372861995613337 : ℚ) / (3632304344011822080000000 : ℚ)), ((61870361767427833317361 : ℚ) / (1816152172005911040000000 : ℚ)), ((10676668948245824474981 : ℚ) / (339756358708588800000000 : ℚ))],
    jensenBound := ((49381153281038399412480847806533731026206373835222235052025302058705699714415478134893900373700689129784444696635823837837740631326279963735515422955286289046162846092798818911608224707790741470105829376000000000000000000 : ℚ) / (130585072192145040334925580602749972959134957920410651366841521626432510816621870697254360284834263970573639076699539068020675178862660026095239099706246829971667987893603311858989319322952132630386576566460365159425275532134351979151 : ℚ)),
    jensenFloorQ96 := (29960377335743016 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_simplexId_before"
  err.flush

theorem geometryRow026_simplexId_read :
    geometryRowsJson026.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped026.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_vertexIds_before"
  err.flush

theorem geometryRow026_vertexIds_read :
    geometryRowsJson026.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped026.vertexIds := by decide +kernel

noncomputable def geometryRow026_physicalVolumeNumeratorChars : List Char := ['2', '5', '3', '9', '9', '7', '4', '9', '5', '1', '8', '0', '8', '5', '2', '0', '1', '8', '7', '8', '5', '3', '9', '5', '8', '9', '3', '8', '7', '7', '7', '3', '8', '1', '4', '3', '5', '6', '8', '6', '0', '0', '1']
noncomputable def geometryRow026_physicalVolumeDenominatorChars : List Char := ['7', '6', '0', '0', '9', '9', '9', '6', '6', '3', '3', '3', '7', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_physicalVolumeText : String := String.ofList (geometryRow026_physicalVolumeNumeratorChars ++ '/' :: geometryRow026_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_physicalVolume_before_field"
  err.flush

theorem geometryRow026_physicalVolume_field :
    geometryRowsJson026.getObjVal? "physical_volume" = .ok (.str geometryRow026_physicalVolumeText) := by rfl

theorem geometryRow026_physicalVolume_numerator_no_slash :
    geometryRow026_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeNumeratorChars = some (2539974951808520187853958938777381435686001 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow026_physicalVolumeDenominatorChars = some (76009996633374720000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_physicalVolume_denominator_nonzero : (76009996633374720000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_physicalVolume_parse :
    parseRational geometryRow026_physicalVolumeText = .ok geometryRowsTyped026.physicalVolume :=
  original_rational_fraction_of_chars geometryRow026_physicalVolumeNumeratorChars geometryRow026_physicalVolumeDenominatorChars
    (2539974951808520187853958938777381435686001 : Int) (76009996633374720000000000000000000000000000000000000000000000000 : Int)
    geometryRow026_physicalVolume_numerator_no_slash geometryRow026_physicalVolume_numerator_parse
    geometryRow026_physicalVolume_denominator_parse geometryRow026_physicalVolume_denominator_nonzero

theorem geometryRow026_physicalVolume_read :
    rationalField geometryRowsJson026 "physical_volume" = .ok geometryRowsTyped026.physicalVolume :=
  original_rationalField_of_string geometryRowsJson026 "physical_volume" geometryRow026_physicalVolumeText
    geometryRowsTyped026.physicalVolume geometryRow026_physicalVolume_field geometryRow026_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_physicalVolume_complete"
  err.flush

noncomputable def geometryRow026_meanGapNumeratorChars : List Char := ['2', '4', '2', '7', '7', '4', '2', '3']
noncomputable def geometryRow026_meanGapDenominatorChars : List Char := ['1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0']
noncomputable def geometryRow026_meanGapText : String := String.ofList (geometryRow026_meanGapNumeratorChars ++ '/' :: geometryRow026_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_meanGap_before_field"
  err.flush

theorem geometryRow026_meanGap_field :
    geometryRowsJson026.getObjVal? "mean_gap" = .ok (.str geometryRow026_meanGapText) := by rfl

theorem geometryRow026_meanGap_numerator_no_slash :
    geometryRow026_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_meanGap_numerator_parse :
    SourceJson.intChars geometryRow026_meanGapNumeratorChars = some (24277423 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_parse :
    SourceJson.intChars geometryRow026_meanGapDenominatorChars = some (10864218750 : Int) := by decide +kernel

theorem geometryRow026_meanGap_denominator_nonzero : (10864218750 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_meanGap_parse :
    parseRational geometryRow026_meanGapText = .ok geometryRowsTyped026.meanGap :=
  original_rational_fraction_of_chars geometryRow026_meanGapNumeratorChars geometryRow026_meanGapDenominatorChars
    (24277423 : Int) (10864218750 : Int)
    geometryRow026_meanGap_numerator_no_slash geometryRow026_meanGap_numerator_parse
    geometryRow026_meanGap_denominator_parse geometryRow026_meanGap_denominator_nonzero

theorem geometryRow026_meanGap_read :
    rationalField geometryRowsJson026 "mean_gap" = .ok geometryRowsTyped026.meanGap :=
  original_rationalField_of_string geometryRowsJson026 "mean_gap" geometryRow026_meanGapText
    geometryRowsTyped026.meanGap geometryRow026_meanGap_field geometryRow026_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_meanGap_complete"
  err.flush

noncomputable def geometryRow026_jensenBoundNumeratorChars : List Char := ['4', '9', '3', '8', '1', '1', '5', '3', '2', '8', '1', '0', '3', '8', '3', '9', '9', '4', '1', '2', '4', '8', '0', '8', '4', '7', '8', '0', '6', '5', '3', '3', '7', '3', '1', '0', '2', '6', '2', '0', '6', '3', '7', '3', '8', '3', '5', '2', '2', '2', '2', '3', '5', '0', '5', '2', '0', '2', '5', '3', '0', '2', '0', '5', '8', '7', '0', '5', '6', '9', '9', '7', '1', '4', '4', '1', '5', '4', '7', '8', '1', '3', '4', '8', '9', '3', '9', '0', '0', '3', '7', '3', '7', '0', '0', '6', '8', '9', '1', '2', '9', '7', '8', '4', '4', '4', '4', '6', '9', '6', '6', '3', '5', '8', '2', '3', '8', '3', '7', '8', '3', '7', '7', '4', '0', '6', '3', '1', '3', '2', '6', '2', '7', '9', '9', '6', '3', '7', '3', '5', '5', '1', '5', '4', '2', '2', '9', '5', '5', '2', '8', '6', '2', '8', '9', '0', '4', '6', '1', '6', '2', '8', '4', '6', '0', '9', '2', '7', '9', '8', '8', '1', '8', '9', '1', '1', '6', '0', '8', '2', '2', '4', '7', '0', '7', '7', '9', '0', '7', '4', '1', '4', '7', '0', '1', '0', '5', '8', '2', '9', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow026_jensenBoundDenominatorChars : List Char := ['1', '3', '0', '5', '8', '5', '0', '7', '2', '1', '9', '2', '1', '4', '5', '0', '4', '0', '3', '3', '4', '9', '2', '5', '5', '8', '0', '6', '0', '2', '7', '4', '9', '9', '7', '2', '9', '5', '9', '1', '3', '4', '9', '5', '7', '9', '2', '0', '4', '1', '0', '6', '5', '1', '3', '6', '6', '8', '4', '1', '5', '2', '1', '6', '2', '6', '4', '3', '2', '5', '1', '0', '8', '1', '6', '6', '2', '1', '8', '7', '0', '6', '9', '7', '2', '5', '4', '3', '6', '0', '2', '8', '4', '8', '3', '4', '2', '6', '3', '9', '7', '0', '5', '7', '3', '6', '3', '9', '0', '7', '6', '6', '9', '9', '5', '3', '9', '0', '6', '8', '0', '2', '0', '6', '7', '5', '1', '7', '8', '8', '6', '2', '6', '6', '0', '0', '2', '6', '0', '9', '5', '2', '3', '9', '0', '9', '9', '7', '0', '6', '2', '4', '6', '8', '2', '9', '9', '7', '1', '6', '6', '7', '9', '8', '7', '8', '9', '3', '6', '0', '3', '3', '1', '1', '8', '5', '8', '9', '8', '9', '3', '1', '9', '3', '2', '2', '9', '5', '2', '1', '3', '2', '6', '3', '0', '3', '8', '6', '5', '7', '6', '5', '6', '6', '4', '6', '0', '3', '6', '5', '1', '5', '9', '4', '2', '5', '2', '7', '5', '5', '3', '2', '1', '3', '4', '3', '5', '1', '9', '7', '9', '1', '5', '1']
noncomputable def geometryRow026_jensenBoundText : String := String.ofList (geometryRow026_jensenBoundNumeratorChars ++ '/' :: geometryRow026_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_jensenBound_before_field"
  err.flush

theorem geometryRow026_jensenBound_field :
    geometryRowsJson026.getObjVal? "jensen_bound" = .ok (.str geometryRow026_jensenBoundText) := by rfl

theorem geometryRow026_jensenBound_numerator_no_slash :
    geometryRow026_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow026_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow026_jensenBoundNumeratorChars = some (49381153281038399412480847806533731026206373835222235052025302058705699714415478134893900373700689129784444696635823837837740631326279963735515422955286289046162846092798818911608224707790741470105829376000000000000000000 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow026_jensenBoundDenominatorChars = some (130585072192145040334925580602749972959134957920410651366841521626432510816621870697254360284834263970573639076699539068020675178862660026095239099706246829971667987893603311858989319322952132630386576566460365159425275532134351979151 : Int) := by decide +kernel

theorem geometryRow026_jensenBound_denominator_nonzero : (130585072192145040334925580602749972959134957920410651366841521626432510816621870697254360284834263970573639076699539068020675178862660026095239099706246829971667987893603311858989319322952132630386576566460365159425275532134351979151 : Int) ≠ 0 := by decide +kernel

theorem geometryRow026_jensenBound_parse :
    parseRational geometryRow026_jensenBoundText = .ok geometryRowsTyped026.jensenBound :=
  original_rational_fraction_of_chars geometryRow026_jensenBoundNumeratorChars geometryRow026_jensenBoundDenominatorChars
    (49381153281038399412480847806533731026206373835222235052025302058705699714415478134893900373700689129784444696635823837837740631326279963735515422955286289046162846092798818911608224707790741470105829376000000000000000000 : Int) (130585072192145040334925580602749972959134957920410651366841521626432510816621870697254360284834263970573639076699539068020675178862660026095239099706246829971667987893603311858989319322952132630386576566460365159425275532134351979151 : Int)
    geometryRow026_jensenBound_numerator_no_slash geometryRow026_jensenBound_numerator_parse
    geometryRow026_jensenBound_denominator_parse geometryRow026_jensenBound_denominator_nonzero

theorem geometryRow026_jensenBound_read :
    rationalField geometryRowsJson026 "jensen_bound" = .ok geometryRowsTyped026.jensenBound :=
  original_rationalField_of_string geometryRowsJson026 "jensen_bound" geometryRow026_jensenBoundText
    geometryRowsTyped026.jensenBound geometryRow026_jensenBound_field geometryRow026_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_factorMaxima_before"
  err.flush

theorem geometryRow026_factorMaxima_read :
    rationalArrayField geometryRowsJson026 "factor_maxima" = .ok geometryRowsTyped026.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_gapWeightedMeans_before"
  err.flush

theorem geometryRow026_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson026 "gap_weighted_means" = .ok geometryRowsTyped026.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow026_floorChars : List Char := ['2', '9', '9', '6', '0', '3', '7', '7', '3', '3', '5', '7', '4', '3', '0', '1', '6']
noncomputable def geometryRow026_floorText : String := String.ofList geometryRow026_floorChars

theorem geometryRow026_floor_text_read :
    geometryRowsJson026.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow026_floorText := by rfl

theorem geometryRow026_floor_chars_parse :
    SourceJson.intChars geometryRow026_floorChars = some (29960377335743016 : Int) := by decide +kernel

theorem geometryRow026_floor_parse :
    parseInteger geometryRow026_floorText = .ok geometryRowsTyped026.jensenFloorQ96 := by
  simp only [geometryRow026_floorText, parseInteger, String.toList_ofList, geometryRow026_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_026 :
    decodeGeometryRow geometryRowsJson026 = .ok geometryRowsTyped026 :=
  original_geometryRow_of_fields geometryRowsJson026 geometryRowsTyped026 geometryRow026_floorText
    geometryRow026_simplexId_read geometryRow026_vertexIds_read
    geometryRow026_physicalVolume_read geometryRow026_meanGap_read
    geometryRow026_factorMaxima_read geometryRow026_gapWeightedMeans_read
    geometryRow026_jensenBound_read geometryRow026_floor_text_read geometryRow026_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_026_original_decoder_complete"
  err.flush

theorem geometryRow026_shape :
    geometryRowsTyped026.simplexId = 26 ∧
    geometryRowsTyped026.vertexIds.size = 9 ∧ geometryRowsTyped026.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped026.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped026.factorMaxima.size = 10 ∧ geometryRowsTyped026.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson027 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped027 : GeometryRow :=
  { simplexId := 27,
    vertexIds := #[32, 30, 20, 16, 14, 12, 10, 1, 0],
    physicalVolume := ((193419332776186601314719063489180189083 : ℚ) / (16571946940416000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7712555304871992052277 : ℚ) / (85738087468923120000000 : ℚ)), ((5631141001482339540523 : ℚ) / (61241491049230800000000 : ℚ)), ((99303129520990046746861 : ℚ) / (857380874689231200000000 : ℚ)), ((75851675642442188915551 : ℚ) / (857380874689231200000000 : ℚ)), ((24868124541058099580449 : ℚ) / (285793624896410400000000 : ℚ)), ((9364603461569303809 : ℚ) / (124709945409342720000 : ℚ)), ((304407333021039010421 : ℚ) / (7794371588083920000000 : ℚ)), ((272001181358364552551 : ℚ) / (7794371588083920000000 : ℚ)), ((263522715495839929943 : ℚ) / (7794371588083920000000 : ℚ)), ((639857394865783390067 : ℚ) / (20413830349743600000000 : ℚ))],
    jensenBound := ((842518657422012609042394723775099047010394810304663610597488605005625180583821097957785062455912101753089573596029624141518821728186347313732176897346238412064161135345394096537600000000000000 : ℚ) / (9767836362516592491740341644925593807540696842186824387734087545162843560200128071481989467714697199334723662914237110589610706024472520727080886524318899928095603690407836110555371893512863426963924812013539 : ℚ)),
    jensenFloorQ96 := (6833775939130 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_simplexId_before"
  err.flush

theorem geometryRow027_simplexId_read :
    geometryRowsJson027.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped027.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_vertexIds_before"
  err.flush

theorem geometryRow027_vertexIds_read :
    geometryRowsJson027.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped027.vertexIds := by decide +kernel

noncomputable def geometryRow027_physicalVolumeNumeratorChars : List Char := ['1', '9', '3', '4', '1', '9', '3', '3', '2', '7', '7', '6', '1', '8', '6', '6', '0', '1', '3', '1', '4', '7', '1', '9', '0', '6', '3', '4', '8', '9', '1', '8', '0', '1', '8', '9', '0', '8', '3']
noncomputable def geometryRow027_physicalVolumeDenominatorChars : List Char := ['1', '6', '5', '7', '1', '9', '4', '6', '9', '4', '0', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_physicalVolumeText : String := String.ofList (geometryRow027_physicalVolumeNumeratorChars ++ '/' :: geometryRow027_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_physicalVolume_before_field"
  err.flush

theorem geometryRow027_physicalVolume_field :
    geometryRowsJson027.getObjVal? "physical_volume" = .ok (.str geometryRow027_physicalVolumeText) := by rfl

theorem geometryRow027_physicalVolume_numerator_no_slash :
    geometryRow027_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeNumeratorChars = some (193419332776186601314719063489180189083 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow027_physicalVolumeDenominatorChars = some (16571946940416000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow027_physicalVolume_denominator_nonzero : (16571946940416000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_physicalVolume_parse :
    parseRational geometryRow027_physicalVolumeText = .ok geometryRowsTyped027.physicalVolume :=
  original_rational_fraction_of_chars geometryRow027_physicalVolumeNumeratorChars geometryRow027_physicalVolumeDenominatorChars
    (193419332776186601314719063489180189083 : Int) (16571946940416000000000000000000000000000000000000000000000000000 : Int)
    geometryRow027_physicalVolume_numerator_no_slash geometryRow027_physicalVolume_numerator_parse
    geometryRow027_physicalVolume_denominator_parse geometryRow027_physicalVolume_denominator_nonzero

theorem geometryRow027_physicalVolume_read :
    rationalField geometryRowsJson027 "physical_volume" = .ok geometryRowsTyped027.physicalVolume :=
  original_rationalField_of_string geometryRowsJson027 "physical_volume" geometryRow027_physicalVolumeText
    geometryRowsTyped027.physicalVolume geometryRow027_physicalVolume_field geometryRow027_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_physicalVolume_complete"
  err.flush

noncomputable def geometryRow027_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow027_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_meanGapText : String := String.ofList (geometryRow027_meanGapNumeratorChars ++ '/' :: geometryRow027_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_meanGap_before_field"
  err.flush

theorem geometryRow027_meanGap_field :
    geometryRowsJson027.getObjVal? "mean_gap" = .ok (.str geometryRow027_meanGapText) := by rfl

theorem geometryRow027_meanGap_numerator_no_slash :
    geometryRow027_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_meanGap_numerator_parse :
    SourceJson.intChars geometryRow027_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_parse :
    SourceJson.intChars geometryRow027_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow027_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_meanGap_parse :
    parseRational geometryRow027_meanGapText = .ok geometryRowsTyped027.meanGap :=
  original_rational_fraction_of_chars geometryRow027_meanGapNumeratorChars geometryRow027_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow027_meanGap_numerator_no_slash geometryRow027_meanGap_numerator_parse
    geometryRow027_meanGap_denominator_parse geometryRow027_meanGap_denominator_nonzero

theorem geometryRow027_meanGap_read :
    rationalField geometryRowsJson027 "mean_gap" = .ok geometryRowsTyped027.meanGap :=
  original_rationalField_of_string geometryRowsJson027 "mean_gap" geometryRow027_meanGapText
    geometryRowsTyped027.meanGap geometryRow027_meanGap_field geometryRow027_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_meanGap_complete"
  err.flush

noncomputable def geometryRow027_jensenBoundNumeratorChars : List Char := ['8', '4', '2', '5', '1', '8', '6', '5', '7', '4', '2', '2', '0', '1', '2', '6', '0', '9', '0', '4', '2', '3', '9', '4', '7', '2', '3', '7', '7', '5', '0', '9', '9', '0', '4', '7', '0', '1', '0', '3', '9', '4', '8', '1', '0', '3', '0', '4', '6', '6', '3', '6', '1', '0', '5', '9', '7', '4', '8', '8', '6', '0', '5', '0', '0', '5', '6', '2', '5', '1', '8', '0', '5', '8', '3', '8', '2', '1', '0', '9', '7', '9', '5', '7', '7', '8', '5', '0', '6', '2', '4', '5', '5', '9', '1', '2', '1', '0', '1', '7', '5', '3', '0', '8', '9', '5', '7', '3', '5', '9', '6', '0', '2', '9', '6', '2', '4', '1', '4', '1', '5', '1', '8', '8', '2', '1', '7', '2', '8', '1', '8', '6', '3', '4', '7', '3', '1', '3', '7', '3', '2', '1', '7', '6', '8', '9', '7', '3', '4', '6', '2', '3', '8', '4', '1', '2', '0', '6', '4', '1', '6', '1', '1', '3', '5', '3', '4', '5', '3', '9', '4', '0', '9', '6', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow027_jensenBoundDenominatorChars : List Char := ['9', '7', '6', '7', '8', '3', '6', '3', '6', '2', '5', '1', '6', '5', '9', '2', '4', '9', '1', '7', '4', '0', '3', '4', '1', '6', '4', '4', '9', '2', '5', '5', '9', '3', '8', '0', '7', '5', '4', '0', '6', '9', '6', '8', '4', '2', '1', '8', '6', '8', '2', '4', '3', '8', '7', '7', '3', '4', '0', '8', '7', '5', '4', '5', '1', '6', '2', '8', '4', '3', '5', '6', '0', '2', '0', '0', '1', '2', '8', '0', '7', '1', '4', '8', '1', '9', '8', '9', '4', '6', '7', '7', '1', '4', '6', '9', '7', '1', '9', '9', '3', '3', '4', '7', '2', '3', '6', '6', '2', '9', '1', '4', '2', '3', '7', '1', '1', '0', '5', '8', '9', '6', '1', '0', '7', '0', '6', '0', '2', '4', '4', '7', '2', '5', '2', '0', '7', '2', '7', '0', '8', '0', '8', '8', '6', '5', '2', '4', '3', '1', '8', '8', '9', '9', '9', '2', '8', '0', '9', '5', '6', '0', '3', '6', '9', '0', '4', '0', '7', '8', '3', '6', '1', '1', '0', '5', '5', '5', '3', '7', '1', '8', '9', '3', '5', '1', '2', '8', '6', '3', '4', '2', '6', '9', '6', '3', '9', '2', '4', '8', '1', '2', '0', '1', '3', '5', '3', '9']
noncomputable def geometryRow027_jensenBoundText : String := String.ofList (geometryRow027_jensenBoundNumeratorChars ++ '/' :: geometryRow027_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_jensenBound_before_field"
  err.flush

theorem geometryRow027_jensenBound_field :
    geometryRowsJson027.getObjVal? "jensen_bound" = .ok (.str geometryRow027_jensenBoundText) := by rfl

theorem geometryRow027_jensenBound_numerator_no_slash :
    geometryRow027_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow027_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow027_jensenBoundNumeratorChars = some (842518657422012609042394723775099047010394810304663610597488605005625180583821097957785062455912101753089573596029624141518821728186347313732176897346238412064161135345394096537600000000000000 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow027_jensenBoundDenominatorChars = some (9767836362516592491740341644925593807540696842186824387734087545162843560200128071481989467714697199334723662914237110589610706024472520727080886524318899928095603690407836110555371893512863426963924812013539 : Int) := by decide +kernel

theorem geometryRow027_jensenBound_denominator_nonzero : (9767836362516592491740341644925593807540696842186824387734087545162843560200128071481989467714697199334723662914237110589610706024472520727080886524318899928095603690407836110555371893512863426963924812013539 : Int) ≠ 0 := by decide +kernel

theorem geometryRow027_jensenBound_parse :
    parseRational geometryRow027_jensenBoundText = .ok geometryRowsTyped027.jensenBound :=
  original_rational_fraction_of_chars geometryRow027_jensenBoundNumeratorChars geometryRow027_jensenBoundDenominatorChars
    (842518657422012609042394723775099047010394810304663610597488605005625180583821097957785062455912101753089573596029624141518821728186347313732176897346238412064161135345394096537600000000000000 : Int) (9767836362516592491740341644925593807540696842186824387734087545162843560200128071481989467714697199334723662914237110589610706024472520727080886524318899928095603690407836110555371893512863426963924812013539 : Int)
    geometryRow027_jensenBound_numerator_no_slash geometryRow027_jensenBound_numerator_parse
    geometryRow027_jensenBound_denominator_parse geometryRow027_jensenBound_denominator_nonzero

theorem geometryRow027_jensenBound_read :
    rationalField geometryRowsJson027 "jensen_bound" = .ok geometryRowsTyped027.jensenBound :=
  original_rationalField_of_string geometryRowsJson027 "jensen_bound" geometryRow027_jensenBoundText
    geometryRowsTyped027.jensenBound geometryRow027_jensenBound_field geometryRow027_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_factorMaxima_before"
  err.flush

theorem geometryRow027_factorMaxima_read :
    rationalArrayField geometryRowsJson027 "factor_maxima" = .ok geometryRowsTyped027.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_gapWeightedMeans_before"
  err.flush

theorem geometryRow027_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson027 "gap_weighted_means" = .ok geometryRowsTyped027.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow027_floorChars : List Char := ['6', '8', '3', '3', '7', '7', '5', '9', '3', '9', '1', '3', '0']
noncomputable def geometryRow027_floorText : String := String.ofList geometryRow027_floorChars

theorem geometryRow027_floor_text_read :
    geometryRowsJson027.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow027_floorText := by rfl

theorem geometryRow027_floor_chars_parse :
    SourceJson.intChars geometryRow027_floorChars = some (6833775939130 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_027_original_decoder_complete"
  err.flush

theorem geometryRow027_shape :
    geometryRowsTyped027.simplexId = 27 ∧
    geometryRowsTyped027.vertexIds.size = 9 ∧ geometryRowsTyped027.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped027.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped027.factorMaxima.size = 10 ∧ geometryRowsTyped027.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson028 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped028 : GeometryRow :=
  { simplexId := 28,
    vertexIds := #[32, 30, 20, 16, 14, 12, 10, 8, 0],
    physicalVolume := ((4280144497779622236986773274582215644863 : ℚ) / (36525923868672000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7625977187107 : ℚ) / (85433040000000 : ℚ)), ((38694086120027 : ℚ) / (427165200000000 : ℚ)), ((297417671529001 : ℚ) / (2562991200000000 : ℚ)), ((225025324366211 : ℚ) / (2562991200000000 : ℚ)), ((221296731632807 : ℚ) / (2562991200000000 : ℚ)), ((3551730040217 : ℚ) / (46599840000000 : ℚ)), ((920163646517 : ℚ) / (23299920000000 : ℚ)), ((829158541601 : ℚ) / (23299920000000 : ℚ)), ((803813640593 : ℚ) / (23299920000000 : ℚ)), ((39583937679547 : ℚ) / (1281495600000000 : ℚ))],
    jensenBound := ((159628330512101026552693737658289517671953638492620662856407424675592694338928107604097652516362649600000000000000000 : ℚ) / (376816772960704469956657207065178812364827345045747066258645749932216096739524689502473625436709975163152685136509751392447257874307 : ℚ)),
    jensenFloorQ96 := (33562888435999 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_simplexId_before"
  err.flush

theorem geometryRow028_simplexId_read :
    geometryRowsJson028.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped028.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_vertexIds_before"
  err.flush

theorem geometryRow028_vertexIds_read :
    geometryRowsJson028.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped028.vertexIds := by decide +kernel

noncomputable def geometryRow028_physicalVolumeNumeratorChars : List Char := ['4', '2', '8', '0', '1', '4', '4', '4', '9', '7', '7', '7', '9', '6', '2', '2', '2', '3', '6', '9', '8', '6', '7', '7', '3', '2', '7', '4', '5', '8', '2', '2', '1', '5', '6', '4', '4', '8', '6', '3']
noncomputable def geometryRow028_physicalVolumeDenominatorChars : List Char := ['3', '6', '5', '2', '5', '9', '2', '3', '8', '6', '8', '6', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_physicalVolumeText : String := String.ofList (geometryRow028_physicalVolumeNumeratorChars ++ '/' :: geometryRow028_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_physicalVolume_before_field"
  err.flush

theorem geometryRow028_physicalVolume_field :
    geometryRowsJson028.getObjVal? "physical_volume" = .ok (.str geometryRow028_physicalVolumeText) := by rfl

theorem geometryRow028_physicalVolume_numerator_no_slash :
    geometryRow028_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeNumeratorChars = some (4280144497779622236986773274582215644863 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow028_physicalVolumeDenominatorChars = some (36525923868672000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow028_physicalVolume_denominator_nonzero : (36525923868672000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_physicalVolume_parse :
    parseRational geometryRow028_physicalVolumeText = .ok geometryRowsTyped028.physicalVolume :=
  original_rational_fraction_of_chars geometryRow028_physicalVolumeNumeratorChars geometryRow028_physicalVolumeDenominatorChars
    (4280144497779622236986773274582215644863 : Int) (36525923868672000000000000000000000000000000000000000000000000000 : Int)
    geometryRow028_physicalVolume_numerator_no_slash geometryRow028_physicalVolume_numerator_parse
    geometryRow028_physicalVolume_denominator_parse geometryRow028_physicalVolume_denominator_nonzero

theorem geometryRow028_physicalVolume_read :
    rationalField geometryRowsJson028 "physical_volume" = .ok geometryRowsTyped028.physicalVolume :=
  original_rationalField_of_string geometryRowsJson028 "physical_volume" geometryRow028_physicalVolumeText
    geometryRowsTyped028.physicalVolume geometryRow028_physicalVolume_field geometryRow028_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_physicalVolume_complete"
  err.flush

noncomputable def geometryRow028_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow028_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_meanGapText : String := String.ofList (geometryRow028_meanGapNumeratorChars ++ '/' :: geometryRow028_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_meanGap_before_field"
  err.flush

theorem geometryRow028_meanGap_field :
    geometryRowsJson028.getObjVal? "mean_gap" = .ok (.str geometryRow028_meanGapText) := by rfl

theorem geometryRow028_meanGap_numerator_no_slash :
    geometryRow028_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_meanGap_numerator_parse :
    SourceJson.intChars geometryRow028_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_parse :
    SourceJson.intChars geometryRow028_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow028_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_meanGap_parse :
    parseRational geometryRow028_meanGapText = .ok geometryRowsTyped028.meanGap :=
  original_rational_fraction_of_chars geometryRow028_meanGapNumeratorChars geometryRow028_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow028_meanGap_numerator_no_slash geometryRow028_meanGap_numerator_parse
    geometryRow028_meanGap_denominator_parse geometryRow028_meanGap_denominator_nonzero

theorem geometryRow028_meanGap_read :
    rationalField geometryRowsJson028 "mean_gap" = .ok geometryRowsTyped028.meanGap :=
  original_rationalField_of_string geometryRowsJson028 "mean_gap" geometryRow028_meanGapText
    geometryRowsTyped028.meanGap geometryRow028_meanGap_field geometryRow028_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_meanGap_complete"
  err.flush

noncomputable def geometryRow028_jensenBoundNumeratorChars : List Char := ['1', '5', '9', '6', '2', '8', '3', '3', '0', '5', '1', '2', '1', '0', '1', '0', '2', '6', '5', '5', '2', '6', '9', '3', '7', '3', '7', '6', '5', '8', '2', '8', '9', '5', '1', '7', '6', '7', '1', '9', '5', '3', '6', '3', '8', '4', '9', '2', '6', '2', '0', '6', '6', '2', '8', '5', '6', '4', '0', '7', '4', '2', '4', '6', '7', '5', '5', '9', '2', '6', '9', '4', '3', '3', '8', '9', '2', '8', '1', '0', '7', '6', '0', '4', '0', '9', '7', '6', '5', '2', '5', '1', '6', '3', '6', '2', '6', '4', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow028_jensenBoundDenominatorChars : List Char := ['3', '7', '6', '8', '1', '6', '7', '7', '2', '9', '6', '0', '7', '0', '4', '4', '6', '9', '9', '5', '6', '6', '5', '7', '2', '0', '7', '0', '6', '5', '1', '7', '8', '8', '1', '2', '3', '6', '4', '8', '2', '7', '3', '4', '5', '0', '4', '5', '7', '4', '7', '0', '6', '6', '2', '5', '8', '6', '4', '5', '7', '4', '9', '9', '3', '2', '2', '1', '6', '0', '9', '6', '7', '3', '9', '5', '2', '4', '6', '8', '9', '5', '0', '2', '4', '7', '3', '6', '2', '5', '4', '3', '6', '7', '0', '9', '9', '7', '5', '1', '6', '3', '1', '5', '2', '6', '8', '5', '1', '3', '6', '5', '0', '9', '7', '5', '1', '3', '9', '2', '4', '4', '7', '2', '5', '7', '8', '7', '4', '3', '0', '7']
noncomputable def geometryRow028_jensenBoundText : String := String.ofList (geometryRow028_jensenBoundNumeratorChars ++ '/' :: geometryRow028_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_jensenBound_before_field"
  err.flush

theorem geometryRow028_jensenBound_field :
    geometryRowsJson028.getObjVal? "jensen_bound" = .ok (.str geometryRow028_jensenBoundText) := by rfl

theorem geometryRow028_jensenBound_numerator_no_slash :
    geometryRow028_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow028_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow028_jensenBoundNumeratorChars = some (159628330512101026552693737658289517671953638492620662856407424675592694338928107604097652516362649600000000000000000 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow028_jensenBoundDenominatorChars = some (376816772960704469956657207065178812364827345045747066258645749932216096739524689502473625436709975163152685136509751392447257874307 : Int) := by decide +kernel

theorem geometryRow028_jensenBound_denominator_nonzero : (376816772960704469956657207065178812364827345045747066258645749932216096739524689502473625436709975163152685136509751392447257874307 : Int) ≠ 0 := by decide +kernel

theorem geometryRow028_jensenBound_parse :
    parseRational geometryRow028_jensenBoundText = .ok geometryRowsTyped028.jensenBound :=
  original_rational_fraction_of_chars geometryRow028_jensenBoundNumeratorChars geometryRow028_jensenBoundDenominatorChars
    (159628330512101026552693737658289517671953638492620662856407424675592694338928107604097652516362649600000000000000000 : Int) (376816772960704469956657207065178812364827345045747066258645749932216096739524689502473625436709975163152685136509751392447257874307 : Int)
    geometryRow028_jensenBound_numerator_no_slash geometryRow028_jensenBound_numerator_parse
    geometryRow028_jensenBound_denominator_parse geometryRow028_jensenBound_denominator_nonzero

theorem geometryRow028_jensenBound_read :
    rationalField geometryRowsJson028 "jensen_bound" = .ok geometryRowsTyped028.jensenBound :=
  original_rationalField_of_string geometryRowsJson028 "jensen_bound" geometryRow028_jensenBoundText
    geometryRowsTyped028.jensenBound geometryRow028_jensenBound_field geometryRow028_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_factorMaxima_before"
  err.flush

theorem geometryRow028_factorMaxima_read :
    rationalArrayField geometryRowsJson028 "factor_maxima" = .ok geometryRowsTyped028.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_gapWeightedMeans_before"
  err.flush

theorem geometryRow028_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson028 "gap_weighted_means" = .ok geometryRowsTyped028.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow028_floorChars : List Char := ['3', '3', '5', '6', '2', '8', '8', '8', '4', '3', '5', '9', '9', '9']
noncomputable def geometryRow028_floorText : String := String.ofList geometryRow028_floorChars

theorem geometryRow028_floor_text_read :
    geometryRowsJson028.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow028_floorText := by rfl

theorem geometryRow028_floor_chars_parse :
    SourceJson.intChars geometryRow028_floorChars = some (33562888435999 : Int) := by decide +kernel

theorem geometryRow028_floor_parse :
    parseInteger geometryRow028_floorText = .ok geometryRowsTyped028.jensenFloorQ96 := by
  simp only [geometryRow028_floorText, parseInteger, String.toList_ofList, geometryRow028_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_028 :
    decodeGeometryRow geometryRowsJson028 = .ok geometryRowsTyped028 :=
  original_geometryRow_of_fields geometryRowsJson028 geometryRowsTyped028 geometryRow028_floorText
    geometryRow028_simplexId_read geometryRow028_vertexIds_read
    geometryRow028_physicalVolume_read geometryRow028_meanGap_read
    geometryRow028_factorMaxima_read geometryRow028_gapWeightedMeans_read
    geometryRow028_jensenBound_read geometryRow028_floor_text_read geometryRow028_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_028_original_decoder_complete"
  err.flush

theorem geometryRow028_shape :
    geometryRowsTyped028.simplexId = 28 ∧
    geometryRowsTyped028.vertexIds.size = 9 ∧ geometryRowsTyped028.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped028.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped028.factorMaxima.size = 10 ∧ geometryRowsTyped028.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson029 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped029 : GeometryRow :=
  { simplexId := 29,
    vertexIds := #[32, 30, 20, 16, 14, 12, 11, 3, 0],
    physicalVolume := ((1410182531339571077773946279777197284474277 : ℚ) / (3619523649208320000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((31729387 : ℚ) / (21285000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((5256028389849706505581 : ℚ) / (58280866758049320000000 : ℚ)), ((53733242452285334210857 : ℚ) / (582808667580493200000000 : ℚ)), ((135037852703386668575497 : ℚ) / (1165617335160986400000000 : ℚ)), ((103100469109222354086367 : ℚ) / (1165617335160986400000000 : ℚ)), ((11267194480374586610931 : ℚ) / (129513037240109600000000 : ℚ)), ((1590035819446072535669 : ℚ) / (21193042457472480000000 : ℚ)), ((114805758358291230691 : ℚ) / (3027577493924640000000 : ℚ)), ((30490111773601093969 : ℚ) / (847721698298899200000 : ℚ)), ((178101360290062573543 : ℚ) / (5298260614368120000000 : ℚ)), ((2035086057999317393451 : ℚ) / (64756518620054800000000 : ℚ))],
    jensenBound := ((872472313342529646110661309801233259297217725939907079993985858644149565408833362488101361803516280755518357070085704939063613124049847383390397504222622661263383256666663353926837862400000000000000000 : ℚ) / (300923336399276612275847993717479212987571659229872597064318524832465266054110724510660076186742952757149953453806320106392002037182902029223860725058647182790468922806224265754025890664138288293291303006214577587 : ℚ)),
    jensenFloorQ96 := (229707602799475887 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_simplexId_before"
  err.flush

theorem geometryRow029_simplexId_read :
    geometryRowsJson029.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped029.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_vertexIds_before"
  err.flush

theorem geometryRow029_vertexIds_read :
    geometryRowsJson029.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped029.vertexIds := by decide +kernel

noncomputable def geometryRow029_physicalVolumeNumeratorChars : List Char := ['1', '4', '1', '0', '1', '8', '2', '5', '3', '1', '3', '3', '9', '5', '7', '1', '0', '7', '7', '7', '7', '3', '9', '4', '6', '2', '7', '9', '7', '7', '7', '1', '9', '7', '2', '8', '4', '4', '7', '4', '2', '7', '7']
noncomputable def geometryRow029_physicalVolumeDenominatorChars : List Char := ['3', '6', '1', '9', '5', '2', '3', '6', '4', '9', '2', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_physicalVolumeText : String := String.ofList (geometryRow029_physicalVolumeNumeratorChars ++ '/' :: geometryRow029_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_physicalVolume_before_field"
  err.flush

theorem geometryRow029_physicalVolume_field :
    geometryRowsJson029.getObjVal? "physical_volume" = .ok (.str geometryRow029_physicalVolumeText) := by rfl

theorem geometryRow029_physicalVolume_numerator_no_slash :
    geometryRow029_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeNumeratorChars = some (1410182531339571077773946279777197284474277 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow029_physicalVolumeDenominatorChars = some (3619523649208320000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow029_physicalVolume_denominator_nonzero : (3619523649208320000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_physicalVolume_parse :
    parseRational geometryRow029_physicalVolumeText = .ok geometryRowsTyped029.physicalVolume :=
  original_rational_fraction_of_chars geometryRow029_physicalVolumeNumeratorChars geometryRow029_physicalVolumeDenominatorChars
    (1410182531339571077773946279777197284474277 : Int) (3619523649208320000000000000000000000000000000000000000000000000 : Int)
    geometryRow029_physicalVolume_numerator_no_slash geometryRow029_physicalVolume_numerator_parse
    geometryRow029_physicalVolume_denominator_parse geometryRow029_physicalVolume_denominator_nonzero

theorem geometryRow029_physicalVolume_read :
    rationalField geometryRowsJson029 "physical_volume" = .ok geometryRowsTyped029.physicalVolume :=
  original_rationalField_of_string geometryRowsJson029 "physical_volume" geometryRow029_physicalVolumeText
    geometryRowsTyped029.physicalVolume geometryRow029_physicalVolume_field geometryRow029_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_physicalVolume_complete"
  err.flush

noncomputable def geometryRow029_meanGapNumeratorChars : List Char := ['3', '1', '7', '2', '9', '3', '8', '7']
noncomputable def geometryRow029_meanGapDenominatorChars : List Char := ['2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_meanGapText : String := String.ofList (geometryRow029_meanGapNumeratorChars ++ '/' :: geometryRow029_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_meanGap_before_field"
  err.flush

theorem geometryRow029_meanGap_field :
    geometryRowsJson029.getObjVal? "mean_gap" = .ok (.str geometryRow029_meanGapText) := by rfl

theorem geometryRow029_meanGap_numerator_no_slash :
    geometryRow029_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_meanGap_numerator_parse :
    SourceJson.intChars geometryRow029_meanGapNumeratorChars = some (31729387 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_parse :
    SourceJson.intChars geometryRow029_meanGapDenominatorChars = some (21285000000 : Int) := by decide +kernel

theorem geometryRow029_meanGap_denominator_nonzero : (21285000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_meanGap_parse :
    parseRational geometryRow029_meanGapText = .ok geometryRowsTyped029.meanGap :=
  original_rational_fraction_of_chars geometryRow029_meanGapNumeratorChars geometryRow029_meanGapDenominatorChars
    (31729387 : Int) (21285000000 : Int)
    geometryRow029_meanGap_numerator_no_slash geometryRow029_meanGap_numerator_parse
    geometryRow029_meanGap_denominator_parse geometryRow029_meanGap_denominator_nonzero

theorem geometryRow029_meanGap_read :
    rationalField geometryRowsJson029 "mean_gap" = .ok geometryRowsTyped029.meanGap :=
  original_rationalField_of_string geometryRowsJson029 "mean_gap" geometryRow029_meanGapText
    geometryRowsTyped029.meanGap geometryRow029_meanGap_field geometryRow029_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_meanGap_complete"
  err.flush

noncomputable def geometryRow029_jensenBoundNumeratorChars : List Char := ['8', '7', '2', '4', '7', '2', '3', '1', '3', '3', '4', '2', '5', '2', '9', '6', '4', '6', '1', '1', '0', '6', '6', '1', '3', '0', '9', '8', '0', '1', '2', '3', '3', '2', '5', '9', '2', '9', '7', '2', '1', '7', '7', '2', '5', '9', '3', '9', '9', '0', '7', '0', '7', '9', '9', '9', '3', '9', '8', '5', '8', '5', '8', '6', '4', '4', '1', '4', '9', '5', '6', '5', '4', '0', '8', '8', '3', '3', '3', '6', '2', '4', '8', '8', '1', '0', '1', '3', '6', '1', '8', '0', '3', '5', '1', '6', '2', '8', '0', '7', '5', '5', '5', '1', '8', '3', '5', '7', '0', '7', '0', '0', '8', '5', '7', '0', '4', '9', '3', '9', '0', '6', '3', '6', '1', '3', '1', '2', '4', '0', '4', '9', '8', '4', '7', '3', '8', '3', '3', '9', '0', '3', '9', '7', '5', '0', '4', '2', '2', '2', '6', '2', '2', '6', '6', '1', '2', '6', '3', '3', '8', '3', '2', '5', '6', '6', '6', '6', '6', '6', '3', '3', '5', '3', '9', '2', '6', '8', '3', '7', '8', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow029_jensenBoundDenominatorChars : List Char := ['3', '0', '0', '9', '2', '3', '3', '3', '6', '3', '9', '9', '2', '7', '6', '6', '1', '2', '2', '7', '5', '8', '4', '7', '9', '9', '3', '7', '1', '7', '4', '7', '9', '2', '1', '2', '9', '8', '7', '5', '7', '1', '6', '5', '9', '2', '2', '9', '8', '7', '2', '5', '9', '7', '0', '6', '4', '3', '1', '8', '5', '2', '4', '8', '3', '2', '4', '6', '5', '2', '6', '6', '0', '5', '4', '1', '1', '0', '7', '2', '4', '5', '1', '0', '6', '6', '0', '0', '7', '6', '1', '8', '6', '7', '4', '2', '9', '5', '2', '7', '5', '7', '1', '4', '9', '9', '5', '3', '4', '5', '3', '8', '0', '6', '3', '2', '0', '1', '0', '6', '3', '9', '2', '0', '0', '2', '0', '3', '7', '1', '8', '2', '9', '0', '2', '0', '2', '9', '2', '2', '3', '8', '6', '0', '7', '2', '5', '0', '5', '8', '6', '4', '7', '1', '8', '2', '7', '9', '0', '4', '6', '8', '9', '2', '2', '8', '0', '6', '2', '2', '4', '2', '6', '5', '7', '5', '4', '0', '2', '5', '8', '9', '0', '6', '6', '4', '1', '3', '8', '2', '8', '8', '2', '9', '3', '2', '9', '1', '3', '0', '3', '0', '0', '6', '2', '1', '4', '5', '7', '7', '5', '8', '7']
noncomputable def geometryRow029_jensenBoundText : String := String.ofList (geometryRow029_jensenBoundNumeratorChars ++ '/' :: geometryRow029_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_jensenBound_before_field"
  err.flush

theorem geometryRow029_jensenBound_field :
    geometryRowsJson029.getObjVal? "jensen_bound" = .ok (.str geometryRow029_jensenBoundText) := by rfl

theorem geometryRow029_jensenBound_numerator_no_slash :
    geometryRow029_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow029_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow029_jensenBoundNumeratorChars = some (872472313342529646110661309801233259297217725939907079993985858644149565408833362488101361803516280755518357070085704939063613124049847383390397504222622661263383256666663353926837862400000000000000000 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow029_jensenBoundDenominatorChars = some (300923336399276612275847993717479212987571659229872597064318524832465266054110724510660076186742952757149953453806320106392002037182902029223860725058647182790468922806224265754025890664138288293291303006214577587 : Int) := by decide +kernel

theorem geometryRow029_jensenBound_denominator_nonzero : (300923336399276612275847993717479212987571659229872597064318524832465266054110724510660076186742952757149953453806320106392002037182902029223860725058647182790468922806224265754025890664138288293291303006214577587 : Int) ≠ 0 := by decide +kernel

theorem geometryRow029_jensenBound_parse :
    parseRational geometryRow029_jensenBoundText = .ok geometryRowsTyped029.jensenBound :=
  original_rational_fraction_of_chars geometryRow029_jensenBoundNumeratorChars geometryRow029_jensenBoundDenominatorChars
    (872472313342529646110661309801233259297217725939907079993985858644149565408833362488101361803516280755518357070085704939063613124049847383390397504222622661263383256666663353926837862400000000000000000 : Int) (300923336399276612275847993717479212987571659229872597064318524832465266054110724510660076186742952757149953453806320106392002037182902029223860725058647182790468922806224265754025890664138288293291303006214577587 : Int)
    geometryRow029_jensenBound_numerator_no_slash geometryRow029_jensenBound_numerator_parse
    geometryRow029_jensenBound_denominator_parse geometryRow029_jensenBound_denominator_nonzero

theorem geometryRow029_jensenBound_read :
    rationalField geometryRowsJson029 "jensen_bound" = .ok geometryRowsTyped029.jensenBound :=
  original_rationalField_of_string geometryRowsJson029 "jensen_bound" geometryRow029_jensenBoundText
    geometryRowsTyped029.jensenBound geometryRow029_jensenBound_field geometryRow029_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_factorMaxima_before"
  err.flush

theorem geometryRow029_factorMaxima_read :
    rationalArrayField geometryRowsJson029 "factor_maxima" = .ok geometryRowsTyped029.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_gapWeightedMeans_before"
  err.flush

theorem geometryRow029_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson029 "gap_weighted_means" = .ok geometryRowsTyped029.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow029_floorChars : List Char := ['2', '2', '9', '7', '0', '7', '6', '0', '2', '7', '9', '9', '4', '7', '5', '8', '8', '7']
noncomputable def geometryRow029_floorText : String := String.ofList geometryRow029_floorChars

theorem geometryRow029_floor_text_read :
    geometryRowsJson029.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow029_floorText := by rfl

theorem geometryRow029_floor_chars_parse :
    SourceJson.intChars geometryRow029_floorChars = some (229707602799475887 : Int) := by decide +kernel

theorem geometryRow029_floor_parse :
    parseInteger geometryRow029_floorText = .ok geometryRowsTyped029.jensenFloorQ96 := by
  simp only [geometryRow029_floorText, parseInteger, String.toList_ofList, geometryRow029_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_029 :
    decodeGeometryRow geometryRowsJson029 = .ok geometryRowsTyped029 :=
  original_geometryRow_of_fields geometryRowsJson029 geometryRowsTyped029 geometryRow029_floorText
    geometryRow029_simplexId_read geometryRow029_vertexIds_read
    geometryRow029_physicalVolume_read geometryRow029_meanGap_read
    geometryRow029_factorMaxima_read geometryRow029_gapWeightedMeans_read
    geometryRow029_jensenBound_read geometryRow029_floor_text_read geometryRow029_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_029_original_decoder_complete"
  err.flush

theorem geometryRow029_shape :
    geometryRowsTyped029.simplexId = 29 ∧
    geometryRowsTyped029.vertexIds.size = 9 ∧ geometryRowsTyped029.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped029.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped029.factorMaxima.size = 10 ∧ geometryRowsTyped029.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson030 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped030 : GeometryRow :=
  { simplexId := 30,
    vertexIds := #[32, 30, 20, 16, 14, 12, 11, 8, 0],
    physicalVolume := ((780171897786860749280537472866456641223274491 : ℚ) / (454544830365696000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((1525196413799 : ℚ) / (17086608000000 : ℚ)), ((38694110529467 : ℚ) / (427165200000000 : ℚ)), ((297417695938441 : ℚ) / (2562991200000000 : ℚ)), ((225025299956771 : ℚ) / (2562991200000000 : ℚ)), ((221296707223367 : ℚ) / (2562991200000000 : ℚ)), ((3551729596409 : ℚ) / (46599840000000 : ℚ)), ((32050427927 : ℚ) / (832140000000 : ℚ)), ((425954992129 : ℚ) / (11649960000000 : ℚ)), ((803812531073 : ℚ) / (23299920000000 : ℚ)), ((39583962088987 : ℚ) / (1281495600000000 : ℚ))],
    jensenBound := ((1192917085124562697811121655244638456844089098445268436349167288893489092381227751809372824032144650240000000000000000 : ℚ) / (192644752179586401018849976054741227998304764517531088469673398628685410130982727036572540876299013280818197721413346057069489291 : ℚ)),
    jensenFloorQ96 := (490605778859655787 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_simplexId_before"
  err.flush

theorem geometryRow030_simplexId_read :
    geometryRowsJson030.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped030.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_vertexIds_before"
  err.flush

theorem geometryRow030_vertexIds_read :
    geometryRowsJson030.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped030.vertexIds := by decide +kernel

noncomputable def geometryRow030_physicalVolumeNumeratorChars : List Char := ['7', '8', '0', '1', '7', '1', '8', '9', '7', '7', '8', '6', '8', '6', '0', '7', '4', '9', '2', '8', '0', '5', '3', '7', '4', '7', '2', '8', '6', '6', '4', '5', '6', '6', '4', '1', '2', '2', '3', '2', '7', '4', '4', '9', '1']
noncomputable def geometryRow030_physicalVolumeDenominatorChars : List Char := ['4', '5', '4', '5', '4', '4', '8', '3', '0', '3', '6', '5', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_physicalVolumeText : String := String.ofList (geometryRow030_physicalVolumeNumeratorChars ++ '/' :: geometryRow030_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_physicalVolume_before_field"
  err.flush

theorem geometryRow030_physicalVolume_field :
    geometryRowsJson030.getObjVal? "physical_volume" = .ok (.str geometryRow030_physicalVolumeText) := by rfl

theorem geometryRow030_physicalVolume_numerator_no_slash :
    geometryRow030_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeNumeratorChars = some (780171897786860749280537472866456641223274491 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow030_physicalVolumeDenominatorChars = some (454544830365696000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow030_physicalVolume_denominator_nonzero : (454544830365696000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_physicalVolume_parse :
    parseRational geometryRow030_physicalVolumeText = .ok geometryRowsTyped030.physicalVolume :=
  original_rational_fraction_of_chars geometryRow030_physicalVolumeNumeratorChars geometryRow030_physicalVolumeDenominatorChars
    (780171897786860749280537472866456641223274491 : Int) (454544830365696000000000000000000000000000000000000000000000000000 : Int)
    geometryRow030_physicalVolume_numerator_no_slash geometryRow030_physicalVolume_numerator_parse
    geometryRow030_physicalVolume_denominator_parse geometryRow030_physicalVolume_denominator_nonzero

theorem geometryRow030_physicalVolume_read :
    rationalField geometryRowsJson030 "physical_volume" = .ok geometryRowsTyped030.physicalVolume :=
  original_rationalField_of_string geometryRowsJson030 "physical_volume" geometryRow030_physicalVolumeText
    geometryRowsTyped030.physicalVolume geometryRow030_physicalVolume_field geometryRow030_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_physicalVolume_complete"
  err.flush

noncomputable def geometryRow030_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow030_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_meanGapText : String := String.ofList (geometryRow030_meanGapNumeratorChars ++ '/' :: geometryRow030_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_meanGap_before_field"
  err.flush

theorem geometryRow030_meanGap_field :
    geometryRowsJson030.getObjVal? "mean_gap" = .ok (.str geometryRow030_meanGapText) := by rfl

theorem geometryRow030_meanGap_numerator_no_slash :
    geometryRow030_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_meanGap_numerator_parse :
    SourceJson.intChars geometryRow030_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_parse :
    SourceJson.intChars geometryRow030_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow030_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_meanGap_parse :
    parseRational geometryRow030_meanGapText = .ok geometryRowsTyped030.meanGap :=
  original_rational_fraction_of_chars geometryRow030_meanGapNumeratorChars geometryRow030_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow030_meanGap_numerator_no_slash geometryRow030_meanGap_numerator_parse
    geometryRow030_meanGap_denominator_parse geometryRow030_meanGap_denominator_nonzero

theorem geometryRow030_meanGap_read :
    rationalField geometryRowsJson030 "mean_gap" = .ok geometryRowsTyped030.meanGap :=
  original_rationalField_of_string geometryRowsJson030 "mean_gap" geometryRow030_meanGapText
    geometryRowsTyped030.meanGap geometryRow030_meanGap_field geometryRow030_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_meanGap_complete"
  err.flush

noncomputable def geometryRow030_jensenBoundNumeratorChars : List Char := ['1', '1', '9', '2', '9', '1', '7', '0', '8', '5', '1', '2', '4', '5', '6', '2', '6', '9', '7', '8', '1', '1', '1', '2', '1', '6', '5', '5', '2', '4', '4', '6', '3', '8', '4', '5', '6', '8', '4', '4', '0', '8', '9', '0', '9', '8', '4', '4', '5', '2', '6', '8', '4', '3', '6', '3', '4', '9', '1', '6', '7', '2', '8', '8', '8', '9', '3', '4', '8', '9', '0', '9', '2', '3', '8', '1', '2', '2', '7', '7', '5', '1', '8', '0', '9', '3', '7', '2', '8', '2', '4', '0', '3', '2', '1', '4', '4', '6', '5', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow030_jensenBoundDenominatorChars : List Char := ['1', '9', '2', '6', '4', '4', '7', '5', '2', '1', '7', '9', '5', '8', '6', '4', '0', '1', '0', '1', '8', '8', '4', '9', '9', '7', '6', '0', '5', '4', '7', '4', '1', '2', '2', '7', '9', '9', '8', '3', '0', '4', '7', '6', '4', '5', '1', '7', '5', '3', '1', '0', '8', '8', '4', '6', '9', '6', '7', '3', '3', '9', '8', '6', '2', '8', '6', '8', '5', '4', '1', '0', '1', '3', '0', '9', '8', '2', '7', '2', '7', '0', '3', '6', '5', '7', '2', '5', '4', '0', '8', '7', '6', '2', '9', '9', '0', '1', '3', '2', '8', '0', '8', '1', '8', '1', '9', '7', '7', '2', '1', '4', '1', '3', '3', '4', '6', '0', '5', '7', '0', '6', '9', '4', '8', '9', '2', '9', '1']
noncomputable def geometryRow030_jensenBoundText : String := String.ofList (geometryRow030_jensenBoundNumeratorChars ++ '/' :: geometryRow030_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_jensenBound_before_field"
  err.flush

theorem geometryRow030_jensenBound_field :
    geometryRowsJson030.getObjVal? "jensen_bound" = .ok (.str geometryRow030_jensenBoundText) := by rfl

theorem geometryRow030_jensenBound_numerator_no_slash :
    geometryRow030_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow030_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow030_jensenBoundNumeratorChars = some (1192917085124562697811121655244638456844089098445268436349167288893489092381227751809372824032144650240000000000000000 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow030_jensenBoundDenominatorChars = some (192644752179586401018849976054741227998304764517531088469673398628685410130982727036572540876299013280818197721413346057069489291 : Int) := by decide +kernel

theorem geometryRow030_jensenBound_denominator_nonzero : (192644752179586401018849976054741227998304764517531088469673398628685410130982727036572540876299013280818197721413346057069489291 : Int) ≠ 0 := by decide +kernel

theorem geometryRow030_jensenBound_parse :
    parseRational geometryRow030_jensenBoundText = .ok geometryRowsTyped030.jensenBound :=
  original_rational_fraction_of_chars geometryRow030_jensenBoundNumeratorChars geometryRow030_jensenBoundDenominatorChars
    (1192917085124562697811121655244638456844089098445268436349167288893489092381227751809372824032144650240000000000000000 : Int) (192644752179586401018849976054741227998304764517531088469673398628685410130982727036572540876299013280818197721413346057069489291 : Int)
    geometryRow030_jensenBound_numerator_no_slash geometryRow030_jensenBound_numerator_parse
    geometryRow030_jensenBound_denominator_parse geometryRow030_jensenBound_denominator_nonzero

theorem geometryRow030_jensenBound_read :
    rationalField geometryRowsJson030 "jensen_bound" = .ok geometryRowsTyped030.jensenBound :=
  original_rationalField_of_string geometryRowsJson030 "jensen_bound" geometryRow030_jensenBoundText
    geometryRowsTyped030.jensenBound geometryRow030_jensenBound_field geometryRow030_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_factorMaxima_before"
  err.flush

theorem geometryRow030_factorMaxima_read :
    rationalArrayField geometryRowsJson030 "factor_maxima" = .ok geometryRowsTyped030.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_gapWeightedMeans_before"
  err.flush

theorem geometryRow030_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson030 "gap_weighted_means" = .ok geometryRowsTyped030.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow030_floorChars : List Char := ['4', '9', '0', '6', '0', '5', '7', '7', '8', '8', '5', '9', '6', '5', '5', '7', '8', '7']
noncomputable def geometryRow030_floorText : String := String.ofList geometryRow030_floorChars

theorem geometryRow030_floor_text_read :
    geometryRowsJson030.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow030_floorText := by rfl

theorem geometryRow030_floor_chars_parse :
    SourceJson.intChars geometryRow030_floorChars = some (490605778859655787 : Int) := by decide +kernel

theorem geometryRow030_floor_parse :
    parseInteger geometryRow030_floorText = .ok geometryRowsTyped030.jensenFloorQ96 := by
  simp only [geometryRow030_floorText, parseInteger, String.toList_ofList, geometryRow030_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_030 :
    decodeGeometryRow geometryRowsJson030 = .ok geometryRowsTyped030 :=
  original_geometryRow_of_fields geometryRowsJson030 geometryRowsTyped030 geometryRow030_floorText
    geometryRow030_simplexId_read geometryRow030_vertexIds_read
    geometryRow030_physicalVolume_read geometryRow030_meanGap_read
    geometryRow030_factorMaxima_read geometryRow030_gapWeightedMeans_read
    geometryRow030_jensenBound_read geometryRow030_floor_text_read geometryRow030_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_030_original_decoder_complete"
  err.flush

theorem geometryRow030_shape :
    geometryRowsTyped030.simplexId = 30 ∧
    geometryRowsTyped030.vertexIds.size = 9 ∧ geometryRowsTyped030.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped030.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped030.factorMaxima.size = 10 ∧ geometryRowsTyped030.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson031 : SourceJson :=
  (SimplicesBlock003.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped031 : GeometryRow :=
  { simplexId := 31,
    vertexIds := #[32, 30, 20, 16, 14, 12, 11, 7, 3],
    physicalVolume := ((27023477728327228451709259594397978955043819 : ℚ) / (96520630645555200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((49290167 : ℚ) / (34056000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((82351880852065750223189 : ℚ) / (905366893917301200000000 : ℚ)), ((84122114323840409078279 : ℚ) / (905366893917301200000000 : ℚ)), ((210061051187917951862807 : ℚ) / (1810733787834602400000000 : ℚ)), ((159806850276778714893701 : ℚ) / (1810733787834602400000000 : ℚ)), ((52390875957182661136331 : ℚ) / (603577929278200800000000 : ℚ)), ((135774439445850184885513 : ℚ) / (1810733787834602400000000 : ℚ)), ((2450854199031032091773 : ℚ) / (64669063851235800000000 : ℚ)), ((8135970986642328645073 : ℚ) / (226341723479325300000000 : ℚ)), ((29857733508068931776137 : ℚ) / (905366893917301200000000 : ℚ)), ((9556459377635590265711 : ℚ) / (301788964639100400000000 : ℚ))],
    jensenBound := ((2720102291209912874838495245234048415039587032952713747289464449946177083655629397745984379827045478398259053434512203833754175970898498669016583381919572191354280176578280216428799143234298000000000000000000000000 : ℚ) / (1344562483934130557394477050754618883111160312971379472780125290383588870860603619119850302325609356759622049761295923707691017625323885436196962782057082081437407054633266319466470210215344327659351558786736267612790859147679 : ℚ)),
    jensenFloorQ96 := (160281659616764541 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_simplexId_before"
  err.flush

theorem geometryRow031_simplexId_read :
    geometryRowsJson031.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped031.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_vertexIds_before"
  err.flush

theorem geometryRow031_vertexIds_read :
    geometryRowsJson031.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped031.vertexIds := by decide +kernel

noncomputable def geometryRow031_physicalVolumeNumeratorChars : List Char := ['2', '7', '0', '2', '3', '4', '7', '7', '7', '2', '8', '3', '2', '7', '2', '2', '8', '4', '5', '1', '7', '0', '9', '2', '5', '9', '5', '9', '4', '3', '9', '7', '9', '7', '8', '9', '5', '5', '0', '4', '3', '8', '1', '9']
noncomputable def geometryRow031_physicalVolumeDenominatorChars : List Char := ['9', '6', '5', '2', '0', '6', '3', '0', '6', '4', '5', '5', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_physicalVolumeText : String := String.ofList (geometryRow031_physicalVolumeNumeratorChars ++ '/' :: geometryRow031_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_physicalVolume_before_field"
  err.flush

theorem geometryRow031_physicalVolume_field :
    geometryRowsJson031.getObjVal? "physical_volume" = .ok (.str geometryRow031_physicalVolumeText) := by rfl

theorem geometryRow031_physicalVolume_numerator_no_slash :
    geometryRow031_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeNumeratorChars = some (27023477728327228451709259594397978955043819 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow031_physicalVolumeDenominatorChars = some (96520630645555200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_physicalVolume_denominator_nonzero : (96520630645555200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_physicalVolume_parse :
    parseRational geometryRow031_physicalVolumeText = .ok geometryRowsTyped031.physicalVolume :=
  original_rational_fraction_of_chars geometryRow031_physicalVolumeNumeratorChars geometryRow031_physicalVolumeDenominatorChars
    (27023477728327228451709259594397978955043819 : Int) (96520630645555200000000000000000000000000000000000000000000000000 : Int)
    geometryRow031_physicalVolume_numerator_no_slash geometryRow031_physicalVolume_numerator_parse
    geometryRow031_physicalVolume_denominator_parse geometryRow031_physicalVolume_denominator_nonzero

theorem geometryRow031_physicalVolume_read :
    rationalField geometryRowsJson031 "physical_volume" = .ok geometryRowsTyped031.physicalVolume :=
  original_rationalField_of_string geometryRowsJson031 "physical_volume" geometryRow031_physicalVolumeText
    geometryRowsTyped031.physicalVolume geometryRow031_physicalVolume_field geometryRow031_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_physicalVolume_complete"
  err.flush

noncomputable def geometryRow031_meanGapNumeratorChars : List Char := ['4', '9', '2', '9', '0', '1', '6', '7']
noncomputable def geometryRow031_meanGapDenominatorChars : List Char := ['3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_meanGapText : String := String.ofList (geometryRow031_meanGapNumeratorChars ++ '/' :: geometryRow031_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_meanGap_before_field"
  err.flush

theorem geometryRow031_meanGap_field :
    geometryRowsJson031.getObjVal? "mean_gap" = .ok (.str geometryRow031_meanGapText) := by rfl

theorem geometryRow031_meanGap_numerator_no_slash :
    geometryRow031_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_meanGap_numerator_parse :
    SourceJson.intChars geometryRow031_meanGapNumeratorChars = some (49290167 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_parse :
    SourceJson.intChars geometryRow031_meanGapDenominatorChars = some (34056000000 : Int) := by decide +kernel

theorem geometryRow031_meanGap_denominator_nonzero : (34056000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_meanGap_parse :
    parseRational geometryRow031_meanGapText = .ok geometryRowsTyped031.meanGap :=
  original_rational_fraction_of_chars geometryRow031_meanGapNumeratorChars geometryRow031_meanGapDenominatorChars
    (49290167 : Int) (34056000000 : Int)
    geometryRow031_meanGap_numerator_no_slash geometryRow031_meanGap_numerator_parse
    geometryRow031_meanGap_denominator_parse geometryRow031_meanGap_denominator_nonzero

theorem geometryRow031_meanGap_read :
    rationalField geometryRowsJson031 "mean_gap" = .ok geometryRowsTyped031.meanGap :=
  original_rationalField_of_string geometryRowsJson031 "mean_gap" geometryRow031_meanGapText
    geometryRowsTyped031.meanGap geometryRow031_meanGap_field geometryRow031_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_meanGap_complete"
  err.flush

noncomputable def geometryRow031_jensenBoundNumeratorChars : List Char := ['2', '7', '2', '0', '1', '0', '2', '2', '9', '1', '2', '0', '9', '9', '1', '2', '8', '7', '4', '8', '3', '8', '4', '9', '5', '2', '4', '5', '2', '3', '4', '0', '4', '8', '4', '1', '5', '0', '3', '9', '5', '8', '7', '0', '3', '2', '9', '5', '2', '7', '1', '3', '7', '4', '7', '2', '8', '9', '4', '6', '4', '4', '4', '9', '9', '4', '6', '1', '7', '7', '0', '8', '3', '6', '5', '5', '6', '2', '9', '3', '9', '7', '7', '4', '5', '9', '8', '4', '3', '7', '9', '8', '2', '7', '0', '4', '5', '4', '7', '8', '3', '9', '8', '2', '5', '9', '0', '5', '3', '4', '3', '4', '5', '1', '2', '2', '0', '3', '8', '3', '3', '7', '5', '4', '1', '7', '5', '9', '7', '0', '8', '9', '8', '4', '9', '8', '6', '6', '9', '0', '1', '6', '5', '8', '3', '3', '8', '1', '9', '1', '9', '5', '7', '2', '1', '9', '1', '3', '5', '4', '2', '8', '0', '1', '7', '6', '5', '7', '8', '2', '8', '0', '2', '1', '6', '4', '2', '8', '7', '9', '9', '1', '4', '3', '2', '3', '4', '2', '9', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow031_jensenBoundDenominatorChars : List Char := ['1', '3', '4', '4', '5', '6', '2', '4', '8', '3', '9', '3', '4', '1', '3', '0', '5', '5', '7', '3', '9', '4', '4', '7', '7', '0', '5', '0', '7', '5', '4', '6', '1', '8', '8', '8', '3', '1', '1', '1', '1', '6', '0', '3', '1', '2', '9', '7', '1', '3', '7', '9', '4', '7', '2', '7', '8', '0', '1', '2', '5', '2', '9', '0', '3', '8', '3', '5', '8', '8', '8', '7', '0', '8', '6', '0', '6', '0', '3', '6', '1', '9', '1', '1', '9', '8', '5', '0', '3', '0', '2', '3', '2', '5', '6', '0', '9', '3', '5', '6', '7', '5', '9', '6', '2', '2', '0', '4', '9', '7', '6', '1', '2', '9', '5', '9', '2', '3', '7', '0', '7', '6', '9', '1', '0', '1', '7', '6', '2', '5', '3', '2', '3', '8', '8', '5', '4', '3', '6', '1', '9', '6', '9', '6', '2', '7', '8', '2', '0', '5', '7', '0', '8', '2', '0', '8', '1', '4', '3', '7', '4', '0', '7', '0', '5', '4', '6', '3', '3', '2', '6', '6', '3', '1', '9', '4', '6', '6', '4', '7', '0', '2', '1', '0', '2', '1', '5', '3', '4', '4', '3', '2', '7', '6', '5', '9', '3', '5', '1', '5', '5', '8', '7', '8', '6', '7', '3', '6', '2', '6', '7', '6', '1', '2', '7', '9', '0', '8', '5', '9', '1', '4', '7', '6', '7', '9']
noncomputable def geometryRow031_jensenBoundText : String := String.ofList (geometryRow031_jensenBoundNumeratorChars ++ '/' :: geometryRow031_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_jensenBound_before_field"
  err.flush

theorem geometryRow031_jensenBound_field :
    geometryRowsJson031.getObjVal? "jensen_bound" = .ok (.str geometryRow031_jensenBoundText) := by rfl

theorem geometryRow031_jensenBound_numerator_no_slash :
    geometryRow031_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow031_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow031_jensenBoundNumeratorChars = some (2720102291209912874838495245234048415039587032952713747289464449946177083655629397745984379827045478398259053434512203833754175970898498669016583381919572191354280176578280216428799143234298000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow031_jensenBoundDenominatorChars = some (1344562483934130557394477050754618883111160312971379472780125290383588870860603619119850302325609356759622049761295923707691017625323885436196962782057082081437407054633266319466470210215344327659351558786736267612790859147679 : Int) := by decide +kernel

theorem geometryRow031_jensenBound_denominator_nonzero : (1344562483934130557394477050754618883111160312971379472780125290383588870860603619119850302325609356759622049761295923707691017625323885436196962782057082081437407054633266319466470210215344327659351558786736267612790859147679 : Int) ≠ 0 := by decide +kernel

theorem geometryRow031_jensenBound_parse :
    parseRational geometryRow031_jensenBoundText = .ok geometryRowsTyped031.jensenBound :=
  original_rational_fraction_of_chars geometryRow031_jensenBoundNumeratorChars geometryRow031_jensenBoundDenominatorChars
    (2720102291209912874838495245234048415039587032952713747289464449946177083655629397745984379827045478398259053434512203833754175970898498669016583381919572191354280176578280216428799143234298000000000000000000000000 : Int) (1344562483934130557394477050754618883111160312971379472780125290383588870860603619119850302325609356759622049761295923707691017625323885436196962782057082081437407054633266319466470210215344327659351558786736267612790859147679 : Int)
    geometryRow031_jensenBound_numerator_no_slash geometryRow031_jensenBound_numerator_parse
    geometryRow031_jensenBound_denominator_parse geometryRow031_jensenBound_denominator_nonzero

theorem geometryRow031_jensenBound_read :
    rationalField geometryRowsJson031 "jensen_bound" = .ok geometryRowsTyped031.jensenBound :=
  original_rationalField_of_string geometryRowsJson031 "jensen_bound" geometryRow031_jensenBoundText
    geometryRowsTyped031.jensenBound geometryRow031_jensenBound_field geometryRow031_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_factorMaxima_before"
  err.flush

theorem geometryRow031_factorMaxima_read :
    rationalArrayField geometryRowsJson031 "factor_maxima" = .ok geometryRowsTyped031.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_gapWeightedMeans_before"
  err.flush

theorem geometryRow031_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson031 "gap_weighted_means" = .ok geometryRowsTyped031.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow031_floorChars : List Char := ['1', '6', '0', '2', '8', '1', '6', '5', '9', '6', '1', '6', '7', '6', '4', '5', '4', '1']
noncomputable def geometryRow031_floorText : String := String.ofList geometryRow031_floorChars

theorem geometryRow031_floor_text_read :
    geometryRowsJson031.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow031_floorText := by rfl

theorem geometryRow031_floor_chars_parse :
    SourceJson.intChars geometryRow031_floorChars = some (160281659616764541 : Int) := by decide +kernel

theorem geometryRow031_floor_parse :
    parseInteger geometryRow031_floorText = .ok geometryRowsTyped031.jensenFloorQ96 := by
  simp only [geometryRow031_floorText, parseInteger, String.toList_ofList, geometryRow031_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_031 :
    decodeGeometryRow geometryRowsJson031 = .ok geometryRowsTyped031 :=
  original_geometryRow_of_fields geometryRowsJson031 geometryRowsTyped031 geometryRow031_floorText
    geometryRow031_simplexId_read geometryRow031_vertexIds_read
    geometryRow031_physicalVolume_read geometryRow031_meanGap_read
    geometryRow031_factorMaxima_read geometryRow031_gapWeightedMeans_read
    geometryRow031_jensenBound_read geometryRow031_floor_text_read geometryRow031_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_031_original_decoder_complete"
  err.flush

theorem geometryRow031_shape :
    geometryRowsTyped031.simplexId = 31 ∧
    geometryRowsTyped031.vertexIds.size = 9 ∧ geometryRowsTyped031.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped031.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped031.factorMaxima.size = 10 ∧ geometryRowsTyped031.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock003 : List SourceJson := [geometryRowsJson024, geometryRowsJson025, geometryRowsJson026, geometryRowsJson027, geometryRowsJson028, geometryRowsJson029, geometryRowsJson030, geometryRowsJson031]
noncomputable def geometryRowsTypedBlock003 : List GeometryRow := [geometryRowsTyped024, geometryRowsTyped025, geometryRowsTyped026, geometryRowsTyped027, geometryRowsTyped028, geometryRowsTyped029, geometryRowsTyped030, geometryRowsTyped031]

theorem geometry_Rows_block_003_push_eq (acc : List SourceJson) :
    SimplicesBlock003.blockPush acc = [geometryRowsJson031, geometryRowsJson030, geometryRowsJson029, geometryRowsJson028, geometryRowsJson027, geometryRowsJson026, geometryRowsJson025, geometryRowsJson024] ++ acc := by rfl

theorem geometry_Rows_block_003_reverse (acc : List SourceJson) :
    (SimplicesBlock003.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock003 := by
  rw [geometry_Rows_block_003_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_003 :
    geometryRowsJsonBlock003.mapM decodeGeometryRow = .ok geometryRowsTypedBlock003 := by
  simp only [geometryRowsJsonBlock003, geometryRowsTypedBlock003, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_024, decode_geometry_Rows_025, decode_geometry_Rows_026, decode_geometry_Rows_027, decode_geometry_Rows_028, decode_geometry_Rows_029, decode_geometry_Rows_030, decode_geometry_Rows_031]
  rfl

theorem geometry_Rows_block_003_length : geometryRowsTypedBlock003.length = 8 := by rfl

#print axioms geometryRow024_simplexId_read
#print axioms geometryRow024_vertexIds_read
#print axioms geometryRow024_physicalVolume_field
#print axioms geometryRow024_physicalVolume_numerator_no_slash
#print axioms geometryRow024_physicalVolume_numerator_parse
#print axioms geometryRow024_physicalVolume_denominator_parse
#print axioms geometryRow024_physicalVolume_denominator_nonzero
#print axioms geometryRow024_physicalVolume_parse
#print axioms geometryRow024_physicalVolume_read
#print axioms geometryRow024_meanGap_field
#print axioms geometryRow024_meanGap_numerator_no_slash
#print axioms geometryRow024_meanGap_numerator_parse
#print axioms geometryRow024_meanGap_denominator_parse
#print axioms geometryRow024_meanGap_denominator_nonzero
#print axioms geometryRow024_meanGap_parse
#print axioms geometryRow024_meanGap_read
#print axioms geometryRow024_jensenBound_field
#print axioms geometryRow024_jensenBound_numerator_no_slash
#print axioms geometryRow024_jensenBound_numerator_parse
#print axioms geometryRow024_jensenBound_denominator_parse
#print axioms geometryRow024_jensenBound_denominator_nonzero
#print axioms geometryRow024_jensenBound_parse
#print axioms geometryRow024_jensenBound_read
#print axioms geometryRow024_factorMaxima_read
#print axioms geometryRow024_gapWeightedMeans_read
#print axioms geometryRow024_floor_text_read
#print axioms geometryRow024_floor_chars_parse
#print axioms geometryRow024_floor_parse
#print axioms decode_geometry_Rows_024
#print axioms geometryRow024_shape
#print axioms geometryRow025_simplexId_read
#print axioms geometryRow025_vertexIds_read
#print axioms geometryRow025_physicalVolume_field
#print axioms geometryRow025_physicalVolume_numerator_no_slash
#print axioms geometryRow025_physicalVolume_numerator_parse
#print axioms geometryRow025_physicalVolume_denominator_parse
#print axioms geometryRow025_physicalVolume_denominator_nonzero
#print axioms geometryRow025_physicalVolume_parse
#print axioms geometryRow025_physicalVolume_read
#print axioms geometryRow025_meanGap_field
#print axioms geometryRow025_meanGap_numerator_no_slash
#print axioms geometryRow025_meanGap_numerator_parse
#print axioms geometryRow025_meanGap_denominator_parse
#print axioms geometryRow025_meanGap_denominator_nonzero
#print axioms geometryRow025_meanGap_parse
#print axioms geometryRow025_meanGap_read
#print axioms geometryRow025_jensenBound_field
#print axioms geometryRow025_jensenBound_numerator_no_slash
#print axioms geometryRow025_jensenBound_numerator_parse
#print axioms geometryRow025_jensenBound_denominator_parse
#print axioms geometryRow025_jensenBound_denominator_nonzero
#print axioms geometryRow025_jensenBound_parse
#print axioms geometryRow025_jensenBound_read
#print axioms geometryRow025_factorMaxima_read
#print axioms geometryRow025_gapWeightedMeans_read
#print axioms geometryRow025_floor_text_read
#print axioms geometryRow025_floor_chars_parse
#print axioms geometryRow025_floor_parse
#print axioms decode_geometry_Rows_025
#print axioms geometryRow025_shape
#print axioms geometryRow026_simplexId_read
#print axioms geometryRow026_vertexIds_read
#print axioms geometryRow026_physicalVolume_field
#print axioms geometryRow026_physicalVolume_numerator_no_slash
#print axioms geometryRow026_physicalVolume_numerator_parse
#print axioms geometryRow026_physicalVolume_denominator_parse
#print axioms geometryRow026_physicalVolume_denominator_nonzero
#print axioms geometryRow026_physicalVolume_parse
#print axioms geometryRow026_physicalVolume_read
#print axioms geometryRow026_meanGap_field
#print axioms geometryRow026_meanGap_numerator_no_slash
#print axioms geometryRow026_meanGap_numerator_parse
#print axioms geometryRow026_meanGap_denominator_parse
#print axioms geometryRow026_meanGap_denominator_nonzero
#print axioms geometryRow026_meanGap_parse
#print axioms geometryRow026_meanGap_read
#print axioms geometryRow026_jensenBound_field
#print axioms geometryRow026_jensenBound_numerator_no_slash
#print axioms geometryRow026_jensenBound_numerator_parse
#print axioms geometryRow026_jensenBound_denominator_parse
#print axioms geometryRow026_jensenBound_denominator_nonzero
#print axioms geometryRow026_jensenBound_parse
#print axioms geometryRow026_jensenBound_read
#print axioms geometryRow026_factorMaxima_read
#print axioms geometryRow026_gapWeightedMeans_read
#print axioms geometryRow026_floor_text_read
#print axioms geometryRow026_floor_chars_parse
#print axioms geometryRow026_floor_parse
#print axioms decode_geometry_Rows_026
#print axioms geometryRow026_shape
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
#print axioms geometryRow027_shape
#print axioms geometryRow028_simplexId_read
#print axioms geometryRow028_vertexIds_read
#print axioms geometryRow028_physicalVolume_field
#print axioms geometryRow028_physicalVolume_numerator_no_slash
#print axioms geometryRow028_physicalVolume_numerator_parse
#print axioms geometryRow028_physicalVolume_denominator_parse
#print axioms geometryRow028_physicalVolume_denominator_nonzero
#print axioms geometryRow028_physicalVolume_parse
#print axioms geometryRow028_physicalVolume_read
#print axioms geometryRow028_meanGap_field
#print axioms geometryRow028_meanGap_numerator_no_slash
#print axioms geometryRow028_meanGap_numerator_parse
#print axioms geometryRow028_meanGap_denominator_parse
#print axioms geometryRow028_meanGap_denominator_nonzero
#print axioms geometryRow028_meanGap_parse
#print axioms geometryRow028_meanGap_read
#print axioms geometryRow028_jensenBound_field
#print axioms geometryRow028_jensenBound_numerator_no_slash
#print axioms geometryRow028_jensenBound_numerator_parse
#print axioms geometryRow028_jensenBound_denominator_parse
#print axioms geometryRow028_jensenBound_denominator_nonzero
#print axioms geometryRow028_jensenBound_parse
#print axioms geometryRow028_jensenBound_read
#print axioms geometryRow028_factorMaxima_read
#print axioms geometryRow028_gapWeightedMeans_read
#print axioms geometryRow028_floor_text_read
#print axioms geometryRow028_floor_chars_parse
#print axioms geometryRow028_floor_parse
#print axioms decode_geometry_Rows_028
#print axioms geometryRow028_shape
#print axioms geometryRow029_simplexId_read
#print axioms geometryRow029_vertexIds_read
#print axioms geometryRow029_physicalVolume_field
#print axioms geometryRow029_physicalVolume_numerator_no_slash
#print axioms geometryRow029_physicalVolume_numerator_parse
#print axioms geometryRow029_physicalVolume_denominator_parse
#print axioms geometryRow029_physicalVolume_denominator_nonzero
#print axioms geometryRow029_physicalVolume_parse
#print axioms geometryRow029_physicalVolume_read
#print axioms geometryRow029_meanGap_field
#print axioms geometryRow029_meanGap_numerator_no_slash
#print axioms geometryRow029_meanGap_numerator_parse
#print axioms geometryRow029_meanGap_denominator_parse
#print axioms geometryRow029_meanGap_denominator_nonzero
#print axioms geometryRow029_meanGap_parse
#print axioms geometryRow029_meanGap_read
#print axioms geometryRow029_jensenBound_field
#print axioms geometryRow029_jensenBound_numerator_no_slash
#print axioms geometryRow029_jensenBound_numerator_parse
#print axioms geometryRow029_jensenBound_denominator_parse
#print axioms geometryRow029_jensenBound_denominator_nonzero
#print axioms geometryRow029_jensenBound_parse
#print axioms geometryRow029_jensenBound_read
#print axioms geometryRow029_factorMaxima_read
#print axioms geometryRow029_gapWeightedMeans_read
#print axioms geometryRow029_floor_text_read
#print axioms geometryRow029_floor_chars_parse
#print axioms geometryRow029_floor_parse
#print axioms decode_geometry_Rows_029
#print axioms geometryRow029_shape
#print axioms geometryRow030_simplexId_read
#print axioms geometryRow030_vertexIds_read
#print axioms geometryRow030_physicalVolume_field
#print axioms geometryRow030_physicalVolume_numerator_no_slash
#print axioms geometryRow030_physicalVolume_numerator_parse
#print axioms geometryRow030_physicalVolume_denominator_parse
#print axioms geometryRow030_physicalVolume_denominator_nonzero
#print axioms geometryRow030_physicalVolume_parse
#print axioms geometryRow030_physicalVolume_read
#print axioms geometryRow030_meanGap_field
#print axioms geometryRow030_meanGap_numerator_no_slash
#print axioms geometryRow030_meanGap_numerator_parse
#print axioms geometryRow030_meanGap_denominator_parse
#print axioms geometryRow030_meanGap_denominator_nonzero
#print axioms geometryRow030_meanGap_parse
#print axioms geometryRow030_meanGap_read
#print axioms geometryRow030_jensenBound_field
#print axioms geometryRow030_jensenBound_numerator_no_slash
#print axioms geometryRow030_jensenBound_numerator_parse
#print axioms geometryRow030_jensenBound_denominator_parse
#print axioms geometryRow030_jensenBound_denominator_nonzero
#print axioms geometryRow030_jensenBound_parse
#print axioms geometryRow030_jensenBound_read
#print axioms geometryRow030_factorMaxima_read
#print axioms geometryRow030_gapWeightedMeans_read
#print axioms geometryRow030_floor_text_read
#print axioms geometryRow030_floor_chars_parse
#print axioms geometryRow030_floor_parse
#print axioms decode_geometry_Rows_030
#print axioms geometryRow030_shape
#print axioms geometryRow031_simplexId_read
#print axioms geometryRow031_vertexIds_read
#print axioms geometryRow031_physicalVolume_field
#print axioms geometryRow031_physicalVolume_numerator_no_slash
#print axioms geometryRow031_physicalVolume_numerator_parse
#print axioms geometryRow031_physicalVolume_denominator_parse
#print axioms geometryRow031_physicalVolume_denominator_nonzero
#print axioms geometryRow031_physicalVolume_parse
#print axioms geometryRow031_physicalVolume_read
#print axioms geometryRow031_meanGap_field
#print axioms geometryRow031_meanGap_numerator_no_slash
#print axioms geometryRow031_meanGap_numerator_parse
#print axioms geometryRow031_meanGap_denominator_parse
#print axioms geometryRow031_meanGap_denominator_nonzero
#print axioms geometryRow031_meanGap_parse
#print axioms geometryRow031_meanGap_read
#print axioms geometryRow031_jensenBound_field
#print axioms geometryRow031_jensenBound_numerator_no_slash
#print axioms geometryRow031_jensenBound_numerator_parse
#print axioms geometryRow031_jensenBound_denominator_parse
#print axioms geometryRow031_jensenBound_denominator_nonzero
#print axioms geometryRow031_jensenBound_parse
#print axioms geometryRow031_jensenBound_read
#print axioms geometryRow031_factorMaxima_read
#print axioms geometryRow031_gapWeightedMeans_read
#print axioms geometryRow031_floor_text_read
#print axioms geometryRow031_floor_chars_parse
#print axioms geometryRow031_floor_parse
#print axioms decode_geometry_Rows_031
#print axioms geometryRow031_shape
#print axioms geometry_Rows_block_003_push_eq
#print axioms geometry_Rows_block_003_reverse
#print axioms decode_geometry_Rows_block_003
#print axioms geometry_Rows_block_003_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
