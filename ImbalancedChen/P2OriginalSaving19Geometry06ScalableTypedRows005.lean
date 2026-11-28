import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock005

/-! Local typed certificates for original cell 06, rows 40 through 47.
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

noncomputable def geometryRowsJson040 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped040 : GeometryRow :=
  { simplexId := 40,
    vertexIds := #[32, 30, 28, 16, 15, 13, 10, 8, 0],
    physicalVolume := ((2121243312006159983879362188871792835219 : ℚ) / (23039953097011200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((71455432771 : ℚ) / (796950000000 : ℚ)), ((145016090111 : ℚ) / (1593900000000 : ℚ)), ((19484287283 : ℚ) / (166320000000 : ℚ)), ((1697910953797 : ℚ) / (19126800000000 : ℚ)), ((1687517173477 : ℚ) / (19126800000000 : ℚ)), ((130427464169 : ℚ) / (1738800000000 : ℚ)), ((1002415903 : ℚ) / (27168750000 : ℚ)), ((4339918823 : ℚ) / (124200000000 : ℚ)), ((4272401903 : ℚ) / (124200000000 : ℚ)), ((148336431751 : ℚ) / (4781700000000 : ℚ))],
    jensenBound := ((945168146761585757748255065421744498468588445249122711192902231688941250000000000000000000 : ℚ) / (2701636334100754722979016229191919329464980911091268991115937346289222085686576537930340013786683583218723 : ℚ)),
    jensenFloorQ96 := (27717992458766 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_simplexId_before"
  err.flush

theorem geometryRow040_simplexId_read :
    geometryRowsJson040.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped040.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_vertexIds_before"
  err.flush

theorem geometryRow040_vertexIds_read :
    geometryRowsJson040.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped040.vertexIds := by decide +kernel

noncomputable def geometryRow040_physicalVolumeNumeratorChars : List Char := ['2', '1', '2', '1', '2', '4', '3', '3', '1', '2', '0', '0', '6', '1', '5', '9', '9', '8', '3', '8', '7', '9', '3', '6', '2', '1', '8', '8', '8', '7', '1', '7', '9', '2', '8', '3', '5', '2', '1', '9']
noncomputable def geometryRow040_physicalVolumeDenominatorChars : List Char := ['2', '3', '0', '3', '9', '9', '5', '3', '0', '9', '7', '0', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_physicalVolumeText : String := String.ofList (geometryRow040_physicalVolumeNumeratorChars ++ '/' :: geometryRow040_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_physicalVolume_before_field"
  err.flush

theorem geometryRow040_physicalVolume_field :
    geometryRowsJson040.getObjVal? "physical_volume" = .ok (.str geometryRow040_physicalVolumeText) := by rfl

theorem geometryRow040_physicalVolume_numerator_no_slash :
    geometryRow040_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeNumeratorChars = some (2121243312006159983879362188871792835219 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow040_physicalVolumeDenominatorChars = some (23039953097011200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_physicalVolume_denominator_nonzero : (23039953097011200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_physicalVolume_parse :
    parseRational geometryRow040_physicalVolumeText = .ok geometryRowsTyped040.physicalVolume :=
  original_rational_fraction_of_chars geometryRow040_physicalVolumeNumeratorChars geometryRow040_physicalVolumeDenominatorChars
    (2121243312006159983879362188871792835219 : Int) (23039953097011200000000000000000000000000000000000000000000000000 : Int)
    geometryRow040_physicalVolume_numerator_no_slash geometryRow040_physicalVolume_numerator_parse
    geometryRow040_physicalVolume_denominator_parse geometryRow040_physicalVolume_denominator_nonzero

theorem geometryRow040_physicalVolume_read :
    rationalField geometryRowsJson040 "physical_volume" = .ok geometryRowsTyped040.physicalVolume :=
  original_rationalField_of_string geometryRowsJson040 "physical_volume" geometryRow040_physicalVolumeText
    geometryRowsTyped040.physicalVolume geometryRow040_physicalVolume_field geometryRow040_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_physicalVolume_complete"
  err.flush

noncomputable def geometryRow040_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow040_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_meanGapText : String := String.ofList (geometryRow040_meanGapNumeratorChars ++ '/' :: geometryRow040_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_meanGap_before_field"
  err.flush

theorem geometryRow040_meanGap_field :
    geometryRowsJson040.getObjVal? "mean_gap" = .ok (.str geometryRow040_meanGapText) := by rfl

theorem geometryRow040_meanGap_numerator_no_slash :
    geometryRow040_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_meanGap_numerator_parse :
    SourceJson.intChars geometryRow040_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_parse :
    SourceJson.intChars geometryRow040_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow040_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_meanGap_parse :
    parseRational geometryRow040_meanGapText = .ok geometryRowsTyped040.meanGap :=
  original_rational_fraction_of_chars geometryRow040_meanGapNumeratorChars geometryRow040_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow040_meanGap_numerator_no_slash geometryRow040_meanGap_numerator_parse
    geometryRow040_meanGap_denominator_parse geometryRow040_meanGap_denominator_nonzero

theorem geometryRow040_meanGap_read :
    rationalField geometryRowsJson040 "mean_gap" = .ok geometryRowsTyped040.meanGap :=
  original_rationalField_of_string geometryRowsJson040 "mean_gap" geometryRow040_meanGapText
    geometryRowsTyped040.meanGap geometryRow040_meanGap_field geometryRow040_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_meanGap_complete"
  err.flush

noncomputable def geometryRow040_jensenBoundNumeratorChars : List Char := ['9', '4', '5', '1', '6', '8', '1', '4', '6', '7', '6', '1', '5', '8', '5', '7', '5', '7', '7', '4', '8', '2', '5', '5', '0', '6', '5', '4', '2', '1', '7', '4', '4', '4', '9', '8', '4', '6', '8', '5', '8', '8', '4', '4', '5', '2', '4', '9', '1', '2', '2', '7', '1', '1', '1', '9', '2', '9', '0', '2', '2', '3', '1', '6', '8', '8', '9', '4', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow040_jensenBoundDenominatorChars : List Char := ['2', '7', '0', '1', '6', '3', '6', '3', '3', '4', '1', '0', '0', '7', '5', '4', '7', '2', '2', '9', '7', '9', '0', '1', '6', '2', '2', '9', '1', '9', '1', '9', '1', '9', '3', '2', '9', '4', '6', '4', '9', '8', '0', '9', '1', '1', '0', '9', '1', '2', '6', '8', '9', '9', '1', '1', '1', '5', '9', '3', '7', '3', '4', '6', '2', '8', '9', '2', '2', '2', '0', '8', '5', '6', '8', '6', '5', '7', '6', '5', '3', '7', '9', '3', '0', '3', '4', '0', '0', '1', '3', '7', '8', '6', '6', '8', '3', '5', '8', '3', '2', '1', '8', '7', '2', '3']
noncomputable def geometryRow040_jensenBoundText : String := String.ofList (geometryRow040_jensenBoundNumeratorChars ++ '/' :: geometryRow040_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_jensenBound_before_field"
  err.flush

theorem geometryRow040_jensenBound_field :
    geometryRowsJson040.getObjVal? "jensen_bound" = .ok (.str geometryRow040_jensenBoundText) := by rfl

theorem geometryRow040_jensenBound_numerator_no_slash :
    geometryRow040_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow040_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow040_jensenBoundNumeratorChars = some (945168146761585757748255065421744498468588445249122711192902231688941250000000000000000000 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow040_jensenBoundDenominatorChars = some (2701636334100754722979016229191919329464980911091268991115937346289222085686576537930340013786683583218723 : Int) := by decide +kernel

theorem geometryRow040_jensenBound_denominator_nonzero : (2701636334100754722979016229191919329464980911091268991115937346289222085686576537930340013786683583218723 : Int) ≠ 0 := by decide +kernel

theorem geometryRow040_jensenBound_parse :
    parseRational geometryRow040_jensenBoundText = .ok geometryRowsTyped040.jensenBound :=
  original_rational_fraction_of_chars geometryRow040_jensenBoundNumeratorChars geometryRow040_jensenBoundDenominatorChars
    (945168146761585757748255065421744498468588445249122711192902231688941250000000000000000000 : Int) (2701636334100754722979016229191919329464980911091268991115937346289222085686576537930340013786683583218723 : Int)
    geometryRow040_jensenBound_numerator_no_slash geometryRow040_jensenBound_numerator_parse
    geometryRow040_jensenBound_denominator_parse geometryRow040_jensenBound_denominator_nonzero

theorem geometryRow040_jensenBound_read :
    rationalField geometryRowsJson040 "jensen_bound" = .ok geometryRowsTyped040.jensenBound :=
  original_rationalField_of_string geometryRowsJson040 "jensen_bound" geometryRow040_jensenBoundText
    geometryRowsTyped040.jensenBound geometryRow040_jensenBound_field geometryRow040_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_factorMaxima_before"
  err.flush

theorem geometryRow040_factorMaxima_read :
    rationalArrayField geometryRowsJson040 "factor_maxima" = .ok geometryRowsTyped040.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_gapWeightedMeans_before"
  err.flush

theorem geometryRow040_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson040 "gap_weighted_means" = .ok geometryRowsTyped040.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow040_floorChars : List Char := ['2', '7', '7', '1', '7', '9', '9', '2', '4', '5', '8', '7', '6', '6']
noncomputable def geometryRow040_floorText : String := String.ofList geometryRow040_floorChars

theorem geometryRow040_floor_text_read :
    geometryRowsJson040.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow040_floorText := by rfl

theorem geometryRow040_floor_chars_parse :
    SourceJson.intChars geometryRow040_floorChars = some (27717992458766 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_040_original_decoder_complete"
  err.flush

theorem geometryRow040_shape :
    geometryRowsTyped040.simplexId = 40 ∧
    geometryRowsTyped040.vertexIds.size = 9 ∧ geometryRowsTyped040.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped040.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped040.factorMaxima.size = 10 ∧ geometryRowsTyped040.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson041 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped041 : GeometryRow :=
  { simplexId := 41,
    vertexIds := #[32, 30, 28, 16, 14, 4, 3, 1, 0],
    physicalVolume := ((586463577936671932463591521637571078938311 : ℚ) / (238323010277560320000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1544234459 : ℚ) / (521482500000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((35240670927248284384858663 : ℚ) / (397105219358427333600000000 : ℚ)), ((652922278170999645642299 : ℚ) / (7091164631400488100000000 : ℚ)), ((1151461885670625738955457 : ℚ) / (9927630483960683340000000 : ℚ)), ((6040266071796378792363379 : ℚ) / (66184203226404555600000000 : ℚ)), ((2001433538857266483179313 : ℚ) / (22061401075468185200000000 : ℚ)), ((1302971626394885769884269 : ℚ) / (18050237243564878800000000 : ℚ)), ((2540155344077992053348263 : ℚ) / (72200948974259515200000000 : ℚ)), ((41393829919575021382943 : ℚ) / (1183622114332123200000000 : ℚ)), ((1214591107310255777052649 : ℚ) / (36100474487129757600000000 : ℚ)), ((222564759056086878587953 : ℚ) / (7091164631400488100000000 : ℚ))],
    jensenBound := ((8242506108246890576568903779092000696542578787688243537959552713197616214173211731463533501359462780657071735919098741300072218350292150258739879127818393907096101971735602517504648567077647054069502771200000000000000000000000 : ℚ) / (208110959767396829215656551315032351524847633827823238873671937977618990288740530305051380315822636532677481224644096061268817824173940858513592439854277080441797185192408328588855425472384431211720331994097758300586745023359486330019736563 : ℚ)),
    jensenFloorQ96 := (3137934754608285 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_simplexId_before"
  err.flush

theorem geometryRow041_simplexId_read :
    geometryRowsJson041.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped041.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_vertexIds_before"
  err.flush

theorem geometryRow041_vertexIds_read :
    geometryRowsJson041.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped041.vertexIds := by decide +kernel

noncomputable def geometryRow041_physicalVolumeNumeratorChars : List Char := ['5', '8', '6', '4', '6', '3', '5', '7', '7', '9', '3', '6', '6', '7', '1', '9', '3', '2', '4', '6', '3', '5', '9', '1', '5', '2', '1', '6', '3', '7', '5', '7', '1', '0', '7', '8', '9', '3', '8', '3', '1', '1']
noncomputable def geometryRow041_physicalVolumeDenominatorChars : List Char := ['2', '3', '8', '3', '2', '3', '0', '1', '0', '2', '7', '7', '5', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_physicalVolumeText : String := String.ofList (geometryRow041_physicalVolumeNumeratorChars ++ '/' :: geometryRow041_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_physicalVolume_before_field"
  err.flush

theorem geometryRow041_physicalVolume_field :
    geometryRowsJson041.getObjVal? "physical_volume" = .ok (.str geometryRow041_physicalVolumeText) := by rfl

theorem geometryRow041_physicalVolume_numerator_no_slash :
    geometryRow041_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeNumeratorChars = some (586463577936671932463591521637571078938311 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow041_physicalVolumeDenominatorChars = some (238323010277560320000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_physicalVolume_denominator_nonzero : (238323010277560320000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_physicalVolume_parse :
    parseRational geometryRow041_physicalVolumeText = .ok geometryRowsTyped041.physicalVolume :=
  original_rational_fraction_of_chars geometryRow041_physicalVolumeNumeratorChars geometryRow041_physicalVolumeDenominatorChars
    (586463577936671932463591521637571078938311 : Int) (238323010277560320000000000000000000000000000000000000000000000000 : Int)
    geometryRow041_physicalVolume_numerator_no_slash geometryRow041_physicalVolume_numerator_parse
    geometryRow041_physicalVolume_denominator_parse geometryRow041_physicalVolume_denominator_nonzero

theorem geometryRow041_physicalVolume_read :
    rationalField geometryRowsJson041 "physical_volume" = .ok geometryRowsTyped041.physicalVolume :=
  original_rationalField_of_string geometryRowsJson041 "physical_volume" geometryRow041_physicalVolumeText
    geometryRowsTyped041.physicalVolume geometryRow041_physicalVolume_field geometryRow041_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_physicalVolume_complete"
  err.flush

noncomputable def geometryRow041_meanGapNumeratorChars : List Char := ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9']
noncomputable def geometryRow041_meanGapDenominatorChars : List Char := ['5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_meanGapText : String := String.ofList (geometryRow041_meanGapNumeratorChars ++ '/' :: geometryRow041_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_meanGap_before_field"
  err.flush

theorem geometryRow041_meanGap_field :
    geometryRowsJson041.getObjVal? "mean_gap" = .ok (.str geometryRow041_meanGapText) := by rfl

theorem geometryRow041_meanGap_numerator_no_slash :
    geometryRow041_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_meanGap_numerator_parse :
    SourceJson.intChars geometryRow041_meanGapNumeratorChars = some (1544234459 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_parse :
    SourceJson.intChars geometryRow041_meanGapDenominatorChars = some (521482500000 : Int) := by decide +kernel

theorem geometryRow041_meanGap_denominator_nonzero : (521482500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_meanGap_parse :
    parseRational geometryRow041_meanGapText = .ok geometryRowsTyped041.meanGap :=
  original_rational_fraction_of_chars geometryRow041_meanGapNumeratorChars geometryRow041_meanGapDenominatorChars
    (1544234459 : Int) (521482500000 : Int)
    geometryRow041_meanGap_numerator_no_slash geometryRow041_meanGap_numerator_parse
    geometryRow041_meanGap_denominator_parse geometryRow041_meanGap_denominator_nonzero

theorem geometryRow041_meanGap_read :
    rationalField geometryRowsJson041 "mean_gap" = .ok geometryRowsTyped041.meanGap :=
  original_rationalField_of_string geometryRowsJson041 "mean_gap" geometryRow041_meanGapText
    geometryRowsTyped041.meanGap geometryRow041_meanGap_field geometryRow041_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_meanGap_complete"
  err.flush

noncomputable def geometryRow041_jensenBoundNumeratorChars : List Char := ['8', '2', '4', '2', '5', '0', '6', '1', '0', '8', '2', '4', '6', '8', '9', '0', '5', '7', '6', '5', '6', '8', '9', '0', '3', '7', '7', '9', '0', '9', '2', '0', '0', '0', '6', '9', '6', '5', '4', '2', '5', '7', '8', '7', '8', '7', '6', '8', '8', '2', '4', '3', '5', '3', '7', '9', '5', '9', '5', '5', '2', '7', '1', '3', '1', '9', '7', '6', '1', '6', '2', '1', '4', '1', '7', '3', '2', '1', '1', '7', '3', '1', '4', '6', '3', '5', '3', '3', '5', '0', '1', '3', '5', '9', '4', '6', '2', '7', '8', '0', '6', '5', '7', '0', '7', '1', '7', '3', '5', '9', '1', '9', '0', '9', '8', '7', '4', '1', '3', '0', '0', '0', '7', '2', '2', '1', '8', '3', '5', '0', '2', '9', '2', '1', '5', '0', '2', '5', '8', '7', '3', '9', '8', '7', '9', '1', '2', '7', '8', '1', '8', '3', '9', '3', '9', '0', '7', '0', '9', '6', '1', '0', '1', '9', '7', '1', '7', '3', '5', '6', '0', '2', '5', '1', '7', '5', '0', '4', '6', '4', '8', '5', '6', '7', '0', '7', '7', '6', '4', '7', '0', '5', '4', '0', '6', '9', '5', '0', '2', '7', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow041_jensenBoundDenominatorChars : List Char := ['2', '0', '8', '1', '1', '0', '9', '5', '9', '7', '6', '7', '3', '9', '6', '8', '2', '9', '2', '1', '5', '6', '5', '6', '5', '5', '1', '3', '1', '5', '0', '3', '2', '3', '5', '1', '5', '2', '4', '8', '4', '7', '6', '3', '3', '8', '2', '7', '8', '2', '3', '2', '3', '8', '8', '7', '3', '6', '7', '1', '9', '3', '7', '9', '7', '7', '6', '1', '8', '9', '9', '0', '2', '8', '8', '7', '4', '0', '5', '3', '0', '3', '0', '5', '0', '5', '1', '3', '8', '0', '3', '1', '5', '8', '2', '2', '6', '3', '6', '5', '3', '2', '6', '7', '7', '4', '8', '1', '2', '2', '4', '6', '4', '4', '0', '9', '6', '0', '6', '1', '2', '6', '8', '8', '1', '7', '8', '2', '4', '1', '7', '3', '9', '4', '0', '8', '5', '8', '5', '1', '3', '5', '9', '2', '4', '3', '9', '8', '5', '4', '2', '7', '7', '0', '8', '0', '4', '4', '1', '7', '9', '7', '1', '8', '5', '1', '9', '2', '4', '0', '8', '3', '2', '8', '5', '8', '8', '8', '5', '5', '4', '2', '5', '4', '7', '2', '3', '8', '4', '4', '3', '1', '2', '1', '1', '7', '2', '0', '3', '3', '1', '9', '9', '4', '0', '9', '7', '7', '5', '8', '3', '0', '0', '5', '8', '6', '7', '4', '5', '0', '2', '3', '3', '5', '9', '4', '8', '6', '3', '3', '0', '0', '1', '9', '7', '3', '6', '5', '6', '3']
noncomputable def geometryRow041_jensenBoundText : String := String.ofList (geometryRow041_jensenBoundNumeratorChars ++ '/' :: geometryRow041_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_jensenBound_before_field"
  err.flush

theorem geometryRow041_jensenBound_field :
    geometryRowsJson041.getObjVal? "jensen_bound" = .ok (.str geometryRow041_jensenBoundText) := by rfl

theorem geometryRow041_jensenBound_numerator_no_slash :
    geometryRow041_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow041_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow041_jensenBoundNumeratorChars = some (8242506108246890576568903779092000696542578787688243537959552713197616214173211731463533501359462780657071735919098741300072218350292150258739879127818393907096101971735602517504648567077647054069502771200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow041_jensenBoundDenominatorChars = some (208110959767396829215656551315032351524847633827823238873671937977618990288740530305051380315822636532677481224644096061268817824173940858513592439854277080441797185192408328588855425472384431211720331994097758300586745023359486330019736563 : Int) := by decide +kernel

theorem geometryRow041_jensenBound_denominator_nonzero : (208110959767396829215656551315032351524847633827823238873671937977618990288740530305051380315822636532677481224644096061268817824173940858513592439854277080441797185192408328588855425472384431211720331994097758300586745023359486330019736563 : Int) ≠ 0 := by decide +kernel

theorem geometryRow041_jensenBound_parse :
    parseRational geometryRow041_jensenBoundText = .ok geometryRowsTyped041.jensenBound :=
  original_rational_fraction_of_chars geometryRow041_jensenBoundNumeratorChars geometryRow041_jensenBoundDenominatorChars
    (8242506108246890576568903779092000696542578787688243537959552713197616214173211731463533501359462780657071735919098741300072218350292150258739879127818393907096101971735602517504648567077647054069502771200000000000000000000000 : Int) (208110959767396829215656551315032351524847633827823238873671937977618990288740530305051380315822636532677481224644096061268817824173940858513592439854277080441797185192408328588855425472384431211720331994097758300586745023359486330019736563 : Int)
    geometryRow041_jensenBound_numerator_no_slash geometryRow041_jensenBound_numerator_parse
    geometryRow041_jensenBound_denominator_parse geometryRow041_jensenBound_denominator_nonzero

theorem geometryRow041_jensenBound_read :
    rationalField geometryRowsJson041 "jensen_bound" = .ok geometryRowsTyped041.jensenBound :=
  original_rationalField_of_string geometryRowsJson041 "jensen_bound" geometryRow041_jensenBoundText
    geometryRowsTyped041.jensenBound geometryRow041_jensenBound_field geometryRow041_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_factorMaxima_before"
  err.flush

theorem geometryRow041_factorMaxima_read :
    rationalArrayField geometryRowsJson041 "factor_maxima" = .ok geometryRowsTyped041.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_gapWeightedMeans_before"
  err.flush

theorem geometryRow041_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson041 "gap_weighted_means" = .ok geometryRowsTyped041.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow041_floorChars : List Char := ['3', '1', '3', '7', '9', '3', '4', '7', '5', '4', '6', '0', '8', '2', '8', '5']
noncomputable def geometryRow041_floorText : String := String.ofList geometryRow041_floorChars

theorem geometryRow041_floor_text_read :
    geometryRowsJson041.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow041_floorText := by rfl

theorem geometryRow041_floor_chars_parse :
    SourceJson.intChars geometryRow041_floorChars = some (3137934754608285 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_041_original_decoder_complete"
  err.flush

theorem geometryRow041_shape :
    geometryRowsTyped041.simplexId = 41 ∧
    geometryRowsTyped041.vertexIds.size = 9 ∧ geometryRowsTyped041.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped041.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped041.factorMaxima.size = 10 ∧ geometryRowsTyped041.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson042 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped042 : GeometryRow :=
  { simplexId := 42,
    vertexIds := #[32, 30, 28, 16, 14, 12, 3, 1, 0],
    physicalVolume := ((15540153007657621841807736735580496537533 : ℚ) / (738986078380032000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((24277423 : ℚ) / (10864218750 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((8929736414635621643925071 : ℚ) / (99888369460325107200000000 : ℚ)), ((656971610099771702955547 : ℚ) / (7134883532880364800000000 : ℚ)), ((2325562542717662365078217 : ℚ) / (19977673892065021440000000 : ℚ)), ((3009505408708369403599511 : ℚ) / (33296123153441702400000000 : ℚ)), ((2991411812834279712345751 : ℚ) / (33296123153441702400000000 : ℚ)), ((664085588758243544954071 : ℚ) / (9080760860029555200000000 : ℚ)), ((665395116401216378576401 : ℚ) / (18161521720059110400000000 : ℚ)), ((625873054343010471969661 : ℚ) / (18161521720059110400000000 : ℚ)), ((300737827192432078234613 : ℚ) / (9080760860029555200000000 : ℚ)), ((223944894123177761408009 : ℚ) / (7134883532880364800000000 : ℚ))],
    jensenBound := ((575775278000689984709708827235451304509452626723328981467779406913166273323231153400246483135979284419037201499340609025819871968507609147770626209340508662905406287414391203796407817723307019447929143296000000000000000000000000 : ℚ) / (2287724591310230013369282232544063692529344925808212041707000979995854102290964022454549370080380628587260447837283249695333537247292987695786916566550642676400833319978708939596975815910725513345291274673354362349927288371339350770565610963 : ℚ)),
    jensenFloorQ96 := (19940170014524425 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_simplexId_before"
  err.flush

theorem geometryRow042_simplexId_read :
    geometryRowsJson042.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped042.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_vertexIds_before"
  err.flush

theorem geometryRow042_vertexIds_read :
    geometryRowsJson042.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped042.vertexIds := by decide +kernel

noncomputable def geometryRow042_physicalVolumeNumeratorChars : List Char := ['1', '5', '5', '4', '0', '1', '5', '3', '0', '0', '7', '6', '5', '7', '6', '2', '1', '8', '4', '1', '8', '0', '7', '7', '3', '6', '7', '3', '5', '5', '8', '0', '4', '9', '6', '5', '3', '7', '5', '3', '3']
noncomputable def geometryRow042_physicalVolumeDenominatorChars : List Char := ['7', '3', '8', '9', '8', '6', '0', '7', '8', '3', '8', '0', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_physicalVolumeText : String := String.ofList (geometryRow042_physicalVolumeNumeratorChars ++ '/' :: geometryRow042_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_physicalVolume_before_field"
  err.flush

theorem geometryRow042_physicalVolume_field :
    geometryRowsJson042.getObjVal? "physical_volume" = .ok (.str geometryRow042_physicalVolumeText) := by rfl

theorem geometryRow042_physicalVolume_numerator_no_slash :
    geometryRow042_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeNumeratorChars = some (15540153007657621841807736735580496537533 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeDenominatorChars = some (738986078380032000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_nonzero : (738986078380032000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_physicalVolume_parse :
    parseRational geometryRow042_physicalVolumeText = .ok geometryRowsTyped042.physicalVolume :=
  original_rational_fraction_of_chars geometryRow042_physicalVolumeNumeratorChars geometryRow042_physicalVolumeDenominatorChars
    (15540153007657621841807736735580496537533 : Int) (738986078380032000000000000000000000000000000000000000000000000 : Int)
    geometryRow042_physicalVolume_numerator_no_slash geometryRow042_physicalVolume_numerator_parse
    geometryRow042_physicalVolume_denominator_parse geometryRow042_physicalVolume_denominator_nonzero

theorem geometryRow042_physicalVolume_read :
    rationalField geometryRowsJson042 "physical_volume" = .ok geometryRowsTyped042.physicalVolume :=
  original_rationalField_of_string geometryRowsJson042 "physical_volume" geometryRow042_physicalVolumeText
    geometryRowsTyped042.physicalVolume geometryRow042_physicalVolume_field geometryRow042_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_physicalVolume_complete"
  err.flush

noncomputable def geometryRow042_meanGapNumeratorChars : List Char := ['2', '4', '2', '7', '7', '4', '2', '3']
noncomputable def geometryRow042_meanGapDenominatorChars : List Char := ['1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0']
noncomputable def geometryRow042_meanGapText : String := String.ofList (geometryRow042_meanGapNumeratorChars ++ '/' :: geometryRow042_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_meanGap_before_field"
  err.flush

theorem geometryRow042_meanGap_field :
    geometryRowsJson042.getObjVal? "mean_gap" = .ok (.str geometryRow042_meanGapText) := by rfl

theorem geometryRow042_meanGap_numerator_no_slash :
    geometryRow042_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_meanGap_numerator_parse :
    SourceJson.intChars geometryRow042_meanGapNumeratorChars = some (24277423 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_parse :
    SourceJson.intChars geometryRow042_meanGapDenominatorChars = some (10864218750 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_nonzero : (10864218750 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_meanGap_parse :
    parseRational geometryRow042_meanGapText = .ok geometryRowsTyped042.meanGap :=
  original_rational_fraction_of_chars geometryRow042_meanGapNumeratorChars geometryRow042_meanGapDenominatorChars
    (24277423 : Int) (10864218750 : Int)
    geometryRow042_meanGap_numerator_no_slash geometryRow042_meanGap_numerator_parse
    geometryRow042_meanGap_denominator_parse geometryRow042_meanGap_denominator_nonzero

theorem geometryRow042_meanGap_read :
    rationalField geometryRowsJson042 "mean_gap" = .ok geometryRowsTyped042.meanGap :=
  original_rationalField_of_string geometryRowsJson042 "mean_gap" geometryRow042_meanGapText
    geometryRowsTyped042.meanGap geometryRow042_meanGap_field geometryRow042_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_meanGap_complete"
  err.flush

noncomputable def geometryRow042_jensenBoundNumeratorChars : List Char := ['5', '7', '5', '7', '7', '5', '2', '7', '8', '0', '0', '0', '6', '8', '9', '9', '8', '4', '7', '0', '9', '7', '0', '8', '8', '2', '7', '2', '3', '5', '4', '5', '1', '3', '0', '4', '5', '0', '9', '4', '5', '2', '6', '2', '6', '7', '2', '3', '3', '2', '8', '9', '8', '1', '4', '6', '7', '7', '7', '9', '4', '0', '6', '9', '1', '3', '1', '6', '6', '2', '7', '3', '3', '2', '3', '2', '3', '1', '1', '5', '3', '4', '0', '0', '2', '4', '6', '4', '8', '3', '1', '3', '5', '9', '7', '9', '2', '8', '4', '4', '1', '9', '0', '3', '7', '2', '0', '1', '4', '9', '9', '3', '4', '0', '6', '0', '9', '0', '2', '5', '8', '1', '9', '8', '7', '1', '9', '6', '8', '5', '0', '7', '6', '0', '9', '1', '4', '7', '7', '7', '0', '6', '2', '6', '2', '0', '9', '3', '4', '0', '5', '0', '8', '6', '6', '2', '9', '0', '5', '4', '0', '6', '2', '8', '7', '4', '1', '4', '3', '9', '1', '2', '0', '3', '7', '9', '6', '4', '0', '7', '8', '1', '7', '7', '2', '3', '3', '0', '7', '0', '1', '9', '4', '4', '7', '9', '2', '9', '1', '4', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_jensenBoundDenominatorChars : List Char := ['2', '2', '8', '7', '7', '2', '4', '5', '9', '1', '3', '1', '0', '2', '3', '0', '0', '1', '3', '3', '6', '9', '2', '8', '2', '2', '3', '2', '5', '4', '4', '0', '6', '3', '6', '9', '2', '5', '2', '9', '3', '4', '4', '9', '2', '5', '8', '0', '8', '2', '1', '2', '0', '4', '1', '7', '0', '7', '0', '0', '0', '9', '7', '9', '9', '9', '5', '8', '5', '4', '1', '0', '2', '2', '9', '0', '9', '6', '4', '0', '2', '2', '4', '5', '4', '5', '4', '9', '3', '7', '0', '0', '8', '0', '3', '8', '0', '6', '2', '8', '5', '8', '7', '2', '6', '0', '4', '4', '7', '8', '3', '7', '2', '8', '3', '2', '4', '9', '6', '9', '5', '3', '3', '3', '5', '3', '7', '2', '4', '7', '2', '9', '2', '9', '8', '7', '6', '9', '5', '7', '8', '6', '9', '1', '6', '5', '6', '6', '5', '5', '0', '6', '4', '2', '6', '7', '6', '4', '0', '0', '8', '3', '3', '3', '1', '9', '9', '7', '8', '7', '0', '8', '9', '3', '9', '5', '9', '6', '9', '7', '5', '8', '1', '5', '9', '1', '0', '7', '2', '5', '5', '1', '3', '3', '4', '5', '2', '9', '1', '2', '7', '4', '6', '7', '3', '3', '5', '4', '3', '6', '2', '3', '4', '9', '9', '2', '7', '2', '8', '8', '3', '7', '1', '3', '3', '9', '3', '5', '0', '7', '7', '0', '5', '6', '5', '6', '1', '0', '9', '6', '3']
noncomputable def geometryRow042_jensenBoundText : String := String.ofList (geometryRow042_jensenBoundNumeratorChars ++ '/' :: geometryRow042_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_jensenBound_before_field"
  err.flush

theorem geometryRow042_jensenBound_field :
    geometryRowsJson042.getObjVal? "jensen_bound" = .ok (.str geometryRow042_jensenBoundText) := by rfl

theorem geometryRow042_jensenBound_numerator_no_slash :
    geometryRow042_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow042_jensenBoundNumeratorChars = some (575775278000689984709708827235451304509452626723328981467779406913166273323231153400246483135979284419037201499340609025819871968507609147770626209340508662905406287414391203796407817723307019447929143296000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow042_jensenBoundDenominatorChars = some (2287724591310230013369282232544063692529344925808212041707000979995854102290964022454549370080380628587260447837283249695333537247292987695786916566550642676400833319978708939596975815910725513345291274673354362349927288371339350770565610963 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_nonzero : (2287724591310230013369282232544063692529344925808212041707000979995854102290964022454549370080380628587260447837283249695333537247292987695786916566550642676400833319978708939596975815910725513345291274673354362349927288371339350770565610963 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_jensenBound_parse :
    parseRational geometryRow042_jensenBoundText = .ok geometryRowsTyped042.jensenBound :=
  original_rational_fraction_of_chars geometryRow042_jensenBoundNumeratorChars geometryRow042_jensenBoundDenominatorChars
    (575775278000689984709708827235451304509452626723328981467779406913166273323231153400246483135979284419037201499340609025819871968507609147770626209340508662905406287414391203796407817723307019447929143296000000000000000000000000 : Int) (2287724591310230013369282232544063692529344925808212041707000979995854102290964022454549370080380628587260447837283249695333537247292987695786916566550642676400833319978708939596975815910725513345291274673354362349927288371339350770565610963 : Int)
    geometryRow042_jensenBound_numerator_no_slash geometryRow042_jensenBound_numerator_parse
    geometryRow042_jensenBound_denominator_parse geometryRow042_jensenBound_denominator_nonzero

theorem geometryRow042_jensenBound_read :
    rationalField geometryRowsJson042 "jensen_bound" = .ok geometryRowsTyped042.jensenBound :=
  original_rationalField_of_string geometryRowsJson042 "jensen_bound" geometryRow042_jensenBoundText
    geometryRowsTyped042.jensenBound geometryRow042_jensenBound_field geometryRow042_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_factorMaxima_before"
  err.flush

theorem geometryRow042_factorMaxima_read :
    rationalArrayField geometryRowsJson042 "factor_maxima" = .ok geometryRowsTyped042.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_gapWeightedMeans_before"
  err.flush

theorem geometryRow042_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson042 "gap_weighted_means" = .ok geometryRowsTyped042.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow042_floorChars : List Char := ['1', '9', '9', '4', '0', '1', '7', '0', '0', '1', '4', '5', '2', '4', '4', '2', '5']
noncomputable def geometryRow042_floorText : String := String.ofList geometryRow042_floorChars

theorem geometryRow042_floor_text_read :
    geometryRowsJson042.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow042_floorText := by rfl

theorem geometryRow042_floor_chars_parse :
    SourceJson.intChars geometryRow042_floorChars = some (19940170014524425 : Int) := by decide +kernel

theorem geometryRow042_floor_parse :
    parseInteger geometryRow042_floorText = .ok geometryRowsTyped042.jensenFloorQ96 := by
  simp only [geometryRow042_floorText, parseInteger, String.toList_ofList, geometryRow042_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_042 :
    decodeGeometryRow geometryRowsJson042 = .ok geometryRowsTyped042 :=
  original_geometryRow_of_fields geometryRowsJson042 geometryRowsTyped042 geometryRow042_floorText
    geometryRow042_simplexId_read geometryRow042_vertexIds_read
    geometryRow042_physicalVolume_read geometryRow042_meanGap_read
    geometryRow042_factorMaxima_read geometryRow042_gapWeightedMeans_read
    geometryRow042_jensenBound_read geometryRow042_floor_text_read geometryRow042_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_042_original_decoder_complete"
  err.flush

theorem geometryRow042_shape :
    geometryRowsTyped042.simplexId = 42 ∧
    geometryRowsTyped042.vertexIds.size = 9 ∧ geometryRowsTyped042.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped042.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped042.factorMaxima.size = 10 ∧ geometryRowsTyped042.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson043 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped043 : GeometryRow :=
  { simplexId := 43,
    vertexIds := #[32, 30, 28, 16, 14, 12, 10, 1, 0],
    physicalVolume := ((1183384121107498550435237799589398239 : ℚ) / (161116150809600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((38514982235777016063013 : ℚ) / (428690437344615600000000 : ℚ)), ((5624313245970490369327 : ℚ) / (61241491049230800000000 : ℚ)), ((20032840814828552110769 : ℚ) / (171476174937846240000000 : ℚ)), ((25581537684883399618261 : ℚ) / (285793624896410400000000 : ℚ)), ((8475411095726032501767 : ℚ) / (95264541632136800000000 : ℚ)), ((5774597658648749989081 : ℚ) / (77943715880839200000000 : ℚ)), ((1485070679413955053579 : ℚ) / (38971857940419600000000 : ℚ)), ((1323039921100582764229 : ℚ) / (38971857940419600000000 : ℚ)), ((1280644993664096956549 : ℚ) / (38971857940419600000000 : ℚ)), ((1917296266093400446469 : ℚ) / (61241491049230800000000 : ℚ))],
    jensenBound := ((167051398501662697233620164625646637096757597038848772224601689185723523413326532928970699124352462991316524870680014730668261653006447285982494851220600886008674062323697170513920000000000000000000000 : ℚ) / (2912369251549483698246409903051096692715079044079488619809530654584348650993953717406128467678853010418259569382124038732060647491766024880536422010797071255967257918680196645022674365838154687047903487524874116066767 : ℚ)),
    jensenFloorQ96 := (4544470225292 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_simplexId_before"
  err.flush

theorem geometryRow043_simplexId_read :
    geometryRowsJson043.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped043.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_vertexIds_before"
  err.flush

theorem geometryRow043_vertexIds_read :
    geometryRowsJson043.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped043.vertexIds := by decide +kernel

noncomputable def geometryRow043_physicalVolumeNumeratorChars : List Char := ['1', '1', '8', '3', '3', '8', '4', '1', '2', '1', '1', '0', '7', '4', '9', '8', '5', '5', '0', '4', '3', '5', '2', '3', '7', '7', '9', '9', '5', '8', '9', '3', '9', '8', '2', '3', '9']
noncomputable def geometryRow043_physicalVolumeDenominatorChars : List Char := ['1', '6', '1', '1', '1', '6', '1', '5', '0', '8', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_physicalVolumeText : String := String.ofList (geometryRow043_physicalVolumeNumeratorChars ++ '/' :: geometryRow043_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_physicalVolume_before_field"
  err.flush

theorem geometryRow043_physicalVolume_field :
    geometryRowsJson043.getObjVal? "physical_volume" = .ok (.str geometryRow043_physicalVolumeText) := by rfl

theorem geometryRow043_physicalVolume_numerator_no_slash :
    geometryRow043_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeNumeratorChars = some (1183384121107498550435237799589398239 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeDenominatorChars = some (161116150809600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_nonzero : (161116150809600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_physicalVolume_parse :
    parseRational geometryRow043_physicalVolumeText = .ok geometryRowsTyped043.physicalVolume :=
  original_rational_fraction_of_chars geometryRow043_physicalVolumeNumeratorChars geometryRow043_physicalVolumeDenominatorChars
    (1183384121107498550435237799589398239 : Int) (161116150809600000000000000000000000000000000000000000000000000 : Int)
    geometryRow043_physicalVolume_numerator_no_slash geometryRow043_physicalVolume_numerator_parse
    geometryRow043_physicalVolume_denominator_parse geometryRow043_physicalVolume_denominator_nonzero

theorem geometryRow043_physicalVolume_read :
    rationalField geometryRowsJson043 "physical_volume" = .ok geometryRowsTyped043.physicalVolume :=
  original_rationalField_of_string geometryRowsJson043 "physical_volume" geometryRow043_physicalVolumeText
    geometryRowsTyped043.physicalVolume geometryRow043_physicalVolume_field geometryRow043_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_physicalVolume_complete"
  err.flush

noncomputable def geometryRow043_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow043_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_meanGapText : String := String.ofList (geometryRow043_meanGapNumeratorChars ++ '/' :: geometryRow043_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_meanGap_before_field"
  err.flush

theorem geometryRow043_meanGap_field :
    geometryRowsJson043.getObjVal? "mean_gap" = .ok (.str geometryRow043_meanGapText) := by rfl

theorem geometryRow043_meanGap_numerator_no_slash :
    geometryRow043_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_meanGap_numerator_parse :
    SourceJson.intChars geometryRow043_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_parse :
    SourceJson.intChars geometryRow043_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_meanGap_parse :
    parseRational geometryRow043_meanGapText = .ok geometryRowsTyped043.meanGap :=
  original_rational_fraction_of_chars geometryRow043_meanGapNumeratorChars geometryRow043_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow043_meanGap_numerator_no_slash geometryRow043_meanGap_numerator_parse
    geometryRow043_meanGap_denominator_parse geometryRow043_meanGap_denominator_nonzero

theorem geometryRow043_meanGap_read :
    rationalField geometryRowsJson043 "mean_gap" = .ok geometryRowsTyped043.meanGap :=
  original_rationalField_of_string geometryRowsJson043 "mean_gap" geometryRow043_meanGapText
    geometryRowsTyped043.meanGap geometryRow043_meanGap_field geometryRow043_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_meanGap_complete"
  err.flush

noncomputable def geometryRow043_jensenBoundNumeratorChars : List Char := ['1', '6', '7', '0', '5', '1', '3', '9', '8', '5', '0', '1', '6', '6', '2', '6', '9', '7', '2', '3', '3', '6', '2', '0', '1', '6', '4', '6', '2', '5', '6', '4', '6', '6', '3', '7', '0', '9', '6', '7', '5', '7', '5', '9', '7', '0', '3', '8', '8', '4', '8', '7', '7', '2', '2', '2', '4', '6', '0', '1', '6', '8', '9', '1', '8', '5', '7', '2', '3', '5', '2', '3', '4', '1', '3', '3', '2', '6', '5', '3', '2', '9', '2', '8', '9', '7', '0', '6', '9', '9', '1', '2', '4', '3', '5', '2', '4', '6', '2', '9', '9', '1', '3', '1', '6', '5', '2', '4', '8', '7', '0', '6', '8', '0', '0', '1', '4', '7', '3', '0', '6', '6', '8', '2', '6', '1', '6', '5', '3', '0', '0', '6', '4', '4', '7', '2', '8', '5', '9', '8', '2', '4', '9', '4', '8', '5', '1', '2', '2', '0', '6', '0', '0', '8', '8', '6', '0', '0', '8', '6', '7', '4', '0', '6', '2', '3', '2', '3', '6', '9', '7', '1', '7', '0', '5', '1', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_jensenBoundDenominatorChars : List Char := ['2', '9', '1', '2', '3', '6', '9', '2', '5', '1', '5', '4', '9', '4', '8', '3', '6', '9', '8', '2', '4', '6', '4', '0', '9', '9', '0', '3', '0', '5', '1', '0', '9', '6', '6', '9', '2', '7', '1', '5', '0', '7', '9', '0', '4', '4', '0', '7', '9', '4', '8', '8', '6', '1', '9', '8', '0', '9', '5', '3', '0', '6', '5', '4', '5', '8', '4', '3', '4', '8', '6', '5', '0', '9', '9', '3', '9', '5', '3', '7', '1', '7', '4', '0', '6', '1', '2', '8', '4', '6', '7', '6', '7', '8', '8', '5', '3', '0', '1', '0', '4', '1', '8', '2', '5', '9', '5', '6', '9', '3', '8', '2', '1', '2', '4', '0', '3', '8', '7', '3', '2', '0', '6', '0', '6', '4', '7', '4', '9', '1', '7', '6', '6', '0', '2', '4', '8', '8', '0', '5', '3', '6', '4', '2', '2', '0', '1', '0', '7', '9', '7', '0', '7', '1', '2', '5', '5', '9', '6', '7', '2', '5', '7', '9', '1', '8', '6', '8', '0', '1', '9', '6', '6', '4', '5', '0', '2', '2', '6', '7', '4', '3', '6', '5', '8', '3', '8', '1', '5', '4', '6', '8', '7', '0', '4', '7', '9', '0', '3', '4', '8', '7', '5', '2', '4', '8', '7', '4', '1', '1', '6', '0', '6', '6', '7', '6', '7']
noncomputable def geometryRow043_jensenBoundText : String := String.ofList (geometryRow043_jensenBoundNumeratorChars ++ '/' :: geometryRow043_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_jensenBound_before_field"
  err.flush

theorem geometryRow043_jensenBound_field :
    geometryRowsJson043.getObjVal? "jensen_bound" = .ok (.str geometryRow043_jensenBoundText) := by rfl

theorem geometryRow043_jensenBound_numerator_no_slash :
    geometryRow043_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow043_jensenBoundNumeratorChars = some (167051398501662697233620164625646637096757597038848772224601689185723523413326532928970699124352462991316524870680014730668261653006447285982494851220600886008674062323697170513920000000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow043_jensenBoundDenominatorChars = some (2912369251549483698246409903051096692715079044079488619809530654584348650993953717406128467678853010418259569382124038732060647491766024880536422010797071255967257918680196645022674365838154687047903487524874116066767 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_nonzero : (2912369251549483698246409903051096692715079044079488619809530654584348650993953717406128467678853010418259569382124038732060647491766024880536422010797071255967257918680196645022674365838154687047903487524874116066767 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_jensenBound_parse :
    parseRational geometryRow043_jensenBoundText = .ok geometryRowsTyped043.jensenBound :=
  original_rational_fraction_of_chars geometryRow043_jensenBoundNumeratorChars geometryRow043_jensenBoundDenominatorChars
    (167051398501662697233620164625646637096757597038848772224601689185723523413326532928970699124352462991316524870680014730668261653006447285982494851220600886008674062323697170513920000000000000000000000 : Int) (2912369251549483698246409903051096692715079044079488619809530654584348650993953717406128467678853010418259569382124038732060647491766024880536422010797071255967257918680196645022674365838154687047903487524874116066767 : Int)
    geometryRow043_jensenBound_numerator_no_slash geometryRow043_jensenBound_numerator_parse
    geometryRow043_jensenBound_denominator_parse geometryRow043_jensenBound_denominator_nonzero

theorem geometryRow043_jensenBound_read :
    rationalField geometryRowsJson043 "jensen_bound" = .ok geometryRowsTyped043.jensenBound :=
  original_rationalField_of_string geometryRowsJson043 "jensen_bound" geometryRow043_jensenBoundText
    geometryRowsTyped043.jensenBound geometryRow043_jensenBound_field geometryRow043_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_factorMaxima_before"
  err.flush

theorem geometryRow043_factorMaxima_read :
    rationalArrayField geometryRowsJson043 "factor_maxima" = .ok geometryRowsTyped043.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_gapWeightedMeans_before"
  err.flush

theorem geometryRow043_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson043 "gap_weighted_means" = .ok geometryRowsTyped043.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow043_floorChars : List Char := ['4', '5', '4', '4', '4', '7', '0', '2', '2', '5', '2', '9', '2']
noncomputable def geometryRow043_floorText : String := String.ofList geometryRow043_floorChars

theorem geometryRow043_floor_text_read :
    geometryRowsJson043.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow043_floorText := by rfl

theorem geometryRow043_floor_chars_parse :
    SourceJson.intChars geometryRow043_floorChars = some (4544470225292 : Int) := by decide +kernel

theorem geometryRow043_floor_parse :
    parseInteger geometryRow043_floorText = .ok geometryRowsTyped043.jensenFloorQ96 := by
  simp only [geometryRow043_floorText, parseInteger, String.toList_ofList, geometryRow043_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_043 :
    decodeGeometryRow geometryRowsJson043 = .ok geometryRowsTyped043 :=
  original_geometryRow_of_fields geometryRowsJson043 geometryRowsTyped043 geometryRow043_floorText
    geometryRow043_simplexId_read geometryRow043_vertexIds_read
    geometryRow043_physicalVolume_read geometryRow043_meanGap_read
    geometryRow043_factorMaxima_read geometryRow043_gapWeightedMeans_read
    geometryRow043_jensenBound_read geometryRow043_floor_text_read geometryRow043_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_043_original_decoder_complete"
  err.flush

theorem geometryRow043_shape :
    geometryRowsTyped043.simplexId = 43 ∧
    geometryRowsTyped043.vertexIds.size = 9 ∧ geometryRowsTyped043.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped043.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped043.factorMaxima.size = 10 ∧ geometryRowsTyped043.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson044 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped044 : GeometryRow :=
  { simplexId := 44,
    vertexIds := #[32, 30, 28, 16, 14, 12, 10, 8, 0],
    physicalVolume := ((26186911939040839335032787614813548979 : ℚ) / (355113148723200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((5440323099173 : ℚ) / (61023600000000 : ℚ)), ((5520923125529 : ℚ) / (61023600000000 : ℚ)), ((59998340867837 : ℚ) / (512598240000000 : ℚ)), ((227694605659043 : ℚ) / (2562991200000000 : ℚ)), ((226301839096163 : ℚ) / (2562991200000000 : ℚ)), ((17524647218341 : ℚ) / (232999200000000 : ℚ)), ((4490314839259 : ℚ) / (116499600000000 : ℚ)), ((576469902097 : ℚ) / (16642800000000 : ℚ)), ((558365291857 : ℚ) / (16642800000000 : ℚ)), ((5648044776889 : ℚ) / (183070800000000 : ℚ))],
    jensenBound := ((4012457274618029714195218205460789373174533596934351651019829047523639461771055260342026240000000000000000000000 : ℚ) / (14268753592364243958361614024162395982008821376325481453428048175450739483872119536920719769542430634837064697932250546476082709 : ℚ)),
    jensenFloorQ96 := (22279424406424 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_simplexId_before"
  err.flush

theorem geometryRow044_simplexId_read :
    geometryRowsJson044.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped044.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_vertexIds_before"
  err.flush

theorem geometryRow044_vertexIds_read :
    geometryRowsJson044.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped044.vertexIds := by decide +kernel

noncomputable def geometryRow044_physicalVolumeNumeratorChars : List Char := ['2', '6', '1', '8', '6', '9', '1', '1', '9', '3', '9', '0', '4', '0', '8', '3', '9', '3', '3', '5', '0', '3', '2', '7', '8', '7', '6', '1', '4', '8', '1', '3', '5', '4', '8', '9', '7', '9']
noncomputable def geometryRow044_physicalVolumeDenominatorChars : List Char := ['3', '5', '5', '1', '1', '3', '1', '4', '8', '7', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_physicalVolumeText : String := String.ofList (geometryRow044_physicalVolumeNumeratorChars ++ '/' :: geometryRow044_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_physicalVolume_before_field"
  err.flush

theorem geometryRow044_physicalVolume_field :
    geometryRowsJson044.getObjVal? "physical_volume" = .ok (.str geometryRow044_physicalVolumeText) := by rfl

theorem geometryRow044_physicalVolume_numerator_no_slash :
    geometryRow044_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeNumeratorChars = some (26186911939040839335032787614813548979 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeDenominatorChars = some (355113148723200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_nonzero : (355113148723200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_physicalVolume_parse :
    parseRational geometryRow044_physicalVolumeText = .ok geometryRowsTyped044.physicalVolume :=
  original_rational_fraction_of_chars geometryRow044_physicalVolumeNumeratorChars geometryRow044_physicalVolumeDenominatorChars
    (26186911939040839335032787614813548979 : Int) (355113148723200000000000000000000000000000000000000000000000000 : Int)
    geometryRow044_physicalVolume_numerator_no_slash geometryRow044_physicalVolume_numerator_parse
    geometryRow044_physicalVolume_denominator_parse geometryRow044_physicalVolume_denominator_nonzero

theorem geometryRow044_physicalVolume_read :
    rationalField geometryRowsJson044 "physical_volume" = .ok geometryRowsTyped044.physicalVolume :=
  original_rationalField_of_string geometryRowsJson044 "physical_volume" geometryRow044_physicalVolumeText
    geometryRowsTyped044.physicalVolume geometryRow044_physicalVolume_field geometryRow044_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_physicalVolume_complete"
  err.flush

noncomputable def geometryRow044_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow044_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_meanGapText : String := String.ofList (geometryRow044_meanGapNumeratorChars ++ '/' :: geometryRow044_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_meanGap_before_field"
  err.flush

theorem geometryRow044_meanGap_field :
    geometryRowsJson044.getObjVal? "mean_gap" = .ok (.str geometryRow044_meanGapText) := by rfl

theorem geometryRow044_meanGap_numerator_no_slash :
    geometryRow044_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_meanGap_numerator_parse :
    SourceJson.intChars geometryRow044_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_parse :
    SourceJson.intChars geometryRow044_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_meanGap_parse :
    parseRational geometryRow044_meanGapText = .ok geometryRowsTyped044.meanGap :=
  original_rational_fraction_of_chars geometryRow044_meanGapNumeratorChars geometryRow044_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow044_meanGap_numerator_no_slash geometryRow044_meanGap_numerator_parse
    geometryRow044_meanGap_denominator_parse geometryRow044_meanGap_denominator_nonzero

theorem geometryRow044_meanGap_read :
    rationalField geometryRowsJson044 "mean_gap" = .ok geometryRowsTyped044.meanGap :=
  original_rationalField_of_string geometryRowsJson044 "mean_gap" geometryRow044_meanGapText
    geometryRowsTyped044.meanGap geometryRow044_meanGap_field geometryRow044_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_meanGap_complete"
  err.flush

noncomputable def geometryRow044_jensenBoundNumeratorChars : List Char := ['4', '0', '1', '2', '4', '5', '7', '2', '7', '4', '6', '1', '8', '0', '2', '9', '7', '1', '4', '1', '9', '5', '2', '1', '8', '2', '0', '5', '4', '6', '0', '7', '8', '9', '3', '7', '3', '1', '7', '4', '5', '3', '3', '5', '9', '6', '9', '3', '4', '3', '5', '1', '6', '5', '1', '0', '1', '9', '8', '2', '9', '0', '4', '7', '5', '2', '3', '6', '3', '9', '4', '6', '1', '7', '7', '1', '0', '5', '5', '2', '6', '0', '3', '4', '2', '0', '2', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_jensenBoundDenominatorChars : List Char := ['1', '4', '2', '6', '8', '7', '5', '3', '5', '9', '2', '3', '6', '4', '2', '4', '3', '9', '5', '8', '3', '6', '1', '6', '1', '4', '0', '2', '4', '1', '6', '2', '3', '9', '5', '9', '8', '2', '0', '0', '8', '8', '2', '1', '3', '7', '6', '3', '2', '5', '4', '8', '1', '4', '5', '3', '4', '2', '8', '0', '4', '8', '1', '7', '5', '4', '5', '0', '7', '3', '9', '4', '8', '3', '8', '7', '2', '1', '1', '9', '5', '3', '6', '9', '2', '0', '7', '1', '9', '7', '6', '9', '5', '4', '2', '4', '3', '0', '6', '3', '4', '8', '3', '7', '0', '6', '4', '6', '9', '7', '9', '3', '2', '2', '5', '0', '5', '4', '6', '4', '7', '6', '0', '8', '2', '7', '0', '9']
noncomputable def geometryRow044_jensenBoundText : String := String.ofList (geometryRow044_jensenBoundNumeratorChars ++ '/' :: geometryRow044_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_jensenBound_before_field"
  err.flush

theorem geometryRow044_jensenBound_field :
    geometryRowsJson044.getObjVal? "jensen_bound" = .ok (.str geometryRow044_jensenBoundText) := by rfl

theorem geometryRow044_jensenBound_numerator_no_slash :
    geometryRow044_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow044_jensenBoundNumeratorChars = some (4012457274618029714195218205460789373174533596934351651019829047523639461771055260342026240000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow044_jensenBoundDenominatorChars = some (14268753592364243958361614024162395982008821376325481453428048175450739483872119536920719769542430634837064697932250546476082709 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_nonzero : (14268753592364243958361614024162395982008821376325481453428048175450739483872119536920719769542430634837064697932250546476082709 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_jensenBound_parse :
    parseRational geometryRow044_jensenBoundText = .ok geometryRowsTyped044.jensenBound :=
  original_rational_fraction_of_chars geometryRow044_jensenBoundNumeratorChars geometryRow044_jensenBoundDenominatorChars
    (4012457274618029714195218205460789373174533596934351651019829047523639461771055260342026240000000000000000000000 : Int) (14268753592364243958361614024162395982008821376325481453428048175450739483872119536920719769542430634837064697932250546476082709 : Int)
    geometryRow044_jensenBound_numerator_no_slash geometryRow044_jensenBound_numerator_parse
    geometryRow044_jensenBound_denominator_parse geometryRow044_jensenBound_denominator_nonzero

theorem geometryRow044_jensenBound_read :
    rationalField geometryRowsJson044 "jensen_bound" = .ok geometryRowsTyped044.jensenBound :=
  original_rationalField_of_string geometryRowsJson044 "jensen_bound" geometryRow044_jensenBoundText
    geometryRowsTyped044.jensenBound geometryRow044_jensenBound_field geometryRow044_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_factorMaxima_before"
  err.flush

theorem geometryRow044_factorMaxima_read :
    rationalArrayField geometryRowsJson044 "factor_maxima" = .ok geometryRowsTyped044.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_gapWeightedMeans_before"
  err.flush

theorem geometryRow044_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson044 "gap_weighted_means" = .ok geometryRowsTyped044.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow044_floorChars : List Char := ['2', '2', '2', '7', '9', '4', '2', '4', '4', '0', '6', '4', '2', '4']
noncomputable def geometryRow044_floorText : String := String.ofList geometryRow044_floorChars

theorem geometryRow044_floor_text_read :
    geometryRowsJson044.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow044_floorText := by rfl

theorem geometryRow044_floor_chars_parse :
    SourceJson.intChars geometryRow044_floorChars = some (22279424406424 : Int) := by decide +kernel

theorem geometryRow044_floor_parse :
    parseInteger geometryRow044_floorText = .ok geometryRowsTyped044.jensenFloorQ96 := by
  simp only [geometryRow044_floorText, parseInteger, String.toList_ofList, geometryRow044_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_044 :
    decodeGeometryRow geometryRowsJson044 = .ok geometryRowsTyped044 :=
  original_geometryRow_of_fields geometryRowsJson044 geometryRowsTyped044 geometryRow044_floorText
    geometryRow044_simplexId_read geometryRow044_vertexIds_read
    geometryRow044_physicalVolume_read geometryRow044_meanGap_read
    geometryRow044_factorMaxima_read geometryRow044_gapWeightedMeans_read
    geometryRow044_jensenBound_read geometryRow044_floor_text_read geometryRow044_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_044_original_decoder_complete"
  err.flush

theorem geometryRow044_shape :
    geometryRowsTyped044.simplexId = 44 ∧
    geometryRowsTyped044.vertexIds.size = 9 ∧ geometryRowsTyped044.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped044.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped044.factorMaxima.size = 10 ∧ geometryRowsTyped044.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson045 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped045 : GeometryRow :=
  { simplexId := 45,
    vertexIds := #[32, 30, 28, 16, 14, 12, 11, 3, 0],
    physicalVolume := ((8627822211451055219768850665883396812641 : ℚ) / (35189813256192000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((31729387 : ℚ) / (21285000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((26247653557602194877563 : ℚ) / (291404333790246600000000 : ℚ)), ((53668265668992658910173 : ℚ) / (582808667580493200000000 : ℚ)), ((27241698325807740656429 : ℚ) / (233123467032197280000000 : ℚ)), ((11590491765600315443719 : ℚ) / (129513037240109600000000 : ℚ)), ((34560337512490500526037 : ℚ) / (388539111720328800000000 : ℚ)), ((7843757376716541341377 : ℚ) / (105965212287362400000000 : ℚ)), ((3917690334499448767541 : ℚ) / (105965212287362400000000 : ℚ)), ((3710752763659392439481 : ℚ) / (105965212287362400000000 : ℚ)), ((432688616676627667507 : ℚ) / (13245651535920300000000 : ℚ)), ((18294115594229631440831 : ℚ) / (582808667580493200000000 : ℚ))],
    jensenBound := ((1408069659937551104658687199376704822993726547954531727022890616045114338192484244113887606332751159115362111480599880019100692924702805937969403258103498859641713178853573912742182912000000000000000000000000 : ℚ) / (730250103630261348342219670762813888538282020953619823773379057625541273245000853176211283085575065128321219808003468778130972303474169839088215900675499915844878157121196581607742732552550388588839705996781553707511803 : ℚ)),
    jensenFloorQ96 := (152767895950099605 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_simplexId_before"
  err.flush

theorem geometryRow045_simplexId_read :
    geometryRowsJson045.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped045.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_vertexIds_before"
  err.flush

theorem geometryRow045_vertexIds_read :
    geometryRowsJson045.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped045.vertexIds := by decide +kernel

noncomputable def geometryRow045_physicalVolumeNumeratorChars : List Char := ['8', '6', '2', '7', '8', '2', '2', '2', '1', '1', '4', '5', '1', '0', '5', '5', '2', '1', '9', '7', '6', '8', '8', '5', '0', '6', '6', '5', '8', '8', '3', '3', '9', '6', '8', '1', '2', '6', '4', '1']
noncomputable def geometryRow045_physicalVolumeDenominatorChars : List Char := ['3', '5', '1', '8', '9', '8', '1', '3', '2', '5', '6', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_physicalVolumeText : String := String.ofList (geometryRow045_physicalVolumeNumeratorChars ++ '/' :: geometryRow045_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_physicalVolume_before_field"
  err.flush

theorem geometryRow045_physicalVolume_field :
    geometryRowsJson045.getObjVal? "physical_volume" = .ok (.str geometryRow045_physicalVolumeText) := by rfl

theorem geometryRow045_physicalVolume_numerator_no_slash :
    geometryRow045_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeNumeratorChars = some (8627822211451055219768850665883396812641 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow045_physicalVolumeDenominatorChars = some (35189813256192000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_physicalVolume_denominator_nonzero : (35189813256192000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_physicalVolume_parse :
    parseRational geometryRow045_physicalVolumeText = .ok geometryRowsTyped045.physicalVolume :=
  original_rational_fraction_of_chars geometryRow045_physicalVolumeNumeratorChars geometryRow045_physicalVolumeDenominatorChars
    (8627822211451055219768850665883396812641 : Int) (35189813256192000000000000000000000000000000000000000000000000 : Int)
    geometryRow045_physicalVolume_numerator_no_slash geometryRow045_physicalVolume_numerator_parse
    geometryRow045_physicalVolume_denominator_parse geometryRow045_physicalVolume_denominator_nonzero

theorem geometryRow045_physicalVolume_read :
    rationalField geometryRowsJson045 "physical_volume" = .ok geometryRowsTyped045.physicalVolume :=
  original_rationalField_of_string geometryRowsJson045 "physical_volume" geometryRow045_physicalVolumeText
    geometryRowsTyped045.physicalVolume geometryRow045_physicalVolume_field geometryRow045_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_physicalVolume_complete"
  err.flush

noncomputable def geometryRow045_meanGapNumeratorChars : List Char := ['3', '1', '7', '2', '9', '3', '8', '7']
noncomputable def geometryRow045_meanGapDenominatorChars : List Char := ['2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_meanGapText : String := String.ofList (geometryRow045_meanGapNumeratorChars ++ '/' :: geometryRow045_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_meanGap_before_field"
  err.flush

theorem geometryRow045_meanGap_field :
    geometryRowsJson045.getObjVal? "mean_gap" = .ok (.str geometryRow045_meanGapText) := by rfl

theorem geometryRow045_meanGap_numerator_no_slash :
    geometryRow045_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_meanGap_numerator_parse :
    SourceJson.intChars geometryRow045_meanGapNumeratorChars = some (31729387 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_parse :
    SourceJson.intChars geometryRow045_meanGapDenominatorChars = some (21285000000 : Int) := by decide +kernel

theorem geometryRow045_meanGap_denominator_nonzero : (21285000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_meanGap_parse :
    parseRational geometryRow045_meanGapText = .ok geometryRowsTyped045.meanGap :=
  original_rational_fraction_of_chars geometryRow045_meanGapNumeratorChars geometryRow045_meanGapDenominatorChars
    (31729387 : Int) (21285000000 : Int)
    geometryRow045_meanGap_numerator_no_slash geometryRow045_meanGap_numerator_parse
    geometryRow045_meanGap_denominator_parse geometryRow045_meanGap_denominator_nonzero

theorem geometryRow045_meanGap_read :
    rationalField geometryRowsJson045 "mean_gap" = .ok geometryRowsTyped045.meanGap :=
  original_rationalField_of_string geometryRowsJson045 "mean_gap" geometryRow045_meanGapText
    geometryRowsTyped045.meanGap geometryRow045_meanGap_field geometryRow045_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_meanGap_complete"
  err.flush

noncomputable def geometryRow045_jensenBoundNumeratorChars : List Char := ['1', '4', '0', '8', '0', '6', '9', '6', '5', '9', '9', '3', '7', '5', '5', '1', '1', '0', '4', '6', '5', '8', '6', '8', '7', '1', '9', '9', '3', '7', '6', '7', '0', '4', '8', '2', '2', '9', '9', '3', '7', '2', '6', '5', '4', '7', '9', '5', '4', '5', '3', '1', '7', '2', '7', '0', '2', '2', '8', '9', '0', '6', '1', '6', '0', '4', '5', '1', '1', '4', '3', '3', '8', '1', '9', '2', '4', '8', '4', '2', '4', '4', '1', '1', '3', '8', '8', '7', '6', '0', '6', '3', '3', '2', '7', '5', '1', '1', '5', '9', '1', '1', '5', '3', '6', '2', '1', '1', '1', '4', '8', '0', '5', '9', '9', '8', '8', '0', '0', '1', '9', '1', '0', '0', '6', '9', '2', '9', '2', '4', '7', '0', '2', '8', '0', '5', '9', '3', '7', '9', '6', '9', '4', '0', '3', '2', '5', '8', '1', '0', '3', '4', '9', '8', '8', '5', '9', '6', '4', '1', '7', '1', '3', '1', '7', '8', '8', '5', '3', '5', '7', '3', '9', '1', '2', '7', '4', '2', '1', '8', '2', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow045_jensenBoundDenominatorChars : List Char := ['7', '3', '0', '2', '5', '0', '1', '0', '3', '6', '3', '0', '2', '6', '1', '3', '4', '8', '3', '4', '2', '2', '1', '9', '6', '7', '0', '7', '6', '2', '8', '1', '3', '8', '8', '8', '5', '3', '8', '2', '8', '2', '0', '2', '0', '9', '5', '3', '6', '1', '9', '8', '2', '3', '7', '7', '3', '3', '7', '9', '0', '5', '7', '6', '2', '5', '5', '4', '1', '2', '7', '3', '2', '4', '5', '0', '0', '0', '8', '5', '3', '1', '7', '6', '2', '1', '1', '2', '8', '3', '0', '8', '5', '5', '7', '5', '0', '6', '5', '1', '2', '8', '3', '2', '1', '2', '1', '9', '8', '0', '8', '0', '0', '3', '4', '6', '8', '7', '7', '8', '1', '3', '0', '9', '7', '2', '3', '0', '3', '4', '7', '4', '1', '6', '9', '8', '3', '9', '0', '8', '8', '2', '1', '5', '9', '0', '0', '6', '7', '5', '4', '9', '9', '9', '1', '5', '8', '4', '4', '8', '7', '8', '1', '5', '7', '1', '2', '1', '1', '9', '6', '5', '8', '1', '6', '0', '7', '7', '4', '2', '7', '3', '2', '5', '5', '2', '5', '5', '0', '3', '8', '8', '5', '8', '8', '8', '3', '9', '7', '0', '5', '9', '9', '6', '7', '8', '1', '5', '5', '3', '7', '0', '7', '5', '1', '1', '8', '0', '3']
noncomputable def geometryRow045_jensenBoundText : String := String.ofList (geometryRow045_jensenBoundNumeratorChars ++ '/' :: geometryRow045_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_jensenBound_before_field"
  err.flush

theorem geometryRow045_jensenBound_field :
    geometryRowsJson045.getObjVal? "jensen_bound" = .ok (.str geometryRow045_jensenBoundText) := by rfl

theorem geometryRow045_jensenBound_numerator_no_slash :
    geometryRow045_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow045_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow045_jensenBoundNumeratorChars = some (1408069659937551104658687199376704822993726547954531727022890616045114338192484244113887606332751159115362111480599880019100692924702805937969403258103498859641713178853573912742182912000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow045_jensenBoundDenominatorChars = some (730250103630261348342219670762813888538282020953619823773379057625541273245000853176211283085575065128321219808003468778130972303474169839088215900675499915844878157121196581607742732552550388588839705996781553707511803 : Int) := by decide +kernel

theorem geometryRow045_jensenBound_denominator_nonzero : (730250103630261348342219670762813888538282020953619823773379057625541273245000853176211283085575065128321219808003468778130972303474169839088215900675499915844878157121196581607742732552550388588839705996781553707511803 : Int) ≠ 0 := by decide +kernel

theorem geometryRow045_jensenBound_parse :
    parseRational geometryRow045_jensenBoundText = .ok geometryRowsTyped045.jensenBound :=
  original_rational_fraction_of_chars geometryRow045_jensenBoundNumeratorChars geometryRow045_jensenBoundDenominatorChars
    (1408069659937551104658687199376704822993726547954531727022890616045114338192484244113887606332751159115362111480599880019100692924702805937969403258103498859641713178853573912742182912000000000000000000000000 : Int) (730250103630261348342219670762813888538282020953619823773379057625541273245000853176211283085575065128321219808003468778130972303474169839088215900675499915844878157121196581607742732552550388588839705996781553707511803 : Int)
    geometryRow045_jensenBound_numerator_no_slash geometryRow045_jensenBound_numerator_parse
    geometryRow045_jensenBound_denominator_parse geometryRow045_jensenBound_denominator_nonzero

theorem geometryRow045_jensenBound_read :
    rationalField geometryRowsJson045 "jensen_bound" = .ok geometryRowsTyped045.jensenBound :=
  original_rationalField_of_string geometryRowsJson045 "jensen_bound" geometryRow045_jensenBoundText
    geometryRowsTyped045.jensenBound geometryRow045_jensenBound_field geometryRow045_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_factorMaxima_before"
  err.flush

theorem geometryRow045_factorMaxima_read :
    rationalArrayField geometryRowsJson045 "factor_maxima" = .ok geometryRowsTyped045.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_gapWeightedMeans_before"
  err.flush

theorem geometryRow045_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson045 "gap_weighted_means" = .ok geometryRowsTyped045.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow045_floorChars : List Char := ['1', '5', '2', '7', '6', '7', '8', '9', '5', '9', '5', '0', '0', '9', '9', '6', '0', '5']
noncomputable def geometryRow045_floorText : String := String.ofList geometryRow045_floorChars

theorem geometryRow045_floor_text_read :
    geometryRowsJson045.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow045_floorText := by rfl

theorem geometryRow045_floor_chars_parse :
    SourceJson.intChars geometryRow045_floorChars = some (152767895950099605 : Int) := by decide +kernel

theorem geometryRow045_floor_parse :
    parseInteger geometryRow045_floorText = .ok geometryRowsTyped045.jensenFloorQ96 := by
  simp only [geometryRow045_floorText, parseInteger, String.toList_ofList, geometryRow045_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_045 :
    decodeGeometryRow geometryRowsJson045 = .ok geometryRowsTyped045 :=
  original_geometryRow_of_fields geometryRowsJson045 geometryRowsTyped045 geometryRow045_floorText
    geometryRow045_simplexId_read geometryRow045_vertexIds_read
    geometryRow045_physicalVolume_read geometryRow045_meanGap_read
    geometryRow045_factorMaxima_read geometryRow045_gapWeightedMeans_read
    geometryRow045_jensenBound_read geometryRow045_floor_text_read geometryRow045_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_045_original_decoder_complete"
  err.flush

theorem geometryRow045_shape :
    geometryRowsTyped045.simplexId = 45 ∧
    geometryRowsTyped045.vertexIds.size = 9 ∧ geometryRowsTyped045.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped045.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped045.factorMaxima.size = 10 ∧ geometryRowsTyped045.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson046 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped046 : GeometryRow :=
  { simplexId := 46,
    vertexIds := #[32, 30, 28, 16, 14, 12, 11, 8, 0],
    physicalVolume := ((4773271742404341621605502990589262223712703 : ℚ) / (4419185850777600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((38082286103651 : ℚ) / (427165200000000 : ℚ)), ((38646486288143 : ℚ) / (427165200000000 : ℚ)), ((2399933829989 : ℚ) / (20503929600000 : ℚ)), ((227694581249603 : ℚ) / (2562991200000000 : ℚ)), ((226301814686723 : ℚ) / (2562991200000000 : ℚ)), ((17524644999301 : ℚ) / (232999200000000 : ℚ)), ((2188278258227 : ℚ) / (58249800000000 : ℚ)), ((1037261631991 : ℚ) / (29124900000000 : ℚ)), ((3908551495399 : ℚ) / (116499600000000 : ℚ)), ((39536337847663 : ℚ) / (1281495600000000 : ℚ))],
    jensenBound := ((22000389954875460400041392825254206702535712440850838113755026143587456637671068455167666507807334400000000000000000000 : ℚ) / (5352776433655261192162231794715600146153995074594241599435483467550914465448827809541137024819883831928653538709122000289867309513 : ℚ)),
    jensenFloorQ96 := (325634834991937307 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_simplexId_before"
  err.flush

theorem geometryRow046_simplexId_read :
    geometryRowsJson046.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped046.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_vertexIds_before"
  err.flush

theorem geometryRow046_vertexIds_read :
    geometryRowsJson046.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped046.vertexIds := by decide +kernel

noncomputable def geometryRow046_physicalVolumeNumeratorChars : List Char := ['4', '7', '7', '3', '2', '7', '1', '7', '4', '2', '4', '0', '4', '3', '4', '1', '6', '2', '1', '6', '0', '5', '5', '0', '2', '9', '9', '0', '5', '8', '9', '2', '6', '2', '2', '2', '3', '7', '1', '2', '7', '0', '3']
noncomputable def geometryRow046_physicalVolumeDenominatorChars : List Char := ['4', '4', '1', '9', '1', '8', '5', '8', '5', '0', '7', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_physicalVolumeText : String := String.ofList (geometryRow046_physicalVolumeNumeratorChars ++ '/' :: geometryRow046_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_physicalVolume_before_field"
  err.flush

theorem geometryRow046_physicalVolume_field :
    geometryRowsJson046.getObjVal? "physical_volume" = .ok (.str geometryRow046_physicalVolumeText) := by rfl

theorem geometryRow046_physicalVolume_numerator_no_slash :
    geometryRow046_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeNumeratorChars = some (4773271742404341621605502990589262223712703 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow046_physicalVolumeDenominatorChars = some (4419185850777600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_physicalVolume_denominator_nonzero : (4419185850777600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_physicalVolume_parse :
    parseRational geometryRow046_physicalVolumeText = .ok geometryRowsTyped046.physicalVolume :=
  original_rational_fraction_of_chars geometryRow046_physicalVolumeNumeratorChars geometryRow046_physicalVolumeDenominatorChars
    (4773271742404341621605502990589262223712703 : Int) (4419185850777600000000000000000000000000000000000000000000000000 : Int)
    geometryRow046_physicalVolume_numerator_no_slash geometryRow046_physicalVolume_numerator_parse
    geometryRow046_physicalVolume_denominator_parse geometryRow046_physicalVolume_denominator_nonzero

theorem geometryRow046_physicalVolume_read :
    rationalField geometryRowsJson046 "physical_volume" = .ok geometryRowsTyped046.physicalVolume :=
  original_rationalField_of_string geometryRowsJson046 "physical_volume" geometryRow046_physicalVolumeText
    geometryRowsTyped046.physicalVolume geometryRow046_physicalVolume_field geometryRow046_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_physicalVolume_complete"
  err.flush

noncomputable def geometryRow046_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow046_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_meanGapText : String := String.ofList (geometryRow046_meanGapNumeratorChars ++ '/' :: geometryRow046_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_meanGap_before_field"
  err.flush

theorem geometryRow046_meanGap_field :
    geometryRowsJson046.getObjVal? "mean_gap" = .ok (.str geometryRow046_meanGapText) := by rfl

theorem geometryRow046_meanGap_numerator_no_slash :
    geometryRow046_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_meanGap_numerator_parse :
    SourceJson.intChars geometryRow046_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_parse :
    SourceJson.intChars geometryRow046_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow046_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_meanGap_parse :
    parseRational geometryRow046_meanGapText = .ok geometryRowsTyped046.meanGap :=
  original_rational_fraction_of_chars geometryRow046_meanGapNumeratorChars geometryRow046_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow046_meanGap_numerator_no_slash geometryRow046_meanGap_numerator_parse
    geometryRow046_meanGap_denominator_parse geometryRow046_meanGap_denominator_nonzero

theorem geometryRow046_meanGap_read :
    rationalField geometryRowsJson046 "mean_gap" = .ok geometryRowsTyped046.meanGap :=
  original_rationalField_of_string geometryRowsJson046 "mean_gap" geometryRow046_meanGapText
    geometryRowsTyped046.meanGap geometryRow046_meanGap_field geometryRow046_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_meanGap_complete"
  err.flush

noncomputable def geometryRow046_jensenBoundNumeratorChars : List Char := ['2', '2', '0', '0', '0', '3', '8', '9', '9', '5', '4', '8', '7', '5', '4', '6', '0', '4', '0', '0', '0', '4', '1', '3', '9', '2', '8', '2', '5', '2', '5', '4', '2', '0', '6', '7', '0', '2', '5', '3', '5', '7', '1', '2', '4', '4', '0', '8', '5', '0', '8', '3', '8', '1', '1', '3', '7', '5', '5', '0', '2', '6', '1', '4', '3', '5', '8', '7', '4', '5', '6', '6', '3', '7', '6', '7', '1', '0', '6', '8', '4', '5', '5', '1', '6', '7', '6', '6', '6', '5', '0', '7', '8', '0', '7', '3', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow046_jensenBoundDenominatorChars : List Char := ['5', '3', '5', '2', '7', '7', '6', '4', '3', '3', '6', '5', '5', '2', '6', '1', '1', '9', '2', '1', '6', '2', '2', '3', '1', '7', '9', '4', '7', '1', '5', '6', '0', '0', '1', '4', '6', '1', '5', '3', '9', '9', '5', '0', '7', '4', '5', '9', '4', '2', '4', '1', '5', '9', '9', '4', '3', '5', '4', '8', '3', '4', '6', '7', '5', '5', '0', '9', '1', '4', '4', '6', '5', '4', '4', '8', '8', '2', '7', '8', '0', '9', '5', '4', '1', '1', '3', '7', '0', '2', '4', '8', '1', '9', '8', '8', '3', '8', '3', '1', '9', '2', '8', '6', '5', '3', '5', '3', '8', '7', '0', '9', '1', '2', '2', '0', '0', '0', '2', '8', '9', '8', '6', '7', '3', '0', '9', '5', '1', '3']
noncomputable def geometryRow046_jensenBoundText : String := String.ofList (geometryRow046_jensenBoundNumeratorChars ++ '/' :: geometryRow046_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_jensenBound_before_field"
  err.flush

theorem geometryRow046_jensenBound_field :
    geometryRowsJson046.getObjVal? "jensen_bound" = .ok (.str geometryRow046_jensenBoundText) := by rfl

theorem geometryRow046_jensenBound_numerator_no_slash :
    geometryRow046_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow046_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow046_jensenBoundNumeratorChars = some (22000389954875460400041392825254206702535712440850838113755026143587456637671068455167666507807334400000000000000000000 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow046_jensenBoundDenominatorChars = some (5352776433655261192162231794715600146153995074594241599435483467550914465448827809541137024819883831928653538709122000289867309513 : Int) := by decide +kernel

theorem geometryRow046_jensenBound_denominator_nonzero : (5352776433655261192162231794715600146153995074594241599435483467550914465448827809541137024819883831928653538709122000289867309513 : Int) ≠ 0 := by decide +kernel

theorem geometryRow046_jensenBound_parse :
    parseRational geometryRow046_jensenBoundText = .ok geometryRowsTyped046.jensenBound :=
  original_rational_fraction_of_chars geometryRow046_jensenBoundNumeratorChars geometryRow046_jensenBoundDenominatorChars
    (22000389954875460400041392825254206702535712440850838113755026143587456637671068455167666507807334400000000000000000000 : Int) (5352776433655261192162231794715600146153995074594241599435483467550914465448827809541137024819883831928653538709122000289867309513 : Int)
    geometryRow046_jensenBound_numerator_no_slash geometryRow046_jensenBound_numerator_parse
    geometryRow046_jensenBound_denominator_parse geometryRow046_jensenBound_denominator_nonzero

theorem geometryRow046_jensenBound_read :
    rationalField geometryRowsJson046 "jensen_bound" = .ok geometryRowsTyped046.jensenBound :=
  original_rationalField_of_string geometryRowsJson046 "jensen_bound" geometryRow046_jensenBoundText
    geometryRowsTyped046.jensenBound geometryRow046_jensenBound_field geometryRow046_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_factorMaxima_before"
  err.flush

theorem geometryRow046_factorMaxima_read :
    rationalArrayField geometryRowsJson046 "factor_maxima" = .ok geometryRowsTyped046.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_gapWeightedMeans_before"
  err.flush

theorem geometryRow046_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson046 "gap_weighted_means" = .ok geometryRowsTyped046.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow046_floorChars : List Char := ['3', '2', '5', '6', '3', '4', '8', '3', '4', '9', '9', '1', '9', '3', '7', '3', '0', '7']
noncomputable def geometryRow046_floorText : String := String.ofList geometryRow046_floorChars

theorem geometryRow046_floor_text_read :
    geometryRowsJson046.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow046_floorText := by rfl

theorem geometryRow046_floor_chars_parse :
    SourceJson.intChars geometryRow046_floorChars = some (325634834991937307 : Int) := by decide +kernel

theorem geometryRow046_floor_parse :
    parseInteger geometryRow046_floorText = .ok geometryRowsTyped046.jensenFloorQ96 := by
  simp only [geometryRow046_floorText, parseInteger, String.toList_ofList, geometryRow046_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_046 :
    decodeGeometryRow geometryRowsJson046 = .ok geometryRowsTyped046 :=
  original_geometryRow_of_fields geometryRowsJson046 geometryRowsTyped046 geometryRow046_floorText
    geometryRow046_simplexId_read geometryRow046_vertexIds_read
    geometryRow046_physicalVolume_read geometryRow046_meanGap_read
    geometryRow046_factorMaxima_read geometryRow046_gapWeightedMeans_read
    geometryRow046_jensenBound_read geometryRow046_floor_text_read geometryRow046_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_046_original_decoder_complete"
  err.flush

theorem geometryRow046_shape :
    geometryRowsTyped046.simplexId = 46 ∧
    geometryRowsTyped046.vertexIds.size = 9 ∧ geometryRowsTyped046.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped046.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped046.factorMaxima.size = 10 ∧ geometryRowsTyped046.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson047 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped047 : GeometryRow :=
  { simplexId := 47,
    vertexIds := #[32, 30, 28, 16, 14, 12, 11, 7, 3],
    physicalVolume := ((165335874040104163831045197857742890636527 : ℚ) / (938395020165120000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((49290167 : ℚ) / (34056000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((16450188471863418999109 : ℚ) / (181073378783460240000000 : ℚ)), ((16804235166218350770127 : ℚ) / (181073378783460240000000 : ℚ)), ((8475183431574455306663 : ℚ) / (72429351513384096000000 : ℚ)), ((10779511813781416612171 : ℚ) / (120715585855640160000000 : ℚ)), ((3571304404975405821529 : ℚ) / (40238528618546720000000 : ℚ)), ((26791180968881350816349 : ℚ) / (362146757566920480000000 : ℚ)), ((83632977277458813517 : ℚ) / (2263417234793253000000 : ℚ)), ((3168511607111839070227 : ℚ) / (90536689391730120000000 : ℚ)), ((5799781054965016015607 : ℚ) / (181073378783460240000000 : ℚ)), ((5727146393731443810917 : ℚ) / (181073378783460240000000 : ℚ))],
    jensenBound := ((28629932978400448347669729169773825361316324887859323722154595282306936909400758615779644317391742820941864937283502515275855502676108562222374316535689804197586501569812051303950030556324986880000000000000 : ℚ) / (21268619366681228722834260832639232759126897923334807695300510614834044811047191035370044757476217916370890124500928445770744242946735552306431894250937322265854018097104134726808707309382842530364895062349568210915799 : ℚ)),
    jensenFloorQ96 := (106649940162014075 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_simplexId_before"
  err.flush

theorem geometryRow047_simplexId_read :
    geometryRowsJson047.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped047.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_vertexIds_before"
  err.flush

theorem geometryRow047_vertexIds_read :
    geometryRowsJson047.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped047.vertexIds := by decide +kernel

noncomputable def geometryRow047_physicalVolumeNumeratorChars : List Char := ['1', '6', '5', '3', '3', '5', '8', '7', '4', '0', '4', '0', '1', '0', '4', '1', '6', '3', '8', '3', '1', '0', '4', '5', '1', '9', '7', '8', '5', '7', '7', '4', '2', '8', '9', '0', '6', '3', '6', '5', '2', '7']
noncomputable def geometryRow047_physicalVolumeDenominatorChars : List Char := ['9', '3', '8', '3', '9', '5', '0', '2', '0', '1', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_physicalVolumeText : String := String.ofList (geometryRow047_physicalVolumeNumeratorChars ++ '/' :: geometryRow047_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_physicalVolume_before_field"
  err.flush

theorem geometryRow047_physicalVolume_field :
    geometryRowsJson047.getObjVal? "physical_volume" = .ok (.str geometryRow047_physicalVolumeText) := by rfl

theorem geometryRow047_physicalVolume_numerator_no_slash :
    geometryRow047_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeNumeratorChars = some (165335874040104163831045197857742890636527 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow047_physicalVolumeDenominatorChars = some (938395020165120000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow047_physicalVolume_denominator_nonzero : (938395020165120000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_physicalVolume_parse :
    parseRational geometryRow047_physicalVolumeText = .ok geometryRowsTyped047.physicalVolume :=
  original_rational_fraction_of_chars geometryRow047_physicalVolumeNumeratorChars geometryRow047_physicalVolumeDenominatorChars
    (165335874040104163831045197857742890636527 : Int) (938395020165120000000000000000000000000000000000000000000000000 : Int)
    geometryRow047_physicalVolume_numerator_no_slash geometryRow047_physicalVolume_numerator_parse
    geometryRow047_physicalVolume_denominator_parse geometryRow047_physicalVolume_denominator_nonzero

theorem geometryRow047_physicalVolume_read :
    rationalField geometryRowsJson047 "physical_volume" = .ok geometryRowsTyped047.physicalVolume :=
  original_rationalField_of_string geometryRowsJson047 "physical_volume" geometryRow047_physicalVolumeText
    geometryRowsTyped047.physicalVolume geometryRow047_physicalVolume_field geometryRow047_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_physicalVolume_complete"
  err.flush

noncomputable def geometryRow047_meanGapNumeratorChars : List Char := ['4', '9', '2', '9', '0', '1', '6', '7']
noncomputable def geometryRow047_meanGapDenominatorChars : List Char := ['3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_meanGapText : String := String.ofList (geometryRow047_meanGapNumeratorChars ++ '/' :: geometryRow047_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_meanGap_before_field"
  err.flush

theorem geometryRow047_meanGap_field :
    geometryRowsJson047.getObjVal? "mean_gap" = .ok (.str geometryRow047_meanGapText) := by rfl

theorem geometryRow047_meanGap_numerator_no_slash :
    geometryRow047_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_meanGap_numerator_parse :
    SourceJson.intChars geometryRow047_meanGapNumeratorChars = some (49290167 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_parse :
    SourceJson.intChars geometryRow047_meanGapDenominatorChars = some (34056000000 : Int) := by decide +kernel

theorem geometryRow047_meanGap_denominator_nonzero : (34056000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_meanGap_parse :
    parseRational geometryRow047_meanGapText = .ok geometryRowsTyped047.meanGap :=
  original_rational_fraction_of_chars geometryRow047_meanGapNumeratorChars geometryRow047_meanGapDenominatorChars
    (49290167 : Int) (34056000000 : Int)
    geometryRow047_meanGap_numerator_no_slash geometryRow047_meanGap_numerator_parse
    geometryRow047_meanGap_denominator_parse geometryRow047_meanGap_denominator_nonzero

theorem geometryRow047_meanGap_read :
    rationalField geometryRowsJson047 "mean_gap" = .ok geometryRowsTyped047.meanGap :=
  original_rationalField_of_string geometryRowsJson047 "mean_gap" geometryRow047_meanGapText
    geometryRowsTyped047.meanGap geometryRow047_meanGap_field geometryRow047_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_meanGap_complete"
  err.flush

noncomputable def geometryRow047_jensenBoundNumeratorChars : List Char := ['2', '8', '6', '2', '9', '9', '3', '2', '9', '7', '8', '4', '0', '0', '4', '4', '8', '3', '4', '7', '6', '6', '9', '7', '2', '9', '1', '6', '9', '7', '7', '3', '8', '2', '5', '3', '6', '1', '3', '1', '6', '3', '2', '4', '8', '8', '7', '8', '5', '9', '3', '2', '3', '7', '2', '2', '1', '5', '4', '5', '9', '5', '2', '8', '2', '3', '0', '6', '9', '3', '6', '9', '0', '9', '4', '0', '0', '7', '5', '8', '6', '1', '5', '7', '7', '9', '6', '4', '4', '3', '1', '7', '3', '9', '1', '7', '4', '2', '8', '2', '0', '9', '4', '1', '8', '6', '4', '9', '3', '7', '2', '8', '3', '5', '0', '2', '5', '1', '5', '2', '7', '5', '8', '5', '5', '5', '0', '2', '6', '7', '6', '1', '0', '8', '5', '6', '2', '2', '2', '2', '3', '7', '4', '3', '1', '6', '5', '3', '5', '6', '8', '9', '8', '0', '4', '1', '9', '7', '5', '8', '6', '5', '0', '1', '5', '6', '9', '8', '1', '2', '0', '5', '1', '3', '0', '3', '9', '5', '0', '0', '3', '0', '5', '5', '6', '3', '2', '4', '9', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow047_jensenBoundDenominatorChars : List Char := ['2', '1', '2', '6', '8', '6', '1', '9', '3', '6', '6', '6', '8', '1', '2', '2', '8', '7', '2', '2', '8', '3', '4', '2', '6', '0', '8', '3', '2', '6', '3', '9', '2', '3', '2', '7', '5', '9', '1', '2', '6', '8', '9', '7', '9', '2', '3', '3', '3', '4', '8', '0', '7', '6', '9', '5', '3', '0', '0', '5', '1', '0', '6', '1', '4', '8', '3', '4', '0', '4', '4', '8', '1', '1', '0', '4', '7', '1', '9', '1', '0', '3', '5', '3', '7', '0', '0', '4', '4', '7', '5', '7', '4', '7', '6', '2', '1', '7', '9', '1', '6', '3', '7', '0', '8', '9', '0', '1', '2', '4', '5', '0', '0', '9', '2', '8', '4', '4', '5', '7', '7', '0', '7', '4', '4', '2', '4', '2', '9', '4', '6', '7', '3', '5', '5', '5', '2', '3', '0', '6', '4', '3', '1', '8', '9', '4', '2', '5', '0', '9', '3', '7', '3', '2', '2', '2', '6', '5', '8', '5', '4', '0', '1', '8', '0', '9', '7', '1', '0', '4', '1', '3', '4', '7', '2', '6', '8', '0', '8', '7', '0', '7', '3', '0', '9', '3', '8', '2', '8', '4', '2', '5', '3', '0', '3', '6', '4', '8', '9', '5', '0', '6', '2', '3', '4', '9', '5', '6', '8', '2', '1', '0', '9', '1', '5', '7', '9', '9']
noncomputable def geometryRow047_jensenBoundText : String := String.ofList (geometryRow047_jensenBoundNumeratorChars ++ '/' :: geometryRow047_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_jensenBound_before_field"
  err.flush

theorem geometryRow047_jensenBound_field :
    geometryRowsJson047.getObjVal? "jensen_bound" = .ok (.str geometryRow047_jensenBoundText) := by rfl

theorem geometryRow047_jensenBound_numerator_no_slash :
    geometryRow047_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow047_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow047_jensenBoundNumeratorChars = some (28629932978400448347669729169773825361316324887859323722154595282306936909400758615779644317391742820941864937283502515275855502676108562222374316535689804197586501569812051303950030556324986880000000000000 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow047_jensenBoundDenominatorChars = some (21268619366681228722834260832639232759126897923334807695300510614834044811047191035370044757476217916370890124500928445770744242946735552306431894250937322265854018097104134726808707309382842530364895062349568210915799 : Int) := by decide +kernel

theorem geometryRow047_jensenBound_denominator_nonzero : (21268619366681228722834260832639232759126897923334807695300510614834044811047191035370044757476217916370890124500928445770744242946735552306431894250937322265854018097104134726808707309382842530364895062349568210915799 : Int) ≠ 0 := by decide +kernel

theorem geometryRow047_jensenBound_parse :
    parseRational geometryRow047_jensenBoundText = .ok geometryRowsTyped047.jensenBound :=
  original_rational_fraction_of_chars geometryRow047_jensenBoundNumeratorChars geometryRow047_jensenBoundDenominatorChars
    (28629932978400448347669729169773825361316324887859323722154595282306936909400758615779644317391742820941864937283502515275855502676108562222374316535689804197586501569812051303950030556324986880000000000000 : Int) (21268619366681228722834260832639232759126897923334807695300510614834044811047191035370044757476217916370890124500928445770744242946735552306431894250937322265854018097104134726808707309382842530364895062349568210915799 : Int)
    geometryRow047_jensenBound_numerator_no_slash geometryRow047_jensenBound_numerator_parse
    geometryRow047_jensenBound_denominator_parse geometryRow047_jensenBound_denominator_nonzero

theorem geometryRow047_jensenBound_read :
    rationalField geometryRowsJson047 "jensen_bound" = .ok geometryRowsTyped047.jensenBound :=
  original_rationalField_of_string geometryRowsJson047 "jensen_bound" geometryRow047_jensenBoundText
    geometryRowsTyped047.jensenBound geometryRow047_jensenBound_field geometryRow047_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_factorMaxima_before"
  err.flush

theorem geometryRow047_factorMaxima_read :
    rationalArrayField geometryRowsJson047 "factor_maxima" = .ok geometryRowsTyped047.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_gapWeightedMeans_before"
  err.flush

theorem geometryRow047_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson047 "gap_weighted_means" = .ok geometryRowsTyped047.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow047_floorChars : List Char := ['1', '0', '6', '6', '4', '9', '9', '4', '0', '1', '6', '2', '0', '1', '4', '0', '7', '5']
noncomputable def geometryRow047_floorText : String := String.ofList geometryRow047_floorChars

theorem geometryRow047_floor_text_read :
    geometryRowsJson047.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow047_floorText := by rfl

theorem geometryRow047_floor_chars_parse :
    SourceJson.intChars geometryRow047_floorChars = some (106649940162014075 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_047_original_decoder_complete"
  err.flush

theorem geometryRow047_shape :
    geometryRowsTyped047.simplexId = 47 ∧
    geometryRowsTyped047.vertexIds.size = 9 ∧ geometryRowsTyped047.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped047.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped047.factorMaxima.size = 10 ∧ geometryRowsTyped047.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock005 : List SourceJson := [geometryRowsJson040, geometryRowsJson041, geometryRowsJson042, geometryRowsJson043, geometryRowsJson044, geometryRowsJson045, geometryRowsJson046, geometryRowsJson047]
noncomputable def geometryRowsTypedBlock005 : List GeometryRow := [geometryRowsTyped040, geometryRowsTyped041, geometryRowsTyped042, geometryRowsTyped043, geometryRowsTyped044, geometryRowsTyped045, geometryRowsTyped046, geometryRowsTyped047]

theorem geometry_Rows_block_005_push_eq (acc : List SourceJson) :
    SimplicesBlock005.blockPush acc = [geometryRowsJson047, geometryRowsJson046, geometryRowsJson045, geometryRowsJson044, geometryRowsJson043, geometryRowsJson042, geometryRowsJson041, geometryRowsJson040] ++ acc := by rfl

theorem geometry_Rows_block_005_reverse (acc : List SourceJson) :
    (SimplicesBlock005.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock005 := by
  rw [geometry_Rows_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_005 :
    geometryRowsJsonBlock005.mapM decodeGeometryRow = .ok geometryRowsTypedBlock005 := by
  simp only [geometryRowsJsonBlock005, geometryRowsTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_040, decode_geometry_Rows_041, decode_geometry_Rows_042, decode_geometry_Rows_043, decode_geometry_Rows_044, decode_geometry_Rows_045, decode_geometry_Rows_046, decode_geometry_Rows_047]
  rfl

theorem geometry_Rows_block_005_length : geometryRowsTypedBlock005.length = 8 := by rfl

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
#print axioms geometryRow040_shape
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
#print axioms geometryRow041_shape
#print axioms geometryRow042_simplexId_read
#print axioms geometryRow042_vertexIds_read
#print axioms geometryRow042_physicalVolume_field
#print axioms geometryRow042_physicalVolume_numerator_no_slash
#print axioms geometryRow042_physicalVolume_numerator_parse
#print axioms geometryRow042_physicalVolume_denominator_parse
#print axioms geometryRow042_physicalVolume_denominator_nonzero
#print axioms geometryRow042_physicalVolume_parse
#print axioms geometryRow042_physicalVolume_read
#print axioms geometryRow042_meanGap_field
#print axioms geometryRow042_meanGap_numerator_no_slash
#print axioms geometryRow042_meanGap_numerator_parse
#print axioms geometryRow042_meanGap_denominator_parse
#print axioms geometryRow042_meanGap_denominator_nonzero
#print axioms geometryRow042_meanGap_parse
#print axioms geometryRow042_meanGap_read
#print axioms geometryRow042_jensenBound_field
#print axioms geometryRow042_jensenBound_numerator_no_slash
#print axioms geometryRow042_jensenBound_numerator_parse
#print axioms geometryRow042_jensenBound_denominator_parse
#print axioms geometryRow042_jensenBound_denominator_nonzero
#print axioms geometryRow042_jensenBound_parse
#print axioms geometryRow042_jensenBound_read
#print axioms geometryRow042_factorMaxima_read
#print axioms geometryRow042_gapWeightedMeans_read
#print axioms geometryRow042_floor_text_read
#print axioms geometryRow042_floor_chars_parse
#print axioms geometryRow042_floor_parse
#print axioms decode_geometry_Rows_042
#print axioms geometryRow042_shape
#print axioms geometryRow043_simplexId_read
#print axioms geometryRow043_vertexIds_read
#print axioms geometryRow043_physicalVolume_field
#print axioms geometryRow043_physicalVolume_numerator_no_slash
#print axioms geometryRow043_physicalVolume_numerator_parse
#print axioms geometryRow043_physicalVolume_denominator_parse
#print axioms geometryRow043_physicalVolume_denominator_nonzero
#print axioms geometryRow043_physicalVolume_parse
#print axioms geometryRow043_physicalVolume_read
#print axioms geometryRow043_meanGap_field
#print axioms geometryRow043_meanGap_numerator_no_slash
#print axioms geometryRow043_meanGap_numerator_parse
#print axioms geometryRow043_meanGap_denominator_parse
#print axioms geometryRow043_meanGap_denominator_nonzero
#print axioms geometryRow043_meanGap_parse
#print axioms geometryRow043_meanGap_read
#print axioms geometryRow043_jensenBound_field
#print axioms geometryRow043_jensenBound_numerator_no_slash
#print axioms geometryRow043_jensenBound_numerator_parse
#print axioms geometryRow043_jensenBound_denominator_parse
#print axioms geometryRow043_jensenBound_denominator_nonzero
#print axioms geometryRow043_jensenBound_parse
#print axioms geometryRow043_jensenBound_read
#print axioms geometryRow043_factorMaxima_read
#print axioms geometryRow043_gapWeightedMeans_read
#print axioms geometryRow043_floor_text_read
#print axioms geometryRow043_floor_chars_parse
#print axioms geometryRow043_floor_parse
#print axioms decode_geometry_Rows_043
#print axioms geometryRow043_shape
#print axioms geometryRow044_simplexId_read
#print axioms geometryRow044_vertexIds_read
#print axioms geometryRow044_physicalVolume_field
#print axioms geometryRow044_physicalVolume_numerator_no_slash
#print axioms geometryRow044_physicalVolume_numerator_parse
#print axioms geometryRow044_physicalVolume_denominator_parse
#print axioms geometryRow044_physicalVolume_denominator_nonzero
#print axioms geometryRow044_physicalVolume_parse
#print axioms geometryRow044_physicalVolume_read
#print axioms geometryRow044_meanGap_field
#print axioms geometryRow044_meanGap_numerator_no_slash
#print axioms geometryRow044_meanGap_numerator_parse
#print axioms geometryRow044_meanGap_denominator_parse
#print axioms geometryRow044_meanGap_denominator_nonzero
#print axioms geometryRow044_meanGap_parse
#print axioms geometryRow044_meanGap_read
#print axioms geometryRow044_jensenBound_field
#print axioms geometryRow044_jensenBound_numerator_no_slash
#print axioms geometryRow044_jensenBound_numerator_parse
#print axioms geometryRow044_jensenBound_denominator_parse
#print axioms geometryRow044_jensenBound_denominator_nonzero
#print axioms geometryRow044_jensenBound_parse
#print axioms geometryRow044_jensenBound_read
#print axioms geometryRow044_factorMaxima_read
#print axioms geometryRow044_gapWeightedMeans_read
#print axioms geometryRow044_floor_text_read
#print axioms geometryRow044_floor_chars_parse
#print axioms geometryRow044_floor_parse
#print axioms decode_geometry_Rows_044
#print axioms geometryRow044_shape
#print axioms geometryRow045_simplexId_read
#print axioms geometryRow045_vertexIds_read
#print axioms geometryRow045_physicalVolume_field
#print axioms geometryRow045_physicalVolume_numerator_no_slash
#print axioms geometryRow045_physicalVolume_numerator_parse
#print axioms geometryRow045_physicalVolume_denominator_parse
#print axioms geometryRow045_physicalVolume_denominator_nonzero
#print axioms geometryRow045_physicalVolume_parse
#print axioms geometryRow045_physicalVolume_read
#print axioms geometryRow045_meanGap_field
#print axioms geometryRow045_meanGap_numerator_no_slash
#print axioms geometryRow045_meanGap_numerator_parse
#print axioms geometryRow045_meanGap_denominator_parse
#print axioms geometryRow045_meanGap_denominator_nonzero
#print axioms geometryRow045_meanGap_parse
#print axioms geometryRow045_meanGap_read
#print axioms geometryRow045_jensenBound_field
#print axioms geometryRow045_jensenBound_numerator_no_slash
#print axioms geometryRow045_jensenBound_numerator_parse
#print axioms geometryRow045_jensenBound_denominator_parse
#print axioms geometryRow045_jensenBound_denominator_nonzero
#print axioms geometryRow045_jensenBound_parse
#print axioms geometryRow045_jensenBound_read
#print axioms geometryRow045_factorMaxima_read
#print axioms geometryRow045_gapWeightedMeans_read
#print axioms geometryRow045_floor_text_read
#print axioms geometryRow045_floor_chars_parse
#print axioms geometryRow045_floor_parse
#print axioms decode_geometry_Rows_045
#print axioms geometryRow045_shape
#print axioms geometryRow046_simplexId_read
#print axioms geometryRow046_vertexIds_read
#print axioms geometryRow046_physicalVolume_field
#print axioms geometryRow046_physicalVolume_numerator_no_slash
#print axioms geometryRow046_physicalVolume_numerator_parse
#print axioms geometryRow046_physicalVolume_denominator_parse
#print axioms geometryRow046_physicalVolume_denominator_nonzero
#print axioms geometryRow046_physicalVolume_parse
#print axioms geometryRow046_physicalVolume_read
#print axioms geometryRow046_meanGap_field
#print axioms geometryRow046_meanGap_numerator_no_slash
#print axioms geometryRow046_meanGap_numerator_parse
#print axioms geometryRow046_meanGap_denominator_parse
#print axioms geometryRow046_meanGap_denominator_nonzero
#print axioms geometryRow046_meanGap_parse
#print axioms geometryRow046_meanGap_read
#print axioms geometryRow046_jensenBound_field
#print axioms geometryRow046_jensenBound_numerator_no_slash
#print axioms geometryRow046_jensenBound_numerator_parse
#print axioms geometryRow046_jensenBound_denominator_parse
#print axioms geometryRow046_jensenBound_denominator_nonzero
#print axioms geometryRow046_jensenBound_parse
#print axioms geometryRow046_jensenBound_read
#print axioms geometryRow046_factorMaxima_read
#print axioms geometryRow046_gapWeightedMeans_read
#print axioms geometryRow046_floor_text_read
#print axioms geometryRow046_floor_chars_parse
#print axioms geometryRow046_floor_parse
#print axioms decode_geometry_Rows_046
#print axioms geometryRow046_shape
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
#print axioms geometryRow047_shape
#print axioms geometry_Rows_block_005_push_eq
#print axioms geometry_Rows_block_005_reverse
#print axioms decode_geometry_Rows_block_005
#print axioms geometry_Rows_block_005_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
