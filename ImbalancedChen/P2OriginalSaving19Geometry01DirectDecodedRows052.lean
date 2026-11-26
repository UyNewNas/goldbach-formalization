import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows051

/-! Original simplices typed block 52, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson102 : SourceJson :=
  (SimplicesBlock052.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped102 : GeometryRow :=
  { simplexId := 102,
    vertexIds := #[39, 37, 24, 22, 9, 7, 6, 2, 0],
    physicalVolume := ((3423562801062010206020711567687474134187 : ℚ) / (800959512084480000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((9233771 : ℚ) / (168000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((1703169 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((4656919783 : ℚ) / (53200000000 : ℚ)), ((32990243561 : ℚ) / (372400000000 : ℚ)), ((481735293469 : ℚ) / (3351600000000 : ℚ)), ((20822308447 : ℚ) / (186200000000 : ℚ)), ((185961077129 : ℚ) / (3351600000000 : ℚ)), ((163346514887 : ℚ) / (3351600000000 : ℚ)), ((27248851201 : ℚ) / (670320000000 : ℚ)), ((24887355169 : ℚ) / (670320000000 : ℚ)), ((24887310481 : ℚ) / (670320000000 : ℚ)), ((113992936063 : ℚ) / (3351600000000 : ℚ))],
    jensenBound := ((100445105262923311077447665518856527665208249235965976379930379822080000000000000000000000 : ℚ) / (6456442983184837967444272495483893211504069715254957988484314746224875599469404856283906876774615198001 : ℚ)),
    jensenFloorQ96 := (1232579788013199 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_simplexId_before"
  err.flush

theorem geometryRow102_simplexId_read :
    geometryRowsJson102.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped102.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_vertexIds_before"
  err.flush

theorem geometryRow102_vertexIds_read :
    geometryRowsJson102.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped102.vertexIds := by decide +kernel

noncomputable def geometryRow102_physicalVolumeNumeratorChars : List Char := ['3', '4', '2', '3', '5', '6', '2', '8', '0', '1', '0', '6', '2', '0', '1', '0', '2', '0', '6', '0', '2', '0', '7', '1', '1', '5', '6', '7', '6', '8', '7', '4', '7', '4', '1', '3', '4', '1', '8', '7']
noncomputable def geometryRow102_physicalVolumeDenominatorChars : List Char := ['8', '0', '0', '9', '5', '9', '5', '1', '2', '0', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow102_physicalVolumeText : String := String.ofList (geometryRow102_physicalVolumeNumeratorChars ++ '/' :: geometryRow102_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_physicalVolume_before_field"
  err.flush

theorem geometryRow102_physicalVolume_field :
    geometryRowsJson102.getObjVal? "physical_volume" = .ok (.str geometryRow102_physicalVolumeText) := by rfl

theorem geometryRow102_physicalVolume_numerator_no_slash :
    geometryRow102_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow102_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow102_physicalVolumeNumeratorChars = some (3423562801062010206020711567687474134187 : Int) := by decide +kernel

theorem geometryRow102_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow102_physicalVolumeDenominatorChars = some (800959512084480000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow102_physicalVolume_denominator_nonzero : (800959512084480000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow102_physicalVolume_parse :
    parseRational geometryRow102_physicalVolumeText = .ok geometryRowsTyped102.physicalVolume :=
  original_rational_fraction_of_chars geometryRow102_physicalVolumeNumeratorChars geometryRow102_physicalVolumeDenominatorChars
    (3423562801062010206020711567687474134187 : Int) (800959512084480000000000000000000000000000000000000000000000000 : Int)
    geometryRow102_physicalVolume_numerator_no_slash geometryRow102_physicalVolume_numerator_parse
    geometryRow102_physicalVolume_denominator_parse geometryRow102_physicalVolume_denominator_nonzero

theorem geometryRow102_physicalVolume_read :
    rationalField geometryRowsJson102 "physical_volume" = .ok geometryRowsTyped102.physicalVolume :=
  original_rationalField_of_string geometryRowsJson102 "physical_volume" geometryRow102_physicalVolumeText
    geometryRowsTyped102.physicalVolume geometryRow102_physicalVolume_field geometryRow102_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_physicalVolume_complete"
  err.flush

noncomputable def geometryRow102_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow102_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow102_meanGapText : String := String.ofList (geometryRow102_meanGapNumeratorChars ++ '/' :: geometryRow102_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_meanGap_before_field"
  err.flush

theorem geometryRow102_meanGap_field :
    geometryRowsJson102.getObjVal? "mean_gap" = .ok (.str geometryRow102_meanGapText) := by rfl

theorem geometryRow102_meanGap_numerator_no_slash :
    geometryRow102_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow102_meanGap_numerator_parse :
    SourceJson.intChars geometryRow102_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow102_meanGap_denominator_parse :
    SourceJson.intChars geometryRow102_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow102_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow102_meanGap_parse :
    parseRational geometryRow102_meanGapText = .ok geometryRowsTyped102.meanGap :=
  original_rational_fraction_of_chars geometryRow102_meanGapNumeratorChars geometryRow102_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow102_meanGap_numerator_no_slash geometryRow102_meanGap_numerator_parse
    geometryRow102_meanGap_denominator_parse geometryRow102_meanGap_denominator_nonzero

theorem geometryRow102_meanGap_read :
    rationalField geometryRowsJson102 "mean_gap" = .ok geometryRowsTyped102.meanGap :=
  original_rationalField_of_string geometryRowsJson102 "mean_gap" geometryRow102_meanGapText
    geometryRowsTyped102.meanGap geometryRow102_meanGap_field geometryRow102_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_meanGap_complete"
  err.flush

noncomputable def geometryRow102_jensenBoundNumeratorChars : List Char := ['1', '0', '0', '4', '4', '5', '1', '0', '5', '2', '6', '2', '9', '2', '3', '3', '1', '1', '0', '7', '7', '4', '4', '7', '6', '6', '5', '5', '1', '8', '8', '5', '6', '5', '2', '7', '6', '6', '5', '2', '0', '8', '2', '4', '9', '2', '3', '5', '9', '6', '5', '9', '7', '6', '3', '7', '9', '9', '3', '0', '3', '7', '9', '8', '2', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow102_jensenBoundDenominatorChars : List Char := ['6', '4', '5', '6', '4', '4', '2', '9', '8', '3', '1', '8', '4', '8', '3', '7', '9', '6', '7', '4', '4', '4', '2', '7', '2', '4', '9', '5', '4', '8', '3', '8', '9', '3', '2', '1', '1', '5', '0', '4', '0', '6', '9', '7', '1', '5', '2', '5', '4', '9', '5', '7', '9', '8', '8', '4', '8', '4', '3', '1', '4', '7', '4', '6', '2', '2', '4', '8', '7', '5', '5', '9', '9', '4', '6', '9', '4', '0', '4', '8', '5', '6', '2', '8', '3', '9', '0', '6', '8', '7', '6', '7', '7', '4', '6', '1', '5', '1', '9', '8', '0', '0', '1']
noncomputable def geometryRow102_jensenBoundText : String := String.ofList (geometryRow102_jensenBoundNumeratorChars ++ '/' :: geometryRow102_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_jensenBound_before_field"
  err.flush

theorem geometryRow102_jensenBound_field :
    geometryRowsJson102.getObjVal? "jensen_bound" = .ok (.str geometryRow102_jensenBoundText) := by rfl

theorem geometryRow102_jensenBound_numerator_no_slash :
    geometryRow102_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow102_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow102_jensenBoundNumeratorChars = some (100445105262923311077447665518856527665208249235965976379930379822080000000000000000000000 : Int) := by decide +kernel

theorem geometryRow102_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow102_jensenBoundDenominatorChars = some (6456442983184837967444272495483893211504069715254957988484314746224875599469404856283906876774615198001 : Int) := by decide +kernel

theorem geometryRow102_jensenBound_denominator_nonzero : (6456442983184837967444272495483893211504069715254957988484314746224875599469404856283906876774615198001 : Int) ≠ 0 := by decide +kernel

theorem geometryRow102_jensenBound_parse :
    parseRational geometryRow102_jensenBoundText = .ok geometryRowsTyped102.jensenBound :=
  original_rational_fraction_of_chars geometryRow102_jensenBoundNumeratorChars geometryRow102_jensenBoundDenominatorChars
    (100445105262923311077447665518856527665208249235965976379930379822080000000000000000000000 : Int) (6456442983184837967444272495483893211504069715254957988484314746224875599469404856283906876774615198001 : Int)
    geometryRow102_jensenBound_numerator_no_slash geometryRow102_jensenBound_numerator_parse
    geometryRow102_jensenBound_denominator_parse geometryRow102_jensenBound_denominator_nonzero

theorem geometryRow102_jensenBound_read :
    rationalField geometryRowsJson102 "jensen_bound" = .ok geometryRowsTyped102.jensenBound :=
  original_rationalField_of_string geometryRowsJson102 "jensen_bound" geometryRow102_jensenBoundText
    geometryRowsTyped102.jensenBound geometryRow102_jensenBound_field geometryRow102_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_factorMaxima_before"
  err.flush

theorem geometryRow102_factorMaxima_read :
    rationalArrayField geometryRowsJson102 "factor_maxima" = .ok geometryRowsTyped102.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_gapWeightedMeans_before"
  err.flush

theorem geometryRow102_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson102 "gap_weighted_means" = .ok geometryRowsTyped102.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow102_floorChars : List Char := ['1', '2', '3', '2', '5', '7', '9', '7', '8', '8', '0', '1', '3', '1', '9', '9']
noncomputable def geometryRow102_floorText : String := String.ofList geometryRow102_floorChars

theorem geometryRow102_floor_text_read :
    geometryRowsJson102.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow102_floorText := by rfl

theorem geometryRow102_floor_chars_parse :
    SourceJson.intChars geometryRow102_floorChars = some (1232579788013199 : Int) := by decide +kernel

theorem geometryRow102_floor_parse :
    parseInteger geometryRow102_floorText = .ok geometryRowsTyped102.jensenFloorQ96 := by
  simp only [geometryRow102_floorText, parseInteger, String.toList_ofList, geometryRow102_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_102 :
    decodeGeometryRow geometryRowsJson102 = .ok geometryRowsTyped102 :=
  original_geometryRow_of_fields geometryRowsJson102 geometryRowsTyped102 geometryRow102_floorText
    geometryRow102_simplexId_read geometryRow102_vertexIds_read
    geometryRow102_physicalVolume_read geometryRow102_meanGap_read
    geometryRow102_factorMaxima_read geometryRow102_gapWeightedMeans_read
    geometryRow102_jensenBound_read geometryRow102_floor_text_read geometryRow102_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_102_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson103 : SourceJson :=
  (SimplicesBlock052.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped103 : GeometryRow :=
  { simplexId := 103,
    vertexIds := #[39, 37, 24, 22, 19, 7, 6, 2, 0],
    physicalVolume := ((808194685628018471654152636017340844780581 : ℚ) / (858857442529443840000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((34630061 : ℚ) / (49039200000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((807 : ℚ) / (17792 : ℚ))],
    gapWeightedMeans := #[((21686985852973693037 : ℚ) / (256082375082800000000 : ℚ)), ((30752504426181362563 : ℚ) / (358515325115920000000 : ℚ)), ((2327453144996363017979 : ℚ) / (16133189630216400000000 : ℚ)), ((297693339559578705091 : ℚ) / (2688864938369400000000 : ℚ)), ((886961554974818671879 : ℚ) / (16133189630216400000000 : ℚ)), ((776481305037759364297 : ℚ) / (16133189630216400000000 : ℚ)), ((128879835026823089231 : ℚ) / (3226637926043280000000 : ℚ)), ((125433723453357661847 : ℚ) / (3226637926043280000000 : ℚ)), ((25086701668832518459 : ℚ) / (645327585208656000000 : ℚ)), ((576490554899788528241 : ℚ) / (16133189630216400000000 : ℚ))],
    jensenBound := ((936250687465709059089689578393762068988596965900599193632388431760855202921588715182019547190742558258612478836356845235821453770793077241547988808532571539407116032000000000000000000000 : ℚ) / (233243696043043052069469514509039502886706439515121057249262743086647233117711522174444378138537236101721428314696731542584447412548898490652928156433696962123555506388495335966486615399779874569345269 : ℚ)),
    jensenFloorQ96 := (318025408099073 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_simplexId_before"
  err.flush

theorem geometryRow103_simplexId_read :
    geometryRowsJson103.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped103.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_vertexIds_before"
  err.flush

theorem geometryRow103_vertexIds_read :
    geometryRowsJson103.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped103.vertexIds := by decide +kernel

noncomputable def geometryRow103_physicalVolumeNumeratorChars : List Char := ['8', '0', '8', '1', '9', '4', '6', '8', '5', '6', '2', '8', '0', '1', '8', '4', '7', '1', '6', '5', '4', '1', '5', '2', '6', '3', '6', '0', '1', '7', '3', '4', '0', '8', '4', '4', '7', '8', '0', '5', '8', '1']
noncomputable def geometryRow103_physicalVolumeDenominatorChars : List Char := ['8', '5', '8', '8', '5', '7', '4', '4', '2', '5', '2', '9', '4', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow103_physicalVolumeText : String := String.ofList (geometryRow103_physicalVolumeNumeratorChars ++ '/' :: geometryRow103_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_physicalVolume_before_field"
  err.flush

theorem geometryRow103_physicalVolume_field :
    geometryRowsJson103.getObjVal? "physical_volume" = .ok (.str geometryRow103_physicalVolumeText) := by rfl

theorem geometryRow103_physicalVolume_numerator_no_slash :
    geometryRow103_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow103_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow103_physicalVolumeNumeratorChars = some (808194685628018471654152636017340844780581 : Int) := by decide +kernel

theorem geometryRow103_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow103_physicalVolumeDenominatorChars = some (858857442529443840000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow103_physicalVolume_denominator_nonzero : (858857442529443840000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow103_physicalVolume_parse :
    parseRational geometryRow103_physicalVolumeText = .ok geometryRowsTyped103.physicalVolume :=
  original_rational_fraction_of_chars geometryRow103_physicalVolumeNumeratorChars geometryRow103_physicalVolumeDenominatorChars
    (808194685628018471654152636017340844780581 : Int) (858857442529443840000000000000000000000000000000000000000000000000 : Int)
    geometryRow103_physicalVolume_numerator_no_slash geometryRow103_physicalVolume_numerator_parse
    geometryRow103_physicalVolume_denominator_parse geometryRow103_physicalVolume_denominator_nonzero

theorem geometryRow103_physicalVolume_read :
    rationalField geometryRowsJson103 "physical_volume" = .ok geometryRowsTyped103.physicalVolume :=
  original_rationalField_of_string geometryRowsJson103 "physical_volume" geometryRow103_physicalVolumeText
    geometryRowsTyped103.physicalVolume geometryRow103_physicalVolume_field geometryRow103_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_physicalVolume_complete"
  err.flush

noncomputable def geometryRow103_meanGapNumeratorChars : List Char := ['3', '4', '6', '3', '0', '0', '6', '1']
noncomputable def geometryRow103_meanGapDenominatorChars : List Char := ['4', '9', '0', '3', '9', '2', '0', '0', '0', '0', '0']
noncomputable def geometryRow103_meanGapText : String := String.ofList (geometryRow103_meanGapNumeratorChars ++ '/' :: geometryRow103_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_meanGap_before_field"
  err.flush

theorem geometryRow103_meanGap_field :
    geometryRowsJson103.getObjVal? "mean_gap" = .ok (.str geometryRow103_meanGapText) := by rfl

theorem geometryRow103_meanGap_numerator_no_slash :
    geometryRow103_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow103_meanGap_numerator_parse :
    SourceJson.intChars geometryRow103_meanGapNumeratorChars = some (34630061 : Int) := by decide +kernel

theorem geometryRow103_meanGap_denominator_parse :
    SourceJson.intChars geometryRow103_meanGapDenominatorChars = some (49039200000 : Int) := by decide +kernel

theorem geometryRow103_meanGap_denominator_nonzero : (49039200000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow103_meanGap_parse :
    parseRational geometryRow103_meanGapText = .ok geometryRowsTyped103.meanGap :=
  original_rational_fraction_of_chars geometryRow103_meanGapNumeratorChars geometryRow103_meanGapDenominatorChars
    (34630061 : Int) (49039200000 : Int)
    geometryRow103_meanGap_numerator_no_slash geometryRow103_meanGap_numerator_parse
    geometryRow103_meanGap_denominator_parse geometryRow103_meanGap_denominator_nonzero

theorem geometryRow103_meanGap_read :
    rationalField geometryRowsJson103 "mean_gap" = .ok geometryRowsTyped103.meanGap :=
  original_rationalField_of_string geometryRowsJson103 "mean_gap" geometryRow103_meanGapText
    geometryRowsTyped103.meanGap geometryRow103_meanGap_field geometryRow103_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_meanGap_complete"
  err.flush

noncomputable def geometryRow103_jensenBoundNumeratorChars : List Char := ['9', '3', '6', '2', '5', '0', '6', '8', '7', '4', '6', '5', '7', '0', '9', '0', '5', '9', '0', '8', '9', '6', '8', '9', '5', '7', '8', '3', '9', '3', '7', '6', '2', '0', '6', '8', '9', '8', '8', '5', '9', '6', '9', '6', '5', '9', '0', '0', '5', '9', '9', '1', '9', '3', '6', '3', '2', '3', '8', '8', '4', '3', '1', '7', '6', '0', '8', '5', '5', '2', '0', '2', '9', '2', '1', '5', '8', '8', '7', '1', '5', '1', '8', '2', '0', '1', '9', '5', '4', '7', '1', '9', '0', '7', '4', '2', '5', '5', '8', '2', '5', '8', '6', '1', '2', '4', '7', '8', '8', '3', '6', '3', '5', '6', '8', '4', '5', '2', '3', '5', '8', '2', '1', '4', '5', '3', '7', '7', '0', '7', '9', '3', '0', '7', '7', '2', '4', '1', '5', '4', '7', '9', '8', '8', '8', '0', '8', '5', '3', '2', '5', '7', '1', '5', '3', '9', '4', '0', '7', '1', '1', '6', '0', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow103_jensenBoundDenominatorChars : List Char := ['2', '3', '3', '2', '4', '3', '6', '9', '6', '0', '4', '3', '0', '4', '3', '0', '5', '2', '0', '6', '9', '4', '6', '9', '5', '1', '4', '5', '0', '9', '0', '3', '9', '5', '0', '2', '8', '8', '6', '7', '0', '6', '4', '3', '9', '5', '1', '5', '1', '2', '1', '0', '5', '7', '2', '4', '9', '2', '6', '2', '7', '4', '3', '0', '8', '6', '6', '4', '7', '2', '3', '3', '1', '1', '7', '7', '1', '1', '5', '2', '2', '1', '7', '4', '4', '4', '4', '3', '7', '8', '1', '3', '8', '5', '3', '7', '2', '3', '6', '1', '0', '1', '7', '2', '1', '4', '2', '8', '3', '1', '4', '6', '9', '6', '7', '3', '1', '5', '4', '2', '5', '8', '4', '4', '4', '7', '4', '1', '2', '5', '4', '8', '8', '9', '8', '4', '9', '0', '6', '5', '2', '9', '2', '8', '1', '5', '6', '4', '3', '3', '6', '9', '6', '9', '6', '2', '1', '2', '3', '5', '5', '5', '5', '0', '6', '3', '8', '8', '4', '9', '5', '3', '3', '5', '9', '6', '6', '4', '8', '6', '6', '1', '5', '3', '9', '9', '7', '7', '9', '8', '7', '4', '5', '6', '9', '3', '4', '5', '2', '6', '9']
noncomputable def geometryRow103_jensenBoundText : String := String.ofList (geometryRow103_jensenBoundNumeratorChars ++ '/' :: geometryRow103_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_jensenBound_before_field"
  err.flush

theorem geometryRow103_jensenBound_field :
    geometryRowsJson103.getObjVal? "jensen_bound" = .ok (.str geometryRow103_jensenBoundText) := by rfl

theorem geometryRow103_jensenBound_numerator_no_slash :
    geometryRow103_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow103_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow103_jensenBoundNumeratorChars = some (936250687465709059089689578393762068988596965900599193632388431760855202921588715182019547190742558258612478836356845235821453770793077241547988808532571539407116032000000000000000000000 : Int) := by decide +kernel

theorem geometryRow103_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow103_jensenBoundDenominatorChars = some (233243696043043052069469514509039502886706439515121057249262743086647233117711522174444378138537236101721428314696731542584447412548898490652928156433696962123555506388495335966486615399779874569345269 : Int) := by decide +kernel

theorem geometryRow103_jensenBound_denominator_nonzero : (233243696043043052069469514509039502886706439515121057249262743086647233117711522174444378138537236101721428314696731542584447412548898490652928156433696962123555506388495335966486615399779874569345269 : Int) ≠ 0 := by decide +kernel

theorem geometryRow103_jensenBound_parse :
    parseRational geometryRow103_jensenBoundText = .ok geometryRowsTyped103.jensenBound :=
  original_rational_fraction_of_chars geometryRow103_jensenBoundNumeratorChars geometryRow103_jensenBoundDenominatorChars
    (936250687465709059089689578393762068988596965900599193632388431760855202921588715182019547190742558258612478836356845235821453770793077241547988808532571539407116032000000000000000000000 : Int) (233243696043043052069469514509039502886706439515121057249262743086647233117711522174444378138537236101721428314696731542584447412548898490652928156433696962123555506388495335966486615399779874569345269 : Int)
    geometryRow103_jensenBound_numerator_no_slash geometryRow103_jensenBound_numerator_parse
    geometryRow103_jensenBound_denominator_parse geometryRow103_jensenBound_denominator_nonzero

theorem geometryRow103_jensenBound_read :
    rationalField geometryRowsJson103 "jensen_bound" = .ok geometryRowsTyped103.jensenBound :=
  original_rationalField_of_string geometryRowsJson103 "jensen_bound" geometryRow103_jensenBoundText
    geometryRowsTyped103.jensenBound geometryRow103_jensenBound_field geometryRow103_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_factorMaxima_before"
  err.flush

theorem geometryRow103_factorMaxima_read :
    rationalArrayField geometryRowsJson103 "factor_maxima" = .ok geometryRowsTyped103.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_gapWeightedMeans_before"
  err.flush

theorem geometryRow103_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson103 "gap_weighted_means" = .ok geometryRowsTyped103.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow103_floorChars : List Char := ['3', '1', '8', '0', '2', '5', '4', '0', '8', '0', '9', '9', '0', '7', '3']
noncomputable def geometryRow103_floorText : String := String.ofList geometryRow103_floorChars

theorem geometryRow103_floor_text_read :
    geometryRowsJson103.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow103_floorText := by rfl

theorem geometryRow103_floor_chars_parse :
    SourceJson.intChars geometryRow103_floorChars = some (318025408099073 : Int) := by decide +kernel

theorem geometryRow103_floor_parse :
    parseInteger geometryRow103_floorText = .ok geometryRowsTyped103.jensenFloorQ96 := by
  simp only [geometryRow103_floorText, parseInteger, String.toList_ofList, geometryRow103_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_103 :
    decodeGeometryRow geometryRowsJson103 = .ok geometryRowsTyped103 :=
  original_geometryRow_of_fields geometryRowsJson103 geometryRowsTyped103 geometryRow103_floorText
    geometryRow103_simplexId_read geometryRow103_vertexIds_read
    geometryRow103_physicalVolume_read geometryRow103_meanGap_read
    geometryRow103_factorMaxima_read geometryRow103_gapWeightedMeans_read
    geometryRow103_jensenBound_read geometryRow103_floor_text_read geometryRow103_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_103_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock052 : List SourceJson := [geometryRowsJson102, geometryRowsJson103]
noncomputable def geometryRowsTypedBlock052 : List (GeometryRow) := [geometryRowsTyped102, geometryRowsTyped103]
noncomputable def geometryRowsTypedThroughBlock052 : List (GeometryRow) := geometryRowsTypedThroughBlock051 ++ geometryRowsTypedBlock052

theorem geometry_Rows_block_052_push_eq (acc : List SourceJson) :
    SimplicesBlock052.blockPush acc = [geometryRowsJson103, geometryRowsJson102] ++ acc := by rfl

theorem geometry_Rows_block_052_reverse (acc : List SourceJson) :
    (SimplicesBlock052.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock052 := by
  rw [geometry_Rows_block_052_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_052 :
    geometryRowsJsonBlock052.mapM decodeGeometryRow = .ok geometryRowsTypedBlock052 := by
  simp only [geometryRowsJsonBlock052, geometryRowsTypedBlock052, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_102, decode_geometry_Rows_103]
  rfl

theorem decode_geometry_Rows_through_block_052 :
    SimplicesValue.arrayAcc053.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock052 := by
  change (SimplicesBlock052.blockPush SimplicesValue.arrayAcc052).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_052_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_051, decode_geometry_Rows_block_052]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_052_complete"
  err.flush

#print axioms geometryRow102_simplexId_read
#print axioms geometryRow102_vertexIds_read
#print axioms geometryRow102_physicalVolume_field
#print axioms geometryRow102_physicalVolume_numerator_no_slash
#print axioms geometryRow102_physicalVolume_numerator_parse
#print axioms geometryRow102_physicalVolume_denominator_parse
#print axioms geometryRow102_physicalVolume_denominator_nonzero
#print axioms geometryRow102_physicalVolume_parse
#print axioms geometryRow102_physicalVolume_read
#print axioms geometryRow102_meanGap_field
#print axioms geometryRow102_meanGap_numerator_no_slash
#print axioms geometryRow102_meanGap_numerator_parse
#print axioms geometryRow102_meanGap_denominator_parse
#print axioms geometryRow102_meanGap_denominator_nonzero
#print axioms geometryRow102_meanGap_parse
#print axioms geometryRow102_meanGap_read
#print axioms geometryRow102_jensenBound_field
#print axioms geometryRow102_jensenBound_numerator_no_slash
#print axioms geometryRow102_jensenBound_numerator_parse
#print axioms geometryRow102_jensenBound_denominator_parse
#print axioms geometryRow102_jensenBound_denominator_nonzero
#print axioms geometryRow102_jensenBound_parse
#print axioms geometryRow102_jensenBound_read
#print axioms geometryRow102_factorMaxima_read
#print axioms geometryRow102_gapWeightedMeans_read
#print axioms geometryRow102_floor_text_read
#print axioms geometryRow102_floor_chars_parse
#print axioms geometryRow102_floor_parse
#print axioms decode_geometry_Rows_102
#print axioms geometryRow103_simplexId_read
#print axioms geometryRow103_vertexIds_read
#print axioms geometryRow103_physicalVolume_field
#print axioms geometryRow103_physicalVolume_numerator_no_slash
#print axioms geometryRow103_physicalVolume_numerator_parse
#print axioms geometryRow103_physicalVolume_denominator_parse
#print axioms geometryRow103_physicalVolume_denominator_nonzero
#print axioms geometryRow103_physicalVolume_parse
#print axioms geometryRow103_physicalVolume_read
#print axioms geometryRow103_meanGap_field
#print axioms geometryRow103_meanGap_numerator_no_slash
#print axioms geometryRow103_meanGap_numerator_parse
#print axioms geometryRow103_meanGap_denominator_parse
#print axioms geometryRow103_meanGap_denominator_nonzero
#print axioms geometryRow103_meanGap_parse
#print axioms geometryRow103_meanGap_read
#print axioms geometryRow103_jensenBound_field
#print axioms geometryRow103_jensenBound_numerator_no_slash
#print axioms geometryRow103_jensenBound_numerator_parse
#print axioms geometryRow103_jensenBound_denominator_parse
#print axioms geometryRow103_jensenBound_denominator_nonzero
#print axioms geometryRow103_jensenBound_parse
#print axioms geometryRow103_jensenBound_read
#print axioms geometryRow103_factorMaxima_read
#print axioms geometryRow103_gapWeightedMeans_read
#print axioms geometryRow103_floor_text_read
#print axioms geometryRow103_floor_chars_parse
#print axioms geometryRow103_floor_parse
#print axioms decode_geometry_Rows_103
#print axioms geometry_Rows_block_052_push_eq
#print axioms geometry_Rows_block_052_reverse
#print axioms decode_geometry_Rows_block_052
#print axioms decode_geometry_Rows_through_block_052

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
