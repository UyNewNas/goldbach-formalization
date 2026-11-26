import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows043

/-! Original simplices typed block 44, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson087 : SourceJson :=
  (SimplicesBlock044.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped087 : GeometryRow :=
  { simplexId := 87,
    vertexIds := #[39, 37, 24, 23, 21, 8, 3, 2, 0],
    physicalVolume := ((22798993409788730487576067625677353121441313 : ℚ) / (28215344068853760000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((88491047107602752017 : ℚ) / (1017415973371200000000 : ℚ)), ((4413205348947464033023 : ℚ) / (49853382695188800000000 : ℚ)), ((183985897868478474973 : ℚ) / (1278291863979200000000 : ℚ)), ((8280771846860296906307 : ℚ) / (74780074042783200000000 : ℚ)), ((54383533382651826107 : ℚ) / (977517307748800000000 : ℚ)), ((789248129657787483347 : ℚ) / (16617794231729600000000 : ℚ)), ((61681835384529987421 : ℚ) / (1574317348269120000000 : ℚ)), ((1155982819319562702103 : ℚ) / (29912029617113280000000 : ℚ)), ((5507216028567941472857 : ℚ) / (149560148085566400000000 : ℚ)), ((5427969721237133997167 : ℚ) / (149560148085566400000000 : ℚ))],
    jensenBound := ((10597056308592318970693468904464941542526448341086235940541109740399478297235659746743849247252325936961666659585432077811042893946617436986410865562076714272195325749048115200000000000000000000000 : ℚ) / (1877024781603368478103167713645921350413878357879673675008855749054834575696522375164425156583211413889803980576206086532136238299115817915019338774798274972234609608669866125829832774395961796738498994387497 : ℚ)),
    jensenFloorQ96 := (447295798978627441 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_simplexId_before"
  err.flush

theorem geometryRow087_simplexId_read :
    geometryRowsJson087.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped087.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_vertexIds_before"
  err.flush

theorem geometryRow087_vertexIds_read :
    geometryRowsJson087.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped087.vertexIds := by decide +kernel

noncomputable def geometryRow087_physicalVolumeNumeratorChars : List Char := ['2', '2', '7', '9', '8', '9', '9', '3', '4', '0', '9', '7', '8', '8', '7', '3', '0', '4', '8', '7', '5', '7', '6', '0', '6', '7', '6', '2', '5', '6', '7', '7', '3', '5', '3', '1', '2', '1', '4', '4', '1', '3', '1', '3']
noncomputable def geometryRow087_physicalVolumeDenominatorChars : List Char := ['2', '8', '2', '1', '5', '3', '4', '4', '0', '6', '8', '8', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow087_physicalVolumeText : String := String.ofList (geometryRow087_physicalVolumeNumeratorChars ++ '/' :: geometryRow087_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_physicalVolume_before_field"
  err.flush

theorem geometryRow087_physicalVolume_field :
    geometryRowsJson087.getObjVal? "physical_volume" = .ok (.str geometryRow087_physicalVolumeText) := by rfl

theorem geometryRow087_physicalVolume_numerator_no_slash :
    geometryRow087_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow087_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow087_physicalVolumeNumeratorChars = some (22798993409788730487576067625677353121441313 : Int) := by decide +kernel

theorem geometryRow087_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow087_physicalVolumeDenominatorChars = some (28215344068853760000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow087_physicalVolume_denominator_nonzero : (28215344068853760000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow087_physicalVolume_parse :
    parseRational geometryRow087_physicalVolumeText = .ok geometryRowsTyped087.physicalVolume :=
  original_rational_fraction_of_chars geometryRow087_physicalVolumeNumeratorChars geometryRow087_physicalVolumeDenominatorChars
    (22798993409788730487576067625677353121441313 : Int) (28215344068853760000000000000000000000000000000000000000000000000 : Int)
    geometryRow087_physicalVolume_numerator_no_slash geometryRow087_physicalVolume_numerator_parse
    geometryRow087_physicalVolume_denominator_parse geometryRow087_physicalVolume_denominator_nonzero

theorem geometryRow087_physicalVolume_read :
    rationalField geometryRowsJson087 "physical_volume" = .ok geometryRowsTyped087.physicalVolume :=
  original_rationalField_of_string geometryRowsJson087 "physical_volume" geometryRow087_physicalVolumeText
    geometryRowsTyped087.physicalVolume geometryRow087_physicalVolume_field geometryRow087_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_physicalVolume_complete"
  err.flush

noncomputable def geometryRow087_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow087_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow087_meanGapText : String := String.ofList (geometryRow087_meanGapNumeratorChars ++ '/' :: geometryRow087_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_meanGap_before_field"
  err.flush

theorem geometryRow087_meanGap_field :
    geometryRowsJson087.getObjVal? "mean_gap" = .ok (.str geometryRow087_meanGapText) := by rfl

theorem geometryRow087_meanGap_numerator_no_slash :
    geometryRow087_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow087_meanGap_numerator_parse :
    SourceJson.intChars geometryRow087_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow087_meanGap_denominator_parse :
    SourceJson.intChars geometryRow087_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow087_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow087_meanGap_parse :
    parseRational geometryRow087_meanGapText = .ok geometryRowsTyped087.meanGap :=
  original_rational_fraction_of_chars geometryRow087_meanGapNumeratorChars geometryRow087_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow087_meanGap_numerator_no_slash geometryRow087_meanGap_numerator_parse
    geometryRow087_meanGap_denominator_parse geometryRow087_meanGap_denominator_nonzero

theorem geometryRow087_meanGap_read :
    rationalField geometryRowsJson087 "mean_gap" = .ok geometryRowsTyped087.meanGap :=
  original_rationalField_of_string geometryRowsJson087 "mean_gap" geometryRow087_meanGapText
    geometryRowsTyped087.meanGap geometryRow087_meanGap_field geometryRow087_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_meanGap_complete"
  err.flush

noncomputable def geometryRow087_jensenBoundNumeratorChars : List Char := ['1', '0', '5', '9', '7', '0', '5', '6', '3', '0', '8', '5', '9', '2', '3', '1', '8', '9', '7', '0', '6', '9', '3', '4', '6', '8', '9', '0', '4', '4', '6', '4', '9', '4', '1', '5', '4', '2', '5', '2', '6', '4', '4', '8', '3', '4', '1', '0', '8', '6', '2', '3', '5', '9', '4', '0', '5', '4', '1', '1', '0', '9', '7', '4', '0', '3', '9', '9', '4', '7', '8', '2', '9', '7', '2', '3', '5', '6', '5', '9', '7', '4', '6', '7', '4', '3', '8', '4', '9', '2', '4', '7', '2', '5', '2', '3', '2', '5', '9', '3', '6', '9', '6', '1', '6', '6', '6', '6', '5', '9', '5', '8', '5', '4', '3', '2', '0', '7', '7', '8', '1', '1', '0', '4', '2', '8', '9', '3', '9', '4', '6', '6', '1', '7', '4', '3', '6', '9', '8', '6', '4', '1', '0', '8', '6', '5', '5', '6', '2', '0', '7', '6', '7', '1', '4', '2', '7', '2', '1', '9', '5', '3', '2', '5', '7', '4', '9', '0', '4', '8', '1', '1', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow087_jensenBoundDenominatorChars : List Char := ['1', '8', '7', '7', '0', '2', '4', '7', '8', '1', '6', '0', '3', '3', '6', '8', '4', '7', '8', '1', '0', '3', '1', '6', '7', '7', '1', '3', '6', '4', '5', '9', '2', '1', '3', '5', '0', '4', '1', '3', '8', '7', '8', '3', '5', '7', '8', '7', '9', '6', '7', '3', '6', '7', '5', '0', '0', '8', '8', '5', '5', '7', '4', '9', '0', '5', '4', '8', '3', '4', '5', '7', '5', '6', '9', '6', '5', '2', '2', '3', '7', '5', '1', '6', '4', '4', '2', '5', '1', '5', '6', '5', '8', '3', '2', '1', '1', '4', '1', '3', '8', '8', '9', '8', '0', '3', '9', '8', '0', '5', '7', '6', '2', '0', '6', '0', '8', '6', '5', '3', '2', '1', '3', '6', '2', '3', '8', '2', '9', '9', '1', '1', '5', '8', '1', '7', '9', '1', '5', '0', '1', '9', '3', '3', '8', '7', '7', '4', '7', '9', '8', '2', '7', '4', '9', '7', '2', '2', '3', '4', '6', '0', '9', '6', '0', '8', '6', '6', '9', '8', '6', '6', '1', '2', '5', '8', '2', '9', '8', '3', '2', '7', '7', '4', '3', '9', '5', '9', '6', '1', '7', '9', '6', '7', '3', '8', '4', '9', '8', '9', '9', '4', '3', '8', '7', '4', '9', '7']
noncomputable def geometryRow087_jensenBoundText : String := String.ofList (geometryRow087_jensenBoundNumeratorChars ++ '/' :: geometryRow087_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_jensenBound_before_field"
  err.flush

theorem geometryRow087_jensenBound_field :
    geometryRowsJson087.getObjVal? "jensen_bound" = .ok (.str geometryRow087_jensenBoundText) := by rfl

theorem geometryRow087_jensenBound_numerator_no_slash :
    geometryRow087_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow087_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow087_jensenBoundNumeratorChars = some (10597056308592318970693468904464941542526448341086235940541109740399478297235659746743849247252325936961666659585432077811042893946617436986410865562076714272195325749048115200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow087_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow087_jensenBoundDenominatorChars = some (1877024781603368478103167713645921350413878357879673675008855749054834575696522375164425156583211413889803980576206086532136238299115817915019338774798274972234609608669866125829832774395961796738498994387497 : Int) := by decide +kernel

theorem geometryRow087_jensenBound_denominator_nonzero : (1877024781603368478103167713645921350413878357879673675008855749054834575696522375164425156583211413889803980576206086532136238299115817915019338774798274972234609608669866125829832774395961796738498994387497 : Int) ≠ 0 := by decide +kernel

theorem geometryRow087_jensenBound_parse :
    parseRational geometryRow087_jensenBoundText = .ok geometryRowsTyped087.jensenBound :=
  original_rational_fraction_of_chars geometryRow087_jensenBoundNumeratorChars geometryRow087_jensenBoundDenominatorChars
    (10597056308592318970693468904464941542526448341086235940541109740399478297235659746743849247252325936961666659585432077811042893946617436986410865562076714272195325749048115200000000000000000000000 : Int) (1877024781603368478103167713645921350413878357879673675008855749054834575696522375164425156583211413889803980576206086532136238299115817915019338774798274972234609608669866125829832774395961796738498994387497 : Int)
    geometryRow087_jensenBound_numerator_no_slash geometryRow087_jensenBound_numerator_parse
    geometryRow087_jensenBound_denominator_parse geometryRow087_jensenBound_denominator_nonzero

theorem geometryRow087_jensenBound_read :
    rationalField geometryRowsJson087 "jensen_bound" = .ok geometryRowsTyped087.jensenBound :=
  original_rationalField_of_string geometryRowsJson087 "jensen_bound" geometryRow087_jensenBoundText
    geometryRowsTyped087.jensenBound geometryRow087_jensenBound_field geometryRow087_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_factorMaxima_before"
  err.flush

theorem geometryRow087_factorMaxima_read :
    rationalArrayField geometryRowsJson087 "factor_maxima" = .ok geometryRowsTyped087.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_gapWeightedMeans_before"
  err.flush

theorem geometryRow087_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson087 "gap_weighted_means" = .ok geometryRowsTyped087.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow087_floorChars : List Char := ['4', '4', '7', '2', '9', '5', '7', '9', '8', '9', '7', '8', '6', '2', '7', '4', '4', '1']
noncomputable def geometryRow087_floorText : String := String.ofList geometryRow087_floorChars

theorem geometryRow087_floor_text_read :
    geometryRowsJson087.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow087_floorText := by rfl

theorem geometryRow087_floor_chars_parse :
    SourceJson.intChars geometryRow087_floorChars = some (447295798978627441 : Int) := by decide +kernel

theorem geometryRow087_floor_parse :
    parseInteger geometryRow087_floorText = .ok geometryRowsTyped087.jensenFloorQ96 := by
  simp only [geometryRow087_floorText, parseInteger, String.toList_ofList, geometryRow087_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_087 :
    decodeGeometryRow geometryRowsJson087 = .ok geometryRowsTyped087 :=
  original_geometryRow_of_fields geometryRowsJson087 geometryRowsTyped087 geometryRow087_floorText
    geometryRow087_simplexId_read geometryRow087_vertexIds_read
    geometryRow087_physicalVolume_read geometryRow087_meanGap_read
    geometryRow087_factorMaxima_read geometryRow087_gapWeightedMeans_read
    geometryRow087_jensenBound_read geometryRow087_floor_text_read geometryRow087_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_087_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson088 : SourceJson :=
  (SimplicesBlock044.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped088 : GeometryRow :=
  { simplexId := 88,
    vertexIds := #[39, 37, 24, 23, 21, 8, 6, 2, 0],
    physicalVolume := ((4398277472279798703633737292438972464142605371 : ℚ) / (1867969883528985600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((843210968683 : ℚ) / (9751560000000 : ℚ)), ((1194858930389 : ℚ) / (13652184000000 : ℚ)), ((3786023127431 : ℚ) / (26254200000000 : ℚ)), ((56496382988653 : ℚ) / (511956900000000 : ℚ)), ((2358171813301 : ℚ) / (42663075000000 : ℚ)), ((16202745889639 : ℚ) / (341304600000000 : ℚ)), ((21285407191 : ℚ) / (538902000000 : ℚ)), ((3989553692599 : ℚ) / (102391380000000 : ℚ)), ((38542758428479 : ℚ) / (1023913800000000 : ℚ)), ((36818719955023 : ℚ) / (1023913800000000 : ℚ))],
    jensenBound := ((321832488000918284942936086836457956212264597472495761390794609265119395517470027107758984692000000000000000000 : ℚ) / (38486211315518500813395536439647052647085686928751645035966610250829162370370059763395777827052721328546559299634245298609 : ℚ)),
    jensenFloorQ96 := (662528105265205420 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_simplexId_before"
  err.flush

theorem geometryRow088_simplexId_read :
    geometryRowsJson088.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped088.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_vertexIds_before"
  err.flush

theorem geometryRow088_vertexIds_read :
    geometryRowsJson088.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped088.vertexIds := by decide +kernel

noncomputable def geometryRow088_physicalVolumeNumeratorChars : List Char := ['4', '3', '9', '8', '2', '7', '7', '4', '7', '2', '2', '7', '9', '7', '9', '8', '7', '0', '3', '6', '3', '3', '7', '3', '7', '2', '9', '2', '4', '3', '8', '9', '7', '2', '4', '6', '4', '1', '4', '2', '6', '0', '5', '3', '7', '1']
noncomputable def geometryRow088_physicalVolumeDenominatorChars : List Char := ['1', '8', '6', '7', '9', '6', '9', '8', '8', '3', '5', '2', '8', '9', '8', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow088_physicalVolumeText : String := String.ofList (geometryRow088_physicalVolumeNumeratorChars ++ '/' :: geometryRow088_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_physicalVolume_before_field"
  err.flush

theorem geometryRow088_physicalVolume_field :
    geometryRowsJson088.getObjVal? "physical_volume" = .ok (.str geometryRow088_physicalVolumeText) := by rfl

theorem geometryRow088_physicalVolume_numerator_no_slash :
    geometryRow088_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow088_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow088_physicalVolumeNumeratorChars = some (4398277472279798703633737292438972464142605371 : Int) := by decide +kernel

theorem geometryRow088_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow088_physicalVolumeDenominatorChars = some (1867969883528985600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow088_physicalVolume_denominator_nonzero : (1867969883528985600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow088_physicalVolume_parse :
    parseRational geometryRow088_physicalVolumeText = .ok geometryRowsTyped088.physicalVolume :=
  original_rational_fraction_of_chars geometryRow088_physicalVolumeNumeratorChars geometryRow088_physicalVolumeDenominatorChars
    (4398277472279798703633737292438972464142605371 : Int) (1867969883528985600000000000000000000000000000000000000000000000000 : Int)
    geometryRow088_physicalVolume_numerator_no_slash geometryRow088_physicalVolume_numerator_parse
    geometryRow088_physicalVolume_denominator_parse geometryRow088_physicalVolume_denominator_nonzero

theorem geometryRow088_physicalVolume_read :
    rationalField geometryRowsJson088 "physical_volume" = .ok geometryRowsTyped088.physicalVolume :=
  original_rationalField_of_string geometryRowsJson088 "physical_volume" geometryRow088_physicalVolumeText
    geometryRowsTyped088.physicalVolume geometryRow088_physicalVolume_field geometryRow088_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_physicalVolume_complete"
  err.flush

noncomputable def geometryRow088_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow088_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow088_meanGapText : String := String.ofList (geometryRow088_meanGapNumeratorChars ++ '/' :: geometryRow088_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_meanGap_before_field"
  err.flush

theorem geometryRow088_meanGap_field :
    geometryRowsJson088.getObjVal? "mean_gap" = .ok (.str geometryRow088_meanGapText) := by rfl

theorem geometryRow088_meanGap_numerator_no_slash :
    geometryRow088_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow088_meanGap_numerator_parse :
    SourceJson.intChars geometryRow088_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow088_meanGap_denominator_parse :
    SourceJson.intChars geometryRow088_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow088_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow088_meanGap_parse :
    parseRational geometryRow088_meanGapText = .ok geometryRowsTyped088.meanGap :=
  original_rational_fraction_of_chars geometryRow088_meanGapNumeratorChars geometryRow088_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow088_meanGap_numerator_no_slash geometryRow088_meanGap_numerator_parse
    geometryRow088_meanGap_denominator_parse geometryRow088_meanGap_denominator_nonzero

theorem geometryRow088_meanGap_read :
    rationalField geometryRowsJson088 "mean_gap" = .ok geometryRowsTyped088.meanGap :=
  original_rationalField_of_string geometryRowsJson088 "mean_gap" geometryRow088_meanGapText
    geometryRowsTyped088.meanGap geometryRow088_meanGap_field geometryRow088_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_meanGap_complete"
  err.flush

noncomputable def geometryRow088_jensenBoundNumeratorChars : List Char := ['3', '2', '1', '8', '3', '2', '4', '8', '8', '0', '0', '0', '9', '1', '8', '2', '8', '4', '9', '4', '2', '9', '3', '6', '0', '8', '6', '8', '3', '6', '4', '5', '7', '9', '5', '6', '2', '1', '2', '2', '6', '4', '5', '9', '7', '4', '7', '2', '4', '9', '5', '7', '6', '1', '3', '9', '0', '7', '9', '4', '6', '0', '9', '2', '6', '5', '1', '1', '9', '3', '9', '5', '5', '1', '7', '4', '7', '0', '0', '2', '7', '1', '0', '7', '7', '5', '8', '9', '8', '4', '6', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow088_jensenBoundDenominatorChars : List Char := ['3', '8', '4', '8', '6', '2', '1', '1', '3', '1', '5', '5', '1', '8', '5', '0', '0', '8', '1', '3', '3', '9', '5', '5', '3', '6', '4', '3', '9', '6', '4', '7', '0', '5', '2', '6', '4', '7', '0', '8', '5', '6', '8', '6', '9', '2', '8', '7', '5', '1', '6', '4', '5', '0', '3', '5', '9', '6', '6', '6', '1', '0', '2', '5', '0', '8', '2', '9', '1', '6', '2', '3', '7', '0', '3', '7', '0', '0', '5', '9', '7', '6', '3', '3', '9', '5', '7', '7', '7', '8', '2', '7', '0', '5', '2', '7', '2', '1', '3', '2', '8', '5', '4', '6', '5', '5', '9', '2', '9', '9', '6', '3', '4', '2', '4', '5', '2', '9', '8', '6', '0', '9']
noncomputable def geometryRow088_jensenBoundText : String := String.ofList (geometryRow088_jensenBoundNumeratorChars ++ '/' :: geometryRow088_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_jensenBound_before_field"
  err.flush

theorem geometryRow088_jensenBound_field :
    geometryRowsJson088.getObjVal? "jensen_bound" = .ok (.str geometryRow088_jensenBoundText) := by rfl

theorem geometryRow088_jensenBound_numerator_no_slash :
    geometryRow088_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow088_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow088_jensenBoundNumeratorChars = some (321832488000918284942936086836457956212264597472495761390794609265119395517470027107758984692000000000000000000 : Int) := by decide +kernel

theorem geometryRow088_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow088_jensenBoundDenominatorChars = some (38486211315518500813395536439647052647085686928751645035966610250829162370370059763395777827052721328546559299634245298609 : Int) := by decide +kernel

theorem geometryRow088_jensenBound_denominator_nonzero : (38486211315518500813395536439647052647085686928751645035966610250829162370370059763395777827052721328546559299634245298609 : Int) ≠ 0 := by decide +kernel

theorem geometryRow088_jensenBound_parse :
    parseRational geometryRow088_jensenBoundText = .ok geometryRowsTyped088.jensenBound :=
  original_rational_fraction_of_chars geometryRow088_jensenBoundNumeratorChars geometryRow088_jensenBoundDenominatorChars
    (321832488000918284942936086836457956212264597472495761390794609265119395517470027107758984692000000000000000000 : Int) (38486211315518500813395536439647052647085686928751645035966610250829162370370059763395777827052721328546559299634245298609 : Int)
    geometryRow088_jensenBound_numerator_no_slash geometryRow088_jensenBound_numerator_parse
    geometryRow088_jensenBound_denominator_parse geometryRow088_jensenBound_denominator_nonzero

theorem geometryRow088_jensenBound_read :
    rationalField geometryRowsJson088 "jensen_bound" = .ok geometryRowsTyped088.jensenBound :=
  original_rationalField_of_string geometryRowsJson088 "jensen_bound" geometryRow088_jensenBoundText
    geometryRowsTyped088.jensenBound geometryRow088_jensenBound_field geometryRow088_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_factorMaxima_before"
  err.flush

theorem geometryRow088_factorMaxima_read :
    rationalArrayField geometryRowsJson088 "factor_maxima" = .ok geometryRowsTyped088.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_gapWeightedMeans_before"
  err.flush

theorem geometryRow088_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson088 "gap_weighted_means" = .ok geometryRowsTyped088.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow088_floorChars : List Char := ['6', '6', '2', '5', '2', '8', '1', '0', '5', '2', '6', '5', '2', '0', '5', '4', '2', '0']
noncomputable def geometryRow088_floorText : String := String.ofList geometryRow088_floorChars

theorem geometryRow088_floor_text_read :
    geometryRowsJson088.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow088_floorText := by rfl

theorem geometryRow088_floor_chars_parse :
    SourceJson.intChars geometryRow088_floorChars = some (662528105265205420 : Int) := by decide +kernel

theorem geometryRow088_floor_parse :
    parseInteger geometryRow088_floorText = .ok geometryRowsTyped088.jensenFloorQ96 := by
  simp only [geometryRow088_floorText, parseInteger, String.toList_ofList, geometryRow088_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_088 :
    decodeGeometryRow geometryRowsJson088 = .ok geometryRowsTyped088 :=
  original_geometryRow_of_fields geometryRowsJson088 geometryRowsTyped088 geometryRow088_floorText
    geometryRow088_simplexId_read geometryRow088_vertexIds_read
    geometryRow088_physicalVolume_read geometryRow088_meanGap_read
    geometryRow088_factorMaxima_read geometryRow088_gapWeightedMeans_read
    geometryRow088_jensenBound_read geometryRow088_floor_text_read geometryRow088_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_088_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock044 : List SourceJson := [geometryRowsJson087, geometryRowsJson088]
noncomputable def geometryRowsTypedBlock044 : List (GeometryRow) := [geometryRowsTyped087, geometryRowsTyped088]
noncomputable def geometryRowsTypedThroughBlock044 : List (GeometryRow) := geometryRowsTypedThroughBlock043 ++ geometryRowsTypedBlock044

theorem geometry_Rows_block_044_push_eq (acc : List SourceJson) :
    SimplicesBlock044.blockPush acc = [geometryRowsJson088, geometryRowsJson087] ++ acc := by rfl

theorem geometry_Rows_block_044_reverse (acc : List SourceJson) :
    (SimplicesBlock044.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock044 := by
  rw [geometry_Rows_block_044_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_044 :
    geometryRowsJsonBlock044.mapM decodeGeometryRow = .ok geometryRowsTypedBlock044 := by
  simp only [geometryRowsJsonBlock044, geometryRowsTypedBlock044, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_087, decode_geometry_Rows_088]
  rfl

theorem decode_geometry_Rows_through_block_044 :
    SimplicesValue.arrayAcc045.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock044 := by
  change (SimplicesBlock044.blockPush SimplicesValue.arrayAcc044).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_044_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_043, decode_geometry_Rows_block_044]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_044_complete"
  err.flush

#print axioms geometryRow087_simplexId_read
#print axioms geometryRow087_vertexIds_read
#print axioms geometryRow087_physicalVolume_field
#print axioms geometryRow087_physicalVolume_numerator_no_slash
#print axioms geometryRow087_physicalVolume_numerator_parse
#print axioms geometryRow087_physicalVolume_denominator_parse
#print axioms geometryRow087_physicalVolume_denominator_nonzero
#print axioms geometryRow087_physicalVolume_parse
#print axioms geometryRow087_physicalVolume_read
#print axioms geometryRow087_meanGap_field
#print axioms geometryRow087_meanGap_numerator_no_slash
#print axioms geometryRow087_meanGap_numerator_parse
#print axioms geometryRow087_meanGap_denominator_parse
#print axioms geometryRow087_meanGap_denominator_nonzero
#print axioms geometryRow087_meanGap_parse
#print axioms geometryRow087_meanGap_read
#print axioms geometryRow087_jensenBound_field
#print axioms geometryRow087_jensenBound_numerator_no_slash
#print axioms geometryRow087_jensenBound_numerator_parse
#print axioms geometryRow087_jensenBound_denominator_parse
#print axioms geometryRow087_jensenBound_denominator_nonzero
#print axioms geometryRow087_jensenBound_parse
#print axioms geometryRow087_jensenBound_read
#print axioms geometryRow087_factorMaxima_read
#print axioms geometryRow087_gapWeightedMeans_read
#print axioms geometryRow087_floor_text_read
#print axioms geometryRow087_floor_chars_parse
#print axioms geometryRow087_floor_parse
#print axioms decode_geometry_Rows_087
#print axioms geometryRow088_simplexId_read
#print axioms geometryRow088_vertexIds_read
#print axioms geometryRow088_physicalVolume_field
#print axioms geometryRow088_physicalVolume_numerator_no_slash
#print axioms geometryRow088_physicalVolume_numerator_parse
#print axioms geometryRow088_physicalVolume_denominator_parse
#print axioms geometryRow088_physicalVolume_denominator_nonzero
#print axioms geometryRow088_physicalVolume_parse
#print axioms geometryRow088_physicalVolume_read
#print axioms geometryRow088_meanGap_field
#print axioms geometryRow088_meanGap_numerator_no_slash
#print axioms geometryRow088_meanGap_numerator_parse
#print axioms geometryRow088_meanGap_denominator_parse
#print axioms geometryRow088_meanGap_denominator_nonzero
#print axioms geometryRow088_meanGap_parse
#print axioms geometryRow088_meanGap_read
#print axioms geometryRow088_jensenBound_field
#print axioms geometryRow088_jensenBound_numerator_no_slash
#print axioms geometryRow088_jensenBound_numerator_parse
#print axioms geometryRow088_jensenBound_denominator_parse
#print axioms geometryRow088_jensenBound_denominator_nonzero
#print axioms geometryRow088_jensenBound_parse
#print axioms geometryRow088_jensenBound_read
#print axioms geometryRow088_factorMaxima_read
#print axioms geometryRow088_gapWeightedMeans_read
#print axioms geometryRow088_floor_text_read
#print axioms geometryRow088_floor_chars_parse
#print axioms geometryRow088_floor_parse
#print axioms decode_geometry_Rows_088
#print axioms geometry_Rows_block_044_push_eq
#print axioms geometry_Rows_block_044_reverse
#print axioms decode_geometry_Rows_block_044
#print axioms decode_geometry_Rows_through_block_044

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
