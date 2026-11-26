import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows001

/-! Original simplices typed block 2, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson004 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped004 : GeometryRow :=
  { simplexId := 4,
    vertexIds := #[39, 35, 29, 28, 25, 13, 5, 3, 2],
    physicalVolume := ((2456234377652874140348249285478981998550504859277 : ℚ) / (1136467097919317606400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((805156799 : ℚ) / (479808000000 : ℚ)),
    factorMaxima := #[((12703177 : ℚ) / (136000000 : ℚ)), ((13390549 : ℚ) / (136000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((8952953 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((157594606352520078429 : ℚ) / (1877947717987600000000 : ℚ)), ((645510482945031002391 : ℚ) / (7511790871950400000000 : ℚ)), ((233492235228362881373 : ℚ) / (1609669472560800000000 : ℚ)), ((2664344404332803325769 : ℚ) / (22535372615851200000000 : ℚ)), ((4432164339875680633 : ℚ) / (63124293041600000000 : ℚ)), ((128578120089794599321 : ℚ) / (2816921576981400000000 : ℚ)), ((22129148121590516371 : ℚ) / (613207418118400000000 : ℚ)), ((62570608567211060683 : ℚ) / (1839622254355200000000 : ℚ)), ((706045377833219362303 : ℚ) / (22535372615851200000000 : ℚ)), ((231794768273070949301 : ℚ) / (7511790871950400000000 : ℚ))],
    jensenBound := ((252075082095253704086552390087869593442478804749013273781280972082354730686877554638143294096709814868182097268242673443280303670631601202746794117493726428322420955084000000000000000000000000 : ℚ) / (8172627416318096844437498142502890822677694850062116783367038953974839435113306075869296179438730993060621300029304358678520120108807628512942949036992926954566040758573721788493856941177911337011429421 : ℚ)),
    jensenFloorQ96 := (2443699504783829963 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_simplexId_before"
  err.flush

theorem geometryRow004_simplexId_read :
    geometryRowsJson004.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped004.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_vertexIds_before"
  err.flush

theorem geometryRow004_vertexIds_read :
    geometryRowsJson004.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped004.vertexIds := by decide +kernel

noncomputable def geometryRow004_physicalVolumeNumeratorChars : List Char := ['2', '4', '5', '6', '2', '3', '4', '3', '7', '7', '6', '5', '2', '8', '7', '4', '1', '4', '0', '3', '4', '8', '2', '4', '9', '2', '8', '5', '4', '7', '8', '9', '8', '1', '9', '9', '8', '5', '5', '0', '5', '0', '4', '8', '5', '9', '2', '7', '7']
noncomputable def geometryRow004_physicalVolumeDenominatorChars : List Char := ['1', '1', '3', '6', '4', '6', '7', '0', '9', '7', '9', '1', '9', '3', '1', '7', '6', '0', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_physicalVolumeText : String := String.ofList (geometryRow004_physicalVolumeNumeratorChars ++ '/' :: geometryRow004_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_physicalVolume_before_field"
  err.flush

theorem geometryRow004_physicalVolume_field :
    geometryRowsJson004.getObjVal? "physical_volume" = .ok (.str geometryRow004_physicalVolumeText) := by rfl

theorem geometryRow004_physicalVolume_numerator_no_slash :
    geometryRow004_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeNumeratorChars = some (2456234377652874140348249285478981998550504859277 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeDenominatorChars = some (1136467097919317606400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_nonzero : (1136467097919317606400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_physicalVolume_parse :
    parseRational geometryRow004_physicalVolumeText = .ok geometryRowsTyped004.physicalVolume :=
  original_rational_fraction_of_chars geometryRow004_physicalVolumeNumeratorChars geometryRow004_physicalVolumeDenominatorChars
    (2456234377652874140348249285478981998550504859277 : Int) (1136467097919317606400000000000000000000000000000000000000000000000000 : Int)
    geometryRow004_physicalVolume_numerator_no_slash geometryRow004_physicalVolume_numerator_parse
    geometryRow004_physicalVolume_denominator_parse geometryRow004_physicalVolume_denominator_nonzero

theorem geometryRow004_physicalVolume_read :
    rationalField geometryRowsJson004 "physical_volume" = .ok geometryRowsTyped004.physicalVolume :=
  original_rationalField_of_string geometryRowsJson004 "physical_volume" geometryRow004_physicalVolumeText
    geometryRowsTyped004.physicalVolume geometryRow004_physicalVolume_field geometryRow004_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_physicalVolume_complete"
  err.flush

noncomputable def geometryRow004_meanGapNumeratorChars : List Char := ['8', '0', '5', '1', '5', '6', '7', '9', '9']
noncomputable def geometryRow004_meanGapDenominatorChars : List Char := ['4', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_meanGapText : String := String.ofList (geometryRow004_meanGapNumeratorChars ++ '/' :: geometryRow004_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_meanGap_before_field"
  err.flush

theorem geometryRow004_meanGap_field :
    geometryRowsJson004.getObjVal? "mean_gap" = .ok (.str geometryRow004_meanGapText) := by rfl

theorem geometryRow004_meanGap_numerator_no_slash :
    geometryRow004_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_meanGap_numerator_parse :
    SourceJson.intChars geometryRow004_meanGapNumeratorChars = some (805156799 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_parse :
    SourceJson.intChars geometryRow004_meanGapDenominatorChars = some (479808000000 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_nonzero : (479808000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_meanGap_parse :
    parseRational geometryRow004_meanGapText = .ok geometryRowsTyped004.meanGap :=
  original_rational_fraction_of_chars geometryRow004_meanGapNumeratorChars geometryRow004_meanGapDenominatorChars
    (805156799 : Int) (479808000000 : Int)
    geometryRow004_meanGap_numerator_no_slash geometryRow004_meanGap_numerator_parse
    geometryRow004_meanGap_denominator_parse geometryRow004_meanGap_denominator_nonzero

theorem geometryRow004_meanGap_read :
    rationalField geometryRowsJson004 "mean_gap" = .ok geometryRowsTyped004.meanGap :=
  original_rationalField_of_string geometryRowsJson004 "mean_gap" geometryRow004_meanGapText
    geometryRowsTyped004.meanGap geometryRow004_meanGap_field geometryRow004_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_meanGap_complete"
  err.flush

noncomputable def geometryRow004_jensenBoundNumeratorChars : List Char := ['2', '5', '2', '0', '7', '5', '0', '8', '2', '0', '9', '5', '2', '5', '3', '7', '0', '4', '0', '8', '6', '5', '5', '2', '3', '9', '0', '0', '8', '7', '8', '6', '9', '5', '9', '3', '4', '4', '2', '4', '7', '8', '8', '0', '4', '7', '4', '9', '0', '1', '3', '2', '7', '3', '7', '8', '1', '2', '8', '0', '9', '7', '2', '0', '8', '2', '3', '5', '4', '7', '3', '0', '6', '8', '6', '8', '7', '7', '5', '5', '4', '6', '3', '8', '1', '4', '3', '2', '9', '4', '0', '9', '6', '7', '0', '9', '8', '1', '4', '8', '6', '8', '1', '8', '2', '0', '9', '7', '2', '6', '8', '2', '4', '2', '6', '7', '3', '4', '4', '3', '2', '8', '0', '3', '0', '3', '6', '7', '0', '6', '3', '1', '6', '0', '1', '2', '0', '2', '7', '4', '6', '7', '9', '4', '1', '1', '7', '4', '9', '3', '7', '2', '6', '4', '2', '8', '3', '2', '2', '4', '2', '0', '9', '5', '5', '0', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_jensenBoundDenominatorChars : List Char := ['8', '1', '7', '2', '6', '2', '7', '4', '1', '6', '3', '1', '8', '0', '9', '6', '8', '4', '4', '4', '3', '7', '4', '9', '8', '1', '4', '2', '5', '0', '2', '8', '9', '0', '8', '2', '2', '6', '7', '7', '6', '9', '4', '8', '5', '0', '0', '6', '2', '1', '1', '6', '7', '8', '3', '3', '6', '7', '0', '3', '8', '9', '5', '3', '9', '7', '4', '8', '3', '9', '4', '3', '5', '1', '1', '3', '3', '0', '6', '0', '7', '5', '8', '6', '9', '2', '9', '6', '1', '7', '9', '4', '3', '8', '7', '3', '0', '9', '9', '3', '0', '6', '0', '6', '2', '1', '3', '0', '0', '0', '2', '9', '3', '0', '4', '3', '5', '8', '6', '7', '8', '5', '2', '0', '1', '2', '0', '1', '0', '8', '8', '0', '7', '6', '2', '8', '5', '1', '2', '9', '4', '2', '9', '4', '9', '0', '3', '6', '9', '9', '2', '9', '2', '6', '9', '5', '4', '5', '6', '6', '0', '4', '0', '7', '5', '8', '5', '7', '3', '7', '2', '1', '7', '8', '8', '4', '9', '3', '8', '5', '6', '9', '4', '1', '1', '7', '7', '9', '1', '1', '3', '3', '7', '0', '1', '1', '4', '2', '9', '4', '2', '1']
noncomputable def geometryRow004_jensenBoundText : String := String.ofList (geometryRow004_jensenBoundNumeratorChars ++ '/' :: geometryRow004_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_jensenBound_before_field"
  err.flush

theorem geometryRow004_jensenBound_field :
    geometryRowsJson004.getObjVal? "jensen_bound" = .ok (.str geometryRow004_jensenBoundText) := by rfl

theorem geometryRow004_jensenBound_numerator_no_slash :
    geometryRow004_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow004_jensenBoundNumeratorChars = some (252075082095253704086552390087869593442478804749013273781280972082354730686877554638143294096709814868182097268242673443280303670631601202746794117493726428322420955084000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow004_jensenBoundDenominatorChars = some (8172627416318096844437498142502890822677694850062116783367038953974839435113306075869296179438730993060621300029304358678520120108807628512942949036992926954566040758573721788493856941177911337011429421 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_nonzero : (8172627416318096844437498142502890822677694850062116783367038953974839435113306075869296179438730993060621300029304358678520120108807628512942949036992926954566040758573721788493856941177911337011429421 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_jensenBound_parse :
    parseRational geometryRow004_jensenBoundText = .ok geometryRowsTyped004.jensenBound :=
  original_rational_fraction_of_chars geometryRow004_jensenBoundNumeratorChars geometryRow004_jensenBoundDenominatorChars
    (252075082095253704086552390087869593442478804749013273781280972082354730686877554638143294096709814868182097268242673443280303670631601202746794117493726428322420955084000000000000000000000000 : Int) (8172627416318096844437498142502890822677694850062116783367038953974839435113306075869296179438730993060621300029304358678520120108807628512942949036992926954566040758573721788493856941177911337011429421 : Int)
    geometryRow004_jensenBound_numerator_no_slash geometryRow004_jensenBound_numerator_parse
    geometryRow004_jensenBound_denominator_parse geometryRow004_jensenBound_denominator_nonzero

theorem geometryRow004_jensenBound_read :
    rationalField geometryRowsJson004 "jensen_bound" = .ok geometryRowsTyped004.jensenBound :=
  original_rationalField_of_string geometryRowsJson004 "jensen_bound" geometryRow004_jensenBoundText
    geometryRowsTyped004.jensenBound geometryRow004_jensenBound_field geometryRow004_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_factorMaxima_before"
  err.flush

theorem geometryRow004_factorMaxima_read :
    rationalArrayField geometryRowsJson004 "factor_maxima" = .ok geometryRowsTyped004.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_gapWeightedMeans_before"
  err.flush

theorem geometryRow004_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson004 "gap_weighted_means" = .ok geometryRowsTyped004.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow004_floorChars : List Char := ['2', '4', '4', '3', '6', '9', '9', '5', '0', '4', '7', '8', '3', '8', '2', '9', '9', '6', '3']
noncomputable def geometryRow004_floorText : String := String.ofList geometryRow004_floorChars

theorem geometryRow004_floor_text_read :
    geometryRowsJson004.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow004_floorText := by rfl

theorem geometryRow004_floor_chars_parse :
    SourceJson.intChars geometryRow004_floorChars = some (2443699504783829963 : Int) := by decide +kernel

theorem geometryRow004_floor_parse :
    parseInteger geometryRow004_floorText = .ok geometryRowsTyped004.jensenFloorQ96 := by
  simp only [geometryRow004_floorText, parseInteger, String.toList_ofList, geometryRow004_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_004 :
    decodeGeometryRow geometryRowsJson004 = .ok geometryRowsTyped004 :=
  original_geometryRow_of_fields geometryRowsJson004 geometryRowsTyped004 geometryRow004_floorText
    geometryRow004_simplexId_read geometryRow004_vertexIds_read
    geometryRow004_physicalVolume_read geometryRow004_meanGap_read
    geometryRow004_factorMaxima_read geometryRow004_gapWeightedMeans_read
    geometryRow004_jensenBound_read geometryRow004_floor_text_read geometryRow004_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_004_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson005 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped005 : GeometryRow :=
  { simplexId := 5,
    vertexIds := #[39, 35, 29, 28, 25, 13, 5, 4, 2],
    physicalVolume := ((6821809491132219563851403881330129052233303819 : ℚ) / (4001964970664263680000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((520143709 : ℚ) / (310464000000 : ℚ)),
    factorMaxima := #[((1021879 : ℚ) / (11200000 : ℚ)), ((37827897 : ℚ) / (392000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((8952953 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((8163869853141856569 : ℚ) / (98125110702850000000 : ℚ)), ((267558982048264090003 : ℚ) / (3140003542491200000000 : ℚ)), ((32591983092439433073 : ℚ) / (224285967320800000000 : ℚ)), ((1118366273121761339297 : ℚ) / (9420010627473600000000 : ℚ)), ((95489507785582243279 : ℚ) / (1345715803924800000000 : ℚ)), ((35633551145318747807 : ℚ) / (785000885622800000000 : ℚ)), ((9187857802260599603 : ℚ) / (256326819795200000000 : ℚ)), ((25968097956287083019 : ℚ) / (768980459385600000000 : ℚ)), ((99026105645104155873 : ℚ) / (3140003542491200000000 : ℚ)), ((288406737268297875739 : ℚ) / (9420010627473600000000 : ℚ))],
    jensenBound := ((45801170119132386798250660015155378750822038404888934149708925063745274684393242158383927639809660633205246022839385115515125369881901648788867246021234172246425188750000000000000000000000 : ℚ) / (1846012862147488752427152953723189207235297428800636392136669668589261842761194015717278904002560565775899750474019947859474015296343481842658544163499233105251450226801923762622921808519230927146729 : ℚ)),
    jensenFloorQ96 := (1965718995760803648 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_simplexId_before"
  err.flush

theorem geometryRow005_simplexId_read :
    geometryRowsJson005.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped005.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_vertexIds_before"
  err.flush

theorem geometryRow005_vertexIds_read :
    geometryRowsJson005.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped005.vertexIds := by decide +kernel

noncomputable def geometryRow005_physicalVolumeNumeratorChars : List Char := ['6', '8', '2', '1', '8', '0', '9', '4', '9', '1', '1', '3', '2', '2', '1', '9', '5', '6', '3', '8', '5', '1', '4', '0', '3', '8', '8', '1', '3', '3', '0', '1', '2', '9', '0', '5', '2', '2', '3', '3', '3', '0', '3', '8', '1', '9']
noncomputable def geometryRow005_physicalVolumeDenominatorChars : List Char := ['4', '0', '0', '1', '9', '6', '4', '9', '7', '0', '6', '6', '4', '2', '6', '3', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_physicalVolumeText : String := String.ofList (geometryRow005_physicalVolumeNumeratorChars ++ '/' :: geometryRow005_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_physicalVolume_before_field"
  err.flush

theorem geometryRow005_physicalVolume_field :
    geometryRowsJson005.getObjVal? "physical_volume" = .ok (.str geometryRow005_physicalVolumeText) := by rfl

theorem geometryRow005_physicalVolume_numerator_no_slash :
    geometryRow005_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeNumeratorChars = some (6821809491132219563851403881330129052233303819 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeDenominatorChars = some (4001964970664263680000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_nonzero : (4001964970664263680000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_physicalVolume_parse :
    parseRational geometryRow005_physicalVolumeText = .ok geometryRowsTyped005.physicalVolume :=
  original_rational_fraction_of_chars geometryRow005_physicalVolumeNumeratorChars geometryRow005_physicalVolumeDenominatorChars
    (6821809491132219563851403881330129052233303819 : Int) (4001964970664263680000000000000000000000000000000000000000000000000 : Int)
    geometryRow005_physicalVolume_numerator_no_slash geometryRow005_physicalVolume_numerator_parse
    geometryRow005_physicalVolume_denominator_parse geometryRow005_physicalVolume_denominator_nonzero

theorem geometryRow005_physicalVolume_read :
    rationalField geometryRowsJson005 "physical_volume" = .ok geometryRowsTyped005.physicalVolume :=
  original_rationalField_of_string geometryRowsJson005 "physical_volume" geometryRow005_physicalVolumeText
    geometryRowsTyped005.physicalVolume geometryRow005_physicalVolume_field geometryRow005_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_physicalVolume_complete"
  err.flush

noncomputable def geometryRow005_meanGapNumeratorChars : List Char := ['5', '2', '0', '1', '4', '3', '7', '0', '9']
noncomputable def geometryRow005_meanGapDenominatorChars : List Char := ['3', '1', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_meanGapText : String := String.ofList (geometryRow005_meanGapNumeratorChars ++ '/' :: geometryRow005_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_meanGap_before_field"
  err.flush

theorem geometryRow005_meanGap_field :
    geometryRowsJson005.getObjVal? "mean_gap" = .ok (.str geometryRow005_meanGapText) := by rfl

theorem geometryRow005_meanGap_numerator_no_slash :
    geometryRow005_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_meanGap_numerator_parse :
    SourceJson.intChars geometryRow005_meanGapNumeratorChars = some (520143709 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_parse :
    SourceJson.intChars geometryRow005_meanGapDenominatorChars = some (310464000000 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_nonzero : (310464000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_meanGap_parse :
    parseRational geometryRow005_meanGapText = .ok geometryRowsTyped005.meanGap :=
  original_rational_fraction_of_chars geometryRow005_meanGapNumeratorChars geometryRow005_meanGapDenominatorChars
    (520143709 : Int) (310464000000 : Int)
    geometryRow005_meanGap_numerator_no_slash geometryRow005_meanGap_numerator_parse
    geometryRow005_meanGap_denominator_parse geometryRow005_meanGap_denominator_nonzero

theorem geometryRow005_meanGap_read :
    rationalField geometryRowsJson005 "mean_gap" = .ok geometryRowsTyped005.meanGap :=
  original_rationalField_of_string geometryRowsJson005 "mean_gap" geometryRow005_meanGapText
    geometryRowsTyped005.meanGap geometryRow005_meanGap_field geometryRow005_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_meanGap_complete"
  err.flush

noncomputable def geometryRow005_jensenBoundNumeratorChars : List Char := ['4', '5', '8', '0', '1', '1', '7', '0', '1', '1', '9', '1', '3', '2', '3', '8', '6', '7', '9', '8', '2', '5', '0', '6', '6', '0', '0', '1', '5', '1', '5', '5', '3', '7', '8', '7', '5', '0', '8', '2', '2', '0', '3', '8', '4', '0', '4', '8', '8', '8', '9', '3', '4', '1', '4', '9', '7', '0', '8', '9', '2', '5', '0', '6', '3', '7', '4', '5', '2', '7', '4', '6', '8', '4', '3', '9', '3', '2', '4', '2', '1', '5', '8', '3', '8', '3', '9', '2', '7', '6', '3', '9', '8', '0', '9', '6', '6', '0', '6', '3', '3', '2', '0', '5', '2', '4', '6', '0', '2', '2', '8', '3', '9', '3', '8', '5', '1', '1', '5', '5', '1', '5', '1', '2', '5', '3', '6', '9', '8', '8', '1', '9', '0', '1', '6', '4', '8', '7', '8', '8', '8', '6', '7', '2', '4', '6', '0', '2', '1', '2', '3', '4', '1', '7', '2', '2', '4', '6', '4', '2', '5', '1', '8', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_jensenBoundDenominatorChars : List Char := ['1', '8', '4', '6', '0', '1', '2', '8', '6', '2', '1', '4', '7', '4', '8', '8', '7', '5', '2', '4', '2', '7', '1', '5', '2', '9', '5', '3', '7', '2', '3', '1', '8', '9', '2', '0', '7', '2', '3', '5', '2', '9', '7', '4', '2', '8', '8', '0', '0', '6', '3', '6', '3', '9', '2', '1', '3', '6', '6', '6', '9', '6', '6', '8', '5', '8', '9', '2', '6', '1', '8', '4', '2', '7', '6', '1', '1', '9', '4', '0', '1', '5', '7', '1', '7', '2', '7', '8', '9', '0', '4', '0', '0', '2', '5', '6', '0', '5', '6', '5', '7', '7', '5', '8', '9', '9', '7', '5', '0', '4', '7', '4', '0', '1', '9', '9', '4', '7', '8', '5', '9', '4', '7', '4', '0', '1', '5', '2', '9', '6', '3', '4', '3', '4', '8', '1', '8', '4', '2', '6', '5', '8', '5', '4', '4', '1', '6', '3', '4', '9', '9', '2', '3', '3', '1', '0', '5', '2', '5', '1', '4', '5', '0', '2', '2', '6', '8', '0', '1', '9', '2', '3', '7', '6', '2', '6', '2', '2', '9', '2', '1', '8', '0', '8', '5', '1', '9', '2', '3', '0', '9', '2', '7', '1', '4', '6', '7', '2', '9']
noncomputable def geometryRow005_jensenBoundText : String := String.ofList (geometryRow005_jensenBoundNumeratorChars ++ '/' :: geometryRow005_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_jensenBound_before_field"
  err.flush

theorem geometryRow005_jensenBound_field :
    geometryRowsJson005.getObjVal? "jensen_bound" = .ok (.str geometryRow005_jensenBoundText) := by rfl

theorem geometryRow005_jensenBound_numerator_no_slash :
    geometryRow005_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow005_jensenBoundNumeratorChars = some (45801170119132386798250660015155378750822038404888934149708925063745274684393242158383927639809660633205246022839385115515125369881901648788867246021234172246425188750000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow005_jensenBoundDenominatorChars = some (1846012862147488752427152953723189207235297428800636392136669668589261842761194015717278904002560565775899750474019947859474015296343481842658544163499233105251450226801923762622921808519230927146729 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_nonzero : (1846012862147488752427152953723189207235297428800636392136669668589261842761194015717278904002560565775899750474019947859474015296343481842658544163499233105251450226801923762622921808519230927146729 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_jensenBound_parse :
    parseRational geometryRow005_jensenBoundText = .ok geometryRowsTyped005.jensenBound :=
  original_rational_fraction_of_chars geometryRow005_jensenBoundNumeratorChars geometryRow005_jensenBoundDenominatorChars
    (45801170119132386798250660015155378750822038404888934149708925063745274684393242158383927639809660633205246022839385115515125369881901648788867246021234172246425188750000000000000000000000 : Int) (1846012862147488752427152953723189207235297428800636392136669668589261842761194015717278904002560565775899750474019947859474015296343481842658544163499233105251450226801923762622921808519230927146729 : Int)
    geometryRow005_jensenBound_numerator_no_slash geometryRow005_jensenBound_numerator_parse
    geometryRow005_jensenBound_denominator_parse geometryRow005_jensenBound_denominator_nonzero

theorem geometryRow005_jensenBound_read :
    rationalField geometryRowsJson005 "jensen_bound" = .ok geometryRowsTyped005.jensenBound :=
  original_rationalField_of_string geometryRowsJson005 "jensen_bound" geometryRow005_jensenBoundText
    geometryRowsTyped005.jensenBound geometryRow005_jensenBound_field geometryRow005_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_factorMaxima_before"
  err.flush

theorem geometryRow005_factorMaxima_read :
    rationalArrayField geometryRowsJson005 "factor_maxima" = .ok geometryRowsTyped005.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_gapWeightedMeans_before"
  err.flush

theorem geometryRow005_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson005 "gap_weighted_means" = .ok geometryRowsTyped005.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow005_floorChars : List Char := ['1', '9', '6', '5', '7', '1', '8', '9', '9', '5', '7', '6', '0', '8', '0', '3', '6', '4', '8']
noncomputable def geometryRow005_floorText : String := String.ofList geometryRow005_floorChars

theorem geometryRow005_floor_text_read :
    geometryRowsJson005.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow005_floorText := by rfl

theorem geometryRow005_floor_chars_parse :
    SourceJson.intChars geometryRow005_floorChars = some (1965718995760803648 : Int) := by decide +kernel

theorem geometryRow005_floor_parse :
    parseInteger geometryRow005_floorText = .ok geometryRowsTyped005.jensenFloorQ96 := by
  simp only [geometryRow005_floorText, parseInteger, String.toList_ofList, geometryRow005_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_005 :
    decodeGeometryRow geometryRowsJson005 = .ok geometryRowsTyped005 :=
  original_geometryRow_of_fields geometryRowsJson005 geometryRowsTyped005 geometryRow005_floorText
    geometryRow005_simplexId_read geometryRow005_vertexIds_read
    geometryRow005_physicalVolume_read geometryRow005_meanGap_read
    geometryRow005_factorMaxima_read geometryRow005_gapWeightedMeans_read
    geometryRow005_jensenBound_read geometryRow005_floor_text_read geometryRow005_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_005_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock002 : List SourceJson := [geometryRowsJson004, geometryRowsJson005]
noncomputable def geometryRowsTypedBlock002 : List (GeometryRow) := [geometryRowsTyped004, geometryRowsTyped005]
noncomputable def geometryRowsTypedThroughBlock002 : List (GeometryRow) := geometryRowsTypedThroughBlock001 ++ geometryRowsTypedBlock002

theorem geometry_Rows_block_002_push_eq (acc : List SourceJson) :
    SimplicesBlock002.blockPush acc = [geometryRowsJson005, geometryRowsJson004] ++ acc := by rfl

theorem geometry_Rows_block_002_reverse (acc : List SourceJson) :
    (SimplicesBlock002.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock002 := by
  rw [geometry_Rows_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_002 :
    geometryRowsJsonBlock002.mapM decodeGeometryRow = .ok geometryRowsTypedBlock002 := by
  simp only [geometryRowsJsonBlock002, geometryRowsTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_004, decode_geometry_Rows_005]
  rfl

theorem decode_geometry_Rows_through_block_002 :
    SimplicesValue.arrayAcc003.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock002 := by
  change (SimplicesBlock002.blockPush SimplicesValue.arrayAcc002).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_002_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_001, decode_geometry_Rows_block_002]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_002_complete"
  err.flush

#print axioms geometryRow004_simplexId_read
#print axioms geometryRow004_vertexIds_read
#print axioms geometryRow004_physicalVolume_field
#print axioms geometryRow004_physicalVolume_numerator_no_slash
#print axioms geometryRow004_physicalVolume_numerator_parse
#print axioms geometryRow004_physicalVolume_denominator_parse
#print axioms geometryRow004_physicalVolume_denominator_nonzero
#print axioms geometryRow004_physicalVolume_parse
#print axioms geometryRow004_physicalVolume_read
#print axioms geometryRow004_meanGap_field
#print axioms geometryRow004_meanGap_numerator_no_slash
#print axioms geometryRow004_meanGap_numerator_parse
#print axioms geometryRow004_meanGap_denominator_parse
#print axioms geometryRow004_meanGap_denominator_nonzero
#print axioms geometryRow004_meanGap_parse
#print axioms geometryRow004_meanGap_read
#print axioms geometryRow004_jensenBound_field
#print axioms geometryRow004_jensenBound_numerator_no_slash
#print axioms geometryRow004_jensenBound_numerator_parse
#print axioms geometryRow004_jensenBound_denominator_parse
#print axioms geometryRow004_jensenBound_denominator_nonzero
#print axioms geometryRow004_jensenBound_parse
#print axioms geometryRow004_jensenBound_read
#print axioms geometryRow004_factorMaxima_read
#print axioms geometryRow004_gapWeightedMeans_read
#print axioms geometryRow004_floor_text_read
#print axioms geometryRow004_floor_chars_parse
#print axioms geometryRow004_floor_parse
#print axioms decode_geometry_Rows_004
#print axioms geometryRow005_simplexId_read
#print axioms geometryRow005_vertexIds_read
#print axioms geometryRow005_physicalVolume_field
#print axioms geometryRow005_physicalVolume_numerator_no_slash
#print axioms geometryRow005_physicalVolume_numerator_parse
#print axioms geometryRow005_physicalVolume_denominator_parse
#print axioms geometryRow005_physicalVolume_denominator_nonzero
#print axioms geometryRow005_physicalVolume_parse
#print axioms geometryRow005_physicalVolume_read
#print axioms geometryRow005_meanGap_field
#print axioms geometryRow005_meanGap_numerator_no_slash
#print axioms geometryRow005_meanGap_numerator_parse
#print axioms geometryRow005_meanGap_denominator_parse
#print axioms geometryRow005_meanGap_denominator_nonzero
#print axioms geometryRow005_meanGap_parse
#print axioms geometryRow005_meanGap_read
#print axioms geometryRow005_jensenBound_field
#print axioms geometryRow005_jensenBound_numerator_no_slash
#print axioms geometryRow005_jensenBound_numerator_parse
#print axioms geometryRow005_jensenBound_denominator_parse
#print axioms geometryRow005_jensenBound_denominator_nonzero
#print axioms geometryRow005_jensenBound_parse
#print axioms geometryRow005_jensenBound_read
#print axioms geometryRow005_factorMaxima_read
#print axioms geometryRow005_gapWeightedMeans_read
#print axioms geometryRow005_floor_text_read
#print axioms geometryRow005_floor_chars_parse
#print axioms geometryRow005_floor_parse
#print axioms decode_geometry_Rows_005
#print axioms geometry_Rows_block_002_push_eq
#print axioms geometry_Rows_block_002_reverse
#print axioms decode_geometry_Rows_block_002
#print axioms decode_geometry_Rows_through_block_002

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
