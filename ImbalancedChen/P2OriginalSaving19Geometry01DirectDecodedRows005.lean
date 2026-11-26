import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows004

/-! Original simplices typed block 5, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson010 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped010 : GeometryRow :=
  { simplexId := 10,
    vertexIds := #[39, 35, 29, 28, 25, 17, 12, 4, 2],
    physicalVolume := ((402319128836900279765646578438774441937775371991 : ℚ) / (85962346526985420800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((591629 : ℚ) / (517440000 : ℚ)),
    factorMaxima := #[((1021879 : ℚ) / (11200000 : ℚ)), ((37827897 : ℚ) / (392000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((8952977 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((15380681399020982389 : ℚ) / (186582486552000000000 : ℚ)), ((1044582047633730083 : ℚ) / (12438832436800000000 : ℚ)), ((5829668108574715841 : ℚ) / (39981961404000000000 : ℚ)), ((13287448299848682821 : ℚ) / (111949491931200000000 : ℚ)), ((1137773067608379529 : ℚ) / (15992784561600000000 : ℚ)), ((2528790196067250749 : ℚ) / (55974745965600000000 : ℚ)), ((234985959466676401 : ℚ) / (6527667168000000000 : ℚ)), ((221442399824256451 : ℚ) / (6527667168000000000 : ℚ)), ((17974499807211865717 : ℚ) / (559747459656000000000 : ℚ)), ((1127168493908782187 : ℚ) / (37316497310400000000 : ℚ))],
    jensenBound := ((177163320044784703266285704815412101433017457062682316306920921966017473128655008948000128089851540950071792361696538518286060969653182154256640000000000000000000000000000000 : ℚ) / (3775029487134252914668138372944512488855141862295240854297418093188371300554028069497802297576380797337929854446706728732054721024725273438410982081167675886429796355805167115330584963 : ℚ)),
    jensenFloorQ96 := (3718202562367335390 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_simplexId_before"
  err.flush

theorem geometryRow010_simplexId_read :
    geometryRowsJson010.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped010.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_vertexIds_before"
  err.flush

theorem geometryRow010_vertexIds_read :
    geometryRowsJson010.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped010.vertexIds := by decide +kernel

noncomputable def geometryRow010_physicalVolumeNumeratorChars : List Char := ['4', '0', '2', '3', '1', '9', '1', '2', '8', '8', '3', '6', '9', '0', '0', '2', '7', '9', '7', '6', '5', '6', '4', '6', '5', '7', '8', '4', '3', '8', '7', '7', '4', '4', '4', '1', '9', '3', '7', '7', '7', '5', '3', '7', '1', '9', '9', '1']
noncomputable def geometryRow010_physicalVolumeDenominatorChars : List Char := ['8', '5', '9', '6', '2', '3', '4', '6', '5', '2', '6', '9', '8', '5', '4', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_physicalVolumeText : String := String.ofList (geometryRow010_physicalVolumeNumeratorChars ++ '/' :: geometryRow010_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_physicalVolume_before_field"
  err.flush

theorem geometryRow010_physicalVolume_field :
    geometryRowsJson010.getObjVal? "physical_volume" = .ok (.str geometryRow010_physicalVolumeText) := by rfl

theorem geometryRow010_physicalVolume_numerator_no_slash :
    geometryRow010_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeNumeratorChars = some (402319128836900279765646578438774441937775371991 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeDenominatorChars = some (85962346526985420800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_nonzero : (85962346526985420800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_physicalVolume_parse :
    parseRational geometryRow010_physicalVolumeText = .ok geometryRowsTyped010.physicalVolume :=
  original_rational_fraction_of_chars geometryRow010_physicalVolumeNumeratorChars geometryRow010_physicalVolumeDenominatorChars
    (402319128836900279765646578438774441937775371991 : Int) (85962346526985420800000000000000000000000000000000000000000000000000 : Int)
    geometryRow010_physicalVolume_numerator_no_slash geometryRow010_physicalVolume_numerator_parse
    geometryRow010_physicalVolume_denominator_parse geometryRow010_physicalVolume_denominator_nonzero

theorem geometryRow010_physicalVolume_read :
    rationalField geometryRowsJson010 "physical_volume" = .ok geometryRowsTyped010.physicalVolume :=
  original_rationalField_of_string geometryRowsJson010 "physical_volume" geometryRow010_physicalVolumeText
    geometryRowsTyped010.physicalVolume geometryRow010_physicalVolume_field geometryRow010_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_physicalVolume_complete"
  err.flush

noncomputable def geometryRow010_meanGapNumeratorChars : List Char := ['5', '9', '1', '6', '2', '9']
noncomputable def geometryRow010_meanGapDenominatorChars : List Char := ['5', '1', '7', '4', '4', '0', '0', '0', '0']
noncomputable def geometryRow010_meanGapText : String := String.ofList (geometryRow010_meanGapNumeratorChars ++ '/' :: geometryRow010_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_meanGap_before_field"
  err.flush

theorem geometryRow010_meanGap_field :
    geometryRowsJson010.getObjVal? "mean_gap" = .ok (.str geometryRow010_meanGapText) := by rfl

theorem geometryRow010_meanGap_numerator_no_slash :
    geometryRow010_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_meanGap_numerator_parse :
    SourceJson.intChars geometryRow010_meanGapNumeratorChars = some (591629 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_parse :
    SourceJson.intChars geometryRow010_meanGapDenominatorChars = some (517440000 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_nonzero : (517440000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_meanGap_parse :
    parseRational geometryRow010_meanGapText = .ok geometryRowsTyped010.meanGap :=
  original_rational_fraction_of_chars geometryRow010_meanGapNumeratorChars geometryRow010_meanGapDenominatorChars
    (591629 : Int) (517440000 : Int)
    geometryRow010_meanGap_numerator_no_slash geometryRow010_meanGap_numerator_parse
    geometryRow010_meanGap_denominator_parse geometryRow010_meanGap_denominator_nonzero

theorem geometryRow010_meanGap_read :
    rationalField geometryRowsJson010 "mean_gap" = .ok geometryRowsTyped010.meanGap :=
  original_rationalField_of_string geometryRowsJson010 "mean_gap" geometryRow010_meanGapText
    geometryRowsTyped010.meanGap geometryRow010_meanGap_field geometryRow010_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_meanGap_complete"
  err.flush

noncomputable def geometryRow010_jensenBoundNumeratorChars : List Char := ['1', '7', '7', '1', '6', '3', '3', '2', '0', '0', '4', '4', '7', '8', '4', '7', '0', '3', '2', '6', '6', '2', '8', '5', '7', '0', '4', '8', '1', '5', '4', '1', '2', '1', '0', '1', '4', '3', '3', '0', '1', '7', '4', '5', '7', '0', '6', '2', '6', '8', '2', '3', '1', '6', '3', '0', '6', '9', '2', '0', '9', '2', '1', '9', '6', '6', '0', '1', '7', '4', '7', '3', '1', '2', '8', '6', '5', '5', '0', '0', '8', '9', '4', '8', '0', '0', '0', '1', '2', '8', '0', '8', '9', '8', '5', '1', '5', '4', '0', '9', '5', '0', '0', '7', '1', '7', '9', '2', '3', '6', '1', '6', '9', '6', '5', '3', '8', '5', '1', '8', '2', '8', '6', '0', '6', '0', '9', '6', '9', '6', '5', '3', '1', '8', '2', '1', '5', '4', '2', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_jensenBoundDenominatorChars : List Char := ['3', '7', '7', '5', '0', '2', '9', '4', '8', '7', '1', '3', '4', '2', '5', '2', '9', '1', '4', '6', '6', '8', '1', '3', '8', '3', '7', '2', '9', '4', '4', '5', '1', '2', '4', '8', '8', '8', '5', '5', '1', '4', '1', '8', '6', '2', '2', '9', '5', '2', '4', '0', '8', '5', '4', '2', '9', '7', '4', '1', '8', '0', '9', '3', '1', '8', '8', '3', '7', '1', '3', '0', '0', '5', '5', '4', '0', '2', '8', '0', '6', '9', '4', '9', '7', '8', '0', '2', '2', '9', '7', '5', '7', '6', '3', '8', '0', '7', '9', '7', '3', '3', '7', '9', '2', '9', '8', '5', '4', '4', '4', '6', '7', '0', '6', '7', '2', '8', '7', '3', '2', '0', '5', '4', '7', '2', '1', '0', '2', '4', '7', '2', '5', '2', '7', '3', '4', '3', '8', '4', '1', '0', '9', '8', '2', '0', '8', '1', '1', '6', '7', '6', '7', '5', '8', '8', '6', '4', '2', '9', '7', '9', '6', '3', '5', '5', '8', '0', '5', '1', '6', '7', '1', '1', '5', '3', '3', '0', '5', '8', '4', '9', '6', '3']
noncomputable def geometryRow010_jensenBoundText : String := String.ofList (geometryRow010_jensenBoundNumeratorChars ++ '/' :: geometryRow010_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_jensenBound_before_field"
  err.flush

theorem geometryRow010_jensenBound_field :
    geometryRowsJson010.getObjVal? "jensen_bound" = .ok (.str geometryRow010_jensenBoundText) := by rfl

theorem geometryRow010_jensenBound_numerator_no_slash :
    geometryRow010_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow010_jensenBoundNumeratorChars = some (177163320044784703266285704815412101433017457062682316306920921966017473128655008948000128089851540950071792361696538518286060969653182154256640000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow010_jensenBoundDenominatorChars = some (3775029487134252914668138372944512488855141862295240854297418093188371300554028069497802297576380797337929854446706728732054721024725273438410982081167675886429796355805167115330584963 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_nonzero : (3775029487134252914668138372944512488855141862295240854297418093188371300554028069497802297576380797337929854446706728732054721024725273438410982081167675886429796355805167115330584963 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_jensenBound_parse :
    parseRational geometryRow010_jensenBoundText = .ok geometryRowsTyped010.jensenBound :=
  original_rational_fraction_of_chars geometryRow010_jensenBoundNumeratorChars geometryRow010_jensenBoundDenominatorChars
    (177163320044784703266285704815412101433017457062682316306920921966017473128655008948000128089851540950071792361696538518286060969653182154256640000000000000000000000000000000 : Int) (3775029487134252914668138372944512488855141862295240854297418093188371300554028069497802297576380797337929854446706728732054721024725273438410982081167675886429796355805167115330584963 : Int)
    geometryRow010_jensenBound_numerator_no_slash geometryRow010_jensenBound_numerator_parse
    geometryRow010_jensenBound_denominator_parse geometryRow010_jensenBound_denominator_nonzero

theorem geometryRow010_jensenBound_read :
    rationalField geometryRowsJson010 "jensen_bound" = .ok geometryRowsTyped010.jensenBound :=
  original_rationalField_of_string geometryRowsJson010 "jensen_bound" geometryRow010_jensenBoundText
    geometryRowsTyped010.jensenBound geometryRow010_jensenBound_field geometryRow010_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_factorMaxima_before"
  err.flush

theorem geometryRow010_factorMaxima_read :
    rationalArrayField geometryRowsJson010 "factor_maxima" = .ok geometryRowsTyped010.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_gapWeightedMeans_before"
  err.flush

theorem geometryRow010_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson010 "gap_weighted_means" = .ok geometryRowsTyped010.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow010_floorChars : List Char := ['3', '7', '1', '8', '2', '0', '2', '5', '6', '2', '3', '6', '7', '3', '3', '5', '3', '9', '0']
noncomputable def geometryRow010_floorText : String := String.ofList geometryRow010_floorChars

theorem geometryRow010_floor_text_read :
    geometryRowsJson010.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow010_floorText := by rfl

theorem geometryRow010_floor_chars_parse :
    SourceJson.intChars geometryRow010_floorChars = some (3718202562367335390 : Int) := by decide +kernel

theorem geometryRow010_floor_parse :
    parseInteger geometryRow010_floorText = .ok geometryRowsTyped010.jensenFloorQ96 := by
  simp only [geometryRow010_floorText, parseInteger, String.toList_ofList, geometryRow010_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_010 :
    decodeGeometryRow geometryRowsJson010 = .ok geometryRowsTyped010 :=
  original_geometryRow_of_fields geometryRowsJson010 geometryRowsTyped010 geometryRow010_floorText
    geometryRow010_simplexId_read geometryRow010_vertexIds_read
    geometryRow010_physicalVolume_read geometryRow010_meanGap_read
    geometryRow010_factorMaxima_read geometryRow010_gapWeightedMeans_read
    geometryRow010_jensenBound_read geometryRow010_floor_text_read geometryRow010_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_010_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson011 : SourceJson :=
  (SimplicesBlock005.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped011 : GeometryRow :=
  { simplexId := 11,
    vertexIds := #[39, 35, 29, 28, 25, 17, 6, 2, 0],
    physicalVolume := ((1534326222939258532156956162779844024418695478861 : ℚ) / (98905540748378112000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((14002804403347 : ℚ) / (166286400000000 : ℚ)), ((14177755682227 : ℚ) / (166286400000000 : ℚ)), ((1031988490069 : ℚ) / (7126560000000 : ℚ)), ((6445344584299 : ℚ) / (55428800000000 : ℚ)), ((4844649302207 : ℚ) / (71265600000000 : ℚ)), ((11579259507961 : ℚ) / (249429600000000 : ℚ)), ((1510035631633 : ℚ) / (40723200000000 : ℚ)), ((1425543412003 : ℚ) / (40723200000000 : ℚ)), ((16559042033083 : ℚ) / (498859200000000 : ℚ)), ((15281798437819 : ℚ) / (498859200000000 : ℚ))],
    jensenBound := ((223562108667815707730188999323390105589731502361867801588872766469015047862986877937106634670080000000000000000000000 : ℚ) / (3103992067569844229603920044514948401717718014841683154717659547619856733683003727040656524071717466921486611598053624735219663 : ℚ)),
    jensenFloorQ96 := (5706333873279710728 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_simplexId_before"
  err.flush

theorem geometryRow011_simplexId_read :
    geometryRowsJson011.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped011.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_vertexIds_before"
  err.flush

theorem geometryRow011_vertexIds_read :
    geometryRowsJson011.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped011.vertexIds := by decide +kernel

noncomputable def geometryRow011_physicalVolumeNumeratorChars : List Char := ['1', '5', '3', '4', '3', '2', '6', '2', '2', '2', '9', '3', '9', '2', '5', '8', '5', '3', '2', '1', '5', '6', '9', '5', '6', '1', '6', '2', '7', '7', '9', '8', '4', '4', '0', '2', '4', '4', '1', '8', '6', '9', '5', '4', '7', '8', '8', '6', '1']
noncomputable def geometryRow011_physicalVolumeDenominatorChars : List Char := ['9', '8', '9', '0', '5', '5', '4', '0', '7', '4', '8', '3', '7', '8', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_physicalVolumeText : String := String.ofList (geometryRow011_physicalVolumeNumeratorChars ++ '/' :: geometryRow011_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_physicalVolume_before_field"
  err.flush

theorem geometryRow011_physicalVolume_field :
    geometryRowsJson011.getObjVal? "physical_volume" = .ok (.str geometryRow011_physicalVolumeText) := by rfl

theorem geometryRow011_physicalVolume_numerator_no_slash :
    geometryRow011_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeNumeratorChars = some (1534326222939258532156956162779844024418695478861 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeDenominatorChars = some (98905540748378112000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_nonzero : (98905540748378112000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_physicalVolume_parse :
    parseRational geometryRow011_physicalVolumeText = .ok geometryRowsTyped011.physicalVolume :=
  original_rational_fraction_of_chars geometryRow011_physicalVolumeNumeratorChars geometryRow011_physicalVolumeDenominatorChars
    (1534326222939258532156956162779844024418695478861 : Int) (98905540748378112000000000000000000000000000000000000000000000000000 : Int)
    geometryRow011_physicalVolume_numerator_no_slash geometryRow011_physicalVolume_numerator_parse
    geometryRow011_physicalVolume_denominator_parse geometryRow011_physicalVolume_denominator_nonzero

theorem geometryRow011_physicalVolume_read :
    rationalField geometryRowsJson011 "physical_volume" = .ok geometryRowsTyped011.physicalVolume :=
  original_rationalField_of_string geometryRowsJson011 "physical_volume" geometryRow011_physicalVolumeText
    geometryRowsTyped011.physicalVolume geometryRow011_physicalVolume_field geometryRow011_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_physicalVolume_complete"
  err.flush

noncomputable def geometryRow011_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow011_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_meanGapText : String := String.ofList (geometryRow011_meanGapNumeratorChars ++ '/' :: geometryRow011_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_meanGap_before_field"
  err.flush

theorem geometryRow011_meanGap_field :
    geometryRowsJson011.getObjVal? "mean_gap" = .ok (.str geometryRow011_meanGapText) := by rfl

theorem geometryRow011_meanGap_numerator_no_slash :
    geometryRow011_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_meanGap_numerator_parse :
    SourceJson.intChars geometryRow011_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_parse :
    SourceJson.intChars geometryRow011_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_meanGap_parse :
    parseRational geometryRow011_meanGapText = .ok geometryRowsTyped011.meanGap :=
  original_rational_fraction_of_chars geometryRow011_meanGapNumeratorChars geometryRow011_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow011_meanGap_numerator_no_slash geometryRow011_meanGap_numerator_parse
    geometryRow011_meanGap_denominator_parse geometryRow011_meanGap_denominator_nonzero

theorem geometryRow011_meanGap_read :
    rationalField geometryRowsJson011 "mean_gap" = .ok geometryRowsTyped011.meanGap :=
  original_rationalField_of_string geometryRowsJson011 "mean_gap" geometryRow011_meanGapText
    geometryRowsTyped011.meanGap geometryRow011_meanGap_field geometryRow011_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_meanGap_complete"
  err.flush

noncomputable def geometryRow011_jensenBoundNumeratorChars : List Char := ['2', '2', '3', '5', '6', '2', '1', '0', '8', '6', '6', '7', '8', '1', '5', '7', '0', '7', '7', '3', '0', '1', '8', '8', '9', '9', '9', '3', '2', '3', '3', '9', '0', '1', '0', '5', '5', '8', '9', '7', '3', '1', '5', '0', '2', '3', '6', '1', '8', '6', '7', '8', '0', '1', '5', '8', '8', '8', '7', '2', '7', '6', '6', '4', '6', '9', '0', '1', '5', '0', '4', '7', '8', '6', '2', '9', '8', '6', '8', '7', '7', '9', '3', '7', '1', '0', '6', '6', '3', '4', '6', '7', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_jensenBoundDenominatorChars : List Char := ['3', '1', '0', '3', '9', '9', '2', '0', '6', '7', '5', '6', '9', '8', '4', '4', '2', '2', '9', '6', '0', '3', '9', '2', '0', '0', '4', '4', '5', '1', '4', '9', '4', '8', '4', '0', '1', '7', '1', '7', '7', '1', '8', '0', '1', '4', '8', '4', '1', '6', '8', '3', '1', '5', '4', '7', '1', '7', '6', '5', '9', '5', '4', '7', '6', '1', '9', '8', '5', '6', '7', '3', '3', '6', '8', '3', '0', '0', '3', '7', '2', '7', '0', '4', '0', '6', '5', '6', '5', '2', '4', '0', '7', '1', '7', '1', '7', '4', '6', '6', '9', '2', '1', '4', '8', '6', '6', '1', '1', '5', '9', '8', '0', '5', '3', '6', '2', '4', '7', '3', '5', '2', '1', '9', '6', '6', '3']
noncomputable def geometryRow011_jensenBoundText : String := String.ofList (geometryRow011_jensenBoundNumeratorChars ++ '/' :: geometryRow011_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_jensenBound_before_field"
  err.flush

theorem geometryRow011_jensenBound_field :
    geometryRowsJson011.getObjVal? "jensen_bound" = .ok (.str geometryRow011_jensenBoundText) := by rfl

theorem geometryRow011_jensenBound_numerator_no_slash :
    geometryRow011_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow011_jensenBoundNumeratorChars = some (223562108667815707730188999323390105589731502361867801588872766469015047862986877937106634670080000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow011_jensenBoundDenominatorChars = some (3103992067569844229603920044514948401717718014841683154717659547619856733683003727040656524071717466921486611598053624735219663 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_nonzero : (3103992067569844229603920044514948401717718014841683154717659547619856733683003727040656524071717466921486611598053624735219663 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_jensenBound_parse :
    parseRational geometryRow011_jensenBoundText = .ok geometryRowsTyped011.jensenBound :=
  original_rational_fraction_of_chars geometryRow011_jensenBoundNumeratorChars geometryRow011_jensenBoundDenominatorChars
    (223562108667815707730188999323390105589731502361867801588872766469015047862986877937106634670080000000000000000000000 : Int) (3103992067569844229603920044514948401717718014841683154717659547619856733683003727040656524071717466921486611598053624735219663 : Int)
    geometryRow011_jensenBound_numerator_no_slash geometryRow011_jensenBound_numerator_parse
    geometryRow011_jensenBound_denominator_parse geometryRow011_jensenBound_denominator_nonzero

theorem geometryRow011_jensenBound_read :
    rationalField geometryRowsJson011 "jensen_bound" = .ok geometryRowsTyped011.jensenBound :=
  original_rationalField_of_string geometryRowsJson011 "jensen_bound" geometryRow011_jensenBoundText
    geometryRowsTyped011.jensenBound geometryRow011_jensenBound_field geometryRow011_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_factorMaxima_before"
  err.flush

theorem geometryRow011_factorMaxima_read :
    rationalArrayField geometryRowsJson011 "factor_maxima" = .ok geometryRowsTyped011.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_gapWeightedMeans_before"
  err.flush

theorem geometryRow011_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson011 "gap_weighted_means" = .ok geometryRowsTyped011.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow011_floorChars : List Char := ['5', '7', '0', '6', '3', '3', '3', '8', '7', '3', '2', '7', '9', '7', '1', '0', '7', '2', '8']
noncomputable def geometryRow011_floorText : String := String.ofList geometryRow011_floorChars

theorem geometryRow011_floor_text_read :
    geometryRowsJson011.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow011_floorText := by rfl

theorem geometryRow011_floor_chars_parse :
    SourceJson.intChars geometryRow011_floorChars = some (5706333873279710728 : Int) := by decide +kernel

theorem geometryRow011_floor_parse :
    parseInteger geometryRow011_floorText = .ok geometryRowsTyped011.jensenFloorQ96 := by
  simp only [geometryRow011_floorText, parseInteger, String.toList_ofList, geometryRow011_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_011 :
    decodeGeometryRow geometryRowsJson011 = .ok geometryRowsTyped011 :=
  original_geometryRow_of_fields geometryRowsJson011 geometryRowsTyped011 geometryRow011_floorText
    geometryRow011_simplexId_read geometryRow011_vertexIds_read
    geometryRow011_physicalVolume_read geometryRow011_meanGap_read
    geometryRow011_factorMaxima_read geometryRow011_gapWeightedMeans_read
    geometryRow011_jensenBound_read geometryRow011_floor_text_read geometryRow011_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_011_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock005 : List SourceJson := [geometryRowsJson010, geometryRowsJson011]
noncomputable def geometryRowsTypedBlock005 : List (GeometryRow) := [geometryRowsTyped010, geometryRowsTyped011]
noncomputable def geometryRowsTypedThroughBlock005 : List (GeometryRow) := geometryRowsTypedThroughBlock004 ++ geometryRowsTypedBlock005

theorem geometry_Rows_block_005_push_eq (acc : List SourceJson) :
    SimplicesBlock005.blockPush acc = [geometryRowsJson011, geometryRowsJson010] ++ acc := by rfl

theorem geometry_Rows_block_005_reverse (acc : List SourceJson) :
    (SimplicesBlock005.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock005 := by
  rw [geometry_Rows_block_005_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_005 :
    geometryRowsJsonBlock005.mapM decodeGeometryRow = .ok geometryRowsTypedBlock005 := by
  simp only [geometryRowsJsonBlock005, geometryRowsTypedBlock005, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_010, decode_geometry_Rows_011]
  rfl

theorem decode_geometry_Rows_through_block_005 :
    SimplicesValue.arrayAcc006.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock005 := by
  change (SimplicesBlock005.blockPush SimplicesValue.arrayAcc005).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_005_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_004, decode_geometry_Rows_block_005]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_005_complete"
  err.flush

#print axioms geometryRow010_simplexId_read
#print axioms geometryRow010_vertexIds_read
#print axioms geometryRow010_physicalVolume_field
#print axioms geometryRow010_physicalVolume_numerator_no_slash
#print axioms geometryRow010_physicalVolume_numerator_parse
#print axioms geometryRow010_physicalVolume_denominator_parse
#print axioms geometryRow010_physicalVolume_denominator_nonzero
#print axioms geometryRow010_physicalVolume_parse
#print axioms geometryRow010_physicalVolume_read
#print axioms geometryRow010_meanGap_field
#print axioms geometryRow010_meanGap_numerator_no_slash
#print axioms geometryRow010_meanGap_numerator_parse
#print axioms geometryRow010_meanGap_denominator_parse
#print axioms geometryRow010_meanGap_denominator_nonzero
#print axioms geometryRow010_meanGap_parse
#print axioms geometryRow010_meanGap_read
#print axioms geometryRow010_jensenBound_field
#print axioms geometryRow010_jensenBound_numerator_no_slash
#print axioms geometryRow010_jensenBound_numerator_parse
#print axioms geometryRow010_jensenBound_denominator_parse
#print axioms geometryRow010_jensenBound_denominator_nonzero
#print axioms geometryRow010_jensenBound_parse
#print axioms geometryRow010_jensenBound_read
#print axioms geometryRow010_factorMaxima_read
#print axioms geometryRow010_gapWeightedMeans_read
#print axioms geometryRow010_floor_text_read
#print axioms geometryRow010_floor_chars_parse
#print axioms geometryRow010_floor_parse
#print axioms decode_geometry_Rows_010
#print axioms geometryRow011_simplexId_read
#print axioms geometryRow011_vertexIds_read
#print axioms geometryRow011_physicalVolume_field
#print axioms geometryRow011_physicalVolume_numerator_no_slash
#print axioms geometryRow011_physicalVolume_numerator_parse
#print axioms geometryRow011_physicalVolume_denominator_parse
#print axioms geometryRow011_physicalVolume_denominator_nonzero
#print axioms geometryRow011_physicalVolume_parse
#print axioms geometryRow011_physicalVolume_read
#print axioms geometryRow011_meanGap_field
#print axioms geometryRow011_meanGap_numerator_no_slash
#print axioms geometryRow011_meanGap_numerator_parse
#print axioms geometryRow011_meanGap_denominator_parse
#print axioms geometryRow011_meanGap_denominator_nonzero
#print axioms geometryRow011_meanGap_parse
#print axioms geometryRow011_meanGap_read
#print axioms geometryRow011_jensenBound_field
#print axioms geometryRow011_jensenBound_numerator_no_slash
#print axioms geometryRow011_jensenBound_numerator_parse
#print axioms geometryRow011_jensenBound_denominator_parse
#print axioms geometryRow011_jensenBound_denominator_nonzero
#print axioms geometryRow011_jensenBound_parse
#print axioms geometryRow011_jensenBound_read
#print axioms geometryRow011_factorMaxima_read
#print axioms geometryRow011_gapWeightedMeans_read
#print axioms geometryRow011_floor_text_read
#print axioms geometryRow011_floor_chars_parse
#print axioms geometryRow011_floor_parse
#print axioms decode_geometry_Rows_011
#print axioms geometry_Rows_block_005_push_eq
#print axioms geometry_Rows_block_005_reverse
#print axioms decode_geometry_Rows_block_005
#print axioms decode_geometry_Rows_through_block_005

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
