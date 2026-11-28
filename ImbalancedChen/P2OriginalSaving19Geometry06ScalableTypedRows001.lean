import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock001

/-! Local typed certificates for original cell 06, rows 8 through 15.
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

noncomputable def geometryRowsJson008 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped008 : GeometryRow :=
  { simplexId := 8,
    vertexIds := #[32, 20, 18, 16, 14, 12, 3, 1, 0],
    physicalVolume := ((13469431177770969002362404505206165518891791 : ℚ) / (264382596985651200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((24277423 : ℚ) / (10864218750 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((391240683581949582976393 : ℚ) / (4342972585231526400000000 : ℚ)), ((4111092213463186604219 : ℚ) / (44316046788076800000000 : ℚ)), ((496327987830539403258779 : ℚ) / (4342972585231526400000000 : ℚ)), ((75671992558684923402151 : ℚ) / (868594517046305280000000 : ℚ)), ((124800639977411632516609 : ℚ) / (1447657528410508800000000 : ℚ)), ((29712294347140650375233 : ℚ) / (394815689566502400000000 : ℚ)), ((30121702978515581226263 : ℚ) / (789631379133004800000000 : ℚ)), ((28403352454245759199883 : ℚ) / (789631379133004800000000 : ℚ)), ((13885899176932072150099 : ℚ) / (394815689566502400000000 : ℚ)), ((480508223323709720323 : ℚ) / (14772015596025600000000 : ℚ))],
    jensenBound := ((69673382961452790893280813630001075361444069139226259078851736723954516587251966173944478327625775539405208723455349668354142111190172753550747058053497232865728388388019917088660641546240000000000000000000000 : ℚ) / (129650169123113471641515250135583433343767712742596674186087646636893246626878915718779196073589531878920413778526424448570537766825982163417530958863255122167463734774036486845031676545858011708398394530146230557033243061 : ℚ)),
    jensenFloorQ96 := (42576836926041919 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_simplexId_before"
  err.flush

theorem geometryRow008_simplexId_read :
    geometryRowsJson008.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped008.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_vertexIds_before"
  err.flush

theorem geometryRow008_vertexIds_read :
    geometryRowsJson008.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped008.vertexIds := by decide +kernel

noncomputable def geometryRow008_physicalVolumeNumeratorChars : List Char := ['1', '3', '4', '6', '9', '4', '3', '1', '1', '7', '7', '7', '7', '0', '9', '6', '9', '0', '0', '2', '3', '6', '2', '4', '0', '4', '5', '0', '5', '2', '0', '6', '1', '6', '5', '5', '1', '8', '8', '9', '1', '7', '9', '1']
noncomputable def geometryRow008_physicalVolumeDenominatorChars : List Char := ['2', '6', '4', '3', '8', '2', '5', '9', '6', '9', '8', '5', '6', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_physicalVolumeText : String := String.ofList (geometryRow008_physicalVolumeNumeratorChars ++ '/' :: geometryRow008_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_physicalVolume_before_field"
  err.flush

theorem geometryRow008_physicalVolume_field :
    geometryRowsJson008.getObjVal? "physical_volume" = .ok (.str geometryRow008_physicalVolumeText) := by rfl

theorem geometryRow008_physicalVolume_numerator_no_slash :
    geometryRow008_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeNumeratorChars = some (13469431177770969002362404505206165518891791 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeDenominatorChars = some (264382596985651200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_nonzero : (264382596985651200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_physicalVolume_parse :
    parseRational geometryRow008_physicalVolumeText = .ok geometryRowsTyped008.physicalVolume :=
  original_rational_fraction_of_chars geometryRow008_physicalVolumeNumeratorChars geometryRow008_physicalVolumeDenominatorChars
    (13469431177770969002362404505206165518891791 : Int) (264382596985651200000000000000000000000000000000000000000000000000 : Int)
    geometryRow008_physicalVolume_numerator_no_slash geometryRow008_physicalVolume_numerator_parse
    geometryRow008_physicalVolume_denominator_parse geometryRow008_physicalVolume_denominator_nonzero

theorem geometryRow008_physicalVolume_read :
    rationalField geometryRowsJson008 "physical_volume" = .ok geometryRowsTyped008.physicalVolume :=
  original_rationalField_of_string geometryRowsJson008 "physical_volume" geometryRow008_physicalVolumeText
    geometryRowsTyped008.physicalVolume geometryRow008_physicalVolume_field geometryRow008_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_physicalVolume_complete"
  err.flush

noncomputable def geometryRow008_meanGapNumeratorChars : List Char := ['2', '4', '2', '7', '7', '4', '2', '3']
noncomputable def geometryRow008_meanGapDenominatorChars : List Char := ['1', '0', '8', '6', '4', '2', '1', '8', '7', '5', '0']
noncomputable def geometryRow008_meanGapText : String := String.ofList (geometryRow008_meanGapNumeratorChars ++ '/' :: geometryRow008_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_meanGap_before_field"
  err.flush

theorem geometryRow008_meanGap_field :
    geometryRowsJson008.getObjVal? "mean_gap" = .ok (.str geometryRow008_meanGapText) := by rfl

theorem geometryRow008_meanGap_numerator_no_slash :
    geometryRow008_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_meanGap_numerator_parse :
    SourceJson.intChars geometryRow008_meanGapNumeratorChars = some (24277423 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_parse :
    SourceJson.intChars geometryRow008_meanGapDenominatorChars = some (10864218750 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_nonzero : (10864218750 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_meanGap_parse :
    parseRational geometryRow008_meanGapText = .ok geometryRowsTyped008.meanGap :=
  original_rational_fraction_of_chars geometryRow008_meanGapNumeratorChars geometryRow008_meanGapDenominatorChars
    (24277423 : Int) (10864218750 : Int)
    geometryRow008_meanGap_numerator_no_slash geometryRow008_meanGap_numerator_parse
    geometryRow008_meanGap_denominator_parse geometryRow008_meanGap_denominator_nonzero

theorem geometryRow008_meanGap_read :
    rationalField geometryRowsJson008 "mean_gap" = .ok geometryRowsTyped008.meanGap :=
  original_rationalField_of_string geometryRowsJson008 "mean_gap" geometryRow008_meanGapText
    geometryRowsTyped008.meanGap geometryRow008_meanGap_field geometryRow008_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_meanGap_complete"
  err.flush

noncomputable def geometryRow008_jensenBoundNumeratorChars : List Char := ['6', '9', '6', '7', '3', '3', '8', '2', '9', '6', '1', '4', '5', '2', '7', '9', '0', '8', '9', '3', '2', '8', '0', '8', '1', '3', '6', '3', '0', '0', '0', '1', '0', '7', '5', '3', '6', '1', '4', '4', '4', '0', '6', '9', '1', '3', '9', '2', '2', '6', '2', '5', '9', '0', '7', '8', '8', '5', '1', '7', '3', '6', '7', '2', '3', '9', '5', '4', '5', '1', '6', '5', '8', '7', '2', '5', '1', '9', '6', '6', '1', '7', '3', '9', '4', '4', '4', '7', '8', '3', '2', '7', '6', '2', '5', '7', '7', '5', '5', '3', '9', '4', '0', '5', '2', '0', '8', '7', '2', '3', '4', '5', '5', '3', '4', '9', '6', '6', '8', '3', '5', '4', '1', '4', '2', '1', '1', '1', '1', '9', '0', '1', '7', '2', '7', '5', '3', '5', '5', '0', '7', '4', '7', '0', '5', '8', '0', '5', '3', '4', '9', '7', '2', '3', '2', '8', '6', '5', '7', '2', '8', '3', '8', '8', '3', '8', '8', '0', '1', '9', '9', '1', '7', '0', '8', '8', '6', '6', '0', '6', '4', '1', '5', '4', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_jensenBoundDenominatorChars : List Char := ['1', '2', '9', '6', '5', '0', '1', '6', '9', '1', '2', '3', '1', '1', '3', '4', '7', '1', '6', '4', '1', '5', '1', '5', '2', '5', '0', '1', '3', '5', '5', '8', '3', '4', '3', '3', '3', '4', '3', '7', '6', '7', '7', '1', '2', '7', '4', '2', '5', '9', '6', '6', '7', '4', '1', '8', '6', '0', '8', '7', '6', '4', '6', '6', '3', '6', '8', '9', '3', '2', '4', '6', '6', '2', '6', '8', '7', '8', '9', '1', '5', '7', '1', '8', '7', '7', '9', '1', '9', '6', '0', '7', '3', '5', '8', '9', '5', '3', '1', '8', '7', '8', '9', '2', '0', '4', '1', '3', '7', '7', '8', '5', '2', '6', '4', '2', '4', '4', '4', '8', '5', '7', '0', '5', '3', '7', '7', '6', '6', '8', '2', '5', '9', '8', '2', '1', '6', '3', '4', '1', '7', '5', '3', '0', '9', '5', '8', '8', '6', '3', '2', '5', '5', '1', '2', '2', '1', '6', '7', '4', '6', '3', '7', '3', '4', '7', '7', '4', '0', '3', '6', '4', '8', '6', '8', '4', '5', '0', '3', '1', '6', '7', '6', '5', '4', '5', '8', '5', '8', '0', '1', '1', '7', '0', '8', '3', '9', '8', '3', '9', '4', '5', '3', '0', '1', '4', '6', '2', '3', '0', '5', '5', '7', '0', '3', '3', '2', '4', '3', '0', '6', '1']
noncomputable def geometryRow008_jensenBoundText : String := String.ofList (geometryRow008_jensenBoundNumeratorChars ++ '/' :: geometryRow008_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_jensenBound_before_field"
  err.flush

theorem geometryRow008_jensenBound_field :
    geometryRowsJson008.getObjVal? "jensen_bound" = .ok (.str geometryRow008_jensenBoundText) := by rfl

theorem geometryRow008_jensenBound_numerator_no_slash :
    geometryRow008_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow008_jensenBoundNumeratorChars = some (69673382961452790893280813630001075361444069139226259078851736723954516587251966173944478327625775539405208723455349668354142111190172753550747058053497232865728388388019917088660641546240000000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow008_jensenBoundDenominatorChars = some (129650169123113471641515250135583433343767712742596674186087646636893246626878915718779196073589531878920413778526424448570537766825982163417530958863255122167463734774036486845031676545858011708398394530146230557033243061 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_nonzero : (129650169123113471641515250135583433343767712742596674186087646636893246626878915718779196073589531878920413778526424448570537766825982163417530958863255122167463734774036486845031676545858011708398394530146230557033243061 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_jensenBound_parse :
    parseRational geometryRow008_jensenBoundText = .ok geometryRowsTyped008.jensenBound :=
  original_rational_fraction_of_chars geometryRow008_jensenBoundNumeratorChars geometryRow008_jensenBoundDenominatorChars
    (69673382961452790893280813630001075361444069139226259078851736723954516587251966173944478327625775539405208723455349668354142111190172753550747058053497232865728388388019917088660641546240000000000000000000000 : Int) (129650169123113471641515250135583433343767712742596674186087646636893246626878915718779196073589531878920413778526424448570537766825982163417530958863255122167463734774036486845031676545858011708398394530146230557033243061 : Int)
    geometryRow008_jensenBound_numerator_no_slash geometryRow008_jensenBound_numerator_parse
    geometryRow008_jensenBound_denominator_parse geometryRow008_jensenBound_denominator_nonzero

theorem geometryRow008_jensenBound_read :
    rationalField geometryRowsJson008 "jensen_bound" = .ok geometryRowsTyped008.jensenBound :=
  original_rationalField_of_string geometryRowsJson008 "jensen_bound" geometryRow008_jensenBoundText
    geometryRowsTyped008.jensenBound geometryRow008_jensenBound_field geometryRow008_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_factorMaxima_before"
  err.flush

theorem geometryRow008_factorMaxima_read :
    rationalArrayField geometryRowsJson008 "factor_maxima" = .ok geometryRowsTyped008.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_gapWeightedMeans_before"
  err.flush

theorem geometryRow008_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson008 "gap_weighted_means" = .ok geometryRowsTyped008.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow008_floorChars : List Char := ['4', '2', '5', '7', '6', '8', '3', '6', '9', '2', '6', '0', '4', '1', '9', '1', '9']
noncomputable def geometryRow008_floorText : String := String.ofList geometryRow008_floorChars

theorem geometryRow008_floor_text_read :
    geometryRowsJson008.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow008_floorText := by rfl

theorem geometryRow008_floor_chars_parse :
    SourceJson.intChars geometryRow008_floorChars = some (42576836926041919 : Int) := by decide +kernel

theorem geometryRow008_floor_parse :
    parseInteger geometryRow008_floorText = .ok geometryRowsTyped008.jensenFloorQ96 := by
  simp only [geometryRow008_floorText, parseInteger, String.toList_ofList, geometryRow008_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_008 :
    decodeGeometryRow geometryRowsJson008 = .ok geometryRowsTyped008 :=
  original_geometryRow_of_fields geometryRowsJson008 geometryRowsTyped008 geometryRow008_floorText
    geometryRow008_simplexId_read geometryRow008_vertexIds_read
    geometryRow008_physicalVolume_read geometryRow008_meanGap_read
    geometryRow008_factorMaxima_read geometryRow008_gapWeightedMeans_read
    geometryRow008_jensenBound_read geometryRow008_floor_text_read geometryRow008_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_008_original_decoder_complete"
  err.flush

theorem geometryRow008_shape :
    geometryRowsTyped008.simplexId = 8 ∧
    geometryRowsTyped008.vertexIds.size = 9 ∧ geometryRowsTyped008.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped008.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped008.factorMaxima.size = 10 ∧ geometryRowsTyped008.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson009 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped009 : GeometryRow :=
  { simplexId := 9,
    vertexIds := #[32, 20, 18, 16, 14, 12, 10, 1, 0],
    physicalVolume := ((11282683037352997061722176798170215156183 : ℚ) / (634057100328960000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1687402082422037579099 : ℚ) / (18638714667157200000000 : ℚ)), ((246369306718778141873 : ℚ) / (2662673523879600000000 : ℚ)), ((4275748540280667522179 : ℚ) / (37277429334314400000000 : ℚ)), ((642994720065428191057 : ℚ) / (7455485866862880000000 : ℚ)), ((1060333391034380552699 : ℚ) / (12425809778104800000000 : ℚ)), ((258270995623808922623 : ℚ) / (3388857212210400000000 : ℚ)), ((67125026046604027697 : ℚ) / (1694428606105200000000 : ℚ)), ((60080210467761754247 : ℚ) / (1694428606105200000000 : ℚ)), ((59157955738439969927 : ℚ) / (1694428606105200000000 : ℚ)), ((28799565553567448851 : ℚ) / (887557841293200000000 : ℚ))],
    jensenBound := ((1844577215885894632550277075777629891065495153528416957563840639320630719289867737302255423545341787442367067618284253061285483046211817242197586189580260164347293286400000000000000000000 : ℚ) / (15039098002172544751431612559412501905561227324019985311445761659164557347243694046838939770576476645155582142053992917206782723912895777936583824224379884170329363270220710078054337834483328227486133537 : ℚ)),
    jensenFloorQ96 := (9717501901324 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_simplexId_before"
  err.flush

theorem geometryRow009_simplexId_read :
    geometryRowsJson009.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped009.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_vertexIds_before"
  err.flush

theorem geometryRow009_vertexIds_read :
    geometryRowsJson009.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped009.vertexIds := by decide +kernel

noncomputable def geometryRow009_physicalVolumeNumeratorChars : List Char := ['1', '1', '2', '8', '2', '6', '8', '3', '0', '3', '7', '3', '5', '2', '9', '9', '7', '0', '6', '1', '7', '2', '2', '1', '7', '6', '7', '9', '8', '1', '7', '0', '2', '1', '5', '1', '5', '6', '1', '8', '3']
noncomputable def geometryRow009_physicalVolumeDenominatorChars : List Char := ['6', '3', '4', '0', '5', '7', '1', '0', '0', '3', '2', '8', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_physicalVolumeText : String := String.ofList (geometryRow009_physicalVolumeNumeratorChars ++ '/' :: geometryRow009_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_physicalVolume_before_field"
  err.flush

theorem geometryRow009_physicalVolume_field :
    geometryRowsJson009.getObjVal? "physical_volume" = .ok (.str geometryRow009_physicalVolumeText) := by rfl

theorem geometryRow009_physicalVolume_numerator_no_slash :
    geometryRow009_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeNumeratorChars = some (11282683037352997061722176798170215156183 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeDenominatorChars = some (634057100328960000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_nonzero : (634057100328960000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_physicalVolume_parse :
    parseRational geometryRow009_physicalVolumeText = .ok geometryRowsTyped009.physicalVolume :=
  original_rational_fraction_of_chars geometryRow009_physicalVolumeNumeratorChars geometryRow009_physicalVolumeDenominatorChars
    (11282683037352997061722176798170215156183 : Int) (634057100328960000000000000000000000000000000000000000000000000000 : Int)
    geometryRow009_physicalVolume_numerator_no_slash geometryRow009_physicalVolume_numerator_parse
    geometryRow009_physicalVolume_denominator_parse geometryRow009_physicalVolume_denominator_nonzero

theorem geometryRow009_physicalVolume_read :
    rationalField geometryRowsJson009 "physical_volume" = .ok geometryRowsTyped009.physicalVolume :=
  original_rationalField_of_string geometryRowsJson009 "physical_volume" geometryRow009_physicalVolumeText
    geometryRowsTyped009.physicalVolume geometryRow009_physicalVolume_field geometryRow009_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_physicalVolume_complete"
  err.flush

noncomputable def geometryRow009_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow009_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_meanGapText : String := String.ofList (geometryRow009_meanGapNumeratorChars ++ '/' :: geometryRow009_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_meanGap_before_field"
  err.flush

theorem geometryRow009_meanGap_field :
    geometryRowsJson009.getObjVal? "mean_gap" = .ok (.str geometryRow009_meanGapText) := by rfl

theorem geometryRow009_meanGap_numerator_no_slash :
    geometryRow009_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_meanGap_numerator_parse :
    SourceJson.intChars geometryRow009_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_parse :
    SourceJson.intChars geometryRow009_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_meanGap_parse :
    parseRational geometryRow009_meanGapText = .ok geometryRowsTyped009.meanGap :=
  original_rational_fraction_of_chars geometryRow009_meanGapNumeratorChars geometryRow009_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow009_meanGap_numerator_no_slash geometryRow009_meanGap_numerator_parse
    geometryRow009_meanGap_denominator_parse geometryRow009_meanGap_denominator_nonzero

theorem geometryRow009_meanGap_read :
    rationalField geometryRowsJson009 "mean_gap" = .ok geometryRowsTyped009.meanGap :=
  original_rationalField_of_string geometryRowsJson009 "mean_gap" geometryRow009_meanGapText
    geometryRowsTyped009.meanGap geometryRow009_meanGap_field geometryRow009_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_meanGap_complete"
  err.flush

noncomputable def geometryRow009_jensenBoundNumeratorChars : List Char := ['1', '8', '4', '4', '5', '7', '7', '2', '1', '5', '8', '8', '5', '8', '9', '4', '6', '3', '2', '5', '5', '0', '2', '7', '7', '0', '7', '5', '7', '7', '7', '6', '2', '9', '8', '9', '1', '0', '6', '5', '4', '9', '5', '1', '5', '3', '5', '2', '8', '4', '1', '6', '9', '5', '7', '5', '6', '3', '8', '4', '0', '6', '3', '9', '3', '2', '0', '6', '3', '0', '7', '1', '9', '2', '8', '9', '8', '6', '7', '7', '3', '7', '3', '0', '2', '2', '5', '5', '4', '2', '3', '5', '4', '5', '3', '4', '1', '7', '8', '7', '4', '4', '2', '3', '6', '7', '0', '6', '7', '6', '1', '8', '2', '8', '4', '2', '5', '3', '0', '6', '1', '2', '8', '5', '4', '8', '3', '0', '4', '6', '2', '1', '1', '8', '1', '7', '2', '4', '2', '1', '9', '7', '5', '8', '6', '1', '8', '9', '5', '8', '0', '2', '6', '0', '1', '6', '4', '3', '4', '7', '2', '9', '3', '2', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_jensenBoundDenominatorChars : List Char := ['1', '5', '0', '3', '9', '0', '9', '8', '0', '0', '2', '1', '7', '2', '5', '4', '4', '7', '5', '1', '4', '3', '1', '6', '1', '2', '5', '5', '9', '4', '1', '2', '5', '0', '1', '9', '0', '5', '5', '6', '1', '2', '2', '7', '3', '2', '4', '0', '1', '9', '9', '8', '5', '3', '1', '1', '4', '4', '5', '7', '6', '1', '6', '5', '9', '1', '6', '4', '5', '5', '7', '3', '4', '7', '2', '4', '3', '6', '9', '4', '0', '4', '6', '8', '3', '8', '9', '3', '9', '7', '7', '0', '5', '7', '6', '4', '7', '6', '6', '4', '5', '1', '5', '5', '5', '8', '2', '1', '4', '2', '0', '5', '3', '9', '9', '2', '9', '1', '7', '2', '0', '6', '7', '8', '2', '7', '2', '3', '9', '1', '2', '8', '9', '5', '7', '7', '7', '9', '3', '6', '5', '8', '3', '8', '2', '4', '2', '2', '4', '3', '7', '9', '8', '8', '4', '1', '7', '0', '3', '2', '9', '3', '6', '3', '2', '7', '0', '2', '2', '0', '7', '1', '0', '0', '7', '8', '0', '5', '4', '3', '3', '7', '8', '3', '4', '4', '8', '3', '3', '2', '8', '2', '2', '7', '4', '8', '6', '1', '3', '3', '5', '3', '7']
noncomputable def geometryRow009_jensenBoundText : String := String.ofList (geometryRow009_jensenBoundNumeratorChars ++ '/' :: geometryRow009_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_jensenBound_before_field"
  err.flush

theorem geometryRow009_jensenBound_field :
    geometryRowsJson009.getObjVal? "jensen_bound" = .ok (.str geometryRow009_jensenBoundText) := by rfl

theorem geometryRow009_jensenBound_numerator_no_slash :
    geometryRow009_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow009_jensenBoundNumeratorChars = some (1844577215885894632550277075777629891065495153528416957563840639320630719289867737302255423545341787442367067618284253061285483046211817242197586189580260164347293286400000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow009_jensenBoundDenominatorChars = some (15039098002172544751431612559412501905561227324019985311445761659164557347243694046838939770576476645155582142053992917206782723912895777936583824224379884170329363270220710078054337834483328227486133537 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_nonzero : (15039098002172544751431612559412501905561227324019985311445761659164557347243694046838939770576476645155582142053992917206782723912895777936583824224379884170329363270220710078054337834483328227486133537 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_jensenBound_parse :
    parseRational geometryRow009_jensenBoundText = .ok geometryRowsTyped009.jensenBound :=
  original_rational_fraction_of_chars geometryRow009_jensenBoundNumeratorChars geometryRow009_jensenBoundDenominatorChars
    (1844577215885894632550277075777629891065495153528416957563840639320630719289867737302255423545341787442367067618284253061285483046211817242197586189580260164347293286400000000000000000000 : Int) (15039098002172544751431612559412501905561227324019985311445761659164557347243694046838939770576476645155582142053992917206782723912895777936583824224379884170329363270220710078054337834483328227486133537 : Int)
    geometryRow009_jensenBound_numerator_no_slash geometryRow009_jensenBound_numerator_parse
    geometryRow009_jensenBound_denominator_parse geometryRow009_jensenBound_denominator_nonzero

theorem geometryRow009_jensenBound_read :
    rationalField geometryRowsJson009 "jensen_bound" = .ok geometryRowsTyped009.jensenBound :=
  original_rationalField_of_string geometryRowsJson009 "jensen_bound" geometryRow009_jensenBoundText
    geometryRowsTyped009.jensenBound geometryRow009_jensenBound_field geometryRow009_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_factorMaxima_before"
  err.flush

theorem geometryRow009_factorMaxima_read :
    rationalArrayField geometryRowsJson009 "factor_maxima" = .ok geometryRowsTyped009.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_gapWeightedMeans_before"
  err.flush

theorem geometryRow009_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson009 "gap_weighted_means" = .ok geometryRowsTyped009.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow009_floorChars : List Char := ['9', '7', '1', '7', '5', '0', '1', '9', '0', '1', '3', '2', '4']
noncomputable def geometryRow009_floorText : String := String.ofList geometryRow009_floorChars

theorem geometryRow009_floor_text_read :
    geometryRowsJson009.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow009_floorText := by rfl

theorem geometryRow009_floor_chars_parse :
    SourceJson.intChars geometryRow009_floorChars = some (9717501901324 : Int) := by decide +kernel

theorem geometryRow009_floor_parse :
    parseInteger geometryRow009_floorText = .ok geometryRowsTyped009.jensenFloorQ96 := by
  simp only [geometryRow009_floorText, parseInteger, String.toList_ofList, geometryRow009_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_009 :
    decodeGeometryRow geometryRowsJson009 = .ok geometryRowsTyped009 :=
  original_geometryRow_of_fields geometryRowsJson009 geometryRowsTyped009 geometryRow009_floorText
    geometryRow009_simplexId_read geometryRow009_vertexIds_read
    geometryRow009_physicalVolume_read geometryRow009_meanGap_read
    geometryRow009_factorMaxima_read geometryRow009_gapWeightedMeans_read
    geometryRow009_jensenBound_read geometryRow009_floor_text_read geometryRow009_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_009_original_decoder_complete"
  err.flush

theorem geometryRow009_shape :
    geometryRowsTyped009.simplexId = 9 ∧
    geometryRowsTyped009.vertexIds.size = 9 ∧ geometryRowsTyped009.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped009.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped009.factorMaxima.size = 10 ∧ geometryRowsTyped009.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson010 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped010 : GeometryRow :=
  { simplexId := 10,
    vertexIds := #[32, 20, 18, 16, 14, 12, 10, 8, 0],
    physicalVolume := ((249672631113860714933138537509456894597963 : ℚ) / (1397513608888320000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1668542470813 : ℚ) / (18572400000000 : ℚ)), ((1693072913617 : ℚ) / (18572400000000 : ℚ)), ((12806312553959 : ℚ) / (111434400000000 : ℚ)), ((1907163770621 : ℚ) / (22286880000000 : ℚ)), ((9434261193517 : ℚ) / (111434400000000 : ℚ)), ((783468913043 : ℚ) / (10130400000000 : ℚ)), ((202873997057 : ℚ) / (5065200000000 : ℚ)), ((183090278597 : ℚ) / (5065200000000 : ℚ)), ((180333358277 : ℚ) / (5065200000000 : ℚ)), ((1782540941651 : ℚ) / (55717200000000 : ℚ))],
    jensenBound := ((3671717839104801733797814593102506134978615105043018186422748263847005892499304448102400000000000000000000 : ℚ) / (6089223750973766009015955043788912091901122043930819784843971565072433177772320718876976823352252208987898899790061873987 : ℚ)),
    jensenFloorQ96 := (47773487978102 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_simplexId_before"
  err.flush

theorem geometryRow010_simplexId_read :
    geometryRowsJson010.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped010.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_vertexIds_before"
  err.flush

theorem geometryRow010_vertexIds_read :
    geometryRowsJson010.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped010.vertexIds := by decide +kernel

noncomputable def geometryRow010_physicalVolumeNumeratorChars : List Char := ['2', '4', '9', '6', '7', '2', '6', '3', '1', '1', '1', '3', '8', '6', '0', '7', '1', '4', '9', '3', '3', '1', '3', '8', '5', '3', '7', '5', '0', '9', '4', '5', '6', '8', '9', '4', '5', '9', '7', '9', '6', '3']
noncomputable def geometryRow010_physicalVolumeDenominatorChars : List Char := ['1', '3', '9', '7', '5', '1', '3', '6', '0', '8', '8', '8', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_physicalVolumeText : String := String.ofList (geometryRow010_physicalVolumeNumeratorChars ++ '/' :: geometryRow010_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_physicalVolume_before_field"
  err.flush

theorem geometryRow010_physicalVolume_field :
    geometryRowsJson010.getObjVal? "physical_volume" = .ok (.str geometryRow010_physicalVolumeText) := by rfl

theorem geometryRow010_physicalVolume_numerator_no_slash :
    geometryRow010_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeNumeratorChars = some (249672631113860714933138537509456894597963 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow010_physicalVolumeDenominatorChars = some (1397513608888320000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_physicalVolume_denominator_nonzero : (1397513608888320000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_physicalVolume_parse :
    parseRational geometryRow010_physicalVolumeText = .ok geometryRowsTyped010.physicalVolume :=
  original_rational_fraction_of_chars geometryRow010_physicalVolumeNumeratorChars geometryRow010_physicalVolumeDenominatorChars
    (249672631113860714933138537509456894597963 : Int) (1397513608888320000000000000000000000000000000000000000000000000000 : Int)
    geometryRow010_physicalVolume_numerator_no_slash geometryRow010_physicalVolume_numerator_parse
    geometryRow010_physicalVolume_denominator_parse geometryRow010_physicalVolume_denominator_nonzero

theorem geometryRow010_physicalVolume_read :
    rationalField geometryRowsJson010 "physical_volume" = .ok geometryRowsTyped010.physicalVolume :=
  original_rationalField_of_string geometryRowsJson010 "physical_volume" geometryRow010_physicalVolumeText
    geometryRowsTyped010.physicalVolume geometryRow010_physicalVolume_field geometryRow010_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_physicalVolume_complete"
  err.flush

noncomputable def geometryRow010_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow010_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_meanGapText : String := String.ofList (geometryRow010_meanGapNumeratorChars ++ '/' :: geometryRow010_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_meanGap_before_field"
  err.flush

theorem geometryRow010_meanGap_field :
    geometryRowsJson010.getObjVal? "mean_gap" = .ok (.str geometryRow010_meanGapText) := by rfl

theorem geometryRow010_meanGap_numerator_no_slash :
    geometryRow010_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_meanGap_numerator_parse :
    SourceJson.intChars geometryRow010_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_parse :
    SourceJson.intChars geometryRow010_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow010_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_meanGap_parse :
    parseRational geometryRow010_meanGapText = .ok geometryRowsTyped010.meanGap :=
  original_rational_fraction_of_chars geometryRow010_meanGapNumeratorChars geometryRow010_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow010_meanGap_numerator_no_slash geometryRow010_meanGap_numerator_parse
    geometryRow010_meanGap_denominator_parse geometryRow010_meanGap_denominator_nonzero

theorem geometryRow010_meanGap_read :
    rationalField geometryRowsJson010 "mean_gap" = .ok geometryRowsTyped010.meanGap :=
  original_rationalField_of_string geometryRowsJson010 "mean_gap" geometryRow010_meanGapText
    geometryRowsTyped010.meanGap geometryRow010_meanGap_field geometryRow010_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_meanGap_complete"
  err.flush

noncomputable def geometryRow010_jensenBoundNumeratorChars : List Char := ['3', '6', '7', '1', '7', '1', '7', '8', '3', '9', '1', '0', '4', '8', '0', '1', '7', '3', '3', '7', '9', '7', '8', '1', '4', '5', '9', '3', '1', '0', '2', '5', '0', '6', '1', '3', '4', '9', '7', '8', '6', '1', '5', '1', '0', '5', '0', '4', '3', '0', '1', '8', '1', '8', '6', '4', '2', '2', '7', '4', '8', '2', '6', '3', '8', '4', '7', '0', '0', '5', '8', '9', '2', '4', '9', '9', '3', '0', '4', '4', '4', '8', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow010_jensenBoundDenominatorChars : List Char := ['6', '0', '8', '9', '2', '2', '3', '7', '5', '0', '9', '7', '3', '7', '6', '6', '0', '0', '9', '0', '1', '5', '9', '5', '5', '0', '4', '3', '7', '8', '8', '9', '1', '2', '0', '9', '1', '9', '0', '1', '1', '2', '2', '0', '4', '3', '9', '3', '0', '8', '1', '9', '7', '8', '4', '8', '4', '3', '9', '7', '1', '5', '6', '5', '0', '7', '2', '4', '3', '3', '1', '7', '7', '7', '7', '2', '3', '2', '0', '7', '1', '8', '8', '7', '6', '9', '7', '6', '8', '2', '3', '3', '5', '2', '2', '5', '2', '2', '0', '8', '9', '8', '7', '8', '9', '8', '8', '9', '9', '7', '9', '0', '0', '6', '1', '8', '7', '3', '9', '8', '7']
noncomputable def geometryRow010_jensenBoundText : String := String.ofList (geometryRow010_jensenBoundNumeratorChars ++ '/' :: geometryRow010_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_jensenBound_before_field"
  err.flush

theorem geometryRow010_jensenBound_field :
    geometryRowsJson010.getObjVal? "jensen_bound" = .ok (.str geometryRow010_jensenBoundText) := by rfl

theorem geometryRow010_jensenBound_numerator_no_slash :
    geometryRow010_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow010_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow010_jensenBoundNumeratorChars = some (3671717839104801733797814593102506134978615105043018186422748263847005892499304448102400000000000000000000 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow010_jensenBoundDenominatorChars = some (6089223750973766009015955043788912091901122043930819784843971565072433177772320718876976823352252208987898899790061873987 : Int) := by decide +kernel

theorem geometryRow010_jensenBound_denominator_nonzero : (6089223750973766009015955043788912091901122043930819784843971565072433177772320718876976823352252208987898899790061873987 : Int) ≠ 0 := by decide +kernel

theorem geometryRow010_jensenBound_parse :
    parseRational geometryRow010_jensenBoundText = .ok geometryRowsTyped010.jensenBound :=
  original_rational_fraction_of_chars geometryRow010_jensenBoundNumeratorChars geometryRow010_jensenBoundDenominatorChars
    (3671717839104801733797814593102506134978615105043018186422748263847005892499304448102400000000000000000000 : Int) (6089223750973766009015955043788912091901122043930819784843971565072433177772320718876976823352252208987898899790061873987 : Int)
    geometryRow010_jensenBound_numerator_no_slash geometryRow010_jensenBound_numerator_parse
    geometryRow010_jensenBound_denominator_parse geometryRow010_jensenBound_denominator_nonzero

theorem geometryRow010_jensenBound_read :
    rationalField geometryRowsJson010 "jensen_bound" = .ok geometryRowsTyped010.jensenBound :=
  original_rationalField_of_string geometryRowsJson010 "jensen_bound" geometryRow010_jensenBoundText
    geometryRowsTyped010.jensenBound geometryRow010_jensenBound_field geometryRow010_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_factorMaxima_before"
  err.flush

theorem geometryRow010_factorMaxima_read :
    rationalArrayField geometryRowsJson010 "factor_maxima" = .ok geometryRowsTyped010.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_gapWeightedMeans_before"
  err.flush

theorem geometryRow010_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson010 "gap_weighted_means" = .ok geometryRowsTyped010.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow010_floorChars : List Char := ['4', '7', '7', '7', '3', '4', '8', '7', '9', '7', '8', '1', '0', '2']
noncomputable def geometryRow010_floorText : String := String.ofList geometryRow010_floorChars

theorem geometryRow010_floor_text_read :
    geometryRowsJson010.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow010_floorText := by rfl

theorem geometryRow010_floor_chars_parse :
    SourceJson.intChars geometryRow010_floorChars = some (47773487978102 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_010_original_decoder_complete"
  err.flush

theorem geometryRow010_shape :
    geometryRowsTyped010.simplexId = 10 ∧
    geometryRowsTyped010.vertexIds.size = 9 ∧ geometryRowsTyped010.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped010.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped010.factorMaxima.size = 10 ∧ geometryRowsTyped010.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson011 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped011 : GeometryRow :=
  { simplexId := 11,
    vertexIds := #[32, 20, 18, 16, 14, 12, 11, 3, 0],
    physicalVolume := ((7478166877373648705567194055259178679558107 : ℚ) / (12589647475507200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((31729387 : ℚ) / (21285000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1149928772768081350129 : ℚ) / (12669753643054200000000 : ℚ)), ((2350855743526957011347 : ℚ) / (25339507286108400000000 : ℚ)), ((5814412275867984043223 : ℚ) / (50679014572216800000000 : ℚ)), ((873978262770925767817 : ℚ) / (10135802914443360000000 : ℚ)), ((480411569013220899161 : ℚ) / (5631001619135200000000 : ℚ)), ((350823479952399308471 : ℚ) / (4607183142928800000000 : ℚ)), ((25326596356382632189 : ℚ) / (658169020418400000000 : ℚ)), ((168288888805980324103 : ℚ) / (4607183142928800000000 : ℚ)), ((312414892414301549 : ℚ) / (8998404576032812500 : ℚ)), ((91589728444759826783 : ℚ) / (2815500809567600000000 : ℚ))],
    jensenBound := ((6031705953328741631778630121909072140307746276851030980369485387870198219064512161801318417644423404597504959713069172458343659786115279742092160730715598316668026246520000000000000000000000 : ℚ) / (1463049250880125280263975804928570045077401434050854770350579709196767594739839995565792551613664237446556196223478877577737142150306594975605963474116661639314288855782049121047596296456341388026851779 : ℚ)),
    jensenFloorQ96 := (326633556061839201 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_simplexId_before"
  err.flush

theorem geometryRow011_simplexId_read :
    geometryRowsJson011.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped011.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_vertexIds_before"
  err.flush

theorem geometryRow011_vertexIds_read :
    geometryRowsJson011.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped011.vertexIds := by decide +kernel

noncomputable def geometryRow011_physicalVolumeNumeratorChars : List Char := ['7', '4', '7', '8', '1', '6', '6', '8', '7', '7', '3', '7', '3', '6', '4', '8', '7', '0', '5', '5', '6', '7', '1', '9', '4', '0', '5', '5', '2', '5', '9', '1', '7', '8', '6', '7', '9', '5', '5', '8', '1', '0', '7']
noncomputable def geometryRow011_physicalVolumeDenominatorChars : List Char := ['1', '2', '5', '8', '9', '6', '4', '7', '4', '7', '5', '5', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_physicalVolumeText : String := String.ofList (geometryRow011_physicalVolumeNumeratorChars ++ '/' :: geometryRow011_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_physicalVolume_before_field"
  err.flush

theorem geometryRow011_physicalVolume_field :
    geometryRowsJson011.getObjVal? "physical_volume" = .ok (.str geometryRow011_physicalVolumeText) := by rfl

theorem geometryRow011_physicalVolume_numerator_no_slash :
    geometryRow011_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeNumeratorChars = some (7478166877373648705567194055259178679558107 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow011_physicalVolumeDenominatorChars = some (12589647475507200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_physicalVolume_denominator_nonzero : (12589647475507200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_physicalVolume_parse :
    parseRational geometryRow011_physicalVolumeText = .ok geometryRowsTyped011.physicalVolume :=
  original_rational_fraction_of_chars geometryRow011_physicalVolumeNumeratorChars geometryRow011_physicalVolumeDenominatorChars
    (7478166877373648705567194055259178679558107 : Int) (12589647475507200000000000000000000000000000000000000000000000000 : Int)
    geometryRow011_physicalVolume_numerator_no_slash geometryRow011_physicalVolume_numerator_parse
    geometryRow011_physicalVolume_denominator_parse geometryRow011_physicalVolume_denominator_nonzero

theorem geometryRow011_physicalVolume_read :
    rationalField geometryRowsJson011 "physical_volume" = .ok geometryRowsTyped011.physicalVolume :=
  original_rationalField_of_string geometryRowsJson011 "physical_volume" geometryRow011_physicalVolumeText
    geometryRowsTyped011.physicalVolume geometryRow011_physicalVolume_field geometryRow011_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_physicalVolume_complete"
  err.flush

noncomputable def geometryRow011_meanGapNumeratorChars : List Char := ['3', '1', '7', '2', '9', '3', '8', '7']
noncomputable def geometryRow011_meanGapDenominatorChars : List Char := ['2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_meanGapText : String := String.ofList (geometryRow011_meanGapNumeratorChars ++ '/' :: geometryRow011_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_meanGap_before_field"
  err.flush

theorem geometryRow011_meanGap_field :
    geometryRowsJson011.getObjVal? "mean_gap" = .ok (.str geometryRow011_meanGapText) := by rfl

theorem geometryRow011_meanGap_numerator_no_slash :
    geometryRow011_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_meanGap_numerator_parse :
    SourceJson.intChars geometryRow011_meanGapNumeratorChars = some (31729387 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_parse :
    SourceJson.intChars geometryRow011_meanGapDenominatorChars = some (21285000000 : Int) := by decide +kernel

theorem geometryRow011_meanGap_denominator_nonzero : (21285000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_meanGap_parse :
    parseRational geometryRow011_meanGapText = .ok geometryRowsTyped011.meanGap :=
  original_rational_fraction_of_chars geometryRow011_meanGapNumeratorChars geometryRow011_meanGapDenominatorChars
    (31729387 : Int) (21285000000 : Int)
    geometryRow011_meanGap_numerator_no_slash geometryRow011_meanGap_numerator_parse
    geometryRow011_meanGap_denominator_parse geometryRow011_meanGap_denominator_nonzero

theorem geometryRow011_meanGap_read :
    rationalField geometryRowsJson011 "mean_gap" = .ok geometryRowsTyped011.meanGap :=
  original_rationalField_of_string geometryRowsJson011 "mean_gap" geometryRow011_meanGapText
    geometryRowsTyped011.meanGap geometryRow011_meanGap_field geometryRow011_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_meanGap_complete"
  err.flush

noncomputable def geometryRow011_jensenBoundNumeratorChars : List Char := ['6', '0', '3', '1', '7', '0', '5', '9', '5', '3', '3', '2', '8', '7', '4', '1', '6', '3', '1', '7', '7', '8', '6', '3', '0', '1', '2', '1', '9', '0', '9', '0', '7', '2', '1', '4', '0', '3', '0', '7', '7', '4', '6', '2', '7', '6', '8', '5', '1', '0', '3', '0', '9', '8', '0', '3', '6', '9', '4', '8', '5', '3', '8', '7', '8', '7', '0', '1', '9', '8', '2', '1', '9', '0', '6', '4', '5', '1', '2', '1', '6', '1', '8', '0', '1', '3', '1', '8', '4', '1', '7', '6', '4', '4', '4', '2', '3', '4', '0', '4', '5', '9', '7', '5', '0', '4', '9', '5', '9', '7', '1', '3', '0', '6', '9', '1', '7', '2', '4', '5', '8', '3', '4', '3', '6', '5', '9', '7', '8', '6', '1', '1', '5', '2', '7', '9', '7', '4', '2', '0', '9', '2', '1', '6', '0', '7', '3', '0', '7', '1', '5', '5', '9', '8', '3', '1', '6', '6', '6', '8', '0', '2', '6', '2', '4', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow011_jensenBoundDenominatorChars : List Char := ['1', '4', '6', '3', '0', '4', '9', '2', '5', '0', '8', '8', '0', '1', '2', '5', '2', '8', '0', '2', '6', '3', '9', '7', '5', '8', '0', '4', '9', '2', '8', '5', '7', '0', '0', '4', '5', '0', '7', '7', '4', '0', '1', '4', '3', '4', '0', '5', '0', '8', '5', '4', '7', '7', '0', '3', '5', '0', '5', '7', '9', '7', '0', '9', '1', '9', '6', '7', '6', '7', '5', '9', '4', '7', '3', '9', '8', '3', '9', '9', '9', '5', '5', '6', '5', '7', '9', '2', '5', '5', '1', '6', '1', '3', '6', '6', '4', '2', '3', '7', '4', '4', '6', '5', '5', '6', '1', '9', '6', '2', '2', '3', '4', '7', '8', '8', '7', '7', '5', '7', '7', '7', '3', '7', '1', '4', '2', '1', '5', '0', '3', '0', '6', '5', '9', '4', '9', '7', '5', '6', '0', '5', '9', '6', '3', '4', '7', '4', '1', '1', '6', '6', '6', '1', '6', '3', '9', '3', '1', '4', '2', '8', '8', '8', '5', '5', '7', '8', '2', '0', '4', '9', '1', '2', '1', '0', '4', '7', '5', '9', '6', '2', '9', '6', '4', '5', '6', '3', '4', '1', '3', '8', '8', '0', '2', '6', '8', '5', '1', '7', '7', '9']
noncomputable def geometryRow011_jensenBoundText : String := String.ofList (geometryRow011_jensenBoundNumeratorChars ++ '/' :: geometryRow011_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_jensenBound_before_field"
  err.flush

theorem geometryRow011_jensenBound_field :
    geometryRowsJson011.getObjVal? "jensen_bound" = .ok (.str geometryRow011_jensenBoundText) := by rfl

theorem geometryRow011_jensenBound_numerator_no_slash :
    geometryRow011_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow011_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow011_jensenBoundNumeratorChars = some (6031705953328741631778630121909072140307746276851030980369485387870198219064512161801318417644423404597504959713069172458343659786115279742092160730715598316668026246520000000000000000000000 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow011_jensenBoundDenominatorChars = some (1463049250880125280263975804928570045077401434050854770350579709196767594739839995565792551613664237446556196223478877577737142150306594975605963474116661639314288855782049121047596296456341388026851779 : Int) := by decide +kernel

theorem geometryRow011_jensenBound_denominator_nonzero : (1463049250880125280263975804928570045077401434050854770350579709196767594739839995565792551613664237446556196223478877577737142150306594975605963474116661639314288855782049121047596296456341388026851779 : Int) ≠ 0 := by decide +kernel

theorem geometryRow011_jensenBound_parse :
    parseRational geometryRow011_jensenBoundText = .ok geometryRowsTyped011.jensenBound :=
  original_rational_fraction_of_chars geometryRow011_jensenBoundNumeratorChars geometryRow011_jensenBoundDenominatorChars
    (6031705953328741631778630121909072140307746276851030980369485387870198219064512161801318417644423404597504959713069172458343659786115279742092160730715598316668026246520000000000000000000000 : Int) (1463049250880125280263975804928570045077401434050854770350579709196767594739839995565792551613664237446556196223478877577737142150306594975605963474116661639314288855782049121047596296456341388026851779 : Int)
    geometryRow011_jensenBound_numerator_no_slash geometryRow011_jensenBound_numerator_parse
    geometryRow011_jensenBound_denominator_parse geometryRow011_jensenBound_denominator_nonzero

theorem geometryRow011_jensenBound_read :
    rationalField geometryRowsJson011 "jensen_bound" = .ok geometryRowsTyped011.jensenBound :=
  original_rationalField_of_string geometryRowsJson011 "jensen_bound" geometryRow011_jensenBoundText
    geometryRowsTyped011.jensenBound geometryRow011_jensenBound_field geometryRow011_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_factorMaxima_before"
  err.flush

theorem geometryRow011_factorMaxima_read :
    rationalArrayField geometryRowsJson011 "factor_maxima" = .ok geometryRowsTyped011.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_gapWeightedMeans_before"
  err.flush

theorem geometryRow011_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson011 "gap_weighted_means" = .ok geometryRowsTyped011.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow011_floorChars : List Char := ['3', '2', '6', '6', '3', '3', '5', '5', '6', '0', '6', '1', '8', '3', '9', '2', '0', '1']
noncomputable def geometryRow011_floorText : String := String.ofList geometryRow011_floorChars

theorem geometryRow011_floor_text_read :
    geometryRowsJson011.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow011_floorText := by rfl

theorem geometryRow011_floor_chars_parse :
    SourceJson.intChars geometryRow011_floorChars = some (326633556061839201 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_011_original_decoder_complete"
  err.flush

theorem geometryRow011_shape :
    geometryRowsTyped011.simplexId = 11 ∧
    geometryRowsTyped011.vertexIds.size = 9 ∧ geometryRowsTyped011.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped011.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped011.factorMaxima.size = 10 ∧ geometryRowsTyped011.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson012 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped012 : GeometryRow :=
  { simplexId := 12,
    vertexIds := #[32, 20, 18, 16, 14, 12, 11, 8, 0],
    physicalVolume := ((45509578132838268859036345928738385595353611191 : ℚ) / (17391280466165760000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1668543532093 : ℚ) / (18572400000000 : ℚ)), ((1693073974897 : ℚ) / (18572400000000 : ℚ)), ((12806313615239 : ℚ) / (111434400000000 : ℚ)), ((381432711673 : ℚ) / (4457376000000 : ℚ)), ((9434260132237 : ℚ) / (111434400000000 : ℚ)), ((783468816563 : ℚ) / (10130400000000 : ℚ)), ((14137713073 : ℚ) / (361800000000 : ℚ)), ((23504530549 : ℚ) / (633150000000 : ℚ)), ((180333117077 : ℚ) / (5065200000000 : ℚ)), ((1782542002931 : ℚ) / (55717200000000 : ℚ))],
    jensenBound := ((671585937118737372781607070167871285989313482148384840696533849772081794830133062644720000000000000000000 : ℚ) / (76189491648776024872213742766585144383384554379275248660758975691598633071616685719022138019695937935432374849864121 : ℚ)),
    jensenFloorQ96 := (698370846384202426 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_simplexId_before"
  err.flush

theorem geometryRow012_simplexId_read :
    geometryRowsJson012.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped012.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_vertexIds_before"
  err.flush

theorem geometryRow012_vertexIds_read :
    geometryRowsJson012.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped012.vertexIds := by decide +kernel

noncomputable def geometryRow012_physicalVolumeNumeratorChars : List Char := ['4', '5', '5', '0', '9', '5', '7', '8', '1', '3', '2', '8', '3', '8', '2', '6', '8', '8', '5', '9', '0', '3', '6', '3', '4', '5', '9', '2', '8', '7', '3', '8', '3', '8', '5', '5', '9', '5', '3', '5', '3', '6', '1', '1', '1', '9', '1']
noncomputable def geometryRow012_physicalVolumeDenominatorChars : List Char := ['1', '7', '3', '9', '1', '2', '8', '0', '4', '6', '6', '1', '6', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_physicalVolumeText : String := String.ofList (geometryRow012_physicalVolumeNumeratorChars ++ '/' :: geometryRow012_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_physicalVolume_before_field"
  err.flush

theorem geometryRow012_physicalVolume_field :
    geometryRowsJson012.getObjVal? "physical_volume" = .ok (.str geometryRow012_physicalVolumeText) := by rfl

theorem geometryRow012_physicalVolume_numerator_no_slash :
    geometryRow012_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeNumeratorChars = some (45509578132838268859036345928738385595353611191 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow012_physicalVolumeDenominatorChars = some (17391280466165760000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_physicalVolume_denominator_nonzero : (17391280466165760000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_physicalVolume_parse :
    parseRational geometryRow012_physicalVolumeText = .ok geometryRowsTyped012.physicalVolume :=
  original_rational_fraction_of_chars geometryRow012_physicalVolumeNumeratorChars geometryRow012_physicalVolumeDenominatorChars
    (45509578132838268859036345928738385595353611191 : Int) (17391280466165760000000000000000000000000000000000000000000000000000 : Int)
    geometryRow012_physicalVolume_numerator_no_slash geometryRow012_physicalVolume_numerator_parse
    geometryRow012_physicalVolume_denominator_parse geometryRow012_physicalVolume_denominator_nonzero

theorem geometryRow012_physicalVolume_read :
    rationalField geometryRowsJson012 "physical_volume" = .ok geometryRowsTyped012.physicalVolume :=
  original_rationalField_of_string geometryRowsJson012 "physical_volume" geometryRow012_physicalVolumeText
    geometryRowsTyped012.physicalVolume geometryRow012_physicalVolume_field geometryRow012_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_physicalVolume_complete"
  err.flush

noncomputable def geometryRow012_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow012_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_meanGapText : String := String.ofList (geometryRow012_meanGapNumeratorChars ++ '/' :: geometryRow012_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_meanGap_before_field"
  err.flush

theorem geometryRow012_meanGap_field :
    geometryRowsJson012.getObjVal? "mean_gap" = .ok (.str geometryRow012_meanGapText) := by rfl

theorem geometryRow012_meanGap_numerator_no_slash :
    geometryRow012_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_meanGap_numerator_parse :
    SourceJson.intChars geometryRow012_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_parse :
    SourceJson.intChars geometryRow012_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow012_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_meanGap_parse :
    parseRational geometryRow012_meanGapText = .ok geometryRowsTyped012.meanGap :=
  original_rational_fraction_of_chars geometryRow012_meanGapNumeratorChars geometryRow012_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow012_meanGap_numerator_no_slash geometryRow012_meanGap_numerator_parse
    geometryRow012_meanGap_denominator_parse geometryRow012_meanGap_denominator_nonzero

theorem geometryRow012_meanGap_read :
    rationalField geometryRowsJson012 "mean_gap" = .ok geometryRowsTyped012.meanGap :=
  original_rationalField_of_string geometryRowsJson012 "mean_gap" geometryRow012_meanGapText
    geometryRowsTyped012.meanGap geometryRow012_meanGap_field geometryRow012_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_meanGap_complete"
  err.flush

noncomputable def geometryRow012_jensenBoundNumeratorChars : List Char := ['6', '7', '1', '5', '8', '5', '9', '3', '7', '1', '1', '8', '7', '3', '7', '3', '7', '2', '7', '8', '1', '6', '0', '7', '0', '7', '0', '1', '6', '7', '8', '7', '1', '2', '8', '5', '9', '8', '9', '3', '1', '3', '4', '8', '2', '1', '4', '8', '3', '8', '4', '8', '4', '0', '6', '9', '6', '5', '3', '3', '8', '4', '9', '7', '7', '2', '0', '8', '1', '7', '9', '4', '8', '3', '0', '1', '3', '3', '0', '6', '2', '6', '4', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow012_jensenBoundDenominatorChars : List Char := ['7', '6', '1', '8', '9', '4', '9', '1', '6', '4', '8', '7', '7', '6', '0', '2', '4', '8', '7', '2', '2', '1', '3', '7', '4', '2', '7', '6', '6', '5', '8', '5', '1', '4', '4', '3', '8', '3', '3', '8', '4', '5', '5', '4', '3', '7', '9', '2', '7', '5', '2', '4', '8', '6', '6', '0', '7', '5', '8', '9', '7', '5', '6', '9', '1', '5', '9', '8', '6', '3', '3', '0', '7', '1', '6', '1', '6', '6', '8', '5', '7', '1', '9', '0', '2', '2', '1', '3', '8', '0', '1', '9', '6', '9', '5', '9', '3', '7', '9', '3', '5', '4', '3', '2', '3', '7', '4', '8', '4', '9', '8', '6', '4', '1', '2', '1']
noncomputable def geometryRow012_jensenBoundText : String := String.ofList (geometryRow012_jensenBoundNumeratorChars ++ '/' :: geometryRow012_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_jensenBound_before_field"
  err.flush

theorem geometryRow012_jensenBound_field :
    geometryRowsJson012.getObjVal? "jensen_bound" = .ok (.str geometryRow012_jensenBoundText) := by rfl

theorem geometryRow012_jensenBound_numerator_no_slash :
    geometryRow012_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow012_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow012_jensenBoundNumeratorChars = some (671585937118737372781607070167871285989313482148384840696533849772081794830133062644720000000000000000000 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow012_jensenBoundDenominatorChars = some (76189491648776024872213742766585144383384554379275248660758975691598633071616685719022138019695937935432374849864121 : Int) := by decide +kernel

theorem geometryRow012_jensenBound_denominator_nonzero : (76189491648776024872213742766585144383384554379275248660758975691598633071616685719022138019695937935432374849864121 : Int) ≠ 0 := by decide +kernel

theorem geometryRow012_jensenBound_parse :
    parseRational geometryRow012_jensenBoundText = .ok geometryRowsTyped012.jensenBound :=
  original_rational_fraction_of_chars geometryRow012_jensenBoundNumeratorChars geometryRow012_jensenBoundDenominatorChars
    (671585937118737372781607070167871285989313482148384840696533849772081794830133062644720000000000000000000 : Int) (76189491648776024872213742766585144383384554379275248660758975691598633071616685719022138019695937935432374849864121 : Int)
    geometryRow012_jensenBound_numerator_no_slash geometryRow012_jensenBound_numerator_parse
    geometryRow012_jensenBound_denominator_parse geometryRow012_jensenBound_denominator_nonzero

theorem geometryRow012_jensenBound_read :
    rationalField geometryRowsJson012 "jensen_bound" = .ok geometryRowsTyped012.jensenBound :=
  original_rationalField_of_string geometryRowsJson012 "jensen_bound" geometryRow012_jensenBoundText
    geometryRowsTyped012.jensenBound geometryRow012_jensenBound_field geometryRow012_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_factorMaxima_before"
  err.flush

theorem geometryRow012_factorMaxima_read :
    rationalArrayField geometryRowsJson012 "factor_maxima" = .ok geometryRowsTyped012.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_gapWeightedMeans_before"
  err.flush

theorem geometryRow012_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson012 "gap_weighted_means" = .ok geometryRowsTyped012.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow012_floorChars : List Char := ['6', '9', '8', '3', '7', '0', '8', '4', '6', '3', '8', '4', '2', '0', '2', '4', '2', '6']
noncomputable def geometryRow012_floorText : String := String.ofList geometryRow012_floorChars

theorem geometryRow012_floor_text_read :
    geometryRowsJson012.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow012_floorText := by rfl

theorem geometryRow012_floor_chars_parse :
    SourceJson.intChars geometryRow012_floorChars = some (698370846384202426 : Int) := by decide +kernel

theorem geometryRow012_floor_parse :
    parseInteger geometryRow012_floorText = .ok geometryRowsTyped012.jensenFloorQ96 := by
  simp only [geometryRow012_floorText, parseInteger, String.toList_ofList, geometryRow012_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_012 :
    decodeGeometryRow geometryRowsJson012 = .ok geometryRowsTyped012 :=
  original_geometryRow_of_fields geometryRowsJson012 geometryRowsTyped012 geometryRow012_floorText
    geometryRow012_simplexId_read geometryRow012_vertexIds_read
    geometryRow012_physicalVolume_read geometryRow012_meanGap_read
    geometryRow012_factorMaxima_read geometryRow012_gapWeightedMeans_read
    geometryRow012_jensenBound_read geometryRow012_floor_text_read geometryRow012_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_012_original_decoder_complete"
  err.flush

theorem geometryRow012_shape :
    geometryRowsTyped012.simplexId = 12 ∧
    geometryRowsTyped012.vertexIds.size = 9 ∧ geometryRowsTyped012.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped012.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped012.factorMaxima.size = 10 ∧ geometryRowsTyped012.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson013 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped013 : GeometryRow :=
  { simplexId := 13,
    vertexIds := #[32, 20, 18, 16, 14, 12, 11, 7, 3],
    physicalVolume := ((1576353973511496202996384637981192886477654119 : ℚ) / (3692963259482112000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((49290167 : ℚ) / (34056000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((3603240201007359004951 : ℚ) / (39363777996404400000000 : ℚ)), ((3680206873693213737781 : ℚ) / (39363777996404400000000 : ℚ)), ((9044854954230308488153 : ℚ) / (78727555992808800000000 : ℚ)), ((6772990888392149683783 : ℚ) / (78727555992808800000000 : ℚ)), ((2233747058124879687769 : ℚ) / (26242518664269600000000 : ℚ)), ((5991470725498740935687 : ℚ) / (78727555992808800000000 : ℚ)), ((54067244715201340751 : ℚ) / (1405849214157300000000 : ℚ)), ((718505016450533233459 : ℚ) / (19681888998202200000000 : ℚ)), ((1341614355105698580953 : ℚ) / (39363777996404400000000 : ℚ)), ((85996273723118778443 : ℚ) / (2624251866426960000000 : ℚ))],
    jensenBound := ((10780756334474327087904115339702262235957146179156276399855243642573677034428491014217929576285795160927665784274284547265367004457509482488533668956651016454803687034379297072635000000000000000000000 : ℚ) / (3748374720911692912248634667213122627559198277235198496964002579482764857476024684107329241818287377334761354424878802529877112935267043887653468949055874982619888940642725139055188929434839488012213100368640329 : ℚ)),
    jensenFloorQ96 := (227869297626324260 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_simplexId_before"
  err.flush

theorem geometryRow013_simplexId_read :
    geometryRowsJson013.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped013.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_vertexIds_before"
  err.flush

theorem geometryRow013_vertexIds_read :
    geometryRowsJson013.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped013.vertexIds := by decide +kernel

noncomputable def geometryRow013_physicalVolumeNumeratorChars : List Char := ['1', '5', '7', '6', '3', '5', '3', '9', '7', '3', '5', '1', '1', '4', '9', '6', '2', '0', '2', '9', '9', '6', '3', '8', '4', '6', '3', '7', '9', '8', '1', '1', '9', '2', '8', '8', '6', '4', '7', '7', '6', '5', '4', '1', '1', '9']
noncomputable def geometryRow013_physicalVolumeDenominatorChars : List Char := ['3', '6', '9', '2', '9', '6', '3', '2', '5', '9', '4', '8', '2', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_physicalVolumeText : String := String.ofList (geometryRow013_physicalVolumeNumeratorChars ++ '/' :: geometryRow013_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_physicalVolume_before_field"
  err.flush

theorem geometryRow013_physicalVolume_field :
    geometryRowsJson013.getObjVal? "physical_volume" = .ok (.str geometryRow013_physicalVolumeText) := by rfl

theorem geometryRow013_physicalVolume_numerator_no_slash :
    geometryRow013_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeNumeratorChars = some (1576353973511496202996384637981192886477654119 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow013_physicalVolumeDenominatorChars = some (3692963259482112000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_physicalVolume_denominator_nonzero : (3692963259482112000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_physicalVolume_parse :
    parseRational geometryRow013_physicalVolumeText = .ok geometryRowsTyped013.physicalVolume :=
  original_rational_fraction_of_chars geometryRow013_physicalVolumeNumeratorChars geometryRow013_physicalVolumeDenominatorChars
    (1576353973511496202996384637981192886477654119 : Int) (3692963259482112000000000000000000000000000000000000000000000000000 : Int)
    geometryRow013_physicalVolume_numerator_no_slash geometryRow013_physicalVolume_numerator_parse
    geometryRow013_physicalVolume_denominator_parse geometryRow013_physicalVolume_denominator_nonzero

theorem geometryRow013_physicalVolume_read :
    rationalField geometryRowsJson013 "physical_volume" = .ok geometryRowsTyped013.physicalVolume :=
  original_rationalField_of_string geometryRowsJson013 "physical_volume" geometryRow013_physicalVolumeText
    geometryRowsTyped013.physicalVolume geometryRow013_physicalVolume_field geometryRow013_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_physicalVolume_complete"
  err.flush

noncomputable def geometryRow013_meanGapNumeratorChars : List Char := ['4', '9', '2', '9', '0', '1', '6', '7']
noncomputable def geometryRow013_meanGapDenominatorChars : List Char := ['3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_meanGapText : String := String.ofList (geometryRow013_meanGapNumeratorChars ++ '/' :: geometryRow013_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_meanGap_before_field"
  err.flush

theorem geometryRow013_meanGap_field :
    geometryRowsJson013.getObjVal? "mean_gap" = .ok (.str geometryRow013_meanGapText) := by rfl

theorem geometryRow013_meanGap_numerator_no_slash :
    geometryRow013_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_meanGap_numerator_parse :
    SourceJson.intChars geometryRow013_meanGapNumeratorChars = some (49290167 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_parse :
    SourceJson.intChars geometryRow013_meanGapDenominatorChars = some (34056000000 : Int) := by decide +kernel

theorem geometryRow013_meanGap_denominator_nonzero : (34056000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_meanGap_parse :
    parseRational geometryRow013_meanGapText = .ok geometryRowsTyped013.meanGap :=
  original_rational_fraction_of_chars geometryRow013_meanGapNumeratorChars geometryRow013_meanGapDenominatorChars
    (49290167 : Int) (34056000000 : Int)
    geometryRow013_meanGap_numerator_no_slash geometryRow013_meanGap_numerator_parse
    geometryRow013_meanGap_denominator_parse geometryRow013_meanGap_denominator_nonzero

theorem geometryRow013_meanGap_read :
    rationalField geometryRowsJson013 "mean_gap" = .ok geometryRowsTyped013.meanGap :=
  original_rationalField_of_string geometryRowsJson013 "mean_gap" geometryRow013_meanGapText
    geometryRowsTyped013.meanGap geometryRow013_meanGap_field geometryRow013_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_meanGap_complete"
  err.flush

noncomputable def geometryRow013_jensenBoundNumeratorChars : List Char := ['1', '0', '7', '8', '0', '7', '5', '6', '3', '3', '4', '4', '7', '4', '3', '2', '7', '0', '8', '7', '9', '0', '4', '1', '1', '5', '3', '3', '9', '7', '0', '2', '2', '6', '2', '2', '3', '5', '9', '5', '7', '1', '4', '6', '1', '7', '9', '1', '5', '6', '2', '7', '6', '3', '9', '9', '8', '5', '5', '2', '4', '3', '6', '4', '2', '5', '7', '3', '6', '7', '7', '0', '3', '4', '4', '2', '8', '4', '9', '1', '0', '1', '4', '2', '1', '7', '9', '2', '9', '5', '7', '6', '2', '8', '5', '7', '9', '5', '1', '6', '0', '9', '2', '7', '6', '6', '5', '7', '8', '4', '2', '7', '4', '2', '8', '4', '5', '4', '7', '2', '6', '5', '3', '6', '7', '0', '0', '4', '4', '5', '7', '5', '0', '9', '4', '8', '2', '4', '8', '8', '5', '3', '3', '6', '6', '8', '9', '5', '6', '6', '5', '1', '0', '1', '6', '4', '5', '4', '8', '0', '3', '6', '8', '7', '0', '3', '4', '3', '7', '9', '2', '9', '7', '0', '7', '2', '6', '3', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow013_jensenBoundDenominatorChars : List Char := ['3', '7', '4', '8', '3', '7', '4', '7', '2', '0', '9', '1', '1', '6', '9', '2', '9', '1', '2', '2', '4', '8', '6', '3', '4', '6', '6', '7', '2', '1', '3', '1', '2', '2', '6', '2', '7', '5', '5', '9', '1', '9', '8', '2', '7', '7', '2', '3', '5', '1', '9', '8', '4', '9', '6', '9', '6', '4', '0', '0', '2', '5', '7', '9', '4', '8', '2', '7', '6', '4', '8', '5', '7', '4', '7', '6', '0', '2', '4', '6', '8', '4', '1', '0', '7', '3', '2', '9', '2', '4', '1', '8', '1', '8', '2', '8', '7', '3', '7', '7', '3', '3', '4', '7', '6', '1', '3', '5', '4', '4', '2', '4', '8', '7', '8', '8', '0', '2', '5', '2', '9', '8', '7', '7', '1', '1', '2', '9', '3', '5', '2', '6', '7', '0', '4', '3', '8', '8', '7', '6', '5', '3', '4', '6', '8', '9', '4', '9', '0', '5', '5', '8', '7', '4', '9', '8', '2', '6', '1', '9', '8', '8', '8', '9', '4', '0', '6', '4', '2', '7', '2', '5', '1', '3', '9', '0', '5', '5', '1', '8', '8', '9', '2', '9', '4', '3', '4', '8', '3', '9', '4', '8', '8', '0', '1', '2', '2', '1', '3', '1', '0', '0', '3', '6', '8', '6', '4', '0', '3', '2', '9']
noncomputable def geometryRow013_jensenBoundText : String := String.ofList (geometryRow013_jensenBoundNumeratorChars ++ '/' :: geometryRow013_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_jensenBound_before_field"
  err.flush

theorem geometryRow013_jensenBound_field :
    geometryRowsJson013.getObjVal? "jensen_bound" = .ok (.str geometryRow013_jensenBoundText) := by rfl

theorem geometryRow013_jensenBound_numerator_no_slash :
    geometryRow013_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow013_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow013_jensenBoundNumeratorChars = some (10780756334474327087904115339702262235957146179156276399855243642573677034428491014217929576285795160927665784274284547265367004457509482488533668956651016454803687034379297072635000000000000000000000 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow013_jensenBoundDenominatorChars = some (3748374720911692912248634667213122627559198277235198496964002579482764857476024684107329241818287377334761354424878802529877112935267043887653468949055874982619888940642725139055188929434839488012213100368640329 : Int) := by decide +kernel

theorem geometryRow013_jensenBound_denominator_nonzero : (3748374720911692912248634667213122627559198277235198496964002579482764857476024684107329241818287377334761354424878802529877112935267043887653468949055874982619888940642725139055188929434839488012213100368640329 : Int) ≠ 0 := by decide +kernel

theorem geometryRow013_jensenBound_parse :
    parseRational geometryRow013_jensenBoundText = .ok geometryRowsTyped013.jensenBound :=
  original_rational_fraction_of_chars geometryRow013_jensenBoundNumeratorChars geometryRow013_jensenBoundDenominatorChars
    (10780756334474327087904115339702262235957146179156276399855243642573677034428491014217929576285795160927665784274284547265367004457509482488533668956651016454803687034379297072635000000000000000000000 : Int) (3748374720911692912248634667213122627559198277235198496964002579482764857476024684107329241818287377334761354424878802529877112935267043887653468949055874982619888940642725139055188929434839488012213100368640329 : Int)
    geometryRow013_jensenBound_numerator_no_slash geometryRow013_jensenBound_numerator_parse
    geometryRow013_jensenBound_denominator_parse geometryRow013_jensenBound_denominator_nonzero

theorem geometryRow013_jensenBound_read :
    rationalField geometryRowsJson013 "jensen_bound" = .ok geometryRowsTyped013.jensenBound :=
  original_rationalField_of_string geometryRowsJson013 "jensen_bound" geometryRow013_jensenBoundText
    geometryRowsTyped013.jensenBound geometryRow013_jensenBound_field geometryRow013_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_factorMaxima_before"
  err.flush

theorem geometryRow013_factorMaxima_read :
    rationalArrayField geometryRowsJson013 "factor_maxima" = .ok geometryRowsTyped013.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_gapWeightedMeans_before"
  err.flush

theorem geometryRow013_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson013 "gap_weighted_means" = .ok geometryRowsTyped013.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow013_floorChars : List Char := ['2', '2', '7', '8', '6', '9', '2', '9', '7', '6', '2', '6', '3', '2', '4', '2', '6', '0']
noncomputable def geometryRow013_floorText : String := String.ofList geometryRow013_floorChars

theorem geometryRow013_floor_text_read :
    geometryRowsJson013.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow013_floorText := by rfl

theorem geometryRow013_floor_chars_parse :
    SourceJson.intChars geometryRow013_floorChars = some (227869297626324260 : Int) := by decide +kernel

theorem geometryRow013_floor_parse :
    parseInteger geometryRow013_floorText = .ok geometryRowsTyped013.jensenFloorQ96 := by
  simp only [geometryRow013_floorText, parseInteger, String.toList_ofList, geometryRow013_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_013 :
    decodeGeometryRow geometryRowsJson013 = .ok geometryRowsTyped013 :=
  original_geometryRow_of_fields geometryRowsJson013 geometryRowsTyped013 geometryRow013_floorText
    geometryRow013_simplexId_read geometryRow013_vertexIds_read
    geometryRow013_physicalVolume_read geometryRow013_meanGap_read
    geometryRow013_factorMaxima_read geometryRow013_gapWeightedMeans_read
    geometryRow013_jensenBound_read geometryRow013_floor_text_read geometryRow013_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_013_original_decoder_complete"
  err.flush

theorem geometryRow013_shape :
    geometryRowsTyped013.simplexId = 13 ∧
    geometryRowsTyped013.vertexIds.size = 9 ∧ geometryRowsTyped013.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped013.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped013.factorMaxima.size = 10 ∧ geometryRowsTyped013.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson014 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped014 : GeometryRow :=
  { simplexId := 14,
    vertexIds := #[32, 20, 18, 16, 14, 13, 4, 1, 0],
    physicalVolume := ((35243320988879209737510759230187316119424261 : ℚ) / (2320072571658240000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((4621814422621355773048891 : ℚ) / (51409089676521838800000000 : ℚ)), ((15806659206290118397939 : ℚ) / (170794317862198800000000 : ℚ)), ((270458731064842403728165133 : ℚ) / (2364818125120004584800000000 : ℚ)), ((41244845407918151846540719 : ℚ) / (472963625024000916960000000 : ℚ)), ((68023003104613125699570533 : ℚ) / (788272708373334861600000000 : ℚ)), ((16051158679963170463612481 : ℚ) / (214983465920000416800000000 : ℚ)), ((3963603907545475541162099 : ℚ) / (107491732960000208400000000 : ℚ)), ((3939522865718070453238769 : ℚ) / (107491732960000208400000000 : ℚ)), ((3881023725502273961713889 : ℚ) / (107491732960000208400000000 : ℚ)), ((1847713263058479273433 : ℚ) / (56931439287399600000000 : ℚ))],
    jensenBound := ((15761902494958401711100257929950521218028701954465366026355145812548900465062054198085756555012207690163369974123153204478036998520539531055590329303308752516591292562295082538243671609401940070971010234571943116800000000000000000000 : ℚ) / (99632313878971391937407850001562810755399451781975466532227673320386991318429800547905951055722673351152609422889119321878326424717056263270251039734546375717620528222057138287044224583736394074524783813095880456950767825743644908572332909585413 : ℚ)),
    jensenFloorQ96 := (12533951323478439 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_simplexId_before"
  err.flush

theorem geometryRow014_simplexId_read :
    geometryRowsJson014.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped014.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_vertexIds_before"
  err.flush

theorem geometryRow014_vertexIds_read :
    geometryRowsJson014.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped014.vertexIds := by decide +kernel

noncomputable def geometryRow014_physicalVolumeNumeratorChars : List Char := ['3', '5', '2', '4', '3', '3', '2', '0', '9', '8', '8', '8', '7', '9', '2', '0', '9', '7', '3', '7', '5', '1', '0', '7', '5', '9', '2', '3', '0', '1', '8', '7', '3', '1', '6', '1', '1', '9', '4', '2', '4', '2', '6', '1']
noncomputable def geometryRow014_physicalVolumeDenominatorChars : List Char := ['2', '3', '2', '0', '0', '7', '2', '5', '7', '1', '6', '5', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_physicalVolumeText : String := String.ofList (geometryRow014_physicalVolumeNumeratorChars ++ '/' :: geometryRow014_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_physicalVolume_before_field"
  err.flush

theorem geometryRow014_physicalVolume_field :
    geometryRowsJson014.getObjVal? "physical_volume" = .ok (.str geometryRow014_physicalVolumeText) := by rfl

theorem geometryRow014_physicalVolume_numerator_no_slash :
    geometryRow014_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeNumeratorChars = some (35243320988879209737510759230187316119424261 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeDenominatorChars = some (2320072571658240000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_nonzero : (2320072571658240000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_physicalVolume_parse :
    parseRational geometryRow014_physicalVolumeText = .ok geometryRowsTyped014.physicalVolume :=
  original_rational_fraction_of_chars geometryRow014_physicalVolumeNumeratorChars geometryRow014_physicalVolumeDenominatorChars
    (35243320988879209737510759230187316119424261 : Int) (2320072571658240000000000000000000000000000000000000000000000000000 : Int)
    geometryRow014_physicalVolume_numerator_no_slash geometryRow014_physicalVolume_numerator_parse
    geometryRow014_physicalVolume_denominator_parse geometryRow014_physicalVolume_denominator_nonzero

theorem geometryRow014_physicalVolume_read :
    rationalField geometryRowsJson014 "physical_volume" = .ok geometryRowsTyped014.physicalVolume :=
  original_rationalField_of_string geometryRowsJson014 "physical_volume" geometryRow014_physicalVolumeText
    geometryRowsTyped014.physicalVolume geometryRow014_physicalVolume_field geometryRow014_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_physicalVolume_complete"
  err.flush

noncomputable def geometryRow014_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow014_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_meanGapText : String := String.ofList (geometryRow014_meanGapNumeratorChars ++ '/' :: geometryRow014_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_meanGap_before_field"
  err.flush

theorem geometryRow014_meanGap_field :
    geometryRowsJson014.getObjVal? "mean_gap" = .ok (.str geometryRow014_meanGapText) := by rfl

theorem geometryRow014_meanGap_numerator_no_slash :
    geometryRow014_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_meanGap_numerator_parse :
    SourceJson.intChars geometryRow014_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_parse :
    SourceJson.intChars geometryRow014_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_meanGap_parse :
    parseRational geometryRow014_meanGapText = .ok geometryRowsTyped014.meanGap :=
  original_rational_fraction_of_chars geometryRow014_meanGapNumeratorChars geometryRow014_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow014_meanGap_numerator_no_slash geometryRow014_meanGap_numerator_parse
    geometryRow014_meanGap_denominator_parse geometryRow014_meanGap_denominator_nonzero

theorem geometryRow014_meanGap_read :
    rationalField geometryRowsJson014 "mean_gap" = .ok geometryRowsTyped014.meanGap :=
  original_rationalField_of_string geometryRowsJson014 "mean_gap" geometryRow014_meanGapText
    geometryRowsTyped014.meanGap geometryRow014_meanGap_field geometryRow014_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_meanGap_complete"
  err.flush

noncomputable def geometryRow014_jensenBoundNumeratorChars : List Char := ['1', '5', '7', '6', '1', '9', '0', '2', '4', '9', '4', '9', '5', '8', '4', '0', '1', '7', '1', '1', '1', '0', '0', '2', '5', '7', '9', '2', '9', '9', '5', '0', '5', '2', '1', '2', '1', '8', '0', '2', '8', '7', '0', '1', '9', '5', '4', '4', '6', '5', '3', '6', '6', '0', '2', '6', '3', '5', '5', '1', '4', '5', '8', '1', '2', '5', '4', '8', '9', '0', '0', '4', '6', '5', '0', '6', '2', '0', '5', '4', '1', '9', '8', '0', '8', '5', '7', '5', '6', '5', '5', '5', '0', '1', '2', '2', '0', '7', '6', '9', '0', '1', '6', '3', '3', '6', '9', '9', '7', '4', '1', '2', '3', '1', '5', '3', '2', '0', '4', '4', '7', '8', '0', '3', '6', '9', '9', '8', '5', '2', '0', '5', '3', '9', '5', '3', '1', '0', '5', '5', '5', '9', '0', '3', '2', '9', '3', '0', '3', '3', '0', '8', '7', '5', '2', '5', '1', '6', '5', '9', '1', '2', '9', '2', '5', '6', '2', '2', '9', '5', '0', '8', '2', '5', '3', '8', '2', '4', '3', '6', '7', '1', '6', '0', '9', '4', '0', '1', '9', '4', '0', '0', '7', '0', '9', '7', '1', '0', '1', '0', '2', '3', '4', '5', '7', '1', '9', '4', '3', '1', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_jensenBoundDenominatorChars : List Char := ['9', '9', '6', '3', '2', '3', '1', '3', '8', '7', '8', '9', '7', '1', '3', '9', '1', '9', '3', '7', '4', '0', '7', '8', '5', '0', '0', '0', '1', '5', '6', '2', '8', '1', '0', '7', '5', '5', '3', '9', '9', '4', '5', '1', '7', '8', '1', '9', '7', '5', '4', '6', '6', '5', '3', '2', '2', '2', '7', '6', '7', '3', '3', '2', '0', '3', '8', '6', '9', '9', '1', '3', '1', '8', '4', '2', '9', '8', '0', '0', '5', '4', '7', '9', '0', '5', '9', '5', '1', '0', '5', '5', '7', '2', '2', '6', '7', '3', '3', '5', '1', '1', '5', '2', '6', '0', '9', '4', '2', '2', '8', '8', '9', '1', '1', '9', '3', '2', '1', '8', '7', '8', '3', '2', '6', '4', '2', '4', '7', '1', '7', '0', '5', '6', '2', '6', '3', '2', '7', '0', '2', '5', '1', '0', '3', '9', '7', '3', '4', '5', '4', '6', '3', '7', '5', '7', '1', '7', '6', '2', '0', '5', '2', '8', '2', '2', '2', '0', '5', '7', '1', '3', '8', '2', '8', '7', '0', '4', '4', '2', '2', '4', '5', '8', '3', '7', '3', '6', '3', '9', '4', '0', '7', '4', '5', '2', '4', '7', '8', '3', '8', '1', '3', '0', '9', '5', '8', '8', '0', '4', '5', '6', '9', '5', '0', '7', '6', '7', '8', '2', '5', '7', '4', '3', '6', '4', '4', '9', '0', '8', '5', '7', '2', '3', '3', '2', '9', '0', '9', '5', '8', '5', '4', '1', '3']
noncomputable def geometryRow014_jensenBoundText : String := String.ofList (geometryRow014_jensenBoundNumeratorChars ++ '/' :: geometryRow014_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_jensenBound_before_field"
  err.flush

theorem geometryRow014_jensenBound_field :
    geometryRowsJson014.getObjVal? "jensen_bound" = .ok (.str geometryRow014_jensenBoundText) := by rfl

theorem geometryRow014_jensenBound_numerator_no_slash :
    geometryRow014_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow014_jensenBoundNumeratorChars = some (15761902494958401711100257929950521218028701954465366026355145812548900465062054198085756555012207690163369974123153204478036998520539531055590329303308752516591292562295082538243671609401940070971010234571943116800000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow014_jensenBoundDenominatorChars = some (99632313878971391937407850001562810755399451781975466532227673320386991318429800547905951055722673351152609422889119321878326424717056263270251039734546375717620528222057138287044224583736394074524783813095880456950767825743644908572332909585413 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_nonzero : (99632313878971391937407850001562810755399451781975466532227673320386991318429800547905951055722673351152609422889119321878326424717056263270251039734546375717620528222057138287044224583736394074524783813095880456950767825743644908572332909585413 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_jensenBound_parse :
    parseRational geometryRow014_jensenBoundText = .ok geometryRowsTyped014.jensenBound :=
  original_rational_fraction_of_chars geometryRow014_jensenBoundNumeratorChars geometryRow014_jensenBoundDenominatorChars
    (15761902494958401711100257929950521218028701954465366026355145812548900465062054198085756555012207690163369974123153204478036998520539531055590329303308752516591292562295082538243671609401940070971010234571943116800000000000000000000 : Int) (99632313878971391937407850001562810755399451781975466532227673320386991318429800547905951055722673351152609422889119321878326424717056263270251039734546375717620528222057138287044224583736394074524783813095880456950767825743644908572332909585413 : Int)
    geometryRow014_jensenBound_numerator_no_slash geometryRow014_jensenBound_numerator_parse
    geometryRow014_jensenBound_denominator_parse geometryRow014_jensenBound_denominator_nonzero

theorem geometryRow014_jensenBound_read :
    rationalField geometryRowsJson014 "jensen_bound" = .ok geometryRowsTyped014.jensenBound :=
  original_rationalField_of_string geometryRowsJson014 "jensen_bound" geometryRow014_jensenBoundText
    geometryRowsTyped014.jensenBound geometryRow014_jensenBound_field geometryRow014_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_factorMaxima_before"
  err.flush

theorem geometryRow014_factorMaxima_read :
    rationalArrayField geometryRowsJson014 "factor_maxima" = .ok geometryRowsTyped014.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_gapWeightedMeans_before"
  err.flush

theorem geometryRow014_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson014 "gap_weighted_means" = .ok geometryRowsTyped014.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow014_floorChars : List Char := ['1', '2', '5', '3', '3', '9', '5', '1', '3', '2', '3', '4', '7', '8', '4', '3', '9']
noncomputable def geometryRow014_floorText : String := String.ofList geometryRow014_floorChars

theorem geometryRow014_floor_text_read :
    geometryRowsJson014.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow014_floorText := by rfl

theorem geometryRow014_floor_chars_parse :
    SourceJson.intChars geometryRow014_floorChars = some (12533951323478439 : Int) := by decide +kernel

theorem geometryRow014_floor_parse :
    parseInteger geometryRow014_floorText = .ok geometryRowsTyped014.jensenFloorQ96 := by
  simp only [geometryRow014_floorText, parseInteger, String.toList_ofList, geometryRow014_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_014 :
    decodeGeometryRow geometryRowsJson014 = .ok geometryRowsTyped014 :=
  original_geometryRow_of_fields geometryRowsJson014 geometryRowsTyped014 geometryRow014_floorText
    geometryRow014_simplexId_read geometryRow014_vertexIds_read
    geometryRow014_physicalVolume_read geometryRow014_meanGap_read
    geometryRow014_factorMaxima_read geometryRow014_gapWeightedMeans_read
    geometryRow014_jensenBound_read geometryRow014_floor_text_read geometryRow014_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_014_original_decoder_complete"
  err.flush

theorem geometryRow014_shape :
    geometryRowsTyped014.simplexId = 14 ∧
    geometryRowsTyped014.vertexIds.size = 9 ∧ geometryRowsTyped014.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped014.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped014.factorMaxima.size = 10 ∧ geometryRowsTyped014.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson015 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped015 : GeometryRow :=
  { simplexId := 15,
    vertexIds := #[32, 20, 18, 16, 14, 13, 10, 1, 0],
    physicalVolume := ((27766604059092169448290087893309518923072337099 : ℚ) / (153124789729443840000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1687401017352628027259 : ℚ) / (18638714667157200000000 : ℚ)), ((246369154566005348753 : ℚ) / (2662673523879600000000 : ℚ)), ((98415008462117497320937 : ℚ) / (857380874689231200000000 : ℚ)), ((14803440234850133215451 : ℚ) / (171476174937846240000000 : ℚ)), ((8137312483122075804659 : ℚ) / (95264541632136800000000 : ℚ)), ((5893906240908709805749 : ℚ) / (77943715880839200000000 : ℚ)), ((1494240211739263390141 : ℚ) / (38971857940419600000000 : ℚ)), ((1408316898871701887281 : ℚ) / (38971857940419600000000 : ℚ)), ((1387107638221163542561 : ℚ) / (38971857940419600000000 : ℚ)), ((28799548647703805171 : ℚ) / (887557841293200000000 : ℚ))],
    jensenBound := ((1574782395511474045446576336675830132348075572098638103476534520304316573824198833034671864563660612223541561900706317132952104364626832959250772910774093888246956644053625241600000000000000000000 : ℚ) / (1260521715647726388108865720840256908010704239462410870507707937588022834945649618801011689285694375264996710917893054931237034887518372313564430814963149589324697649285225414902344227585183907312806297482229 : ℚ)),
    jensenFloorQ96 := (98980536398036791 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_simplexId_before"
  err.flush

theorem geometryRow015_simplexId_read :
    geometryRowsJson015.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped015.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_vertexIds_before"
  err.flush

theorem geometryRow015_vertexIds_read :
    geometryRowsJson015.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped015.vertexIds := by decide +kernel

noncomputable def geometryRow015_physicalVolumeNumeratorChars : List Char := ['2', '7', '7', '6', '6', '6', '0', '4', '0', '5', '9', '0', '9', '2', '1', '6', '9', '4', '4', '8', '2', '9', '0', '0', '8', '7', '8', '9', '3', '3', '0', '9', '5', '1', '8', '9', '2', '3', '0', '7', '2', '3', '3', '7', '0', '9', '9']
noncomputable def geometryRow015_physicalVolumeDenominatorChars : List Char := ['1', '5', '3', '1', '2', '4', '7', '8', '9', '7', '2', '9', '4', '4', '3', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_physicalVolumeText : String := String.ofList (geometryRow015_physicalVolumeNumeratorChars ++ '/' :: geometryRow015_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_physicalVolume_before_field"
  err.flush

theorem geometryRow015_physicalVolume_field :
    geometryRowsJson015.getObjVal? "physical_volume" = .ok (.str geometryRow015_physicalVolumeText) := by rfl

theorem geometryRow015_physicalVolume_numerator_no_slash :
    geometryRow015_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeNumeratorChars = some (27766604059092169448290087893309518923072337099 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeDenominatorChars = some (153124789729443840000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_nonzero : (153124789729443840000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_physicalVolume_parse :
    parseRational geometryRow015_physicalVolumeText = .ok geometryRowsTyped015.physicalVolume :=
  original_rational_fraction_of_chars geometryRow015_physicalVolumeNumeratorChars geometryRow015_physicalVolumeDenominatorChars
    (27766604059092169448290087893309518923072337099 : Int) (153124789729443840000000000000000000000000000000000000000000000000000 : Int)
    geometryRow015_physicalVolume_numerator_no_slash geometryRow015_physicalVolume_numerator_parse
    geometryRow015_physicalVolume_denominator_parse geometryRow015_physicalVolume_denominator_nonzero

theorem geometryRow015_physicalVolume_read :
    rationalField geometryRowsJson015 "physical_volume" = .ok geometryRowsTyped015.physicalVolume :=
  original_rationalField_of_string geometryRowsJson015 "physical_volume" geometryRow015_physicalVolumeText
    geometryRowsTyped015.physicalVolume geometryRow015_physicalVolume_field geometryRow015_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_physicalVolume_complete"
  err.flush

noncomputable def geometryRow015_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow015_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_meanGapText : String := String.ofList (geometryRow015_meanGapNumeratorChars ++ '/' :: geometryRow015_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_meanGap_before_field"
  err.flush

theorem geometryRow015_meanGap_field :
    geometryRowsJson015.getObjVal? "mean_gap" = .ok (.str geometryRow015_meanGapText) := by rfl

theorem geometryRow015_meanGap_numerator_no_slash :
    geometryRow015_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_meanGap_numerator_parse :
    SourceJson.intChars geometryRow015_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_parse :
    SourceJson.intChars geometryRow015_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_meanGap_parse :
    parseRational geometryRow015_meanGapText = .ok geometryRowsTyped015.meanGap :=
  original_rational_fraction_of_chars geometryRow015_meanGapNumeratorChars geometryRow015_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow015_meanGap_numerator_no_slash geometryRow015_meanGap_numerator_parse
    geometryRow015_meanGap_denominator_parse geometryRow015_meanGap_denominator_nonzero

theorem geometryRow015_meanGap_read :
    rationalField geometryRowsJson015 "mean_gap" = .ok geometryRowsTyped015.meanGap :=
  original_rationalField_of_string geometryRowsJson015 "mean_gap" geometryRow015_meanGapText
    geometryRowsTyped015.meanGap geometryRow015_meanGap_field geometryRow015_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_meanGap_complete"
  err.flush

noncomputable def geometryRow015_jensenBoundNumeratorChars : List Char := ['1', '5', '7', '4', '7', '8', '2', '3', '9', '5', '5', '1', '1', '4', '7', '4', '0', '4', '5', '4', '4', '6', '5', '7', '6', '3', '3', '6', '6', '7', '5', '8', '3', '0', '1', '3', '2', '3', '4', '8', '0', '7', '5', '5', '7', '2', '0', '9', '8', '6', '3', '8', '1', '0', '3', '4', '7', '6', '5', '3', '4', '5', '2', '0', '3', '0', '4', '3', '1', '6', '5', '7', '3', '8', '2', '4', '1', '9', '8', '8', '3', '3', '0', '3', '4', '6', '7', '1', '8', '6', '4', '5', '6', '3', '6', '6', '0', '6', '1', '2', '2', '2', '3', '5', '4', '1', '5', '6', '1', '9', '0', '0', '7', '0', '6', '3', '1', '7', '1', '3', '2', '9', '5', '2', '1', '0', '4', '3', '6', '4', '6', '2', '6', '8', '3', '2', '9', '5', '9', '2', '5', '0', '7', '7', '2', '9', '1', '0', '7', '7', '4', '0', '9', '3', '8', '8', '8', '2', '4', '6', '9', '5', '6', '6', '4', '4', '0', '5', '3', '6', '2', '5', '2', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_jensenBoundDenominatorChars : List Char := ['1', '2', '6', '0', '5', '2', '1', '7', '1', '5', '6', '4', '7', '7', '2', '6', '3', '8', '8', '1', '0', '8', '8', '6', '5', '7', '2', '0', '8', '4', '0', '2', '5', '6', '9', '0', '8', '0', '1', '0', '7', '0', '4', '2', '3', '9', '4', '6', '2', '4', '1', '0', '8', '7', '0', '5', '0', '7', '7', '0', '7', '9', '3', '7', '5', '8', '8', '0', '2', '2', '8', '3', '4', '9', '4', '5', '6', '4', '9', '6', '1', '8', '8', '0', '1', '0', '1', '1', '6', '8', '9', '2', '8', '5', '6', '9', '4', '3', '7', '5', '2', '6', '4', '9', '9', '6', '7', '1', '0', '9', '1', '7', '8', '9', '3', '0', '5', '4', '9', '3', '1', '2', '3', '7', '0', '3', '4', '8', '8', '7', '5', '1', '8', '3', '7', '2', '3', '1', '3', '5', '6', '4', '4', '3', '0', '8', '1', '4', '9', '6', '3', '1', '4', '9', '5', '8', '9', '3', '2', '4', '6', '9', '7', '6', '4', '9', '2', '8', '5', '2', '2', '5', '4', '1', '4', '9', '0', '2', '3', '4', '4', '2', '2', '7', '5', '8', '5', '1', '8', '3', '9', '0', '7', '3', '1', '2', '8', '0', '6', '2', '9', '7', '4', '8', '2', '2', '2', '9']
noncomputable def geometryRow015_jensenBoundText : String := String.ofList (geometryRow015_jensenBoundNumeratorChars ++ '/' :: geometryRow015_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_jensenBound_before_field"
  err.flush

theorem geometryRow015_jensenBound_field :
    geometryRowsJson015.getObjVal? "jensen_bound" = .ok (.str geometryRow015_jensenBoundText) := by rfl

theorem geometryRow015_jensenBound_numerator_no_slash :
    geometryRow015_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow015_jensenBoundNumeratorChars = some (1574782395511474045446576336675830132348075572098638103476534520304316573824198833034671864563660612223541561900706317132952104364626832959250772910774093888246956644053625241600000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow015_jensenBoundDenominatorChars = some (1260521715647726388108865720840256908010704239462410870507707937588022834945649618801011689285694375264996710917893054931237034887518372313564430814963149589324697649285225414902344227585183907312806297482229 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_nonzero : (1260521715647726388108865720840256908010704239462410870507707937588022834945649618801011689285694375264996710917893054931237034887518372313564430814963149589324697649285225414902344227585183907312806297482229 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_jensenBound_parse :
    parseRational geometryRow015_jensenBoundText = .ok geometryRowsTyped015.jensenBound :=
  original_rational_fraction_of_chars geometryRow015_jensenBoundNumeratorChars geometryRow015_jensenBoundDenominatorChars
    (1574782395511474045446576336675830132348075572098638103476534520304316573824198833034671864563660612223541561900706317132952104364626832959250772910774093888246956644053625241600000000000000000000 : Int) (1260521715647726388108865720840256908010704239462410870507707937588022834945649618801011689285694375264996710917893054931237034887518372313564430814963149589324697649285225414902344227585183907312806297482229 : Int)
    geometryRow015_jensenBound_numerator_no_slash geometryRow015_jensenBound_numerator_parse
    geometryRow015_jensenBound_denominator_parse geometryRow015_jensenBound_denominator_nonzero

theorem geometryRow015_jensenBound_read :
    rationalField geometryRowsJson015 "jensen_bound" = .ok geometryRowsTyped015.jensenBound :=
  original_rationalField_of_string geometryRowsJson015 "jensen_bound" geometryRow015_jensenBoundText
    geometryRowsTyped015.jensenBound geometryRow015_jensenBound_field geometryRow015_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_factorMaxima_before"
  err.flush

theorem geometryRow015_factorMaxima_read :
    rationalArrayField geometryRowsJson015 "factor_maxima" = .ok geometryRowsTyped015.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_gapWeightedMeans_before"
  err.flush

theorem geometryRow015_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson015 "gap_weighted_means" = .ok geometryRowsTyped015.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow015_floorChars : List Char := ['9', '8', '9', '8', '0', '5', '3', '6', '3', '9', '8', '0', '3', '6', '7', '9', '1']
noncomputable def geometryRow015_floorText : String := String.ofList geometryRow015_floorChars

theorem geometryRow015_floor_text_read :
    geometryRowsJson015.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow015_floorText := by rfl

theorem geometryRow015_floor_chars_parse :
    SourceJson.intChars geometryRow015_floorChars = some (98980536398036791 : Int) := by decide +kernel

theorem geometryRow015_floor_parse :
    parseInteger geometryRow015_floorText = .ok geometryRowsTyped015.jensenFloorQ96 := by
  simp only [geometryRow015_floorText, parseInteger, String.toList_ofList, geometryRow015_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_015 :
    decodeGeometryRow geometryRowsJson015 = .ok geometryRowsTyped015 :=
  original_geometryRow_of_fields geometryRowsJson015 geometryRowsTyped015 geometryRow015_floorText
    geometryRow015_simplexId_read geometryRow015_vertexIds_read
    geometryRow015_physicalVolume_read geometryRow015_meanGap_read
    geometryRow015_factorMaxima_read geometryRow015_gapWeightedMeans_read
    geometryRow015_jensenBound_read geometryRow015_floor_text_read geometryRow015_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_015_original_decoder_complete"
  err.flush

theorem geometryRow015_shape :
    geometryRowsTyped015.simplexId = 15 ∧
    geometryRowsTyped015.vertexIds.size = 9 ∧ geometryRowsTyped015.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped015.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped015.factorMaxima.size = 10 ∧ geometryRowsTyped015.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock001 : List SourceJson := [geometryRowsJson008, geometryRowsJson009, geometryRowsJson010, geometryRowsJson011, geometryRowsJson012, geometryRowsJson013, geometryRowsJson014, geometryRowsJson015]
noncomputable def geometryRowsTypedBlock001 : List GeometryRow := [geometryRowsTyped008, geometryRowsTyped009, geometryRowsTyped010, geometryRowsTyped011, geometryRowsTyped012, geometryRowsTyped013, geometryRowsTyped014, geometryRowsTyped015]

theorem geometry_Rows_block_001_push_eq (acc : List SourceJson) :
    SimplicesBlock001.blockPush acc = [geometryRowsJson015, geometryRowsJson014, geometryRowsJson013, geometryRowsJson012, geometryRowsJson011, geometryRowsJson010, geometryRowsJson009, geometryRowsJson008] ++ acc := by rfl

theorem geometry_Rows_block_001_reverse (acc : List SourceJson) :
    (SimplicesBlock001.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock001 := by
  rw [geometry_Rows_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_001 :
    geometryRowsJsonBlock001.mapM decodeGeometryRow = .ok geometryRowsTypedBlock001 := by
  simp only [geometryRowsJsonBlock001, geometryRowsTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_008, decode_geometry_Rows_009, decode_geometry_Rows_010, decode_geometry_Rows_011, decode_geometry_Rows_012, decode_geometry_Rows_013, decode_geometry_Rows_014, decode_geometry_Rows_015]
  rfl

theorem geometry_Rows_block_001_length : geometryRowsTypedBlock001.length = 8 := by rfl

#print axioms geometryRow008_simplexId_read
#print axioms geometryRow008_vertexIds_read
#print axioms geometryRow008_physicalVolume_field
#print axioms geometryRow008_physicalVolume_numerator_no_slash
#print axioms geometryRow008_physicalVolume_numerator_parse
#print axioms geometryRow008_physicalVolume_denominator_parse
#print axioms geometryRow008_physicalVolume_denominator_nonzero
#print axioms geometryRow008_physicalVolume_parse
#print axioms geometryRow008_physicalVolume_read
#print axioms geometryRow008_meanGap_field
#print axioms geometryRow008_meanGap_numerator_no_slash
#print axioms geometryRow008_meanGap_numerator_parse
#print axioms geometryRow008_meanGap_denominator_parse
#print axioms geometryRow008_meanGap_denominator_nonzero
#print axioms geometryRow008_meanGap_parse
#print axioms geometryRow008_meanGap_read
#print axioms geometryRow008_jensenBound_field
#print axioms geometryRow008_jensenBound_numerator_no_slash
#print axioms geometryRow008_jensenBound_numerator_parse
#print axioms geometryRow008_jensenBound_denominator_parse
#print axioms geometryRow008_jensenBound_denominator_nonzero
#print axioms geometryRow008_jensenBound_parse
#print axioms geometryRow008_jensenBound_read
#print axioms geometryRow008_factorMaxima_read
#print axioms geometryRow008_gapWeightedMeans_read
#print axioms geometryRow008_floor_text_read
#print axioms geometryRow008_floor_chars_parse
#print axioms geometryRow008_floor_parse
#print axioms decode_geometry_Rows_008
#print axioms geometryRow008_shape
#print axioms geometryRow009_simplexId_read
#print axioms geometryRow009_vertexIds_read
#print axioms geometryRow009_physicalVolume_field
#print axioms geometryRow009_physicalVolume_numerator_no_slash
#print axioms geometryRow009_physicalVolume_numerator_parse
#print axioms geometryRow009_physicalVolume_denominator_parse
#print axioms geometryRow009_physicalVolume_denominator_nonzero
#print axioms geometryRow009_physicalVolume_parse
#print axioms geometryRow009_physicalVolume_read
#print axioms geometryRow009_meanGap_field
#print axioms geometryRow009_meanGap_numerator_no_slash
#print axioms geometryRow009_meanGap_numerator_parse
#print axioms geometryRow009_meanGap_denominator_parse
#print axioms geometryRow009_meanGap_denominator_nonzero
#print axioms geometryRow009_meanGap_parse
#print axioms geometryRow009_meanGap_read
#print axioms geometryRow009_jensenBound_field
#print axioms geometryRow009_jensenBound_numerator_no_slash
#print axioms geometryRow009_jensenBound_numerator_parse
#print axioms geometryRow009_jensenBound_denominator_parse
#print axioms geometryRow009_jensenBound_denominator_nonzero
#print axioms geometryRow009_jensenBound_parse
#print axioms geometryRow009_jensenBound_read
#print axioms geometryRow009_factorMaxima_read
#print axioms geometryRow009_gapWeightedMeans_read
#print axioms geometryRow009_floor_text_read
#print axioms geometryRow009_floor_chars_parse
#print axioms geometryRow009_floor_parse
#print axioms decode_geometry_Rows_009
#print axioms geometryRow009_shape
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
#print axioms geometryRow010_shape
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
#print axioms geometryRow011_shape
#print axioms geometryRow012_simplexId_read
#print axioms geometryRow012_vertexIds_read
#print axioms geometryRow012_physicalVolume_field
#print axioms geometryRow012_physicalVolume_numerator_no_slash
#print axioms geometryRow012_physicalVolume_numerator_parse
#print axioms geometryRow012_physicalVolume_denominator_parse
#print axioms geometryRow012_physicalVolume_denominator_nonzero
#print axioms geometryRow012_physicalVolume_parse
#print axioms geometryRow012_physicalVolume_read
#print axioms geometryRow012_meanGap_field
#print axioms geometryRow012_meanGap_numerator_no_slash
#print axioms geometryRow012_meanGap_numerator_parse
#print axioms geometryRow012_meanGap_denominator_parse
#print axioms geometryRow012_meanGap_denominator_nonzero
#print axioms geometryRow012_meanGap_parse
#print axioms geometryRow012_meanGap_read
#print axioms geometryRow012_jensenBound_field
#print axioms geometryRow012_jensenBound_numerator_no_slash
#print axioms geometryRow012_jensenBound_numerator_parse
#print axioms geometryRow012_jensenBound_denominator_parse
#print axioms geometryRow012_jensenBound_denominator_nonzero
#print axioms geometryRow012_jensenBound_parse
#print axioms geometryRow012_jensenBound_read
#print axioms geometryRow012_factorMaxima_read
#print axioms geometryRow012_gapWeightedMeans_read
#print axioms geometryRow012_floor_text_read
#print axioms geometryRow012_floor_chars_parse
#print axioms geometryRow012_floor_parse
#print axioms decode_geometry_Rows_012
#print axioms geometryRow012_shape
#print axioms geometryRow013_simplexId_read
#print axioms geometryRow013_vertexIds_read
#print axioms geometryRow013_physicalVolume_field
#print axioms geometryRow013_physicalVolume_numerator_no_slash
#print axioms geometryRow013_physicalVolume_numerator_parse
#print axioms geometryRow013_physicalVolume_denominator_parse
#print axioms geometryRow013_physicalVolume_denominator_nonzero
#print axioms geometryRow013_physicalVolume_parse
#print axioms geometryRow013_physicalVolume_read
#print axioms geometryRow013_meanGap_field
#print axioms geometryRow013_meanGap_numerator_no_slash
#print axioms geometryRow013_meanGap_numerator_parse
#print axioms geometryRow013_meanGap_denominator_parse
#print axioms geometryRow013_meanGap_denominator_nonzero
#print axioms geometryRow013_meanGap_parse
#print axioms geometryRow013_meanGap_read
#print axioms geometryRow013_jensenBound_field
#print axioms geometryRow013_jensenBound_numerator_no_slash
#print axioms geometryRow013_jensenBound_numerator_parse
#print axioms geometryRow013_jensenBound_denominator_parse
#print axioms geometryRow013_jensenBound_denominator_nonzero
#print axioms geometryRow013_jensenBound_parse
#print axioms geometryRow013_jensenBound_read
#print axioms geometryRow013_factorMaxima_read
#print axioms geometryRow013_gapWeightedMeans_read
#print axioms geometryRow013_floor_text_read
#print axioms geometryRow013_floor_chars_parse
#print axioms geometryRow013_floor_parse
#print axioms decode_geometry_Rows_013
#print axioms geometryRow013_shape
#print axioms geometryRow014_simplexId_read
#print axioms geometryRow014_vertexIds_read
#print axioms geometryRow014_physicalVolume_field
#print axioms geometryRow014_physicalVolume_numerator_no_slash
#print axioms geometryRow014_physicalVolume_numerator_parse
#print axioms geometryRow014_physicalVolume_denominator_parse
#print axioms geometryRow014_physicalVolume_denominator_nonzero
#print axioms geometryRow014_physicalVolume_parse
#print axioms geometryRow014_physicalVolume_read
#print axioms geometryRow014_meanGap_field
#print axioms geometryRow014_meanGap_numerator_no_slash
#print axioms geometryRow014_meanGap_numerator_parse
#print axioms geometryRow014_meanGap_denominator_parse
#print axioms geometryRow014_meanGap_denominator_nonzero
#print axioms geometryRow014_meanGap_parse
#print axioms geometryRow014_meanGap_read
#print axioms geometryRow014_jensenBound_field
#print axioms geometryRow014_jensenBound_numerator_no_slash
#print axioms geometryRow014_jensenBound_numerator_parse
#print axioms geometryRow014_jensenBound_denominator_parse
#print axioms geometryRow014_jensenBound_denominator_nonzero
#print axioms geometryRow014_jensenBound_parse
#print axioms geometryRow014_jensenBound_read
#print axioms geometryRow014_factorMaxima_read
#print axioms geometryRow014_gapWeightedMeans_read
#print axioms geometryRow014_floor_text_read
#print axioms geometryRow014_floor_chars_parse
#print axioms geometryRow014_floor_parse
#print axioms decode_geometry_Rows_014
#print axioms geometryRow014_shape
#print axioms geometryRow015_simplexId_read
#print axioms geometryRow015_vertexIds_read
#print axioms geometryRow015_physicalVolume_field
#print axioms geometryRow015_physicalVolume_numerator_no_slash
#print axioms geometryRow015_physicalVolume_numerator_parse
#print axioms geometryRow015_physicalVolume_denominator_parse
#print axioms geometryRow015_physicalVolume_denominator_nonzero
#print axioms geometryRow015_physicalVolume_parse
#print axioms geometryRow015_physicalVolume_read
#print axioms geometryRow015_meanGap_field
#print axioms geometryRow015_meanGap_numerator_no_slash
#print axioms geometryRow015_meanGap_numerator_parse
#print axioms geometryRow015_meanGap_denominator_parse
#print axioms geometryRow015_meanGap_denominator_nonzero
#print axioms geometryRow015_meanGap_parse
#print axioms geometryRow015_meanGap_read
#print axioms geometryRow015_jensenBound_field
#print axioms geometryRow015_jensenBound_numerator_no_slash
#print axioms geometryRow015_jensenBound_numerator_parse
#print axioms geometryRow015_jensenBound_denominator_parse
#print axioms geometryRow015_jensenBound_denominator_nonzero
#print axioms geometryRow015_jensenBound_parse
#print axioms geometryRow015_jensenBound_read
#print axioms geometryRow015_factorMaxima_read
#print axioms geometryRow015_gapWeightedMeans_read
#print axioms geometryRow015_floor_text_read
#print axioms geometryRow015_floor_chars_parse
#print axioms geometryRow015_floor_parse
#print axioms decode_geometry_Rows_015
#print axioms geometryRow015_shape
#print axioms geometry_Rows_block_001_push_eq
#print axioms geometry_Rows_block_001_reverse
#print axioms decode_geometry_Rows_block_001
#print axioms geometry_Rows_block_001_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
