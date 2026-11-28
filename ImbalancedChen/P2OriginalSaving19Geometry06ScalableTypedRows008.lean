import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock008

/-! Local typed certificates for original cell 06, rows 64 through 71.
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

noncomputable def geometryRowsJson064 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped064 : GeometryRow :=
  { simplexId := 64,
    vertexIds := #[32, 30, 28, 26, 14, 12, 10, 8, 0],
    physicalVolume := ((213448968611622653866607354858314127 : ℚ) / (3995022923136000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((1327309003907 : ℚ) / (15255900000000 : ℚ)), ((21054047039 : ℚ) / (238373437500 : ℚ)), ((1891110314557 : ℚ) / (16018695000000 : ℚ)), ((14507235676163 : ℚ) / (160186950000000 : ℚ)), ((14420187765983 : ℚ) / (160186950000000 : ℚ)), ((2161195152407 : ℚ) / (29124900000000 : ℚ)), ((2294452526417 : ℚ) / (58249800000000 : ℚ)), ((282276447251 : ℚ) / (8321400000000 : ℚ)), ((273224142131 : ℚ) / (8321400000000 : ℚ)), ((172404927917 : ℚ) / (5720962500000 : ℚ))],
    jensenBound := ((157542415445249693772888194274738857971977001769551848459066500420017961973254690812774658203125000000000 : ℚ) / (728947959587575132354296163893217549487702276246181029643794151445845945640230456727223829372012161297195562304318820447 : ℚ)),
    jensenFloorQ96 := (17123027686157 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_simplexId_before"
  err.flush

theorem geometryRow064_simplexId_read :
    geometryRowsJson064.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped064.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_vertexIds_before"
  err.flush

theorem geometryRow064_vertexIds_read :
    geometryRowsJson064.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped064.vertexIds := by decide +kernel

noncomputable def geometryRow064_physicalVolumeNumeratorChars : List Char := ['2', '1', '3', '4', '4', '8', '9', '6', '8', '6', '1', '1', '6', '2', '2', '6', '5', '3', '8', '6', '6', '6', '0', '7', '3', '5', '4', '8', '5', '8', '3', '1', '4', '1', '2', '7']
noncomputable def geometryRow064_physicalVolumeDenominatorChars : List Char := ['3', '9', '9', '5', '0', '2', '2', '9', '2', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow064_physicalVolumeText : String := String.ofList (geometryRow064_physicalVolumeNumeratorChars ++ '/' :: geometryRow064_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_physicalVolume_before_field"
  err.flush

theorem geometryRow064_physicalVolume_field :
    geometryRowsJson064.getObjVal? "physical_volume" = .ok (.str geometryRow064_physicalVolumeText) := by rfl

theorem geometryRow064_physicalVolume_numerator_no_slash :
    geometryRow064_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow064_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow064_physicalVolumeNumeratorChars = some (213448968611622653866607354858314127 : Int) := by decide +kernel

theorem geometryRow064_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow064_physicalVolumeDenominatorChars = some (3995022923136000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow064_physicalVolume_denominator_nonzero : (3995022923136000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow064_physicalVolume_parse :
    parseRational geometryRow064_physicalVolumeText = .ok geometryRowsTyped064.physicalVolume :=
  original_rational_fraction_of_chars geometryRow064_physicalVolumeNumeratorChars geometryRow064_physicalVolumeDenominatorChars
    (213448968611622653866607354858314127 : Int) (3995022923136000000000000000000000000000000000000000000000000 : Int)
    geometryRow064_physicalVolume_numerator_no_slash geometryRow064_physicalVolume_numerator_parse
    geometryRow064_physicalVolume_denominator_parse geometryRow064_physicalVolume_denominator_nonzero

theorem geometryRow064_physicalVolume_read :
    rationalField geometryRowsJson064 "physical_volume" = .ok geometryRowsTyped064.physicalVolume :=
  original_rationalField_of_string geometryRowsJson064 "physical_volume" geometryRow064_physicalVolumeText
    geometryRowsTyped064.physicalVolume geometryRow064_physicalVolume_field geometryRow064_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_physicalVolume_complete"
  err.flush

noncomputable def geometryRow064_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow064_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow064_meanGapText : String := String.ofList (geometryRow064_meanGapNumeratorChars ++ '/' :: geometryRow064_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_meanGap_before_field"
  err.flush

theorem geometryRow064_meanGap_field :
    geometryRowsJson064.getObjVal? "mean_gap" = .ok (.str geometryRow064_meanGapText) := by rfl

theorem geometryRow064_meanGap_numerator_no_slash :
    geometryRow064_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow064_meanGap_numerator_parse :
    SourceJson.intChars geometryRow064_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow064_meanGap_denominator_parse :
    SourceJson.intChars geometryRow064_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow064_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow064_meanGap_parse :
    parseRational geometryRow064_meanGapText = .ok geometryRowsTyped064.meanGap :=
  original_rational_fraction_of_chars geometryRow064_meanGapNumeratorChars geometryRow064_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow064_meanGap_numerator_no_slash geometryRow064_meanGap_numerator_parse
    geometryRow064_meanGap_denominator_parse geometryRow064_meanGap_denominator_nonzero

theorem geometryRow064_meanGap_read :
    rationalField geometryRowsJson064 "mean_gap" = .ok geometryRowsTyped064.meanGap :=
  original_rationalField_of_string geometryRowsJson064 "mean_gap" geometryRow064_meanGapText
    geometryRowsTyped064.meanGap geometryRow064_meanGap_field geometryRow064_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_meanGap_complete"
  err.flush

noncomputable def geometryRow064_jensenBoundNumeratorChars : List Char := ['1', '5', '7', '5', '4', '2', '4', '1', '5', '4', '4', '5', '2', '4', '9', '6', '9', '3', '7', '7', '2', '8', '8', '8', '1', '9', '4', '2', '7', '4', '7', '3', '8', '8', '5', '7', '9', '7', '1', '9', '7', '7', '0', '0', '1', '7', '6', '9', '5', '5', '1', '8', '4', '8', '4', '5', '9', '0', '6', '6', '5', '0', '0', '4', '2', '0', '0', '1', '7', '9', '6', '1', '9', '7', '3', '2', '5', '4', '6', '9', '0', '8', '1', '2', '7', '7', '4', '6', '5', '8', '2', '0', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow064_jensenBoundDenominatorChars : List Char := ['7', '2', '8', '9', '4', '7', '9', '5', '9', '5', '8', '7', '5', '7', '5', '1', '3', '2', '3', '5', '4', '2', '9', '6', '1', '6', '3', '8', '9', '3', '2', '1', '7', '5', '4', '9', '4', '8', '7', '7', '0', '2', '2', '7', '6', '2', '4', '6', '1', '8', '1', '0', '2', '9', '6', '4', '3', '7', '9', '4', '1', '5', '1', '4', '4', '5', '8', '4', '5', '9', '4', '5', '6', '4', '0', '2', '3', '0', '4', '5', '6', '7', '2', '7', '2', '2', '3', '8', '2', '9', '3', '7', '2', '0', '1', '2', '1', '6', '1', '2', '9', '7', '1', '9', '5', '5', '6', '2', '3', '0', '4', '3', '1', '8', '8', '2', '0', '4', '4', '7']
noncomputable def geometryRow064_jensenBoundText : String := String.ofList (geometryRow064_jensenBoundNumeratorChars ++ '/' :: geometryRow064_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_jensenBound_before_field"
  err.flush

theorem geometryRow064_jensenBound_field :
    geometryRowsJson064.getObjVal? "jensen_bound" = .ok (.str geometryRow064_jensenBoundText) := by rfl

theorem geometryRow064_jensenBound_numerator_no_slash :
    geometryRow064_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow064_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow064_jensenBoundNumeratorChars = some (157542415445249693772888194274738857971977001769551848459066500420017961973254690812774658203125000000000 : Int) := by decide +kernel

theorem geometryRow064_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow064_jensenBoundDenominatorChars = some (728947959587575132354296163893217549487702276246181029643794151445845945640230456727223829372012161297195562304318820447 : Int) := by decide +kernel

theorem geometryRow064_jensenBound_denominator_nonzero : (728947959587575132354296163893217549487702276246181029643794151445845945640230456727223829372012161297195562304318820447 : Int) ≠ 0 := by decide +kernel

theorem geometryRow064_jensenBound_parse :
    parseRational geometryRow064_jensenBoundText = .ok geometryRowsTyped064.jensenBound :=
  original_rational_fraction_of_chars geometryRow064_jensenBoundNumeratorChars geometryRow064_jensenBoundDenominatorChars
    (157542415445249693772888194274738857971977001769551848459066500420017961973254690812774658203125000000000 : Int) (728947959587575132354296163893217549487702276246181029643794151445845945640230456727223829372012161297195562304318820447 : Int)
    geometryRow064_jensenBound_numerator_no_slash geometryRow064_jensenBound_numerator_parse
    geometryRow064_jensenBound_denominator_parse geometryRow064_jensenBound_denominator_nonzero

theorem geometryRow064_jensenBound_read :
    rationalField geometryRowsJson064 "jensen_bound" = .ok geometryRowsTyped064.jensenBound :=
  original_rationalField_of_string geometryRowsJson064 "jensen_bound" geometryRow064_jensenBoundText
    geometryRowsTyped064.jensenBound geometryRow064_jensenBound_field geometryRow064_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_factorMaxima_before"
  err.flush

theorem geometryRow064_factorMaxima_read :
    rationalArrayField geometryRowsJson064 "factor_maxima" = .ok geometryRowsTyped064.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_gapWeightedMeans_before"
  err.flush

theorem geometryRow064_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson064 "gap_weighted_means" = .ok geometryRowsTyped064.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow064_floorChars : List Char := ['1', '7', '1', '2', '3', '0', '2', '7', '6', '8', '6', '1', '5', '7']
noncomputable def geometryRow064_floorText : String := String.ofList geometryRow064_floorChars

theorem geometryRow064_floor_text_read :
    geometryRowsJson064.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow064_floorText := by rfl

theorem geometryRow064_floor_chars_parse :
    SourceJson.intChars geometryRow064_floorChars = some (17123027686157 : Int) := by decide +kernel

theorem geometryRow064_floor_parse :
    parseInteger geometryRow064_floorText = .ok geometryRowsTyped064.jensenFloorQ96 := by
  simp only [geometryRow064_floorText, parseInteger, String.toList_ofList, geometryRow064_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_064 :
    decodeGeometryRow geometryRowsJson064 = .ok geometryRowsTyped064 :=
  original_geometryRow_of_fields geometryRowsJson064 geometryRowsTyped064 geometryRow064_floorText
    geometryRow064_simplexId_read geometryRow064_vertexIds_read
    geometryRow064_physicalVolume_read geometryRow064_meanGap_read
    geometryRow064_factorMaxima_read geometryRow064_gapWeightedMeans_read
    geometryRow064_jensenBound_read geometryRow064_floor_text_read geometryRow064_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_064_original_decoder_complete"
  err.flush

theorem geometryRow064_shape :
    geometryRowsTyped064.simplexId = 64 ∧
    geometryRowsTyped064.vertexIds.size = 9 ∧ geometryRowsTyped064.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped064.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped064.factorMaxima.size = 10 ∧ geometryRowsTyped064.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson065 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped065 : GeometryRow :=
  { simplexId := 65,
    vertexIds := #[32, 30, 28, 26, 14, 12, 11, 3, 0],
    physicalVolume := ((70325197437775101036445338034849558933 : ℚ) / (395885399132160000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((31729387 : ℚ) / (21285000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((51243353961049698043711 : ℚ) / (582808667580493200000000 : ℚ)), ((26208156257418983599379 : ℚ) / (291404333790246600000000 : ℚ)), ((13738454852445772526659 : ℚ) / (116561733516098640000000 : ℚ)), ((17720853036987498130921 : ℚ) / (194269555860164400000000 : ℚ)), ((17615284144832275228361 : ℚ) / (194269555860164400000000 : ℚ)), ((3868421556748315125941 : ℚ) / (52982606143681200000000 : ℚ)), ((4007365603006218518591 : ℚ) / (105965212287362400000000 : ℚ)), ((3634876814922744456971 : ℚ) / (105965212287362400000000 : ℚ)), ((1692816492338186678773 : ℚ) / (52982606143681200000000 : ℚ)), ((8938398938089033768513 : ℚ) / (291404333790246600000000 : ℚ))],
    jensenBound := ((7268859255068446462848933487548557996136795345248539517813760261728782076036018614412294242600239094576584339605729252593188915328597575213806056568236052715289277931502434539121868800000000000000000000000000 : ℚ) / (4910641823127826578152416034209183774169749980658163399132962821240523131821405488537837372374240041304426803708180862645209994983474750175136356782948982798994118034622359492755576217017183569954731140014099712621102699 : ℚ)),
    jensenFloorQ96 := (117275578854386821 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_simplexId_before"
  err.flush

theorem geometryRow065_simplexId_read :
    geometryRowsJson065.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped065.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_vertexIds_before"
  err.flush

theorem geometryRow065_vertexIds_read :
    geometryRowsJson065.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped065.vertexIds := by decide +kernel

noncomputable def geometryRow065_physicalVolumeNumeratorChars : List Char := ['7', '0', '3', '2', '5', '1', '9', '7', '4', '3', '7', '7', '7', '5', '1', '0', '1', '0', '3', '6', '4', '4', '5', '3', '3', '8', '0', '3', '4', '8', '4', '9', '5', '5', '8', '9', '3', '3']
noncomputable def geometryRow065_physicalVolumeDenominatorChars : List Char := ['3', '9', '5', '8', '8', '5', '3', '9', '9', '1', '3', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow065_physicalVolumeText : String := String.ofList (geometryRow065_physicalVolumeNumeratorChars ++ '/' :: geometryRow065_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_physicalVolume_before_field"
  err.flush

theorem geometryRow065_physicalVolume_field :
    geometryRowsJson065.getObjVal? "physical_volume" = .ok (.str geometryRow065_physicalVolumeText) := by rfl

theorem geometryRow065_physicalVolume_numerator_no_slash :
    geometryRow065_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow065_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow065_physicalVolumeNumeratorChars = some (70325197437775101036445338034849558933 : Int) := by decide +kernel

theorem geometryRow065_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow065_physicalVolumeDenominatorChars = some (395885399132160000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow065_physicalVolume_denominator_nonzero : (395885399132160000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow065_physicalVolume_parse :
    parseRational geometryRow065_physicalVolumeText = .ok geometryRowsTyped065.physicalVolume :=
  original_rational_fraction_of_chars geometryRow065_physicalVolumeNumeratorChars geometryRow065_physicalVolumeDenominatorChars
    (70325197437775101036445338034849558933 : Int) (395885399132160000000000000000000000000000000000000000000000 : Int)
    geometryRow065_physicalVolume_numerator_no_slash geometryRow065_physicalVolume_numerator_parse
    geometryRow065_physicalVolume_denominator_parse geometryRow065_physicalVolume_denominator_nonzero

theorem geometryRow065_physicalVolume_read :
    rationalField geometryRowsJson065 "physical_volume" = .ok geometryRowsTyped065.physicalVolume :=
  original_rationalField_of_string geometryRowsJson065 "physical_volume" geometryRow065_physicalVolumeText
    geometryRowsTyped065.physicalVolume geometryRow065_physicalVolume_field geometryRow065_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_physicalVolume_complete"
  err.flush

noncomputable def geometryRow065_meanGapNumeratorChars : List Char := ['3', '1', '7', '2', '9', '3', '8', '7']
noncomputable def geometryRow065_meanGapDenominatorChars : List Char := ['2', '1', '2', '8', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow065_meanGapText : String := String.ofList (geometryRow065_meanGapNumeratorChars ++ '/' :: geometryRow065_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_meanGap_before_field"
  err.flush

theorem geometryRow065_meanGap_field :
    geometryRowsJson065.getObjVal? "mean_gap" = .ok (.str geometryRow065_meanGapText) := by rfl

theorem geometryRow065_meanGap_numerator_no_slash :
    geometryRow065_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow065_meanGap_numerator_parse :
    SourceJson.intChars geometryRow065_meanGapNumeratorChars = some (31729387 : Int) := by decide +kernel

theorem geometryRow065_meanGap_denominator_parse :
    SourceJson.intChars geometryRow065_meanGapDenominatorChars = some (21285000000 : Int) := by decide +kernel

theorem geometryRow065_meanGap_denominator_nonzero : (21285000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow065_meanGap_parse :
    parseRational geometryRow065_meanGapText = .ok geometryRowsTyped065.meanGap :=
  original_rational_fraction_of_chars geometryRow065_meanGapNumeratorChars geometryRow065_meanGapDenominatorChars
    (31729387 : Int) (21285000000 : Int)
    geometryRow065_meanGap_numerator_no_slash geometryRow065_meanGap_numerator_parse
    geometryRow065_meanGap_denominator_parse geometryRow065_meanGap_denominator_nonzero

theorem geometryRow065_meanGap_read :
    rationalField geometryRowsJson065 "mean_gap" = .ok geometryRowsTyped065.meanGap :=
  original_rationalField_of_string geometryRowsJson065 "mean_gap" geometryRow065_meanGapText
    geometryRowsTyped065.meanGap geometryRow065_meanGap_field geometryRow065_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_meanGap_complete"
  err.flush

noncomputable def geometryRow065_jensenBoundNumeratorChars : List Char := ['7', '2', '6', '8', '8', '5', '9', '2', '5', '5', '0', '6', '8', '4', '4', '6', '4', '6', '2', '8', '4', '8', '9', '3', '3', '4', '8', '7', '5', '4', '8', '5', '5', '7', '9', '9', '6', '1', '3', '6', '7', '9', '5', '3', '4', '5', '2', '4', '8', '5', '3', '9', '5', '1', '7', '8', '1', '3', '7', '6', '0', '2', '6', '1', '7', '2', '8', '7', '8', '2', '0', '7', '6', '0', '3', '6', '0', '1', '8', '6', '1', '4', '4', '1', '2', '2', '9', '4', '2', '4', '2', '6', '0', '0', '2', '3', '9', '0', '9', '4', '5', '7', '6', '5', '8', '4', '3', '3', '9', '6', '0', '5', '7', '2', '9', '2', '5', '2', '5', '9', '3', '1', '8', '8', '9', '1', '5', '3', '2', '8', '5', '9', '7', '5', '7', '5', '2', '1', '3', '8', '0', '6', '0', '5', '6', '5', '6', '8', '2', '3', '6', '0', '5', '2', '7', '1', '5', '2', '8', '9', '2', '7', '7', '9', '3', '1', '5', '0', '2', '4', '3', '4', '5', '3', '9', '1', '2', '1', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow065_jensenBoundDenominatorChars : List Char := ['4', '9', '1', '0', '6', '4', '1', '8', '2', '3', '1', '2', '7', '8', '2', '6', '5', '7', '8', '1', '5', '2', '4', '1', '6', '0', '3', '4', '2', '0', '9', '1', '8', '3', '7', '7', '4', '1', '6', '9', '7', '4', '9', '9', '8', '0', '6', '5', '8', '1', '6', '3', '3', '9', '9', '1', '3', '2', '9', '6', '2', '8', '2', '1', '2', '4', '0', '5', '2', '3', '1', '3', '1', '8', '2', '1', '4', '0', '5', '4', '8', '8', '5', '3', '7', '8', '3', '7', '3', '7', '2', '3', '7', '4', '2', '4', '0', '0', '4', '1', '3', '0', '4', '4', '2', '6', '8', '0', '3', '7', '0', '8', '1', '8', '0', '8', '6', '2', '6', '4', '5', '2', '0', '9', '9', '9', '4', '9', '8', '3', '4', '7', '4', '7', '5', '0', '1', '7', '5', '1', '3', '6', '3', '5', '6', '7', '8', '2', '9', '4', '8', '9', '8', '2', '7', '9', '8', '9', '9', '4', '1', '1', '8', '0', '3', '4', '6', '2', '2', '3', '5', '9', '4', '9', '2', '7', '5', '5', '5', '7', '6', '2', '1', '7', '0', '1', '7', '1', '8', '3', '5', '6', '9', '9', '5', '4', '7', '3', '1', '1', '4', '0', '0', '1', '4', '0', '9', '9', '7', '1', '2', '6', '2', '1', '1', '0', '2', '6', '9', '9']
noncomputable def geometryRow065_jensenBoundText : String := String.ofList (geometryRow065_jensenBoundNumeratorChars ++ '/' :: geometryRow065_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_jensenBound_before_field"
  err.flush

theorem geometryRow065_jensenBound_field :
    geometryRowsJson065.getObjVal? "jensen_bound" = .ok (.str geometryRow065_jensenBoundText) := by rfl

theorem geometryRow065_jensenBound_numerator_no_slash :
    geometryRow065_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow065_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow065_jensenBoundNumeratorChars = some (7268859255068446462848933487548557996136795345248539517813760261728782076036018614412294242600239094576584339605729252593188915328597575213806056568236052715289277931502434539121868800000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow065_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow065_jensenBoundDenominatorChars = some (4910641823127826578152416034209183774169749980658163399132962821240523131821405488537837372374240041304426803708180862645209994983474750175136356782948982798994118034622359492755576217017183569954731140014099712621102699 : Int) := by decide +kernel

theorem geometryRow065_jensenBound_denominator_nonzero : (4910641823127826578152416034209183774169749980658163399132962821240523131821405488537837372374240041304426803708180862645209994983474750175136356782948982798994118034622359492755576217017183569954731140014099712621102699 : Int) ≠ 0 := by decide +kernel

theorem geometryRow065_jensenBound_parse :
    parseRational geometryRow065_jensenBoundText = .ok geometryRowsTyped065.jensenBound :=
  original_rational_fraction_of_chars geometryRow065_jensenBoundNumeratorChars geometryRow065_jensenBoundDenominatorChars
    (7268859255068446462848933487548557996136795345248539517813760261728782076036018614412294242600239094576584339605729252593188915328597575213806056568236052715289277931502434539121868800000000000000000000000000 : Int) (4910641823127826578152416034209183774169749980658163399132962821240523131821405488537837372374240041304426803708180862645209994983474750175136356782948982798994118034622359492755576217017183569954731140014099712621102699 : Int)
    geometryRow065_jensenBound_numerator_no_slash geometryRow065_jensenBound_numerator_parse
    geometryRow065_jensenBound_denominator_parse geometryRow065_jensenBound_denominator_nonzero

theorem geometryRow065_jensenBound_read :
    rationalField geometryRowsJson065 "jensen_bound" = .ok geometryRowsTyped065.jensenBound :=
  original_rationalField_of_string geometryRowsJson065 "jensen_bound" geometryRow065_jensenBoundText
    geometryRowsTyped065.jensenBound geometryRow065_jensenBound_field geometryRow065_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_factorMaxima_before"
  err.flush

theorem geometryRow065_factorMaxima_read :
    rationalArrayField geometryRowsJson065 "factor_maxima" = .ok geometryRowsTyped065.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_gapWeightedMeans_before"
  err.flush

theorem geometryRow065_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson065 "gap_weighted_means" = .ok geometryRowsTyped065.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow065_floorChars : List Char := ['1', '1', '7', '2', '7', '5', '5', '7', '8', '8', '5', '4', '3', '8', '6', '8', '2', '1']
noncomputable def geometryRow065_floorText : String := String.ofList geometryRow065_floorChars

theorem geometryRow065_floor_text_read :
    geometryRowsJson065.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow065_floorText := by rfl

theorem geometryRow065_floor_chars_parse :
    SourceJson.intChars geometryRow065_floorChars = some (117275578854386821 : Int) := by decide +kernel

theorem geometryRow065_floor_parse :
    parseInteger geometryRow065_floorText = .ok geometryRowsTyped065.jensenFloorQ96 := by
  simp only [geometryRow065_floorText, parseInteger, String.toList_ofList, geometryRow065_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_065 :
    decodeGeometryRow geometryRowsJson065 = .ok geometryRowsTyped065 :=
  original_geometryRow_of_fields geometryRowsJson065 geometryRowsTyped065 geometryRow065_floorText
    geometryRow065_simplexId_read geometryRow065_vertexIds_read
    geometryRow065_physicalVolume_read geometryRow065_meanGap_read
    geometryRow065_factorMaxima_read geometryRow065_gapWeightedMeans_read
    geometryRow065_jensenBound_read geometryRow065_floor_text_read geometryRow065_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_065_original_decoder_complete"
  err.flush

theorem geometryRow065_shape :
    geometryRowsTyped065.simplexId = 65 ∧
    geometryRowsTyped065.vertexIds.size = 9 ∧ geometryRowsTyped065.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped065.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped065.factorMaxima.size = 10 ∧ geometryRowsTyped065.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson066 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped066 : GeometryRow :=
  { simplexId := 66,
    vertexIds := #[32, 30, 28, 26, 14, 12, 11, 8, 0],
    physicalVolume := ((38906837609983867261621570597781353916939 : ℚ) / (49715840821248000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((9291169129709 : ℚ) / (106791300000000 : ℚ)), ((1179027396979 : ℚ) / (13348912500000 : ℚ)), ((472777616779 : ℚ) / (4004673750000 : ℚ)), ((14507234150573 : ℚ) / (160186950000000 : ℚ)), ((14420186240393 : ℚ) / (160186950000000 : ℚ)), ((2161194875027 : ℚ) / (29124900000000 : ℚ)), ((4475146730029 : ℚ) / (116499600000000 : ℚ)), ((4065627474799 : ℚ) / (116499600000000 : ℚ)), ((1912566221117 : ℚ) / (58249800000000 : ℚ)), ((603417629107 : ℚ) / (20023368750000 : ℚ))],
    jensenBound := ((14102995407821022821097680924368609334163930746305577045569930387655677897615835094713141540519714355468750000000 : ℚ) / (4469688331058057609123548540972678488317059823883420985127922022839411282420470275808305525887793170306611411246020222756813 : ℚ)),
    jensenFloorQ96 := (249984860095215916 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_simplexId_before"
  err.flush

theorem geometryRow066_simplexId_read :
    geometryRowsJson066.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped066.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_vertexIds_before"
  err.flush

theorem geometryRow066_vertexIds_read :
    geometryRowsJson066.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped066.vertexIds := by decide +kernel

noncomputable def geometryRow066_physicalVolumeNumeratorChars : List Char := ['3', '8', '9', '0', '6', '8', '3', '7', '6', '0', '9', '9', '8', '3', '8', '6', '7', '2', '6', '1', '6', '2', '1', '5', '7', '0', '5', '9', '7', '7', '8', '1', '3', '5', '3', '9', '1', '6', '9', '3', '9']
noncomputable def geometryRow066_physicalVolumeDenominatorChars : List Char := ['4', '9', '7', '1', '5', '8', '4', '0', '8', '2', '1', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow066_physicalVolumeText : String := String.ofList (geometryRow066_physicalVolumeNumeratorChars ++ '/' :: geometryRow066_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_physicalVolume_before_field"
  err.flush

theorem geometryRow066_physicalVolume_field :
    geometryRowsJson066.getObjVal? "physical_volume" = .ok (.str geometryRow066_physicalVolumeText) := by rfl

theorem geometryRow066_physicalVolume_numerator_no_slash :
    geometryRow066_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow066_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow066_physicalVolumeNumeratorChars = some (38906837609983867261621570597781353916939 : Int) := by decide +kernel

theorem geometryRow066_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow066_physicalVolumeDenominatorChars = some (49715840821248000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow066_physicalVolume_denominator_nonzero : (49715840821248000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow066_physicalVolume_parse :
    parseRational geometryRow066_physicalVolumeText = .ok geometryRowsTyped066.physicalVolume :=
  original_rational_fraction_of_chars geometryRow066_physicalVolumeNumeratorChars geometryRow066_physicalVolumeDenominatorChars
    (38906837609983867261621570597781353916939 : Int) (49715840821248000000000000000000000000000000000000000000000000 : Int)
    geometryRow066_physicalVolume_numerator_no_slash geometryRow066_physicalVolume_numerator_parse
    geometryRow066_physicalVolume_denominator_parse geometryRow066_physicalVolume_denominator_nonzero

theorem geometryRow066_physicalVolume_read :
    rationalField geometryRowsJson066 "physical_volume" = .ok geometryRowsTyped066.physicalVolume :=
  original_rationalField_of_string geometryRowsJson066 "physical_volume" geometryRow066_physicalVolumeText
    geometryRowsTyped066.physicalVolume geometryRow066_physicalVolume_field geometryRow066_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_physicalVolume_complete"
  err.flush

noncomputable def geometryRow066_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow066_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow066_meanGapText : String := String.ofList (geometryRow066_meanGapNumeratorChars ++ '/' :: geometryRow066_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_meanGap_before_field"
  err.flush

theorem geometryRow066_meanGap_field :
    geometryRowsJson066.getObjVal? "mean_gap" = .ok (.str geometryRow066_meanGapText) := by rfl

theorem geometryRow066_meanGap_numerator_no_slash :
    geometryRow066_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow066_meanGap_numerator_parse :
    SourceJson.intChars geometryRow066_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow066_meanGap_denominator_parse :
    SourceJson.intChars geometryRow066_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow066_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow066_meanGap_parse :
    parseRational geometryRow066_meanGapText = .ok geometryRowsTyped066.meanGap :=
  original_rational_fraction_of_chars geometryRow066_meanGapNumeratorChars geometryRow066_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow066_meanGap_numerator_no_slash geometryRow066_meanGap_numerator_parse
    geometryRow066_meanGap_denominator_parse geometryRow066_meanGap_denominator_nonzero

theorem geometryRow066_meanGap_read :
    rationalField geometryRowsJson066 "mean_gap" = .ok geometryRowsTyped066.meanGap :=
  original_rationalField_of_string geometryRowsJson066 "mean_gap" geometryRow066_meanGapText
    geometryRowsTyped066.meanGap geometryRow066_meanGap_field geometryRow066_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_meanGap_complete"
  err.flush

noncomputable def geometryRow066_jensenBoundNumeratorChars : List Char := ['1', '4', '1', '0', '2', '9', '9', '5', '4', '0', '7', '8', '2', '1', '0', '2', '2', '8', '2', '1', '0', '9', '7', '6', '8', '0', '9', '2', '4', '3', '6', '8', '6', '0', '9', '3', '3', '4', '1', '6', '3', '9', '3', '0', '7', '4', '6', '3', '0', '5', '5', '7', '7', '0', '4', '5', '5', '6', '9', '9', '3', '0', '3', '8', '7', '6', '5', '5', '6', '7', '7', '8', '9', '7', '6', '1', '5', '8', '3', '5', '0', '9', '4', '7', '1', '3', '1', '4', '1', '5', '4', '0', '5', '1', '9', '7', '1', '4', '3', '5', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow066_jensenBoundDenominatorChars : List Char := ['4', '4', '6', '9', '6', '8', '8', '3', '3', '1', '0', '5', '8', '0', '5', '7', '6', '0', '9', '1', '2', '3', '5', '4', '8', '5', '4', '0', '9', '7', '2', '6', '7', '8', '4', '8', '8', '3', '1', '7', '0', '5', '9', '8', '2', '3', '8', '8', '3', '4', '2', '0', '9', '8', '5', '1', '2', '7', '9', '2', '2', '0', '2', '2', '8', '3', '9', '4', '1', '1', '2', '8', '2', '4', '2', '0', '4', '7', '0', '2', '7', '5', '8', '0', '8', '3', '0', '5', '5', '2', '5', '8', '8', '7', '7', '9', '3', '1', '7', '0', '3', '0', '6', '6', '1', '1', '4', '1', '1', '2', '4', '6', '0', '2', '0', '2', '2', '2', '7', '5', '6', '8', '1', '3']
noncomputable def geometryRow066_jensenBoundText : String := String.ofList (geometryRow066_jensenBoundNumeratorChars ++ '/' :: geometryRow066_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_jensenBound_before_field"
  err.flush

theorem geometryRow066_jensenBound_field :
    geometryRowsJson066.getObjVal? "jensen_bound" = .ok (.str geometryRow066_jensenBoundText) := by rfl

theorem geometryRow066_jensenBound_numerator_no_slash :
    geometryRow066_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow066_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow066_jensenBoundNumeratorChars = some (14102995407821022821097680924368609334163930746305577045569930387655677897615835094713141540519714355468750000000 : Int) := by decide +kernel

theorem geometryRow066_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow066_jensenBoundDenominatorChars = some (4469688331058057609123548540972678488317059823883420985127922022839411282420470275808305525887793170306611411246020222756813 : Int) := by decide +kernel

theorem geometryRow066_jensenBound_denominator_nonzero : (4469688331058057609123548540972678488317059823883420985127922022839411282420470275808305525887793170306611411246020222756813 : Int) ≠ 0 := by decide +kernel

theorem geometryRow066_jensenBound_parse :
    parseRational geometryRow066_jensenBoundText = .ok geometryRowsTyped066.jensenBound :=
  original_rational_fraction_of_chars geometryRow066_jensenBoundNumeratorChars geometryRow066_jensenBoundDenominatorChars
    (14102995407821022821097680924368609334163930746305577045569930387655677897615835094713141540519714355468750000000 : Int) (4469688331058057609123548540972678488317059823883420985127922022839411282420470275808305525887793170306611411246020222756813 : Int)
    geometryRow066_jensenBound_numerator_no_slash geometryRow066_jensenBound_numerator_parse
    geometryRow066_jensenBound_denominator_parse geometryRow066_jensenBound_denominator_nonzero

theorem geometryRow066_jensenBound_read :
    rationalField geometryRowsJson066 "jensen_bound" = .ok geometryRowsTyped066.jensenBound :=
  original_rationalField_of_string geometryRowsJson066 "jensen_bound" geometryRow066_jensenBoundText
    geometryRowsTyped066.jensenBound geometryRow066_jensenBound_field geometryRow066_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_factorMaxima_before"
  err.flush

theorem geometryRow066_factorMaxima_read :
    rationalArrayField geometryRowsJson066 "factor_maxima" = .ok geometryRowsTyped066.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_gapWeightedMeans_before"
  err.flush

theorem geometryRow066_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson066 "gap_weighted_means" = .ok geometryRowsTyped066.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow066_floorChars : List Char := ['2', '4', '9', '9', '8', '4', '8', '6', '0', '0', '9', '5', '2', '1', '5', '9', '1', '6']
noncomputable def geometryRow066_floorText : String := String.ofList geometryRow066_floorChars

theorem geometryRow066_floor_text_read :
    geometryRowsJson066.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow066_floorText := by rfl

theorem geometryRow066_floor_chars_parse :
    SourceJson.intChars geometryRow066_floorChars = some (249984860095215916 : Int) := by decide +kernel

theorem geometryRow066_floor_parse :
    parseInteger geometryRow066_floorText = .ok geometryRowsTyped066.jensenFloorQ96 := by
  simp only [geometryRow066_floorText, parseInteger, String.toList_ofList, geometryRow066_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_066 :
    decodeGeometryRow geometryRowsJson066 = .ok geometryRowsTyped066 :=
  original_geometryRow_of_fields geometryRowsJson066 geometryRowsTyped066 geometryRow066_floorText
    geometryRow066_simplexId_read geometryRow066_vertexIds_read
    geometryRow066_physicalVolume_read geometryRow066_meanGap_read
    geometryRow066_factorMaxima_read geometryRow066_gapWeightedMeans_read
    geometryRow066_jensenBound_read geometryRow066_floor_text_read geometryRow066_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_066_original_decoder_complete"
  err.flush

theorem geometryRow066_shape :
    geometryRowsTyped066.simplexId = 66 ∧
    geometryRowsTyped066.vertexIds.size = 9 ∧ geometryRowsTyped066.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped066.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped066.factorMaxima.size = 10 ∧ geometryRowsTyped066.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson067 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped067 : GeometryRow :=
  { simplexId := 67,
    vertexIds := #[32, 30, 28, 26, 14, 12, 11, 7, 3],
    physicalVolume := ((1347649232964656411352184771921544461051 : ℚ) / (10556943976857600000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((49290167 : ℚ) / (34056000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((5921703 : ℚ) / (172000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((8030608978323481838903 : ℚ) / (90536689391730120000000 : ℚ)), ((2051908081375236931103 : ℚ) / (22634172347932530000000 : ℚ)), ((1335665856010520492027 : ℚ) / (11317086173966265000000 : ℚ)), ((457822768786383323087 : ℚ) / (5029816077318340000000 : ℚ)), ((1365268481502250075813 : ℚ) / (15089448231955020000000 : ℚ)), ((16516119209010607253 : ℚ) / (226341723479325300000 : ℚ)), ((1368775060270853259643 : ℚ) / (36214675756692048000000 : ℚ)), ((6207366375818193033353 : ℚ) / (181073378783460240000000 : ℚ)), ((2835062108279765454253 : ℚ) / (90536689391730120000000 : ℚ)), ((699686194415744837977 : ℚ) / (22634172347932530000000 : ℚ))],
    jensenBound := ((3956468060586153287708187455578942757228053657755120329592705640982821978484074801914052805822554484494750573005520477719128859627718959921826180162152126142963099582911658804645618836225000000000000 : ℚ) / (3829420095952937157817760400247442251920749744593024132472610157413393628234757423340941682101665829102743052420326686082993680351014667230110729850652557851714790796142341130730860774649081256133115039635954651 : ℚ)),
    jensenFloorQ96 := (81856700657599620 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_simplexId_before"
  err.flush

theorem geometryRow067_simplexId_read :
    geometryRowsJson067.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped067.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_vertexIds_before"
  err.flush

theorem geometryRow067_vertexIds_read :
    geometryRowsJson067.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped067.vertexIds := by decide +kernel

noncomputable def geometryRow067_physicalVolumeNumeratorChars : List Char := ['1', '3', '4', '7', '6', '4', '9', '2', '3', '2', '9', '6', '4', '6', '5', '6', '4', '1', '1', '3', '5', '2', '1', '8', '4', '7', '7', '1', '9', '2', '1', '5', '4', '4', '4', '6', '1', '0', '5', '1']
noncomputable def geometryRow067_physicalVolumeDenominatorChars : List Char := ['1', '0', '5', '5', '6', '9', '4', '3', '9', '7', '6', '8', '5', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow067_physicalVolumeText : String := String.ofList (geometryRow067_physicalVolumeNumeratorChars ++ '/' :: geometryRow067_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_physicalVolume_before_field"
  err.flush

theorem geometryRow067_physicalVolume_field :
    geometryRowsJson067.getObjVal? "physical_volume" = .ok (.str geometryRow067_physicalVolumeText) := by rfl

theorem geometryRow067_physicalVolume_numerator_no_slash :
    geometryRow067_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow067_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow067_physicalVolumeNumeratorChars = some (1347649232964656411352184771921544461051 : Int) := by decide +kernel

theorem geometryRow067_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow067_physicalVolumeDenominatorChars = some (10556943976857600000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow067_physicalVolume_denominator_nonzero : (10556943976857600000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow067_physicalVolume_parse :
    parseRational geometryRow067_physicalVolumeText = .ok geometryRowsTyped067.physicalVolume :=
  original_rational_fraction_of_chars geometryRow067_physicalVolumeNumeratorChars geometryRow067_physicalVolumeDenominatorChars
    (1347649232964656411352184771921544461051 : Int) (10556943976857600000000000000000000000000000000000000000000000 : Int)
    geometryRow067_physicalVolume_numerator_no_slash geometryRow067_physicalVolume_numerator_parse
    geometryRow067_physicalVolume_denominator_parse geometryRow067_physicalVolume_denominator_nonzero

theorem geometryRow067_physicalVolume_read :
    rationalField geometryRowsJson067 "physical_volume" = .ok geometryRowsTyped067.physicalVolume :=
  original_rationalField_of_string geometryRowsJson067 "physical_volume" geometryRow067_physicalVolumeText
    geometryRowsTyped067.physicalVolume geometryRow067_physicalVolume_field geometryRow067_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_physicalVolume_complete"
  err.flush

noncomputable def geometryRow067_meanGapNumeratorChars : List Char := ['4', '9', '2', '9', '0', '1', '6', '7']
noncomputable def geometryRow067_meanGapDenominatorChars : List Char := ['3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow067_meanGapText : String := String.ofList (geometryRow067_meanGapNumeratorChars ++ '/' :: geometryRow067_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_meanGap_before_field"
  err.flush

theorem geometryRow067_meanGap_field :
    geometryRowsJson067.getObjVal? "mean_gap" = .ok (.str geometryRow067_meanGapText) := by rfl

theorem geometryRow067_meanGap_numerator_no_slash :
    geometryRow067_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow067_meanGap_numerator_parse :
    SourceJson.intChars geometryRow067_meanGapNumeratorChars = some (49290167 : Int) := by decide +kernel

theorem geometryRow067_meanGap_denominator_parse :
    SourceJson.intChars geometryRow067_meanGapDenominatorChars = some (34056000000 : Int) := by decide +kernel

theorem geometryRow067_meanGap_denominator_nonzero : (34056000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow067_meanGap_parse :
    parseRational geometryRow067_meanGapText = .ok geometryRowsTyped067.meanGap :=
  original_rational_fraction_of_chars geometryRow067_meanGapNumeratorChars geometryRow067_meanGapDenominatorChars
    (49290167 : Int) (34056000000 : Int)
    geometryRow067_meanGap_numerator_no_slash geometryRow067_meanGap_numerator_parse
    geometryRow067_meanGap_denominator_parse geometryRow067_meanGap_denominator_nonzero

theorem geometryRow067_meanGap_read :
    rationalField geometryRowsJson067 "mean_gap" = .ok geometryRowsTyped067.meanGap :=
  original_rationalField_of_string geometryRowsJson067 "mean_gap" geometryRow067_meanGapText
    geometryRowsTyped067.meanGap geometryRow067_meanGap_field geometryRow067_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_meanGap_complete"
  err.flush

noncomputable def geometryRow067_jensenBoundNumeratorChars : List Char := ['3', '9', '5', '6', '4', '6', '8', '0', '6', '0', '5', '8', '6', '1', '5', '3', '2', '8', '7', '7', '0', '8', '1', '8', '7', '4', '5', '5', '5', '7', '8', '9', '4', '2', '7', '5', '7', '2', '2', '8', '0', '5', '3', '6', '5', '7', '7', '5', '5', '1', '2', '0', '3', '2', '9', '5', '9', '2', '7', '0', '5', '6', '4', '0', '9', '8', '2', '8', '2', '1', '9', '7', '8', '4', '8', '4', '0', '7', '4', '8', '0', '1', '9', '1', '4', '0', '5', '2', '8', '0', '5', '8', '2', '2', '5', '5', '4', '4', '8', '4', '4', '9', '4', '7', '5', '0', '5', '7', '3', '0', '0', '5', '5', '2', '0', '4', '7', '7', '7', '1', '9', '1', '2', '8', '8', '5', '9', '6', '2', '7', '7', '1', '8', '9', '5', '9', '9', '2', '1', '8', '2', '6', '1', '8', '0', '1', '6', '2', '1', '5', '2', '1', '2', '6', '1', '4', '2', '9', '6', '3', '0', '9', '9', '5', '8', '2', '9', '1', '1', '6', '5', '8', '8', '0', '4', '6', '4', '5', '6', '1', '8', '8', '3', '6', '2', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow067_jensenBoundDenominatorChars : List Char := ['3', '8', '2', '9', '4', '2', '0', '0', '9', '5', '9', '5', '2', '9', '3', '7', '1', '5', '7', '8', '1', '7', '7', '6', '0', '4', '0', '0', '2', '4', '7', '4', '4', '2', '2', '5', '1', '9', '2', '0', '7', '4', '9', '7', '4', '4', '5', '9', '3', '0', '2', '4', '1', '3', '2', '4', '7', '2', '6', '1', '0', '1', '5', '7', '4', '1', '3', '3', '9', '3', '6', '2', '8', '2', '3', '4', '7', '5', '7', '4', '2', '3', '3', '4', '0', '9', '4', '1', '6', '8', '2', '1', '0', '1', '6', '6', '5', '8', '2', '9', '1', '0', '2', '7', '4', '3', '0', '5', '2', '4', '2', '0', '3', '2', '6', '6', '8', '6', '0', '8', '2', '9', '9', '3', '6', '8', '0', '3', '5', '1', '0', '1', '4', '6', '6', '7', '2', '3', '0', '1', '1', '0', '7', '2', '9', '8', '5', '0', '6', '5', '2', '5', '5', '7', '8', '5', '1', '7', '1', '4', '7', '9', '0', '7', '9', '6', '1', '4', '2', '3', '4', '1', '1', '3', '0', '7', '3', '0', '8', '6', '0', '7', '7', '4', '6', '4', '9', '0', '8', '1', '2', '5', '6', '1', '3', '3', '1', '1', '5', '0', '3', '9', '6', '3', '5', '9', '5', '4', '6', '5', '1']
noncomputable def geometryRow067_jensenBoundText : String := String.ofList (geometryRow067_jensenBoundNumeratorChars ++ '/' :: geometryRow067_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_jensenBound_before_field"
  err.flush

theorem geometryRow067_jensenBound_field :
    geometryRowsJson067.getObjVal? "jensen_bound" = .ok (.str geometryRow067_jensenBoundText) := by rfl

theorem geometryRow067_jensenBound_numerator_no_slash :
    geometryRow067_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow067_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow067_jensenBoundNumeratorChars = some (3956468060586153287708187455578942757228053657755120329592705640982821978484074801914052805822554484494750573005520477719128859627718959921826180162152126142963099582911658804645618836225000000000000 : Int) := by decide +kernel

theorem geometryRow067_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow067_jensenBoundDenominatorChars = some (3829420095952937157817760400247442251920749744593024132472610157413393628234757423340941682101665829102743052420326686082993680351014667230110729850652557851714790796142341130730860774649081256133115039635954651 : Int) := by decide +kernel

theorem geometryRow067_jensenBound_denominator_nonzero : (3829420095952937157817760400247442251920749744593024132472610157413393628234757423340941682101665829102743052420326686082993680351014667230110729850652557851714790796142341130730860774649081256133115039635954651 : Int) ≠ 0 := by decide +kernel

theorem geometryRow067_jensenBound_parse :
    parseRational geometryRow067_jensenBoundText = .ok geometryRowsTyped067.jensenBound :=
  original_rational_fraction_of_chars geometryRow067_jensenBoundNumeratorChars geometryRow067_jensenBoundDenominatorChars
    (3956468060586153287708187455578942757228053657755120329592705640982821978484074801914052805822554484494750573005520477719128859627718959921826180162152126142963099582911658804645618836225000000000000 : Int) (3829420095952937157817760400247442251920749744593024132472610157413393628234757423340941682101665829102743052420326686082993680351014667230110729850652557851714790796142341130730860774649081256133115039635954651 : Int)
    geometryRow067_jensenBound_numerator_no_slash geometryRow067_jensenBound_numerator_parse
    geometryRow067_jensenBound_denominator_parse geometryRow067_jensenBound_denominator_nonzero

theorem geometryRow067_jensenBound_read :
    rationalField geometryRowsJson067 "jensen_bound" = .ok geometryRowsTyped067.jensenBound :=
  original_rationalField_of_string geometryRowsJson067 "jensen_bound" geometryRow067_jensenBoundText
    geometryRowsTyped067.jensenBound geometryRow067_jensenBound_field geometryRow067_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_factorMaxima_before"
  err.flush

theorem geometryRow067_factorMaxima_read :
    rationalArrayField geometryRowsJson067 "factor_maxima" = .ok geometryRowsTyped067.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_gapWeightedMeans_before"
  err.flush

theorem geometryRow067_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson067 "gap_weighted_means" = .ok geometryRowsTyped067.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow067_floorChars : List Char := ['8', '1', '8', '5', '6', '7', '0', '0', '6', '5', '7', '5', '9', '9', '6', '2', '0']
noncomputable def geometryRow067_floorText : String := String.ofList geometryRow067_floorChars

theorem geometryRow067_floor_text_read :
    geometryRowsJson067.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow067_floorText := by rfl

theorem geometryRow067_floor_chars_parse :
    SourceJson.intChars geometryRow067_floorChars = some (81856700657599620 : Int) := by decide +kernel

theorem geometryRow067_floor_parse :
    parseInteger geometryRow067_floorText = .ok geometryRowsTyped067.jensenFloorQ96 := by
  simp only [geometryRow067_floorText, parseInteger, String.toList_ofList, geometryRow067_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_067 :
    decodeGeometryRow geometryRowsJson067 = .ok geometryRowsTyped067 :=
  original_geometryRow_of_fields geometryRowsJson067 geometryRowsTyped067 geometryRow067_floorText
    geometryRow067_simplexId_read geometryRow067_vertexIds_read
    geometryRow067_physicalVolume_read geometryRow067_meanGap_read
    geometryRow067_factorMaxima_read geometryRow067_gapWeightedMeans_read
    geometryRow067_jensenBound_read geometryRow067_floor_text_read geometryRow067_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_067_original_decoder_complete"
  err.flush

theorem geometryRow067_shape :
    geometryRowsTyped067.simplexId = 67 ∧
    geometryRowsTyped067.vertexIds.size = 9 ∧ geometryRowsTyped067.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped067.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped067.factorMaxima.size = 10 ∧ geometryRowsTyped067.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson068 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped068 : GeometryRow :=
  { simplexId := 68,
    vertexIds := #[32, 30, 28, 26, 14, 13, 4, 1, 0],
    physicalVolume := ((331430622978591096436688118325265483659 : ℚ) / (72955407038472000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((1608552439149509260627013 : ℚ) / (18475141602500035818750000 : ℚ)), ((88102264178092939841309 : ℚ) / (982067327707643100000000 : ℚ)), ((604065466498284698178311 : ℚ) / (5140908967652183880000000 : ℚ)), ((6056307741653493301867147 : ℚ) / (65689392364444571800000000 : ℚ)), ((18061833521467424780106481 : ℚ) / (197068177093333715400000000 : ℚ)), ((3844349135346052674224531 : ℚ) / (53745866480000104200000000 : ℚ)), ((1946187984479765929691683 : ℚ) / (53745866480000104200000000 : ℚ)), ((231272425074989736200411 : ℚ) / (6718233310000013025000000 : ℚ)), ((111982273850353485069763 : ℚ) / (3359116655000006512500000 : ℚ)), ((30049354395912238313623 : ℚ) / (982067327707643100000000 : ℚ))],
    jensenBound := ((281494804056480214101417487697996416903344982192995378316266509366723185066157496851813240418334189277425929089585525798660989880467216906443708496491603504562272562762918754350294739325726215459301280593750000000000000000000 : ℚ) / (4956775823837279121896860433800942422089884995383135329802640299668055943077449675905314638818625525181444516313792347507603852962128308578964375411236172712066174294423297041704080831060050369195732521064795737829603945934794828945224393 : ℚ)),
    jensenFloorQ96 := (4499359437531010 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_simplexId_before"
  err.flush

theorem geometryRow068_simplexId_read :
    geometryRowsJson068.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped068.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_vertexIds_before"
  err.flush

theorem geometryRow068_vertexIds_read :
    geometryRowsJson068.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped068.vertexIds := by decide +kernel

noncomputable def geometryRow068_physicalVolumeNumeratorChars : List Char := ['3', '3', '1', '4', '3', '0', '6', '2', '2', '9', '7', '8', '5', '9', '1', '0', '9', '6', '4', '3', '6', '6', '8', '8', '1', '1', '8', '3', '2', '5', '2', '6', '5', '4', '8', '3', '6', '5', '9']
noncomputable def geometryRow068_physicalVolumeDenominatorChars : List Char := ['7', '2', '9', '5', '5', '4', '0', '7', '0', '3', '8', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow068_physicalVolumeText : String := String.ofList (geometryRow068_physicalVolumeNumeratorChars ++ '/' :: geometryRow068_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_physicalVolume_before_field"
  err.flush

theorem geometryRow068_physicalVolume_field :
    geometryRowsJson068.getObjVal? "physical_volume" = .ok (.str geometryRow068_physicalVolumeText) := by rfl

theorem geometryRow068_physicalVolume_numerator_no_slash :
    geometryRow068_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow068_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow068_physicalVolumeNumeratorChars = some (331430622978591096436688118325265483659 : Int) := by decide +kernel

theorem geometryRow068_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow068_physicalVolumeDenominatorChars = some (72955407038472000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow068_physicalVolume_denominator_nonzero : (72955407038472000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow068_physicalVolume_parse :
    parseRational geometryRow068_physicalVolumeText = .ok geometryRowsTyped068.physicalVolume :=
  original_rational_fraction_of_chars geometryRow068_physicalVolumeNumeratorChars geometryRow068_physicalVolumeDenominatorChars
    (331430622978591096436688118325265483659 : Int) (72955407038472000000000000000000000000000000000000000000000000 : Int)
    geometryRow068_physicalVolume_numerator_no_slash geometryRow068_physicalVolume_numerator_parse
    geometryRow068_physicalVolume_denominator_parse geometryRow068_physicalVolume_denominator_nonzero

theorem geometryRow068_physicalVolume_read :
    rationalField geometryRowsJson068 "physical_volume" = .ok geometryRowsTyped068.physicalVolume :=
  original_rationalField_of_string geometryRowsJson068 "physical_volume" geometryRow068_physicalVolumeText
    geometryRowsTyped068.physicalVolume geometryRow068_physicalVolume_field geometryRow068_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_physicalVolume_complete"
  err.flush

noncomputable def geometryRow068_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow068_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow068_meanGapText : String := String.ofList (geometryRow068_meanGapNumeratorChars ++ '/' :: geometryRow068_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_meanGap_before_field"
  err.flush

theorem geometryRow068_meanGap_field :
    geometryRowsJson068.getObjVal? "mean_gap" = .ok (.str geometryRow068_meanGapText) := by rfl

theorem geometryRow068_meanGap_numerator_no_slash :
    geometryRow068_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow068_meanGap_numerator_parse :
    SourceJson.intChars geometryRow068_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow068_meanGap_denominator_parse :
    SourceJson.intChars geometryRow068_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow068_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow068_meanGap_parse :
    parseRational geometryRow068_meanGapText = .ok geometryRowsTyped068.meanGap :=
  original_rational_fraction_of_chars geometryRow068_meanGapNumeratorChars geometryRow068_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow068_meanGap_numerator_no_slash geometryRow068_meanGap_numerator_parse
    geometryRow068_meanGap_denominator_parse geometryRow068_meanGap_denominator_nonzero

theorem geometryRow068_meanGap_read :
    rationalField geometryRowsJson068 "mean_gap" = .ok geometryRowsTyped068.meanGap :=
  original_rationalField_of_string geometryRowsJson068 "mean_gap" geometryRow068_meanGapText
    geometryRowsTyped068.meanGap geometryRow068_meanGap_field geometryRow068_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_meanGap_complete"
  err.flush

noncomputable def geometryRow068_jensenBoundNumeratorChars : List Char := ['2', '8', '1', '4', '9', '4', '8', '0', '4', '0', '5', '6', '4', '8', '0', '2', '1', '4', '1', '0', '1', '4', '1', '7', '4', '8', '7', '6', '9', '7', '9', '9', '6', '4', '1', '6', '9', '0', '3', '3', '4', '4', '9', '8', '2', '1', '9', '2', '9', '9', '5', '3', '7', '8', '3', '1', '6', '2', '6', '6', '5', '0', '9', '3', '6', '6', '7', '2', '3', '1', '8', '5', '0', '6', '6', '1', '5', '7', '4', '9', '6', '8', '5', '1', '8', '1', '3', '2', '4', '0', '4', '1', '8', '3', '3', '4', '1', '8', '9', '2', '7', '7', '4', '2', '5', '9', '2', '9', '0', '8', '9', '5', '8', '5', '5', '2', '5', '7', '9', '8', '6', '6', '0', '9', '8', '9', '8', '8', '0', '4', '6', '7', '2', '1', '6', '9', '0', '6', '4', '4', '3', '7', '0', '8', '4', '9', '6', '4', '9', '1', '6', '0', '3', '5', '0', '4', '5', '6', '2', '2', '7', '2', '5', '6', '2', '7', '6', '2', '9', '1', '8', '7', '5', '4', '3', '5', '0', '2', '9', '4', '7', '3', '9', '3', '2', '5', '7', '2', '6', '2', '1', '5', '4', '5', '9', '3', '0', '1', '2', '8', '0', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow068_jensenBoundDenominatorChars : List Char := ['4', '9', '5', '6', '7', '7', '5', '8', '2', '3', '8', '3', '7', '2', '7', '9', '1', '2', '1', '8', '9', '6', '8', '6', '0', '4', '3', '3', '8', '0', '0', '9', '4', '2', '4', '2', '2', '0', '8', '9', '8', '8', '4', '9', '9', '5', '3', '8', '3', '1', '3', '5', '3', '2', '9', '8', '0', '2', '6', '4', '0', '2', '9', '9', '6', '6', '8', '0', '5', '5', '9', '4', '3', '0', '7', '7', '4', '4', '9', '6', '7', '5', '9', '0', '5', '3', '1', '4', '6', '3', '8', '8', '1', '8', '6', '2', '5', '5', '2', '5', '1', '8', '1', '4', '4', '4', '5', '1', '6', '3', '1', '3', '7', '9', '2', '3', '4', '7', '5', '0', '7', '6', '0', '3', '8', '5', '2', '9', '6', '2', '1', '2', '8', '3', '0', '8', '5', '7', '8', '9', '6', '4', '3', '7', '5', '4', '1', '1', '2', '3', '6', '1', '7', '2', '7', '1', '2', '0', '6', '6', '1', '7', '4', '2', '9', '4', '4', '2', '3', '2', '9', '7', '0', '4', '1', '7', '0', '4', '0', '8', '0', '8', '3', '1', '0', '6', '0', '0', '5', '0', '3', '6', '9', '1', '9', '5', '7', '3', '2', '5', '2', '1', '0', '6', '4', '7', '9', '5', '7', '3', '7', '8', '2', '9', '6', '0', '3', '9', '4', '5', '9', '3', '4', '7', '9', '4', '8', '2', '8', '9', '4', '5', '2', '2', '4', '3', '9', '3']
noncomputable def geometryRow068_jensenBoundText : String := String.ofList (geometryRow068_jensenBoundNumeratorChars ++ '/' :: geometryRow068_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_jensenBound_before_field"
  err.flush

theorem geometryRow068_jensenBound_field :
    geometryRowsJson068.getObjVal? "jensen_bound" = .ok (.str geometryRow068_jensenBoundText) := by rfl

theorem geometryRow068_jensenBound_numerator_no_slash :
    geometryRow068_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow068_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow068_jensenBoundNumeratorChars = some (281494804056480214101417487697996416903344982192995378316266509366723185066157496851813240418334189277425929089585525798660989880467216906443708496491603504562272562762918754350294739325726215459301280593750000000000000000000 : Int) := by decide +kernel

theorem geometryRow068_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow068_jensenBoundDenominatorChars = some (4956775823837279121896860433800942422089884995383135329802640299668055943077449675905314638818625525181444516313792347507603852962128308578964375411236172712066174294423297041704080831060050369195732521064795737829603945934794828945224393 : Int) := by decide +kernel

theorem geometryRow068_jensenBound_denominator_nonzero : (4956775823837279121896860433800942422089884995383135329802640299668055943077449675905314638818625525181444516313792347507603852962128308578964375411236172712066174294423297041704080831060050369195732521064795737829603945934794828945224393 : Int) ≠ 0 := by decide +kernel

theorem geometryRow068_jensenBound_parse :
    parseRational geometryRow068_jensenBoundText = .ok geometryRowsTyped068.jensenBound :=
  original_rational_fraction_of_chars geometryRow068_jensenBoundNumeratorChars geometryRow068_jensenBoundDenominatorChars
    (281494804056480214101417487697996416903344982192995378316266509366723185066157496851813240418334189277425929089585525798660989880467216906443708496491603504562272562762918754350294739325726215459301280593750000000000000000000 : Int) (4956775823837279121896860433800942422089884995383135329802640299668055943077449675905314638818625525181444516313792347507603852962128308578964375411236172712066174294423297041704080831060050369195732521064795737829603945934794828945224393 : Int)
    geometryRow068_jensenBound_numerator_no_slash geometryRow068_jensenBound_numerator_parse
    geometryRow068_jensenBound_denominator_parse geometryRow068_jensenBound_denominator_nonzero

theorem geometryRow068_jensenBound_read :
    rationalField geometryRowsJson068 "jensen_bound" = .ok geometryRowsTyped068.jensenBound :=
  original_rationalField_of_string geometryRowsJson068 "jensen_bound" geometryRow068_jensenBoundText
    geometryRowsTyped068.jensenBound geometryRow068_jensenBound_field geometryRow068_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_factorMaxima_before"
  err.flush

theorem geometryRow068_factorMaxima_read :
    rationalArrayField geometryRowsJson068 "factor_maxima" = .ok geometryRowsTyped068.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_gapWeightedMeans_before"
  err.flush

theorem geometryRow068_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson068 "gap_weighted_means" = .ok geometryRowsTyped068.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow068_floorChars : List Char := ['4', '4', '9', '9', '3', '5', '9', '4', '3', '7', '5', '3', '1', '0', '1', '0']
noncomputable def geometryRow068_floorText : String := String.ofList geometryRow068_floorChars

theorem geometryRow068_floor_text_read :
    geometryRowsJson068.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow068_floorText := by rfl

theorem geometryRow068_floor_chars_parse :
    SourceJson.intChars geometryRow068_floorChars = some (4499359437531010 : Int) := by decide +kernel

theorem geometryRow068_floor_parse :
    parseInteger geometryRow068_floorText = .ok geometryRowsTyped068.jensenFloorQ96 := by
  simp only [geometryRow068_floorText, parseInteger, String.toList_ofList, geometryRow068_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_068 :
    decodeGeometryRow geometryRowsJson068 = .ok geometryRowsTyped068 :=
  original_geometryRow_of_fields geometryRowsJson068 geometryRowsTyped068 geometryRow068_floorText
    geometryRow068_simplexId_read geometryRow068_vertexIds_read
    geometryRow068_physicalVolume_read geometryRow068_meanGap_read
    geometryRow068_factorMaxima_read geometryRow068_gapWeightedMeans_read
    geometryRow068_jensenBound_read geometryRow068_floor_text_read geometryRow068_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_068_original_decoder_complete"
  err.flush

theorem geometryRow068_shape :
    geometryRowsTyped068.simplexId = 68 ∧
    geometryRowsTyped068.vertexIds.size = 9 ∧ geometryRowsTyped068.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped068.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped068.factorMaxima.size = 10 ∧ geometryRowsTyped068.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson069 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped069 : GeometryRow :=
  { simplexId := 69,
    vertexIds := #[32, 30, 28, 26, 14, 13, 10, 1, 0],
    physicalVolume := ((23738096449817449218836888973370645939471 : ℚ) / (437732442230832000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((1174814741713413349289 : ℚ) / (13396576167019237500000 : ℚ)), ((1373188650744487274983 : ℚ) / (15310372762307700000000 : ℚ)), ((10989353902386203423 : ℚ) / (93193573335786000000 : ℚ)), ((3262350217351070932627 : ℚ) / (35724203112051300000000 : ℚ)), ((3242937167637908168507 : ℚ) / (35724203112051300000000 : ℚ)), ((176550912528864300263 : ℚ) / (2435741121276225000000 : ℚ)), ((91776002423569561579 : ℚ) / (2435741121276225000000 : ℚ)), ((82600396419891766729 : ℚ) / (2435741121276225000000 : ℚ)), ((19987718959463205541 : ℚ) / (608935280319056250000 : ℚ)), ((468360846273971672501 : ℚ) / (15310372762307700000000 : ℚ))],
    jensenBound := ((790308312597646745503947828202342484596383110603567490337053875661961528926234747478409623376133495617882222940104467361244091535824946964843318403963168119835170947408670043945312500000000 : ℚ) / (1762932848547601623183766327013466125115897115590633242870543933780722371714506289652132709708311474012893072413621598787884096298546253709278107026637784892848776878010900946884066497370018149398889449 : ℚ)),
    jensenFloorQ96 := (35517334354763255 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_simplexId_before"
  err.flush

theorem geometryRow069_simplexId_read :
    geometryRowsJson069.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped069.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_vertexIds_before"
  err.flush

theorem geometryRow069_vertexIds_read :
    geometryRowsJson069.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped069.vertexIds := by decide +kernel

noncomputable def geometryRow069_physicalVolumeNumeratorChars : List Char := ['2', '3', '7', '3', '8', '0', '9', '6', '4', '4', '9', '8', '1', '7', '4', '4', '9', '2', '1', '8', '8', '3', '6', '8', '8', '8', '9', '7', '3', '3', '7', '0', '6', '4', '5', '9', '3', '9', '4', '7', '1']
noncomputable def geometryRow069_physicalVolumeDenominatorChars : List Char := ['4', '3', '7', '7', '3', '2', '4', '4', '2', '2', '3', '0', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow069_physicalVolumeText : String := String.ofList (geometryRow069_physicalVolumeNumeratorChars ++ '/' :: geometryRow069_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_physicalVolume_before_field"
  err.flush

theorem geometryRow069_physicalVolume_field :
    geometryRowsJson069.getObjVal? "physical_volume" = .ok (.str geometryRow069_physicalVolumeText) := by rfl

theorem geometryRow069_physicalVolume_numerator_no_slash :
    geometryRow069_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow069_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow069_physicalVolumeNumeratorChars = some (23738096449817449218836888973370645939471 : Int) := by decide +kernel

theorem geometryRow069_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow069_physicalVolumeDenominatorChars = some (437732442230832000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow069_physicalVolume_denominator_nonzero : (437732442230832000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow069_physicalVolume_parse :
    parseRational geometryRow069_physicalVolumeText = .ok geometryRowsTyped069.physicalVolume :=
  original_rational_fraction_of_chars geometryRow069_physicalVolumeNumeratorChars geometryRow069_physicalVolumeDenominatorChars
    (23738096449817449218836888973370645939471 : Int) (437732442230832000000000000000000000000000000000000000000000000 : Int)
    geometryRow069_physicalVolume_numerator_no_slash geometryRow069_physicalVolume_numerator_parse
    geometryRow069_physicalVolume_denominator_parse geometryRow069_physicalVolume_denominator_nonzero

theorem geometryRow069_physicalVolume_read :
    rationalField geometryRowsJson069 "physical_volume" = .ok geometryRowsTyped069.physicalVolume :=
  original_rationalField_of_string geometryRowsJson069 "physical_volume" geometryRow069_physicalVolumeText
    geometryRowsTyped069.physicalVolume geometryRow069_physicalVolume_field geometryRow069_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_physicalVolume_complete"
  err.flush

noncomputable def geometryRow069_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow069_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow069_meanGapText : String := String.ofList (geometryRow069_meanGapNumeratorChars ++ '/' :: geometryRow069_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_meanGap_before_field"
  err.flush

theorem geometryRow069_meanGap_field :
    geometryRowsJson069.getObjVal? "mean_gap" = .ok (.str geometryRow069_meanGapText) := by rfl

theorem geometryRow069_meanGap_numerator_no_slash :
    geometryRow069_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow069_meanGap_numerator_parse :
    SourceJson.intChars geometryRow069_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow069_meanGap_denominator_parse :
    SourceJson.intChars geometryRow069_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow069_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow069_meanGap_parse :
    parseRational geometryRow069_meanGapText = .ok geometryRowsTyped069.meanGap :=
  original_rational_fraction_of_chars geometryRow069_meanGapNumeratorChars geometryRow069_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow069_meanGap_numerator_no_slash geometryRow069_meanGap_numerator_parse
    geometryRow069_meanGap_denominator_parse geometryRow069_meanGap_denominator_nonzero

theorem geometryRow069_meanGap_read :
    rationalField geometryRowsJson069 "mean_gap" = .ok geometryRowsTyped069.meanGap :=
  original_rationalField_of_string geometryRowsJson069 "mean_gap" geometryRow069_meanGapText
    geometryRowsTyped069.meanGap geometryRow069_meanGap_field geometryRow069_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_meanGap_complete"
  err.flush

noncomputable def geometryRow069_jensenBoundNumeratorChars : List Char := ['7', '9', '0', '3', '0', '8', '3', '1', '2', '5', '9', '7', '6', '4', '6', '7', '4', '5', '5', '0', '3', '9', '4', '7', '8', '2', '8', '2', '0', '2', '3', '4', '2', '4', '8', '4', '5', '9', '6', '3', '8', '3', '1', '1', '0', '6', '0', '3', '5', '6', '7', '4', '9', '0', '3', '3', '7', '0', '5', '3', '8', '7', '5', '6', '6', '1', '9', '6', '1', '5', '2', '8', '9', '2', '6', '2', '3', '4', '7', '4', '7', '4', '7', '8', '4', '0', '9', '6', '2', '3', '3', '7', '6', '1', '3', '3', '4', '9', '5', '6', '1', '7', '8', '8', '2', '2', '2', '2', '9', '4', '0', '1', '0', '4', '4', '6', '7', '3', '6', '1', '2', '4', '4', '0', '9', '1', '5', '3', '5', '8', '2', '4', '9', '4', '6', '9', '6', '4', '8', '4', '3', '3', '1', '8', '4', '0', '3', '9', '6', '3', '1', '6', '8', '1', '1', '9', '8', '3', '5', '1', '7', '0', '9', '4', '7', '4', '0', '8', '6', '7', '0', '0', '4', '3', '9', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow069_jensenBoundDenominatorChars : List Char := ['1', '7', '6', '2', '9', '3', '2', '8', '4', '8', '5', '4', '7', '6', '0', '1', '6', '2', '3', '1', '8', '3', '7', '6', '6', '3', '2', '7', '0', '1', '3', '4', '6', '6', '1', '2', '5', '1', '1', '5', '8', '9', '7', '1', '1', '5', '5', '9', '0', '6', '3', '3', '2', '4', '2', '8', '7', '0', '5', '4', '3', '9', '3', '3', '7', '8', '0', '7', '2', '2', '3', '7', '1', '7', '1', '4', '5', '0', '6', '2', '8', '9', '6', '5', '2', '1', '3', '2', '7', '0', '9', '7', '0', '8', '3', '1', '1', '4', '7', '4', '0', '1', '2', '8', '9', '3', '0', '7', '2', '4', '1', '3', '6', '2', '1', '5', '9', '8', '7', '8', '7', '8', '8', '4', '0', '9', '6', '2', '9', '8', '5', '4', '6', '2', '5', '3', '7', '0', '9', '2', '7', '8', '1', '0', '7', '0', '2', '6', '6', '3', '7', '7', '8', '4', '8', '9', '2', '8', '4', '8', '7', '7', '6', '8', '7', '8', '0', '1', '0', '9', '0', '0', '9', '4', '6', '8', '8', '4', '0', '6', '6', '4', '9', '7', '3', '7', '0', '0', '1', '8', '1', '4', '9', '3', '9', '8', '8', '8', '9', '4', '4', '9']
noncomputable def geometryRow069_jensenBoundText : String := String.ofList (geometryRow069_jensenBoundNumeratorChars ++ '/' :: geometryRow069_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_jensenBound_before_field"
  err.flush

theorem geometryRow069_jensenBound_field :
    geometryRowsJson069.getObjVal? "jensen_bound" = .ok (.str geometryRow069_jensenBoundText) := by rfl

theorem geometryRow069_jensenBound_numerator_no_slash :
    geometryRow069_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow069_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow069_jensenBoundNumeratorChars = some (790308312597646745503947828202342484596383110603567490337053875661961528926234747478409623376133495617882222940104467361244091535824946964843318403963168119835170947408670043945312500000000 : Int) := by decide +kernel

theorem geometryRow069_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow069_jensenBoundDenominatorChars = some (1762932848547601623183766327013466125115897115590633242870543933780722371714506289652132709708311474012893072413621598787884096298546253709278107026637784892848776878010900946884066497370018149398889449 : Int) := by decide +kernel

theorem geometryRow069_jensenBound_denominator_nonzero : (1762932848547601623183766327013466125115897115590633242870543933780722371714506289652132709708311474012893072413621598787884096298546253709278107026637784892848776878010900946884066497370018149398889449 : Int) ≠ 0 := by decide +kernel

theorem geometryRow069_jensenBound_parse :
    parseRational geometryRow069_jensenBoundText = .ok geometryRowsTyped069.jensenBound :=
  original_rational_fraction_of_chars geometryRow069_jensenBoundNumeratorChars geometryRow069_jensenBoundDenominatorChars
    (790308312597646745503947828202342484596383110603567490337053875661961528926234747478409623376133495617882222940104467361244091535824946964843318403963168119835170947408670043945312500000000 : Int) (1762932848547601623183766327013466125115897115590633242870543933780722371714506289652132709708311474012893072413621598787884096298546253709278107026637784892848776878010900946884066497370018149398889449 : Int)
    geometryRow069_jensenBound_numerator_no_slash geometryRow069_jensenBound_numerator_parse
    geometryRow069_jensenBound_denominator_parse geometryRow069_jensenBound_denominator_nonzero

theorem geometryRow069_jensenBound_read :
    rationalField geometryRowsJson069 "jensen_bound" = .ok geometryRowsTyped069.jensenBound :=
  original_rationalField_of_string geometryRowsJson069 "jensen_bound" geometryRow069_jensenBoundText
    geometryRowsTyped069.jensenBound geometryRow069_jensenBound_field geometryRow069_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_factorMaxima_before"
  err.flush

theorem geometryRow069_factorMaxima_read :
    rationalArrayField geometryRowsJson069 "factor_maxima" = .ok geometryRowsTyped069.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_gapWeightedMeans_before"
  err.flush

theorem geometryRow069_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson069 "gap_weighted_means" = .ok geometryRowsTyped069.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow069_floorChars : List Char := ['3', '5', '5', '1', '7', '3', '3', '4', '3', '5', '4', '7', '6', '3', '2', '5', '5']
noncomputable def geometryRow069_floorText : String := String.ofList geometryRow069_floorChars

theorem geometryRow069_floor_text_read :
    geometryRowsJson069.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow069_floorText := by rfl

theorem geometryRow069_floor_chars_parse :
    SourceJson.intChars geometryRow069_floorChars = some (35517334354763255 : Int) := by decide +kernel

theorem geometryRow069_floor_parse :
    parseInteger geometryRow069_floorText = .ok geometryRowsTyped069.jensenFloorQ96 := by
  simp only [geometryRow069_floorText, parseInteger, String.toList_ofList, geometryRow069_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_069 :
    decodeGeometryRow geometryRowsJson069 = .ok geometryRowsTyped069 :=
  original_geometryRow_of_fields geometryRowsJson069 geometryRowsTyped069 geometryRow069_floorText
    geometryRow069_simplexId_read geometryRow069_vertexIds_read
    geometryRow069_physicalVolume_read geometryRow069_meanGap_read
    geometryRow069_factorMaxima_read geometryRow069_gapWeightedMeans_read
    geometryRow069_jensenBound_read geometryRow069_floor_text_read geometryRow069_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_069_original_decoder_complete"
  err.flush

theorem geometryRow069_shape :
    geometryRowsTyped069.simplexId = 69 ∧
    geometryRowsTyped069.vertexIds.size = 9 ∧ geometryRowsTyped069.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped069.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped069.factorMaxima.size = 10 ∧ geometryRowsTyped069.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson070 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped070 : GeometryRow :=
  { simplexId := 70,
    vertexIds := #[32, 30, 28, 26, 14, 13, 10, 8, 0],
    physicalVolume := ((525296419179651067654140963174171848247331 : ℚ) / (964798035937344000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((9291156924989 : ℚ) / (106791300000000 : ℚ)), ((1179025871389 : ℚ) / (13348912500000 : ℚ)), ((658250542339 : ℚ) / (5571720000000 : ℚ)), ((58083354696077 : ℚ) / (640747800000000 : ℚ)), ((57735163055357 : ℚ) / (640747800000000 : ℚ)), ((4287768930169 : ℚ) / (58249800000000 : ℚ)), ((555066085493 : ℚ) / (14562450000000 : ℚ)), ((287928848651 : ℚ) / (8321400000000 : ℚ)), ((278877098291 : ℚ) / (8321400000000 : ℚ)), ((75427108289 : ℚ) / (2502921093750 : ℚ))],
    jensenBound := ((69648909593469822610713676870659656365505663421321426903289320581307238617818164859709791015625000000000000000 : ℚ) / (31687305764417755027167935061095080688529616077217341542625589985579076333237277321541823947725278365021576774542957899973 : ℚ)),
    jensenFloorQ96 := (174144030080625129 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_simplexId_before"
  err.flush

theorem geometryRow070_simplexId_read :
    geometryRowsJson070.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped070.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_vertexIds_before"
  err.flush

theorem geometryRow070_vertexIds_read :
    geometryRowsJson070.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped070.vertexIds := by decide +kernel

noncomputable def geometryRow070_physicalVolumeNumeratorChars : List Char := ['5', '2', '5', '2', '9', '6', '4', '1', '9', '1', '7', '9', '6', '5', '1', '0', '6', '7', '6', '5', '4', '1', '4', '0', '9', '6', '3', '1', '7', '4', '1', '7', '1', '8', '4', '8', '2', '4', '7', '3', '3', '1']
noncomputable def geometryRow070_physicalVolumeDenominatorChars : List Char := ['9', '6', '4', '7', '9', '8', '0', '3', '5', '9', '3', '7', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow070_physicalVolumeText : String := String.ofList (geometryRow070_physicalVolumeNumeratorChars ++ '/' :: geometryRow070_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_physicalVolume_before_field"
  err.flush

theorem geometryRow070_physicalVolume_field :
    geometryRowsJson070.getObjVal? "physical_volume" = .ok (.str geometryRow070_physicalVolumeText) := by rfl

theorem geometryRow070_physicalVolume_numerator_no_slash :
    geometryRow070_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow070_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow070_physicalVolumeNumeratorChars = some (525296419179651067654140963174171848247331 : Int) := by decide +kernel

theorem geometryRow070_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow070_physicalVolumeDenominatorChars = some (964798035937344000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow070_physicalVolume_denominator_nonzero : (964798035937344000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow070_physicalVolume_parse :
    parseRational geometryRow070_physicalVolumeText = .ok geometryRowsTyped070.physicalVolume :=
  original_rational_fraction_of_chars geometryRow070_physicalVolumeNumeratorChars geometryRow070_physicalVolumeDenominatorChars
    (525296419179651067654140963174171848247331 : Int) (964798035937344000000000000000000000000000000000000000000000000 : Int)
    geometryRow070_physicalVolume_numerator_no_slash geometryRow070_physicalVolume_numerator_parse
    geometryRow070_physicalVolume_denominator_parse geometryRow070_physicalVolume_denominator_nonzero

theorem geometryRow070_physicalVolume_read :
    rationalField geometryRowsJson070 "physical_volume" = .ok geometryRowsTyped070.physicalVolume :=
  original_rationalField_of_string geometryRowsJson070 "physical_volume" geometryRow070_physicalVolumeText
    geometryRowsTyped070.physicalVolume geometryRow070_physicalVolume_field geometryRow070_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_physicalVolume_complete"
  err.flush

noncomputable def geometryRow070_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow070_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow070_meanGapText : String := String.ofList (geometryRow070_meanGapNumeratorChars ++ '/' :: geometryRow070_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_meanGap_before_field"
  err.flush

theorem geometryRow070_meanGap_field :
    geometryRowsJson070.getObjVal? "mean_gap" = .ok (.str geometryRow070_meanGapText) := by rfl

theorem geometryRow070_meanGap_numerator_no_slash :
    geometryRow070_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow070_meanGap_numerator_parse :
    SourceJson.intChars geometryRow070_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow070_meanGap_denominator_parse :
    SourceJson.intChars geometryRow070_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow070_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow070_meanGap_parse :
    parseRational geometryRow070_meanGapText = .ok geometryRowsTyped070.meanGap :=
  original_rational_fraction_of_chars geometryRow070_meanGapNumeratorChars geometryRow070_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow070_meanGap_numerator_no_slash geometryRow070_meanGap_numerator_parse
    geometryRow070_meanGap_denominator_parse geometryRow070_meanGap_denominator_nonzero

theorem geometryRow070_meanGap_read :
    rationalField geometryRowsJson070 "mean_gap" = .ok geometryRowsTyped070.meanGap :=
  original_rationalField_of_string geometryRowsJson070 "mean_gap" geometryRow070_meanGapText
    geometryRowsTyped070.meanGap geometryRow070_meanGap_field geometryRow070_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_meanGap_complete"
  err.flush

noncomputable def geometryRow070_jensenBoundNumeratorChars : List Char := ['6', '9', '6', '4', '8', '9', '0', '9', '5', '9', '3', '4', '6', '9', '8', '2', '2', '6', '1', '0', '7', '1', '3', '6', '7', '6', '8', '7', '0', '6', '5', '9', '6', '5', '6', '3', '6', '5', '5', '0', '5', '6', '6', '3', '4', '2', '1', '3', '2', '1', '4', '2', '6', '9', '0', '3', '2', '8', '9', '3', '2', '0', '5', '8', '1', '3', '0', '7', '2', '3', '8', '6', '1', '7', '8', '1', '8', '1', '6', '4', '8', '5', '9', '7', '0', '9', '7', '9', '1', '0', '1', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow070_jensenBoundDenominatorChars : List Char := ['3', '1', '6', '8', '7', '3', '0', '5', '7', '6', '4', '4', '1', '7', '7', '5', '5', '0', '2', '7', '1', '6', '7', '9', '3', '5', '0', '6', '1', '0', '9', '5', '0', '8', '0', '6', '8', '8', '5', '2', '9', '6', '1', '6', '0', '7', '7', '2', '1', '7', '3', '4', '1', '5', '4', '2', '6', '2', '5', '5', '8', '9', '9', '8', '5', '5', '7', '9', '0', '7', '6', '3', '3', '3', '2', '3', '7', '2', '7', '7', '3', '2', '1', '5', '4', '1', '8', '2', '3', '9', '4', '7', '7', '2', '5', '2', '7', '8', '3', '6', '5', '0', '2', '1', '5', '7', '6', '7', '7', '4', '5', '4', '2', '9', '5', '7', '8', '9', '9', '9', '7', '3']
noncomputable def geometryRow070_jensenBoundText : String := String.ofList (geometryRow070_jensenBoundNumeratorChars ++ '/' :: geometryRow070_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_jensenBound_before_field"
  err.flush

theorem geometryRow070_jensenBound_field :
    geometryRowsJson070.getObjVal? "jensen_bound" = .ok (.str geometryRow070_jensenBoundText) := by rfl

theorem geometryRow070_jensenBound_numerator_no_slash :
    geometryRow070_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow070_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow070_jensenBoundNumeratorChars = some (69648909593469822610713676870659656365505663421321426903289320581307238617818164859709791015625000000000000000 : Int) := by decide +kernel

theorem geometryRow070_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow070_jensenBoundDenominatorChars = some (31687305764417755027167935061095080688529616077217341542625589985579076333237277321541823947725278365021576774542957899973 : Int) := by decide +kernel

theorem geometryRow070_jensenBound_denominator_nonzero : (31687305764417755027167935061095080688529616077217341542625589985579076333237277321541823947725278365021576774542957899973 : Int) ≠ 0 := by decide +kernel

theorem geometryRow070_jensenBound_parse :
    parseRational geometryRow070_jensenBoundText = .ok geometryRowsTyped070.jensenBound :=
  original_rational_fraction_of_chars geometryRow070_jensenBoundNumeratorChars geometryRow070_jensenBoundDenominatorChars
    (69648909593469822610713676870659656365505663421321426903289320581307238617818164859709791015625000000000000000 : Int) (31687305764417755027167935061095080688529616077217341542625589985579076333237277321541823947725278365021576774542957899973 : Int)
    geometryRow070_jensenBound_numerator_no_slash geometryRow070_jensenBound_numerator_parse
    geometryRow070_jensenBound_denominator_parse geometryRow070_jensenBound_denominator_nonzero

theorem geometryRow070_jensenBound_read :
    rationalField geometryRowsJson070 "jensen_bound" = .ok geometryRowsTyped070.jensenBound :=
  original_rationalField_of_string geometryRowsJson070 "jensen_bound" geometryRow070_jensenBoundText
    geometryRowsTyped070.jensenBound geometryRow070_jensenBound_field geometryRow070_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_factorMaxima_before"
  err.flush

theorem geometryRow070_factorMaxima_read :
    rationalArrayField geometryRowsJson070 "factor_maxima" = .ok geometryRowsTyped070.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_gapWeightedMeans_before"
  err.flush

theorem geometryRow070_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson070 "gap_weighted_means" = .ok geometryRowsTyped070.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow070_floorChars : List Char := ['1', '7', '4', '1', '4', '4', '0', '3', '0', '0', '8', '0', '6', '2', '5', '1', '2', '9']
noncomputable def geometryRow070_floorText : String := String.ofList geometryRow070_floorChars

theorem geometryRow070_floor_text_read :
    geometryRowsJson070.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow070_floorText := by rfl

theorem geometryRow070_floor_chars_parse :
    SourceJson.intChars geometryRow070_floorChars = some (174144030080625129 : Int) := by decide +kernel

theorem geometryRow070_floor_parse :
    parseInteger geometryRow070_floorText = .ok geometryRowsTyped070.jensenFloorQ96 := by
  simp only [geometryRow070_floorText, parseInteger, String.toList_ofList, geometryRow070_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_070 :
    decodeGeometryRow geometryRowsJson070 = .ok geometryRowsTyped070 :=
  original_geometryRow_of_fields geometryRowsJson070 geometryRowsTyped070 geometryRow070_floorText
    geometryRow070_simplexId_read geometryRow070_vertexIds_read
    geometryRow070_physicalVolume_read geometryRow070_meanGap_read
    geometryRow070_factorMaxima_read geometryRow070_gapWeightedMeans_read
    geometryRow070_jensenBound_read geometryRow070_floor_text_read geometryRow070_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_070_original_decoder_complete"
  err.flush

theorem geometryRow070_shape :
    geometryRowsTyped070.simplexId = 70 ∧
    geometryRowsTyped070.vertexIds.size = 9 ∧ geometryRowsTyped070.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped070.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped070.factorMaxima.size = 10 ∧ geometryRowsTyped070.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson071 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped071 : GeometryRow :=
  { simplexId := 71,
    vertexIds := #[32, 30, 28, 26, 23, 13, 4, 1, 0],
    physicalVolume := ((1302990259954996511004581880237865351 : ℚ) / (2341106345264400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((753809285968903425926773 : ℚ) / (8823948228059718600000000 : ℚ)), ((2581896521165477412679 : ℚ) / (29315442618138600000000 : ℚ)), ((9094623021042120653549 : ℚ) / (76729984591823640000000 : ℚ)), ((137900820984239207287439 : ℚ) / (1470658038009953100000000 : ℚ)), ((137101644092499989932999 : ℚ) / (1470658038009953100000000 : ℚ)), ((56882698225124576117783 : ℚ) / (802177111641792600000000 : ℚ)), ((14713202854314534631277 : ℚ) / (401088555820896300000000 : ℚ)), ((26740146990131792602549 : ℚ) / (802177111641792600000000 : ℚ)), ((26304071886488072959789 : ℚ) / (802177111641792600000000 : ℚ)), ((880988382773007646013 : ℚ) / (29315442618138600000000 : ℚ))],
    jensenBound := ((5487761214933046039840335662414585101818827728128164445126392151764177157763565850818853325512649831663566716936130063055171335607963262677085994167714731480387596572054999829441934080000000000000000000000 : ℚ) / (744874277391165297951547933581406925182008118298917742139587440462953814944931464954303441679857387391609756289514782659125516281846046023519428449005048056376423620296102263526543951004611902444479964381749311407752126393 : ℚ)),
    jensenFloorQ96 := (583702848350 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_simplexId_before"
  err.flush

theorem geometryRow071_simplexId_read :
    geometryRowsJson071.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped071.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_vertexIds_before"
  err.flush

theorem geometryRow071_vertexIds_read :
    geometryRowsJson071.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped071.vertexIds := by decide +kernel

noncomputable def geometryRow071_physicalVolumeNumeratorChars : List Char := ['1', '3', '0', '2', '9', '9', '0', '2', '5', '9', '9', '5', '4', '9', '9', '6', '5', '1', '1', '0', '0', '4', '5', '8', '1', '8', '8', '0', '2', '3', '7', '8', '6', '5', '3', '5', '1']
noncomputable def geometryRow071_physicalVolumeDenominatorChars : List Char := ['2', '3', '4', '1', '1', '0', '6', '3', '4', '5', '2', '6', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow071_physicalVolumeText : String := String.ofList (geometryRow071_physicalVolumeNumeratorChars ++ '/' :: geometryRow071_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_physicalVolume_before_field"
  err.flush

theorem geometryRow071_physicalVolume_field :
    geometryRowsJson071.getObjVal? "physical_volume" = .ok (.str geometryRow071_physicalVolumeText) := by rfl

theorem geometryRow071_physicalVolume_numerator_no_slash :
    geometryRow071_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow071_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow071_physicalVolumeNumeratorChars = some (1302990259954996511004581880237865351 : Int) := by decide +kernel

theorem geometryRow071_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow071_physicalVolumeDenominatorChars = some (2341106345264400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow071_physicalVolume_denominator_nonzero : (2341106345264400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow071_physicalVolume_parse :
    parseRational geometryRow071_physicalVolumeText = .ok geometryRowsTyped071.physicalVolume :=
  original_rational_fraction_of_chars geometryRow071_physicalVolumeNumeratorChars geometryRow071_physicalVolumeDenominatorChars
    (1302990259954996511004581880237865351 : Int) (2341106345264400000000000000000000000000000000000000000000000000 : Int)
    geometryRow071_physicalVolume_numerator_no_slash geometryRow071_physicalVolume_numerator_parse
    geometryRow071_physicalVolume_denominator_parse geometryRow071_physicalVolume_denominator_nonzero

theorem geometryRow071_physicalVolume_read :
    rationalField geometryRowsJson071 "physical_volume" = .ok geometryRowsTyped071.physicalVolume :=
  original_rationalField_of_string geometryRowsJson071 "physical_volume" geometryRow071_physicalVolumeText
    geometryRowsTyped071.physicalVolume geometryRow071_physicalVolume_field geometryRow071_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_physicalVolume_complete"
  err.flush

noncomputable def geometryRow071_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow071_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow071_meanGapText : String := String.ofList (geometryRow071_meanGapNumeratorChars ++ '/' :: geometryRow071_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_meanGap_before_field"
  err.flush

theorem geometryRow071_meanGap_field :
    geometryRowsJson071.getObjVal? "mean_gap" = .ok (.str geometryRow071_meanGapText) := by rfl

theorem geometryRow071_meanGap_numerator_no_slash :
    geometryRow071_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow071_meanGap_numerator_parse :
    SourceJson.intChars geometryRow071_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow071_meanGap_denominator_parse :
    SourceJson.intChars geometryRow071_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow071_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow071_meanGap_parse :
    parseRational geometryRow071_meanGapText = .ok geometryRowsTyped071.meanGap :=
  original_rational_fraction_of_chars geometryRow071_meanGapNumeratorChars geometryRow071_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow071_meanGap_numerator_no_slash geometryRow071_meanGap_numerator_parse
    geometryRow071_meanGap_denominator_parse geometryRow071_meanGap_denominator_nonzero

theorem geometryRow071_meanGap_read :
    rationalField geometryRowsJson071 "mean_gap" = .ok geometryRowsTyped071.meanGap :=
  original_rationalField_of_string geometryRowsJson071 "mean_gap" geometryRow071_meanGapText
    geometryRowsTyped071.meanGap geometryRow071_meanGap_field geometryRow071_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_meanGap_complete"
  err.flush

noncomputable def geometryRow071_jensenBoundNumeratorChars : List Char := ['5', '4', '8', '7', '7', '6', '1', '2', '1', '4', '9', '3', '3', '0', '4', '6', '0', '3', '9', '8', '4', '0', '3', '3', '5', '6', '6', '2', '4', '1', '4', '5', '8', '5', '1', '0', '1', '8', '1', '8', '8', '2', '7', '7', '2', '8', '1', '2', '8', '1', '6', '4', '4', '4', '5', '1', '2', '6', '3', '9', '2', '1', '5', '1', '7', '6', '4', '1', '7', '7', '1', '5', '7', '7', '6', '3', '5', '6', '5', '8', '5', '0', '8', '1', '8', '8', '5', '3', '3', '2', '5', '5', '1', '2', '6', '4', '9', '8', '3', '1', '6', '6', '3', '5', '6', '6', '7', '1', '6', '9', '3', '6', '1', '3', '0', '0', '6', '3', '0', '5', '5', '1', '7', '1', '3', '3', '5', '6', '0', '7', '9', '6', '3', '2', '6', '2', '6', '7', '7', '0', '8', '5', '9', '9', '4', '1', '6', '7', '7', '1', '4', '7', '3', '1', '4', '8', '0', '3', '8', '7', '5', '9', '6', '5', '7', '2', '0', '5', '4', '9', '9', '9', '8', '2', '9', '4', '4', '1', '9', '3', '4', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow071_jensenBoundDenominatorChars : List Char := ['7', '4', '4', '8', '7', '4', '2', '7', '7', '3', '9', '1', '1', '6', '5', '2', '9', '7', '9', '5', '1', '5', '4', '7', '9', '3', '3', '5', '8', '1', '4', '0', '6', '9', '2', '5', '1', '8', '2', '0', '0', '8', '1', '1', '8', '2', '9', '8', '9', '1', '7', '7', '4', '2', '1', '3', '9', '5', '8', '7', '4', '4', '0', '4', '6', '2', '9', '5', '3', '8', '1', '4', '9', '4', '4', '9', '3', '1', '4', '6', '4', '9', '5', '4', '3', '0', '3', '4', '4', '1', '6', '7', '9', '8', '5', '7', '3', '8', '7', '3', '9', '1', '6', '0', '9', '7', '5', '6', '2', '8', '9', '5', '1', '4', '7', '8', '2', '6', '5', '9', '1', '2', '5', '5', '1', '6', '2', '8', '1', '8', '4', '6', '0', '4', '6', '0', '2', '3', '5', '1', '9', '4', '2', '8', '4', '4', '9', '0', '0', '5', '0', '4', '8', '0', '5', '6', '3', '7', '6', '4', '2', '3', '6', '2', '0', '2', '9', '6', '1', '0', '2', '2', '6', '3', '5', '2', '6', '5', '4', '3', '9', '5', '1', '0', '0', '4', '6', '1', '1', '9', '0', '2', '4', '4', '4', '4', '7', '9', '9', '6', '4', '3', '8', '1', '7', '4', '9', '3', '1', '1', '4', '0', '7', '7', '5', '2', '1', '2', '6', '3', '9', '3']
noncomputable def geometryRow071_jensenBoundText : String := String.ofList (geometryRow071_jensenBoundNumeratorChars ++ '/' :: geometryRow071_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_jensenBound_before_field"
  err.flush

theorem geometryRow071_jensenBound_field :
    geometryRowsJson071.getObjVal? "jensen_bound" = .ok (.str geometryRow071_jensenBoundText) := by rfl

theorem geometryRow071_jensenBound_numerator_no_slash :
    geometryRow071_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow071_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow071_jensenBoundNumeratorChars = some (5487761214933046039840335662414585101818827728128164445126392151764177157763565850818853325512649831663566716936130063055171335607963262677085994167714731480387596572054999829441934080000000000000000000000 : Int) := by decide +kernel

theorem geometryRow071_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow071_jensenBoundDenominatorChars = some (744874277391165297951547933581406925182008118298917742139587440462953814944931464954303441679857387391609756289514782659125516281846046023519428449005048056376423620296102263526543951004611902444479964381749311407752126393 : Int) := by decide +kernel

theorem geometryRow071_jensenBound_denominator_nonzero : (744874277391165297951547933581406925182008118298917742139587440462953814944931464954303441679857387391609756289514782659125516281846046023519428449005048056376423620296102263526543951004611902444479964381749311407752126393 : Int) ≠ 0 := by decide +kernel

theorem geometryRow071_jensenBound_parse :
    parseRational geometryRow071_jensenBoundText = .ok geometryRowsTyped071.jensenBound :=
  original_rational_fraction_of_chars geometryRow071_jensenBoundNumeratorChars geometryRow071_jensenBoundDenominatorChars
    (5487761214933046039840335662414585101818827728128164445126392151764177157763565850818853325512649831663566716936130063055171335607963262677085994167714731480387596572054999829441934080000000000000000000000 : Int) (744874277391165297951547933581406925182008118298917742139587440462953814944931464954303441679857387391609756289514782659125516281846046023519428449005048056376423620296102263526543951004611902444479964381749311407752126393 : Int)
    geometryRow071_jensenBound_numerator_no_slash geometryRow071_jensenBound_numerator_parse
    geometryRow071_jensenBound_denominator_parse geometryRow071_jensenBound_denominator_nonzero

theorem geometryRow071_jensenBound_read :
    rationalField geometryRowsJson071 "jensen_bound" = .ok geometryRowsTyped071.jensenBound :=
  original_rationalField_of_string geometryRowsJson071 "jensen_bound" geometryRow071_jensenBoundText
    geometryRowsTyped071.jensenBound geometryRow071_jensenBound_field geometryRow071_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_factorMaxima_before"
  err.flush

theorem geometryRow071_factorMaxima_read :
    rationalArrayField geometryRowsJson071 "factor_maxima" = .ok geometryRowsTyped071.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_gapWeightedMeans_before"
  err.flush

theorem geometryRow071_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson071 "gap_weighted_means" = .ok geometryRowsTyped071.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow071_floorChars : List Char := ['5', '8', '3', '7', '0', '2', '8', '4', '8', '3', '5', '0']
noncomputable def geometryRow071_floorText : String := String.ofList geometryRow071_floorChars

theorem geometryRow071_floor_text_read :
    geometryRowsJson071.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow071_floorText := by rfl

theorem geometryRow071_floor_chars_parse :
    SourceJson.intChars geometryRow071_floorChars = some (583702848350 : Int) := by decide +kernel

theorem geometryRow071_floor_parse :
    parseInteger geometryRow071_floorText = .ok geometryRowsTyped071.jensenFloorQ96 := by
  simp only [geometryRow071_floorText, parseInteger, String.toList_ofList, geometryRow071_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_071 :
    decodeGeometryRow geometryRowsJson071 = .ok geometryRowsTyped071 :=
  original_geometryRow_of_fields geometryRowsJson071 geometryRowsTyped071 geometryRow071_floorText
    geometryRow071_simplexId_read geometryRow071_vertexIds_read
    geometryRow071_physicalVolume_read geometryRow071_meanGap_read
    geometryRow071_factorMaxima_read geometryRow071_gapWeightedMeans_read
    geometryRow071_jensenBound_read geometryRow071_floor_text_read geometryRow071_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_071_original_decoder_complete"
  err.flush

theorem geometryRow071_shape :
    geometryRowsTyped071.simplexId = 71 ∧
    geometryRowsTyped071.vertexIds.size = 9 ∧ geometryRowsTyped071.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped071.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped071.factorMaxima.size = 10 ∧ geometryRowsTyped071.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock008 : List SourceJson := [geometryRowsJson064, geometryRowsJson065, geometryRowsJson066, geometryRowsJson067, geometryRowsJson068, geometryRowsJson069, geometryRowsJson070, geometryRowsJson071]
noncomputable def geometryRowsTypedBlock008 : List GeometryRow := [geometryRowsTyped064, geometryRowsTyped065, geometryRowsTyped066, geometryRowsTyped067, geometryRowsTyped068, geometryRowsTyped069, geometryRowsTyped070, geometryRowsTyped071]

theorem geometry_Rows_block_008_push_eq (acc : List SourceJson) :
    SimplicesBlock008.blockPush acc = [geometryRowsJson071, geometryRowsJson070, geometryRowsJson069, geometryRowsJson068, geometryRowsJson067, geometryRowsJson066, geometryRowsJson065, geometryRowsJson064] ++ acc := by rfl

theorem geometry_Rows_block_008_reverse (acc : List SourceJson) :
    (SimplicesBlock008.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock008 := by
  rw [geometry_Rows_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_008 :
    geometryRowsJsonBlock008.mapM decodeGeometryRow = .ok geometryRowsTypedBlock008 := by
  simp only [geometryRowsJsonBlock008, geometryRowsTypedBlock008, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_064, decode_geometry_Rows_065, decode_geometry_Rows_066, decode_geometry_Rows_067, decode_geometry_Rows_068, decode_geometry_Rows_069, decode_geometry_Rows_070, decode_geometry_Rows_071]
  rfl

theorem geometry_Rows_block_008_length : geometryRowsTypedBlock008.length = 8 := by rfl

#print axioms geometryRow064_simplexId_read
#print axioms geometryRow064_vertexIds_read
#print axioms geometryRow064_physicalVolume_field
#print axioms geometryRow064_physicalVolume_numerator_no_slash
#print axioms geometryRow064_physicalVolume_numerator_parse
#print axioms geometryRow064_physicalVolume_denominator_parse
#print axioms geometryRow064_physicalVolume_denominator_nonzero
#print axioms geometryRow064_physicalVolume_parse
#print axioms geometryRow064_physicalVolume_read
#print axioms geometryRow064_meanGap_field
#print axioms geometryRow064_meanGap_numerator_no_slash
#print axioms geometryRow064_meanGap_numerator_parse
#print axioms geometryRow064_meanGap_denominator_parse
#print axioms geometryRow064_meanGap_denominator_nonzero
#print axioms geometryRow064_meanGap_parse
#print axioms geometryRow064_meanGap_read
#print axioms geometryRow064_jensenBound_field
#print axioms geometryRow064_jensenBound_numerator_no_slash
#print axioms geometryRow064_jensenBound_numerator_parse
#print axioms geometryRow064_jensenBound_denominator_parse
#print axioms geometryRow064_jensenBound_denominator_nonzero
#print axioms geometryRow064_jensenBound_parse
#print axioms geometryRow064_jensenBound_read
#print axioms geometryRow064_factorMaxima_read
#print axioms geometryRow064_gapWeightedMeans_read
#print axioms geometryRow064_floor_text_read
#print axioms geometryRow064_floor_chars_parse
#print axioms geometryRow064_floor_parse
#print axioms decode_geometry_Rows_064
#print axioms geometryRow064_shape
#print axioms geometryRow065_simplexId_read
#print axioms geometryRow065_vertexIds_read
#print axioms geometryRow065_physicalVolume_field
#print axioms geometryRow065_physicalVolume_numerator_no_slash
#print axioms geometryRow065_physicalVolume_numerator_parse
#print axioms geometryRow065_physicalVolume_denominator_parse
#print axioms geometryRow065_physicalVolume_denominator_nonzero
#print axioms geometryRow065_physicalVolume_parse
#print axioms geometryRow065_physicalVolume_read
#print axioms geometryRow065_meanGap_field
#print axioms geometryRow065_meanGap_numerator_no_slash
#print axioms geometryRow065_meanGap_numerator_parse
#print axioms geometryRow065_meanGap_denominator_parse
#print axioms geometryRow065_meanGap_denominator_nonzero
#print axioms geometryRow065_meanGap_parse
#print axioms geometryRow065_meanGap_read
#print axioms geometryRow065_jensenBound_field
#print axioms geometryRow065_jensenBound_numerator_no_slash
#print axioms geometryRow065_jensenBound_numerator_parse
#print axioms geometryRow065_jensenBound_denominator_parse
#print axioms geometryRow065_jensenBound_denominator_nonzero
#print axioms geometryRow065_jensenBound_parse
#print axioms geometryRow065_jensenBound_read
#print axioms geometryRow065_factorMaxima_read
#print axioms geometryRow065_gapWeightedMeans_read
#print axioms geometryRow065_floor_text_read
#print axioms geometryRow065_floor_chars_parse
#print axioms geometryRow065_floor_parse
#print axioms decode_geometry_Rows_065
#print axioms geometryRow065_shape
#print axioms geometryRow066_simplexId_read
#print axioms geometryRow066_vertexIds_read
#print axioms geometryRow066_physicalVolume_field
#print axioms geometryRow066_physicalVolume_numerator_no_slash
#print axioms geometryRow066_physicalVolume_numerator_parse
#print axioms geometryRow066_physicalVolume_denominator_parse
#print axioms geometryRow066_physicalVolume_denominator_nonzero
#print axioms geometryRow066_physicalVolume_parse
#print axioms geometryRow066_physicalVolume_read
#print axioms geometryRow066_meanGap_field
#print axioms geometryRow066_meanGap_numerator_no_slash
#print axioms geometryRow066_meanGap_numerator_parse
#print axioms geometryRow066_meanGap_denominator_parse
#print axioms geometryRow066_meanGap_denominator_nonzero
#print axioms geometryRow066_meanGap_parse
#print axioms geometryRow066_meanGap_read
#print axioms geometryRow066_jensenBound_field
#print axioms geometryRow066_jensenBound_numerator_no_slash
#print axioms geometryRow066_jensenBound_numerator_parse
#print axioms geometryRow066_jensenBound_denominator_parse
#print axioms geometryRow066_jensenBound_denominator_nonzero
#print axioms geometryRow066_jensenBound_parse
#print axioms geometryRow066_jensenBound_read
#print axioms geometryRow066_factorMaxima_read
#print axioms geometryRow066_gapWeightedMeans_read
#print axioms geometryRow066_floor_text_read
#print axioms geometryRow066_floor_chars_parse
#print axioms geometryRow066_floor_parse
#print axioms decode_geometry_Rows_066
#print axioms geometryRow066_shape
#print axioms geometryRow067_simplexId_read
#print axioms geometryRow067_vertexIds_read
#print axioms geometryRow067_physicalVolume_field
#print axioms geometryRow067_physicalVolume_numerator_no_slash
#print axioms geometryRow067_physicalVolume_numerator_parse
#print axioms geometryRow067_physicalVolume_denominator_parse
#print axioms geometryRow067_physicalVolume_denominator_nonzero
#print axioms geometryRow067_physicalVolume_parse
#print axioms geometryRow067_physicalVolume_read
#print axioms geometryRow067_meanGap_field
#print axioms geometryRow067_meanGap_numerator_no_slash
#print axioms geometryRow067_meanGap_numerator_parse
#print axioms geometryRow067_meanGap_denominator_parse
#print axioms geometryRow067_meanGap_denominator_nonzero
#print axioms geometryRow067_meanGap_parse
#print axioms geometryRow067_meanGap_read
#print axioms geometryRow067_jensenBound_field
#print axioms geometryRow067_jensenBound_numerator_no_slash
#print axioms geometryRow067_jensenBound_numerator_parse
#print axioms geometryRow067_jensenBound_denominator_parse
#print axioms geometryRow067_jensenBound_denominator_nonzero
#print axioms geometryRow067_jensenBound_parse
#print axioms geometryRow067_jensenBound_read
#print axioms geometryRow067_factorMaxima_read
#print axioms geometryRow067_gapWeightedMeans_read
#print axioms geometryRow067_floor_text_read
#print axioms geometryRow067_floor_chars_parse
#print axioms geometryRow067_floor_parse
#print axioms decode_geometry_Rows_067
#print axioms geometryRow067_shape
#print axioms geometryRow068_simplexId_read
#print axioms geometryRow068_vertexIds_read
#print axioms geometryRow068_physicalVolume_field
#print axioms geometryRow068_physicalVolume_numerator_no_slash
#print axioms geometryRow068_physicalVolume_numerator_parse
#print axioms geometryRow068_physicalVolume_denominator_parse
#print axioms geometryRow068_physicalVolume_denominator_nonzero
#print axioms geometryRow068_physicalVolume_parse
#print axioms geometryRow068_physicalVolume_read
#print axioms geometryRow068_meanGap_field
#print axioms geometryRow068_meanGap_numerator_no_slash
#print axioms geometryRow068_meanGap_numerator_parse
#print axioms geometryRow068_meanGap_denominator_parse
#print axioms geometryRow068_meanGap_denominator_nonzero
#print axioms geometryRow068_meanGap_parse
#print axioms geometryRow068_meanGap_read
#print axioms geometryRow068_jensenBound_field
#print axioms geometryRow068_jensenBound_numerator_no_slash
#print axioms geometryRow068_jensenBound_numerator_parse
#print axioms geometryRow068_jensenBound_denominator_parse
#print axioms geometryRow068_jensenBound_denominator_nonzero
#print axioms geometryRow068_jensenBound_parse
#print axioms geometryRow068_jensenBound_read
#print axioms geometryRow068_factorMaxima_read
#print axioms geometryRow068_gapWeightedMeans_read
#print axioms geometryRow068_floor_text_read
#print axioms geometryRow068_floor_chars_parse
#print axioms geometryRow068_floor_parse
#print axioms decode_geometry_Rows_068
#print axioms geometryRow068_shape
#print axioms geometryRow069_simplexId_read
#print axioms geometryRow069_vertexIds_read
#print axioms geometryRow069_physicalVolume_field
#print axioms geometryRow069_physicalVolume_numerator_no_slash
#print axioms geometryRow069_physicalVolume_numerator_parse
#print axioms geometryRow069_physicalVolume_denominator_parse
#print axioms geometryRow069_physicalVolume_denominator_nonzero
#print axioms geometryRow069_physicalVolume_parse
#print axioms geometryRow069_physicalVolume_read
#print axioms geometryRow069_meanGap_field
#print axioms geometryRow069_meanGap_numerator_no_slash
#print axioms geometryRow069_meanGap_numerator_parse
#print axioms geometryRow069_meanGap_denominator_parse
#print axioms geometryRow069_meanGap_denominator_nonzero
#print axioms geometryRow069_meanGap_parse
#print axioms geometryRow069_meanGap_read
#print axioms geometryRow069_jensenBound_field
#print axioms geometryRow069_jensenBound_numerator_no_slash
#print axioms geometryRow069_jensenBound_numerator_parse
#print axioms geometryRow069_jensenBound_denominator_parse
#print axioms geometryRow069_jensenBound_denominator_nonzero
#print axioms geometryRow069_jensenBound_parse
#print axioms geometryRow069_jensenBound_read
#print axioms geometryRow069_factorMaxima_read
#print axioms geometryRow069_gapWeightedMeans_read
#print axioms geometryRow069_floor_text_read
#print axioms geometryRow069_floor_chars_parse
#print axioms geometryRow069_floor_parse
#print axioms decode_geometry_Rows_069
#print axioms geometryRow069_shape
#print axioms geometryRow070_simplexId_read
#print axioms geometryRow070_vertexIds_read
#print axioms geometryRow070_physicalVolume_field
#print axioms geometryRow070_physicalVolume_numerator_no_slash
#print axioms geometryRow070_physicalVolume_numerator_parse
#print axioms geometryRow070_physicalVolume_denominator_parse
#print axioms geometryRow070_physicalVolume_denominator_nonzero
#print axioms geometryRow070_physicalVolume_parse
#print axioms geometryRow070_physicalVolume_read
#print axioms geometryRow070_meanGap_field
#print axioms geometryRow070_meanGap_numerator_no_slash
#print axioms geometryRow070_meanGap_numerator_parse
#print axioms geometryRow070_meanGap_denominator_parse
#print axioms geometryRow070_meanGap_denominator_nonzero
#print axioms geometryRow070_meanGap_parse
#print axioms geometryRow070_meanGap_read
#print axioms geometryRow070_jensenBound_field
#print axioms geometryRow070_jensenBound_numerator_no_slash
#print axioms geometryRow070_jensenBound_numerator_parse
#print axioms geometryRow070_jensenBound_denominator_parse
#print axioms geometryRow070_jensenBound_denominator_nonzero
#print axioms geometryRow070_jensenBound_parse
#print axioms geometryRow070_jensenBound_read
#print axioms geometryRow070_factorMaxima_read
#print axioms geometryRow070_gapWeightedMeans_read
#print axioms geometryRow070_floor_text_read
#print axioms geometryRow070_floor_chars_parse
#print axioms geometryRow070_floor_parse
#print axioms decode_geometry_Rows_070
#print axioms geometryRow070_shape
#print axioms geometryRow071_simplexId_read
#print axioms geometryRow071_vertexIds_read
#print axioms geometryRow071_physicalVolume_field
#print axioms geometryRow071_physicalVolume_numerator_no_slash
#print axioms geometryRow071_physicalVolume_numerator_parse
#print axioms geometryRow071_physicalVolume_denominator_parse
#print axioms geometryRow071_physicalVolume_denominator_nonzero
#print axioms geometryRow071_physicalVolume_parse
#print axioms geometryRow071_physicalVolume_read
#print axioms geometryRow071_meanGap_field
#print axioms geometryRow071_meanGap_numerator_no_slash
#print axioms geometryRow071_meanGap_numerator_parse
#print axioms geometryRow071_meanGap_denominator_parse
#print axioms geometryRow071_meanGap_denominator_nonzero
#print axioms geometryRow071_meanGap_parse
#print axioms geometryRow071_meanGap_read
#print axioms geometryRow071_jensenBound_field
#print axioms geometryRow071_jensenBound_numerator_no_slash
#print axioms geometryRow071_jensenBound_numerator_parse
#print axioms geometryRow071_jensenBound_denominator_parse
#print axioms geometryRow071_jensenBound_denominator_nonzero
#print axioms geometryRow071_jensenBound_parse
#print axioms geometryRow071_jensenBound_read
#print axioms geometryRow071_factorMaxima_read
#print axioms geometryRow071_gapWeightedMeans_read
#print axioms geometryRow071_floor_text_read
#print axioms geometryRow071_floor_chars_parse
#print axioms geometryRow071_floor_parse
#print axioms decode_geometry_Rows_071
#print axioms geometryRow071_shape
#print axioms geometry_Rows_block_008_push_eq
#print axioms geometry_Rows_block_008_reverse
#print axioms decode_geometry_Rows_block_008
#print axioms geometry_Rows_block_008_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
