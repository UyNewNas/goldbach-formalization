import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock013

/-! Local typed certificates for original cell 06, rows 104 through 111.
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

noncomputable def geometryRowsJson104 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped104 : GeometryRow :=
  { simplexId := 104,
    vertexIds := #[32, 30, 29, 27, 23, 22, 13, 8, 0],
    physicalVolume := ((17543479521734345640668080558108745797003 : ℚ) / (36428497270200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((81415093963 : ℚ) / (967725000000 : ℚ)), ((330773064091 : ℚ) / (3870900000000 : ℚ)), ((304133173 : ℚ) / (2524500000 : ℚ)), ((1090875199703 : ℚ) / (11612700000000 : ℚ)), ((1076026668863 : ℚ) / (11612700000000 : ℚ)), ((526609453507 : ℚ) / (7389900000000 : ℚ)), ((531557624977 : ℚ) / (14779800000000 : ℚ)), ((508466158117 : ℚ) / (14779800000000 : ℚ)), ((500433615277 : ℚ) / (14779800000000 : ℚ)), ((338836750931 : ℚ) / (11612700000000 : ℚ))],
    jensenBound := ((71348430555064649551014262497724270431941500858512219298654063086316336448597727000000000000000000000 : ℚ) / (33146445345005282645747405376092374248790596143157223805431204933808266911645333233169378922971852306096870744683 : ℚ)),
    jensenFloorQ96 := (170540309596309879 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_simplexId_before"
  err.flush

theorem geometryRow104_simplexId_read :
    geometryRowsJson104.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped104.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_vertexIds_before"
  err.flush

theorem geometryRow104_vertexIds_read :
    geometryRowsJson104.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped104.vertexIds := by decide +kernel

noncomputable def geometryRow104_physicalVolumeNumeratorChars : List Char := ['1', '7', '5', '4', '3', '4', '7', '9', '5', '2', '1', '7', '3', '4', '3', '4', '5', '6', '4', '0', '6', '6', '8', '0', '8', '0', '5', '5', '8', '1', '0', '8', '7', '4', '5', '7', '9', '7', '0', '0', '3']
noncomputable def geometryRow104_physicalVolumeDenominatorChars : List Char := ['3', '6', '4', '2', '8', '4', '9', '7', '2', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow104_physicalVolumeText : String := String.ofList (geometryRow104_physicalVolumeNumeratorChars ++ '/' :: geometryRow104_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_physicalVolume_before_field"
  err.flush

theorem geometryRow104_physicalVolume_field :
    geometryRowsJson104.getObjVal? "physical_volume" = .ok (.str geometryRow104_physicalVolumeText) := by rfl

theorem geometryRow104_physicalVolume_numerator_no_slash :
    geometryRow104_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow104_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow104_physicalVolumeNumeratorChars = some (17543479521734345640668080558108745797003 : Int) := by decide +kernel

theorem geometryRow104_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow104_physicalVolumeDenominatorChars = some (36428497270200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow104_physicalVolume_denominator_nonzero : (36428497270200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow104_physicalVolume_parse :
    parseRational geometryRow104_physicalVolumeText = .ok geometryRowsTyped104.physicalVolume :=
  original_rational_fraction_of_chars geometryRow104_physicalVolumeNumeratorChars geometryRow104_physicalVolumeDenominatorChars
    (17543479521734345640668080558108745797003 : Int) (36428497270200000000000000000000000000000000000000000000000000 : Int)
    geometryRow104_physicalVolume_numerator_no_slash geometryRow104_physicalVolume_numerator_parse
    geometryRow104_physicalVolume_denominator_parse geometryRow104_physicalVolume_denominator_nonzero

theorem geometryRow104_physicalVolume_read :
    rationalField geometryRowsJson104 "physical_volume" = .ok geometryRowsTyped104.physicalVolume :=
  original_rationalField_of_string geometryRowsJson104 "physical_volume" geometryRow104_physicalVolumeText
    geometryRowsTyped104.physicalVolume geometryRow104_physicalVolume_field geometryRow104_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_physicalVolume_complete"
  err.flush

noncomputable def geometryRow104_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow104_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow104_meanGapText : String := String.ofList (geometryRow104_meanGapNumeratorChars ++ '/' :: geometryRow104_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_meanGap_before_field"
  err.flush

theorem geometryRow104_meanGap_field :
    geometryRowsJson104.getObjVal? "mean_gap" = .ok (.str geometryRow104_meanGapText) := by rfl

theorem geometryRow104_meanGap_numerator_no_slash :
    geometryRow104_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow104_meanGap_numerator_parse :
    SourceJson.intChars geometryRow104_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow104_meanGap_denominator_parse :
    SourceJson.intChars geometryRow104_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow104_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow104_meanGap_parse :
    parseRational geometryRow104_meanGapText = .ok geometryRowsTyped104.meanGap :=
  original_rational_fraction_of_chars geometryRow104_meanGapNumeratorChars geometryRow104_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow104_meanGap_numerator_no_slash geometryRow104_meanGap_numerator_parse
    geometryRow104_meanGap_denominator_parse geometryRow104_meanGap_denominator_nonzero

theorem geometryRow104_meanGap_read :
    rationalField geometryRowsJson104 "mean_gap" = .ok geometryRowsTyped104.meanGap :=
  original_rationalField_of_string geometryRowsJson104 "mean_gap" geometryRow104_meanGapText
    geometryRowsTyped104.meanGap geometryRow104_meanGap_field geometryRow104_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_meanGap_complete"
  err.flush

noncomputable def geometryRow104_jensenBoundNumeratorChars : List Char := ['7', '1', '3', '4', '8', '4', '3', '0', '5', '5', '5', '0', '6', '4', '6', '4', '9', '5', '5', '1', '0', '1', '4', '2', '6', '2', '4', '9', '7', '7', '2', '4', '2', '7', '0', '4', '3', '1', '9', '4', '1', '5', '0', '0', '8', '5', '8', '5', '1', '2', '2', '1', '9', '2', '9', '8', '6', '5', '4', '0', '6', '3', '0', '8', '6', '3', '1', '6', '3', '3', '6', '4', '4', '8', '5', '9', '7', '7', '2', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow104_jensenBoundDenominatorChars : List Char := ['3', '3', '1', '4', '6', '4', '4', '5', '3', '4', '5', '0', '0', '5', '2', '8', '2', '6', '4', '5', '7', '4', '7', '4', '0', '5', '3', '7', '6', '0', '9', '2', '3', '7', '4', '2', '4', '8', '7', '9', '0', '5', '9', '6', '1', '4', '3', '1', '5', '7', '2', '2', '3', '8', '0', '5', '4', '3', '1', '2', '0', '4', '9', '3', '3', '8', '0', '8', '2', '6', '6', '9', '1', '1', '6', '4', '5', '3', '3', '3', '2', '3', '3', '1', '6', '9', '3', '7', '8', '9', '2', '2', '9', '7', '1', '8', '5', '2', '3', '0', '6', '0', '9', '6', '8', '7', '0', '7', '4', '4', '6', '8', '3']
noncomputable def geometryRow104_jensenBoundText : String := String.ofList (geometryRow104_jensenBoundNumeratorChars ++ '/' :: geometryRow104_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_jensenBound_before_field"
  err.flush

theorem geometryRow104_jensenBound_field :
    geometryRowsJson104.getObjVal? "jensen_bound" = .ok (.str geometryRow104_jensenBoundText) := by rfl

theorem geometryRow104_jensenBound_numerator_no_slash :
    geometryRow104_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow104_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow104_jensenBoundNumeratorChars = some (71348430555064649551014262497724270431941500858512219298654063086316336448597727000000000000000000000 : Int) := by decide +kernel

theorem geometryRow104_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow104_jensenBoundDenominatorChars = some (33146445345005282645747405376092374248790596143157223805431204933808266911645333233169378922971852306096870744683 : Int) := by decide +kernel

theorem geometryRow104_jensenBound_denominator_nonzero : (33146445345005282645747405376092374248790596143157223805431204933808266911645333233169378922971852306096870744683 : Int) ≠ 0 := by decide +kernel

theorem geometryRow104_jensenBound_parse :
    parseRational geometryRow104_jensenBoundText = .ok geometryRowsTyped104.jensenBound :=
  original_rational_fraction_of_chars geometryRow104_jensenBoundNumeratorChars geometryRow104_jensenBoundDenominatorChars
    (71348430555064649551014262497724270431941500858512219298654063086316336448597727000000000000000000000 : Int) (33146445345005282645747405376092374248790596143157223805431204933808266911645333233169378922971852306096870744683 : Int)
    geometryRow104_jensenBound_numerator_no_slash geometryRow104_jensenBound_numerator_parse
    geometryRow104_jensenBound_denominator_parse geometryRow104_jensenBound_denominator_nonzero

theorem geometryRow104_jensenBound_read :
    rationalField geometryRowsJson104 "jensen_bound" = .ok geometryRowsTyped104.jensenBound :=
  original_rationalField_of_string geometryRowsJson104 "jensen_bound" geometryRow104_jensenBoundText
    geometryRowsTyped104.jensenBound geometryRow104_jensenBound_field geometryRow104_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_factorMaxima_before"
  err.flush

theorem geometryRow104_factorMaxima_read :
    rationalArrayField geometryRowsJson104 "factor_maxima" = .ok geometryRowsTyped104.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_gapWeightedMeans_before"
  err.flush

theorem geometryRow104_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson104 "gap_weighted_means" = .ok geometryRowsTyped104.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow104_floorChars : List Char := ['1', '7', '0', '5', '4', '0', '3', '0', '9', '5', '9', '6', '3', '0', '9', '8', '7', '9']
noncomputable def geometryRow104_floorText : String := String.ofList geometryRow104_floorChars

theorem geometryRow104_floor_text_read :
    geometryRowsJson104.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow104_floorText := by rfl

theorem geometryRow104_floor_chars_parse :
    SourceJson.intChars geometryRow104_floorChars = some (170540309596309879 : Int) := by decide +kernel

theorem geometryRow104_floor_parse :
    parseInteger geometryRow104_floorText = .ok geometryRowsTyped104.jensenFloorQ96 := by
  simp only [geometryRow104_floorText, parseInteger, String.toList_ofList, geometryRow104_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_104 :
    decodeGeometryRow geometryRowsJson104 = .ok geometryRowsTyped104 :=
  original_geometryRow_of_fields geometryRowsJson104 geometryRowsTyped104 geometryRow104_floorText
    geometryRow104_simplexId_read geometryRow104_vertexIds_read
    geometryRow104_physicalVolume_read geometryRow104_meanGap_read
    geometryRow104_factorMaxima_read geometryRow104_gapWeightedMeans_read
    geometryRow104_jensenBound_read geometryRow104_floor_text_read geometryRow104_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_104_original_decoder_complete"
  err.flush

theorem geometryRow104_shape :
    geometryRowsTyped104.simplexId = 104 ∧
    geometryRowsTyped104.vertexIds.size = 9 ∧ geometryRowsTyped104.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped104.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped104.factorMaxima.size = 10 ∧ geometryRowsTyped104.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson105 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped105 : GeometryRow :=
  { simplexId := 105,
    vertexIds := #[32, 30, 29, 27, 23, 22, 21, 8, 0],
    physicalVolume := ((739944937896052894728730478952728701091 : ℚ) / (1696979686500000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((10171707 : ℚ) / (110000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((4444947146051 : ℚ) / (54192600000000 : ℚ)), ((4516524781397 : ℚ) / (54192600000000 : ℚ)), ((4928015325287 : ℚ) / (40644450000000 : ℚ)), ((2216062267381 : ℚ) / (23225400000000 : ℚ)), ((2186365205701 : ℚ) / (23225400000000 : ℚ)), ((131163066967 : ℚ) / (1847475000000 : ℚ)), ((264800219669 : ℚ) / (7389900000000 : ℚ)), ((253254486239 : ℚ) / (7389900000000 : ℚ)), ((249238214819 : ℚ) / (7389900000000 : ℚ)), ((4629416397157 : ℚ) / (162577800000000 : ℚ))],
    jensenBound := ((908067324516929631135568471107351357659550704124986141655143540998757184183124699344480000000000000000000000 : ℚ) / (442265394348024382387808443509716212780839427522499945448441532029726595205124866271476495098698702310951530040155475769 : ℚ)),
    jensenFloorQ96 := (162672699424695317 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_simplexId_before"
  err.flush

theorem geometryRow105_simplexId_read :
    geometryRowsJson105.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped105.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_vertexIds_before"
  err.flush

theorem geometryRow105_vertexIds_read :
    geometryRowsJson105.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped105.vertexIds := by decide +kernel

noncomputable def geometryRow105_physicalVolumeNumeratorChars : List Char := ['7', '3', '9', '9', '4', '4', '9', '3', '7', '8', '9', '6', '0', '5', '2', '8', '9', '4', '7', '2', '8', '7', '3', '0', '4', '7', '8', '9', '5', '2', '7', '2', '8', '7', '0', '1', '0', '9', '1']
noncomputable def geometryRow105_physicalVolumeDenominatorChars : List Char := ['1', '6', '9', '6', '9', '7', '9', '6', '8', '6', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow105_physicalVolumeText : String := String.ofList (geometryRow105_physicalVolumeNumeratorChars ++ '/' :: geometryRow105_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_physicalVolume_before_field"
  err.flush

theorem geometryRow105_physicalVolume_field :
    geometryRowsJson105.getObjVal? "physical_volume" = .ok (.str geometryRow105_physicalVolumeText) := by rfl

theorem geometryRow105_physicalVolume_numerator_no_slash :
    geometryRow105_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow105_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow105_physicalVolumeNumeratorChars = some (739944937896052894728730478952728701091 : Int) := by decide +kernel

theorem geometryRow105_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow105_physicalVolumeDenominatorChars = some (1696979686500000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow105_physicalVolume_denominator_nonzero : (1696979686500000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow105_physicalVolume_parse :
    parseRational geometryRow105_physicalVolumeText = .ok geometryRowsTyped105.physicalVolume :=
  original_rational_fraction_of_chars geometryRow105_physicalVolumeNumeratorChars geometryRow105_physicalVolumeDenominatorChars
    (739944937896052894728730478952728701091 : Int) (1696979686500000000000000000000000000000000000000000000000000 : Int)
    geometryRow105_physicalVolume_numerator_no_slash geometryRow105_physicalVolume_numerator_parse
    geometryRow105_physicalVolume_denominator_parse geometryRow105_physicalVolume_denominator_nonzero

theorem geometryRow105_physicalVolume_read :
    rationalField geometryRowsJson105 "physical_volume" = .ok geometryRowsTyped105.physicalVolume :=
  original_rationalField_of_string geometryRowsJson105 "physical_volume" geometryRow105_physicalVolumeText
    geometryRowsTyped105.physicalVolume geometryRow105_physicalVolume_field geometryRow105_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_physicalVolume_complete"
  err.flush

noncomputable def geometryRow105_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow105_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow105_meanGapText : String := String.ofList (geometryRow105_meanGapNumeratorChars ++ '/' :: geometryRow105_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_meanGap_before_field"
  err.flush

theorem geometryRow105_meanGap_field :
    geometryRowsJson105.getObjVal? "mean_gap" = .ok (.str geometryRow105_meanGapText) := by rfl

theorem geometryRow105_meanGap_numerator_no_slash :
    geometryRow105_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow105_meanGap_numerator_parse :
    SourceJson.intChars geometryRow105_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow105_meanGap_denominator_parse :
    SourceJson.intChars geometryRow105_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow105_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow105_meanGap_parse :
    parseRational geometryRow105_meanGapText = .ok geometryRowsTyped105.meanGap :=
  original_rational_fraction_of_chars geometryRow105_meanGapNumeratorChars geometryRow105_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow105_meanGap_numerator_no_slash geometryRow105_meanGap_numerator_parse
    geometryRow105_meanGap_denominator_parse geometryRow105_meanGap_denominator_nonzero

theorem geometryRow105_meanGap_read :
    rationalField geometryRowsJson105 "mean_gap" = .ok geometryRowsTyped105.meanGap :=
  original_rationalField_of_string geometryRowsJson105 "mean_gap" geometryRow105_meanGapText
    geometryRowsTyped105.meanGap geometryRow105_meanGap_field geometryRow105_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_meanGap_complete"
  err.flush

noncomputable def geometryRow105_jensenBoundNumeratorChars : List Char := ['9', '0', '8', '0', '6', '7', '3', '2', '4', '5', '1', '6', '9', '2', '9', '6', '3', '1', '1', '3', '5', '5', '6', '8', '4', '7', '1', '1', '0', '7', '3', '5', '1', '3', '5', '7', '6', '5', '9', '5', '5', '0', '7', '0', '4', '1', '2', '4', '9', '8', '6', '1', '4', '1', '6', '5', '5', '1', '4', '3', '5', '4', '0', '9', '9', '8', '7', '5', '7', '1', '8', '4', '1', '8', '3', '1', '2', '4', '6', '9', '9', '3', '4', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow105_jensenBoundDenominatorChars : List Char := ['4', '4', '2', '2', '6', '5', '3', '9', '4', '3', '4', '8', '0', '2', '4', '3', '8', '2', '3', '8', '7', '8', '0', '8', '4', '4', '3', '5', '0', '9', '7', '1', '6', '2', '1', '2', '7', '8', '0', '8', '3', '9', '4', '2', '7', '5', '2', '2', '4', '9', '9', '9', '4', '5', '4', '4', '8', '4', '4', '1', '5', '3', '2', '0', '2', '9', '7', '2', '6', '5', '9', '5', '2', '0', '5', '1', '2', '4', '8', '6', '6', '2', '7', '1', '4', '7', '6', '4', '9', '5', '0', '9', '8', '6', '9', '8', '7', '0', '2', '3', '1', '0', '9', '5', '1', '5', '3', '0', '0', '4', '0', '1', '5', '5', '4', '7', '5', '7', '6', '9']
noncomputable def geometryRow105_jensenBoundText : String := String.ofList (geometryRow105_jensenBoundNumeratorChars ++ '/' :: geometryRow105_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_jensenBound_before_field"
  err.flush

theorem geometryRow105_jensenBound_field :
    geometryRowsJson105.getObjVal? "jensen_bound" = .ok (.str geometryRow105_jensenBoundText) := by rfl

theorem geometryRow105_jensenBound_numerator_no_slash :
    geometryRow105_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow105_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow105_jensenBoundNumeratorChars = some (908067324516929631135568471107351357659550704124986141655143540998757184183124699344480000000000000000000000 : Int) := by decide +kernel

theorem geometryRow105_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow105_jensenBoundDenominatorChars = some (442265394348024382387808443509716212780839427522499945448441532029726595205124866271476495098698702310951530040155475769 : Int) := by decide +kernel

theorem geometryRow105_jensenBound_denominator_nonzero : (442265394348024382387808443509716212780839427522499945448441532029726595205124866271476495098698702310951530040155475769 : Int) ≠ 0 := by decide +kernel

theorem geometryRow105_jensenBound_parse :
    parseRational geometryRow105_jensenBoundText = .ok geometryRowsTyped105.jensenBound :=
  original_rational_fraction_of_chars geometryRow105_jensenBoundNumeratorChars geometryRow105_jensenBoundDenominatorChars
    (908067324516929631135568471107351357659550704124986141655143540998757184183124699344480000000000000000000000 : Int) (442265394348024382387808443509716212780839427522499945448441532029726595205124866271476495098698702310951530040155475769 : Int)
    geometryRow105_jensenBound_numerator_no_slash geometryRow105_jensenBound_numerator_parse
    geometryRow105_jensenBound_denominator_parse geometryRow105_jensenBound_denominator_nonzero

theorem geometryRow105_jensenBound_read :
    rationalField geometryRowsJson105 "jensen_bound" = .ok geometryRowsTyped105.jensenBound :=
  original_rationalField_of_string geometryRowsJson105 "jensen_bound" geometryRow105_jensenBoundText
    geometryRowsTyped105.jensenBound geometryRow105_jensenBound_field geometryRow105_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_factorMaxima_before"
  err.flush

theorem geometryRow105_factorMaxima_read :
    rationalArrayField geometryRowsJson105 "factor_maxima" = .ok geometryRowsTyped105.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_gapWeightedMeans_before"
  err.flush

theorem geometryRow105_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson105 "gap_weighted_means" = .ok geometryRowsTyped105.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow105_floorChars : List Char := ['1', '6', '2', '6', '7', '2', '6', '9', '9', '4', '2', '4', '6', '9', '5', '3', '1', '7']
noncomputable def geometryRow105_floorText : String := String.ofList geometryRow105_floorChars

theorem geometryRow105_floor_text_read :
    geometryRowsJson105.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow105_floorText := by rfl

theorem geometryRow105_floor_chars_parse :
    SourceJson.intChars geometryRow105_floorChars = some (162672699424695317 : Int) := by decide +kernel

theorem geometryRow105_floor_parse :
    parseInteger geometryRow105_floorText = .ok geometryRowsTyped105.jensenFloorQ96 := by
  simp only [geometryRow105_floorText, parseInteger, String.toList_ofList, geometryRow105_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_105 :
    decodeGeometryRow geometryRowsJson105 = .ok geometryRowsTyped105 :=
  original_geometryRow_of_fields geometryRowsJson105 geometryRowsTyped105 geometryRow105_floorText
    geometryRow105_simplexId_read geometryRow105_vertexIds_read
    geometryRow105_physicalVolume_read geometryRow105_meanGap_read
    geometryRow105_factorMaxima_read geometryRow105_gapWeightedMeans_read
    geometryRow105_jensenBound_read geometryRow105_floor_text_read geometryRow105_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_105_original_decoder_complete"
  err.flush

theorem geometryRow105_shape :
    geometryRowsTyped105.simplexId = 105 ∧
    geometryRowsTyped105.vertexIds.size = 9 ∧ geometryRowsTyped105.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped105.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped105.factorMaxima.size = 10 ∧ geometryRowsTyped105.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson106 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped106 : GeometryRow :=
  { simplexId := 106,
    vertexIds := #[32, 31, 30, 28, 26, 25, 24, 9, 7],
    physicalVolume := ((307308828878730237642336739586869633 : ℚ) / (135552519083520000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((33449081 : ℚ) / (24552000000 : ℚ)),
    factorMaxima := #[((8015629 : ℚ) / (88000000 : ℚ)), ((2140609 : ℚ) / (22000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1609371 : ℚ) / (22000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((1609371 : ℚ) / (44000000 : ℚ)), ((234379 : ℚ) / (7200000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((16028777180609020379 : ℚ) / (188885622443760000000 : ℚ)), ((16376198551964198201 : ℚ) / (188885622443760000000 : ℚ)), ((20208082182422946191 : ℚ) / (165274919638290000000 : ℚ)), ((165338391103036691 : ℚ) / (1728365172688000000 : ℚ)), ((2465987586291411197 : ℚ) / (25925477590320000000 : ℚ)), ((45634106071850731429 : ℚ) / (661099678553160000000 : ℚ)), ((9215350961181424379 : ℚ) / (264439871421264000000 : ℚ)), ((44011060713643966387 : ℚ) / (1322199357106320000000 : ℚ)), ((5721060001410144307 : ℚ) / (188885622443760000000 : ℚ)), ((5721047409035314723 : ℚ) / (188885622443760000000 : ℚ))],
    jensenBound := ((3845761692223875539305010727834275876474553973581665050861483743020203781895455936619406351403843429804185257123239182746653161700356231513830467045829016289280000000000000 : ℚ) / (187163195662373567642405209464808841173230564028404459101932658540742241981986013019185247183250613440210919891420840618064088943592310991600214287357786125998806271741102091468686452810873 : ℚ)),
    jensenFloorQ96 := (1627951645430 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_simplexId_before"
  err.flush

theorem geometryRow106_simplexId_read :
    geometryRowsJson106.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped106.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_vertexIds_before"
  err.flush

theorem geometryRow106_vertexIds_read :
    geometryRowsJson106.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped106.vertexIds := by decide +kernel

noncomputable def geometryRow106_physicalVolumeNumeratorChars : List Char := ['3', '0', '7', '3', '0', '8', '8', '2', '8', '8', '7', '8', '7', '3', '0', '2', '3', '7', '6', '4', '2', '3', '3', '6', '7', '3', '9', '5', '8', '6', '8', '6', '9', '6', '3', '3']
noncomputable def geometryRow106_physicalVolumeDenominatorChars : List Char := ['1', '3', '5', '5', '5', '2', '5', '1', '9', '0', '8', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow106_physicalVolumeText : String := String.ofList (geometryRow106_physicalVolumeNumeratorChars ++ '/' :: geometryRow106_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_physicalVolume_before_field"
  err.flush

theorem geometryRow106_physicalVolume_field :
    geometryRowsJson106.getObjVal? "physical_volume" = .ok (.str geometryRow106_physicalVolumeText) := by rfl

theorem geometryRow106_physicalVolume_numerator_no_slash :
    geometryRow106_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow106_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow106_physicalVolumeNumeratorChars = some (307308828878730237642336739586869633 : Int) := by decide +kernel

theorem geometryRow106_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow106_physicalVolumeDenominatorChars = some (135552519083520000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow106_physicalVolume_denominator_nonzero : (135552519083520000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow106_physicalVolume_parse :
    parseRational geometryRow106_physicalVolumeText = .ok geometryRowsTyped106.physicalVolume :=
  original_rational_fraction_of_chars geometryRow106_physicalVolumeNumeratorChars geometryRow106_physicalVolumeDenominatorChars
    (307308828878730237642336739586869633 : Int) (135552519083520000000000000000000000000000000000000000000000000 : Int)
    geometryRow106_physicalVolume_numerator_no_slash geometryRow106_physicalVolume_numerator_parse
    geometryRow106_physicalVolume_denominator_parse geometryRow106_physicalVolume_denominator_nonzero

theorem geometryRow106_physicalVolume_read :
    rationalField geometryRowsJson106 "physical_volume" = .ok geometryRowsTyped106.physicalVolume :=
  original_rationalField_of_string geometryRowsJson106 "physical_volume" geometryRow106_physicalVolumeText
    geometryRowsTyped106.physicalVolume geometryRow106_physicalVolume_field geometryRow106_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_physicalVolume_complete"
  err.flush

noncomputable def geometryRow106_meanGapNumeratorChars : List Char := ['3', '3', '4', '4', '9', '0', '8', '1']
noncomputable def geometryRow106_meanGapDenominatorChars : List Char := ['2', '4', '5', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow106_meanGapText : String := String.ofList (geometryRow106_meanGapNumeratorChars ++ '/' :: geometryRow106_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_meanGap_before_field"
  err.flush

theorem geometryRow106_meanGap_field :
    geometryRowsJson106.getObjVal? "mean_gap" = .ok (.str geometryRow106_meanGapText) := by rfl

theorem geometryRow106_meanGap_numerator_no_slash :
    geometryRow106_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow106_meanGap_numerator_parse :
    SourceJson.intChars geometryRow106_meanGapNumeratorChars = some (33449081 : Int) := by decide +kernel

theorem geometryRow106_meanGap_denominator_parse :
    SourceJson.intChars geometryRow106_meanGapDenominatorChars = some (24552000000 : Int) := by decide +kernel

theorem geometryRow106_meanGap_denominator_nonzero : (24552000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow106_meanGap_parse :
    parseRational geometryRow106_meanGapText = .ok geometryRowsTyped106.meanGap :=
  original_rational_fraction_of_chars geometryRow106_meanGapNumeratorChars geometryRow106_meanGapDenominatorChars
    (33449081 : Int) (24552000000 : Int)
    geometryRow106_meanGap_numerator_no_slash geometryRow106_meanGap_numerator_parse
    geometryRow106_meanGap_denominator_parse geometryRow106_meanGap_denominator_nonzero

theorem geometryRow106_meanGap_read :
    rationalField geometryRowsJson106 "mean_gap" = .ok geometryRowsTyped106.meanGap :=
  original_rationalField_of_string geometryRowsJson106 "mean_gap" geometryRow106_meanGapText
    geometryRowsTyped106.meanGap geometryRow106_meanGap_field geometryRow106_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_meanGap_complete"
  err.flush

noncomputable def geometryRow106_jensenBoundNumeratorChars : List Char := ['3', '8', '4', '5', '7', '6', '1', '6', '9', '2', '2', '2', '3', '8', '7', '5', '5', '3', '9', '3', '0', '5', '0', '1', '0', '7', '2', '7', '8', '3', '4', '2', '7', '5', '8', '7', '6', '4', '7', '4', '5', '5', '3', '9', '7', '3', '5', '8', '1', '6', '6', '5', '0', '5', '0', '8', '6', '1', '4', '8', '3', '7', '4', '3', '0', '2', '0', '2', '0', '3', '7', '8', '1', '8', '9', '5', '4', '5', '5', '9', '3', '6', '6', '1', '9', '4', '0', '6', '3', '5', '1', '4', '0', '3', '8', '4', '3', '4', '2', '9', '8', '0', '4', '1', '8', '5', '2', '5', '7', '1', '2', '3', '2', '3', '9', '1', '8', '2', '7', '4', '6', '6', '5', '3', '1', '6', '1', '7', '0', '0', '3', '5', '6', '2', '3', '1', '5', '1', '3', '8', '3', '0', '4', '6', '7', '0', '4', '5', '8', '2', '9', '0', '1', '6', '2', '8', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow106_jensenBoundDenominatorChars : List Char := ['1', '8', '7', '1', '6', '3', '1', '9', '5', '6', '6', '2', '3', '7', '3', '5', '6', '7', '6', '4', '2', '4', '0', '5', '2', '0', '9', '4', '6', '4', '8', '0', '8', '8', '4', '1', '1', '7', '3', '2', '3', '0', '5', '6', '4', '0', '2', '8', '4', '0', '4', '4', '5', '9', '1', '0', '1', '9', '3', '2', '6', '5', '8', '5', '4', '0', '7', '4', '2', '2', '4', '1', '9', '8', '1', '9', '8', '6', '0', '1', '3', '0', '1', '9', '1', '8', '5', '2', '4', '7', '1', '8', '3', '2', '5', '0', '6', '1', '3', '4', '4', '0', '2', '1', '0', '9', '1', '9', '8', '9', '1', '4', '2', '0', '8', '4', '0', '6', '1', '8', '0', '6', '4', '0', '8', '8', '9', '4', '3', '5', '9', '2', '3', '1', '0', '9', '9', '1', '6', '0', '0', '2', '1', '4', '2', '8', '7', '3', '5', '7', '7', '8', '6', '1', '2', '5', '9', '9', '8', '8', '0', '6', '2', '7', '1', '7', '4', '1', '1', '0', '2', '0', '9', '1', '4', '6', '8', '6', '8', '6', '4', '5', '2', '8', '1', '0', '8', '7', '3']
noncomputable def geometryRow106_jensenBoundText : String := String.ofList (geometryRow106_jensenBoundNumeratorChars ++ '/' :: geometryRow106_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_jensenBound_before_field"
  err.flush

theorem geometryRow106_jensenBound_field :
    geometryRowsJson106.getObjVal? "jensen_bound" = .ok (.str geometryRow106_jensenBoundText) := by rfl

theorem geometryRow106_jensenBound_numerator_no_slash :
    geometryRow106_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow106_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow106_jensenBoundNumeratorChars = some (3845761692223875539305010727834275876474553973581665050861483743020203781895455936619406351403843429804185257123239182746653161700356231513830467045829016289280000000000000 : Int) := by decide +kernel

theorem geometryRow106_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow106_jensenBoundDenominatorChars = some (187163195662373567642405209464808841173230564028404459101932658540742241981986013019185247183250613440210919891420840618064088943592310991600214287357786125998806271741102091468686452810873 : Int) := by decide +kernel

theorem geometryRow106_jensenBound_denominator_nonzero : (187163195662373567642405209464808841173230564028404459101932658540742241981986013019185247183250613440210919891420840618064088943592310991600214287357786125998806271741102091468686452810873 : Int) ≠ 0 := by decide +kernel

theorem geometryRow106_jensenBound_parse :
    parseRational geometryRow106_jensenBoundText = .ok geometryRowsTyped106.jensenBound :=
  original_rational_fraction_of_chars geometryRow106_jensenBoundNumeratorChars geometryRow106_jensenBoundDenominatorChars
    (3845761692223875539305010727834275876474553973581665050861483743020203781895455936619406351403843429804185257123239182746653161700356231513830467045829016289280000000000000 : Int) (187163195662373567642405209464808841173230564028404459101932658540742241981986013019185247183250613440210919891420840618064088943592310991600214287357786125998806271741102091468686452810873 : Int)
    geometryRow106_jensenBound_numerator_no_slash geometryRow106_jensenBound_numerator_parse
    geometryRow106_jensenBound_denominator_parse geometryRow106_jensenBound_denominator_nonzero

theorem geometryRow106_jensenBound_read :
    rationalField geometryRowsJson106 "jensen_bound" = .ok geometryRowsTyped106.jensenBound :=
  original_rationalField_of_string geometryRowsJson106 "jensen_bound" geometryRow106_jensenBoundText
    geometryRowsTyped106.jensenBound geometryRow106_jensenBound_field geometryRow106_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_factorMaxima_before"
  err.flush

theorem geometryRow106_factorMaxima_read :
    rationalArrayField geometryRowsJson106 "factor_maxima" = .ok geometryRowsTyped106.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_gapWeightedMeans_before"
  err.flush

theorem geometryRow106_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson106 "gap_weighted_means" = .ok geometryRowsTyped106.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow106_floorChars : List Char := ['1', '6', '2', '7', '9', '5', '1', '6', '4', '5', '4', '3', '0']
noncomputable def geometryRow106_floorText : String := String.ofList geometryRow106_floorChars

theorem geometryRow106_floor_text_read :
    geometryRowsJson106.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow106_floorText := by rfl

theorem geometryRow106_floor_chars_parse :
    SourceJson.intChars geometryRow106_floorChars = some (1627951645430 : Int) := by decide +kernel

theorem geometryRow106_floor_parse :
    parseInteger geometryRow106_floorText = .ok geometryRowsTyped106.jensenFloorQ96 := by
  simp only [geometryRow106_floorText, parseInteger, String.toList_ofList, geometryRow106_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_106 :
    decodeGeometryRow geometryRowsJson106 = .ok geometryRowsTyped106 :=
  original_geometryRow_of_fields geometryRowsJson106 geometryRowsTyped106 geometryRow106_floorText
    geometryRow106_simplexId_read geometryRow106_vertexIds_read
    geometryRow106_physicalVolume_read geometryRow106_meanGap_read
    geometryRow106_factorMaxima_read geometryRow106_gapWeightedMeans_read
    geometryRow106_jensenBound_read geometryRow106_floor_text_read geometryRow106_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_106_original_decoder_complete"
  err.flush

theorem geometryRow106_shape :
    geometryRowsTyped106.simplexId = 106 ∧
    geometryRowsTyped106.vertexIds.size = 9 ∧ geometryRowsTyped106.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped106.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped106.factorMaxima.size = 10 ∧ geometryRowsTyped106.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson107 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped107 : GeometryRow :=
  { simplexId := 107,
    vertexIds := #[32, 31, 30, 28, 26, 25, 24, 14, 7],
    physicalVolume := ((362726405741545981985534844725121667 : ℚ) / (19531223179776000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((1047354171169 : ℚ) / (12204720000000 : ℚ)), ((212504300747 : ℚ) / (2440944000000 : ℚ)), ((163554047417 : ℚ) / (1334891250000 : ℚ)), ((2694036912851 : ℚ) / (28477680000000 : ℚ)), ((2678561728819 : ℚ) / (28477680000000 : ℚ)), ((2971352192507 : ℚ) / (42716520000000 : ℚ)), ((2999953648709 : ℚ) / (85433040000000 : ℚ)), ((2866480186433 : ℚ) / (85433040000000 : ℚ)), ((14844957221 : ℚ) / (488188800000 : ℚ)), ((371123116877 : ℚ) / (12204720000000 : ℚ))],
    jensenBound := ((27192185405191652980766796320840337333274990318960416589529570650559671435219473635082240000000000000 : ℚ) / (327238144961328100287276550810324606803756518618666683834002088223621076831512967279010453126529322248271223542890429 : ℚ)),
    jensenFloorQ96 := (6583544484568 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_simplexId_before"
  err.flush

theorem geometryRow107_simplexId_read :
    geometryRowsJson107.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped107.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_vertexIds_before"
  err.flush

theorem geometryRow107_vertexIds_read :
    geometryRowsJson107.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped107.vertexIds := by decide +kernel

noncomputable def geometryRow107_physicalVolumeNumeratorChars : List Char := ['3', '6', '2', '7', '2', '6', '4', '0', '5', '7', '4', '1', '5', '4', '5', '9', '8', '1', '9', '8', '5', '5', '3', '4', '8', '4', '4', '7', '2', '5', '1', '2', '1', '6', '6', '7']
noncomputable def geometryRow107_physicalVolumeDenominatorChars : List Char := ['1', '9', '5', '3', '1', '2', '2', '3', '1', '7', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow107_physicalVolumeText : String := String.ofList (geometryRow107_physicalVolumeNumeratorChars ++ '/' :: geometryRow107_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_physicalVolume_before_field"
  err.flush

theorem geometryRow107_physicalVolume_field :
    geometryRowsJson107.getObjVal? "physical_volume" = .ok (.str geometryRow107_physicalVolumeText) := by rfl

theorem geometryRow107_physicalVolume_numerator_no_slash :
    geometryRow107_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow107_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow107_physicalVolumeNumeratorChars = some (362726405741545981985534844725121667 : Int) := by decide +kernel

theorem geometryRow107_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow107_physicalVolumeDenominatorChars = some (19531223179776000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow107_physicalVolume_denominator_nonzero : (19531223179776000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow107_physicalVolume_parse :
    parseRational geometryRow107_physicalVolumeText = .ok geometryRowsTyped107.physicalVolume :=
  original_rational_fraction_of_chars geometryRow107_physicalVolumeNumeratorChars geometryRow107_physicalVolumeDenominatorChars
    (362726405741545981985534844725121667 : Int) (19531223179776000000000000000000000000000000000000000000000000 : Int)
    geometryRow107_physicalVolume_numerator_no_slash geometryRow107_physicalVolume_numerator_parse
    geometryRow107_physicalVolume_denominator_parse geometryRow107_physicalVolume_denominator_nonzero

theorem geometryRow107_physicalVolume_read :
    rationalField geometryRowsJson107 "physical_volume" = .ok geometryRowsTyped107.physicalVolume :=
  original_rationalField_of_string geometryRowsJson107 "physical_volume" geometryRow107_physicalVolumeText
    geometryRowsTyped107.physicalVolume geometryRow107_physicalVolume_field geometryRow107_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_physicalVolume_complete"
  err.flush

noncomputable def geometryRow107_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow107_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow107_meanGapText : String := String.ofList (geometryRow107_meanGapNumeratorChars ++ '/' :: geometryRow107_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_meanGap_before_field"
  err.flush

theorem geometryRow107_meanGap_field :
    geometryRowsJson107.getObjVal? "mean_gap" = .ok (.str geometryRow107_meanGapText) := by rfl

theorem geometryRow107_meanGap_numerator_no_slash :
    geometryRow107_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow107_meanGap_numerator_parse :
    SourceJson.intChars geometryRow107_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow107_meanGap_denominator_parse :
    SourceJson.intChars geometryRow107_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow107_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow107_meanGap_parse :
    parseRational geometryRow107_meanGapText = .ok geometryRowsTyped107.meanGap :=
  original_rational_fraction_of_chars geometryRow107_meanGapNumeratorChars geometryRow107_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow107_meanGap_numerator_no_slash geometryRow107_meanGap_numerator_parse
    geometryRow107_meanGap_denominator_parse geometryRow107_meanGap_denominator_nonzero

theorem geometryRow107_meanGap_read :
    rationalField geometryRowsJson107 "mean_gap" = .ok geometryRowsTyped107.meanGap :=
  original_rationalField_of_string geometryRowsJson107 "mean_gap" geometryRow107_meanGapText
    geometryRowsTyped107.meanGap geometryRow107_meanGap_field geometryRow107_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_meanGap_complete"
  err.flush

noncomputable def geometryRow107_jensenBoundNumeratorChars : List Char := ['2', '7', '1', '9', '2', '1', '8', '5', '4', '0', '5', '1', '9', '1', '6', '5', '2', '9', '8', '0', '7', '6', '6', '7', '9', '6', '3', '2', '0', '8', '4', '0', '3', '3', '7', '3', '3', '3', '2', '7', '4', '9', '9', '0', '3', '1', '8', '9', '6', '0', '4', '1', '6', '5', '8', '9', '5', '2', '9', '5', '7', '0', '6', '5', '0', '5', '5', '9', '6', '7', '1', '4', '3', '5', '2', '1', '9', '4', '7', '3', '6', '3', '5', '0', '8', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow107_jensenBoundDenominatorChars : List Char := ['3', '2', '7', '2', '3', '8', '1', '4', '4', '9', '6', '1', '3', '2', '8', '1', '0', '0', '2', '8', '7', '2', '7', '6', '5', '5', '0', '8', '1', '0', '3', '2', '4', '6', '0', '6', '8', '0', '3', '7', '5', '6', '5', '1', '8', '6', '1', '8', '6', '6', '6', '6', '8', '3', '8', '3', '4', '0', '0', '2', '0', '8', '8', '2', '2', '3', '6', '2', '1', '0', '7', '6', '8', '3', '1', '5', '1', '2', '9', '6', '7', '2', '7', '9', '0', '1', '0', '4', '5', '3', '1', '2', '6', '5', '2', '9', '3', '2', '2', '2', '4', '8', '2', '7', '1', '2', '2', '3', '5', '4', '2', '8', '9', '0', '4', '2', '9']
noncomputable def geometryRow107_jensenBoundText : String := String.ofList (geometryRow107_jensenBoundNumeratorChars ++ '/' :: geometryRow107_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_jensenBound_before_field"
  err.flush

theorem geometryRow107_jensenBound_field :
    geometryRowsJson107.getObjVal? "jensen_bound" = .ok (.str geometryRow107_jensenBoundText) := by rfl

theorem geometryRow107_jensenBound_numerator_no_slash :
    geometryRow107_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow107_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow107_jensenBoundNumeratorChars = some (27192185405191652980766796320840337333274990318960416589529570650559671435219473635082240000000000000 : Int) := by decide +kernel

theorem geometryRow107_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow107_jensenBoundDenominatorChars = some (327238144961328100287276550810324606803756518618666683834002088223621076831512967279010453126529322248271223542890429 : Int) := by decide +kernel

theorem geometryRow107_jensenBound_denominator_nonzero : (327238144961328100287276550810324606803756518618666683834002088223621076831512967279010453126529322248271223542890429 : Int) ≠ 0 := by decide +kernel

theorem geometryRow107_jensenBound_parse :
    parseRational geometryRow107_jensenBoundText = .ok geometryRowsTyped107.jensenBound :=
  original_rational_fraction_of_chars geometryRow107_jensenBoundNumeratorChars geometryRow107_jensenBoundDenominatorChars
    (27192185405191652980766796320840337333274990318960416589529570650559671435219473635082240000000000000 : Int) (327238144961328100287276550810324606803756518618666683834002088223621076831512967279010453126529322248271223542890429 : Int)
    geometryRow107_jensenBound_numerator_no_slash geometryRow107_jensenBound_numerator_parse
    geometryRow107_jensenBound_denominator_parse geometryRow107_jensenBound_denominator_nonzero

theorem geometryRow107_jensenBound_read :
    rationalField geometryRowsJson107 "jensen_bound" = .ok geometryRowsTyped107.jensenBound :=
  original_rationalField_of_string geometryRowsJson107 "jensen_bound" geometryRow107_jensenBoundText
    geometryRowsTyped107.jensenBound geometryRow107_jensenBound_field geometryRow107_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_factorMaxima_before"
  err.flush

theorem geometryRow107_factorMaxima_read :
    rationalArrayField geometryRowsJson107 "factor_maxima" = .ok geometryRowsTyped107.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_gapWeightedMeans_before"
  err.flush

theorem geometryRow107_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson107 "gap_weighted_means" = .ok geometryRowsTyped107.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow107_floorChars : List Char := ['6', '5', '8', '3', '5', '4', '4', '4', '8', '4', '5', '6', '8']
noncomputable def geometryRow107_floorText : String := String.ofList geometryRow107_floorChars

theorem geometryRow107_floor_text_read :
    geometryRowsJson107.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow107_floorText := by rfl

theorem geometryRow107_floor_chars_parse :
    SourceJson.intChars geometryRow107_floorChars = some (6583544484568 : Int) := by decide +kernel

theorem geometryRow107_floor_parse :
    parseInteger geometryRow107_floorText = .ok geometryRowsTyped107.jensenFloorQ96 := by
  simp only [geometryRow107_floorText, parseInteger, String.toList_ofList, geometryRow107_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_107 :
    decodeGeometryRow geometryRowsJson107 = .ok geometryRowsTyped107 :=
  original_geometryRow_of_fields geometryRowsJson107 geometryRowsTyped107 geometryRow107_floorText
    geometryRow107_simplexId_read geometryRow107_vertexIds_read
    geometryRow107_physicalVolume_read geometryRow107_meanGap_read
    geometryRow107_factorMaxima_read geometryRow107_gapWeightedMeans_read
    geometryRow107_jensenBound_read geometryRow107_floor_text_read geometryRow107_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_107_original_decoder_complete"
  err.flush

theorem geometryRow107_shape :
    geometryRowsTyped107.simplexId = 107 ∧
    geometryRowsTyped107.vertexIds.size = 9 ∧ geometryRowsTyped107.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped107.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped107.factorMaxima.size = 10 ∧ geometryRowsTyped107.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson108 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped108 : GeometryRow :=
  { simplexId := 108,
    vertexIds := #[32, 31, 30, 28, 26, 25, 14, 11, 7],
    physicalVolume := ((3060182520569588733190795532927393 : ℚ) / (118371049574400000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((738867860173 : ℚ) / (8543304000000 : ℚ)), ((1873712482423 : ℚ) / (21358260000000 : ℚ)), ((740525531917 : ℚ) / (6102360000000 : ℚ)), ((442385704603 : ℚ) / (4746280000000 : ℚ)), ((1319419521793 : ℚ) / (14238840000000 : ℚ)), ((433671959219 : ℚ) / (6102360000000 : ℚ)), ((612861034147 : ℚ) / (17086608000000 : ℚ)), ((2930831708459 : ℚ) / (85433040000000 : ℚ)), ((654233495381 : ℚ) / (21358260000000 : ℚ)), ((654232071497 : ℚ) / (21358260000000 : ℚ))],
    jensenBound := ((21832300740902862365750927062057206349157290040488382318633479155564181341957202082946048000000000000000 : ℚ) / (199513639580414069891676832978427193308004914630455227884678775523567351255074180520387671714856826969140501023407032723 : ℚ)),
    jensenFloorQ96 := (8669748468316 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_simplexId_before"
  err.flush

theorem geometryRow108_simplexId_read :
    geometryRowsJson108.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped108.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_vertexIds_before"
  err.flush

theorem geometryRow108_vertexIds_read :
    geometryRowsJson108.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped108.vertexIds := by decide +kernel

noncomputable def geometryRow108_physicalVolumeNumeratorChars : List Char := ['3', '0', '6', '0', '1', '8', '2', '5', '2', '0', '5', '6', '9', '5', '8', '8', '7', '3', '3', '1', '9', '0', '7', '9', '5', '5', '3', '2', '9', '2', '7', '3', '9', '3']
noncomputable def geometryRow108_physicalVolumeDenominatorChars : List Char := ['1', '1', '8', '3', '7', '1', '0', '4', '9', '5', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow108_physicalVolumeText : String := String.ofList (geometryRow108_physicalVolumeNumeratorChars ++ '/' :: geometryRow108_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_physicalVolume_before_field"
  err.flush

theorem geometryRow108_physicalVolume_field :
    geometryRowsJson108.getObjVal? "physical_volume" = .ok (.str geometryRow108_physicalVolumeText) := by rfl

theorem geometryRow108_physicalVolume_numerator_no_slash :
    geometryRow108_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow108_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow108_physicalVolumeNumeratorChars = some (3060182520569588733190795532927393 : Int) := by decide +kernel

theorem geometryRow108_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow108_physicalVolumeDenominatorChars = some (118371049574400000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow108_physicalVolume_denominator_nonzero : (118371049574400000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow108_physicalVolume_parse :
    parseRational geometryRow108_physicalVolumeText = .ok geometryRowsTyped108.physicalVolume :=
  original_rational_fraction_of_chars geometryRow108_physicalVolumeNumeratorChars geometryRow108_physicalVolumeDenominatorChars
    (3060182520569588733190795532927393 : Int) (118371049574400000000000000000000000000000000000000000000000 : Int)
    geometryRow108_physicalVolume_numerator_no_slash geometryRow108_physicalVolume_numerator_parse
    geometryRow108_physicalVolume_denominator_parse geometryRow108_physicalVolume_denominator_nonzero

theorem geometryRow108_physicalVolume_read :
    rationalField geometryRowsJson108 "physical_volume" = .ok geometryRowsTyped108.physicalVolume :=
  original_rationalField_of_string geometryRowsJson108 "physical_volume" geometryRow108_physicalVolumeText
    geometryRowsTyped108.physicalVolume geometryRow108_physicalVolume_field geometryRow108_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_physicalVolume_complete"
  err.flush

noncomputable def geometryRow108_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow108_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow108_meanGapText : String := String.ofList (geometryRow108_meanGapNumeratorChars ++ '/' :: geometryRow108_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_meanGap_before_field"
  err.flush

theorem geometryRow108_meanGap_field :
    geometryRowsJson108.getObjVal? "mean_gap" = .ok (.str geometryRow108_meanGapText) := by rfl

theorem geometryRow108_meanGap_numerator_no_slash :
    geometryRow108_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow108_meanGap_numerator_parse :
    SourceJson.intChars geometryRow108_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow108_meanGap_denominator_parse :
    SourceJson.intChars geometryRow108_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow108_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow108_meanGap_parse :
    parseRational geometryRow108_meanGapText = .ok geometryRowsTyped108.meanGap :=
  original_rational_fraction_of_chars geometryRow108_meanGapNumeratorChars geometryRow108_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow108_meanGap_numerator_no_slash geometryRow108_meanGap_numerator_parse
    geometryRow108_meanGap_denominator_parse geometryRow108_meanGap_denominator_nonzero

theorem geometryRow108_meanGap_read :
    rationalField geometryRowsJson108 "mean_gap" = .ok geometryRowsTyped108.meanGap :=
  original_rationalField_of_string geometryRowsJson108 "mean_gap" geometryRow108_meanGapText
    geometryRowsTyped108.meanGap geometryRow108_meanGap_field geometryRow108_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_meanGap_complete"
  err.flush

noncomputable def geometryRow108_jensenBoundNumeratorChars : List Char := ['2', '1', '8', '3', '2', '3', '0', '0', '7', '4', '0', '9', '0', '2', '8', '6', '2', '3', '6', '5', '7', '5', '0', '9', '2', '7', '0', '6', '2', '0', '5', '7', '2', '0', '6', '3', '4', '9', '1', '5', '7', '2', '9', '0', '0', '4', '0', '4', '8', '8', '3', '8', '2', '3', '1', '8', '6', '3', '3', '4', '7', '9', '1', '5', '5', '5', '6', '4', '1', '8', '1', '3', '4', '1', '9', '5', '7', '2', '0', '2', '0', '8', '2', '9', '4', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow108_jensenBoundDenominatorChars : List Char := ['1', '9', '9', '5', '1', '3', '6', '3', '9', '5', '8', '0', '4', '1', '4', '0', '6', '9', '8', '9', '1', '6', '7', '6', '8', '3', '2', '9', '7', '8', '4', '2', '7', '1', '9', '3', '3', '0', '8', '0', '0', '4', '9', '1', '4', '6', '3', '0', '4', '5', '5', '2', '2', '7', '8', '8', '4', '6', '7', '8', '7', '7', '5', '5', '2', '3', '5', '6', '7', '3', '5', '1', '2', '5', '5', '0', '7', '4', '1', '8', '0', '5', '2', '0', '3', '8', '7', '6', '7', '1', '7', '1', '4', '8', '5', '6', '8', '2', '6', '9', '6', '9', '1', '4', '0', '5', '0', '1', '0', '2', '3', '4', '0', '7', '0', '3', '2', '7', '2', '3']
noncomputable def geometryRow108_jensenBoundText : String := String.ofList (geometryRow108_jensenBoundNumeratorChars ++ '/' :: geometryRow108_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_jensenBound_before_field"
  err.flush

theorem geometryRow108_jensenBound_field :
    geometryRowsJson108.getObjVal? "jensen_bound" = .ok (.str geometryRow108_jensenBoundText) := by rfl

theorem geometryRow108_jensenBound_numerator_no_slash :
    geometryRow108_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow108_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow108_jensenBoundNumeratorChars = some (21832300740902862365750927062057206349157290040488382318633479155564181341957202082946048000000000000000 : Int) := by decide +kernel

theorem geometryRow108_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow108_jensenBoundDenominatorChars = some (199513639580414069891676832978427193308004914630455227884678775523567351255074180520387671714856826969140501023407032723 : Int) := by decide +kernel

theorem geometryRow108_jensenBound_denominator_nonzero : (199513639580414069891676832978427193308004914630455227884678775523567351255074180520387671714856826969140501023407032723 : Int) ≠ 0 := by decide +kernel

theorem geometryRow108_jensenBound_parse :
    parseRational geometryRow108_jensenBoundText = .ok geometryRowsTyped108.jensenBound :=
  original_rational_fraction_of_chars geometryRow108_jensenBoundNumeratorChars geometryRow108_jensenBoundDenominatorChars
    (21832300740902862365750927062057206349157290040488382318633479155564181341957202082946048000000000000000 : Int) (199513639580414069891676832978427193308004914630455227884678775523567351255074180520387671714856826969140501023407032723 : Int)
    geometryRow108_jensenBound_numerator_no_slash geometryRow108_jensenBound_numerator_parse
    geometryRow108_jensenBound_denominator_parse geometryRow108_jensenBound_denominator_nonzero

theorem geometryRow108_jensenBound_read :
    rationalField geometryRowsJson108 "jensen_bound" = .ok geometryRowsTyped108.jensenBound :=
  original_rationalField_of_string geometryRowsJson108 "jensen_bound" geometryRow108_jensenBoundText
    geometryRowsTyped108.jensenBound geometryRow108_jensenBound_field geometryRow108_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_factorMaxima_before"
  err.flush

theorem geometryRow108_factorMaxima_read :
    rationalArrayField geometryRowsJson108 "factor_maxima" = .ok geometryRowsTyped108.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_gapWeightedMeans_before"
  err.flush

theorem geometryRow108_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson108 "gap_weighted_means" = .ok geometryRowsTyped108.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow108_floorChars : List Char := ['8', '6', '6', '9', '7', '4', '8', '4', '6', '8', '3', '1', '6']
noncomputable def geometryRow108_floorText : String := String.ofList geometryRow108_floorChars

theorem geometryRow108_floor_text_read :
    geometryRowsJson108.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow108_floorText := by rfl

theorem geometryRow108_floor_chars_parse :
    SourceJson.intChars geometryRow108_floorChars = some (8669748468316 : Int) := by decide +kernel

theorem geometryRow108_floor_parse :
    parseInteger geometryRow108_floorText = .ok geometryRowsTyped108.jensenFloorQ96 := by
  simp only [geometryRow108_floorText, parseInteger, String.toList_ofList, geometryRow108_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_108 :
    decodeGeometryRow geometryRowsJson108 = .ok geometryRowsTyped108 :=
  original_geometryRow_of_fields geometryRowsJson108 geometryRowsTyped108 geometryRow108_floorText
    geometryRow108_simplexId_read geometryRow108_vertexIds_read
    geometryRow108_physicalVolume_read geometryRow108_meanGap_read
    geometryRow108_factorMaxima_read geometryRow108_gapWeightedMeans_read
    geometryRow108_jensenBound_read geometryRow108_floor_text_read geometryRow108_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_108_original_decoder_complete"
  err.flush

theorem geometryRow108_shape :
    geometryRowsTyped108.simplexId = 108 ∧
    geometryRowsTyped108.vertexIds.size = 9 ∧ geometryRowsTyped108.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped108.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped108.factorMaxima.size = 10 ∧ geometryRowsTyped108.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson109 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped109 : GeometryRow :=
  { simplexId := 109,
    vertexIds := #[32, 31, 30, 28, 26, 14, 12, 11, 7],
    physicalVolume := ((5950313187058730825056306457196503 : ℚ) / (184132743782400000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((374439009479 : ℚ) / (4271652000000 : ℚ)), ((3797475758771 : ℚ) / (42716520000000 : ℚ)), ((2566813964747 : ℚ) / (21358260000000 : ℚ)), ((1304912316509 : ℚ) / (14238840000000 : ℚ)), ((432391574831 : ℚ) / (4746280000000 : ℚ)), ((1542877254229 : ℚ) / (21358260000000 : ℚ)), ((3197776293773 : ℚ) / (85433040000000 : ℚ)), ((2897462173271 : ℚ) / (85433040000000 : ℚ)), ((1325150588737 : ℚ) / (42716520000000 : ℚ)), ((1325147740969 : ℚ) / (42716520000000 : ℚ))],
    jensenBound := ((6686095229729576288796885785384648104722598283493421848979756386587979641560167800668853760000000000000000 : ℚ) / (51695865311893071974895712042934231076955022614123797932485961271465114724801638405412005259194826629440648316892704374507 : ℚ)),
    jensenFloorQ96 := (10246990474980 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_simplexId_before"
  err.flush

theorem geometryRow109_simplexId_read :
    geometryRowsJson109.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped109.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_vertexIds_before"
  err.flush

theorem geometryRow109_vertexIds_read :
    geometryRowsJson109.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped109.vertexIds := by decide +kernel

noncomputable def geometryRow109_physicalVolumeNumeratorChars : List Char := ['5', '9', '5', '0', '3', '1', '3', '1', '8', '7', '0', '5', '8', '7', '3', '0', '8', '2', '5', '0', '5', '6', '3', '0', '6', '4', '5', '7', '1', '9', '6', '5', '0', '3']
noncomputable def geometryRow109_physicalVolumeDenominatorChars : List Char := ['1', '8', '4', '1', '3', '2', '7', '4', '3', '7', '8', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow109_physicalVolumeText : String := String.ofList (geometryRow109_physicalVolumeNumeratorChars ++ '/' :: geometryRow109_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_physicalVolume_before_field"
  err.flush

theorem geometryRow109_physicalVolume_field :
    geometryRowsJson109.getObjVal? "physical_volume" = .ok (.str geometryRow109_physicalVolumeText) := by rfl

theorem geometryRow109_physicalVolume_numerator_no_slash :
    geometryRow109_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow109_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow109_physicalVolumeNumeratorChars = some (5950313187058730825056306457196503 : Int) := by decide +kernel

theorem geometryRow109_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow109_physicalVolumeDenominatorChars = some (184132743782400000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow109_physicalVolume_denominator_nonzero : (184132743782400000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow109_physicalVolume_parse :
    parseRational geometryRow109_physicalVolumeText = .ok geometryRowsTyped109.physicalVolume :=
  original_rational_fraction_of_chars geometryRow109_physicalVolumeNumeratorChars geometryRow109_physicalVolumeDenominatorChars
    (5950313187058730825056306457196503 : Int) (184132743782400000000000000000000000000000000000000000000000 : Int)
    geometryRow109_physicalVolume_numerator_no_slash geometryRow109_physicalVolume_numerator_parse
    geometryRow109_physicalVolume_denominator_parse geometryRow109_physicalVolume_denominator_nonzero

theorem geometryRow109_physicalVolume_read :
    rationalField geometryRowsJson109 "physical_volume" = .ok geometryRowsTyped109.physicalVolume :=
  original_rationalField_of_string geometryRowsJson109 "physical_volume" geometryRow109_physicalVolumeText
    geometryRowsTyped109.physicalVolume geometryRow109_physicalVolume_field geometryRow109_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_physicalVolume_complete"
  err.flush

noncomputable def geometryRow109_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow109_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow109_meanGapText : String := String.ofList (geometryRow109_meanGapNumeratorChars ++ '/' :: geometryRow109_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_meanGap_before_field"
  err.flush

theorem geometryRow109_meanGap_field :
    geometryRowsJson109.getObjVal? "mean_gap" = .ok (.str geometryRow109_meanGapText) := by rfl

theorem geometryRow109_meanGap_numerator_no_slash :
    geometryRow109_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow109_meanGap_numerator_parse :
    SourceJson.intChars geometryRow109_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow109_meanGap_denominator_parse :
    SourceJson.intChars geometryRow109_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow109_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow109_meanGap_parse :
    parseRational geometryRow109_meanGapText = .ok geometryRowsTyped109.meanGap :=
  original_rational_fraction_of_chars geometryRow109_meanGapNumeratorChars geometryRow109_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow109_meanGap_numerator_no_slash geometryRow109_meanGap_numerator_parse
    geometryRow109_meanGap_denominator_parse geometryRow109_meanGap_denominator_nonzero

theorem geometryRow109_meanGap_read :
    rationalField geometryRowsJson109 "mean_gap" = .ok geometryRowsTyped109.meanGap :=
  original_rationalField_of_string geometryRowsJson109 "mean_gap" geometryRow109_meanGapText
    geometryRowsTyped109.meanGap geometryRow109_meanGap_field geometryRow109_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_meanGap_complete"
  err.flush

noncomputable def geometryRow109_jensenBoundNumeratorChars : List Char := ['6', '6', '8', '6', '0', '9', '5', '2', '2', '9', '7', '2', '9', '5', '7', '6', '2', '8', '8', '7', '9', '6', '8', '8', '5', '7', '8', '5', '3', '8', '4', '6', '4', '8', '1', '0', '4', '7', '2', '2', '5', '9', '8', '2', '8', '3', '4', '9', '3', '4', '2', '1', '8', '4', '8', '9', '7', '9', '7', '5', '6', '3', '8', '6', '5', '8', '7', '9', '7', '9', '6', '4', '1', '5', '6', '0', '1', '6', '7', '8', '0', '0', '6', '6', '8', '8', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow109_jensenBoundDenominatorChars : List Char := ['5', '1', '6', '9', '5', '8', '6', '5', '3', '1', '1', '8', '9', '3', '0', '7', '1', '9', '7', '4', '8', '9', '5', '7', '1', '2', '0', '4', '2', '9', '3', '4', '2', '3', '1', '0', '7', '6', '9', '5', '5', '0', '2', '2', '6', '1', '4', '1', '2', '3', '7', '9', '7', '9', '3', '2', '4', '8', '5', '9', '6', '1', '2', '7', '1', '4', '6', '5', '1', '1', '4', '7', '2', '4', '8', '0', '1', '6', '3', '8', '4', '0', '5', '4', '1', '2', '0', '0', '5', '2', '5', '9', '1', '9', '4', '8', '2', '6', '6', '2', '9', '4', '4', '0', '6', '4', '8', '3', '1', '6', '8', '9', '2', '7', '0', '4', '3', '7', '4', '5', '0', '7']
noncomputable def geometryRow109_jensenBoundText : String := String.ofList (geometryRow109_jensenBoundNumeratorChars ++ '/' :: geometryRow109_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_jensenBound_before_field"
  err.flush

theorem geometryRow109_jensenBound_field :
    geometryRowsJson109.getObjVal? "jensen_bound" = .ok (.str geometryRow109_jensenBoundText) := by rfl

theorem geometryRow109_jensenBound_numerator_no_slash :
    geometryRow109_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow109_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow109_jensenBoundNumeratorChars = some (6686095229729576288796885785384648104722598283493421848979756386587979641560167800668853760000000000000000 : Int) := by decide +kernel

theorem geometryRow109_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow109_jensenBoundDenominatorChars = some (51695865311893071974895712042934231076955022614123797932485961271465114724801638405412005259194826629440648316892704374507 : Int) := by decide +kernel

theorem geometryRow109_jensenBound_denominator_nonzero : (51695865311893071974895712042934231076955022614123797932485961271465114724801638405412005259194826629440648316892704374507 : Int) ≠ 0 := by decide +kernel

theorem geometryRow109_jensenBound_parse :
    parseRational geometryRow109_jensenBoundText = .ok geometryRowsTyped109.jensenBound :=
  original_rational_fraction_of_chars geometryRow109_jensenBoundNumeratorChars geometryRow109_jensenBoundDenominatorChars
    (6686095229729576288796885785384648104722598283493421848979756386587979641560167800668853760000000000000000 : Int) (51695865311893071974895712042934231076955022614123797932485961271465114724801638405412005259194826629440648316892704374507 : Int)
    geometryRow109_jensenBound_numerator_no_slash geometryRow109_jensenBound_numerator_parse
    geometryRow109_jensenBound_denominator_parse geometryRow109_jensenBound_denominator_nonzero

theorem geometryRow109_jensenBound_read :
    rationalField geometryRowsJson109 "jensen_bound" = .ok geometryRowsTyped109.jensenBound :=
  original_rationalField_of_string geometryRowsJson109 "jensen_bound" geometryRow109_jensenBoundText
    geometryRowsTyped109.jensenBound geometryRow109_jensenBound_field geometryRow109_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_factorMaxima_before"
  err.flush

theorem geometryRow109_factorMaxima_read :
    rationalArrayField geometryRowsJson109 "factor_maxima" = .ok geometryRowsTyped109.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_gapWeightedMeans_before"
  err.flush

theorem geometryRow109_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson109 "gap_weighted_means" = .ok geometryRowsTyped109.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow109_floorChars : List Char := ['1', '0', '2', '4', '6', '9', '9', '0', '4', '7', '4', '9', '8', '0']
noncomputable def geometryRow109_floorText : String := String.ofList geometryRow109_floorChars

theorem geometryRow109_floor_text_read :
    geometryRowsJson109.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow109_floorText := by rfl

theorem geometryRow109_floor_chars_parse :
    SourceJson.intChars geometryRow109_floorChars = some (10246990474980 : Int) := by decide +kernel

theorem geometryRow109_floor_parse :
    parseInteger geometryRow109_floorText = .ok geometryRowsTyped109.jensenFloorQ96 := by
  simp only [geometryRow109_floorText, parseInteger, String.toList_ofList, geometryRow109_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_109 :
    decodeGeometryRow geometryRowsJson109 = .ok geometryRowsTyped109 :=
  original_geometryRow_of_fields geometryRowsJson109 geometryRowsTyped109 geometryRow109_floorText
    geometryRow109_simplexId_read geometryRow109_vertexIds_read
    geometryRow109_physicalVolume_read geometryRow109_meanGap_read
    geometryRow109_factorMaxima_read geometryRow109_gapWeightedMeans_read
    geometryRow109_jensenBound_read geometryRow109_floor_text_read geometryRow109_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_109_original_decoder_complete"
  err.flush

theorem geometryRow109_shape :
    geometryRowsTyped109.simplexId = 109 ∧
    geometryRowsTyped109.vertexIds.size = 9 ∧ geometryRowsTyped109.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped109.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped109.factorMaxima.size = 10 ∧ geometryRowsTyped109.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson110 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped110 : GeometryRow :=
  { simplexId := 110,
    vertexIds := #[32, 31, 30, 28, 16, 14, 12, 11, 7],
    physicalVolume := ((8030132977358847837405224879150772841 : ℚ) / (180040905031680000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7672302106543 : ℚ) / (85433040000000 : ℚ)), ((1555694686901 : ℚ) / (17086608000000 : ℚ)), ((20362115318647 : ℚ) / (170866080000000 : ℚ)), ((5121401151379 : ℚ) / (56955360000000 : ℚ)), ((1018090156663 : ℚ) / (11391072000000 : ℚ)), ((12515414433161 : ℚ) / (170866080000000 : ℚ)), ((1562738401909 : ℚ) / (42716520000000 : ℚ)), ((369829518199 : ℚ) / (10679130000000 : ℚ)), ((542295029959 : ℚ) / (17086608000000 : ℚ)), ((2711469454259 : ℚ) / (85433040000000 : ℚ))],
    jensenBound := ((20070031882824803299325064998534124390734648839669483984555280294518441564359495779434310664192000000000000 : ℚ) / (119273229442011118246129975302820789593068671774622392830788558276228777013976568047918648332759076146917563381792615375879 : ℚ)),
    jensenFloorQ96 := (13331673461998 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_simplexId_before"
  err.flush

theorem geometryRow110_simplexId_read :
    geometryRowsJson110.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped110.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_vertexIds_before"
  err.flush

theorem geometryRow110_vertexIds_read :
    geometryRowsJson110.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped110.vertexIds := by decide +kernel

noncomputable def geometryRow110_physicalVolumeNumeratorChars : List Char := ['8', '0', '3', '0', '1', '3', '2', '9', '7', '7', '3', '5', '8', '8', '4', '7', '8', '3', '7', '4', '0', '5', '2', '2', '4', '8', '7', '9', '1', '5', '0', '7', '7', '2', '8', '4', '1']
noncomputable def geometryRow110_physicalVolumeDenominatorChars : List Char := ['1', '8', '0', '0', '4', '0', '9', '0', '5', '0', '3', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow110_physicalVolumeText : String := String.ofList (geometryRow110_physicalVolumeNumeratorChars ++ '/' :: geometryRow110_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_physicalVolume_before_field"
  err.flush

theorem geometryRow110_physicalVolume_field :
    geometryRowsJson110.getObjVal? "physical_volume" = .ok (.str geometryRow110_physicalVolumeText) := by rfl

theorem geometryRow110_physicalVolume_numerator_no_slash :
    geometryRow110_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow110_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow110_physicalVolumeNumeratorChars = some (8030132977358847837405224879150772841 : Int) := by decide +kernel

theorem geometryRow110_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow110_physicalVolumeDenominatorChars = some (180040905031680000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow110_physicalVolume_denominator_nonzero : (180040905031680000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow110_physicalVolume_parse :
    parseRational geometryRow110_physicalVolumeText = .ok geometryRowsTyped110.physicalVolume :=
  original_rational_fraction_of_chars geometryRow110_physicalVolumeNumeratorChars geometryRow110_physicalVolumeDenominatorChars
    (8030132977358847837405224879150772841 : Int) (180040905031680000000000000000000000000000000000000000000000000 : Int)
    geometryRow110_physicalVolume_numerator_no_slash geometryRow110_physicalVolume_numerator_parse
    geometryRow110_physicalVolume_denominator_parse geometryRow110_physicalVolume_denominator_nonzero

theorem geometryRow110_physicalVolume_read :
    rationalField geometryRowsJson110 "physical_volume" = .ok geometryRowsTyped110.physicalVolume :=
  original_rationalField_of_string geometryRowsJson110 "physical_volume" geometryRow110_physicalVolumeText
    geometryRowsTyped110.physicalVolume geometryRow110_physicalVolume_field geometryRow110_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_physicalVolume_complete"
  err.flush

noncomputable def geometryRow110_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow110_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow110_meanGapText : String := String.ofList (geometryRow110_meanGapNumeratorChars ++ '/' :: geometryRow110_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_meanGap_before_field"
  err.flush

theorem geometryRow110_meanGap_field :
    geometryRowsJson110.getObjVal? "mean_gap" = .ok (.str geometryRow110_meanGapText) := by rfl

theorem geometryRow110_meanGap_numerator_no_slash :
    geometryRow110_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow110_meanGap_numerator_parse :
    SourceJson.intChars geometryRow110_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow110_meanGap_denominator_parse :
    SourceJson.intChars geometryRow110_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow110_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow110_meanGap_parse :
    parseRational geometryRow110_meanGapText = .ok geometryRowsTyped110.meanGap :=
  original_rational_fraction_of_chars geometryRow110_meanGapNumeratorChars geometryRow110_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow110_meanGap_numerator_no_slash geometryRow110_meanGap_numerator_parse
    geometryRow110_meanGap_denominator_parse geometryRow110_meanGap_denominator_nonzero

theorem geometryRow110_meanGap_read :
    rationalField geometryRowsJson110 "mean_gap" = .ok geometryRowsTyped110.meanGap :=
  original_rationalField_of_string geometryRowsJson110 "mean_gap" geometryRow110_meanGapText
    geometryRowsTyped110.meanGap geometryRow110_meanGap_field geometryRow110_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_meanGap_complete"
  err.flush

noncomputable def geometryRow110_jensenBoundNumeratorChars : List Char := ['2', '0', '0', '7', '0', '0', '3', '1', '8', '8', '2', '8', '2', '4', '8', '0', '3', '2', '9', '9', '3', '2', '5', '0', '6', '4', '9', '9', '8', '5', '3', '4', '1', '2', '4', '3', '9', '0', '7', '3', '4', '6', '4', '8', '8', '3', '9', '6', '6', '9', '4', '8', '3', '9', '8', '4', '5', '5', '5', '2', '8', '0', '2', '9', '4', '5', '1', '8', '4', '4', '1', '5', '6', '4', '3', '5', '9', '4', '9', '5', '7', '7', '9', '4', '3', '4', '3', '1', '0', '6', '6', '4', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow110_jensenBoundDenominatorChars : List Char := ['1', '1', '9', '2', '7', '3', '2', '2', '9', '4', '4', '2', '0', '1', '1', '1', '1', '8', '2', '4', '6', '1', '2', '9', '9', '7', '5', '3', '0', '2', '8', '2', '0', '7', '8', '9', '5', '9', '3', '0', '6', '8', '6', '7', '1', '7', '7', '4', '6', '2', '2', '3', '9', '2', '8', '3', '0', '7', '8', '8', '5', '5', '8', '2', '7', '6', '2', '2', '8', '7', '7', '7', '0', '1', '3', '9', '7', '6', '5', '6', '8', '0', '4', '7', '9', '1', '8', '6', '4', '8', '3', '3', '2', '7', '5', '9', '0', '7', '6', '1', '4', '6', '9', '1', '7', '5', '6', '3', '3', '8', '1', '7', '9', '2', '6', '1', '5', '3', '7', '5', '8', '7', '9']
noncomputable def geometryRow110_jensenBoundText : String := String.ofList (geometryRow110_jensenBoundNumeratorChars ++ '/' :: geometryRow110_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_jensenBound_before_field"
  err.flush

theorem geometryRow110_jensenBound_field :
    geometryRowsJson110.getObjVal? "jensen_bound" = .ok (.str geometryRow110_jensenBoundText) := by rfl

theorem geometryRow110_jensenBound_numerator_no_slash :
    geometryRow110_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow110_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow110_jensenBoundNumeratorChars = some (20070031882824803299325064998534124390734648839669483984555280294518441564359495779434310664192000000000000 : Int) := by decide +kernel

theorem geometryRow110_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow110_jensenBoundDenominatorChars = some (119273229442011118246129975302820789593068671774622392830788558276228777013976568047918648332759076146917563381792615375879 : Int) := by decide +kernel

theorem geometryRow110_jensenBound_denominator_nonzero : (119273229442011118246129975302820789593068671774622392830788558276228777013976568047918648332759076146917563381792615375879 : Int) ≠ 0 := by decide +kernel

theorem geometryRow110_jensenBound_parse :
    parseRational geometryRow110_jensenBoundText = .ok geometryRowsTyped110.jensenBound :=
  original_rational_fraction_of_chars geometryRow110_jensenBoundNumeratorChars geometryRow110_jensenBoundDenominatorChars
    (20070031882824803299325064998534124390734648839669483984555280294518441564359495779434310664192000000000000 : Int) (119273229442011118246129975302820789593068671774622392830788558276228777013976568047918648332759076146917563381792615375879 : Int)
    geometryRow110_jensenBound_numerator_no_slash geometryRow110_jensenBound_numerator_parse
    geometryRow110_jensenBound_denominator_parse geometryRow110_jensenBound_denominator_nonzero

theorem geometryRow110_jensenBound_read :
    rationalField geometryRowsJson110 "jensen_bound" = .ok geometryRowsTyped110.jensenBound :=
  original_rationalField_of_string geometryRowsJson110 "jensen_bound" geometryRow110_jensenBoundText
    geometryRowsTyped110.jensenBound geometryRow110_jensenBound_field geometryRow110_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_factorMaxima_before"
  err.flush

theorem geometryRow110_factorMaxima_read :
    rationalArrayField geometryRowsJson110 "factor_maxima" = .ok geometryRowsTyped110.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_gapWeightedMeans_before"
  err.flush

theorem geometryRow110_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson110 "gap_weighted_means" = .ok geometryRowsTyped110.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow110_floorChars : List Char := ['1', '3', '3', '3', '1', '6', '7', '3', '4', '6', '1', '9', '9', '8']
noncomputable def geometryRow110_floorText : String := String.ofList geometryRow110_floorChars

theorem geometryRow110_floor_text_read :
    geometryRowsJson110.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow110_floorText := by rfl

theorem geometryRow110_floor_chars_parse :
    SourceJson.intChars geometryRow110_floorChars = some (13331673461998 : Int) := by decide +kernel

theorem geometryRow110_floor_parse :
    parseInteger geometryRow110_floorText = .ok geometryRowsTyped110.jensenFloorQ96 := by
  simp only [geometryRow110_floorText, parseInteger, String.toList_ofList, geometryRow110_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_110 :
    decodeGeometryRow geometryRowsJson110 = .ok geometryRowsTyped110 :=
  original_geometryRow_of_fields geometryRowsJson110 geometryRowsTyped110 geometryRow110_floorText
    geometryRow110_simplexId_read geometryRow110_vertexIds_read
    geometryRow110_physicalVolume_read geometryRow110_meanGap_read
    geometryRow110_factorMaxima_read geometryRow110_gapWeightedMeans_read
    geometryRow110_jensenBound_read geometryRow110_floor_text_read geometryRow110_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_110_original_decoder_complete"
  err.flush

theorem geometryRow110_shape :
    geometryRowsTyped110.simplexId = 110 ∧
    geometryRowsTyped110.vertexIds.size = 9 ∧ geometryRowsTyped110.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped110.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped110.factorMaxima.size = 10 ∧ geometryRowsTyped110.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson111 : SourceJson :=
  (SimplicesBlock013.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped111 : GeometryRow :=
  { simplexId := 111,
    vertexIds := #[32, 31, 30, 19, 16, 14, 12, 11, 7],
    physicalVolume := ((145828960916826615967844039409256543933 : ℚ) / (2743480457625600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((77402268807229 : ℚ) / (854330400000000 : ℚ)), ((78463982086849 : ℚ) / (854330400000000 : ℚ)), ((100952565656507 : ℚ) / (854330400000000 : ℚ)), ((1051897089167 : ℚ) / (11865700000000 : ℚ)), ((24896130865091 : ℚ) / (284776800000000 : ℚ)), ((63435083102533 : ℚ) / (854330400000000 : ℚ)), ((143147885071 : ℚ) / (3813975000000 : ℚ)), ((7599179918411 : ℚ) / (213582600000000 : ℚ)), ((27341167411883 : ℚ) / (854330400000000 : ℚ)), ((27341110456523 : ℚ) / (854330400000000 : ℚ))],
    jensenBound := ((157111374490461311225471731481331682737763562019615139521571667301289520793751214372720176917000000000000000000000000 : ℚ) / (828248938165275340534959574476757785693265924200528475385503599824285297961860175023460171757603690555026331831473037737089572215763 : ℚ)),
    jensenFloorQ96 := (15028869869176 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_simplexId_before"
  err.flush

theorem geometryRow111_simplexId_read :
    geometryRowsJson111.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped111.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_vertexIds_before"
  err.flush

theorem geometryRow111_vertexIds_read :
    geometryRowsJson111.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped111.vertexIds := by decide +kernel

noncomputable def geometryRow111_physicalVolumeNumeratorChars : List Char := ['1', '4', '5', '8', '2', '8', '9', '6', '0', '9', '1', '6', '8', '2', '6', '6', '1', '5', '9', '6', '7', '8', '4', '4', '0', '3', '9', '4', '0', '9', '2', '5', '6', '5', '4', '3', '9', '3', '3']
noncomputable def geometryRow111_physicalVolumeDenominatorChars : List Char := ['2', '7', '4', '3', '4', '8', '0', '4', '5', '7', '6', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow111_physicalVolumeText : String := String.ofList (geometryRow111_physicalVolumeNumeratorChars ++ '/' :: geometryRow111_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_physicalVolume_before_field"
  err.flush

theorem geometryRow111_physicalVolume_field :
    geometryRowsJson111.getObjVal? "physical_volume" = .ok (.str geometryRow111_physicalVolumeText) := by rfl

theorem geometryRow111_physicalVolume_numerator_no_slash :
    geometryRow111_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow111_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow111_physicalVolumeNumeratorChars = some (145828960916826615967844039409256543933 : Int) := by decide +kernel

theorem geometryRow111_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow111_physicalVolumeDenominatorChars = some (2743480457625600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow111_physicalVolume_denominator_nonzero : (2743480457625600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow111_physicalVolume_parse :
    parseRational geometryRow111_physicalVolumeText = .ok geometryRowsTyped111.physicalVolume :=
  original_rational_fraction_of_chars geometryRow111_physicalVolumeNumeratorChars geometryRow111_physicalVolumeDenominatorChars
    (145828960916826615967844039409256543933 : Int) (2743480457625600000000000000000000000000000000000000000000000000 : Int)
    geometryRow111_physicalVolume_numerator_no_slash geometryRow111_physicalVolume_numerator_parse
    geometryRow111_physicalVolume_denominator_parse geometryRow111_physicalVolume_denominator_nonzero

theorem geometryRow111_physicalVolume_read :
    rationalField geometryRowsJson111 "physical_volume" = .ok geometryRowsTyped111.physicalVolume :=
  original_rationalField_of_string geometryRowsJson111 "physical_volume" geometryRow111_physicalVolumeText
    geometryRowsTyped111.physicalVolume geometryRow111_physicalVolume_field geometryRow111_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_physicalVolume_complete"
  err.flush

noncomputable def geometryRow111_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow111_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow111_meanGapText : String := String.ofList (geometryRow111_meanGapNumeratorChars ++ '/' :: geometryRow111_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_meanGap_before_field"
  err.flush

theorem geometryRow111_meanGap_field :
    geometryRowsJson111.getObjVal? "mean_gap" = .ok (.str geometryRow111_meanGapText) := by rfl

theorem geometryRow111_meanGap_numerator_no_slash :
    geometryRow111_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow111_meanGap_numerator_parse :
    SourceJson.intChars geometryRow111_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow111_meanGap_denominator_parse :
    SourceJson.intChars geometryRow111_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow111_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow111_meanGap_parse :
    parseRational geometryRow111_meanGapText = .ok geometryRowsTyped111.meanGap :=
  original_rational_fraction_of_chars geometryRow111_meanGapNumeratorChars geometryRow111_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow111_meanGap_numerator_no_slash geometryRow111_meanGap_numerator_parse
    geometryRow111_meanGap_denominator_parse geometryRow111_meanGap_denominator_nonzero

theorem geometryRow111_meanGap_read :
    rationalField geometryRowsJson111 "mean_gap" = .ok geometryRowsTyped111.meanGap :=
  original_rationalField_of_string geometryRowsJson111 "mean_gap" geometryRow111_meanGapText
    geometryRowsTyped111.meanGap geometryRow111_meanGap_field geometryRow111_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_meanGap_complete"
  err.flush

noncomputable def geometryRow111_jensenBoundNumeratorChars : List Char := ['1', '5', '7', '1', '1', '1', '3', '7', '4', '4', '9', '0', '4', '6', '1', '3', '1', '1', '2', '2', '5', '4', '7', '1', '7', '3', '1', '4', '8', '1', '3', '3', '1', '6', '8', '2', '7', '3', '7', '7', '6', '3', '5', '6', '2', '0', '1', '9', '6', '1', '5', '1', '3', '9', '5', '2', '1', '5', '7', '1', '6', '6', '7', '3', '0', '1', '2', '8', '9', '5', '2', '0', '7', '9', '3', '7', '5', '1', '2', '1', '4', '3', '7', '2', '7', '2', '0', '1', '7', '6', '9', '1', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow111_jensenBoundDenominatorChars : List Char := ['8', '2', '8', '2', '4', '8', '9', '3', '8', '1', '6', '5', '2', '7', '5', '3', '4', '0', '5', '3', '4', '9', '5', '9', '5', '7', '4', '4', '7', '6', '7', '5', '7', '7', '8', '5', '6', '9', '3', '2', '6', '5', '9', '2', '4', '2', '0', '0', '5', '2', '8', '4', '7', '5', '3', '8', '5', '5', '0', '3', '5', '9', '9', '8', '2', '4', '2', '8', '5', '2', '9', '7', '9', '6', '1', '8', '6', '0', '1', '7', '5', '0', '2', '3', '4', '6', '0', '1', '7', '1', '7', '5', '7', '6', '0', '3', '6', '9', '0', '5', '5', '5', '0', '2', '6', '3', '3', '1', '8', '3', '1', '4', '7', '3', '0', '3', '7', '7', '3', '7', '0', '8', '9', '5', '7', '2', '2', '1', '5', '7', '6', '3']
noncomputable def geometryRow111_jensenBoundText : String := String.ofList (geometryRow111_jensenBoundNumeratorChars ++ '/' :: geometryRow111_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_jensenBound_before_field"
  err.flush

theorem geometryRow111_jensenBound_field :
    geometryRowsJson111.getObjVal? "jensen_bound" = .ok (.str geometryRow111_jensenBoundText) := by rfl

theorem geometryRow111_jensenBound_numerator_no_slash :
    geometryRow111_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow111_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow111_jensenBoundNumeratorChars = some (157111374490461311225471731481331682737763562019615139521571667301289520793751214372720176917000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow111_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow111_jensenBoundDenominatorChars = some (828248938165275340534959574476757785693265924200528475385503599824285297961860175023460171757603690555026331831473037737089572215763 : Int) := by decide +kernel

theorem geometryRow111_jensenBound_denominator_nonzero : (828248938165275340534959574476757785693265924200528475385503599824285297961860175023460171757603690555026331831473037737089572215763 : Int) ≠ 0 := by decide +kernel

theorem geometryRow111_jensenBound_parse :
    parseRational geometryRow111_jensenBoundText = .ok geometryRowsTyped111.jensenBound :=
  original_rational_fraction_of_chars geometryRow111_jensenBoundNumeratorChars geometryRow111_jensenBoundDenominatorChars
    (157111374490461311225471731481331682737763562019615139521571667301289520793751214372720176917000000000000000000000000 : Int) (828248938165275340534959574476757785693265924200528475385503599824285297961860175023460171757603690555026331831473037737089572215763 : Int)
    geometryRow111_jensenBound_numerator_no_slash geometryRow111_jensenBound_numerator_parse
    geometryRow111_jensenBound_denominator_parse geometryRow111_jensenBound_denominator_nonzero

theorem geometryRow111_jensenBound_read :
    rationalField geometryRowsJson111 "jensen_bound" = .ok geometryRowsTyped111.jensenBound :=
  original_rationalField_of_string geometryRowsJson111 "jensen_bound" geometryRow111_jensenBoundText
    geometryRowsTyped111.jensenBound geometryRow111_jensenBound_field geometryRow111_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_factorMaxima_before"
  err.flush

theorem geometryRow111_factorMaxima_read :
    rationalArrayField geometryRowsJson111 "factor_maxima" = .ok geometryRowsTyped111.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_gapWeightedMeans_before"
  err.flush

theorem geometryRow111_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson111 "gap_weighted_means" = .ok geometryRowsTyped111.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow111_floorChars : List Char := ['1', '5', '0', '2', '8', '8', '6', '9', '8', '6', '9', '1', '7', '6']
noncomputable def geometryRow111_floorText : String := String.ofList geometryRow111_floorChars

theorem geometryRow111_floor_text_read :
    geometryRowsJson111.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow111_floorText := by rfl

theorem geometryRow111_floor_chars_parse :
    SourceJson.intChars geometryRow111_floorChars = some (15028869869176 : Int) := by decide +kernel

theorem geometryRow111_floor_parse :
    parseInteger geometryRow111_floorText = .ok geometryRowsTyped111.jensenFloorQ96 := by
  simp only [geometryRow111_floorText, parseInteger, String.toList_ofList, geometryRow111_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_111 :
    decodeGeometryRow geometryRowsJson111 = .ok geometryRowsTyped111 :=
  original_geometryRow_of_fields geometryRowsJson111 geometryRowsTyped111 geometryRow111_floorText
    geometryRow111_simplexId_read geometryRow111_vertexIds_read
    geometryRow111_physicalVolume_read geometryRow111_meanGap_read
    geometryRow111_factorMaxima_read geometryRow111_gapWeightedMeans_read
    geometryRow111_jensenBound_read geometryRow111_floor_text_read geometryRow111_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_111_original_decoder_complete"
  err.flush

theorem geometryRow111_shape :
    geometryRowsTyped111.simplexId = 111 ∧
    geometryRowsTyped111.vertexIds.size = 9 ∧ geometryRowsTyped111.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped111.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped111.factorMaxima.size = 10 ∧ geometryRowsTyped111.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock013 : List SourceJson := [geometryRowsJson104, geometryRowsJson105, geometryRowsJson106, geometryRowsJson107, geometryRowsJson108, geometryRowsJson109, geometryRowsJson110, geometryRowsJson111]
noncomputable def geometryRowsTypedBlock013 : List GeometryRow := [geometryRowsTyped104, geometryRowsTyped105, geometryRowsTyped106, geometryRowsTyped107, geometryRowsTyped108, geometryRowsTyped109, geometryRowsTyped110, geometryRowsTyped111]

theorem geometry_Rows_block_013_push_eq (acc : List SourceJson) :
    SimplicesBlock013.blockPush acc = [geometryRowsJson111, geometryRowsJson110, geometryRowsJson109, geometryRowsJson108, geometryRowsJson107, geometryRowsJson106, geometryRowsJson105, geometryRowsJson104] ++ acc := by rfl

theorem geometry_Rows_block_013_reverse (acc : List SourceJson) :
    (SimplicesBlock013.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock013 := by
  rw [geometry_Rows_block_013_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_013 :
    geometryRowsJsonBlock013.mapM decodeGeometryRow = .ok geometryRowsTypedBlock013 := by
  simp only [geometryRowsJsonBlock013, geometryRowsTypedBlock013, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_104, decode_geometry_Rows_105, decode_geometry_Rows_106, decode_geometry_Rows_107, decode_geometry_Rows_108, decode_geometry_Rows_109, decode_geometry_Rows_110, decode_geometry_Rows_111]
  rfl

theorem geometry_Rows_block_013_length : geometryRowsTypedBlock013.length = 8 := by rfl

#print axioms geometryRow104_simplexId_read
#print axioms geometryRow104_vertexIds_read
#print axioms geometryRow104_physicalVolume_field
#print axioms geometryRow104_physicalVolume_numerator_no_slash
#print axioms geometryRow104_physicalVolume_numerator_parse
#print axioms geometryRow104_physicalVolume_denominator_parse
#print axioms geometryRow104_physicalVolume_denominator_nonzero
#print axioms geometryRow104_physicalVolume_parse
#print axioms geometryRow104_physicalVolume_read
#print axioms geometryRow104_meanGap_field
#print axioms geometryRow104_meanGap_numerator_no_slash
#print axioms geometryRow104_meanGap_numerator_parse
#print axioms geometryRow104_meanGap_denominator_parse
#print axioms geometryRow104_meanGap_denominator_nonzero
#print axioms geometryRow104_meanGap_parse
#print axioms geometryRow104_meanGap_read
#print axioms geometryRow104_jensenBound_field
#print axioms geometryRow104_jensenBound_numerator_no_slash
#print axioms geometryRow104_jensenBound_numerator_parse
#print axioms geometryRow104_jensenBound_denominator_parse
#print axioms geometryRow104_jensenBound_denominator_nonzero
#print axioms geometryRow104_jensenBound_parse
#print axioms geometryRow104_jensenBound_read
#print axioms geometryRow104_factorMaxima_read
#print axioms geometryRow104_gapWeightedMeans_read
#print axioms geometryRow104_floor_text_read
#print axioms geometryRow104_floor_chars_parse
#print axioms geometryRow104_floor_parse
#print axioms decode_geometry_Rows_104
#print axioms geometryRow104_shape
#print axioms geometryRow105_simplexId_read
#print axioms geometryRow105_vertexIds_read
#print axioms geometryRow105_physicalVolume_field
#print axioms geometryRow105_physicalVolume_numerator_no_slash
#print axioms geometryRow105_physicalVolume_numerator_parse
#print axioms geometryRow105_physicalVolume_denominator_parse
#print axioms geometryRow105_physicalVolume_denominator_nonzero
#print axioms geometryRow105_physicalVolume_parse
#print axioms geometryRow105_physicalVolume_read
#print axioms geometryRow105_meanGap_field
#print axioms geometryRow105_meanGap_numerator_no_slash
#print axioms geometryRow105_meanGap_numerator_parse
#print axioms geometryRow105_meanGap_denominator_parse
#print axioms geometryRow105_meanGap_denominator_nonzero
#print axioms geometryRow105_meanGap_parse
#print axioms geometryRow105_meanGap_read
#print axioms geometryRow105_jensenBound_field
#print axioms geometryRow105_jensenBound_numerator_no_slash
#print axioms geometryRow105_jensenBound_numerator_parse
#print axioms geometryRow105_jensenBound_denominator_parse
#print axioms geometryRow105_jensenBound_denominator_nonzero
#print axioms geometryRow105_jensenBound_parse
#print axioms geometryRow105_jensenBound_read
#print axioms geometryRow105_factorMaxima_read
#print axioms geometryRow105_gapWeightedMeans_read
#print axioms geometryRow105_floor_text_read
#print axioms geometryRow105_floor_chars_parse
#print axioms geometryRow105_floor_parse
#print axioms decode_geometry_Rows_105
#print axioms geometryRow105_shape
#print axioms geometryRow106_simplexId_read
#print axioms geometryRow106_vertexIds_read
#print axioms geometryRow106_physicalVolume_field
#print axioms geometryRow106_physicalVolume_numerator_no_slash
#print axioms geometryRow106_physicalVolume_numerator_parse
#print axioms geometryRow106_physicalVolume_denominator_parse
#print axioms geometryRow106_physicalVolume_denominator_nonzero
#print axioms geometryRow106_physicalVolume_parse
#print axioms geometryRow106_physicalVolume_read
#print axioms geometryRow106_meanGap_field
#print axioms geometryRow106_meanGap_numerator_no_slash
#print axioms geometryRow106_meanGap_numerator_parse
#print axioms geometryRow106_meanGap_denominator_parse
#print axioms geometryRow106_meanGap_denominator_nonzero
#print axioms geometryRow106_meanGap_parse
#print axioms geometryRow106_meanGap_read
#print axioms geometryRow106_jensenBound_field
#print axioms geometryRow106_jensenBound_numerator_no_slash
#print axioms geometryRow106_jensenBound_numerator_parse
#print axioms geometryRow106_jensenBound_denominator_parse
#print axioms geometryRow106_jensenBound_denominator_nonzero
#print axioms geometryRow106_jensenBound_parse
#print axioms geometryRow106_jensenBound_read
#print axioms geometryRow106_factorMaxima_read
#print axioms geometryRow106_gapWeightedMeans_read
#print axioms geometryRow106_floor_text_read
#print axioms geometryRow106_floor_chars_parse
#print axioms geometryRow106_floor_parse
#print axioms decode_geometry_Rows_106
#print axioms geometryRow106_shape
#print axioms geometryRow107_simplexId_read
#print axioms geometryRow107_vertexIds_read
#print axioms geometryRow107_physicalVolume_field
#print axioms geometryRow107_physicalVolume_numerator_no_slash
#print axioms geometryRow107_physicalVolume_numerator_parse
#print axioms geometryRow107_physicalVolume_denominator_parse
#print axioms geometryRow107_physicalVolume_denominator_nonzero
#print axioms geometryRow107_physicalVolume_parse
#print axioms geometryRow107_physicalVolume_read
#print axioms geometryRow107_meanGap_field
#print axioms geometryRow107_meanGap_numerator_no_slash
#print axioms geometryRow107_meanGap_numerator_parse
#print axioms geometryRow107_meanGap_denominator_parse
#print axioms geometryRow107_meanGap_denominator_nonzero
#print axioms geometryRow107_meanGap_parse
#print axioms geometryRow107_meanGap_read
#print axioms geometryRow107_jensenBound_field
#print axioms geometryRow107_jensenBound_numerator_no_slash
#print axioms geometryRow107_jensenBound_numerator_parse
#print axioms geometryRow107_jensenBound_denominator_parse
#print axioms geometryRow107_jensenBound_denominator_nonzero
#print axioms geometryRow107_jensenBound_parse
#print axioms geometryRow107_jensenBound_read
#print axioms geometryRow107_factorMaxima_read
#print axioms geometryRow107_gapWeightedMeans_read
#print axioms geometryRow107_floor_text_read
#print axioms geometryRow107_floor_chars_parse
#print axioms geometryRow107_floor_parse
#print axioms decode_geometry_Rows_107
#print axioms geometryRow107_shape
#print axioms geometryRow108_simplexId_read
#print axioms geometryRow108_vertexIds_read
#print axioms geometryRow108_physicalVolume_field
#print axioms geometryRow108_physicalVolume_numerator_no_slash
#print axioms geometryRow108_physicalVolume_numerator_parse
#print axioms geometryRow108_physicalVolume_denominator_parse
#print axioms geometryRow108_physicalVolume_denominator_nonzero
#print axioms geometryRow108_physicalVolume_parse
#print axioms geometryRow108_physicalVolume_read
#print axioms geometryRow108_meanGap_field
#print axioms geometryRow108_meanGap_numerator_no_slash
#print axioms geometryRow108_meanGap_numerator_parse
#print axioms geometryRow108_meanGap_denominator_parse
#print axioms geometryRow108_meanGap_denominator_nonzero
#print axioms geometryRow108_meanGap_parse
#print axioms geometryRow108_meanGap_read
#print axioms geometryRow108_jensenBound_field
#print axioms geometryRow108_jensenBound_numerator_no_slash
#print axioms geometryRow108_jensenBound_numerator_parse
#print axioms geometryRow108_jensenBound_denominator_parse
#print axioms geometryRow108_jensenBound_denominator_nonzero
#print axioms geometryRow108_jensenBound_parse
#print axioms geometryRow108_jensenBound_read
#print axioms geometryRow108_factorMaxima_read
#print axioms geometryRow108_gapWeightedMeans_read
#print axioms geometryRow108_floor_text_read
#print axioms geometryRow108_floor_chars_parse
#print axioms geometryRow108_floor_parse
#print axioms decode_geometry_Rows_108
#print axioms geometryRow108_shape
#print axioms geometryRow109_simplexId_read
#print axioms geometryRow109_vertexIds_read
#print axioms geometryRow109_physicalVolume_field
#print axioms geometryRow109_physicalVolume_numerator_no_slash
#print axioms geometryRow109_physicalVolume_numerator_parse
#print axioms geometryRow109_physicalVolume_denominator_parse
#print axioms geometryRow109_physicalVolume_denominator_nonzero
#print axioms geometryRow109_physicalVolume_parse
#print axioms geometryRow109_physicalVolume_read
#print axioms geometryRow109_meanGap_field
#print axioms geometryRow109_meanGap_numerator_no_slash
#print axioms geometryRow109_meanGap_numerator_parse
#print axioms geometryRow109_meanGap_denominator_parse
#print axioms geometryRow109_meanGap_denominator_nonzero
#print axioms geometryRow109_meanGap_parse
#print axioms geometryRow109_meanGap_read
#print axioms geometryRow109_jensenBound_field
#print axioms geometryRow109_jensenBound_numerator_no_slash
#print axioms geometryRow109_jensenBound_numerator_parse
#print axioms geometryRow109_jensenBound_denominator_parse
#print axioms geometryRow109_jensenBound_denominator_nonzero
#print axioms geometryRow109_jensenBound_parse
#print axioms geometryRow109_jensenBound_read
#print axioms geometryRow109_factorMaxima_read
#print axioms geometryRow109_gapWeightedMeans_read
#print axioms geometryRow109_floor_text_read
#print axioms geometryRow109_floor_chars_parse
#print axioms geometryRow109_floor_parse
#print axioms decode_geometry_Rows_109
#print axioms geometryRow109_shape
#print axioms geometryRow110_simplexId_read
#print axioms geometryRow110_vertexIds_read
#print axioms geometryRow110_physicalVolume_field
#print axioms geometryRow110_physicalVolume_numerator_no_slash
#print axioms geometryRow110_physicalVolume_numerator_parse
#print axioms geometryRow110_physicalVolume_denominator_parse
#print axioms geometryRow110_physicalVolume_denominator_nonzero
#print axioms geometryRow110_physicalVolume_parse
#print axioms geometryRow110_physicalVolume_read
#print axioms geometryRow110_meanGap_field
#print axioms geometryRow110_meanGap_numerator_no_slash
#print axioms geometryRow110_meanGap_numerator_parse
#print axioms geometryRow110_meanGap_denominator_parse
#print axioms geometryRow110_meanGap_denominator_nonzero
#print axioms geometryRow110_meanGap_parse
#print axioms geometryRow110_meanGap_read
#print axioms geometryRow110_jensenBound_field
#print axioms geometryRow110_jensenBound_numerator_no_slash
#print axioms geometryRow110_jensenBound_numerator_parse
#print axioms geometryRow110_jensenBound_denominator_parse
#print axioms geometryRow110_jensenBound_denominator_nonzero
#print axioms geometryRow110_jensenBound_parse
#print axioms geometryRow110_jensenBound_read
#print axioms geometryRow110_factorMaxima_read
#print axioms geometryRow110_gapWeightedMeans_read
#print axioms geometryRow110_floor_text_read
#print axioms geometryRow110_floor_chars_parse
#print axioms geometryRow110_floor_parse
#print axioms decode_geometry_Rows_110
#print axioms geometryRow110_shape
#print axioms geometryRow111_simplexId_read
#print axioms geometryRow111_vertexIds_read
#print axioms geometryRow111_physicalVolume_field
#print axioms geometryRow111_physicalVolume_numerator_no_slash
#print axioms geometryRow111_physicalVolume_numerator_parse
#print axioms geometryRow111_physicalVolume_denominator_parse
#print axioms geometryRow111_physicalVolume_denominator_nonzero
#print axioms geometryRow111_physicalVolume_parse
#print axioms geometryRow111_physicalVolume_read
#print axioms geometryRow111_meanGap_field
#print axioms geometryRow111_meanGap_numerator_no_slash
#print axioms geometryRow111_meanGap_numerator_parse
#print axioms geometryRow111_meanGap_denominator_parse
#print axioms geometryRow111_meanGap_denominator_nonzero
#print axioms geometryRow111_meanGap_parse
#print axioms geometryRow111_meanGap_read
#print axioms geometryRow111_jensenBound_field
#print axioms geometryRow111_jensenBound_numerator_no_slash
#print axioms geometryRow111_jensenBound_numerator_parse
#print axioms geometryRow111_jensenBound_denominator_parse
#print axioms geometryRow111_jensenBound_denominator_nonzero
#print axioms geometryRow111_jensenBound_parse
#print axioms geometryRow111_jensenBound_read
#print axioms geometryRow111_factorMaxima_read
#print axioms geometryRow111_gapWeightedMeans_read
#print axioms geometryRow111_floor_text_read
#print axioms geometryRow111_floor_chars_parse
#print axioms geometryRow111_floor_parse
#print axioms decode_geometry_Rows_111
#print axioms geometryRow111_shape
#print axioms geometry_Rows_block_013_push_eq
#print axioms geometry_Rows_block_013_reverse
#print axioms decode_geometry_Rows_block_013
#print axioms geometry_Rows_block_013_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
