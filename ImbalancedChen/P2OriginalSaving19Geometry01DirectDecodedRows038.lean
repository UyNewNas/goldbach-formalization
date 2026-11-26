import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows037

/-! Original simplices typed block 38, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson075 : SourceJson :=
  (SimplicesBlock038.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped075 : GeometryRow :=
  { simplexId := 75,
    vertexIds := #[39, 35, 33, 24, 22, 19, 18, 15, 14],
    physicalVolume := ((5209852848299254472727422822009552012341 : ℚ) / (1353528169065676800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((2859163 : ℚ) / (57000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((159940624633 : ℚ) / (2376900000000 : ℚ)), ((80230582439 : ℚ) / (1188450000000 : ℚ)), ((264313387769 : ℚ) / (1782675000000 : ℚ)), ((1183768869037 : ℚ) / (11092200000000 : ℚ)), ((5606089586297 : ℚ) / (99829800000000 : ℚ)), ((330762169069 : ℚ) / (7130700000000 : ℚ)), ((2207161057343 : ℚ) / (49914900000000 : ℚ)), ((2153850980873 : ℚ) / (49914900000000 : ℚ)), ((2153847653213 : ℚ) / (49914900000000 : ℚ)), ((4191554933911 : ℚ) / (99829800000000 : ℚ))],
    jensenBound := ((132103973537434846476846774028723180907564063561215672692805832984481372962784828552246093750000000000 : ℚ) / (45645971465421026246497472471883189485357494577249697415963070694763626537882816301529588889136330636324955709458856253 : ℚ)),
    jensenFloorQ96 := (229294168755 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_simplexId_before"
  err.flush

theorem geometryRow075_simplexId_read :
    geometryRowsJson075.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped075.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_vertexIds_before"
  err.flush

theorem geometryRow075_vertexIds_read :
    geometryRowsJson075.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped075.vertexIds := by decide +kernel

noncomputable def geometryRow075_physicalVolumeNumeratorChars : List Char := ['5', '2', '0', '9', '8', '5', '2', '8', '4', '8', '2', '9', '9', '2', '5', '4', '4', '7', '2', '7', '2', '7', '4', '2', '2', '8', '2', '2', '0', '0', '9', '5', '5', '2', '0', '1', '2', '3', '4', '1']
noncomputable def geometryRow075_physicalVolumeDenominatorChars : List Char := ['1', '3', '5', '3', '5', '2', '8', '1', '6', '9', '0', '6', '5', '6', '7', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow075_physicalVolumeText : String := String.ofList (geometryRow075_physicalVolumeNumeratorChars ++ '/' :: geometryRow075_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_physicalVolume_before_field"
  err.flush

theorem geometryRow075_physicalVolume_field :
    geometryRowsJson075.getObjVal? "physical_volume" = .ok (.str geometryRow075_physicalVolumeText) := by rfl

theorem geometryRow075_physicalVolume_numerator_no_slash :
    geometryRow075_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow075_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow075_physicalVolumeNumeratorChars = some (5209852848299254472727422822009552012341 : Int) := by decide +kernel

theorem geometryRow075_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow075_physicalVolumeDenominatorChars = some (1353528169065676800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow075_physicalVolume_denominator_nonzero : (1353528169065676800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow075_physicalVolume_parse :
    parseRational geometryRow075_physicalVolumeText = .ok geometryRowsTyped075.physicalVolume :=
  original_rational_fraction_of_chars geometryRow075_physicalVolumeNumeratorChars geometryRow075_physicalVolumeDenominatorChars
    (5209852848299254472727422822009552012341 : Int) (1353528169065676800000000000000000000000000000000000000000000000000 : Int)
    geometryRow075_physicalVolume_numerator_no_slash geometryRow075_physicalVolume_numerator_parse
    geometryRow075_physicalVolume_denominator_parse geometryRow075_physicalVolume_denominator_nonzero

theorem geometryRow075_physicalVolume_read :
    rationalField geometryRowsJson075 "physical_volume" = .ok geometryRowsTyped075.physicalVolume :=
  original_rationalField_of_string geometryRowsJson075 "physical_volume" geometryRow075_physicalVolumeText
    geometryRowsTyped075.physicalVolume geometryRow075_physicalVolume_field geometryRow075_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_physicalVolume_complete"
  err.flush

noncomputable def geometryRow075_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow075_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow075_meanGapText : String := String.ofList (geometryRow075_meanGapNumeratorChars ++ '/' :: geometryRow075_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_meanGap_before_field"
  err.flush

theorem geometryRow075_meanGap_field :
    geometryRowsJson075.getObjVal? "mean_gap" = .ok (.str geometryRow075_meanGapText) := by rfl

theorem geometryRow075_meanGap_numerator_no_slash :
    geometryRow075_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow075_meanGap_numerator_parse :
    SourceJson.intChars geometryRow075_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow075_meanGap_denominator_parse :
    SourceJson.intChars geometryRow075_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow075_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow075_meanGap_parse :
    parseRational geometryRow075_meanGapText = .ok geometryRowsTyped075.meanGap :=
  original_rational_fraction_of_chars geometryRow075_meanGapNumeratorChars geometryRow075_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow075_meanGap_numerator_no_slash geometryRow075_meanGap_numerator_parse
    geometryRow075_meanGap_denominator_parse geometryRow075_meanGap_denominator_nonzero

theorem geometryRow075_meanGap_read :
    rationalField geometryRowsJson075 "mean_gap" = .ok geometryRowsTyped075.meanGap :=
  original_rationalField_of_string geometryRowsJson075 "mean_gap" geometryRow075_meanGapText
    geometryRowsTyped075.meanGap geometryRow075_meanGap_field geometryRow075_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_meanGap_complete"
  err.flush

noncomputable def geometryRow075_jensenBoundNumeratorChars : List Char := ['1', '3', '2', '1', '0', '3', '9', '7', '3', '5', '3', '7', '4', '3', '4', '8', '4', '6', '4', '7', '6', '8', '4', '6', '7', '7', '4', '0', '2', '8', '7', '2', '3', '1', '8', '0', '9', '0', '7', '5', '6', '4', '0', '6', '3', '5', '6', '1', '2', '1', '5', '6', '7', '2', '6', '9', '2', '8', '0', '5', '8', '3', '2', '9', '8', '4', '4', '8', '1', '3', '7', '2', '9', '6', '2', '7', '8', '4', '8', '2', '8', '5', '5', '2', '2', '4', '6', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow075_jensenBoundDenominatorChars : List Char := ['4', '5', '6', '4', '5', '9', '7', '1', '4', '6', '5', '4', '2', '1', '0', '2', '6', '2', '4', '6', '4', '9', '7', '4', '7', '2', '4', '7', '1', '8', '8', '3', '1', '8', '9', '4', '8', '5', '3', '5', '7', '4', '9', '4', '5', '7', '7', '2', '4', '9', '6', '9', '7', '4', '1', '5', '9', '6', '3', '0', '7', '0', '6', '9', '4', '7', '6', '3', '6', '2', '6', '5', '3', '7', '8', '8', '2', '8', '1', '6', '3', '0', '1', '5', '2', '9', '5', '8', '8', '8', '8', '9', '1', '3', '6', '3', '3', '0', '6', '3', '6', '3', '2', '4', '9', '5', '5', '7', '0', '9', '4', '5', '8', '8', '5', '6', '2', '5', '3']
noncomputable def geometryRow075_jensenBoundText : String := String.ofList (geometryRow075_jensenBoundNumeratorChars ++ '/' :: geometryRow075_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_jensenBound_before_field"
  err.flush

theorem geometryRow075_jensenBound_field :
    geometryRowsJson075.getObjVal? "jensen_bound" = .ok (.str geometryRow075_jensenBoundText) := by rfl

theorem geometryRow075_jensenBound_numerator_no_slash :
    geometryRow075_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow075_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow075_jensenBoundNumeratorChars = some (132103973537434846476846774028723180907564063561215672692805832984481372962784828552246093750000000000 : Int) := by decide +kernel

theorem geometryRow075_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow075_jensenBoundDenominatorChars = some (45645971465421026246497472471883189485357494577249697415963070694763626537882816301529588889136330636324955709458856253 : Int) := by decide +kernel

theorem geometryRow075_jensenBound_denominator_nonzero : (45645971465421026246497472471883189485357494577249697415963070694763626537882816301529588889136330636324955709458856253 : Int) ≠ 0 := by decide +kernel

theorem geometryRow075_jensenBound_parse :
    parseRational geometryRow075_jensenBoundText = .ok geometryRowsTyped075.jensenBound :=
  original_rational_fraction_of_chars geometryRow075_jensenBoundNumeratorChars geometryRow075_jensenBoundDenominatorChars
    (132103973537434846476846774028723180907564063561215672692805832984481372962784828552246093750000000000 : Int) (45645971465421026246497472471883189485357494577249697415963070694763626537882816301529588889136330636324955709458856253 : Int)
    geometryRow075_jensenBound_numerator_no_slash geometryRow075_jensenBound_numerator_parse
    geometryRow075_jensenBound_denominator_parse geometryRow075_jensenBound_denominator_nonzero

theorem geometryRow075_jensenBound_read :
    rationalField geometryRowsJson075 "jensen_bound" = .ok geometryRowsTyped075.jensenBound :=
  original_rationalField_of_string geometryRowsJson075 "jensen_bound" geometryRow075_jensenBoundText
    geometryRowsTyped075.jensenBound geometryRow075_jensenBound_field geometryRow075_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_factorMaxima_before"
  err.flush

theorem geometryRow075_factorMaxima_read :
    rationalArrayField geometryRowsJson075 "factor_maxima" = .ok geometryRowsTyped075.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_gapWeightedMeans_before"
  err.flush

theorem geometryRow075_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson075 "gap_weighted_means" = .ok geometryRowsTyped075.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow075_floorChars : List Char := ['2', '2', '9', '2', '9', '4', '1', '6', '8', '7', '5', '5']
noncomputable def geometryRow075_floorText : String := String.ofList geometryRow075_floorChars

theorem geometryRow075_floor_text_read :
    geometryRowsJson075.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow075_floorText := by rfl

theorem geometryRow075_floor_chars_parse :
    SourceJson.intChars geometryRow075_floorChars = some (229294168755 : Int) := by decide +kernel

theorem geometryRow075_floor_parse :
    parseInteger geometryRow075_floorText = .ok geometryRowsTyped075.jensenFloorQ96 := by
  simp only [geometryRow075_floorText, parseInteger, String.toList_ofList, geometryRow075_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_075 :
    decodeGeometryRow geometryRowsJson075 = .ok geometryRowsTyped075 :=
  original_geometryRow_of_fields geometryRowsJson075 geometryRowsTyped075 geometryRow075_floorText
    geometryRow075_simplexId_read geometryRow075_vertexIds_read
    geometryRow075_physicalVolume_read geometryRow075_meanGap_read
    geometryRow075_factorMaxima_read geometryRow075_gapWeightedMeans_read
    geometryRow075_jensenBound_read geometryRow075_floor_text_read geometryRow075_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_075_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson076 : SourceJson :=
  (SimplicesBlock038.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped076 : GeometryRow :=
  { simplexId := 76,
    vertexIds := #[39, 35, 33, 32, 24, 23, 21, 20, 16],
    physicalVolume := ((5205746634712212214521042728864316841237 : ℚ) / (7283644249448448000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((120044974598761 : ℚ) / (1834043400000000 : ℚ)), ((120387436071331 : ℚ) / (1834043400000000 : ℚ)), ((410746250094151 : ℚ) / (2751065100000000 : ℚ)), ((13055882266673 : ℚ) / (122269560000000 : ℚ)), ((62831696338451 : ℚ) / (1100426040000000 : ℚ)), ((12518196004193 : ℚ) / (275106510000000 : ℚ)), ((796346214359 : ℚ) / (18099112500000 : ℚ)), ((119575645108123 : ℚ) / (2751065100000000 : ℚ)), ((236044671709877 : ℚ) / (5502130200000000 : ℚ)), ((236043571283837 : ℚ) / (5502130200000000 : ℚ))],
    jensenBound := ((153124235046201722034486902954447539687249315397151666299305990289311351645866019124491817352903325735546875000000000000 : ℚ) / (323412308667115612617950359066513905269283330340745183770606418491729640228237979661673243763857649604719191499208951337014763593024167307 : ℚ)),
    jensenFloorQ96 := (37511719418 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_simplexId_before"
  err.flush

theorem geometryRow076_simplexId_read :
    geometryRowsJson076.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped076.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_vertexIds_before"
  err.flush

theorem geometryRow076_vertexIds_read :
    geometryRowsJson076.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped076.vertexIds := by decide +kernel

noncomputable def geometryRow076_physicalVolumeNumeratorChars : List Char := ['5', '2', '0', '5', '7', '4', '6', '6', '3', '4', '7', '1', '2', '2', '1', '2', '2', '1', '4', '5', '2', '1', '0', '4', '2', '7', '2', '8', '8', '6', '4', '3', '1', '6', '8', '4', '1', '2', '3', '7']
noncomputable def geometryRow076_physicalVolumeDenominatorChars : List Char := ['7', '2', '8', '3', '6', '4', '4', '2', '4', '9', '4', '4', '8', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow076_physicalVolumeText : String := String.ofList (geometryRow076_physicalVolumeNumeratorChars ++ '/' :: geometryRow076_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_physicalVolume_before_field"
  err.flush

theorem geometryRow076_physicalVolume_field :
    geometryRowsJson076.getObjVal? "physical_volume" = .ok (.str geometryRow076_physicalVolumeText) := by rfl

theorem geometryRow076_physicalVolume_numerator_no_slash :
    geometryRow076_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow076_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow076_physicalVolumeNumeratorChars = some (5205746634712212214521042728864316841237 : Int) := by decide +kernel

theorem geometryRow076_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow076_physicalVolumeDenominatorChars = some (7283644249448448000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow076_physicalVolume_denominator_nonzero : (7283644249448448000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow076_physicalVolume_parse :
    parseRational geometryRow076_physicalVolumeText = .ok geometryRowsTyped076.physicalVolume :=
  original_rational_fraction_of_chars geometryRow076_physicalVolumeNumeratorChars geometryRow076_physicalVolumeDenominatorChars
    (5205746634712212214521042728864316841237 : Int) (7283644249448448000000000000000000000000000000000000000000000000000 : Int)
    geometryRow076_physicalVolume_numerator_no_slash geometryRow076_physicalVolume_numerator_parse
    geometryRow076_physicalVolume_denominator_parse geometryRow076_physicalVolume_denominator_nonzero

theorem geometryRow076_physicalVolume_read :
    rationalField geometryRowsJson076 "physical_volume" = .ok geometryRowsTyped076.physicalVolume :=
  original_rationalField_of_string geometryRowsJson076 "physical_volume" geometryRow076_physicalVolumeText
    geometryRowsTyped076.physicalVolume geometryRow076_physicalVolume_field geometryRow076_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_physicalVolume_complete"
  err.flush

noncomputable def geometryRow076_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow076_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow076_meanGapText : String := String.ofList (geometryRow076_meanGapNumeratorChars ++ '/' :: geometryRow076_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_meanGap_before_field"
  err.flush

theorem geometryRow076_meanGap_field :
    geometryRowsJson076.getObjVal? "mean_gap" = .ok (.str geometryRow076_meanGapText) := by rfl

theorem geometryRow076_meanGap_numerator_no_slash :
    geometryRow076_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow076_meanGap_numerator_parse :
    SourceJson.intChars geometryRow076_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow076_meanGap_denominator_parse :
    SourceJson.intChars geometryRow076_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow076_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow076_meanGap_parse :
    parseRational geometryRow076_meanGapText = .ok geometryRowsTyped076.meanGap :=
  original_rational_fraction_of_chars geometryRow076_meanGapNumeratorChars geometryRow076_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow076_meanGap_numerator_no_slash geometryRow076_meanGap_numerator_parse
    geometryRow076_meanGap_denominator_parse geometryRow076_meanGap_denominator_nonzero

theorem geometryRow076_meanGap_read :
    rationalField geometryRowsJson076 "mean_gap" = .ok geometryRowsTyped076.meanGap :=
  original_rationalField_of_string geometryRowsJson076 "mean_gap" geometryRow076_meanGapText
    geometryRowsTyped076.meanGap geometryRow076_meanGap_field geometryRow076_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_meanGap_complete"
  err.flush

noncomputable def geometryRow076_jensenBoundNumeratorChars : List Char := ['1', '5', '3', '1', '2', '4', '2', '3', '5', '0', '4', '6', '2', '0', '1', '7', '2', '2', '0', '3', '4', '4', '8', '6', '9', '0', '2', '9', '5', '4', '4', '4', '7', '5', '3', '9', '6', '8', '7', '2', '4', '9', '3', '1', '5', '3', '9', '7', '1', '5', '1', '6', '6', '6', '2', '9', '9', '3', '0', '5', '9', '9', '0', '2', '8', '9', '3', '1', '1', '3', '5', '1', '6', '4', '5', '8', '6', '6', '0', '1', '9', '1', '2', '4', '4', '9', '1', '8', '1', '7', '3', '5', '2', '9', '0', '3', '3', '2', '5', '7', '3', '5', '5', '4', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow076_jensenBoundDenominatorChars : List Char := ['3', '2', '3', '4', '1', '2', '3', '0', '8', '6', '6', '7', '1', '1', '5', '6', '1', '2', '6', '1', '7', '9', '5', '0', '3', '5', '9', '0', '6', '6', '5', '1', '3', '9', '0', '5', '2', '6', '9', '2', '8', '3', '3', '3', '0', '3', '4', '0', '7', '4', '5', '1', '8', '3', '7', '7', '0', '6', '0', '6', '4', '1', '8', '4', '9', '1', '7', '2', '9', '6', '4', '0', '2', '2', '8', '2', '3', '7', '9', '7', '9', '6', '6', '1', '6', '7', '3', '2', '4', '3', '7', '6', '3', '8', '5', '7', '6', '4', '9', '6', '0', '4', '7', '1', '9', '1', '9', '1', '4', '9', '9', '2', '0', '8', '9', '5', '1', '3', '3', '7', '0', '1', '4', '7', '6', '3', '5', '9', '3', '0', '2', '4', '1', '6', '7', '3', '0', '7']
noncomputable def geometryRow076_jensenBoundText : String := String.ofList (geometryRow076_jensenBoundNumeratorChars ++ '/' :: geometryRow076_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_jensenBound_before_field"
  err.flush

theorem geometryRow076_jensenBound_field :
    geometryRowsJson076.getObjVal? "jensen_bound" = .ok (.str geometryRow076_jensenBoundText) := by rfl

theorem geometryRow076_jensenBound_numerator_no_slash :
    geometryRow076_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow076_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow076_jensenBoundNumeratorChars = some (153124235046201722034486902954447539687249315397151666299305990289311351645866019124491817352903325735546875000000000000 : Int) := by decide +kernel

theorem geometryRow076_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow076_jensenBoundDenominatorChars = some (323412308667115612617950359066513905269283330340745183770606418491729640228237979661673243763857649604719191499208951337014763593024167307 : Int) := by decide +kernel

theorem geometryRow076_jensenBound_denominator_nonzero : (323412308667115612617950359066513905269283330340745183770606418491729640228237979661673243763857649604719191499208951337014763593024167307 : Int) ≠ 0 := by decide +kernel

theorem geometryRow076_jensenBound_parse :
    parseRational geometryRow076_jensenBoundText = .ok geometryRowsTyped076.jensenBound :=
  original_rational_fraction_of_chars geometryRow076_jensenBoundNumeratorChars geometryRow076_jensenBoundDenominatorChars
    (153124235046201722034486902954447539687249315397151666299305990289311351645866019124491817352903325735546875000000000000 : Int) (323412308667115612617950359066513905269283330340745183770606418491729640228237979661673243763857649604719191499208951337014763593024167307 : Int)
    geometryRow076_jensenBound_numerator_no_slash geometryRow076_jensenBound_numerator_parse
    geometryRow076_jensenBound_denominator_parse geometryRow076_jensenBound_denominator_nonzero

theorem geometryRow076_jensenBound_read :
    rationalField geometryRowsJson076 "jensen_bound" = .ok geometryRowsTyped076.jensenBound :=
  original_rationalField_of_string geometryRowsJson076 "jensen_bound" geometryRow076_jensenBoundText
    geometryRowsTyped076.jensenBound geometryRow076_jensenBound_field geometryRow076_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_factorMaxima_before"
  err.flush

theorem geometryRow076_factorMaxima_read :
    rationalArrayField geometryRowsJson076 "factor_maxima" = .ok geometryRowsTyped076.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_gapWeightedMeans_before"
  err.flush

theorem geometryRow076_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson076 "gap_weighted_means" = .ok geometryRowsTyped076.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow076_floorChars : List Char := ['3', '7', '5', '1', '1', '7', '1', '9', '4', '1', '8']
noncomputable def geometryRow076_floorText : String := String.ofList geometryRow076_floorChars

theorem geometryRow076_floor_text_read :
    geometryRowsJson076.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow076_floorText := by rfl

theorem geometryRow076_floor_chars_parse :
    SourceJson.intChars geometryRow076_floorChars = some (37511719418 : Int) := by decide +kernel

theorem geometryRow076_floor_parse :
    parseInteger geometryRow076_floorText = .ok geometryRowsTyped076.jensenFloorQ96 := by
  simp only [geometryRow076_floorText, parseInteger, String.toList_ofList, geometryRow076_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_076 :
    decodeGeometryRow geometryRowsJson076 = .ok geometryRowsTyped076 :=
  original_geometryRow_of_fields geometryRowsJson076 geometryRowsTyped076 geometryRow076_floorText
    geometryRow076_simplexId_read geometryRow076_vertexIds_read
    geometryRow076_physicalVolume_read geometryRow076_meanGap_read
    geometryRow076_factorMaxima_read geometryRow076_gapWeightedMeans_read
    geometryRow076_jensenBound_read geometryRow076_floor_text_read geometryRow076_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_076_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock038 : List SourceJson := [geometryRowsJson075, geometryRowsJson076]
noncomputable def geometryRowsTypedBlock038 : List (GeometryRow) := [geometryRowsTyped075, geometryRowsTyped076]
noncomputable def geometryRowsTypedThroughBlock038 : List (GeometryRow) := geometryRowsTypedThroughBlock037 ++ geometryRowsTypedBlock038

theorem geometry_Rows_block_038_push_eq (acc : List SourceJson) :
    SimplicesBlock038.blockPush acc = [geometryRowsJson076, geometryRowsJson075] ++ acc := by rfl

theorem geometry_Rows_block_038_reverse (acc : List SourceJson) :
    (SimplicesBlock038.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock038 := by
  rw [geometry_Rows_block_038_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_038 :
    geometryRowsJsonBlock038.mapM decodeGeometryRow = .ok geometryRowsTypedBlock038 := by
  simp only [geometryRowsJsonBlock038, geometryRowsTypedBlock038, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_075, decode_geometry_Rows_076]
  rfl

theorem decode_geometry_Rows_through_block_038 :
    SimplicesValue.arrayAcc039.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock038 := by
  change (SimplicesBlock038.blockPush SimplicesValue.arrayAcc038).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_038_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_037, decode_geometry_Rows_block_038]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_038_complete"
  err.flush

#print axioms geometryRow075_simplexId_read
#print axioms geometryRow075_vertexIds_read
#print axioms geometryRow075_physicalVolume_field
#print axioms geometryRow075_physicalVolume_numerator_no_slash
#print axioms geometryRow075_physicalVolume_numerator_parse
#print axioms geometryRow075_physicalVolume_denominator_parse
#print axioms geometryRow075_physicalVolume_denominator_nonzero
#print axioms geometryRow075_physicalVolume_parse
#print axioms geometryRow075_physicalVolume_read
#print axioms geometryRow075_meanGap_field
#print axioms geometryRow075_meanGap_numerator_no_slash
#print axioms geometryRow075_meanGap_numerator_parse
#print axioms geometryRow075_meanGap_denominator_parse
#print axioms geometryRow075_meanGap_denominator_nonzero
#print axioms geometryRow075_meanGap_parse
#print axioms geometryRow075_meanGap_read
#print axioms geometryRow075_jensenBound_field
#print axioms geometryRow075_jensenBound_numerator_no_slash
#print axioms geometryRow075_jensenBound_numerator_parse
#print axioms geometryRow075_jensenBound_denominator_parse
#print axioms geometryRow075_jensenBound_denominator_nonzero
#print axioms geometryRow075_jensenBound_parse
#print axioms geometryRow075_jensenBound_read
#print axioms geometryRow075_factorMaxima_read
#print axioms geometryRow075_gapWeightedMeans_read
#print axioms geometryRow075_floor_text_read
#print axioms geometryRow075_floor_chars_parse
#print axioms geometryRow075_floor_parse
#print axioms decode_geometry_Rows_075
#print axioms geometryRow076_simplexId_read
#print axioms geometryRow076_vertexIds_read
#print axioms geometryRow076_physicalVolume_field
#print axioms geometryRow076_physicalVolume_numerator_no_slash
#print axioms geometryRow076_physicalVolume_numerator_parse
#print axioms geometryRow076_physicalVolume_denominator_parse
#print axioms geometryRow076_physicalVolume_denominator_nonzero
#print axioms geometryRow076_physicalVolume_parse
#print axioms geometryRow076_physicalVolume_read
#print axioms geometryRow076_meanGap_field
#print axioms geometryRow076_meanGap_numerator_no_slash
#print axioms geometryRow076_meanGap_numerator_parse
#print axioms geometryRow076_meanGap_denominator_parse
#print axioms geometryRow076_meanGap_denominator_nonzero
#print axioms geometryRow076_meanGap_parse
#print axioms geometryRow076_meanGap_read
#print axioms geometryRow076_jensenBound_field
#print axioms geometryRow076_jensenBound_numerator_no_slash
#print axioms geometryRow076_jensenBound_numerator_parse
#print axioms geometryRow076_jensenBound_denominator_parse
#print axioms geometryRow076_jensenBound_denominator_nonzero
#print axioms geometryRow076_jensenBound_parse
#print axioms geometryRow076_jensenBound_read
#print axioms geometryRow076_factorMaxima_read
#print axioms geometryRow076_gapWeightedMeans_read
#print axioms geometryRow076_floor_text_read
#print axioms geometryRow076_floor_chars_parse
#print axioms geometryRow076_floor_parse
#print axioms decode_geometry_Rows_076
#print axioms geometry_Rows_block_038_push_eq
#print axioms geometry_Rows_block_038_reverse
#print axioms decode_geometry_Rows_block_038
#print axioms decode_geometry_Rows_through_block_038

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
