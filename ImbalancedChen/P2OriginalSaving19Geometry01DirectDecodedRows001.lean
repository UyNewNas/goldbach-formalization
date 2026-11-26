import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows000

/-! Original simplices typed block 1, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson002 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped002 : GeometryRow :=
  { simplexId := 2,
    vertexIds := #[39, 35, 29, 28, 25, 13, 12, 2, 0],
    physicalVolume := ((3172058147377718062546305569404273710882361 : ℚ) / (1880184536998871040000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((139690977551 : ℚ) / (1646400000000 : ℚ)), ((141423168431 : ℚ) / (1646400000000 : ℚ)), ((51143538613 : ℚ) / (352800000000 : ℚ)), ((63784253271 : ℚ) / (548800000000 : ℚ)), ((50399663683 : ℚ) / (705600000000 : ℚ)), ((117703370789 : ℚ) / (2469600000000 : ℚ)), ((14287179293 : ℚ) / (403200000000 : ℚ)), ((13450622663 : ℚ) / (403200000000 : ℚ)), ((155820642263 : ℚ) / (4939200000000 : ℚ)), ((152354284823 : ℚ) / (4939200000000 : ℚ))],
    jensenBound := ((973050625603500647327305686231623818149455351191188677593043435520000000000000000000000000 : ℚ) / (118623927025024913822699555577728887116700095557338274629521764128374699490354787457791083751145249907057 : ℚ)),
    jensenFloorQ96 := (649894292267505 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_simplexId_before"
  err.flush

theorem geometryRow002_simplexId_read :
    geometryRowsJson002.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped002.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_vertexIds_before"
  err.flush

theorem geometryRow002_vertexIds_read :
    geometryRowsJson002.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped002.vertexIds := by decide +kernel

noncomputable def geometryRow002_physicalVolumeNumeratorChars : List Char := ['3', '1', '7', '2', '0', '5', '8', '1', '4', '7', '3', '7', '7', '7', '1', '8', '0', '6', '2', '5', '4', '6', '3', '0', '5', '5', '6', '9', '4', '0', '4', '2', '7', '3', '7', '1', '0', '8', '8', '2', '3', '6', '1']
noncomputable def geometryRow002_physicalVolumeDenominatorChars : List Char := ['1', '8', '8', '0', '1', '8', '4', '5', '3', '6', '9', '9', '8', '8', '7', '1', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_physicalVolumeText : String := String.ofList (geometryRow002_physicalVolumeNumeratorChars ++ '/' :: geometryRow002_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_physicalVolume_before_field"
  err.flush

theorem geometryRow002_physicalVolume_field :
    geometryRowsJson002.getObjVal? "physical_volume" = .ok (.str geometryRow002_physicalVolumeText) := by rfl

theorem geometryRow002_physicalVolume_numerator_no_slash :
    geometryRow002_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeNumeratorChars = some (3172058147377718062546305569404273710882361 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeDenominatorChars = some (1880184536998871040000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_nonzero : (1880184536998871040000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_physicalVolume_parse :
    parseRational geometryRow002_physicalVolumeText = .ok geometryRowsTyped002.physicalVolume :=
  original_rational_fraction_of_chars geometryRow002_physicalVolumeNumeratorChars geometryRow002_physicalVolumeDenominatorChars
    (3172058147377718062546305569404273710882361 : Int) (1880184536998871040000000000000000000000000000000000000000000000000 : Int)
    geometryRow002_physicalVolume_numerator_no_slash geometryRow002_physicalVolume_numerator_parse
    geometryRow002_physicalVolume_denominator_parse geometryRow002_physicalVolume_denominator_nonzero

theorem geometryRow002_physicalVolume_read :
    rationalField geometryRowsJson002 "physical_volume" = .ok geometryRowsTyped002.physicalVolume :=
  original_rationalField_of_string geometryRowsJson002 "physical_volume" geometryRow002_physicalVolumeText
    geometryRowsTyped002.physicalVolume geometryRow002_physicalVolume_field geometryRow002_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_physicalVolume_complete"
  err.flush

noncomputable def geometryRow002_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow002_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_meanGapText : String := String.ofList (geometryRow002_meanGapNumeratorChars ++ '/' :: geometryRow002_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_meanGap_before_field"
  err.flush

theorem geometryRow002_meanGap_field :
    geometryRowsJson002.getObjVal? "mean_gap" = .ok (.str geometryRow002_meanGapText) := by rfl

theorem geometryRow002_meanGap_numerator_no_slash :
    geometryRow002_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_meanGap_numerator_parse :
    SourceJson.intChars geometryRow002_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_parse :
    SourceJson.intChars geometryRow002_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_meanGap_parse :
    parseRational geometryRow002_meanGapText = .ok geometryRowsTyped002.meanGap :=
  original_rational_fraction_of_chars geometryRow002_meanGapNumeratorChars geometryRow002_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow002_meanGap_numerator_no_slash geometryRow002_meanGap_numerator_parse
    geometryRow002_meanGap_denominator_parse geometryRow002_meanGap_denominator_nonzero

theorem geometryRow002_meanGap_read :
    rationalField geometryRowsJson002 "mean_gap" = .ok geometryRowsTyped002.meanGap :=
  original_rationalField_of_string geometryRowsJson002 "mean_gap" geometryRow002_meanGapText
    geometryRowsTyped002.meanGap geometryRow002_meanGap_field geometryRow002_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_meanGap_complete"
  err.flush

noncomputable def geometryRow002_jensenBoundNumeratorChars : List Char := ['9', '7', '3', '0', '5', '0', '6', '2', '5', '6', '0', '3', '5', '0', '0', '6', '4', '7', '3', '2', '7', '3', '0', '5', '6', '8', '6', '2', '3', '1', '6', '2', '3', '8', '1', '8', '1', '4', '9', '4', '5', '5', '3', '5', '1', '1', '9', '1', '1', '8', '8', '6', '7', '7', '5', '9', '3', '0', '4', '3', '4', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_jensenBoundDenominatorChars : List Char := ['1', '1', '8', '6', '2', '3', '9', '2', '7', '0', '2', '5', '0', '2', '4', '9', '1', '3', '8', '2', '2', '6', '9', '9', '5', '5', '5', '5', '7', '7', '7', '2', '8', '8', '8', '7', '1', '1', '6', '7', '0', '0', '0', '9', '5', '5', '5', '7', '3', '3', '8', '2', '7', '4', '6', '2', '9', '5', '2', '1', '7', '6', '4', '1', '2', '8', '3', '7', '4', '6', '9', '9', '4', '9', '0', '3', '5', '4', '7', '8', '7', '4', '5', '7', '7', '9', '1', '0', '8', '3', '7', '5', '1', '1', '4', '5', '2', '4', '9', '9', '0', '7', '0', '5', '7']
noncomputable def geometryRow002_jensenBoundText : String := String.ofList (geometryRow002_jensenBoundNumeratorChars ++ '/' :: geometryRow002_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_jensenBound_before_field"
  err.flush

theorem geometryRow002_jensenBound_field :
    geometryRowsJson002.getObjVal? "jensen_bound" = .ok (.str geometryRow002_jensenBoundText) := by rfl

theorem geometryRow002_jensenBound_numerator_no_slash :
    geometryRow002_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow002_jensenBoundNumeratorChars = some (973050625603500647327305686231623818149455351191188677593043435520000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow002_jensenBoundDenominatorChars = some (118623927025024913822699555577728887116700095557338274629521764128374699490354787457791083751145249907057 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_nonzero : (118623927025024913822699555577728887116700095557338274629521764128374699490354787457791083751145249907057 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_jensenBound_parse :
    parseRational geometryRow002_jensenBoundText = .ok geometryRowsTyped002.jensenBound :=
  original_rational_fraction_of_chars geometryRow002_jensenBoundNumeratorChars geometryRow002_jensenBoundDenominatorChars
    (973050625603500647327305686231623818149455351191188677593043435520000000000000000000000000 : Int) (118623927025024913822699555577728887116700095557338274629521764128374699490354787457791083751145249907057 : Int)
    geometryRow002_jensenBound_numerator_no_slash geometryRow002_jensenBound_numerator_parse
    geometryRow002_jensenBound_denominator_parse geometryRow002_jensenBound_denominator_nonzero

theorem geometryRow002_jensenBound_read :
    rationalField geometryRowsJson002 "jensen_bound" = .ok geometryRowsTyped002.jensenBound :=
  original_rationalField_of_string geometryRowsJson002 "jensen_bound" geometryRow002_jensenBoundText
    geometryRowsTyped002.jensenBound geometryRow002_jensenBound_field geometryRow002_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_factorMaxima_before"
  err.flush

theorem geometryRow002_factorMaxima_read :
    rationalArrayField geometryRowsJson002 "factor_maxima" = .ok geometryRowsTyped002.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_gapWeightedMeans_before"
  err.flush

theorem geometryRow002_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson002 "gap_weighted_means" = .ok geometryRowsTyped002.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow002_floorChars : List Char := ['6', '4', '9', '8', '9', '4', '2', '9', '2', '2', '6', '7', '5', '0', '5']
noncomputable def geometryRow002_floorText : String := String.ofList geometryRow002_floorChars

theorem geometryRow002_floor_text_read :
    geometryRowsJson002.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow002_floorText := by rfl

theorem geometryRow002_floor_chars_parse :
    SourceJson.intChars geometryRow002_floorChars = some (649894292267505 : Int) := by decide +kernel

theorem geometryRow002_floor_parse :
    parseInteger geometryRow002_floorText = .ok geometryRowsTyped002.jensenFloorQ96 := by
  simp only [geometryRow002_floorText, parseInteger, String.toList_ofList, geometryRow002_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_002 :
    decodeGeometryRow geometryRowsJson002 = .ok geometryRowsTyped002 :=
  original_geometryRow_of_fields geometryRowsJson002 geometryRowsTyped002 geometryRow002_floorText
    geometryRow002_simplexId_read geometryRow002_vertexIds_read
    geometryRow002_physicalVolume_read geometryRow002_meanGap_read
    geometryRow002_factorMaxima_read geometryRow002_gapWeightedMeans_read
    geometryRow002_jensenBound_read geometryRow002_floor_text_read geometryRow002_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_002_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson003 : SourceJson :=
  (SimplicesBlock001.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped003 : GeometryRow :=
  { simplexId := 3,
    vertexIds := #[39, 35, 29, 28, 25, 13, 12, 4, 2],
    physicalVolume := ((5453139880112870939596362232813636536989489 : ℚ) / (15320022153324134400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((591629 : ℚ) / (517440000 : ℚ)),
    factorMaxima := #[((1021879 : ℚ) / (11200000 : ℚ)), ((37827897 : ℚ) / (392000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((8952977 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((153585156499131689 : ℚ) / (1847351352000000000 : ℚ)), ((10429141994651663 : ℚ) / (123156756800000000 : ℚ)), ((57642043695935191 : ℚ) / (395861004000000000 : ℚ)), ((131081818530412741 : ℚ) / (1108410811200000000 : ℚ)), ((11437323881690249 : ℚ) / (158344401600000000 : ℚ)), ((25510262483923699 : ℚ) / (554205405600000000 : ℚ)), ((15995839870300907 : ℚ) / (452412576000000000 : ℚ)), ((15057177320826257 : ℚ) / (452412576000000000 : ℚ)), ((174408607385909417 : ℚ) / (5542054056000000000 : ℚ)), ((11246829581533367 : ℚ) / (369470270400000000 : ℚ))],
    jensenBound := ((206102366855068729223226441577502608025951633053345422192195444997686848591180204757550397009961833859884252744719259520000000000000000000000000000000 : ℚ) / (57526724140462792030788445282506039240997046634258187721815613202143725377478780508133000622761203417557060728168589627335700923800309003443165032990883602581475103 : ℚ)),
    jensenFloorQ96 := (283852627796034 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_simplexId_before"
  err.flush

theorem geometryRow003_simplexId_read :
    geometryRowsJson003.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped003.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_vertexIds_before"
  err.flush

theorem geometryRow003_vertexIds_read :
    geometryRowsJson003.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped003.vertexIds := by decide +kernel

noncomputable def geometryRow003_physicalVolumeNumeratorChars : List Char := ['5', '4', '5', '3', '1', '3', '9', '8', '8', '0', '1', '1', '2', '8', '7', '0', '9', '3', '9', '5', '9', '6', '3', '6', '2', '2', '3', '2', '8', '1', '3', '6', '3', '6', '5', '3', '6', '9', '8', '9', '4', '8', '9']
noncomputable def geometryRow003_physicalVolumeDenominatorChars : List Char := ['1', '5', '3', '2', '0', '0', '2', '2', '1', '5', '3', '3', '2', '4', '1', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_physicalVolumeText : String := String.ofList (geometryRow003_physicalVolumeNumeratorChars ++ '/' :: geometryRow003_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_physicalVolume_before_field"
  err.flush

theorem geometryRow003_physicalVolume_field :
    geometryRowsJson003.getObjVal? "physical_volume" = .ok (.str geometryRow003_physicalVolumeText) := by rfl

theorem geometryRow003_physicalVolume_numerator_no_slash :
    geometryRow003_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeNumeratorChars = some (5453139880112870939596362232813636536989489 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeDenominatorChars = some (15320022153324134400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_nonzero : (15320022153324134400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_physicalVolume_parse :
    parseRational geometryRow003_physicalVolumeText = .ok geometryRowsTyped003.physicalVolume :=
  original_rational_fraction_of_chars geometryRow003_physicalVolumeNumeratorChars geometryRow003_physicalVolumeDenominatorChars
    (5453139880112870939596362232813636536989489 : Int) (15320022153324134400000000000000000000000000000000000000000000000000 : Int)
    geometryRow003_physicalVolume_numerator_no_slash geometryRow003_physicalVolume_numerator_parse
    geometryRow003_physicalVolume_denominator_parse geometryRow003_physicalVolume_denominator_nonzero

theorem geometryRow003_physicalVolume_read :
    rationalField geometryRowsJson003 "physical_volume" = .ok geometryRowsTyped003.physicalVolume :=
  original_rationalField_of_string geometryRowsJson003 "physical_volume" geometryRow003_physicalVolumeText
    geometryRowsTyped003.physicalVolume geometryRow003_physicalVolume_field geometryRow003_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_physicalVolume_complete"
  err.flush

noncomputable def geometryRow003_meanGapNumeratorChars : List Char := ['5', '9', '1', '6', '2', '9']
noncomputable def geometryRow003_meanGapDenominatorChars : List Char := ['5', '1', '7', '4', '4', '0', '0', '0', '0']
noncomputable def geometryRow003_meanGapText : String := String.ofList (geometryRow003_meanGapNumeratorChars ++ '/' :: geometryRow003_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_meanGap_before_field"
  err.flush

theorem geometryRow003_meanGap_field :
    geometryRowsJson003.getObjVal? "mean_gap" = .ok (.str geometryRow003_meanGapText) := by rfl

theorem geometryRow003_meanGap_numerator_no_slash :
    geometryRow003_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_meanGap_numerator_parse :
    SourceJson.intChars geometryRow003_meanGapNumeratorChars = some (591629 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_parse :
    SourceJson.intChars geometryRow003_meanGapDenominatorChars = some (517440000 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_nonzero : (517440000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_meanGap_parse :
    parseRational geometryRow003_meanGapText = .ok geometryRowsTyped003.meanGap :=
  original_rational_fraction_of_chars geometryRow003_meanGapNumeratorChars geometryRow003_meanGapDenominatorChars
    (591629 : Int) (517440000 : Int)
    geometryRow003_meanGap_numerator_no_slash geometryRow003_meanGap_numerator_parse
    geometryRow003_meanGap_denominator_parse geometryRow003_meanGap_denominator_nonzero

theorem geometryRow003_meanGap_read :
    rationalField geometryRowsJson003 "mean_gap" = .ok geometryRowsTyped003.meanGap :=
  original_rationalField_of_string geometryRowsJson003 "mean_gap" geometryRow003_meanGapText
    geometryRowsTyped003.meanGap geometryRow003_meanGap_field geometryRow003_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_meanGap_complete"
  err.flush

noncomputable def geometryRow003_jensenBoundNumeratorChars : List Char := ['2', '0', '6', '1', '0', '2', '3', '6', '6', '8', '5', '5', '0', '6', '8', '7', '2', '9', '2', '2', '3', '2', '2', '6', '4', '4', '1', '5', '7', '7', '5', '0', '2', '6', '0', '8', '0', '2', '5', '9', '5', '1', '6', '3', '3', '0', '5', '3', '3', '4', '5', '4', '2', '2', '1', '9', '2', '1', '9', '5', '4', '4', '4', '9', '9', '7', '6', '8', '6', '8', '4', '8', '5', '9', '1', '1', '8', '0', '2', '0', '4', '7', '5', '7', '5', '5', '0', '3', '9', '7', '0', '0', '9', '9', '6', '1', '8', '3', '3', '8', '5', '9', '8', '8', '4', '2', '5', '2', '7', '4', '4', '7', '1', '9', '2', '5', '9', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_jensenBoundDenominatorChars : List Char := ['5', '7', '5', '2', '6', '7', '2', '4', '1', '4', '0', '4', '6', '2', '7', '9', '2', '0', '3', '0', '7', '8', '8', '4', '4', '5', '2', '8', '2', '5', '0', '6', '0', '3', '9', '2', '4', '0', '9', '9', '7', '0', '4', '6', '6', '3', '4', '2', '5', '8', '1', '8', '7', '7', '2', '1', '8', '1', '5', '6', '1', '3', '2', '0', '2', '1', '4', '3', '7', '2', '5', '3', '7', '7', '4', '7', '8', '7', '8', '0', '5', '0', '8', '1', '3', '3', '0', '0', '0', '6', '2', '2', '7', '6', '1', '2', '0', '3', '4', '1', '7', '5', '5', '7', '0', '6', '0', '7', '2', '8', '1', '6', '8', '5', '8', '9', '6', '2', '7', '3', '3', '5', '7', '0', '0', '9', '2', '3', '8', '0', '0', '3', '0', '9', '0', '0', '3', '4', '4', '3', '1', '6', '5', '0', '3', '2', '9', '9', '0', '8', '8', '3', '6', '0', '2', '5', '8', '1', '4', '7', '5', '1', '0', '3']
noncomputable def geometryRow003_jensenBoundText : String := String.ofList (geometryRow003_jensenBoundNumeratorChars ++ '/' :: geometryRow003_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_jensenBound_before_field"
  err.flush

theorem geometryRow003_jensenBound_field :
    geometryRowsJson003.getObjVal? "jensen_bound" = .ok (.str geometryRow003_jensenBoundText) := by rfl

theorem geometryRow003_jensenBound_numerator_no_slash :
    geometryRow003_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow003_jensenBoundNumeratorChars = some (206102366855068729223226441577502608025951633053345422192195444997686848591180204757550397009961833859884252744719259520000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow003_jensenBoundDenominatorChars = some (57526724140462792030788445282506039240997046634258187721815613202143725377478780508133000622761203417557060728168589627335700923800309003443165032990883602581475103 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_nonzero : (57526724140462792030788445282506039240997046634258187721815613202143725377478780508133000622761203417557060728168589627335700923800309003443165032990883602581475103 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_jensenBound_parse :
    parseRational geometryRow003_jensenBoundText = .ok geometryRowsTyped003.jensenBound :=
  original_rational_fraction_of_chars geometryRow003_jensenBoundNumeratorChars geometryRow003_jensenBoundDenominatorChars
    (206102366855068729223226441577502608025951633053345422192195444997686848591180204757550397009961833859884252744719259520000000000000000000000000000000 : Int) (57526724140462792030788445282506039240997046634258187721815613202143725377478780508133000622761203417557060728168589627335700923800309003443165032990883602581475103 : Int)
    geometryRow003_jensenBound_numerator_no_slash geometryRow003_jensenBound_numerator_parse
    geometryRow003_jensenBound_denominator_parse geometryRow003_jensenBound_denominator_nonzero

theorem geometryRow003_jensenBound_read :
    rationalField geometryRowsJson003 "jensen_bound" = .ok geometryRowsTyped003.jensenBound :=
  original_rationalField_of_string geometryRowsJson003 "jensen_bound" geometryRow003_jensenBoundText
    geometryRowsTyped003.jensenBound geometryRow003_jensenBound_field geometryRow003_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_factorMaxima_before"
  err.flush

theorem geometryRow003_factorMaxima_read :
    rationalArrayField geometryRowsJson003 "factor_maxima" = .ok geometryRowsTyped003.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_gapWeightedMeans_before"
  err.flush

theorem geometryRow003_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson003 "gap_weighted_means" = .ok geometryRowsTyped003.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow003_floorChars : List Char := ['2', '8', '3', '8', '5', '2', '6', '2', '7', '7', '9', '6', '0', '3', '4']
noncomputable def geometryRow003_floorText : String := String.ofList geometryRow003_floorChars

theorem geometryRow003_floor_text_read :
    geometryRowsJson003.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow003_floorText := by rfl

theorem geometryRow003_floor_chars_parse :
    SourceJson.intChars geometryRow003_floorChars = some (283852627796034 : Int) := by decide +kernel

theorem geometryRow003_floor_parse :
    parseInteger geometryRow003_floorText = .ok geometryRowsTyped003.jensenFloorQ96 := by
  simp only [geometryRow003_floorText, parseInteger, String.toList_ofList, geometryRow003_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_003 :
    decodeGeometryRow geometryRowsJson003 = .ok geometryRowsTyped003 :=
  original_geometryRow_of_fields geometryRowsJson003 geometryRowsTyped003 geometryRow003_floorText
    geometryRow003_simplexId_read geometryRow003_vertexIds_read
    geometryRow003_physicalVolume_read geometryRow003_meanGap_read
    geometryRow003_factorMaxima_read geometryRow003_gapWeightedMeans_read
    geometryRow003_jensenBound_read geometryRow003_floor_text_read geometryRow003_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_003_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock001 : List SourceJson := [geometryRowsJson002, geometryRowsJson003]
noncomputable def geometryRowsTypedBlock001 : List (GeometryRow) := [geometryRowsTyped002, geometryRowsTyped003]
noncomputable def geometryRowsTypedThroughBlock001 : List (GeometryRow) := geometryRowsTypedThroughBlock000 ++ geometryRowsTypedBlock001

theorem geometry_Rows_block_001_push_eq (acc : List SourceJson) :
    SimplicesBlock001.blockPush acc = [geometryRowsJson003, geometryRowsJson002] ++ acc := by rfl

theorem geometry_Rows_block_001_reverse (acc : List SourceJson) :
    (SimplicesBlock001.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock001 := by
  rw [geometry_Rows_block_001_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_001 :
    geometryRowsJsonBlock001.mapM decodeGeometryRow = .ok geometryRowsTypedBlock001 := by
  simp only [geometryRowsJsonBlock001, geometryRowsTypedBlock001, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_002, decode_geometry_Rows_003]
  rfl

theorem decode_geometry_Rows_through_block_001 :
    SimplicesValue.arrayAcc002.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock001 := by
  change (SimplicesBlock001.blockPush SimplicesValue.arrayAcc001).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_001_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_000, decode_geometry_Rows_block_001]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_001_complete"
  err.flush

#print axioms geometryRow002_simplexId_read
#print axioms geometryRow002_vertexIds_read
#print axioms geometryRow002_physicalVolume_field
#print axioms geometryRow002_physicalVolume_numerator_no_slash
#print axioms geometryRow002_physicalVolume_numerator_parse
#print axioms geometryRow002_physicalVolume_denominator_parse
#print axioms geometryRow002_physicalVolume_denominator_nonzero
#print axioms geometryRow002_physicalVolume_parse
#print axioms geometryRow002_physicalVolume_read
#print axioms geometryRow002_meanGap_field
#print axioms geometryRow002_meanGap_numerator_no_slash
#print axioms geometryRow002_meanGap_numerator_parse
#print axioms geometryRow002_meanGap_denominator_parse
#print axioms geometryRow002_meanGap_denominator_nonzero
#print axioms geometryRow002_meanGap_parse
#print axioms geometryRow002_meanGap_read
#print axioms geometryRow002_jensenBound_field
#print axioms geometryRow002_jensenBound_numerator_no_slash
#print axioms geometryRow002_jensenBound_numerator_parse
#print axioms geometryRow002_jensenBound_denominator_parse
#print axioms geometryRow002_jensenBound_denominator_nonzero
#print axioms geometryRow002_jensenBound_parse
#print axioms geometryRow002_jensenBound_read
#print axioms geometryRow002_factorMaxima_read
#print axioms geometryRow002_gapWeightedMeans_read
#print axioms geometryRow002_floor_text_read
#print axioms geometryRow002_floor_chars_parse
#print axioms geometryRow002_floor_parse
#print axioms decode_geometry_Rows_002
#print axioms geometryRow003_simplexId_read
#print axioms geometryRow003_vertexIds_read
#print axioms geometryRow003_physicalVolume_field
#print axioms geometryRow003_physicalVolume_numerator_no_slash
#print axioms geometryRow003_physicalVolume_numerator_parse
#print axioms geometryRow003_physicalVolume_denominator_parse
#print axioms geometryRow003_physicalVolume_denominator_nonzero
#print axioms geometryRow003_physicalVolume_parse
#print axioms geometryRow003_physicalVolume_read
#print axioms geometryRow003_meanGap_field
#print axioms geometryRow003_meanGap_numerator_no_slash
#print axioms geometryRow003_meanGap_numerator_parse
#print axioms geometryRow003_meanGap_denominator_parse
#print axioms geometryRow003_meanGap_denominator_nonzero
#print axioms geometryRow003_meanGap_parse
#print axioms geometryRow003_meanGap_read
#print axioms geometryRow003_jensenBound_field
#print axioms geometryRow003_jensenBound_numerator_no_slash
#print axioms geometryRow003_jensenBound_numerator_parse
#print axioms geometryRow003_jensenBound_denominator_parse
#print axioms geometryRow003_jensenBound_denominator_nonzero
#print axioms geometryRow003_jensenBound_parse
#print axioms geometryRow003_jensenBound_read
#print axioms geometryRow003_factorMaxima_read
#print axioms geometryRow003_gapWeightedMeans_read
#print axioms geometryRow003_floor_text_read
#print axioms geometryRow003_floor_chars_parse
#print axioms geometryRow003_floor_parse
#print axioms decode_geometry_Rows_003
#print axioms geometry_Rows_block_001_push_eq
#print axioms geometry_Rows_block_001_reverse
#print axioms decode_geometry_Rows_block_001
#print axioms decode_geometry_Rows_through_block_001

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
