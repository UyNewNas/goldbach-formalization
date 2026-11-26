import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows021

/-! Original simplices typed block 22, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson043 : SourceJson :=
  (SimplicesBlock022.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped043 : GeometryRow :=
  { simplexId := 43,
    vertexIds := #[39, 35, 24, 23, 21, 20, 3, 2, 0],
    physicalVolume := ((473410541456211677703592924087335445185667377481 : ℚ) / (2696566959906914304000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((6109170227 : ℚ) / (4888044000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((95090043512810052612419 : ℚ) / (1209372804337774480000000 : ℚ)), ((4754565105303059268921911 : ℚ) / (59259267412550949520000000 : ℚ)), ((15366951228909787883061289 : ℚ) / (106666681342591709136000000 : ℚ)), ((48447653615285111610800387 : ℚ) / (444444505594132121400000000 : ℚ)), ((9290106627232203002000989 : ℚ) / (156862766680281925200000000 : ℚ)), ((127745148551236695320578619 : ℚ) / (2666667033564792728400000000 : ℚ)), ((5658405111887530380218299 : ℚ) / (140350896503410143600000000 : ℚ)), ((106085783479658988343437301 : ℚ) / (2666667033564792728400000000 : ℚ)), ((103430331288595156545265663 : ℚ) / (2666667033564792728400000000 : ℚ)), ((102056959950884159179390903 : ℚ) / (2666667033564792728400000000 : ℚ))],
    jensenBound := ((3319761299557368299874299957798911420124685944300179865381442634771139301881320643718647761236369258054089845536150304993294641531934764107513653768793341519219696835703322948126965681886695923957601389067135421631061373440000000000000000000 : ℚ) / (2531122644896107566442610213278131143383892620600922740147478099198925106584837046398804135768918067692426177774037583557648834664229156973518986850089927966780468229100338025193657066092213237543090444351082279182285634538146347756591143179140225296487 : ℚ)),
    jensenFloorQ96 := (103913806105074141 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_simplexId_before"
  err.flush

theorem geometryRow043_simplexId_read :
    geometryRowsJson043.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped043.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_vertexIds_before"
  err.flush

theorem geometryRow043_vertexIds_read :
    geometryRowsJson043.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped043.vertexIds := by decide +kernel

noncomputable def geometryRow043_physicalVolumeNumeratorChars : List Char := ['4', '7', '3', '4', '1', '0', '5', '4', '1', '4', '5', '6', '2', '1', '1', '6', '7', '7', '7', '0', '3', '5', '9', '2', '9', '2', '4', '0', '8', '7', '3', '3', '5', '4', '4', '5', '1', '8', '5', '6', '6', '7', '3', '7', '7', '4', '8', '1']
noncomputable def geometryRow043_physicalVolumeDenominatorChars : List Char := ['2', '6', '9', '6', '5', '6', '6', '9', '5', '9', '9', '0', '6', '9', '1', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_physicalVolumeText : String := String.ofList (geometryRow043_physicalVolumeNumeratorChars ++ '/' :: geometryRow043_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_physicalVolume_before_field"
  err.flush

theorem geometryRow043_physicalVolume_field :
    geometryRowsJson043.getObjVal? "physical_volume" = .ok (.str geometryRow043_physicalVolumeText) := by rfl

theorem geometryRow043_physicalVolume_numerator_no_slash :
    geometryRow043_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeNumeratorChars = some (473410541456211677703592924087335445185667377481 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow043_physicalVolumeDenominatorChars = some (2696566959906914304000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_physicalVolume_denominator_nonzero : (2696566959906914304000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_physicalVolume_parse :
    parseRational geometryRow043_physicalVolumeText = .ok geometryRowsTyped043.physicalVolume :=
  original_rational_fraction_of_chars geometryRow043_physicalVolumeNumeratorChars geometryRow043_physicalVolumeDenominatorChars
    (473410541456211677703592924087335445185667377481 : Int) (2696566959906914304000000000000000000000000000000000000000000000000000 : Int)
    geometryRow043_physicalVolume_numerator_no_slash geometryRow043_physicalVolume_numerator_parse
    geometryRow043_physicalVolume_denominator_parse geometryRow043_physicalVolume_denominator_nonzero

theorem geometryRow043_physicalVolume_read :
    rationalField geometryRowsJson043 "physical_volume" = .ok geometryRowsTyped043.physicalVolume :=
  original_rationalField_of_string geometryRowsJson043 "physical_volume" geometryRow043_physicalVolumeText
    geometryRowsTyped043.physicalVolume geometryRow043_physicalVolume_field geometryRow043_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_physicalVolume_complete"
  err.flush

noncomputable def geometryRow043_meanGapNumeratorChars : List Char := ['6', '1', '0', '9', '1', '7', '0', '2', '2', '7']
noncomputable def geometryRow043_meanGapDenominatorChars : List Char := ['4', '8', '8', '8', '0', '4', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_meanGapText : String := String.ofList (geometryRow043_meanGapNumeratorChars ++ '/' :: geometryRow043_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_meanGap_before_field"
  err.flush

theorem geometryRow043_meanGap_field :
    geometryRowsJson043.getObjVal? "mean_gap" = .ok (.str geometryRow043_meanGapText) := by rfl

theorem geometryRow043_meanGap_numerator_no_slash :
    geometryRow043_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_meanGap_numerator_parse :
    SourceJson.intChars geometryRow043_meanGapNumeratorChars = some (6109170227 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_parse :
    SourceJson.intChars geometryRow043_meanGapDenominatorChars = some (4888044000000 : Int) := by decide +kernel

theorem geometryRow043_meanGap_denominator_nonzero : (4888044000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_meanGap_parse :
    parseRational geometryRow043_meanGapText = .ok geometryRowsTyped043.meanGap :=
  original_rational_fraction_of_chars geometryRow043_meanGapNumeratorChars geometryRow043_meanGapDenominatorChars
    (6109170227 : Int) (4888044000000 : Int)
    geometryRow043_meanGap_numerator_no_slash geometryRow043_meanGap_numerator_parse
    geometryRow043_meanGap_denominator_parse geometryRow043_meanGap_denominator_nonzero

theorem geometryRow043_meanGap_read :
    rationalField geometryRowsJson043 "mean_gap" = .ok geometryRowsTyped043.meanGap :=
  original_rationalField_of_string geometryRowsJson043 "mean_gap" geometryRow043_meanGapText
    geometryRowsTyped043.meanGap geometryRow043_meanGap_field geometryRow043_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_meanGap_complete"
  err.flush

noncomputable def geometryRow043_jensenBoundNumeratorChars : List Char := ['3', '3', '1', '9', '7', '6', '1', '2', '9', '9', '5', '5', '7', '3', '6', '8', '2', '9', '9', '8', '7', '4', '2', '9', '9', '9', '5', '7', '7', '9', '8', '9', '1', '1', '4', '2', '0', '1', '2', '4', '6', '8', '5', '9', '4', '4', '3', '0', '0', '1', '7', '9', '8', '6', '5', '3', '8', '1', '4', '4', '2', '6', '3', '4', '7', '7', '1', '1', '3', '9', '3', '0', '1', '8', '8', '1', '3', '2', '0', '6', '4', '3', '7', '1', '8', '6', '4', '7', '7', '6', '1', '2', '3', '6', '3', '6', '9', '2', '5', '8', '0', '5', '4', '0', '8', '9', '8', '4', '5', '5', '3', '6', '1', '5', '0', '3', '0', '4', '9', '9', '3', '2', '9', '4', '6', '4', '1', '5', '3', '1', '9', '3', '4', '7', '6', '4', '1', '0', '7', '5', '1', '3', '6', '5', '3', '7', '6', '8', '7', '9', '3', '3', '4', '1', '5', '1', '9', '2', '1', '9', '6', '9', '6', '8', '3', '5', '7', '0', '3', '3', '2', '2', '9', '4', '8', '1', '2', '6', '9', '6', '5', '6', '8', '1', '8', '8', '6', '6', '9', '5', '9', '2', '3', '9', '5', '7', '6', '0', '1', '3', '8', '9', '0', '6', '7', '1', '3', '5', '4', '2', '1', '6', '3', '1', '0', '6', '1', '3', '7', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow043_jensenBoundDenominatorChars : List Char := ['2', '5', '3', '1', '1', '2', '2', '6', '4', '4', '8', '9', '6', '1', '0', '7', '5', '6', '6', '4', '4', '2', '6', '1', '0', '2', '1', '3', '2', '7', '8', '1', '3', '1', '1', '4', '3', '3', '8', '3', '8', '9', '2', '6', '2', '0', '6', '0', '0', '9', '2', '2', '7', '4', '0', '1', '4', '7', '4', '7', '8', '0', '9', '9', '1', '9', '8', '9', '2', '5', '1', '0', '6', '5', '8', '4', '8', '3', '7', '0', '4', '6', '3', '9', '8', '8', '0', '4', '1', '3', '5', '7', '6', '8', '9', '1', '8', '0', '6', '7', '6', '9', '2', '4', '2', '6', '1', '7', '7', '7', '7', '4', '0', '3', '7', '5', '8', '3', '5', '5', '7', '6', '4', '8', '8', '3', '4', '6', '6', '4', '2', '2', '9', '1', '5', '6', '9', '7', '3', '5', '1', '8', '9', '8', '6', '8', '5', '0', '0', '8', '9', '9', '2', '7', '9', '6', '6', '7', '8', '0', '4', '6', '8', '2', '2', '9', '1', '0', '0', '3', '3', '8', '0', '2', '5', '1', '9', '3', '6', '5', '7', '0', '6', '6', '0', '9', '2', '2', '1', '3', '2', '3', '7', '5', '4', '3', '0', '9', '0', '4', '4', '4', '3', '5', '1', '0', '8', '2', '2', '7', '9', '1', '8', '2', '2', '8', '5', '6', '3', '4', '5', '3', '8', '1', '4', '6', '3', '4', '7', '7', '5', '6', '5', '9', '1', '1', '4', '3', '1', '7', '9', '1', '4', '0', '2', '2', '5', '2', '9', '6', '4', '8', '7']
noncomputable def geometryRow043_jensenBoundText : String := String.ofList (geometryRow043_jensenBoundNumeratorChars ++ '/' :: geometryRow043_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_jensenBound_before_field"
  err.flush

theorem geometryRow043_jensenBound_field :
    geometryRowsJson043.getObjVal? "jensen_bound" = .ok (.str geometryRow043_jensenBoundText) := by rfl

theorem geometryRow043_jensenBound_numerator_no_slash :
    geometryRow043_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow043_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow043_jensenBoundNumeratorChars = some (3319761299557368299874299957798911420124685944300179865381442634771139301881320643718647761236369258054089845536150304993294641531934764107513653768793341519219696835703322948126965681886695923957601389067135421631061373440000000000000000000 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow043_jensenBoundDenominatorChars = some (2531122644896107566442610213278131143383892620600922740147478099198925106584837046398804135768918067692426177774037583557648834664229156973518986850089927966780468229100338025193657066092213237543090444351082279182285634538146347756591143179140225296487 : Int) := by decide +kernel

theorem geometryRow043_jensenBound_denominator_nonzero : (2531122644896107566442610213278131143383892620600922740147478099198925106584837046398804135768918067692426177774037583557648834664229156973518986850089927966780468229100338025193657066092213237543090444351082279182285634538146347756591143179140225296487 : Int) ≠ 0 := by decide +kernel

theorem geometryRow043_jensenBound_parse :
    parseRational geometryRow043_jensenBoundText = .ok geometryRowsTyped043.jensenBound :=
  original_rational_fraction_of_chars geometryRow043_jensenBoundNumeratorChars geometryRow043_jensenBoundDenominatorChars
    (3319761299557368299874299957798911420124685944300179865381442634771139301881320643718647761236369258054089845536150304993294641531934764107513653768793341519219696835703322948126965681886695923957601389067135421631061373440000000000000000000 : Int) (2531122644896107566442610213278131143383892620600922740147478099198925106584837046398804135768918067692426177774037583557648834664229156973518986850089927966780468229100338025193657066092213237543090444351082279182285634538146347756591143179140225296487 : Int)
    geometryRow043_jensenBound_numerator_no_slash geometryRow043_jensenBound_numerator_parse
    geometryRow043_jensenBound_denominator_parse geometryRow043_jensenBound_denominator_nonzero

theorem geometryRow043_jensenBound_read :
    rationalField geometryRowsJson043 "jensen_bound" = .ok geometryRowsTyped043.jensenBound :=
  original_rationalField_of_string geometryRowsJson043 "jensen_bound" geometryRow043_jensenBoundText
    geometryRowsTyped043.jensenBound geometryRow043_jensenBound_field geometryRow043_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_factorMaxima_before"
  err.flush

theorem geometryRow043_factorMaxima_read :
    rationalArrayField geometryRowsJson043 "factor_maxima" = .ok geometryRowsTyped043.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_gapWeightedMeans_before"
  err.flush

theorem geometryRow043_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson043 "gap_weighted_means" = .ok geometryRowsTyped043.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow043_floorChars : List Char := ['1', '0', '3', '9', '1', '3', '8', '0', '6', '1', '0', '5', '0', '7', '4', '1', '4', '1']
noncomputable def geometryRow043_floorText : String := String.ofList geometryRow043_floorChars

theorem geometryRow043_floor_text_read :
    geometryRowsJson043.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow043_floorText := by rfl

theorem geometryRow043_floor_chars_parse :
    SourceJson.intChars geometryRow043_floorChars = some (103913806105074141 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY01_TYPED Row_043_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson044 : SourceJson :=
  (SimplicesBlock022.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped044 : GeometryRow :=
  { simplexId := 44,
    vertexIds := #[39, 35, 24, 23, 21, 20, 16, 1, 0],
    physicalVolume := ((176912612176799270363411811460544010965359 : ℚ) / (29134576997793792000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((6883213289531 : ℚ) / (91702170000000 : ℚ)), ((13800672726319 : ℚ) / (183404340000000 : ℚ)), ((160030300176181 : ℚ) / (1100426040000000 : ℚ)), ((64038841961519 : ℚ) / (611347800000000 : ℚ)), ((39146154038303 : ℚ) / (687766275000000 : ℚ)), ((271704919391257 : ℚ) / (5502130200000000 : ℚ)), ((12205967063387 : ℚ) / (289585800000000 : ℚ)), ((228975415255463 : ℚ) / (5502130200000000 : ℚ)), ((112934398374547 : ℚ) / (2751065100000000 : ℚ)), ((112933848161527 : ℚ) / (2751065100000000 : ℚ))],
    jensenBound := ((118267937646947105466197558343933666391783213772619861044863614784587230781876169277201652885662369606542968750000000000 : ℚ) / (33553861647885479229169009974539210820647166052124514378112763531915475645913456819338265296877694210992974666854505407148044637393146659 : ℚ)),
    jensenFloorQ96 := (279257019130 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_simplexId_before"
  err.flush

theorem geometryRow044_simplexId_read :
    geometryRowsJson044.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped044.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_vertexIds_before"
  err.flush

theorem geometryRow044_vertexIds_read :
    geometryRowsJson044.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped044.vertexIds := by decide +kernel

noncomputable def geometryRow044_physicalVolumeNumeratorChars : List Char := ['1', '7', '6', '9', '1', '2', '6', '1', '2', '1', '7', '6', '7', '9', '9', '2', '7', '0', '3', '6', '3', '4', '1', '1', '8', '1', '1', '4', '6', '0', '5', '4', '4', '0', '1', '0', '9', '6', '5', '3', '5', '9']
noncomputable def geometryRow044_physicalVolumeDenominatorChars : List Char := ['2', '9', '1', '3', '4', '5', '7', '6', '9', '9', '7', '7', '9', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_physicalVolumeText : String := String.ofList (geometryRow044_physicalVolumeNumeratorChars ++ '/' :: geometryRow044_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_physicalVolume_before_field"
  err.flush

theorem geometryRow044_physicalVolume_field :
    geometryRowsJson044.getObjVal? "physical_volume" = .ok (.str geometryRow044_physicalVolumeText) := by rfl

theorem geometryRow044_physicalVolume_numerator_no_slash :
    geometryRow044_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeNumeratorChars = some (176912612176799270363411811460544010965359 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow044_physicalVolumeDenominatorChars = some (29134576997793792000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow044_physicalVolume_denominator_nonzero : (29134576997793792000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_physicalVolume_parse :
    parseRational geometryRow044_physicalVolumeText = .ok geometryRowsTyped044.physicalVolume :=
  original_rational_fraction_of_chars geometryRow044_physicalVolumeNumeratorChars geometryRow044_physicalVolumeDenominatorChars
    (176912612176799270363411811460544010965359 : Int) (29134576997793792000000000000000000000000000000000000000000000000000 : Int)
    geometryRow044_physicalVolume_numerator_no_slash geometryRow044_physicalVolume_numerator_parse
    geometryRow044_physicalVolume_denominator_parse geometryRow044_physicalVolume_denominator_nonzero

theorem geometryRow044_physicalVolume_read :
    rationalField geometryRowsJson044 "physical_volume" = .ok geometryRowsTyped044.physicalVolume :=
  original_rationalField_of_string geometryRowsJson044 "physical_volume" geometryRow044_physicalVolumeText
    geometryRowsTyped044.physicalVolume geometryRow044_physicalVolume_field geometryRow044_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_physicalVolume_complete"
  err.flush

noncomputable def geometryRow044_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow044_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_meanGapText : String := String.ofList (geometryRow044_meanGapNumeratorChars ++ '/' :: geometryRow044_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_meanGap_before_field"
  err.flush

theorem geometryRow044_meanGap_field :
    geometryRowsJson044.getObjVal? "mean_gap" = .ok (.str geometryRow044_meanGapText) := by rfl

theorem geometryRow044_meanGap_numerator_no_slash :
    geometryRow044_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_meanGap_numerator_parse :
    SourceJson.intChars geometryRow044_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_parse :
    SourceJson.intChars geometryRow044_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow044_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_meanGap_parse :
    parseRational geometryRow044_meanGapText = .ok geometryRowsTyped044.meanGap :=
  original_rational_fraction_of_chars geometryRow044_meanGapNumeratorChars geometryRow044_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow044_meanGap_numerator_no_slash geometryRow044_meanGap_numerator_parse
    geometryRow044_meanGap_denominator_parse geometryRow044_meanGap_denominator_nonzero

theorem geometryRow044_meanGap_read :
    rationalField geometryRowsJson044 "mean_gap" = .ok geometryRowsTyped044.meanGap :=
  original_rationalField_of_string geometryRowsJson044 "mean_gap" geometryRow044_meanGapText
    geometryRowsTyped044.meanGap geometryRow044_meanGap_field geometryRow044_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_meanGap_complete"
  err.flush

noncomputable def geometryRow044_jensenBoundNumeratorChars : List Char := ['1', '1', '8', '2', '6', '7', '9', '3', '7', '6', '4', '6', '9', '4', '7', '1', '0', '5', '4', '6', '6', '1', '9', '7', '5', '5', '8', '3', '4', '3', '9', '3', '3', '6', '6', '6', '3', '9', '1', '7', '8', '3', '2', '1', '3', '7', '7', '2', '6', '1', '9', '8', '6', '1', '0', '4', '4', '8', '6', '3', '6', '1', '4', '7', '8', '4', '5', '8', '7', '2', '3', '0', '7', '8', '1', '8', '7', '6', '1', '6', '9', '2', '7', '7', '2', '0', '1', '6', '5', '2', '8', '8', '5', '6', '6', '2', '3', '6', '9', '6', '0', '6', '5', '4', '2', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow044_jensenBoundDenominatorChars : List Char := ['3', '3', '5', '5', '3', '8', '6', '1', '6', '4', '7', '8', '8', '5', '4', '7', '9', '2', '2', '9', '1', '6', '9', '0', '0', '9', '9', '7', '4', '5', '3', '9', '2', '1', '0', '8', '2', '0', '6', '4', '7', '1', '6', '6', '0', '5', '2', '1', '2', '4', '5', '1', '4', '3', '7', '8', '1', '1', '2', '7', '6', '3', '5', '3', '1', '9', '1', '5', '4', '7', '5', '6', '4', '5', '9', '1', '3', '4', '5', '6', '8', '1', '9', '3', '3', '8', '2', '6', '5', '2', '9', '6', '8', '7', '7', '6', '9', '4', '2', '1', '0', '9', '9', '2', '9', '7', '4', '6', '6', '6', '8', '5', '4', '5', '0', '5', '4', '0', '7', '1', '4', '8', '0', '4', '4', '6', '3', '7', '3', '9', '3', '1', '4', '6', '6', '5', '9']
noncomputable def geometryRow044_jensenBoundText : String := String.ofList (geometryRow044_jensenBoundNumeratorChars ++ '/' :: geometryRow044_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_jensenBound_before_field"
  err.flush

theorem geometryRow044_jensenBound_field :
    geometryRowsJson044.getObjVal? "jensen_bound" = .ok (.str geometryRow044_jensenBoundText) := by rfl

theorem geometryRow044_jensenBound_numerator_no_slash :
    geometryRow044_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow044_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow044_jensenBoundNumeratorChars = some (118267937646947105466197558343933666391783213772619861044863614784587230781876169277201652885662369606542968750000000000 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow044_jensenBoundDenominatorChars = some (33553861647885479229169009974539210820647166052124514378112763531915475645913456819338265296877694210992974666854505407148044637393146659 : Int) := by decide +kernel

theorem geometryRow044_jensenBound_denominator_nonzero : (33553861647885479229169009974539210820647166052124514378112763531915475645913456819338265296877694210992974666854505407148044637393146659 : Int) ≠ 0 := by decide +kernel

theorem geometryRow044_jensenBound_parse :
    parseRational geometryRow044_jensenBoundText = .ok geometryRowsTyped044.jensenBound :=
  original_rational_fraction_of_chars geometryRow044_jensenBoundNumeratorChars geometryRow044_jensenBoundDenominatorChars
    (118267937646947105466197558343933666391783213772619861044863614784587230781876169277201652885662369606542968750000000000 : Int) (33553861647885479229169009974539210820647166052124514378112763531915475645913456819338265296877694210992974666854505407148044637393146659 : Int)
    geometryRow044_jensenBound_numerator_no_slash geometryRow044_jensenBound_numerator_parse
    geometryRow044_jensenBound_denominator_parse geometryRow044_jensenBound_denominator_nonzero

theorem geometryRow044_jensenBound_read :
    rationalField geometryRowsJson044 "jensen_bound" = .ok geometryRowsTyped044.jensenBound :=
  original_rationalField_of_string geometryRowsJson044 "jensen_bound" geometryRow044_jensenBoundText
    geometryRowsTyped044.jensenBound geometryRow044_jensenBound_field geometryRow044_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_factorMaxima_before"
  err.flush

theorem geometryRow044_factorMaxima_read :
    rationalArrayField geometryRowsJson044 "factor_maxima" = .ok geometryRowsTyped044.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_gapWeightedMeans_before"
  err.flush

theorem geometryRow044_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson044 "gap_weighted_means" = .ok geometryRowsTyped044.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow044_floorChars : List Char := ['2', '7', '9', '2', '5', '7', '0', '1', '9', '1', '3', '0']
noncomputable def geometryRow044_floorText : String := String.ofList geometryRow044_floorChars

theorem geometryRow044_floor_text_read :
    geometryRowsJson044.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow044_floorText := by rfl

theorem geometryRow044_floor_chars_parse :
    SourceJson.intChars geometryRow044_floorChars = some (279257019130 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY01_TYPED Row_044_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock022 : List SourceJson := [geometryRowsJson043, geometryRowsJson044]
noncomputable def geometryRowsTypedBlock022 : List (GeometryRow) := [geometryRowsTyped043, geometryRowsTyped044]
noncomputable def geometryRowsTypedThroughBlock022 : List (GeometryRow) := geometryRowsTypedThroughBlock021 ++ geometryRowsTypedBlock022

theorem geometry_Rows_block_022_push_eq (acc : List SourceJson) :
    SimplicesBlock022.blockPush acc = [geometryRowsJson044, geometryRowsJson043] ++ acc := by rfl

theorem geometry_Rows_block_022_reverse (acc : List SourceJson) :
    (SimplicesBlock022.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock022 := by
  rw [geometry_Rows_block_022_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_022 :
    geometryRowsJsonBlock022.mapM decodeGeometryRow = .ok geometryRowsTypedBlock022 := by
  simp only [geometryRowsJsonBlock022, geometryRowsTypedBlock022, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_043, decode_geometry_Rows_044]
  rfl

theorem decode_geometry_Rows_through_block_022 :
    SimplicesValue.arrayAcc023.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock022 := by
  change (SimplicesBlock022.blockPush SimplicesValue.arrayAcc022).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_022_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_021, decode_geometry_Rows_block_022]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_022_complete"
  err.flush

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
#print axioms geometry_Rows_block_022_push_eq
#print axioms geometry_Rows_block_022_reverse
#print axioms decode_geometry_Rows_block_022
#print axioms decode_geometry_Rows_through_block_022

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
