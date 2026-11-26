import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows056

/-! Original simplices typed block 57, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson112 : SourceJson :=
  (SimplicesBlock057.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped112 : GeometryRow :=
  { simplexId := 112,
    vertexIds := #[39, 37, 36, 30, 24, 23, 21, 20, 16],
    physicalVolume := ((103159613413852084588461053050868326921207 : ℚ) / (94396029472851886080000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((5577817 : ℚ) / (108000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((70502874089887 : ℚ) / (917021700000000 : ℚ)), ((17668526206543 : ℚ) / (229255425000000 : ℚ)), ((275948884190431 : ℚ) / (1834043400000000 : ℚ)), ((600223006766267 : ℚ) / (5502130200000000 : ℚ)), ((43997472087313 : ℚ) / (917021700000000 : ℚ)), ((81336589233623 : ℚ) / (1834043400000000 : ℚ)), ((2481422071391 : ℚ) / (57917160000000 : ℚ)), ((46559427566651 : ℚ) / (1100426040000000 : ℚ)), ((114845076259103 : ℚ) / (2751065100000000 : ℚ)), ((114844709450423 : ℚ) / (2751065100000000 : ℚ))],
    jensenBound := ((780448687894138060209971088862070415298555811920501715826394569597330310794247602795213025573077956323242187500000000000 : ℚ) / (1125106814200830717320211926988197042716653241674828189422445272673221326960798228714462286698872727501933499485618264542163481638353197047 : ℚ)),
    jensenFloorQ96 := (54957906838 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_simplexId_before"
  err.flush

theorem geometryRow112_simplexId_read :
    geometryRowsJson112.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped112.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_vertexIds_before"
  err.flush

theorem geometryRow112_vertexIds_read :
    geometryRowsJson112.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped112.vertexIds := by decide +kernel

noncomputable def geometryRow112_physicalVolumeNumeratorChars : List Char := ['1', '0', '3', '1', '5', '9', '6', '1', '3', '4', '1', '3', '8', '5', '2', '0', '8', '4', '5', '8', '8', '4', '6', '1', '0', '5', '3', '0', '5', '0', '8', '6', '8', '3', '2', '6', '9', '2', '1', '2', '0', '7']
noncomputable def geometryRow112_physicalVolumeDenominatorChars : List Char := ['9', '4', '3', '9', '6', '0', '2', '9', '4', '7', '2', '8', '5', '1', '8', '8', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow112_physicalVolumeText : String := String.ofList (geometryRow112_physicalVolumeNumeratorChars ++ '/' :: geometryRow112_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_physicalVolume_before_field"
  err.flush

theorem geometryRow112_physicalVolume_field :
    geometryRowsJson112.getObjVal? "physical_volume" = .ok (.str geometryRow112_physicalVolumeText) := by rfl

theorem geometryRow112_physicalVolume_numerator_no_slash :
    geometryRow112_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow112_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow112_physicalVolumeNumeratorChars = some (103159613413852084588461053050868326921207 : Int) := by decide +kernel

theorem geometryRow112_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow112_physicalVolumeDenominatorChars = some (94396029472851886080000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow112_physicalVolume_denominator_nonzero : (94396029472851886080000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow112_physicalVolume_parse :
    parseRational geometryRow112_physicalVolumeText = .ok geometryRowsTyped112.physicalVolume :=
  original_rational_fraction_of_chars geometryRow112_physicalVolumeNumeratorChars geometryRow112_physicalVolumeDenominatorChars
    (103159613413852084588461053050868326921207 : Int) (94396029472851886080000000000000000000000000000000000000000000000000 : Int)
    geometryRow112_physicalVolume_numerator_no_slash geometryRow112_physicalVolume_numerator_parse
    geometryRow112_physicalVolume_denominator_parse geometryRow112_physicalVolume_denominator_nonzero

theorem geometryRow112_physicalVolume_read :
    rationalField geometryRowsJson112 "physical_volume" = .ok geometryRowsTyped112.physicalVolume :=
  original_rationalField_of_string geometryRowsJson112 "physical_volume" geometryRow112_physicalVolumeText
    geometryRowsTyped112.physicalVolume geometryRow112_physicalVolume_field geometryRow112_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_physicalVolume_complete"
  err.flush

noncomputable def geometryRow112_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow112_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow112_meanGapText : String := String.ofList (geometryRow112_meanGapNumeratorChars ++ '/' :: geometryRow112_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_meanGap_before_field"
  err.flush

theorem geometryRow112_meanGap_field :
    geometryRowsJson112.getObjVal? "mean_gap" = .ok (.str geometryRow112_meanGapText) := by rfl

theorem geometryRow112_meanGap_numerator_no_slash :
    geometryRow112_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow112_meanGap_numerator_parse :
    SourceJson.intChars geometryRow112_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow112_meanGap_denominator_parse :
    SourceJson.intChars geometryRow112_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow112_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow112_meanGap_parse :
    parseRational geometryRow112_meanGapText = .ok geometryRowsTyped112.meanGap :=
  original_rational_fraction_of_chars geometryRow112_meanGapNumeratorChars geometryRow112_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow112_meanGap_numerator_no_slash geometryRow112_meanGap_numerator_parse
    geometryRow112_meanGap_denominator_parse geometryRow112_meanGap_denominator_nonzero

theorem geometryRow112_meanGap_read :
    rationalField geometryRowsJson112 "mean_gap" = .ok geometryRowsTyped112.meanGap :=
  original_rationalField_of_string geometryRowsJson112 "mean_gap" geometryRow112_meanGapText
    geometryRowsTyped112.meanGap geometryRow112_meanGap_field geometryRow112_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_meanGap_complete"
  err.flush

noncomputable def geometryRow112_jensenBoundNumeratorChars : List Char := ['7', '8', '0', '4', '4', '8', '6', '8', '7', '8', '9', '4', '1', '3', '8', '0', '6', '0', '2', '0', '9', '9', '7', '1', '0', '8', '8', '8', '6', '2', '0', '7', '0', '4', '1', '5', '2', '9', '8', '5', '5', '5', '8', '1', '1', '9', '2', '0', '5', '0', '1', '7', '1', '5', '8', '2', '6', '3', '9', '4', '5', '6', '9', '5', '9', '7', '3', '3', '0', '3', '1', '0', '7', '9', '4', '2', '4', '7', '6', '0', '2', '7', '9', '5', '2', '1', '3', '0', '2', '5', '5', '7', '3', '0', '7', '7', '9', '5', '6', '3', '2', '3', '2', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow112_jensenBoundDenominatorChars : List Char := ['1', '1', '2', '5', '1', '0', '6', '8', '1', '4', '2', '0', '0', '8', '3', '0', '7', '1', '7', '3', '2', '0', '2', '1', '1', '9', '2', '6', '9', '8', '8', '1', '9', '7', '0', '4', '2', '7', '1', '6', '6', '5', '3', '2', '4', '1', '6', '7', '4', '8', '2', '8', '1', '8', '9', '4', '2', '2', '4', '4', '5', '2', '7', '2', '6', '7', '3', '2', '2', '1', '3', '2', '6', '9', '6', '0', '7', '9', '8', '2', '2', '8', '7', '1', '4', '4', '6', '2', '2', '8', '6', '6', '9', '8', '8', '7', '2', '7', '2', '7', '5', '0', '1', '9', '3', '3', '4', '9', '9', '4', '8', '5', '6', '1', '8', '2', '6', '4', '5', '4', '2', '1', '6', '3', '4', '8', '1', '6', '3', '8', '3', '5', '3', '1', '9', '7', '0', '4', '7']
noncomputable def geometryRow112_jensenBoundText : String := String.ofList (geometryRow112_jensenBoundNumeratorChars ++ '/' :: geometryRow112_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_jensenBound_before_field"
  err.flush

theorem geometryRow112_jensenBound_field :
    geometryRowsJson112.getObjVal? "jensen_bound" = .ok (.str geometryRow112_jensenBoundText) := by rfl

theorem geometryRow112_jensenBound_numerator_no_slash :
    geometryRow112_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow112_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow112_jensenBoundNumeratorChars = some (780448687894138060209971088862070415298555811920501715826394569597330310794247602795213025573077956323242187500000000000 : Int) := by decide +kernel

theorem geometryRow112_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow112_jensenBoundDenominatorChars = some (1125106814200830717320211926988197042716653241674828189422445272673221326960798228714462286698872727501933499485618264542163481638353197047 : Int) := by decide +kernel

theorem geometryRow112_jensenBound_denominator_nonzero : (1125106814200830717320211926988197042716653241674828189422445272673221326960798228714462286698872727501933499485618264542163481638353197047 : Int) ≠ 0 := by decide +kernel

theorem geometryRow112_jensenBound_parse :
    parseRational geometryRow112_jensenBoundText = .ok geometryRowsTyped112.jensenBound :=
  original_rational_fraction_of_chars geometryRow112_jensenBoundNumeratorChars geometryRow112_jensenBoundDenominatorChars
    (780448687894138060209971088862070415298555811920501715826394569597330310794247602795213025573077956323242187500000000000 : Int) (1125106814200830717320211926988197042716653241674828189422445272673221326960798228714462286698872727501933499485618264542163481638353197047 : Int)
    geometryRow112_jensenBound_numerator_no_slash geometryRow112_jensenBound_numerator_parse
    geometryRow112_jensenBound_denominator_parse geometryRow112_jensenBound_denominator_nonzero

theorem geometryRow112_jensenBound_read :
    rationalField geometryRowsJson112 "jensen_bound" = .ok geometryRowsTyped112.jensenBound :=
  original_rationalField_of_string geometryRowsJson112 "jensen_bound" geometryRow112_jensenBoundText
    geometryRowsTyped112.jensenBound geometryRow112_jensenBound_field geometryRow112_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_factorMaxima_before"
  err.flush

theorem geometryRow112_factorMaxima_read :
    rationalArrayField geometryRowsJson112 "factor_maxima" = .ok geometryRowsTyped112.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_gapWeightedMeans_before"
  err.flush

theorem geometryRow112_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson112 "gap_weighted_means" = .ok geometryRowsTyped112.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow112_floorChars : List Char := ['5', '4', '9', '5', '7', '9', '0', '6', '8', '3', '8']
noncomputable def geometryRow112_floorText : String := String.ofList geometryRow112_floorChars

theorem geometryRow112_floor_text_read :
    geometryRowsJson112.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow112_floorText := by rfl

theorem geometryRow112_floor_chars_parse :
    SourceJson.intChars geometryRow112_floorChars = some (54957906838 : Int) := by decide +kernel

theorem geometryRow112_floor_parse :
    parseInteger geometryRow112_floorText = .ok geometryRowsTyped112.jensenFloorQ96 := by
  simp only [geometryRow112_floorText, parseInteger, String.toList_ofList, geometryRow112_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_112 :
    decodeGeometryRow geometryRowsJson112 = .ok geometryRowsTyped112 :=
  original_geometryRow_of_fields geometryRowsJson112 geometryRowsTyped112 geometryRow112_floorText
    geometryRow112_simplexId_read geometryRow112_vertexIds_read
    geometryRow112_physicalVolume_read geometryRow112_meanGap_read
    geometryRow112_factorMaxima_read geometryRow112_gapWeightedMeans_read
    geometryRow112_jensenBound_read geometryRow112_floor_text_read geometryRow112_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_112_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson113 : SourceJson :=
  (SimplicesBlock057.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped113 : GeometryRow :=
  { simplexId := 113,
    vertexIds := #[39, 37, 31, 24, 23, 19, 18, 15, 14],
    physicalVolume := ((502792965912092746638810425136945175161702953 : ℚ) / (21330737686446864334848000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2484443 : ℚ) / (42000000 : ℚ)), ((734331 : ℚ) / (14000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((140550843019 : ℚ) / (1901520000000 : ℚ)), ((28193455043 : ℚ) / (380304000000 : ℚ)), ((282371939477 : ℚ) / (1901520000000 : ℚ)), ((1069986562957 : ℚ) / (9982980000000 : ℚ)), ((665416082563 : ℚ) / (13310640000000 : ℚ)), ((17553117179 : ℚ) / (380304000000 : ℚ)), ((91888254119 : ℚ) / (2101680000000 : ℚ)), ((1724554479017 : ℚ) / (39931920000000 : ℚ)), ((1713887980139 : ℚ) / (39931920000000 : ℚ)), ((1667434493261 : ℚ) / (39931920000000 : ℚ))],
    jensenBound := ((5614492346092765418892623300823223972205860934294507298220035222723979508057720659200000000000000000 : ℚ) / (333306430990618085892730828175108419506050370547075147565189869027088162402395772152345072143027618421419192731243 : ℚ)),
    jensenFloorQ96 := (1334585446519187 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_simplexId_before"
  err.flush

theorem geometryRow113_simplexId_read :
    geometryRowsJson113.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped113.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_vertexIds_before"
  err.flush

theorem geometryRow113_vertexIds_read :
    geometryRowsJson113.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped113.vertexIds := by decide +kernel

noncomputable def geometryRow113_physicalVolumeNumeratorChars : List Char := ['5', '0', '2', '7', '9', '2', '9', '6', '5', '9', '1', '2', '0', '9', '2', '7', '4', '6', '6', '3', '8', '8', '1', '0', '4', '2', '5', '1', '3', '6', '9', '4', '5', '1', '7', '5', '1', '6', '1', '7', '0', '2', '9', '5', '3']
noncomputable def geometryRow113_physicalVolumeDenominatorChars : List Char := ['2', '1', '3', '3', '0', '7', '3', '7', '6', '8', '6', '4', '4', '6', '8', '6', '4', '3', '3', '4', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow113_physicalVolumeText : String := String.ofList (geometryRow113_physicalVolumeNumeratorChars ++ '/' :: geometryRow113_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_physicalVolume_before_field"
  err.flush

theorem geometryRow113_physicalVolume_field :
    geometryRowsJson113.getObjVal? "physical_volume" = .ok (.str geometryRow113_physicalVolumeText) := by rfl

theorem geometryRow113_physicalVolume_numerator_no_slash :
    geometryRow113_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow113_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow113_physicalVolumeNumeratorChars = some (502792965912092746638810425136945175161702953 : Int) := by decide +kernel

theorem geometryRow113_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow113_physicalVolumeDenominatorChars = some (21330737686446864334848000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow113_physicalVolume_denominator_nonzero : (21330737686446864334848000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow113_physicalVolume_parse :
    parseRational geometryRow113_physicalVolumeText = .ok geometryRowsTyped113.physicalVolume :=
  original_rational_fraction_of_chars geometryRow113_physicalVolumeNumeratorChars geometryRow113_physicalVolumeDenominatorChars
    (502792965912092746638810425136945175161702953 : Int) (21330737686446864334848000000000000000000000000000000000000000000000 : Int)
    geometryRow113_physicalVolume_numerator_no_slash geometryRow113_physicalVolume_numerator_parse
    geometryRow113_physicalVolume_denominator_parse geometryRow113_physicalVolume_denominator_nonzero

theorem geometryRow113_physicalVolume_read :
    rationalField geometryRowsJson113 "physical_volume" = .ok geometryRowsTyped113.physicalVolume :=
  original_rationalField_of_string geometryRowsJson113 "physical_volume" geometryRow113_physicalVolumeText
    geometryRowsTyped113.physicalVolume geometryRow113_physicalVolume_field geometryRow113_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_physicalVolume_complete"
  err.flush

noncomputable def geometryRow113_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow113_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow113_meanGapText : String := String.ofList (geometryRow113_meanGapNumeratorChars ++ '/' :: geometryRow113_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_meanGap_before_field"
  err.flush

theorem geometryRow113_meanGap_field :
    geometryRowsJson113.getObjVal? "mean_gap" = .ok (.str geometryRow113_meanGapText) := by rfl

theorem geometryRow113_meanGap_numerator_no_slash :
    geometryRow113_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow113_meanGap_numerator_parse :
    SourceJson.intChars geometryRow113_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow113_meanGap_denominator_parse :
    SourceJson.intChars geometryRow113_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow113_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow113_meanGap_parse :
    parseRational geometryRow113_meanGapText = .ok geometryRowsTyped113.meanGap :=
  original_rational_fraction_of_chars geometryRow113_meanGapNumeratorChars geometryRow113_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow113_meanGap_numerator_no_slash geometryRow113_meanGap_numerator_parse
    geometryRow113_meanGap_denominator_parse geometryRow113_meanGap_denominator_nonzero

theorem geometryRow113_meanGap_read :
    rationalField geometryRowsJson113 "mean_gap" = .ok geometryRowsTyped113.meanGap :=
  original_rationalField_of_string geometryRowsJson113 "mean_gap" geometryRow113_meanGapText
    geometryRowsTyped113.meanGap geometryRow113_meanGap_field geometryRow113_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_meanGap_complete"
  err.flush

noncomputable def geometryRow113_jensenBoundNumeratorChars : List Char := ['5', '6', '1', '4', '4', '9', '2', '3', '4', '6', '0', '9', '2', '7', '6', '5', '4', '1', '8', '8', '9', '2', '6', '2', '3', '3', '0', '0', '8', '2', '3', '2', '2', '3', '9', '7', '2', '2', '0', '5', '8', '6', '0', '9', '3', '4', '2', '9', '4', '5', '0', '7', '2', '9', '8', '2', '2', '0', '0', '3', '5', '2', '2', '2', '7', '2', '3', '9', '7', '9', '5', '0', '8', '0', '5', '7', '7', '2', '0', '6', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow113_jensenBoundDenominatorChars : List Char := ['3', '3', '3', '3', '0', '6', '4', '3', '0', '9', '9', '0', '6', '1', '8', '0', '8', '5', '8', '9', '2', '7', '3', '0', '8', '2', '8', '1', '7', '5', '1', '0', '8', '4', '1', '9', '5', '0', '6', '0', '5', '0', '3', '7', '0', '5', '4', '7', '0', '7', '5', '1', '4', '7', '5', '6', '5', '1', '8', '9', '8', '6', '9', '0', '2', '7', '0', '8', '8', '1', '6', '2', '4', '0', '2', '3', '9', '5', '7', '7', '2', '1', '5', '2', '3', '4', '5', '0', '7', '2', '1', '4', '3', '0', '2', '7', '6', '1', '8', '4', '2', '1', '4', '1', '9', '1', '9', '2', '7', '3', '1', '2', '4', '3']
noncomputable def geometryRow113_jensenBoundText : String := String.ofList (geometryRow113_jensenBoundNumeratorChars ++ '/' :: geometryRow113_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_jensenBound_before_field"
  err.flush

theorem geometryRow113_jensenBound_field :
    geometryRowsJson113.getObjVal? "jensen_bound" = .ok (.str geometryRow113_jensenBoundText) := by rfl

theorem geometryRow113_jensenBound_numerator_no_slash :
    geometryRow113_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow113_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow113_jensenBoundNumeratorChars = some (5614492346092765418892623300823223972205860934294507298220035222723979508057720659200000000000000000 : Int) := by decide +kernel

theorem geometryRow113_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow113_jensenBoundDenominatorChars = some (333306430990618085892730828175108419506050370547075147565189869027088162402395772152345072143027618421419192731243 : Int) := by decide +kernel

theorem geometryRow113_jensenBound_denominator_nonzero : (333306430990618085892730828175108419506050370547075147565189869027088162402395772152345072143027618421419192731243 : Int) ≠ 0 := by decide +kernel

theorem geometryRow113_jensenBound_parse :
    parseRational geometryRow113_jensenBoundText = .ok geometryRowsTyped113.jensenBound :=
  original_rational_fraction_of_chars geometryRow113_jensenBoundNumeratorChars geometryRow113_jensenBoundDenominatorChars
    (5614492346092765418892623300823223972205860934294507298220035222723979508057720659200000000000000000 : Int) (333306430990618085892730828175108419506050370547075147565189869027088162402395772152345072143027618421419192731243 : Int)
    geometryRow113_jensenBound_numerator_no_slash geometryRow113_jensenBound_numerator_parse
    geometryRow113_jensenBound_denominator_parse geometryRow113_jensenBound_denominator_nonzero

theorem geometryRow113_jensenBound_read :
    rationalField geometryRowsJson113 "jensen_bound" = .ok geometryRowsTyped113.jensenBound :=
  original_rationalField_of_string geometryRowsJson113 "jensen_bound" geometryRow113_jensenBoundText
    geometryRowsTyped113.jensenBound geometryRow113_jensenBound_field geometryRow113_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_factorMaxima_before"
  err.flush

theorem geometryRow113_factorMaxima_read :
    rationalArrayField geometryRowsJson113 "factor_maxima" = .ok geometryRowsTyped113.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_gapWeightedMeans_before"
  err.flush

theorem geometryRow113_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson113 "gap_weighted_means" = .ok geometryRowsTyped113.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow113_floorChars : List Char := ['1', '3', '3', '4', '5', '8', '5', '4', '4', '6', '5', '1', '9', '1', '8', '7']
noncomputable def geometryRow113_floorText : String := String.ofList geometryRow113_floorChars

theorem geometryRow113_floor_text_read :
    geometryRowsJson113.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow113_floorText := by rfl

theorem geometryRow113_floor_chars_parse :
    SourceJson.intChars geometryRow113_floorChars = some (1334585446519187 : Int) := by decide +kernel

theorem geometryRow113_floor_parse :
    parseInteger geometryRow113_floorText = .ok geometryRowsTyped113.jensenFloorQ96 := by
  simp only [geometryRow113_floorText, parseInteger, String.toList_ofList, geometryRow113_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_113 :
    decodeGeometryRow geometryRowsJson113 = .ok geometryRowsTyped113 :=
  original_geometryRow_of_fields geometryRowsJson113 geometryRowsTyped113 geometryRow113_floorText
    geometryRow113_simplexId_read geometryRow113_vertexIds_read
    geometryRow113_physicalVolume_read geometryRow113_meanGap_read
    geometryRow113_factorMaxima_read geometryRow113_gapWeightedMeans_read
    geometryRow113_jensenBound_read geometryRow113_floor_text_read geometryRow113_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_113_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock057 : List SourceJson := [geometryRowsJson112, geometryRowsJson113]
noncomputable def geometryRowsTypedBlock057 : List (GeometryRow) := [geometryRowsTyped112, geometryRowsTyped113]
noncomputable def geometryRowsTypedThroughBlock057 : List (GeometryRow) := geometryRowsTypedThroughBlock056 ++ geometryRowsTypedBlock057

theorem geometry_Rows_block_057_push_eq (acc : List SourceJson) :
    SimplicesBlock057.blockPush acc = [geometryRowsJson113, geometryRowsJson112] ++ acc := by rfl

theorem geometry_Rows_block_057_reverse (acc : List SourceJson) :
    (SimplicesBlock057.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock057 := by
  rw [geometry_Rows_block_057_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_057 :
    geometryRowsJsonBlock057.mapM decodeGeometryRow = .ok geometryRowsTypedBlock057 := by
  simp only [geometryRowsJsonBlock057, geometryRowsTypedBlock057, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_112, decode_geometry_Rows_113]
  rfl

theorem decode_geometry_Rows_through_block_057 :
    SimplicesValue.arrayAcc058.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock057 := by
  change (SimplicesBlock057.blockPush SimplicesValue.arrayAcc057).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_057_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_056, decode_geometry_Rows_block_057]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_057_complete"
  err.flush

#print axioms geometryRow112_simplexId_read
#print axioms geometryRow112_vertexIds_read
#print axioms geometryRow112_physicalVolume_field
#print axioms geometryRow112_physicalVolume_numerator_no_slash
#print axioms geometryRow112_physicalVolume_numerator_parse
#print axioms geometryRow112_physicalVolume_denominator_parse
#print axioms geometryRow112_physicalVolume_denominator_nonzero
#print axioms geometryRow112_physicalVolume_parse
#print axioms geometryRow112_physicalVolume_read
#print axioms geometryRow112_meanGap_field
#print axioms geometryRow112_meanGap_numerator_no_slash
#print axioms geometryRow112_meanGap_numerator_parse
#print axioms geometryRow112_meanGap_denominator_parse
#print axioms geometryRow112_meanGap_denominator_nonzero
#print axioms geometryRow112_meanGap_parse
#print axioms geometryRow112_meanGap_read
#print axioms geometryRow112_jensenBound_field
#print axioms geometryRow112_jensenBound_numerator_no_slash
#print axioms geometryRow112_jensenBound_numerator_parse
#print axioms geometryRow112_jensenBound_denominator_parse
#print axioms geometryRow112_jensenBound_denominator_nonzero
#print axioms geometryRow112_jensenBound_parse
#print axioms geometryRow112_jensenBound_read
#print axioms geometryRow112_factorMaxima_read
#print axioms geometryRow112_gapWeightedMeans_read
#print axioms geometryRow112_floor_text_read
#print axioms geometryRow112_floor_chars_parse
#print axioms geometryRow112_floor_parse
#print axioms decode_geometry_Rows_112
#print axioms geometryRow113_simplexId_read
#print axioms geometryRow113_vertexIds_read
#print axioms geometryRow113_physicalVolume_field
#print axioms geometryRow113_physicalVolume_numerator_no_slash
#print axioms geometryRow113_physicalVolume_numerator_parse
#print axioms geometryRow113_physicalVolume_denominator_parse
#print axioms geometryRow113_physicalVolume_denominator_nonzero
#print axioms geometryRow113_physicalVolume_parse
#print axioms geometryRow113_physicalVolume_read
#print axioms geometryRow113_meanGap_field
#print axioms geometryRow113_meanGap_numerator_no_slash
#print axioms geometryRow113_meanGap_numerator_parse
#print axioms geometryRow113_meanGap_denominator_parse
#print axioms geometryRow113_meanGap_denominator_nonzero
#print axioms geometryRow113_meanGap_parse
#print axioms geometryRow113_meanGap_read
#print axioms geometryRow113_jensenBound_field
#print axioms geometryRow113_jensenBound_numerator_no_slash
#print axioms geometryRow113_jensenBound_numerator_parse
#print axioms geometryRow113_jensenBound_denominator_parse
#print axioms geometryRow113_jensenBound_denominator_nonzero
#print axioms geometryRow113_jensenBound_parse
#print axioms geometryRow113_jensenBound_read
#print axioms geometryRow113_factorMaxima_read
#print axioms geometryRow113_gapWeightedMeans_read
#print axioms geometryRow113_floor_text_read
#print axioms geometryRow113_floor_chars_parse
#print axioms geometryRow113_floor_parse
#print axioms decode_geometry_Rows_113
#print axioms geometry_Rows_block_057_push_eq
#print axioms geometry_Rows_block_057_reverse
#print axioms decode_geometry_Rows_block_057
#print axioms decode_geometry_Rows_through_block_057

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
