import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows026

/-! Original simplices typed block 27, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson053 : SourceJson :=
  (SimplicesBlock027.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped053 : GeometryRow :=
  { simplexId := 53,
    vertexIds := #[39, 35, 24, 23, 19, 18, 15, 7, 0],
    physicalVolume := ((730025565328635287156335784781445703686440559 : ℚ) / (2821526149000907980800000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((4868625173203 : ℚ) / (66553200000000 : ℚ)), ((4883200300063 : ℚ) / (66553200000000 : ℚ)), ((29145281960171 : ℚ) / (199659600000000 : ℚ)), ((1770537211801 : ℚ) / (16638300000000 : ℚ)), ((11264808115843 : ℚ) / (199659600000000 : ℚ)), ((9719158203889 : ℚ) / (199659600000000 : ℚ)), ((448426670681 : ℚ) / (10508400000000 : ℚ)), ((8413494996719 : ℚ) / (199659600000000 : ℚ)), ((8360162502329 : ℚ) / (199659600000000 : ℚ)), ((7986685498919 : ℚ) / (199659600000000 : ℚ))],
    jensenBound := ((667760625288357009038345800748716279574047616625907581959554634395358753563908101016937500000000000000000000000 : ℚ) / (3657607890976603465061137345807195155377211365789005342719852679003385101086309740032574537115200277866307175049192375824207 : ℚ)),
    jensenFloorQ96 := (14464493985670685 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_simplexId_before"
  err.flush

theorem geometryRow053_simplexId_read :
    geometryRowsJson053.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped053.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_vertexIds_before"
  err.flush

theorem geometryRow053_vertexIds_read :
    geometryRowsJson053.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped053.vertexIds := by decide +kernel

noncomputable def geometryRow053_physicalVolumeNumeratorChars : List Char := ['7', '3', '0', '0', '2', '5', '5', '6', '5', '3', '2', '8', '6', '3', '5', '2', '8', '7', '1', '5', '6', '3', '3', '5', '7', '8', '4', '7', '8', '1', '4', '4', '5', '7', '0', '3', '6', '8', '6', '4', '4', '0', '5', '5', '9']
noncomputable def geometryRow053_physicalVolumeDenominatorChars : List Char := ['2', '8', '2', '1', '5', '2', '6', '1', '4', '9', '0', '0', '0', '9', '0', '7', '9', '8', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_physicalVolumeText : String := String.ofList (geometryRow053_physicalVolumeNumeratorChars ++ '/' :: geometryRow053_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_physicalVolume_before_field"
  err.flush

theorem geometryRow053_physicalVolume_field :
    geometryRowsJson053.getObjVal? "physical_volume" = .ok (.str geometryRow053_physicalVolumeText) := by rfl

theorem geometryRow053_physicalVolume_numerator_no_slash :
    geometryRow053_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeNumeratorChars = some (730025565328635287156335784781445703686440559 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeDenominatorChars = some (2821526149000907980800000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_nonzero : (2821526149000907980800000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_physicalVolume_parse :
    parseRational geometryRow053_physicalVolumeText = .ok geometryRowsTyped053.physicalVolume :=
  original_rational_fraction_of_chars geometryRow053_physicalVolumeNumeratorChars geometryRow053_physicalVolumeDenominatorChars
    (730025565328635287156335784781445703686440559 : Int) (2821526149000907980800000000000000000000000000000000000000000000000 : Int)
    geometryRow053_physicalVolume_numerator_no_slash geometryRow053_physicalVolume_numerator_parse
    geometryRow053_physicalVolume_denominator_parse geometryRow053_physicalVolume_denominator_nonzero

theorem geometryRow053_physicalVolume_read :
    rationalField geometryRowsJson053 "physical_volume" = .ok geometryRowsTyped053.physicalVolume :=
  original_rationalField_of_string geometryRowsJson053 "physical_volume" geometryRow053_physicalVolumeText
    geometryRowsTyped053.physicalVolume geometryRow053_physicalVolume_field geometryRow053_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_physicalVolume_complete"
  err.flush

noncomputable def geometryRow053_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow053_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_meanGapText : String := String.ofList (geometryRow053_meanGapNumeratorChars ++ '/' :: geometryRow053_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_meanGap_before_field"
  err.flush

theorem geometryRow053_meanGap_field :
    geometryRowsJson053.getObjVal? "mean_gap" = .ok (.str geometryRow053_meanGapText) := by rfl

theorem geometryRow053_meanGap_numerator_no_slash :
    geometryRow053_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_meanGap_numerator_parse :
    SourceJson.intChars geometryRow053_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_parse :
    SourceJson.intChars geometryRow053_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_meanGap_parse :
    parseRational geometryRow053_meanGapText = .ok geometryRowsTyped053.meanGap :=
  original_rational_fraction_of_chars geometryRow053_meanGapNumeratorChars geometryRow053_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow053_meanGap_numerator_no_slash geometryRow053_meanGap_numerator_parse
    geometryRow053_meanGap_denominator_parse geometryRow053_meanGap_denominator_nonzero

theorem geometryRow053_meanGap_read :
    rationalField geometryRowsJson053 "mean_gap" = .ok geometryRowsTyped053.meanGap :=
  original_rationalField_of_string geometryRowsJson053 "mean_gap" geometryRow053_meanGapText
    geometryRowsTyped053.meanGap geometryRow053_meanGap_field geometryRow053_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_meanGap_complete"
  err.flush

noncomputable def geometryRow053_jensenBoundNumeratorChars : List Char := ['6', '6', '7', '7', '6', '0', '6', '2', '5', '2', '8', '8', '3', '5', '7', '0', '0', '9', '0', '3', '8', '3', '4', '5', '8', '0', '0', '7', '4', '8', '7', '1', '6', '2', '7', '9', '5', '7', '4', '0', '4', '7', '6', '1', '6', '6', '2', '5', '9', '0', '7', '5', '8', '1', '9', '5', '9', '5', '5', '4', '6', '3', '4', '3', '9', '5', '3', '5', '8', '7', '5', '3', '5', '6', '3', '9', '0', '8', '1', '0', '1', '0', '1', '6', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_jensenBoundDenominatorChars : List Char := ['3', '6', '5', '7', '6', '0', '7', '8', '9', '0', '9', '7', '6', '6', '0', '3', '4', '6', '5', '0', '6', '1', '1', '3', '7', '3', '4', '5', '8', '0', '7', '1', '9', '5', '1', '5', '5', '3', '7', '7', '2', '1', '1', '3', '6', '5', '7', '8', '9', '0', '0', '5', '3', '4', '2', '7', '1', '9', '8', '5', '2', '6', '7', '9', '0', '0', '3', '3', '8', '5', '1', '0', '1', '0', '8', '6', '3', '0', '9', '7', '4', '0', '0', '3', '2', '5', '7', '4', '5', '3', '7', '1', '1', '5', '2', '0', '0', '2', '7', '7', '8', '6', '6', '3', '0', '7', '1', '7', '5', '0', '4', '9', '1', '9', '2', '3', '7', '5', '8', '2', '4', '2', '0', '7']
noncomputable def geometryRow053_jensenBoundText : String := String.ofList (geometryRow053_jensenBoundNumeratorChars ++ '/' :: geometryRow053_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_jensenBound_before_field"
  err.flush

theorem geometryRow053_jensenBound_field :
    geometryRowsJson053.getObjVal? "jensen_bound" = .ok (.str geometryRow053_jensenBoundText) := by rfl

theorem geometryRow053_jensenBound_numerator_no_slash :
    geometryRow053_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow053_jensenBoundNumeratorChars = some (667760625288357009038345800748716279574047616625907581959554634395358753563908101016937500000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow053_jensenBoundDenominatorChars = some (3657607890976603465061137345807195155377211365789005342719852679003385101086309740032574537115200277866307175049192375824207 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_nonzero : (3657607890976603465061137345807195155377211365789005342719852679003385101086309740032574537115200277866307175049192375824207 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_jensenBound_parse :
    parseRational geometryRow053_jensenBoundText = .ok geometryRowsTyped053.jensenBound :=
  original_rational_fraction_of_chars geometryRow053_jensenBoundNumeratorChars geometryRow053_jensenBoundDenominatorChars
    (667760625288357009038345800748716279574047616625907581959554634395358753563908101016937500000000000000000000000 : Int) (3657607890976603465061137345807195155377211365789005342719852679003385101086309740032574537115200277866307175049192375824207 : Int)
    geometryRow053_jensenBound_numerator_no_slash geometryRow053_jensenBound_numerator_parse
    geometryRow053_jensenBound_denominator_parse geometryRow053_jensenBound_denominator_nonzero

theorem geometryRow053_jensenBound_read :
    rationalField geometryRowsJson053 "jensen_bound" = .ok geometryRowsTyped053.jensenBound :=
  original_rationalField_of_string geometryRowsJson053 "jensen_bound" geometryRow053_jensenBoundText
    geometryRowsTyped053.jensenBound geometryRow053_jensenBound_field geometryRow053_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_factorMaxima_before"
  err.flush

theorem geometryRow053_factorMaxima_read :
    rationalArrayField geometryRowsJson053 "factor_maxima" = .ok geometryRowsTyped053.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_gapWeightedMeans_before"
  err.flush

theorem geometryRow053_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson053 "gap_weighted_means" = .ok geometryRowsTyped053.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow053_floorChars : List Char := ['1', '4', '4', '6', '4', '4', '9', '3', '9', '8', '5', '6', '7', '0', '6', '8', '5']
noncomputable def geometryRow053_floorText : String := String.ofList geometryRow053_floorChars

theorem geometryRow053_floor_text_read :
    geometryRowsJson053.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow053_floorText := by rfl

theorem geometryRow053_floor_chars_parse :
    SourceJson.intChars geometryRow053_floorChars = some (14464493985670685 : Int) := by decide +kernel

theorem geometryRow053_floor_parse :
    parseInteger geometryRow053_floorText = .ok geometryRowsTyped053.jensenFloorQ96 := by
  simp only [geometryRow053_floorText, parseInteger, String.toList_ofList, geometryRow053_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_053 :
    decodeGeometryRow geometryRowsJson053 = .ok geometryRowsTyped053 :=
  original_geometryRow_of_fields geometryRowsJson053 geometryRowsTyped053 geometryRow053_floorText
    geometryRow053_simplexId_read geometryRow053_vertexIds_read
    geometryRow053_physicalVolume_read geometryRow053_meanGap_read
    geometryRow053_factorMaxima_read geometryRow053_gapWeightedMeans_read
    geometryRow053_jensenBound_read geometryRow053_floor_text_read geometryRow053_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_053_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson054 : SourceJson :=
  (SimplicesBlock027.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped054 : GeometryRow :=
  { simplexId := 54,
    vertexIds := #[39, 35, 24, 23, 19, 18, 15, 14, 7],
    physicalVolume := ((309240539844221578632517082648754174148038211 : ℚ) / (9875341521503177932800000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608819 : ℚ) / (5004000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((403117 : ℚ) / (7200000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((41563040269 : ℚ) / (594225000000 : ℚ)), ((166772701321 : ℚ) / (2376900000000 : ℚ)), ((2097060473089 : ℚ) / (14261400000000 : ℚ)), ((3565192788287 : ℚ) / (33276600000000 : ℚ)), ((345351357899 : ℚ) / (6239362500000 : ℚ)), ((678970967201 : ℚ) / (14261400000000 : ℚ)), ((229833458053 : ℚ) / (5254200000000 : ℚ)), ((4313529829897 : ℚ) / (99829800000000 : ℚ)), ((2143431791351 : ℚ) / (49914900000000 : ℚ)), ((2013884993471 : ℚ) / (49914900000000 : ℚ))],
    jensenBound := ((242372315960123792044032081523349438077826764361084305559081897268420365339045518398284912109375000000 : ℚ) / (10610706593665451309463276433143342453051076514326196542721895295180881740777620166546643707142618896222473424376073 : ℚ)),
    jensenFloorQ96 := (1809748772933864 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_simplexId_before"
  err.flush

theorem geometryRow054_simplexId_read :
    geometryRowsJson054.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped054.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_vertexIds_before"
  err.flush

theorem geometryRow054_vertexIds_read :
    geometryRowsJson054.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped054.vertexIds := by decide +kernel

noncomputable def geometryRow054_physicalVolumeNumeratorChars : List Char := ['3', '0', '9', '2', '4', '0', '5', '3', '9', '8', '4', '4', '2', '2', '1', '5', '7', '8', '6', '3', '2', '5', '1', '7', '0', '8', '2', '6', '4', '8', '7', '5', '4', '1', '7', '4', '1', '4', '8', '0', '3', '8', '2', '1', '1']
noncomputable def geometryRow054_physicalVolumeDenominatorChars : List Char := ['9', '8', '7', '5', '3', '4', '1', '5', '2', '1', '5', '0', '3', '1', '7', '7', '9', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_physicalVolumeText : String := String.ofList (geometryRow054_physicalVolumeNumeratorChars ++ '/' :: geometryRow054_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_physicalVolume_before_field"
  err.flush

theorem geometryRow054_physicalVolume_field :
    geometryRowsJson054.getObjVal? "physical_volume" = .ok (.str geometryRow054_physicalVolumeText) := by rfl

theorem geometryRow054_physicalVolume_numerator_no_slash :
    geometryRow054_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeNumeratorChars = some (309240539844221578632517082648754174148038211 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeDenominatorChars = some (9875341521503177932800000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_nonzero : (9875341521503177932800000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_physicalVolume_parse :
    parseRational geometryRow054_physicalVolumeText = .ok geometryRowsTyped054.physicalVolume :=
  original_rational_fraction_of_chars geometryRow054_physicalVolumeNumeratorChars geometryRow054_physicalVolumeDenominatorChars
    (309240539844221578632517082648754174148038211 : Int) (9875341521503177932800000000000000000000000000000000000000000000000 : Int)
    geometryRow054_physicalVolume_numerator_no_slash geometryRow054_physicalVolume_numerator_parse
    geometryRow054_physicalVolume_denominator_parse geometryRow054_physicalVolume_denominator_nonzero

theorem geometryRow054_physicalVolume_read :
    rationalField geometryRowsJson054 "physical_volume" = .ok geometryRowsTyped054.physicalVolume :=
  original_rationalField_of_string geometryRowsJson054 "physical_volume" geometryRow054_physicalVolumeText
    geometryRowsTyped054.physicalVolume geometryRow054_physicalVolume_field geometryRow054_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_physicalVolume_complete"
  err.flush

noncomputable def geometryRow054_meanGapNumeratorChars : List Char := ['6', '0', '8', '8', '1', '9']
noncomputable def geometryRow054_meanGapDenominatorChars : List Char := ['5', '0', '0', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_meanGapText : String := String.ofList (geometryRow054_meanGapNumeratorChars ++ '/' :: geometryRow054_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_meanGap_before_field"
  err.flush

theorem geometryRow054_meanGap_field :
    geometryRowsJson054.getObjVal? "mean_gap" = .ok (.str geometryRow054_meanGapText) := by rfl

theorem geometryRow054_meanGap_numerator_no_slash :
    geometryRow054_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_meanGap_numerator_parse :
    SourceJson.intChars geometryRow054_meanGapNumeratorChars = some (608819 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_parse :
    SourceJson.intChars geometryRow054_meanGapDenominatorChars = some (5004000000 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_nonzero : (5004000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_meanGap_parse :
    parseRational geometryRow054_meanGapText = .ok geometryRowsTyped054.meanGap :=
  original_rational_fraction_of_chars geometryRow054_meanGapNumeratorChars geometryRow054_meanGapDenominatorChars
    (608819 : Int) (5004000000 : Int)
    geometryRow054_meanGap_numerator_no_slash geometryRow054_meanGap_numerator_parse
    geometryRow054_meanGap_denominator_parse geometryRow054_meanGap_denominator_nonzero

theorem geometryRow054_meanGap_read :
    rationalField geometryRowsJson054 "mean_gap" = .ok geometryRowsTyped054.meanGap :=
  original_rationalField_of_string geometryRowsJson054 "mean_gap" geometryRow054_meanGapText
    geometryRowsTyped054.meanGap geometryRow054_meanGap_field geometryRow054_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_meanGap_complete"
  err.flush

noncomputable def geometryRow054_jensenBoundNumeratorChars : List Char := ['2', '4', '2', '3', '7', '2', '3', '1', '5', '9', '6', '0', '1', '2', '3', '7', '9', '2', '0', '4', '4', '0', '3', '2', '0', '8', '1', '5', '2', '3', '3', '4', '9', '4', '3', '8', '0', '7', '7', '8', '2', '6', '7', '6', '4', '3', '6', '1', '0', '8', '4', '3', '0', '5', '5', '5', '9', '0', '8', '1', '8', '9', '7', '2', '6', '8', '4', '2', '0', '3', '6', '5', '3', '3', '9', '0', '4', '5', '5', '1', '8', '3', '9', '8', '2', '8', '4', '9', '1', '2', '1', '0', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_jensenBoundDenominatorChars : List Char := ['1', '0', '6', '1', '0', '7', '0', '6', '5', '9', '3', '6', '6', '5', '4', '5', '1', '3', '0', '9', '4', '6', '3', '2', '7', '6', '4', '3', '3', '1', '4', '3', '3', '4', '2', '4', '5', '3', '0', '5', '1', '0', '7', '6', '5', '1', '4', '3', '2', '6', '1', '9', '6', '5', '4', '2', '7', '2', '1', '8', '9', '5', '2', '9', '5', '1', '8', '0', '8', '8', '1', '7', '4', '0', '7', '7', '7', '6', '2', '0', '1', '6', '6', '5', '4', '6', '6', '4', '3', '7', '0', '7', '1', '4', '2', '6', '1', '8', '8', '9', '6', '2', '2', '2', '4', '7', '3', '4', '2', '4', '3', '7', '6', '0', '7', '3']
noncomputable def geometryRow054_jensenBoundText : String := String.ofList (geometryRow054_jensenBoundNumeratorChars ++ '/' :: geometryRow054_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_jensenBound_before_field"
  err.flush

theorem geometryRow054_jensenBound_field :
    geometryRowsJson054.getObjVal? "jensen_bound" = .ok (.str geometryRow054_jensenBoundText) := by rfl

theorem geometryRow054_jensenBound_numerator_no_slash :
    geometryRow054_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow054_jensenBoundNumeratorChars = some (242372315960123792044032081523349438077826764361084305559081897268420365339045518398284912109375000000 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow054_jensenBoundDenominatorChars = some (10610706593665451309463276433143342453051076514326196542721895295180881740777620166546643707142618896222473424376073 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_nonzero : (10610706593665451309463276433143342453051076514326196542721895295180881740777620166546643707142618896222473424376073 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_jensenBound_parse :
    parseRational geometryRow054_jensenBoundText = .ok geometryRowsTyped054.jensenBound :=
  original_rational_fraction_of_chars geometryRow054_jensenBoundNumeratorChars geometryRow054_jensenBoundDenominatorChars
    (242372315960123792044032081523349438077826764361084305559081897268420365339045518398284912109375000000 : Int) (10610706593665451309463276433143342453051076514326196542721895295180881740777620166546643707142618896222473424376073 : Int)
    geometryRow054_jensenBound_numerator_no_slash geometryRow054_jensenBound_numerator_parse
    geometryRow054_jensenBound_denominator_parse geometryRow054_jensenBound_denominator_nonzero

theorem geometryRow054_jensenBound_read :
    rationalField geometryRowsJson054 "jensen_bound" = .ok geometryRowsTyped054.jensenBound :=
  original_rationalField_of_string geometryRowsJson054 "jensen_bound" geometryRow054_jensenBoundText
    geometryRowsTyped054.jensenBound geometryRow054_jensenBound_field geometryRow054_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_factorMaxima_before"
  err.flush

theorem geometryRow054_factorMaxima_read :
    rationalArrayField geometryRowsJson054 "factor_maxima" = .ok geometryRowsTyped054.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_gapWeightedMeans_before"
  err.flush

theorem geometryRow054_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson054 "gap_weighted_means" = .ok geometryRowsTyped054.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow054_floorChars : List Char := ['1', '8', '0', '9', '7', '4', '8', '7', '7', '2', '9', '3', '3', '8', '6', '4']
noncomputable def geometryRow054_floorText : String := String.ofList geometryRow054_floorChars

theorem geometryRow054_floor_text_read :
    geometryRowsJson054.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow054_floorText := by rfl

theorem geometryRow054_floor_chars_parse :
    SourceJson.intChars geometryRow054_floorChars = some (1809748772933864 : Int) := by decide +kernel

theorem geometryRow054_floor_parse :
    parseInteger geometryRow054_floorText = .ok geometryRowsTyped054.jensenFloorQ96 := by
  simp only [geometryRow054_floorText, parseInteger, String.toList_ofList, geometryRow054_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_054 :
    decodeGeometryRow geometryRowsJson054 = .ok geometryRowsTyped054 :=
  original_geometryRow_of_fields geometryRowsJson054 geometryRowsTyped054 geometryRow054_floorText
    geometryRow054_simplexId_read geometryRow054_vertexIds_read
    geometryRow054_physicalVolume_read geometryRow054_meanGap_read
    geometryRow054_factorMaxima_read geometryRow054_gapWeightedMeans_read
    geometryRow054_jensenBound_read geometryRow054_floor_text_read geometryRow054_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_054_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock027 : List SourceJson := [geometryRowsJson053, geometryRowsJson054]
noncomputable def geometryRowsTypedBlock027 : List (GeometryRow) := [geometryRowsTyped053, geometryRowsTyped054]
noncomputable def geometryRowsTypedThroughBlock027 : List (GeometryRow) := geometryRowsTypedThroughBlock026 ++ geometryRowsTypedBlock027

theorem geometry_Rows_block_027_push_eq (acc : List SourceJson) :
    SimplicesBlock027.blockPush acc = [geometryRowsJson054, geometryRowsJson053] ++ acc := by rfl

theorem geometry_Rows_block_027_reverse (acc : List SourceJson) :
    (SimplicesBlock027.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock027 := by
  rw [geometry_Rows_block_027_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_027 :
    geometryRowsJsonBlock027.mapM decodeGeometryRow = .ok geometryRowsTypedBlock027 := by
  simp only [geometryRowsJsonBlock027, geometryRowsTypedBlock027, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_053, decode_geometry_Rows_054]
  rfl

theorem decode_geometry_Rows_through_block_027 :
    SimplicesValue.arrayAcc028.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock027 := by
  change (SimplicesBlock027.blockPush SimplicesValue.arrayAcc027).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_027_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_026, decode_geometry_Rows_block_027]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_027_complete"
  err.flush

#print axioms geometryRow053_simplexId_read
#print axioms geometryRow053_vertexIds_read
#print axioms geometryRow053_physicalVolume_field
#print axioms geometryRow053_physicalVolume_numerator_no_slash
#print axioms geometryRow053_physicalVolume_numerator_parse
#print axioms geometryRow053_physicalVolume_denominator_parse
#print axioms geometryRow053_physicalVolume_denominator_nonzero
#print axioms geometryRow053_physicalVolume_parse
#print axioms geometryRow053_physicalVolume_read
#print axioms geometryRow053_meanGap_field
#print axioms geometryRow053_meanGap_numerator_no_slash
#print axioms geometryRow053_meanGap_numerator_parse
#print axioms geometryRow053_meanGap_denominator_parse
#print axioms geometryRow053_meanGap_denominator_nonzero
#print axioms geometryRow053_meanGap_parse
#print axioms geometryRow053_meanGap_read
#print axioms geometryRow053_jensenBound_field
#print axioms geometryRow053_jensenBound_numerator_no_slash
#print axioms geometryRow053_jensenBound_numerator_parse
#print axioms geometryRow053_jensenBound_denominator_parse
#print axioms geometryRow053_jensenBound_denominator_nonzero
#print axioms geometryRow053_jensenBound_parse
#print axioms geometryRow053_jensenBound_read
#print axioms geometryRow053_factorMaxima_read
#print axioms geometryRow053_gapWeightedMeans_read
#print axioms geometryRow053_floor_text_read
#print axioms geometryRow053_floor_chars_parse
#print axioms geometryRow053_floor_parse
#print axioms decode_geometry_Rows_053
#print axioms geometryRow054_simplexId_read
#print axioms geometryRow054_vertexIds_read
#print axioms geometryRow054_physicalVolume_field
#print axioms geometryRow054_physicalVolume_numerator_no_slash
#print axioms geometryRow054_physicalVolume_numerator_parse
#print axioms geometryRow054_physicalVolume_denominator_parse
#print axioms geometryRow054_physicalVolume_denominator_nonzero
#print axioms geometryRow054_physicalVolume_parse
#print axioms geometryRow054_physicalVolume_read
#print axioms geometryRow054_meanGap_field
#print axioms geometryRow054_meanGap_numerator_no_slash
#print axioms geometryRow054_meanGap_numerator_parse
#print axioms geometryRow054_meanGap_denominator_parse
#print axioms geometryRow054_meanGap_denominator_nonzero
#print axioms geometryRow054_meanGap_parse
#print axioms geometryRow054_meanGap_read
#print axioms geometryRow054_jensenBound_field
#print axioms geometryRow054_jensenBound_numerator_no_slash
#print axioms geometryRow054_jensenBound_numerator_parse
#print axioms geometryRow054_jensenBound_denominator_parse
#print axioms geometryRow054_jensenBound_denominator_nonzero
#print axioms geometryRow054_jensenBound_parse
#print axioms geometryRow054_jensenBound_read
#print axioms geometryRow054_factorMaxima_read
#print axioms geometryRow054_gapWeightedMeans_read
#print axioms geometryRow054_floor_text_read
#print axioms geometryRow054_floor_chars_parse
#print axioms geometryRow054_floor_parse
#print axioms decode_geometry_Rows_054
#print axioms geometry_Rows_block_027_push_eq
#print axioms geometry_Rows_block_027_reverse
#print axioms decode_geometry_Rows_block_027
#print axioms decode_geometry_Rows_through_block_027

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
