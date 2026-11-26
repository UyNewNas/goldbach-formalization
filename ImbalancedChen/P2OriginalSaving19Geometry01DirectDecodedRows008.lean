import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows007

/-! Original simplices typed block 8, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson016 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped016 : GeometryRow :=
  { simplexId := 16,
    vertexIds := #[39, 35, 29, 28, 26, 17, 12, 2, 0],
    physicalVolume := ((17335097642232858571521534259147066084427373091 : ℚ) / (492124750856847360000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((281164776979 : ℚ) / (3393600000000 : ℚ)), ((1993146478693 : ℚ) / (23755200000000 : ℚ)), ((575116033827 : ℚ) / (3959200000000 : ℚ)), ((8351322506777 : ℚ) / (71265600000000 : ℚ)), ((1672140238961 : ℚ) / (23755200000000 : ℚ)), ((187223637733 : ℚ) / (3959200000000 : ℚ)), ((3430371336157 : ℚ) / (95020800000000 : ℚ)), ((1077740941229 : ℚ) / (31673600000000 : ℚ)), ((783658974503 : ℚ) / (23755200000000 : ℚ)), ((2150866872349 : ℚ) / (71265600000000 : ℚ))],
    jensenBound := ((2092518359252852026386969144205260137779381334025083188877534228295089968469505392640000000000000000000000000 : ℚ) / (12240047527320216761182068874304892740092317338190843695792212858581745286451803930401682515530129435054241388952490151 : ℚ)),
    jensenFloorQ96 := (13544586674269498002 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_simplexId_before"
  err.flush

theorem geometryRow016_simplexId_read :
    geometryRowsJson016.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped016.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_vertexIds_before"
  err.flush

theorem geometryRow016_vertexIds_read :
    geometryRowsJson016.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped016.vertexIds := by decide +kernel

noncomputable def geometryRow016_physicalVolumeNumeratorChars : List Char := ['1', '7', '3', '3', '5', '0', '9', '7', '6', '4', '2', '2', '3', '2', '8', '5', '8', '5', '7', '1', '5', '2', '1', '5', '3', '4', '2', '5', '9', '1', '4', '7', '0', '6', '6', '0', '8', '4', '4', '2', '7', '3', '7', '3', '0', '9', '1']
noncomputable def geometryRow016_physicalVolumeDenominatorChars : List Char := ['4', '9', '2', '1', '2', '4', '7', '5', '0', '8', '5', '6', '8', '4', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_physicalVolumeText : String := String.ofList (geometryRow016_physicalVolumeNumeratorChars ++ '/' :: geometryRow016_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_physicalVolume_before_field"
  err.flush

theorem geometryRow016_physicalVolume_field :
    geometryRowsJson016.getObjVal? "physical_volume" = .ok (.str geometryRow016_physicalVolumeText) := by rfl

theorem geometryRow016_physicalVolume_numerator_no_slash :
    geometryRow016_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeNumeratorChars = some (17335097642232858571521534259147066084427373091 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeDenominatorChars = some (492124750856847360000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_nonzero : (492124750856847360000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_physicalVolume_parse :
    parseRational geometryRow016_physicalVolumeText = .ok geometryRowsTyped016.physicalVolume :=
  original_rational_fraction_of_chars geometryRow016_physicalVolumeNumeratorChars geometryRow016_physicalVolumeDenominatorChars
    (17335097642232858571521534259147066084427373091 : Int) (492124750856847360000000000000000000000000000000000000000000000000 : Int)
    geometryRow016_physicalVolume_numerator_no_slash geometryRow016_physicalVolume_numerator_parse
    geometryRow016_physicalVolume_denominator_parse geometryRow016_physicalVolume_denominator_nonzero

theorem geometryRow016_physicalVolume_read :
    rationalField geometryRowsJson016 "physical_volume" = .ok geometryRowsTyped016.physicalVolume :=
  original_rationalField_of_string geometryRowsJson016 "physical_volume" geometryRow016_physicalVolumeText
    geometryRowsTyped016.physicalVolume geometryRow016_physicalVolume_field geometryRow016_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_physicalVolume_complete"
  err.flush

noncomputable def geometryRow016_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow016_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_meanGapText : String := String.ofList (geometryRow016_meanGapNumeratorChars ++ '/' :: geometryRow016_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_meanGap_before_field"
  err.flush

theorem geometryRow016_meanGap_field :
    geometryRowsJson016.getObjVal? "mean_gap" = .ok (.str geometryRow016_meanGapText) := by rfl

theorem geometryRow016_meanGap_numerator_no_slash :
    geometryRow016_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_meanGap_numerator_parse :
    SourceJson.intChars geometryRow016_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_parse :
    SourceJson.intChars geometryRow016_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_meanGap_parse :
    parseRational geometryRow016_meanGapText = .ok geometryRowsTyped016.meanGap :=
  original_rational_fraction_of_chars geometryRow016_meanGapNumeratorChars geometryRow016_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow016_meanGap_numerator_no_slash geometryRow016_meanGap_numerator_parse
    geometryRow016_meanGap_denominator_parse geometryRow016_meanGap_denominator_nonzero

theorem geometryRow016_meanGap_read :
    rationalField geometryRowsJson016 "mean_gap" = .ok geometryRowsTyped016.meanGap :=
  original_rationalField_of_string geometryRowsJson016 "mean_gap" geometryRow016_meanGapText
    geometryRowsTyped016.meanGap geometryRow016_meanGap_field geometryRow016_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_meanGap_complete"
  err.flush

noncomputable def geometryRow016_jensenBoundNumeratorChars : List Char := ['2', '0', '9', '2', '5', '1', '8', '3', '5', '9', '2', '5', '2', '8', '5', '2', '0', '2', '6', '3', '8', '6', '9', '6', '9', '1', '4', '4', '2', '0', '5', '2', '6', '0', '1', '3', '7', '7', '7', '9', '3', '8', '1', '3', '3', '4', '0', '2', '5', '0', '8', '3', '1', '8', '8', '8', '7', '7', '5', '3', '4', '2', '2', '8', '2', '9', '5', '0', '8', '9', '9', '6', '8', '4', '6', '9', '5', '0', '5', '3', '9', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_jensenBoundDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '4', '7', '5', '2', '7', '3', '2', '0', '2', '1', '6', '7', '6', '1', '1', '8', '2', '0', '6', '8', '8', '7', '4', '3', '0', '4', '8', '9', '2', '7', '4', '0', '0', '9', '2', '3', '1', '7', '3', '3', '8', '1', '9', '0', '8', '4', '3', '6', '9', '5', '7', '9', '2', '2', '1', '2', '8', '5', '8', '5', '8', '1', '7', '4', '5', '2', '8', '6', '4', '5', '1', '8', '0', '3', '9', '3', '0', '4', '0', '1', '6', '8', '2', '5', '1', '5', '5', '3', '0', '1', '2', '9', '4', '3', '5', '0', '5', '4', '2', '4', '1', '3', '8', '8', '9', '5', '2', '4', '9', '0', '1', '5', '1']
noncomputable def geometryRow016_jensenBoundText : String := String.ofList (geometryRow016_jensenBoundNumeratorChars ++ '/' :: geometryRow016_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_jensenBound_before_field"
  err.flush

theorem geometryRow016_jensenBound_field :
    geometryRowsJson016.getObjVal? "jensen_bound" = .ok (.str geometryRow016_jensenBoundText) := by rfl

theorem geometryRow016_jensenBound_numerator_no_slash :
    geometryRow016_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow016_jensenBoundNumeratorChars = some (2092518359252852026386969144205260137779381334025083188877534228295089968469505392640000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow016_jensenBoundDenominatorChars = some (12240047527320216761182068874304892740092317338190843695792212858581745286451803930401682515530129435054241388952490151 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_nonzero : (12240047527320216761182068874304892740092317338190843695792212858581745286451803930401682515530129435054241388952490151 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_jensenBound_parse :
    parseRational geometryRow016_jensenBoundText = .ok geometryRowsTyped016.jensenBound :=
  original_rational_fraction_of_chars geometryRow016_jensenBoundNumeratorChars geometryRow016_jensenBoundDenominatorChars
    (2092518359252852026386969144205260137779381334025083188877534228295089968469505392640000000000000000000000000 : Int) (12240047527320216761182068874304892740092317338190843695792212858581745286451803930401682515530129435054241388952490151 : Int)
    geometryRow016_jensenBound_numerator_no_slash geometryRow016_jensenBound_numerator_parse
    geometryRow016_jensenBound_denominator_parse geometryRow016_jensenBound_denominator_nonzero

theorem geometryRow016_jensenBound_read :
    rationalField geometryRowsJson016 "jensen_bound" = .ok geometryRowsTyped016.jensenBound :=
  original_rationalField_of_string geometryRowsJson016 "jensen_bound" geometryRow016_jensenBoundText
    geometryRowsTyped016.jensenBound geometryRow016_jensenBound_field geometryRow016_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_factorMaxima_before"
  err.flush

theorem geometryRow016_factorMaxima_read :
    rationalArrayField geometryRowsJson016 "factor_maxima" = .ok geometryRowsTyped016.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_gapWeightedMeans_before"
  err.flush

theorem geometryRow016_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson016 "gap_weighted_means" = .ok geometryRowsTyped016.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow016_floorChars : List Char := ['1', '3', '5', '4', '4', '5', '8', '6', '6', '7', '4', '2', '6', '9', '4', '9', '8', '0', '0', '2']
noncomputable def geometryRow016_floorText : String := String.ofList geometryRow016_floorChars

theorem geometryRow016_floor_text_read :
    geometryRowsJson016.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow016_floorText := by rfl

theorem geometryRow016_floor_chars_parse :
    SourceJson.intChars geometryRow016_floorChars = some (13544586674269498002 : Int) := by decide +kernel

theorem geometryRow016_floor_parse :
    parseInteger geometryRow016_floorText = .ok geometryRowsTyped016.jensenFloorQ96 := by
  simp only [geometryRow016_floorText, parseInteger, String.toList_ofList, geometryRow016_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_016 :
    decodeGeometryRow geometryRowsJson016 = .ok geometryRowsTyped016 :=
  original_geometryRow_of_fields geometryRowsJson016 geometryRowsTyped016 geometryRow016_floorText
    geometryRow016_simplexId_read geometryRow016_vertexIds_read
    geometryRow016_physicalVolume_read geometryRow016_meanGap_read
    geometryRow016_factorMaxima_read geometryRow016_gapWeightedMeans_read
    geometryRow016_jensenBound_read geometryRow016_floor_text_read geometryRow016_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_016_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson017 : SourceJson :=
  (SimplicesBlock008.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped017 : GeometryRow :=
  { simplexId := 17,
    vertexIds := #[39, 35, 29, 28, 26, 17, 12, 4, 2],
    physicalVolume := ((2709187762945799303464685743252700236729733569 : ℚ) / (364536852486553600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((591629 : ℚ) / (517440000 : ℚ)),
    factorMaxima := #[((1021879 : ℚ) / (11200000 : ℚ)), ((37827897 : ℚ) / (392000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((8952977 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((308977524751489861 : ℚ) / (3807805848000000000 : ℚ)), ((146932838364837829 : ℚ) / (1776976062400000000 : ℚ)), ((1944560206750621147 : ℚ) / (13327320468000000000 : ℚ)), ((635563803323061521 : ℚ) / (5330928187200000000 : ℚ)), ((379525189981269683 : ℚ) / (5330928187200000000 : ℚ)), ((40566305124778603 : ℚ) / (888488031200000000 : ℚ)), ((3840779012407146283 : ℚ) / (106618563744000000000 : ℚ)), ((1206522512749206811 : ℚ) / (35539521248000000000 : ℚ)), ((877236896339839577 : ℚ) / (26654640936000000000 : ℚ)), ((158730902118416701 : ℚ) / (5330928187200000000 : ℚ))],
    jensenBound := ((3205385670962363677969880456521980860705668108285626731872708365926381004824569627286341469879976802387062419638012724146034865734712240000000000000000000000000000000 : ℚ) / (42876777555392498140397367969145010557981264765907813162638852313779207642677663426071612977132066054161521243268126755506240689563622536547869129589415526833904894803442173619 : ℚ)),
    jensenFloorQ96 := (5922945504284076301 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_simplexId_before"
  err.flush

theorem geometryRow017_simplexId_read :
    geometryRowsJson017.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped017.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_vertexIds_before"
  err.flush

theorem geometryRow017_vertexIds_read :
    geometryRowsJson017.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped017.vertexIds := by decide +kernel

noncomputable def geometryRow017_physicalVolumeNumeratorChars : List Char := ['2', '7', '0', '9', '1', '8', '7', '7', '6', '2', '9', '4', '5', '7', '9', '9', '3', '0', '3', '4', '6', '4', '6', '8', '5', '7', '4', '3', '2', '5', '2', '7', '0', '0', '2', '3', '6', '7', '2', '9', '7', '3', '3', '5', '6', '9']
noncomputable def geometryRow017_physicalVolumeDenominatorChars : List Char := ['3', '6', '4', '5', '3', '6', '8', '5', '2', '4', '8', '6', '5', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_physicalVolumeText : String := String.ofList (geometryRow017_physicalVolumeNumeratorChars ++ '/' :: geometryRow017_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_physicalVolume_before_field"
  err.flush

theorem geometryRow017_physicalVolume_field :
    geometryRowsJson017.getObjVal? "physical_volume" = .ok (.str geometryRow017_physicalVolumeText) := by rfl

theorem geometryRow017_physicalVolume_numerator_no_slash :
    geometryRow017_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeNumeratorChars = some (2709187762945799303464685743252700236729733569 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeDenominatorChars = some (364536852486553600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_nonzero : (364536852486553600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_physicalVolume_parse :
    parseRational geometryRow017_physicalVolumeText = .ok geometryRowsTyped017.physicalVolume :=
  original_rational_fraction_of_chars geometryRow017_physicalVolumeNumeratorChars geometryRow017_physicalVolumeDenominatorChars
    (2709187762945799303464685743252700236729733569 : Int) (364536852486553600000000000000000000000000000000000000000000000000 : Int)
    geometryRow017_physicalVolume_numerator_no_slash geometryRow017_physicalVolume_numerator_parse
    geometryRow017_physicalVolume_denominator_parse geometryRow017_physicalVolume_denominator_nonzero

theorem geometryRow017_physicalVolume_read :
    rationalField geometryRowsJson017 "physical_volume" = .ok geometryRowsTyped017.physicalVolume :=
  original_rationalField_of_string geometryRowsJson017 "physical_volume" geometryRow017_physicalVolumeText
    geometryRowsTyped017.physicalVolume geometryRow017_physicalVolume_field geometryRow017_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_physicalVolume_complete"
  err.flush

noncomputable def geometryRow017_meanGapNumeratorChars : List Char := ['5', '9', '1', '6', '2', '9']
noncomputable def geometryRow017_meanGapDenominatorChars : List Char := ['5', '1', '7', '4', '4', '0', '0', '0', '0']
noncomputable def geometryRow017_meanGapText : String := String.ofList (geometryRow017_meanGapNumeratorChars ++ '/' :: geometryRow017_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_meanGap_before_field"
  err.flush

theorem geometryRow017_meanGap_field :
    geometryRowsJson017.getObjVal? "mean_gap" = .ok (.str geometryRow017_meanGapText) := by rfl

theorem geometryRow017_meanGap_numerator_no_slash :
    geometryRow017_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_meanGap_numerator_parse :
    SourceJson.intChars geometryRow017_meanGapNumeratorChars = some (591629 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_parse :
    SourceJson.intChars geometryRow017_meanGapDenominatorChars = some (517440000 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_nonzero : (517440000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_meanGap_parse :
    parseRational geometryRow017_meanGapText = .ok geometryRowsTyped017.meanGap :=
  original_rational_fraction_of_chars geometryRow017_meanGapNumeratorChars geometryRow017_meanGapDenominatorChars
    (591629 : Int) (517440000 : Int)
    geometryRow017_meanGap_numerator_no_slash geometryRow017_meanGap_numerator_parse
    geometryRow017_meanGap_denominator_parse geometryRow017_meanGap_denominator_nonzero

theorem geometryRow017_meanGap_read :
    rationalField geometryRowsJson017 "mean_gap" = .ok geometryRowsTyped017.meanGap :=
  original_rationalField_of_string geometryRowsJson017 "mean_gap" geometryRow017_meanGapText
    geometryRowsTyped017.meanGap geometryRow017_meanGap_field geometryRow017_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_meanGap_complete"
  err.flush

noncomputable def geometryRow017_jensenBoundNumeratorChars : List Char := ['3', '2', '0', '5', '3', '8', '5', '6', '7', '0', '9', '6', '2', '3', '6', '3', '6', '7', '7', '9', '6', '9', '8', '8', '0', '4', '5', '6', '5', '2', '1', '9', '8', '0', '8', '6', '0', '7', '0', '5', '6', '6', '8', '1', '0', '8', '2', '8', '5', '6', '2', '6', '7', '3', '1', '8', '7', '2', '7', '0', '8', '3', '6', '5', '9', '2', '6', '3', '8', '1', '0', '0', '4', '8', '2', '4', '5', '6', '9', '6', '2', '7', '2', '8', '6', '3', '4', '1', '4', '6', '9', '8', '7', '9', '9', '7', '6', '8', '0', '2', '3', '8', '7', '0', '6', '2', '4', '1', '9', '6', '3', '8', '0', '1', '2', '7', '2', '4', '1', '4', '6', '0', '3', '4', '8', '6', '5', '7', '3', '4', '7', '1', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_jensenBoundDenominatorChars : List Char := ['4', '2', '8', '7', '6', '7', '7', '7', '5', '5', '5', '3', '9', '2', '4', '9', '8', '1', '4', '0', '3', '9', '7', '3', '6', '7', '9', '6', '9', '1', '4', '5', '0', '1', '0', '5', '5', '7', '9', '8', '1', '2', '6', '4', '7', '6', '5', '9', '0', '7', '8', '1', '3', '1', '6', '2', '6', '3', '8', '8', '5', '2', '3', '1', '3', '7', '7', '9', '2', '0', '7', '6', '4', '2', '6', '7', '7', '6', '6', '3', '4', '2', '6', '0', '7', '1', '6', '1', '2', '9', '7', '7', '1', '3', '2', '0', '6', '6', '0', '5', '4', '1', '6', '1', '5', '2', '1', '2', '4', '3', '2', '6', '8', '1', '2', '6', '7', '5', '5', '5', '0', '6', '2', '4', '0', '6', '8', '9', '5', '6', '3', '6', '2', '2', '5', '3', '6', '5', '4', '7', '8', '6', '9', '1', '2', '9', '5', '8', '9', '4', '1', '5', '5', '2', '6', '8', '3', '3', '9', '0', '4', '8', '9', '4', '8', '0', '3', '4', '4', '2', '1', '7', '3', '6', '1', '9']
noncomputable def geometryRow017_jensenBoundText : String := String.ofList (geometryRow017_jensenBoundNumeratorChars ++ '/' :: geometryRow017_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_jensenBound_before_field"
  err.flush

theorem geometryRow017_jensenBound_field :
    geometryRowsJson017.getObjVal? "jensen_bound" = .ok (.str geometryRow017_jensenBoundText) := by rfl

theorem geometryRow017_jensenBound_numerator_no_slash :
    geometryRow017_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow017_jensenBoundNumeratorChars = some (3205385670962363677969880456521980860705668108285626731872708365926381004824569627286341469879976802387062419638012724146034865734712240000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow017_jensenBoundDenominatorChars = some (42876777555392498140397367969145010557981264765907813162638852313779207642677663426071612977132066054161521243268126755506240689563622536547869129589415526833904894803442173619 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_nonzero : (42876777555392498140397367969145010557981264765907813162638852313779207642677663426071612977132066054161521243268126755506240689563622536547869129589415526833904894803442173619 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_jensenBound_parse :
    parseRational geometryRow017_jensenBoundText = .ok geometryRowsTyped017.jensenBound :=
  original_rational_fraction_of_chars geometryRow017_jensenBoundNumeratorChars geometryRow017_jensenBoundDenominatorChars
    (3205385670962363677969880456521980860705668108285626731872708365926381004824569627286341469879976802387062419638012724146034865734712240000000000000000000000000000000 : Int) (42876777555392498140397367969145010557981264765907813162638852313779207642677663426071612977132066054161521243268126755506240689563622536547869129589415526833904894803442173619 : Int)
    geometryRow017_jensenBound_numerator_no_slash geometryRow017_jensenBound_numerator_parse
    geometryRow017_jensenBound_denominator_parse geometryRow017_jensenBound_denominator_nonzero

theorem geometryRow017_jensenBound_read :
    rationalField geometryRowsJson017 "jensen_bound" = .ok geometryRowsTyped017.jensenBound :=
  original_rationalField_of_string geometryRowsJson017 "jensen_bound" geometryRow017_jensenBoundText
    geometryRowsTyped017.jensenBound geometryRow017_jensenBound_field geometryRow017_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_factorMaxima_before"
  err.flush

theorem geometryRow017_factorMaxima_read :
    rationalArrayField geometryRowsJson017 "factor_maxima" = .ok geometryRowsTyped017.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_gapWeightedMeans_before"
  err.flush

theorem geometryRow017_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson017 "gap_weighted_means" = .ok geometryRowsTyped017.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow017_floorChars : List Char := ['5', '9', '2', '2', '9', '4', '5', '5', '0', '4', '2', '8', '4', '0', '7', '6', '3', '0', '1']
noncomputable def geometryRow017_floorText : String := String.ofList geometryRow017_floorChars

theorem geometryRow017_floor_text_read :
    geometryRowsJson017.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow017_floorText := by rfl

theorem geometryRow017_floor_chars_parse :
    SourceJson.intChars geometryRow017_floorChars = some (5922945504284076301 : Int) := by decide +kernel

theorem geometryRow017_floor_parse :
    parseInteger geometryRow017_floorText = .ok geometryRowsTyped017.jensenFloorQ96 := by
  simp only [geometryRow017_floorText, parseInteger, String.toList_ofList, geometryRow017_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_017 :
    decodeGeometryRow geometryRowsJson017 = .ok geometryRowsTyped017 :=
  original_geometryRow_of_fields geometryRowsJson017 geometryRowsTyped017 geometryRow017_floorText
    geometryRow017_simplexId_read geometryRow017_vertexIds_read
    geometryRow017_physicalVolume_read geometryRow017_meanGap_read
    geometryRow017_factorMaxima_read geometryRow017_gapWeightedMeans_read
    geometryRow017_jensenBound_read geometryRow017_floor_text_read geometryRow017_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_017_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock008 : List SourceJson := [geometryRowsJson016, geometryRowsJson017]
noncomputable def geometryRowsTypedBlock008 : List (GeometryRow) := [geometryRowsTyped016, geometryRowsTyped017]
noncomputable def geometryRowsTypedThroughBlock008 : List (GeometryRow) := geometryRowsTypedThroughBlock007 ++ geometryRowsTypedBlock008

theorem geometry_Rows_block_008_push_eq (acc : List SourceJson) :
    SimplicesBlock008.blockPush acc = [geometryRowsJson017, geometryRowsJson016] ++ acc := by rfl

theorem geometry_Rows_block_008_reverse (acc : List SourceJson) :
    (SimplicesBlock008.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock008 := by
  rw [geometry_Rows_block_008_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_008 :
    geometryRowsJsonBlock008.mapM decodeGeometryRow = .ok geometryRowsTypedBlock008 := by
  simp only [geometryRowsJsonBlock008, geometryRowsTypedBlock008, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_016, decode_geometry_Rows_017]
  rfl

theorem decode_geometry_Rows_through_block_008 :
    SimplicesValue.arrayAcc009.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock008 := by
  change (SimplicesBlock008.blockPush SimplicesValue.arrayAcc008).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_008_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_007, decode_geometry_Rows_block_008]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_008_complete"
  err.flush

#print axioms geometryRow016_simplexId_read
#print axioms geometryRow016_vertexIds_read
#print axioms geometryRow016_physicalVolume_field
#print axioms geometryRow016_physicalVolume_numerator_no_slash
#print axioms geometryRow016_physicalVolume_numerator_parse
#print axioms geometryRow016_physicalVolume_denominator_parse
#print axioms geometryRow016_physicalVolume_denominator_nonzero
#print axioms geometryRow016_physicalVolume_parse
#print axioms geometryRow016_physicalVolume_read
#print axioms geometryRow016_meanGap_field
#print axioms geometryRow016_meanGap_numerator_no_slash
#print axioms geometryRow016_meanGap_numerator_parse
#print axioms geometryRow016_meanGap_denominator_parse
#print axioms geometryRow016_meanGap_denominator_nonzero
#print axioms geometryRow016_meanGap_parse
#print axioms geometryRow016_meanGap_read
#print axioms geometryRow016_jensenBound_field
#print axioms geometryRow016_jensenBound_numerator_no_slash
#print axioms geometryRow016_jensenBound_numerator_parse
#print axioms geometryRow016_jensenBound_denominator_parse
#print axioms geometryRow016_jensenBound_denominator_nonzero
#print axioms geometryRow016_jensenBound_parse
#print axioms geometryRow016_jensenBound_read
#print axioms geometryRow016_factorMaxima_read
#print axioms geometryRow016_gapWeightedMeans_read
#print axioms geometryRow016_floor_text_read
#print axioms geometryRow016_floor_chars_parse
#print axioms geometryRow016_floor_parse
#print axioms decode_geometry_Rows_016
#print axioms geometryRow017_simplexId_read
#print axioms geometryRow017_vertexIds_read
#print axioms geometryRow017_physicalVolume_field
#print axioms geometryRow017_physicalVolume_numerator_no_slash
#print axioms geometryRow017_physicalVolume_numerator_parse
#print axioms geometryRow017_physicalVolume_denominator_parse
#print axioms geometryRow017_physicalVolume_denominator_nonzero
#print axioms geometryRow017_physicalVolume_parse
#print axioms geometryRow017_physicalVolume_read
#print axioms geometryRow017_meanGap_field
#print axioms geometryRow017_meanGap_numerator_no_slash
#print axioms geometryRow017_meanGap_numerator_parse
#print axioms geometryRow017_meanGap_denominator_parse
#print axioms geometryRow017_meanGap_denominator_nonzero
#print axioms geometryRow017_meanGap_parse
#print axioms geometryRow017_meanGap_read
#print axioms geometryRow017_jensenBound_field
#print axioms geometryRow017_jensenBound_numerator_no_slash
#print axioms geometryRow017_jensenBound_numerator_parse
#print axioms geometryRow017_jensenBound_denominator_parse
#print axioms geometryRow017_jensenBound_denominator_nonzero
#print axioms geometryRow017_jensenBound_parse
#print axioms geometryRow017_jensenBound_read
#print axioms geometryRow017_factorMaxima_read
#print axioms geometryRow017_gapWeightedMeans_read
#print axioms geometryRow017_floor_text_read
#print axioms geometryRow017_floor_chars_parse
#print axioms geometryRow017_floor_parse
#print axioms decode_geometry_Rows_017
#print axioms geometry_Rows_block_008_push_eq
#print axioms geometry_Rows_block_008_reverse
#print axioms decode_geometry_Rows_block_008
#print axioms decode_geometry_Rows_through_block_008

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
