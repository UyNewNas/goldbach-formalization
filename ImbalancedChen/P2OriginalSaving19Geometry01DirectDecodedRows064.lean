import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows063

/-! Original simplices typed block 64, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson126 : SourceJson :=
  (SimplicesBlock064.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped126 : GeometryRow :=
  { simplexId := 126,
    vertexIds := #[39, 38, 34, 24, 23, 21, 8, 3, 1],
    physicalVolume := ((144629603547265604705821507183384938421 : ℚ) / (861274238976000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((257548093063 : ℚ) / (3157648000000 : ℚ)), ((1303699868411 : ℚ) / (15788240000000 : ℚ)), ((533993145199 : ℚ) / (3643440000000 : ℚ)), ((4423224554383 : ℚ) / (39470600000000 : ℚ)), ((276329246707 : ℚ) / (4643600000000 : ℚ)), ((10878601947481 : ℚ) / (236823600000000 : ℚ)), ((486762909041 : ℚ) / (12464400000000 : ℚ)), ((9122039155759 : ℚ) / (236823600000000 : ℚ)), ((8649478639957 : ℚ) / (236823600000000 : ℚ)), ((8649462851717 : ℚ) / (236823600000000 : ℚ))],
    jensenBound := ((176246476237954557589376513380665268073478748145032190071035060376861135584056287928320000000000000000000 : ℚ) / (283481330034396411316427795722587439061698861260235485740255803654732371109989955834081266467999726825715237160568856711 : ℚ)),
    jensenFloorQ96 := (49257862802650 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_simplexId_before"
  err.flush

theorem geometryRow126_simplexId_read :
    geometryRowsJson126.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped126.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_vertexIds_before"
  err.flush

theorem geometryRow126_vertexIds_read :
    geometryRowsJson126.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped126.vertexIds := by decide +kernel

noncomputable def geometryRow126_physicalVolumeNumeratorChars : List Char := ['1', '4', '4', '6', '2', '9', '6', '0', '3', '5', '4', '7', '2', '6', '5', '6', '0', '4', '7', '0', '5', '8', '2', '1', '5', '0', '7', '1', '8', '3', '3', '8', '4', '9', '3', '8', '4', '2', '1']
noncomputable def geometryRow126_physicalVolumeDenominatorChars : List Char := ['8', '6', '1', '2', '7', '4', '2', '3', '8', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow126_physicalVolumeText : String := String.ofList (geometryRow126_physicalVolumeNumeratorChars ++ '/' :: geometryRow126_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_physicalVolume_before_field"
  err.flush

theorem geometryRow126_physicalVolume_field :
    geometryRowsJson126.getObjVal? "physical_volume" = .ok (.str geometryRow126_physicalVolumeText) := by rfl

theorem geometryRow126_physicalVolume_numerator_no_slash :
    geometryRow126_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow126_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow126_physicalVolumeNumeratorChars = some (144629603547265604705821507183384938421 : Int) := by decide +kernel

theorem geometryRow126_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow126_physicalVolumeDenominatorChars = some (861274238976000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow126_physicalVolume_denominator_nonzero : (861274238976000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow126_physicalVolume_parse :
    parseRational geometryRow126_physicalVolumeText = .ok geometryRowsTyped126.physicalVolume :=
  original_rational_fraction_of_chars geometryRow126_physicalVolumeNumeratorChars geometryRow126_physicalVolumeDenominatorChars
    (144629603547265604705821507183384938421 : Int) (861274238976000000000000000000000000000000000000000000000000000 : Int)
    geometryRow126_physicalVolume_numerator_no_slash geometryRow126_physicalVolume_numerator_parse
    geometryRow126_physicalVolume_denominator_parse geometryRow126_physicalVolume_denominator_nonzero

theorem geometryRow126_physicalVolume_read :
    rationalField geometryRowsJson126 "physical_volume" = .ok geometryRowsTyped126.physicalVolume :=
  original_rationalField_of_string geometryRowsJson126 "physical_volume" geometryRow126_physicalVolumeText
    geometryRowsTyped126.physicalVolume geometryRow126_physicalVolume_field geometryRow126_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_physicalVolume_complete"
  err.flush

noncomputable def geometryRow126_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow126_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow126_meanGapText : String := String.ofList (geometryRow126_meanGapNumeratorChars ++ '/' :: geometryRow126_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_meanGap_before_field"
  err.flush

theorem geometryRow126_meanGap_field :
    geometryRowsJson126.getObjVal? "mean_gap" = .ok (.str geometryRow126_meanGapText) := by rfl

theorem geometryRow126_meanGap_numerator_no_slash :
    geometryRow126_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow126_meanGap_numerator_parse :
    SourceJson.intChars geometryRow126_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow126_meanGap_denominator_parse :
    SourceJson.intChars geometryRow126_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow126_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow126_meanGap_parse :
    parseRational geometryRow126_meanGapText = .ok geometryRowsTyped126.meanGap :=
  original_rational_fraction_of_chars geometryRow126_meanGapNumeratorChars geometryRow126_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow126_meanGap_numerator_no_slash geometryRow126_meanGap_numerator_parse
    geometryRow126_meanGap_denominator_parse geometryRow126_meanGap_denominator_nonzero

theorem geometryRow126_meanGap_read :
    rationalField geometryRowsJson126 "mean_gap" = .ok geometryRowsTyped126.meanGap :=
  original_rationalField_of_string geometryRowsJson126 "mean_gap" geometryRow126_meanGapText
    geometryRowsTyped126.meanGap geometryRow126_meanGap_field geometryRow126_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_meanGap_complete"
  err.flush

noncomputable def geometryRow126_jensenBoundNumeratorChars : List Char := ['1', '7', '6', '2', '4', '6', '4', '7', '6', '2', '3', '7', '9', '5', '4', '5', '5', '7', '5', '8', '9', '3', '7', '6', '5', '1', '3', '3', '8', '0', '6', '6', '5', '2', '6', '8', '0', '7', '3', '4', '7', '8', '7', '4', '8', '1', '4', '5', '0', '3', '2', '1', '9', '0', '0', '7', '1', '0', '3', '5', '0', '6', '0', '3', '7', '6', '8', '6', '1', '1', '3', '5', '5', '8', '4', '0', '5', '6', '2', '8', '7', '9', '2', '8', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow126_jensenBoundDenominatorChars : List Char := ['2', '8', '3', '4', '8', '1', '3', '3', '0', '0', '3', '4', '3', '9', '6', '4', '1', '1', '3', '1', '6', '4', '2', '7', '7', '9', '5', '7', '2', '2', '5', '8', '7', '4', '3', '9', '0', '6', '1', '6', '9', '8', '8', '6', '1', '2', '6', '0', '2', '3', '5', '4', '8', '5', '7', '4', '0', '2', '5', '5', '8', '0', '3', '6', '5', '4', '7', '3', '2', '3', '7', '1', '1', '0', '9', '9', '8', '9', '9', '5', '5', '8', '3', '4', '0', '8', '1', '2', '6', '6', '4', '6', '7', '9', '9', '9', '7', '2', '6', '8', '2', '5', '7', '1', '5', '2', '3', '7', '1', '6', '0', '5', '6', '8', '8', '5', '6', '7', '1', '1']
noncomputable def geometryRow126_jensenBoundText : String := String.ofList (geometryRow126_jensenBoundNumeratorChars ++ '/' :: geometryRow126_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_jensenBound_before_field"
  err.flush

theorem geometryRow126_jensenBound_field :
    geometryRowsJson126.getObjVal? "jensen_bound" = .ok (.str geometryRow126_jensenBoundText) := by rfl

theorem geometryRow126_jensenBound_numerator_no_slash :
    geometryRow126_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow126_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow126_jensenBoundNumeratorChars = some (176246476237954557589376513380665268073478748145032190071035060376861135584056287928320000000000000000000 : Int) := by decide +kernel

theorem geometryRow126_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow126_jensenBoundDenominatorChars = some (283481330034396411316427795722587439061698861260235485740255803654732371109989955834081266467999726825715237160568856711 : Int) := by decide +kernel

theorem geometryRow126_jensenBound_denominator_nonzero : (283481330034396411316427795722587439061698861260235485740255803654732371109989955834081266467999726825715237160568856711 : Int) ≠ 0 := by decide +kernel

theorem geometryRow126_jensenBound_parse :
    parseRational geometryRow126_jensenBoundText = .ok geometryRowsTyped126.jensenBound :=
  original_rational_fraction_of_chars geometryRow126_jensenBoundNumeratorChars geometryRow126_jensenBoundDenominatorChars
    (176246476237954557589376513380665268073478748145032190071035060376861135584056287928320000000000000000000 : Int) (283481330034396411316427795722587439061698861260235485740255803654732371109989955834081266467999726825715237160568856711 : Int)
    geometryRow126_jensenBound_numerator_no_slash geometryRow126_jensenBound_numerator_parse
    geometryRow126_jensenBound_denominator_parse geometryRow126_jensenBound_denominator_nonzero

theorem geometryRow126_jensenBound_read :
    rationalField geometryRowsJson126 "jensen_bound" = .ok geometryRowsTyped126.jensenBound :=
  original_rationalField_of_string geometryRowsJson126 "jensen_bound" geometryRow126_jensenBoundText
    geometryRowsTyped126.jensenBound geometryRow126_jensenBound_field geometryRow126_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_factorMaxima_before"
  err.flush

theorem geometryRow126_factorMaxima_read :
    rationalArrayField geometryRowsJson126 "factor_maxima" = .ok geometryRowsTyped126.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_gapWeightedMeans_before"
  err.flush

theorem geometryRow126_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson126 "gap_weighted_means" = .ok geometryRowsTyped126.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow126_floorChars : List Char := ['4', '9', '2', '5', '7', '8', '6', '2', '8', '0', '2', '6', '5', '0']
noncomputable def geometryRow126_floorText : String := String.ofList geometryRow126_floorChars

theorem geometryRow126_floor_text_read :
    geometryRowsJson126.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow126_floorText := by rfl

theorem geometryRow126_floor_chars_parse :
    SourceJson.intChars geometryRow126_floorChars = some (49257862802650 : Int) := by decide +kernel

theorem geometryRow126_floor_parse :
    parseInteger geometryRow126_floorText = .ok geometryRowsTyped126.jensenFloorQ96 := by
  simp only [geometryRow126_floorText, parseInteger, String.toList_ofList, geometryRow126_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_126 :
    decodeGeometryRow geometryRowsJson126 = .ok geometryRowsTyped126 :=
  original_geometryRow_of_fields geometryRowsJson126 geometryRowsTyped126 geometryRow126_floorText
    geometryRow126_simplexId_read geometryRow126_vertexIds_read
    geometryRow126_physicalVolume_read geometryRow126_meanGap_read
    geometryRow126_factorMaxima_read geometryRow126_gapWeightedMeans_read
    geometryRow126_jensenBound_read geometryRow126_floor_text_read geometryRow126_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_126_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson127 : SourceJson :=
  (SimplicesBlock064.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped127 : GeometryRow :=
  { simplexId := 127,
    vertexIds := #[39, 38, 34, 24, 23, 21, 20, 3, 1],
    physicalVolume := ((56210357688836989290852209123351321764681 : ℚ) / (1684652411437056000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((66369109 : ℚ) / (99756000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((1424531403638327073 : ℚ) / (18197291892280000000 : ℚ)), ((27425659725985007629 : ℚ) / (345748545953320000000 : ℚ)), ((12724915246298310981 : ℚ) / (86437136488330000000 : ℚ)), ((24020819425225229741 : ℚ) / (216092841220825000000 : ℚ)), ((8946810067761630059 : ℚ) / (152536123214700000000 : ℚ)), ((39661886196677825433 : ℚ) / (864371364883300000000 : ℚ)), ((206441113217566047547 : ℚ) / (5186228189299800000000 : ℚ)), ((203671835689429957937 : ℚ) / (5186228189299800000000 : ℚ)), ((24724107310390186907 : ℚ) / (648278523662475000000 : ℚ)), ((4120677348636990457 : ℚ) / (108046420610412500000 : ℚ))],
    jensenBound := ((98280013219604648750581919281192618279101963489594676987807857685681922561036386411212925872417581552921443837632194120564937362883715622989331554435484308123318481445312500000 : ℚ) / (688249353323524076935699120181052577818959651072680950079073327303018833699378859085445043849818346798024039767028407672759878310740041030762520770164282056477925705984965016540378494716259213 : ℚ)),
    jensenFloorQ96 := (11313552016672 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_simplexId_before"
  err.flush

theorem geometryRow127_simplexId_read :
    geometryRowsJson127.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped127.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_vertexIds_before"
  err.flush

theorem geometryRow127_vertexIds_read :
    geometryRowsJson127.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped127.vertexIds := by decide +kernel

noncomputable def geometryRow127_physicalVolumeNumeratorChars : List Char := ['5', '6', '2', '1', '0', '3', '5', '7', '6', '8', '8', '8', '3', '6', '9', '8', '9', '2', '9', '0', '8', '5', '2', '2', '0', '9', '1', '2', '3', '3', '5', '1', '3', '2', '1', '7', '6', '4', '6', '8', '1']
noncomputable def geometryRow127_physicalVolumeDenominatorChars : List Char := ['1', '6', '8', '4', '6', '5', '2', '4', '1', '1', '4', '3', '7', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow127_physicalVolumeText : String := String.ofList (geometryRow127_physicalVolumeNumeratorChars ++ '/' :: geometryRow127_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_physicalVolume_before_field"
  err.flush

theorem geometryRow127_physicalVolume_field :
    geometryRowsJson127.getObjVal? "physical_volume" = .ok (.str geometryRow127_physicalVolumeText) := by rfl

theorem geometryRow127_physicalVolume_numerator_no_slash :
    geometryRow127_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow127_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow127_physicalVolumeNumeratorChars = some (56210357688836989290852209123351321764681 : Int) := by decide +kernel

theorem geometryRow127_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow127_physicalVolumeDenominatorChars = some (1684652411437056000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow127_physicalVolume_denominator_nonzero : (1684652411437056000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow127_physicalVolume_parse :
    parseRational geometryRow127_physicalVolumeText = .ok geometryRowsTyped127.physicalVolume :=
  original_rational_fraction_of_chars geometryRow127_physicalVolumeNumeratorChars geometryRow127_physicalVolumeDenominatorChars
    (56210357688836989290852209123351321764681 : Int) (1684652411437056000000000000000000000000000000000000000000000000000 : Int)
    geometryRow127_physicalVolume_numerator_no_slash geometryRow127_physicalVolume_numerator_parse
    geometryRow127_physicalVolume_denominator_parse geometryRow127_physicalVolume_denominator_nonzero

theorem geometryRow127_physicalVolume_read :
    rationalField geometryRowsJson127 "physical_volume" = .ok geometryRowsTyped127.physicalVolume :=
  original_rationalField_of_string geometryRowsJson127 "physical_volume" geometryRow127_physicalVolumeText
    geometryRowsTyped127.physicalVolume geometryRow127_physicalVolume_field geometryRow127_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_physicalVolume_complete"
  err.flush

noncomputable def geometryRow127_meanGapNumeratorChars : List Char := ['6', '6', '3', '6', '9', '1', '0', '9']
noncomputable def geometryRow127_meanGapDenominatorChars : List Char := ['9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow127_meanGapText : String := String.ofList (geometryRow127_meanGapNumeratorChars ++ '/' :: geometryRow127_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_meanGap_before_field"
  err.flush

theorem geometryRow127_meanGap_field :
    geometryRowsJson127.getObjVal? "mean_gap" = .ok (.str geometryRow127_meanGapText) := by rfl

theorem geometryRow127_meanGap_numerator_no_slash :
    geometryRow127_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow127_meanGap_numerator_parse :
    SourceJson.intChars geometryRow127_meanGapNumeratorChars = some (66369109 : Int) := by decide +kernel

theorem geometryRow127_meanGap_denominator_parse :
    SourceJson.intChars geometryRow127_meanGapDenominatorChars = some (99756000000 : Int) := by decide +kernel

theorem geometryRow127_meanGap_denominator_nonzero : (99756000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow127_meanGap_parse :
    parseRational geometryRow127_meanGapText = .ok geometryRowsTyped127.meanGap :=
  original_rational_fraction_of_chars geometryRow127_meanGapNumeratorChars geometryRow127_meanGapDenominatorChars
    (66369109 : Int) (99756000000 : Int)
    geometryRow127_meanGap_numerator_no_slash geometryRow127_meanGap_numerator_parse
    geometryRow127_meanGap_denominator_parse geometryRow127_meanGap_denominator_nonzero

theorem geometryRow127_meanGap_read :
    rationalField geometryRowsJson127 "mean_gap" = .ok geometryRowsTyped127.meanGap :=
  original_rationalField_of_string geometryRowsJson127 "mean_gap" geometryRow127_meanGapText
    geometryRowsTyped127.meanGap geometryRow127_meanGap_field geometryRow127_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_meanGap_complete"
  err.flush

noncomputable def geometryRow127_jensenBoundNumeratorChars : List Char := ['9', '8', '2', '8', '0', '0', '1', '3', '2', '1', '9', '6', '0', '4', '6', '4', '8', '7', '5', '0', '5', '8', '1', '9', '1', '9', '2', '8', '1', '1', '9', '2', '6', '1', '8', '2', '7', '9', '1', '0', '1', '9', '6', '3', '4', '8', '9', '5', '9', '4', '6', '7', '6', '9', '8', '7', '8', '0', '7', '8', '5', '7', '6', '8', '5', '6', '8', '1', '9', '2', '2', '5', '6', '1', '0', '3', '6', '3', '8', '6', '4', '1', '1', '2', '1', '2', '9', '2', '5', '8', '7', '2', '4', '1', '7', '5', '8', '1', '5', '5', '2', '9', '2', '1', '4', '4', '3', '8', '3', '7', '6', '3', '2', '1', '9', '4', '1', '2', '0', '5', '6', '4', '9', '3', '7', '3', '6', '2', '8', '8', '3', '7', '1', '5', '6', '2', '2', '9', '8', '9', '3', '3', '1', '5', '5', '4', '4', '3', '5', '4', '8', '4', '3', '0', '8', '1', '2', '3', '3', '1', '8', '4', '8', '1', '4', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow127_jensenBoundDenominatorChars : List Char := ['6', '8', '8', '2', '4', '9', '3', '5', '3', '3', '2', '3', '5', '2', '4', '0', '7', '6', '9', '3', '5', '6', '9', '9', '1', '2', '0', '1', '8', '1', '0', '5', '2', '5', '7', '7', '8', '1', '8', '9', '5', '9', '6', '5', '1', '0', '7', '2', '6', '8', '0', '9', '5', '0', '0', '7', '9', '0', '7', '3', '3', '2', '7', '3', '0', '3', '0', '1', '8', '8', '3', '3', '6', '9', '9', '3', '7', '8', '8', '5', '9', '0', '8', '5', '4', '4', '5', '0', '4', '3', '8', '4', '9', '8', '1', '8', '3', '4', '6', '7', '9', '8', '0', '2', '4', '0', '3', '9', '7', '6', '7', '0', '2', '8', '4', '0', '7', '6', '7', '2', '7', '5', '9', '8', '7', '8', '3', '1', '0', '7', '4', '0', '0', '4', '1', '0', '3', '0', '7', '6', '2', '5', '2', '0', '7', '7', '0', '1', '6', '4', '2', '8', '2', '0', '5', '6', '4', '7', '7', '9', '2', '5', '7', '0', '5', '9', '8', '4', '9', '6', '5', '0', '1', '6', '5', '4', '0', '3', '7', '8', '4', '9', '4', '7', '1', '6', '2', '5', '9', '2', '1', '3']
noncomputable def geometryRow127_jensenBoundText : String := String.ofList (geometryRow127_jensenBoundNumeratorChars ++ '/' :: geometryRow127_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_jensenBound_before_field"
  err.flush

theorem geometryRow127_jensenBound_field :
    geometryRowsJson127.getObjVal? "jensen_bound" = .ok (.str geometryRow127_jensenBoundText) := by rfl

theorem geometryRow127_jensenBound_numerator_no_slash :
    geometryRow127_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow127_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow127_jensenBoundNumeratorChars = some (98280013219604648750581919281192618279101963489594676987807857685681922561036386411212925872417581552921443837632194120564937362883715622989331554435484308123318481445312500000 : Int) := by decide +kernel

theorem geometryRow127_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow127_jensenBoundDenominatorChars = some (688249353323524076935699120181052577818959651072680950079073327303018833699378859085445043849818346798024039767028407672759878310740041030762520770164282056477925705984965016540378494716259213 : Int) := by decide +kernel

theorem geometryRow127_jensenBound_denominator_nonzero : (688249353323524076935699120181052577818959651072680950079073327303018833699378859085445043849818346798024039767028407672759878310740041030762520770164282056477925705984965016540378494716259213 : Int) ≠ 0 := by decide +kernel

theorem geometryRow127_jensenBound_parse :
    parseRational geometryRow127_jensenBoundText = .ok geometryRowsTyped127.jensenBound :=
  original_rational_fraction_of_chars geometryRow127_jensenBoundNumeratorChars geometryRow127_jensenBoundDenominatorChars
    (98280013219604648750581919281192618279101963489594676987807857685681922561036386411212925872417581552921443837632194120564937362883715622989331554435484308123318481445312500000 : Int) (688249353323524076935699120181052577818959651072680950079073327303018833699378859085445043849818346798024039767028407672759878310740041030762520770164282056477925705984965016540378494716259213 : Int)
    geometryRow127_jensenBound_numerator_no_slash geometryRow127_jensenBound_numerator_parse
    geometryRow127_jensenBound_denominator_parse geometryRow127_jensenBound_denominator_nonzero

theorem geometryRow127_jensenBound_read :
    rationalField geometryRowsJson127 "jensen_bound" = .ok geometryRowsTyped127.jensenBound :=
  original_rationalField_of_string geometryRowsJson127 "jensen_bound" geometryRow127_jensenBoundText
    geometryRowsTyped127.jensenBound geometryRow127_jensenBound_field geometryRow127_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_factorMaxima_before"
  err.flush

theorem geometryRow127_factorMaxima_read :
    rationalArrayField geometryRowsJson127 "factor_maxima" = .ok geometryRowsTyped127.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_gapWeightedMeans_before"
  err.flush

theorem geometryRow127_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson127 "gap_weighted_means" = .ok geometryRowsTyped127.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow127_floorChars : List Char := ['1', '1', '3', '1', '3', '5', '5', '2', '0', '1', '6', '6', '7', '2']
noncomputable def geometryRow127_floorText : String := String.ofList geometryRow127_floorChars

theorem geometryRow127_floor_text_read :
    geometryRowsJson127.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow127_floorText := by rfl

theorem geometryRow127_floor_chars_parse :
    SourceJson.intChars geometryRow127_floorChars = some (11313552016672 : Int) := by decide +kernel

theorem geometryRow127_floor_parse :
    parseInteger geometryRow127_floorText = .ok geometryRowsTyped127.jensenFloorQ96 := by
  simp only [geometryRow127_floorText, parseInteger, String.toList_ofList, geometryRow127_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_127 :
    decodeGeometryRow geometryRowsJson127 = .ok geometryRowsTyped127 :=
  original_geometryRow_of_fields geometryRowsJson127 geometryRowsTyped127 geometryRow127_floorText
    geometryRow127_simplexId_read geometryRow127_vertexIds_read
    geometryRow127_physicalVolume_read geometryRow127_meanGap_read
    geometryRow127_factorMaxima_read geometryRow127_gapWeightedMeans_read
    geometryRow127_jensenBound_read geometryRow127_floor_text_read geometryRow127_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_127_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock064 : List SourceJson := [geometryRowsJson126, geometryRowsJson127]
noncomputable def geometryRowsTypedBlock064 : List (GeometryRow) := [geometryRowsTyped126, geometryRowsTyped127]
noncomputable def geometryRowsTypedThroughBlock064 : List (GeometryRow) := geometryRowsTypedThroughBlock063 ++ geometryRowsTypedBlock064

theorem geometry_Rows_block_064_push_eq (acc : List SourceJson) :
    SimplicesBlock064.blockPush acc = [geometryRowsJson127, geometryRowsJson126] ++ acc := by rfl

theorem geometry_Rows_block_064_reverse (acc : List SourceJson) :
    (SimplicesBlock064.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock064 := by
  rw [geometry_Rows_block_064_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_064 :
    geometryRowsJsonBlock064.mapM decodeGeometryRow = .ok geometryRowsTypedBlock064 := by
  simp only [geometryRowsJsonBlock064, geometryRowsTypedBlock064, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_126, decode_geometry_Rows_127]
  rfl

theorem decode_geometry_Rows_through_block_064 :
    SimplicesValue.arrayAcc065.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock064 := by
  change (SimplicesBlock064.blockPush SimplicesValue.arrayAcc064).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_064_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_063, decode_geometry_Rows_block_064]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_064_complete"
  err.flush

#print axioms geometryRow126_simplexId_read
#print axioms geometryRow126_vertexIds_read
#print axioms geometryRow126_physicalVolume_field
#print axioms geometryRow126_physicalVolume_numerator_no_slash
#print axioms geometryRow126_physicalVolume_numerator_parse
#print axioms geometryRow126_physicalVolume_denominator_parse
#print axioms geometryRow126_physicalVolume_denominator_nonzero
#print axioms geometryRow126_physicalVolume_parse
#print axioms geometryRow126_physicalVolume_read
#print axioms geometryRow126_meanGap_field
#print axioms geometryRow126_meanGap_numerator_no_slash
#print axioms geometryRow126_meanGap_numerator_parse
#print axioms geometryRow126_meanGap_denominator_parse
#print axioms geometryRow126_meanGap_denominator_nonzero
#print axioms geometryRow126_meanGap_parse
#print axioms geometryRow126_meanGap_read
#print axioms geometryRow126_jensenBound_field
#print axioms geometryRow126_jensenBound_numerator_no_slash
#print axioms geometryRow126_jensenBound_numerator_parse
#print axioms geometryRow126_jensenBound_denominator_parse
#print axioms geometryRow126_jensenBound_denominator_nonzero
#print axioms geometryRow126_jensenBound_parse
#print axioms geometryRow126_jensenBound_read
#print axioms geometryRow126_factorMaxima_read
#print axioms geometryRow126_gapWeightedMeans_read
#print axioms geometryRow126_floor_text_read
#print axioms geometryRow126_floor_chars_parse
#print axioms geometryRow126_floor_parse
#print axioms decode_geometry_Rows_126
#print axioms geometryRow127_simplexId_read
#print axioms geometryRow127_vertexIds_read
#print axioms geometryRow127_physicalVolume_field
#print axioms geometryRow127_physicalVolume_numerator_no_slash
#print axioms geometryRow127_physicalVolume_numerator_parse
#print axioms geometryRow127_physicalVolume_denominator_parse
#print axioms geometryRow127_physicalVolume_denominator_nonzero
#print axioms geometryRow127_physicalVolume_parse
#print axioms geometryRow127_physicalVolume_read
#print axioms geometryRow127_meanGap_field
#print axioms geometryRow127_meanGap_numerator_no_slash
#print axioms geometryRow127_meanGap_numerator_parse
#print axioms geometryRow127_meanGap_denominator_parse
#print axioms geometryRow127_meanGap_denominator_nonzero
#print axioms geometryRow127_meanGap_parse
#print axioms geometryRow127_meanGap_read
#print axioms geometryRow127_jensenBound_field
#print axioms geometryRow127_jensenBound_numerator_no_slash
#print axioms geometryRow127_jensenBound_numerator_parse
#print axioms geometryRow127_jensenBound_denominator_parse
#print axioms geometryRow127_jensenBound_denominator_nonzero
#print axioms geometryRow127_jensenBound_parse
#print axioms geometryRow127_jensenBound_read
#print axioms geometryRow127_factorMaxima_read
#print axioms geometryRow127_gapWeightedMeans_read
#print axioms geometryRow127_floor_text_read
#print axioms geometryRow127_floor_chars_parse
#print axioms geometryRow127_floor_parse
#print axioms decode_geometry_Rows_127
#print axioms geometry_Rows_block_064_push_eq
#print axioms geometry_Rows_block_064_reverse
#print axioms decode_geometry_Rows_block_064
#print axioms decode_geometry_Rows_through_block_064

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
