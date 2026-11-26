import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows033

/-! Original simplices typed block 34, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson067 : SourceJson :=
  (SimplicesBlock034.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped067 : GeometryRow :=
  { simplexId := 67,
    vertexIds := #[39, 35, 34, 24, 23, 21, 8, 3, 1],
    physicalVolume := ((208911525039292802667235548166014943457 : ℚ) / (1244062789632000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((42974410105841 : ℚ) / (552588400000000 : ℚ)), ((43532989214201 : ℚ) / (552588400000000 : ℚ)), ((18568809927679 : ℚ) / (127520400000000 : ℚ)), ((3652614545453 : ℚ) / (33155304000000 : ℚ)), ((1197579353951 : ℚ) / (19503120000000 : ℚ)), ((15544513127617 : ℚ) / (331553040000000 : ℚ)), ((1163365244003 : ℚ) / (29083600000000 : ℚ)), ((65426626096031 : ℚ) / (1657765200000000 : ℚ)), ((62118813003097 : ℚ) / (1657765200000000 : ℚ)), ((20706197322579 : ℚ) / (552588400000000 : ℚ))],
    jensenBound := ((4214692066561803924855724135093686370545614341587745583098146377211215375247356014178363289067520000000000000000000 : ℚ) / (7007739019450596544734031451125575448832772939773546137724892852015436869082597042413680019631968208041148586426720451480483025147 : ℚ)),
    jensenFloorQ96 := (47650505686685 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_simplexId_before"
  err.flush

theorem geometryRow067_simplexId_read :
    geometryRowsJson067.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped067.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_vertexIds_before"
  err.flush

theorem geometryRow067_vertexIds_read :
    geometryRowsJson067.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped067.vertexIds := by decide +kernel

noncomputable def geometryRow067_physicalVolumeNumeratorChars : List Char := ['2', '0', '8', '9', '1', '1', '5', '2', '5', '0', '3', '9', '2', '9', '2', '8', '0', '2', '6', '6', '7', '2', '3', '5', '5', '4', '8', '1', '6', '6', '0', '1', '4', '9', '4', '3', '4', '5', '7']
noncomputable def geometryRow067_physicalVolumeDenominatorChars : List Char := ['1', '2', '4', '4', '0', '6', '2', '7', '8', '9', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow067_physicalVolumeText : String := String.ofList (geometryRow067_physicalVolumeNumeratorChars ++ '/' :: geometryRow067_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_physicalVolume_before_field"
  err.flush

theorem geometryRow067_physicalVolume_field :
    geometryRowsJson067.getObjVal? "physical_volume" = .ok (.str geometryRow067_physicalVolumeText) := by rfl

theorem geometryRow067_physicalVolume_numerator_no_slash :
    geometryRow067_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow067_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow067_physicalVolumeNumeratorChars = some (208911525039292802667235548166014943457 : Int) := by decide +kernel

theorem geometryRow067_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow067_physicalVolumeDenominatorChars = some (1244062789632000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow067_physicalVolume_denominator_nonzero : (1244062789632000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow067_physicalVolume_parse :
    parseRational geometryRow067_physicalVolumeText = .ok geometryRowsTyped067.physicalVolume :=
  original_rational_fraction_of_chars geometryRow067_physicalVolumeNumeratorChars geometryRow067_physicalVolumeDenominatorChars
    (208911525039292802667235548166014943457 : Int) (1244062789632000000000000000000000000000000000000000000000000000 : Int)
    geometryRow067_physicalVolume_numerator_no_slash geometryRow067_physicalVolume_numerator_parse
    geometryRow067_physicalVolume_denominator_parse geometryRow067_physicalVolume_denominator_nonzero

theorem geometryRow067_physicalVolume_read :
    rationalField geometryRowsJson067 "physical_volume" = .ok geometryRowsTyped067.physicalVolume :=
  original_rationalField_of_string geometryRowsJson067 "physical_volume" geometryRow067_physicalVolumeText
    geometryRowsTyped067.physicalVolume geometryRow067_physicalVolume_field geometryRow067_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_physicalVolume_complete"
  err.flush

noncomputable def geometryRow067_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow067_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow067_meanGapText : String := String.ofList (geometryRow067_meanGapNumeratorChars ++ '/' :: geometryRow067_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_meanGap_before_field"
  err.flush

theorem geometryRow067_meanGap_field :
    geometryRowsJson067.getObjVal? "mean_gap" = .ok (.str geometryRow067_meanGapText) := by rfl

theorem geometryRow067_meanGap_numerator_no_slash :
    geometryRow067_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow067_meanGap_numerator_parse :
    SourceJson.intChars geometryRow067_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow067_meanGap_denominator_parse :
    SourceJson.intChars geometryRow067_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow067_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow067_meanGap_parse :
    parseRational geometryRow067_meanGapText = .ok geometryRowsTyped067.meanGap :=
  original_rational_fraction_of_chars geometryRow067_meanGapNumeratorChars geometryRow067_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow067_meanGap_numerator_no_slash geometryRow067_meanGap_numerator_parse
    geometryRow067_meanGap_denominator_parse geometryRow067_meanGap_denominator_nonzero

theorem geometryRow067_meanGap_read :
    rationalField geometryRowsJson067 "mean_gap" = .ok geometryRowsTyped067.meanGap :=
  original_rationalField_of_string geometryRowsJson067 "mean_gap" geometryRow067_meanGapText
    geometryRowsTyped067.meanGap geometryRow067_meanGap_field geometryRow067_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_meanGap_complete"
  err.flush

noncomputable def geometryRow067_jensenBoundNumeratorChars : List Char := ['4', '2', '1', '4', '6', '9', '2', '0', '6', '6', '5', '6', '1', '8', '0', '3', '9', '2', '4', '8', '5', '5', '7', '2', '4', '1', '3', '5', '0', '9', '3', '6', '8', '6', '3', '7', '0', '5', '4', '5', '6', '1', '4', '3', '4', '1', '5', '8', '7', '7', '4', '5', '5', '8', '3', '0', '9', '8', '1', '4', '6', '3', '7', '7', '2', '1', '1', '2', '1', '5', '3', '7', '5', '2', '4', '7', '3', '5', '6', '0', '1', '4', '1', '7', '8', '3', '6', '3', '2', '8', '9', '0', '6', '7', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow067_jensenBoundDenominatorChars : List Char := ['7', '0', '0', '7', '7', '3', '9', '0', '1', '9', '4', '5', '0', '5', '9', '6', '5', '4', '4', '7', '3', '4', '0', '3', '1', '4', '5', '1', '1', '2', '5', '5', '7', '5', '4', '4', '8', '8', '3', '2', '7', '7', '2', '9', '3', '9', '7', '7', '3', '5', '4', '6', '1', '3', '7', '7', '2', '4', '8', '9', '2', '8', '5', '2', '0', '1', '5', '4', '3', '6', '8', '6', '9', '0', '8', '2', '5', '9', '7', '0', '4', '2', '4', '1', '3', '6', '8', '0', '0', '1', '9', '6', '3', '1', '9', '6', '8', '2', '0', '8', '0', '4', '1', '1', '4', '8', '5', '8', '6', '4', '2', '6', '7', '2', '0', '4', '5', '1', '4', '8', '0', '4', '8', '3', '0', '2', '5', '1', '4', '7']
noncomputable def geometryRow067_jensenBoundText : String := String.ofList (geometryRow067_jensenBoundNumeratorChars ++ '/' :: geometryRow067_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_jensenBound_before_field"
  err.flush

theorem geometryRow067_jensenBound_field :
    geometryRowsJson067.getObjVal? "jensen_bound" = .ok (.str geometryRow067_jensenBoundText) := by rfl

theorem geometryRow067_jensenBound_numerator_no_slash :
    geometryRow067_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow067_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow067_jensenBoundNumeratorChars = some (4214692066561803924855724135093686370545614341587745583098146377211215375247356014178363289067520000000000000000000 : Int) := by decide +kernel

theorem geometryRow067_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow067_jensenBoundDenominatorChars = some (7007739019450596544734031451125575448832772939773546137724892852015436869082597042413680019631968208041148586426720451480483025147 : Int) := by decide +kernel

theorem geometryRow067_jensenBound_denominator_nonzero : (7007739019450596544734031451125575448832772939773546137724892852015436869082597042413680019631968208041148586426720451480483025147 : Int) ≠ 0 := by decide +kernel

theorem geometryRow067_jensenBound_parse :
    parseRational geometryRow067_jensenBoundText = .ok geometryRowsTyped067.jensenBound :=
  original_rational_fraction_of_chars geometryRow067_jensenBoundNumeratorChars geometryRow067_jensenBoundDenominatorChars
    (4214692066561803924855724135093686370545614341587745583098146377211215375247356014178363289067520000000000000000000 : Int) (7007739019450596544734031451125575448832772939773546137724892852015436869082597042413680019631968208041148586426720451480483025147 : Int)
    geometryRow067_jensenBound_numerator_no_slash geometryRow067_jensenBound_numerator_parse
    geometryRow067_jensenBound_denominator_parse geometryRow067_jensenBound_denominator_nonzero

theorem geometryRow067_jensenBound_read :
    rationalField geometryRowsJson067 "jensen_bound" = .ok geometryRowsTyped067.jensenBound :=
  original_rationalField_of_string geometryRowsJson067 "jensen_bound" geometryRow067_jensenBoundText
    geometryRowsTyped067.jensenBound geometryRow067_jensenBound_field geometryRow067_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_factorMaxima_before"
  err.flush

theorem geometryRow067_factorMaxima_read :
    rationalArrayField geometryRowsJson067 "factor_maxima" = .ok geometryRowsTyped067.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_gapWeightedMeans_before"
  err.flush

theorem geometryRow067_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson067 "gap_weighted_means" = .ok geometryRowsTyped067.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow067_floorChars : List Char := ['4', '7', '6', '5', '0', '5', '0', '5', '6', '8', '6', '6', '8', '5']
noncomputable def geometryRow067_floorText : String := String.ofList geometryRow067_floorChars

theorem geometryRow067_floor_text_read :
    geometryRowsJson067.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow067_floorText := by rfl

theorem geometryRow067_floor_chars_parse :
    SourceJson.intChars geometryRow067_floorChars = some (47650505686685 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY01_TYPED Row_067_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson068 : SourceJson :=
  (SimplicesBlock034.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped068 : GeometryRow :=
  { simplexId := 68,
    vertexIds := #[39, 35, 34, 24, 23, 21, 20, 3, 1],
    physicalVolume := ((6245658011789038731731560792489016977529 : ℚ) / (187183601270784000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((66369109 : ℚ) / (99756000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((47442197114528289407 : ℚ) / (636905216229800000000 : ℚ)), ((913986452166025262203 : ℚ) / (12101199108366200000000 : ℚ)), ((5310031279822658526721 : ℚ) / (36303597325098600000000 : ℚ)), ((396663141619257442589 : ℚ) / (3630359732509860000000 : ℚ)), ((269388118060359329 : ℚ) / (4448970260428750000 : ℚ)), ((340046468776620150697 : ℚ) / (7260719465019720000000 : ℚ)), ((30823352419699883711 : ℚ) / (756324944272887500000 : ℚ)), ((730067986724320895429 : ℚ) / (18151798662549300000000 : ℚ)), ((1418985553244304225331 : ℚ) / (36303597325098600000000 : ℚ)), ((1418980712764660878851 : ℚ) / (36303597325098600000000 : ℚ))],
    jensenBound := ((14377885844679878003304848545393008920630473408467750976941334007179322125634645933364008771268001581800210711396252291021151447293597551619769720460800698195128992338671166992187500000000 : ℚ) / (103387110344052451738746629154899122437828005257097059999605475924354484526489349642549290246959620264600404063100419304629716134316306389170511995883669587964193375730210605243149353574915477855187022339 : ℚ)),
    jensenFloorQ96 := (11018138262332 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_simplexId_before"
  err.flush

theorem geometryRow068_simplexId_read :
    geometryRowsJson068.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped068.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_vertexIds_before"
  err.flush

theorem geometryRow068_vertexIds_read :
    geometryRowsJson068.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped068.vertexIds := by decide +kernel

noncomputable def geometryRow068_physicalVolumeNumeratorChars : List Char := ['6', '2', '4', '5', '6', '5', '8', '0', '1', '1', '7', '8', '9', '0', '3', '8', '7', '3', '1', '7', '3', '1', '5', '6', '0', '7', '9', '2', '4', '8', '9', '0', '1', '6', '9', '7', '7', '5', '2', '9']
noncomputable def geometryRow068_physicalVolumeDenominatorChars : List Char := ['1', '8', '7', '1', '8', '3', '6', '0', '1', '2', '7', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow068_physicalVolumeText : String := String.ofList (geometryRow068_physicalVolumeNumeratorChars ++ '/' :: geometryRow068_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_physicalVolume_before_field"
  err.flush

theorem geometryRow068_physicalVolume_field :
    geometryRowsJson068.getObjVal? "physical_volume" = .ok (.str geometryRow068_physicalVolumeText) := by rfl

theorem geometryRow068_physicalVolume_numerator_no_slash :
    geometryRow068_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow068_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow068_physicalVolumeNumeratorChars = some (6245658011789038731731560792489016977529 : Int) := by decide +kernel

theorem geometryRow068_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow068_physicalVolumeDenominatorChars = some (187183601270784000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow068_physicalVolume_denominator_nonzero : (187183601270784000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow068_physicalVolume_parse :
    parseRational geometryRow068_physicalVolumeText = .ok geometryRowsTyped068.physicalVolume :=
  original_rational_fraction_of_chars geometryRow068_physicalVolumeNumeratorChars geometryRow068_physicalVolumeDenominatorChars
    (6245658011789038731731560792489016977529 : Int) (187183601270784000000000000000000000000000000000000000000000000000 : Int)
    geometryRow068_physicalVolume_numerator_no_slash geometryRow068_physicalVolume_numerator_parse
    geometryRow068_physicalVolume_denominator_parse geometryRow068_physicalVolume_denominator_nonzero

theorem geometryRow068_physicalVolume_read :
    rationalField geometryRowsJson068 "physical_volume" = .ok geometryRowsTyped068.physicalVolume :=
  original_rationalField_of_string geometryRowsJson068 "physical_volume" geometryRow068_physicalVolumeText
    geometryRowsTyped068.physicalVolume geometryRow068_physicalVolume_field geometryRow068_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_physicalVolume_complete"
  err.flush

noncomputable def geometryRow068_meanGapNumeratorChars : List Char := ['6', '6', '3', '6', '9', '1', '0', '9']
noncomputable def geometryRow068_meanGapDenominatorChars : List Char := ['9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow068_meanGapText : String := String.ofList (geometryRow068_meanGapNumeratorChars ++ '/' :: geometryRow068_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_meanGap_before_field"
  err.flush

theorem geometryRow068_meanGap_field :
    geometryRowsJson068.getObjVal? "mean_gap" = .ok (.str geometryRow068_meanGapText) := by rfl

theorem geometryRow068_meanGap_numerator_no_slash :
    geometryRow068_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow068_meanGap_numerator_parse :
    SourceJson.intChars geometryRow068_meanGapNumeratorChars = some (66369109 : Int) := by decide +kernel

theorem geometryRow068_meanGap_denominator_parse :
    SourceJson.intChars geometryRow068_meanGapDenominatorChars = some (99756000000 : Int) := by decide +kernel

theorem geometryRow068_meanGap_denominator_nonzero : (99756000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow068_meanGap_parse :
    parseRational geometryRow068_meanGapText = .ok geometryRowsTyped068.meanGap :=
  original_rational_fraction_of_chars geometryRow068_meanGapNumeratorChars geometryRow068_meanGapDenominatorChars
    (66369109 : Int) (99756000000 : Int)
    geometryRow068_meanGap_numerator_no_slash geometryRow068_meanGap_numerator_parse
    geometryRow068_meanGap_denominator_parse geometryRow068_meanGap_denominator_nonzero

theorem geometryRow068_meanGap_read :
    rationalField geometryRowsJson068 "mean_gap" = .ok geometryRowsTyped068.meanGap :=
  original_rationalField_of_string geometryRowsJson068 "mean_gap" geometryRow068_meanGapText
    geometryRowsTyped068.meanGap geometryRow068_meanGap_field geometryRow068_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_meanGap_complete"
  err.flush

noncomputable def geometryRow068_jensenBoundNumeratorChars : List Char := ['1', '4', '3', '7', '7', '8', '8', '5', '8', '4', '4', '6', '7', '9', '8', '7', '8', '0', '0', '3', '3', '0', '4', '8', '4', '8', '5', '4', '5', '3', '9', '3', '0', '0', '8', '9', '2', '0', '6', '3', '0', '4', '7', '3', '4', '0', '8', '4', '6', '7', '7', '5', '0', '9', '7', '6', '9', '4', '1', '3', '3', '4', '0', '0', '7', '1', '7', '9', '3', '2', '2', '1', '2', '5', '6', '3', '4', '6', '4', '5', '9', '3', '3', '3', '6', '4', '0', '0', '8', '7', '7', '1', '2', '6', '8', '0', '0', '1', '5', '8', '1', '8', '0', '0', '2', '1', '0', '7', '1', '1', '3', '9', '6', '2', '5', '2', '2', '9', '1', '0', '2', '1', '1', '5', '1', '4', '4', '7', '2', '9', '3', '5', '9', '7', '5', '5', '1', '6', '1', '9', '7', '6', '9', '7', '2', '0', '4', '6', '0', '8', '0', '0', '6', '9', '8', '1', '9', '5', '1', '2', '8', '9', '9', '2', '3', '3', '8', '6', '7', '1', '1', '6', '6', '9', '9', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow068_jensenBoundDenominatorChars : List Char := ['1', '0', '3', '3', '8', '7', '1', '1', '0', '3', '4', '4', '0', '5', '2', '4', '5', '1', '7', '3', '8', '7', '4', '6', '6', '2', '9', '1', '5', '4', '8', '9', '9', '1', '2', '2', '4', '3', '7', '8', '2', '8', '0', '0', '5', '2', '5', '7', '0', '9', '7', '0', '5', '9', '9', '9', '9', '6', '0', '5', '4', '7', '5', '9', '2', '4', '3', '5', '4', '4', '8', '4', '5', '2', '6', '4', '8', '9', '3', '4', '9', '6', '4', '2', '5', '4', '9', '2', '9', '0', '2', '4', '6', '9', '5', '9', '6', '2', '0', '2', '6', '4', '6', '0', '0', '4', '0', '4', '0', '6', '3', '1', '0', '0', '4', '1', '9', '3', '0', '4', '6', '2', '9', '7', '1', '6', '1', '3', '4', '3', '1', '6', '3', '0', '6', '3', '8', '9', '1', '7', '0', '5', '1', '1', '9', '9', '5', '8', '8', '3', '6', '6', '9', '5', '8', '7', '9', '6', '4', '1', '9', '3', '3', '7', '5', '7', '3', '0', '2', '1', '0', '6', '0', '5', '2', '4', '3', '1', '4', '9', '3', '5', '3', '5', '7', '4', '9', '1', '5', '4', '7', '7', '8', '5', '5', '1', '8', '7', '0', '2', '2', '3', '3', '9']
noncomputable def geometryRow068_jensenBoundText : String := String.ofList (geometryRow068_jensenBoundNumeratorChars ++ '/' :: geometryRow068_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_jensenBound_before_field"
  err.flush

theorem geometryRow068_jensenBound_field :
    geometryRowsJson068.getObjVal? "jensen_bound" = .ok (.str geometryRow068_jensenBoundText) := by rfl

theorem geometryRow068_jensenBound_numerator_no_slash :
    geometryRow068_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow068_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow068_jensenBoundNumeratorChars = some (14377885844679878003304848545393008920630473408467750976941334007179322125634645933364008771268001581800210711396252291021151447293597551619769720460800698195128992338671166992187500000000 : Int) := by decide +kernel

theorem geometryRow068_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow068_jensenBoundDenominatorChars = some (103387110344052451738746629154899122437828005257097059999605475924354484526489349642549290246959620264600404063100419304629716134316306389170511995883669587964193375730210605243149353574915477855187022339 : Int) := by decide +kernel

theorem geometryRow068_jensenBound_denominator_nonzero : (103387110344052451738746629154899122437828005257097059999605475924354484526489349642549290246959620264600404063100419304629716134316306389170511995883669587964193375730210605243149353574915477855187022339 : Int) ≠ 0 := by decide +kernel

theorem geometryRow068_jensenBound_parse :
    parseRational geometryRow068_jensenBoundText = .ok geometryRowsTyped068.jensenBound :=
  original_rational_fraction_of_chars geometryRow068_jensenBoundNumeratorChars geometryRow068_jensenBoundDenominatorChars
    (14377885844679878003304848545393008920630473408467750976941334007179322125634645933364008771268001581800210711396252291021151447293597551619769720460800698195128992338671166992187500000000 : Int) (103387110344052451738746629154899122437828005257097059999605475924354484526489349642549290246959620264600404063100419304629716134316306389170511995883669587964193375730210605243149353574915477855187022339 : Int)
    geometryRow068_jensenBound_numerator_no_slash geometryRow068_jensenBound_numerator_parse
    geometryRow068_jensenBound_denominator_parse geometryRow068_jensenBound_denominator_nonzero

theorem geometryRow068_jensenBound_read :
    rationalField geometryRowsJson068 "jensen_bound" = .ok geometryRowsTyped068.jensenBound :=
  original_rationalField_of_string geometryRowsJson068 "jensen_bound" geometryRow068_jensenBoundText
    geometryRowsTyped068.jensenBound geometryRow068_jensenBound_field geometryRow068_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_factorMaxima_before"
  err.flush

theorem geometryRow068_factorMaxima_read :
    rationalArrayField geometryRowsJson068 "factor_maxima" = .ok geometryRowsTyped068.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_gapWeightedMeans_before"
  err.flush

theorem geometryRow068_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson068 "gap_weighted_means" = .ok geometryRowsTyped068.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow068_floorChars : List Char := ['1', '1', '0', '1', '8', '1', '3', '8', '2', '6', '2', '3', '3', '2']
noncomputable def geometryRow068_floorText : String := String.ofList geometryRow068_floorChars

theorem geometryRow068_floor_text_read :
    geometryRowsJson068.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow068_floorText := by rfl

theorem geometryRow068_floor_chars_parse :
    SourceJson.intChars geometryRow068_floorChars = some (11018138262332 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY01_TYPED Row_068_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock034 : List SourceJson := [geometryRowsJson067, geometryRowsJson068]
noncomputable def geometryRowsTypedBlock034 : List (GeometryRow) := [geometryRowsTyped067, geometryRowsTyped068]
noncomputable def geometryRowsTypedThroughBlock034 : List (GeometryRow) := geometryRowsTypedThroughBlock033 ++ geometryRowsTypedBlock034

theorem geometry_Rows_block_034_push_eq (acc : List SourceJson) :
    SimplicesBlock034.blockPush acc = [geometryRowsJson068, geometryRowsJson067] ++ acc := by rfl

theorem geometry_Rows_block_034_reverse (acc : List SourceJson) :
    (SimplicesBlock034.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock034 := by
  rw [geometry_Rows_block_034_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_034 :
    geometryRowsJsonBlock034.mapM decodeGeometryRow = .ok geometryRowsTypedBlock034 := by
  simp only [geometryRowsJsonBlock034, geometryRowsTypedBlock034, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_067, decode_geometry_Rows_068]
  rfl

theorem decode_geometry_Rows_through_block_034 :
    SimplicesValue.arrayAcc035.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock034 := by
  change (SimplicesBlock034.blockPush SimplicesValue.arrayAcc034).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_034_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_033, decode_geometry_Rows_block_034]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_034_complete"
  err.flush

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
#print axioms geometry_Rows_block_034_push_eq
#print axioms geometry_Rows_block_034_reverse
#print axioms decode_geometry_Rows_block_034
#print axioms decode_geometry_Rows_through_block_034

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
