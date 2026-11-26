import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows038

/-! Original simplices typed block 39, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson077 : SourceJson :=
  (SimplicesBlock039.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped077 : GeometryRow :=
  { simplexId := 77,
    vertexIds := #[39, 37, 24, 11, 10, 8, 3, 1, 0],
    physicalVolume := ((1354125827371407473464400494532399 : ℚ) / (428654592000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((909379 : ℚ) / (14400000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((8757147289 : ℚ) / (94057600000 : ℚ)), ((221305614601 : ℚ) / (2351440000000 : ℚ)), ((15487810061 : ℚ) / (108528000000 : ℚ)), ((1175802586963 : ℚ) / (10581480000000 : ℚ)), ((23427207457 : ℚ) / (414960000000 : ℚ)), ((352151073863 : ℚ) / (7054320000000 : ℚ)), ((166700027237 : ℚ) / (4232592000000 : ℚ)), ((770246851909 : ℚ) / (21162960000000 : ℚ)), ((711349129249 : ℚ) / (21162960000000 : ℚ)), ((711344896657 : ℚ) / (21162960000000 : ℚ))],
    jensenBound := ((211658148543400030207249052128774090344062655293081626839047234571529904825045804384256000000000000 : ℚ) / (18917235895650705956781592517838457482094800092703602422326555797737215216075189984719484987708588723860081659433 : ℚ)),
    jensenFloorQ96 := (886455414668707 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_simplexId_before"
  err.flush

theorem geometryRow077_simplexId_read :
    geometryRowsJson077.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped077.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_vertexIds_before"
  err.flush

theorem geometryRow077_vertexIds_read :
    geometryRowsJson077.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped077.vertexIds := by decide +kernel

noncomputable def geometryRow077_physicalVolumeNumeratorChars : List Char := ['1', '3', '5', '4', '1', '2', '5', '8', '2', '7', '3', '7', '1', '4', '0', '7', '4', '7', '3', '4', '6', '4', '4', '0', '0', '4', '9', '4', '5', '3', '2', '3', '9', '9']
noncomputable def geometryRow077_physicalVolumeDenominatorChars : List Char := ['4', '2', '8', '6', '5', '4', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow077_physicalVolumeText : String := String.ofList (geometryRow077_physicalVolumeNumeratorChars ++ '/' :: geometryRow077_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_physicalVolume_before_field"
  err.flush

theorem geometryRow077_physicalVolume_field :
    geometryRowsJson077.getObjVal? "physical_volume" = .ok (.str geometryRow077_physicalVolumeText) := by rfl

theorem geometryRow077_physicalVolume_numerator_no_slash :
    geometryRow077_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow077_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow077_physicalVolumeNumeratorChars = some (1354125827371407473464400494532399 : Int) := by decide +kernel

theorem geometryRow077_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow077_physicalVolumeDenominatorChars = some (428654592000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow077_physicalVolume_denominator_nonzero : (428654592000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow077_physicalVolume_parse :
    parseRational geometryRow077_physicalVolumeText = .ok geometryRowsTyped077.physicalVolume :=
  original_rational_fraction_of_chars geometryRow077_physicalVolumeNumeratorChars geometryRow077_physicalVolumeDenominatorChars
    (1354125827371407473464400494532399 : Int) (428654592000000000000000000000000000000000000000000000000 : Int)
    geometryRow077_physicalVolume_numerator_no_slash geometryRow077_physicalVolume_numerator_parse
    geometryRow077_physicalVolume_denominator_parse geometryRow077_physicalVolume_denominator_nonzero

theorem geometryRow077_physicalVolume_read :
    rationalField geometryRowsJson077 "physical_volume" = .ok geometryRowsTyped077.physicalVolume :=
  original_rationalField_of_string geometryRowsJson077 "physical_volume" geometryRow077_physicalVolumeText
    geometryRowsTyped077.physicalVolume geometryRow077_physicalVolume_field geometryRow077_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_physicalVolume_complete"
  err.flush

noncomputable def geometryRow077_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow077_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow077_meanGapText : String := String.ofList (geometryRow077_meanGapNumeratorChars ++ '/' :: geometryRow077_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_meanGap_before_field"
  err.flush

theorem geometryRow077_meanGap_field :
    geometryRowsJson077.getObjVal? "mean_gap" = .ok (.str geometryRow077_meanGapText) := by rfl

theorem geometryRow077_meanGap_numerator_no_slash :
    geometryRow077_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow077_meanGap_numerator_parse :
    SourceJson.intChars geometryRow077_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow077_meanGap_denominator_parse :
    SourceJson.intChars geometryRow077_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow077_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow077_meanGap_parse :
    parseRational geometryRow077_meanGapText = .ok geometryRowsTyped077.meanGap :=
  original_rational_fraction_of_chars geometryRow077_meanGapNumeratorChars geometryRow077_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow077_meanGap_numerator_no_slash geometryRow077_meanGap_numerator_parse
    geometryRow077_meanGap_denominator_parse geometryRow077_meanGap_denominator_nonzero

theorem geometryRow077_meanGap_read :
    rationalField geometryRowsJson077 "mean_gap" = .ok geometryRowsTyped077.meanGap :=
  original_rationalField_of_string geometryRowsJson077 "mean_gap" geometryRow077_meanGapText
    geometryRowsTyped077.meanGap geometryRow077_meanGap_field geometryRow077_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_meanGap_complete"
  err.flush

noncomputable def geometryRow077_jensenBoundNumeratorChars : List Char := ['2', '1', '1', '6', '5', '8', '1', '4', '8', '5', '4', '3', '4', '0', '0', '0', '3', '0', '2', '0', '7', '2', '4', '9', '0', '5', '2', '1', '2', '8', '7', '7', '4', '0', '9', '0', '3', '4', '4', '0', '6', '2', '6', '5', '5', '2', '9', '3', '0', '8', '1', '6', '2', '6', '8', '3', '9', '0', '4', '7', '2', '3', '4', '5', '7', '1', '5', '2', '9', '9', '0', '4', '8', '2', '5', '0', '4', '5', '8', '0', '4', '3', '8', '4', '2', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow077_jensenBoundDenominatorChars : List Char := ['1', '8', '9', '1', '7', '2', '3', '5', '8', '9', '5', '6', '5', '0', '7', '0', '5', '9', '5', '6', '7', '8', '1', '5', '9', '2', '5', '1', '7', '8', '3', '8', '4', '5', '7', '4', '8', '2', '0', '9', '4', '8', '0', '0', '0', '9', '2', '7', '0', '3', '6', '0', '2', '4', '2', '2', '3', '2', '6', '5', '5', '5', '7', '9', '7', '7', '3', '7', '2', '1', '5', '2', '1', '6', '0', '7', '5', '1', '8', '9', '9', '8', '4', '7', '1', '9', '4', '8', '4', '9', '8', '7', '7', '0', '8', '5', '8', '8', '7', '2', '3', '8', '6', '0', '0', '8', '1', '6', '5', '9', '4', '3', '3']
noncomputable def geometryRow077_jensenBoundText : String := String.ofList (geometryRow077_jensenBoundNumeratorChars ++ '/' :: geometryRow077_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_jensenBound_before_field"
  err.flush

theorem geometryRow077_jensenBound_field :
    geometryRowsJson077.getObjVal? "jensen_bound" = .ok (.str geometryRow077_jensenBoundText) := by rfl

theorem geometryRow077_jensenBound_numerator_no_slash :
    geometryRow077_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow077_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow077_jensenBoundNumeratorChars = some (211658148543400030207249052128774090344062655293081626839047234571529904825045804384256000000000000 : Int) := by decide +kernel

theorem geometryRow077_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow077_jensenBoundDenominatorChars = some (18917235895650705956781592517838457482094800092703602422326555797737215216075189984719484987708588723860081659433 : Int) := by decide +kernel

theorem geometryRow077_jensenBound_denominator_nonzero : (18917235895650705956781592517838457482094800092703602422326555797737215216075189984719484987708588723860081659433 : Int) ≠ 0 := by decide +kernel

theorem geometryRow077_jensenBound_parse :
    parseRational geometryRow077_jensenBoundText = .ok geometryRowsTyped077.jensenBound :=
  original_rational_fraction_of_chars geometryRow077_jensenBoundNumeratorChars geometryRow077_jensenBoundDenominatorChars
    (211658148543400030207249052128774090344062655293081626839047234571529904825045804384256000000000000 : Int) (18917235895650705956781592517838457482094800092703602422326555797737215216075189984719484987708588723860081659433 : Int)
    geometryRow077_jensenBound_numerator_no_slash geometryRow077_jensenBound_numerator_parse
    geometryRow077_jensenBound_denominator_parse geometryRow077_jensenBound_denominator_nonzero

theorem geometryRow077_jensenBound_read :
    rationalField geometryRowsJson077 "jensen_bound" = .ok geometryRowsTyped077.jensenBound :=
  original_rationalField_of_string geometryRowsJson077 "jensen_bound" geometryRow077_jensenBoundText
    geometryRowsTyped077.jensenBound geometryRow077_jensenBound_field geometryRow077_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_factorMaxima_before"
  err.flush

theorem geometryRow077_factorMaxima_read :
    rationalArrayField geometryRowsJson077 "factor_maxima" = .ok geometryRowsTyped077.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_gapWeightedMeans_before"
  err.flush

theorem geometryRow077_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson077 "gap_weighted_means" = .ok geometryRowsTyped077.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow077_floorChars : List Char := ['8', '8', '6', '4', '5', '5', '4', '1', '4', '6', '6', '8', '7', '0', '7']
noncomputable def geometryRow077_floorText : String := String.ofList geometryRow077_floorChars

theorem geometryRow077_floor_text_read :
    geometryRowsJson077.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow077_floorText := by rfl

theorem geometryRow077_floor_chars_parse :
    SourceJson.intChars geometryRow077_floorChars = some (886455414668707 : Int) := by decide +kernel

theorem geometryRow077_floor_parse :
    parseInteger geometryRow077_floorText = .ok geometryRowsTyped077.jensenFloorQ96 := by
  simp only [geometryRow077_floorText, parseInteger, String.toList_ofList, geometryRow077_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_077 :
    decodeGeometryRow geometryRowsJson077 = .ok geometryRowsTyped077 :=
  original_geometryRow_of_fields geometryRowsJson077 geometryRowsTyped077 geometryRow077_floorText
    geometryRow077_simplexId_read geometryRow077_vertexIds_read
    geometryRow077_physicalVolume_read geometryRow077_meanGap_read
    geometryRow077_factorMaxima_read geometryRow077_gapWeightedMeans_read
    geometryRow077_jensenBound_read geometryRow077_floor_text_read geometryRow077_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_077_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson078 : SourceJson :=
  (SimplicesBlock039.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped078 : GeometryRow :=
  { simplexId := 78,
    vertexIds := #[39, 37, 24, 11, 10, 8, 3, 2, 0],
    physicalVolume := ((42749061555204370827276759463802856511 : ℚ) / (2571927552000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((26486326455915613 : ℚ) / (288628644928000000 : ℚ)), ((6598574152869437503 : ℚ) / (70714018007360000000 : ℚ)), ((2333193897660058957 : ℚ) / (16318619540160000000 : ℚ)), ((35871730267214307521 : ℚ) / (318213081033120000000 : ℚ)), ((235206558162306953 : ℚ) / (4159648118080000000 : ℚ)), ((10305292918596029747 : ℚ) / (212142054022080000000 : ℚ)), ((25123201618847651561 : ℚ) / (636426162066240000000 : ℚ)), ((23221008118984705817 : ℚ) / (636426162066240000000 : ℚ)), ((21559227736767104339 : ℚ) / (636426162066240000000 : ℚ)), ((4244401881539967697 : ℚ) / (127285232413248000000 : ℚ))],
    jensenBound := ((67756472962382223277141128390095924975794689234472951783929567850913157132199827762677605513010104172754744750769462984074509495673028641846119372320981332787200000000000000 : ℚ) / (548460742267333767550876453006856976195723454667228445079093740658164994058817885031515589864675057226220204438467761001755195739738871800548660409943242402199160325256318529251747013 : ℚ)),
    jensenFloorQ96 := (9787794162011997730 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_simplexId_before"
  err.flush

theorem geometryRow078_simplexId_read :
    geometryRowsJson078.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped078.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_vertexIds_before"
  err.flush

theorem geometryRow078_vertexIds_read :
    geometryRowsJson078.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped078.vertexIds := by decide +kernel

noncomputable def geometryRow078_physicalVolumeNumeratorChars : List Char := ['4', '2', '7', '4', '9', '0', '6', '1', '5', '5', '5', '2', '0', '4', '3', '7', '0', '8', '2', '7', '2', '7', '6', '7', '5', '9', '4', '6', '3', '8', '0', '2', '8', '5', '6', '5', '1', '1']
noncomputable def geometryRow078_physicalVolumeDenominatorChars : List Char := ['2', '5', '7', '1', '9', '2', '7', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow078_physicalVolumeText : String := String.ofList (geometryRow078_physicalVolumeNumeratorChars ++ '/' :: geometryRow078_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_physicalVolume_before_field"
  err.flush

theorem geometryRow078_physicalVolume_field :
    geometryRowsJson078.getObjVal? "physical_volume" = .ok (.str geometryRow078_physicalVolumeText) := by rfl

theorem geometryRow078_physicalVolume_numerator_no_slash :
    geometryRow078_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow078_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow078_physicalVolumeNumeratorChars = some (42749061555204370827276759463802856511 : Int) := by decide +kernel

theorem geometryRow078_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow078_physicalVolumeDenominatorChars = some (2571927552000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow078_physicalVolume_denominator_nonzero : (2571927552000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow078_physicalVolume_parse :
    parseRational geometryRow078_physicalVolumeText = .ok geometryRowsTyped078.physicalVolume :=
  original_rational_fraction_of_chars geometryRow078_physicalVolumeNumeratorChars geometryRow078_physicalVolumeDenominatorChars
    (42749061555204370827276759463802856511 : Int) (2571927552000000000000000000000000000000000000000000000000 : Int)
    geometryRow078_physicalVolume_numerator_no_slash geometryRow078_physicalVolume_numerator_parse
    geometryRow078_physicalVolume_denominator_parse geometryRow078_physicalVolume_denominator_nonzero

theorem geometryRow078_physicalVolume_read :
    rationalField geometryRowsJson078 "physical_volume" = .ok geometryRowsTyped078.physicalVolume :=
  original_rationalField_of_string geometryRowsJson078 "physical_volume" geometryRow078_physicalVolumeText
    geometryRowsTyped078.physicalVolume geometryRow078_physicalVolume_field geometryRow078_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_physicalVolume_complete"
  err.flush

noncomputable def geometryRow078_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow078_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow078_meanGapText : String := String.ofList (geometryRow078_meanGapNumeratorChars ++ '/' :: geometryRow078_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_meanGap_before_field"
  err.flush

theorem geometryRow078_meanGap_field :
    geometryRowsJson078.getObjVal? "mean_gap" = .ok (.str geometryRow078_meanGapText) := by rfl

theorem geometryRow078_meanGap_numerator_no_slash :
    geometryRow078_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow078_meanGap_numerator_parse :
    SourceJson.intChars geometryRow078_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow078_meanGap_denominator_parse :
    SourceJson.intChars geometryRow078_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow078_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow078_meanGap_parse :
    parseRational geometryRow078_meanGapText = .ok geometryRowsTyped078.meanGap :=
  original_rational_fraction_of_chars geometryRow078_meanGapNumeratorChars geometryRow078_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow078_meanGap_numerator_no_slash geometryRow078_meanGap_numerator_parse
    geometryRow078_meanGap_denominator_parse geometryRow078_meanGap_denominator_nonzero

theorem geometryRow078_meanGap_read :
    rationalField geometryRowsJson078 "mean_gap" = .ok geometryRowsTyped078.meanGap :=
  original_rationalField_of_string geometryRowsJson078 "mean_gap" geometryRow078_meanGapText
    geometryRowsTyped078.meanGap geometryRow078_meanGap_field geometryRow078_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_meanGap_complete"
  err.flush

noncomputable def geometryRow078_jensenBoundNumeratorChars : List Char := ['6', '7', '7', '5', '6', '4', '7', '2', '9', '6', '2', '3', '8', '2', '2', '2', '3', '2', '7', '7', '1', '4', '1', '1', '2', '8', '3', '9', '0', '0', '9', '5', '9', '2', '4', '9', '7', '5', '7', '9', '4', '6', '8', '9', '2', '3', '4', '4', '7', '2', '9', '5', '1', '7', '8', '3', '9', '2', '9', '5', '6', '7', '8', '5', '0', '9', '1', '3', '1', '5', '7', '1', '3', '2', '1', '9', '9', '8', '2', '7', '7', '6', '2', '6', '7', '7', '6', '0', '5', '5', '1', '3', '0', '1', '0', '1', '0', '4', '1', '7', '2', '7', '5', '4', '7', '4', '4', '7', '5', '0', '7', '6', '9', '4', '6', '2', '9', '8', '4', '0', '7', '4', '5', '0', '9', '4', '9', '5', '6', '7', '3', '0', '2', '8', '6', '4', '1', '8', '4', '6', '1', '1', '9', '3', '7', '2', '3', '2', '0', '9', '8', '1', '3', '3', '2', '7', '8', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow078_jensenBoundDenominatorChars : List Char := ['5', '4', '8', '4', '6', '0', '7', '4', '2', '2', '6', '7', '3', '3', '3', '7', '6', '7', '5', '5', '0', '8', '7', '6', '4', '5', '3', '0', '0', '6', '8', '5', '6', '9', '7', '6', '1', '9', '5', '7', '2', '3', '4', '5', '4', '6', '6', '7', '2', '2', '8', '4', '4', '5', '0', '7', '9', '0', '9', '3', '7', '4', '0', '6', '5', '8', '1', '6', '4', '9', '9', '4', '0', '5', '8', '8', '1', '7', '8', '8', '5', '0', '3', '1', '5', '1', '5', '5', '8', '9', '8', '6', '4', '6', '7', '5', '0', '5', '7', '2', '2', '6', '2', '2', '0', '2', '0', '4', '4', '3', '8', '4', '6', '7', '7', '6', '1', '0', '0', '1', '7', '5', '5', '1', '9', '5', '7', '3', '9', '7', '3', '8', '8', '7', '1', '8', '0', '0', '5', '4', '8', '6', '6', '0', '4', '0', '9', '9', '4', '3', '2', '4', '2', '4', '0', '2', '1', '9', '9', '1', '6', '0', '3', '2', '5', '2', '5', '6', '3', '1', '8', '5', '2', '9', '2', '5', '1', '7', '4', '7', '0', '1', '3']
noncomputable def geometryRow078_jensenBoundText : String := String.ofList (geometryRow078_jensenBoundNumeratorChars ++ '/' :: geometryRow078_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_jensenBound_before_field"
  err.flush

theorem geometryRow078_jensenBound_field :
    geometryRowsJson078.getObjVal? "jensen_bound" = .ok (.str geometryRow078_jensenBoundText) := by rfl

theorem geometryRow078_jensenBound_numerator_no_slash :
    geometryRow078_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow078_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow078_jensenBoundNumeratorChars = some (67756472962382223277141128390095924975794689234472951783929567850913157132199827762677605513010104172754744750769462984074509495673028641846119372320981332787200000000000000 : Int) := by decide +kernel

theorem geometryRow078_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow078_jensenBoundDenominatorChars = some (548460742267333767550876453006856976195723454667228445079093740658164994058817885031515589864675057226220204438467761001755195739738871800548660409943242402199160325256318529251747013 : Int) := by decide +kernel

theorem geometryRow078_jensenBound_denominator_nonzero : (548460742267333767550876453006856976195723454667228445079093740658164994058817885031515589864675057226220204438467761001755195739738871800548660409943242402199160325256318529251747013 : Int) ≠ 0 := by decide +kernel

theorem geometryRow078_jensenBound_parse :
    parseRational geometryRow078_jensenBoundText = .ok geometryRowsTyped078.jensenBound :=
  original_rational_fraction_of_chars geometryRow078_jensenBoundNumeratorChars geometryRow078_jensenBoundDenominatorChars
    (67756472962382223277141128390095924975794689234472951783929567850913157132199827762677605513010104172754744750769462984074509495673028641846119372320981332787200000000000000 : Int) (548460742267333767550876453006856976195723454667228445079093740658164994058817885031515589864675057226220204438467761001755195739738871800548660409943242402199160325256318529251747013 : Int)
    geometryRow078_jensenBound_numerator_no_slash geometryRow078_jensenBound_numerator_parse
    geometryRow078_jensenBound_denominator_parse geometryRow078_jensenBound_denominator_nonzero

theorem geometryRow078_jensenBound_read :
    rationalField geometryRowsJson078 "jensen_bound" = .ok geometryRowsTyped078.jensenBound :=
  original_rationalField_of_string geometryRowsJson078 "jensen_bound" geometryRow078_jensenBoundText
    geometryRowsTyped078.jensenBound geometryRow078_jensenBound_field geometryRow078_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_factorMaxima_before"
  err.flush

theorem geometryRow078_factorMaxima_read :
    rationalArrayField geometryRowsJson078 "factor_maxima" = .ok geometryRowsTyped078.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_gapWeightedMeans_before"
  err.flush

theorem geometryRow078_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson078 "gap_weighted_means" = .ok geometryRowsTyped078.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow078_floorChars : List Char := ['9', '7', '8', '7', '7', '9', '4', '1', '6', '2', '0', '1', '1', '9', '9', '7', '7', '3', '0']
noncomputable def geometryRow078_floorText : String := String.ofList geometryRow078_floorChars

theorem geometryRow078_floor_text_read :
    geometryRowsJson078.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow078_floorText := by rfl

theorem geometryRow078_floor_chars_parse :
    SourceJson.intChars geometryRow078_floorChars = some (9787794162011997730 : Int) := by decide +kernel

theorem geometryRow078_floor_parse :
    parseInteger geometryRow078_floorText = .ok geometryRowsTyped078.jensenFloorQ96 := by
  simp only [geometryRow078_floorText, parseInteger, String.toList_ofList, geometryRow078_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_078 :
    decodeGeometryRow geometryRowsJson078 = .ok geometryRowsTyped078 :=
  original_geometryRow_of_fields geometryRowsJson078 geometryRowsTyped078 geometryRow078_floorText
    geometryRow078_simplexId_read geometryRow078_vertexIds_read
    geometryRow078_physicalVolume_read geometryRow078_meanGap_read
    geometryRow078_factorMaxima_read geometryRow078_gapWeightedMeans_read
    geometryRow078_jensenBound_read geometryRow078_floor_text_read geometryRow078_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_078_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock039 : List SourceJson := [geometryRowsJson077, geometryRowsJson078]
noncomputable def geometryRowsTypedBlock039 : List (GeometryRow) := [geometryRowsTyped077, geometryRowsTyped078]
noncomputable def geometryRowsTypedThroughBlock039 : List (GeometryRow) := geometryRowsTypedThroughBlock038 ++ geometryRowsTypedBlock039

theorem geometry_Rows_block_039_push_eq (acc : List SourceJson) :
    SimplicesBlock039.blockPush acc = [geometryRowsJson078, geometryRowsJson077] ++ acc := by rfl

theorem geometry_Rows_block_039_reverse (acc : List SourceJson) :
    (SimplicesBlock039.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock039 := by
  rw [geometry_Rows_block_039_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_039 :
    geometryRowsJsonBlock039.mapM decodeGeometryRow = .ok geometryRowsTypedBlock039 := by
  simp only [geometryRowsJsonBlock039, geometryRowsTypedBlock039, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_077, decode_geometry_Rows_078]
  rfl

theorem decode_geometry_Rows_through_block_039 :
    SimplicesValue.arrayAcc040.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock039 := by
  change (SimplicesBlock039.blockPush SimplicesValue.arrayAcc039).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_039_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_038, decode_geometry_Rows_block_039]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_039_complete"
  err.flush

#print axioms geometryRow077_simplexId_read
#print axioms geometryRow077_vertexIds_read
#print axioms geometryRow077_physicalVolume_field
#print axioms geometryRow077_physicalVolume_numerator_no_slash
#print axioms geometryRow077_physicalVolume_numerator_parse
#print axioms geometryRow077_physicalVolume_denominator_parse
#print axioms geometryRow077_physicalVolume_denominator_nonzero
#print axioms geometryRow077_physicalVolume_parse
#print axioms geometryRow077_physicalVolume_read
#print axioms geometryRow077_meanGap_field
#print axioms geometryRow077_meanGap_numerator_no_slash
#print axioms geometryRow077_meanGap_numerator_parse
#print axioms geometryRow077_meanGap_denominator_parse
#print axioms geometryRow077_meanGap_denominator_nonzero
#print axioms geometryRow077_meanGap_parse
#print axioms geometryRow077_meanGap_read
#print axioms geometryRow077_jensenBound_field
#print axioms geometryRow077_jensenBound_numerator_no_slash
#print axioms geometryRow077_jensenBound_numerator_parse
#print axioms geometryRow077_jensenBound_denominator_parse
#print axioms geometryRow077_jensenBound_denominator_nonzero
#print axioms geometryRow077_jensenBound_parse
#print axioms geometryRow077_jensenBound_read
#print axioms geometryRow077_factorMaxima_read
#print axioms geometryRow077_gapWeightedMeans_read
#print axioms geometryRow077_floor_text_read
#print axioms geometryRow077_floor_chars_parse
#print axioms geometryRow077_floor_parse
#print axioms decode_geometry_Rows_077
#print axioms geometryRow078_simplexId_read
#print axioms geometryRow078_vertexIds_read
#print axioms geometryRow078_physicalVolume_field
#print axioms geometryRow078_physicalVolume_numerator_no_slash
#print axioms geometryRow078_physicalVolume_numerator_parse
#print axioms geometryRow078_physicalVolume_denominator_parse
#print axioms geometryRow078_physicalVolume_denominator_nonzero
#print axioms geometryRow078_physicalVolume_parse
#print axioms geometryRow078_physicalVolume_read
#print axioms geometryRow078_meanGap_field
#print axioms geometryRow078_meanGap_numerator_no_slash
#print axioms geometryRow078_meanGap_numerator_parse
#print axioms geometryRow078_meanGap_denominator_parse
#print axioms geometryRow078_meanGap_denominator_nonzero
#print axioms geometryRow078_meanGap_parse
#print axioms geometryRow078_meanGap_read
#print axioms geometryRow078_jensenBound_field
#print axioms geometryRow078_jensenBound_numerator_no_slash
#print axioms geometryRow078_jensenBound_numerator_parse
#print axioms geometryRow078_jensenBound_denominator_parse
#print axioms geometryRow078_jensenBound_denominator_nonzero
#print axioms geometryRow078_jensenBound_parse
#print axioms geometryRow078_jensenBound_read
#print axioms geometryRow078_factorMaxima_read
#print axioms geometryRow078_gapWeightedMeans_read
#print axioms geometryRow078_floor_text_read
#print axioms geometryRow078_floor_chars_parse
#print axioms geometryRow078_floor_parse
#print axioms decode_geometry_Rows_078
#print axioms geometry_Rows_block_039_push_eq
#print axioms geometry_Rows_block_039_reverse
#print axioms decode_geometry_Rows_block_039
#print axioms decode_geometry_Rows_through_block_039

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
