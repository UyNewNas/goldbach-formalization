import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows010

/-! Original simplices typed block 11, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson022 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped022 : GeometryRow :=
  { simplexId := 22,
    vertexIds := #[39, 35, 29, 11, 10, 8, 6, 2, 0],
    physicalVolume := ((2276686508066719702039711717587732509 : ℚ) / (63897600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((76219421503 : ℚ) / (873600000000 : ℚ)), ((539969802361 : ℚ) / (6115200000000 : ℚ)), ((20191037527 : ℚ) / (141120000000 : ℚ)), ((694301196311 : ℚ) / (6115200000000 : ℚ)), ((1154429960867 : ℚ) / (18345600000000 : ℚ)), ((447006994153 : ℚ) / (9172800000000 : ℚ)), ((366625523657 : ℚ) / (9172800000000 : ℚ)), ((650151107209 : ℚ) / (18345600000000 : ℚ)), ((611460918889 : ℚ) / (18345600000000 : ℚ)), ((580571091817 : ℚ) / (18345600000000 : ℚ))],
    jensenBound := ((159144920343880541820237677548760820713756194812422581810576366323585344050141593600000000000000000000000 : ℚ) / (1095359948618307870898491410887872839286345232850502324409622632580824869908383270082418339881735147148269202520603 : ℚ)),
    jensenFloorQ96 := (11511065041431694013 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_simplexId_before"
  err.flush

theorem geometryRow022_simplexId_read :
    geometryRowsJson022.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped022.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_vertexIds_before"
  err.flush

theorem geometryRow022_vertexIds_read :
    geometryRowsJson022.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped022.vertexIds := by decide +kernel

noncomputable def geometryRow022_physicalVolumeNumeratorChars : List Char := ['2', '2', '7', '6', '6', '8', '6', '5', '0', '8', '0', '6', '6', '7', '1', '9', '7', '0', '2', '0', '3', '9', '7', '1', '1', '7', '1', '7', '5', '8', '7', '7', '3', '2', '5', '0', '9']
noncomputable def geometryRow022_physicalVolumeDenominatorChars : List Char := ['6', '3', '8', '9', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_physicalVolumeText : String := String.ofList (geometryRow022_physicalVolumeNumeratorChars ++ '/' :: geometryRow022_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_physicalVolume_before_field"
  err.flush

theorem geometryRow022_physicalVolume_field :
    geometryRowsJson022.getObjVal? "physical_volume" = .ok (.str geometryRow022_physicalVolumeText) := by rfl

theorem geometryRow022_physicalVolume_numerator_no_slash :
    geometryRow022_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeNumeratorChars = some (2276686508066719702039711717587732509 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeDenominatorChars = some (63897600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_nonzero : (63897600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_physicalVolume_parse :
    parseRational geometryRow022_physicalVolumeText = .ok geometryRowsTyped022.physicalVolume :=
  original_rational_fraction_of_chars geometryRow022_physicalVolumeNumeratorChars geometryRow022_physicalVolumeDenominatorChars
    (2276686508066719702039711717587732509 : Int) (63897600000000000000000000000000000000000000000000000000 : Int)
    geometryRow022_physicalVolume_numerator_no_slash geometryRow022_physicalVolume_numerator_parse
    geometryRow022_physicalVolume_denominator_parse geometryRow022_physicalVolume_denominator_nonzero

theorem geometryRow022_physicalVolume_read :
    rationalField geometryRowsJson022 "physical_volume" = .ok geometryRowsTyped022.physicalVolume :=
  original_rationalField_of_string geometryRowsJson022 "physical_volume" geometryRow022_physicalVolumeText
    geometryRowsTyped022.physicalVolume geometryRow022_physicalVolume_field geometryRow022_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_physicalVolume_complete"
  err.flush

noncomputable def geometryRow022_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow022_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_meanGapText : String := String.ofList (geometryRow022_meanGapNumeratorChars ++ '/' :: geometryRow022_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_meanGap_before_field"
  err.flush

theorem geometryRow022_meanGap_field :
    geometryRowsJson022.getObjVal? "mean_gap" = .ok (.str geometryRow022_meanGapText) := by rfl

theorem geometryRow022_meanGap_numerator_no_slash :
    geometryRow022_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_meanGap_numerator_parse :
    SourceJson.intChars geometryRow022_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_parse :
    SourceJson.intChars geometryRow022_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_meanGap_parse :
    parseRational geometryRow022_meanGapText = .ok geometryRowsTyped022.meanGap :=
  original_rational_fraction_of_chars geometryRow022_meanGapNumeratorChars geometryRow022_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow022_meanGap_numerator_no_slash geometryRow022_meanGap_numerator_parse
    geometryRow022_meanGap_denominator_parse geometryRow022_meanGap_denominator_nonzero

theorem geometryRow022_meanGap_read :
    rationalField geometryRowsJson022 "mean_gap" = .ok geometryRowsTyped022.meanGap :=
  original_rationalField_of_string geometryRowsJson022 "mean_gap" geometryRow022_meanGapText
    geometryRowsTyped022.meanGap geometryRow022_meanGap_field geometryRow022_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_meanGap_complete"
  err.flush

noncomputable def geometryRow022_jensenBoundNumeratorChars : List Char := ['1', '5', '9', '1', '4', '4', '9', '2', '0', '3', '4', '3', '8', '8', '0', '5', '4', '1', '8', '2', '0', '2', '3', '7', '6', '7', '7', '5', '4', '8', '7', '6', '0', '8', '2', '0', '7', '1', '3', '7', '5', '6', '1', '9', '4', '8', '1', '2', '4', '2', '2', '5', '8', '1', '8', '1', '0', '5', '7', '6', '3', '6', '6', '3', '2', '3', '5', '8', '5', '3', '4', '4', '0', '5', '0', '1', '4', '1', '5', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_jensenBoundDenominatorChars : List Char := ['1', '0', '9', '5', '3', '5', '9', '9', '4', '8', '6', '1', '8', '3', '0', '7', '8', '7', '0', '8', '9', '8', '4', '9', '1', '4', '1', '0', '8', '8', '7', '8', '7', '2', '8', '3', '9', '2', '8', '6', '3', '4', '5', '2', '3', '2', '8', '5', '0', '5', '0', '2', '3', '2', '4', '4', '0', '9', '6', '2', '2', '6', '3', '2', '5', '8', '0', '8', '2', '4', '8', '6', '9', '9', '0', '8', '3', '8', '3', '2', '7', '0', '0', '8', '2', '4', '1', '8', '3', '3', '9', '8', '8', '1', '7', '3', '5', '1', '4', '7', '1', '4', '8', '2', '6', '9', '2', '0', '2', '5', '2', '0', '6', '0', '3']
noncomputable def geometryRow022_jensenBoundText : String := String.ofList (geometryRow022_jensenBoundNumeratorChars ++ '/' :: geometryRow022_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_jensenBound_before_field"
  err.flush

theorem geometryRow022_jensenBound_field :
    geometryRowsJson022.getObjVal? "jensen_bound" = .ok (.str geometryRow022_jensenBoundText) := by rfl

theorem geometryRow022_jensenBound_numerator_no_slash :
    geometryRow022_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow022_jensenBoundNumeratorChars = some (159144920343880541820237677548760820713756194812422581810576366323585344050141593600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow022_jensenBoundDenominatorChars = some (1095359948618307870898491410887872839286345232850502324409622632580824869908383270082418339881735147148269202520603 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_nonzero : (1095359948618307870898491410887872839286345232850502324409622632580824869908383270082418339881735147148269202520603 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_jensenBound_parse :
    parseRational geometryRow022_jensenBoundText = .ok geometryRowsTyped022.jensenBound :=
  original_rational_fraction_of_chars geometryRow022_jensenBoundNumeratorChars geometryRow022_jensenBoundDenominatorChars
    (159144920343880541820237677548760820713756194812422581810576366323585344050141593600000000000000000000000 : Int) (1095359948618307870898491410887872839286345232850502324409622632580824869908383270082418339881735147148269202520603 : Int)
    geometryRow022_jensenBound_numerator_no_slash geometryRow022_jensenBound_numerator_parse
    geometryRow022_jensenBound_denominator_parse geometryRow022_jensenBound_denominator_nonzero

theorem geometryRow022_jensenBound_read :
    rationalField geometryRowsJson022 "jensen_bound" = .ok geometryRowsTyped022.jensenBound :=
  original_rationalField_of_string geometryRowsJson022 "jensen_bound" geometryRow022_jensenBoundText
    geometryRowsTyped022.jensenBound geometryRow022_jensenBound_field geometryRow022_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_factorMaxima_before"
  err.flush

theorem geometryRow022_factorMaxima_read :
    rationalArrayField geometryRowsJson022 "factor_maxima" = .ok geometryRowsTyped022.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_gapWeightedMeans_before"
  err.flush

theorem geometryRow022_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson022 "gap_weighted_means" = .ok geometryRowsTyped022.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow022_floorChars : List Char := ['1', '1', '5', '1', '1', '0', '6', '5', '0', '4', '1', '4', '3', '1', '6', '9', '4', '0', '1', '3']
noncomputable def geometryRow022_floorText : String := String.ofList geometryRow022_floorChars

theorem geometryRow022_floor_text_read :
    geometryRowsJson022.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow022_floorText := by rfl

theorem geometryRow022_floor_chars_parse :
    SourceJson.intChars geometryRow022_floorChars = some (11511065041431694013 : Int) := by decide +kernel

theorem geometryRow022_floor_parse :
    parseInteger geometryRow022_floorText = .ok geometryRowsTyped022.jensenFloorQ96 := by
  simp only [geometryRow022_floorText, parseInteger, String.toList_ofList, geometryRow022_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_022 :
    decodeGeometryRow geometryRowsJson022 = .ok geometryRowsTyped022 :=
  original_geometryRow_of_fields geometryRowsJson022 geometryRowsTyped022 geometryRow022_floorText
    geometryRow022_simplexId_read geometryRow022_vertexIds_read
    geometryRow022_physicalVolume_read geometryRow022_meanGap_read
    geometryRow022_factorMaxima_read geometryRow022_gapWeightedMeans_read
    geometryRow022_jensenBound_read geometryRow022_floor_text_read geometryRow022_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_022_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson023 : SourceJson :=
  (SimplicesBlock011.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped023 : GeometryRow :=
  { simplexId := 23,
    vertexIds := #[39, 35, 29, 11, 10, 7, 6, 2, 0],
    physicalVolume := ((48192245695603846300830798301108450435801 : ℚ) / (832359628800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((5774199451 : ℚ) / (67200000000 : ℚ)), ((40914307837 : ℚ) / (470400000000 : ℚ)), ((2243448527 : ℚ) / (15680000000 : ℚ)), ((160845175961 : ℚ) / (1411200000000 : ℚ)), ((29497136293 : ℚ) / (470400000000 : ℚ)), ((3872390309 : ℚ) / (78400000000 : ℚ)), ((3142187261 : ℚ) / (78400000000 : ℚ)), ((16722355871 : ℚ) / (470400000000 : ℚ)), ((16144869311 : ℚ) / (470400000000 : ℚ)), ((44037483949 : ℚ) / (1411200000000 : ℚ))],
    jensenBound := ((85488535567134795017930160814378822574028827716876074791795050728652800000000000000000000000 : ℚ) / (363778204973767457503568106438184761402006331280858099794723821165959804685047672902927548183265668937 : ℚ)),
    jensenFloorQ96 := (18618761367267288538 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_simplexId_before"
  err.flush

theorem geometryRow023_simplexId_read :
    geometryRowsJson023.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped023.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_vertexIds_before"
  err.flush

theorem geometryRow023_vertexIds_read :
    geometryRowsJson023.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped023.vertexIds := by decide +kernel

noncomputable def geometryRow023_physicalVolumeNumeratorChars : List Char := ['4', '8', '1', '9', '2', '2', '4', '5', '6', '9', '5', '6', '0', '3', '8', '4', '6', '3', '0', '0', '8', '3', '0', '7', '9', '8', '3', '0', '1', '1', '0', '8', '4', '5', '0', '4', '3', '5', '8', '0', '1']
noncomputable def geometryRow023_physicalVolumeDenominatorChars : List Char := ['8', '3', '2', '3', '5', '9', '6', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_physicalVolumeText : String := String.ofList (geometryRow023_physicalVolumeNumeratorChars ++ '/' :: geometryRow023_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_physicalVolume_before_field"
  err.flush

theorem geometryRow023_physicalVolume_field :
    geometryRowsJson023.getObjVal? "physical_volume" = .ok (.str geometryRow023_physicalVolumeText) := by rfl

theorem geometryRow023_physicalVolume_numerator_no_slash :
    geometryRow023_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeNumeratorChars = some (48192245695603846300830798301108450435801 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeDenominatorChars = some (832359628800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_nonzero : (832359628800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_physicalVolume_parse :
    parseRational geometryRow023_physicalVolumeText = .ok geometryRowsTyped023.physicalVolume :=
  original_rational_fraction_of_chars geometryRow023_physicalVolumeNumeratorChars geometryRow023_physicalVolumeDenominatorChars
    (48192245695603846300830798301108450435801 : Int) (832359628800000000000000000000000000000000000000000000000000 : Int)
    geometryRow023_physicalVolume_numerator_no_slash geometryRow023_physicalVolume_numerator_parse
    geometryRow023_physicalVolume_denominator_parse geometryRow023_physicalVolume_denominator_nonzero

theorem geometryRow023_physicalVolume_read :
    rationalField geometryRowsJson023 "physical_volume" = .ok geometryRowsTyped023.physicalVolume :=
  original_rationalField_of_string geometryRowsJson023 "physical_volume" geometryRow023_physicalVolumeText
    geometryRowsTyped023.physicalVolume geometryRow023_physicalVolume_field geometryRow023_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_physicalVolume_complete"
  err.flush

noncomputable def geometryRow023_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow023_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_meanGapText : String := String.ofList (geometryRow023_meanGapNumeratorChars ++ '/' :: geometryRow023_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_meanGap_before_field"
  err.flush

theorem geometryRow023_meanGap_field :
    geometryRowsJson023.getObjVal? "mean_gap" = .ok (.str geometryRow023_meanGapText) := by rfl

theorem geometryRow023_meanGap_numerator_no_slash :
    geometryRow023_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_meanGap_numerator_parse :
    SourceJson.intChars geometryRow023_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_parse :
    SourceJson.intChars geometryRow023_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_meanGap_parse :
    parseRational geometryRow023_meanGapText = .ok geometryRowsTyped023.meanGap :=
  original_rational_fraction_of_chars geometryRow023_meanGapNumeratorChars geometryRow023_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow023_meanGap_numerator_no_slash geometryRow023_meanGap_numerator_parse
    geometryRow023_meanGap_denominator_parse geometryRow023_meanGap_denominator_nonzero

theorem geometryRow023_meanGap_read :
    rationalField geometryRowsJson023 "mean_gap" = .ok geometryRowsTyped023.meanGap :=
  original_rationalField_of_string geometryRowsJson023 "mean_gap" geometryRow023_meanGapText
    geometryRowsTyped023.meanGap geometryRow023_meanGap_field geometryRow023_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_meanGap_complete"
  err.flush

noncomputable def geometryRow023_jensenBoundNumeratorChars : List Char := ['8', '5', '4', '8', '8', '5', '3', '5', '5', '6', '7', '1', '3', '4', '7', '9', '5', '0', '1', '7', '9', '3', '0', '1', '6', '0', '8', '1', '4', '3', '7', '8', '8', '2', '2', '5', '7', '4', '0', '2', '8', '8', '2', '7', '7', '1', '6', '8', '7', '6', '0', '7', '4', '7', '9', '1', '7', '9', '5', '0', '5', '0', '7', '2', '8', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_jensenBoundDenominatorChars : List Char := ['3', '6', '3', '7', '7', '8', '2', '0', '4', '9', '7', '3', '7', '6', '7', '4', '5', '7', '5', '0', '3', '5', '6', '8', '1', '0', '6', '4', '3', '8', '1', '8', '4', '7', '6', '1', '4', '0', '2', '0', '0', '6', '3', '3', '1', '2', '8', '0', '8', '5', '8', '0', '9', '9', '7', '9', '4', '7', '2', '3', '8', '2', '1', '1', '6', '5', '9', '5', '9', '8', '0', '4', '6', '8', '5', '0', '4', '7', '6', '7', '2', '9', '0', '2', '9', '2', '7', '5', '4', '8', '1', '8', '3', '2', '6', '5', '6', '6', '8', '9', '3', '7']
noncomputable def geometryRow023_jensenBoundText : String := String.ofList (geometryRow023_jensenBoundNumeratorChars ++ '/' :: geometryRow023_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_jensenBound_before_field"
  err.flush

theorem geometryRow023_jensenBound_field :
    geometryRowsJson023.getObjVal? "jensen_bound" = .ok (.str geometryRow023_jensenBoundText) := by rfl

theorem geometryRow023_jensenBound_numerator_no_slash :
    geometryRow023_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow023_jensenBoundNumeratorChars = some (85488535567134795017930160814378822574028827716876074791795050728652800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow023_jensenBoundDenominatorChars = some (363778204973767457503568106438184761402006331280858099794723821165959804685047672902927548183265668937 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_nonzero : (363778204973767457503568106438184761402006331280858099794723821165959804685047672902927548183265668937 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_jensenBound_parse :
    parseRational geometryRow023_jensenBoundText = .ok geometryRowsTyped023.jensenBound :=
  original_rational_fraction_of_chars geometryRow023_jensenBoundNumeratorChars geometryRow023_jensenBoundDenominatorChars
    (85488535567134795017930160814378822574028827716876074791795050728652800000000000000000000000 : Int) (363778204973767457503568106438184761402006331280858099794723821165959804685047672902927548183265668937 : Int)
    geometryRow023_jensenBound_numerator_no_slash geometryRow023_jensenBound_numerator_parse
    geometryRow023_jensenBound_denominator_parse geometryRow023_jensenBound_denominator_nonzero

theorem geometryRow023_jensenBound_read :
    rationalField geometryRowsJson023 "jensen_bound" = .ok geometryRowsTyped023.jensenBound :=
  original_rationalField_of_string geometryRowsJson023 "jensen_bound" geometryRow023_jensenBoundText
    geometryRowsTyped023.jensenBound geometryRow023_jensenBound_field geometryRow023_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_factorMaxima_before"
  err.flush

theorem geometryRow023_factorMaxima_read :
    rationalArrayField geometryRowsJson023 "factor_maxima" = .ok geometryRowsTyped023.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_gapWeightedMeans_before"
  err.flush

theorem geometryRow023_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson023 "gap_weighted_means" = .ok geometryRowsTyped023.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow023_floorChars : List Char := ['1', '8', '6', '1', '8', '7', '6', '1', '3', '6', '7', '2', '6', '7', '2', '8', '8', '5', '3', '8']
noncomputable def geometryRow023_floorText : String := String.ofList geometryRow023_floorChars

theorem geometryRow023_floor_text_read :
    geometryRowsJson023.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow023_floorText := by rfl

theorem geometryRow023_floor_chars_parse :
    SourceJson.intChars geometryRow023_floorChars = some (18618761367267288538 : Int) := by decide +kernel

theorem geometryRow023_floor_parse :
    parseInteger geometryRow023_floorText = .ok geometryRowsTyped023.jensenFloorQ96 := by
  simp only [geometryRow023_floorText, parseInteger, String.toList_ofList, geometryRow023_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_023 :
    decodeGeometryRow geometryRowsJson023 = .ok geometryRowsTyped023 :=
  original_geometryRow_of_fields geometryRowsJson023 geometryRowsTyped023 geometryRow023_floorText
    geometryRow023_simplexId_read geometryRow023_vertexIds_read
    geometryRow023_physicalVolume_read geometryRow023_meanGap_read
    geometryRow023_factorMaxima_read geometryRow023_gapWeightedMeans_read
    geometryRow023_jensenBound_read geometryRow023_floor_text_read geometryRow023_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_023_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock011 : List SourceJson := [geometryRowsJson022, geometryRowsJson023]
noncomputable def geometryRowsTypedBlock011 : List (GeometryRow) := [geometryRowsTyped022, geometryRowsTyped023]
noncomputable def geometryRowsTypedThroughBlock011 : List (GeometryRow) := geometryRowsTypedThroughBlock010 ++ geometryRowsTypedBlock011

theorem geometry_Rows_block_011_push_eq (acc : List SourceJson) :
    SimplicesBlock011.blockPush acc = [geometryRowsJson023, geometryRowsJson022] ++ acc := by rfl

theorem geometry_Rows_block_011_reverse (acc : List SourceJson) :
    (SimplicesBlock011.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock011 := by
  rw [geometry_Rows_block_011_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_011 :
    geometryRowsJsonBlock011.mapM decodeGeometryRow = .ok geometryRowsTypedBlock011 := by
  simp only [geometryRowsJsonBlock011, geometryRowsTypedBlock011, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_022, decode_geometry_Rows_023]
  rfl

theorem decode_geometry_Rows_through_block_011 :
    SimplicesValue.arrayAcc012.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock011 := by
  change (SimplicesBlock011.blockPush SimplicesValue.arrayAcc011).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_011_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_010, decode_geometry_Rows_block_011]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_011_complete"
  err.flush

#print axioms geometryRow022_simplexId_read
#print axioms geometryRow022_vertexIds_read
#print axioms geometryRow022_physicalVolume_field
#print axioms geometryRow022_physicalVolume_numerator_no_slash
#print axioms geometryRow022_physicalVolume_numerator_parse
#print axioms geometryRow022_physicalVolume_denominator_parse
#print axioms geometryRow022_physicalVolume_denominator_nonzero
#print axioms geometryRow022_physicalVolume_parse
#print axioms geometryRow022_physicalVolume_read
#print axioms geometryRow022_meanGap_field
#print axioms geometryRow022_meanGap_numerator_no_slash
#print axioms geometryRow022_meanGap_numerator_parse
#print axioms geometryRow022_meanGap_denominator_parse
#print axioms geometryRow022_meanGap_denominator_nonzero
#print axioms geometryRow022_meanGap_parse
#print axioms geometryRow022_meanGap_read
#print axioms geometryRow022_jensenBound_field
#print axioms geometryRow022_jensenBound_numerator_no_slash
#print axioms geometryRow022_jensenBound_numerator_parse
#print axioms geometryRow022_jensenBound_denominator_parse
#print axioms geometryRow022_jensenBound_denominator_nonzero
#print axioms geometryRow022_jensenBound_parse
#print axioms geometryRow022_jensenBound_read
#print axioms geometryRow022_factorMaxima_read
#print axioms geometryRow022_gapWeightedMeans_read
#print axioms geometryRow022_floor_text_read
#print axioms geometryRow022_floor_chars_parse
#print axioms geometryRow022_floor_parse
#print axioms decode_geometry_Rows_022
#print axioms geometryRow023_simplexId_read
#print axioms geometryRow023_vertexIds_read
#print axioms geometryRow023_physicalVolume_field
#print axioms geometryRow023_physicalVolume_numerator_no_slash
#print axioms geometryRow023_physicalVolume_numerator_parse
#print axioms geometryRow023_physicalVolume_denominator_parse
#print axioms geometryRow023_physicalVolume_denominator_nonzero
#print axioms geometryRow023_physicalVolume_parse
#print axioms geometryRow023_physicalVolume_read
#print axioms geometryRow023_meanGap_field
#print axioms geometryRow023_meanGap_numerator_no_slash
#print axioms geometryRow023_meanGap_numerator_parse
#print axioms geometryRow023_meanGap_denominator_parse
#print axioms geometryRow023_meanGap_denominator_nonzero
#print axioms geometryRow023_meanGap_parse
#print axioms geometryRow023_meanGap_read
#print axioms geometryRow023_jensenBound_field
#print axioms geometryRow023_jensenBound_numerator_no_slash
#print axioms geometryRow023_jensenBound_numerator_parse
#print axioms geometryRow023_jensenBound_denominator_parse
#print axioms geometryRow023_jensenBound_denominator_nonzero
#print axioms geometryRow023_jensenBound_parse
#print axioms geometryRow023_jensenBound_read
#print axioms geometryRow023_factorMaxima_read
#print axioms geometryRow023_gapWeightedMeans_read
#print axioms geometryRow023_floor_text_read
#print axioms geometryRow023_floor_chars_parse
#print axioms geometryRow023_floor_parse
#print axioms decode_geometry_Rows_023
#print axioms geometry_Rows_block_011_push_eq
#print axioms geometry_Rows_block_011_reverse
#print axioms decode_geometry_Rows_block_011
#print axioms decode_geometry_Rows_through_block_011

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
