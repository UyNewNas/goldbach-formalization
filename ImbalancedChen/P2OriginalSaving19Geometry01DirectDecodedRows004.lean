import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows003

/-! Original simplices typed block 4, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson008 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped008 : GeometryRow :=
  { simplexId := 8,
    vertexIds := #[39, 35, 29, 28, 25, 8, 6, 2, 0],
    physicalVolume := ((488506857691520479650229885835901605566512043 : ℚ) / (24481569492172800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1831380062051 : ℚ) / (21403200000000 : ℚ)), ((1853898543491 : ℚ) / (21403200000000 : ℚ)), ((2036974777 : ℚ) / (14112000000 : ℚ)), ((2469157162201 : ℚ) / (21403200000000 : ℚ)), ((610916210431 : ℚ) / (9172800000000 : ℚ)), ((1505224637213 : ℚ) / (32104800000000 : ℚ)), ((196756478969 : ℚ) / (5241600000000 : ℚ)), ((185881242779 : ℚ) / (5241600000000 : ℚ)), ((2104117451339 : ℚ) / (64209600000000 : ℚ)), ((1996003056587 : ℚ) / (64209600000000 : ℚ))],
    jensenBound := ((215329511528360583510586641041050517084260577346293932376970400661171110201288336343040000000000000000000000 : ℚ) / (2412001576354872528213657058848576018006086043012714806372601624302376587105080653490135288941382832750072905369116953 : ℚ)),
    jensenFloorQ96 := (7073030839087679012 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_simplexId_before"
  err.flush

theorem geometryRow008_simplexId_read :
    geometryRowsJson008.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped008.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_vertexIds_before"
  err.flush

theorem geometryRow008_vertexIds_read :
    geometryRowsJson008.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped008.vertexIds := by decide +kernel

noncomputable def geometryRow008_physicalVolumeNumeratorChars : List Char := ['4', '8', '8', '5', '0', '6', '8', '5', '7', '6', '9', '1', '5', '2', '0', '4', '7', '9', '6', '5', '0', '2', '2', '9', '8', '8', '5', '8', '3', '5', '9', '0', '1', '6', '0', '5', '5', '6', '6', '5', '1', '2', '0', '4', '3']
noncomputable def geometryRow008_physicalVolumeDenominatorChars : List Char := ['2', '4', '4', '8', '1', '5', '6', '9', '4', '9', '2', '1', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_physicalVolumeText : String := String.ofList (geometryRow008_physicalVolumeNumeratorChars ++ '/' :: geometryRow008_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_physicalVolume_before_field"
  err.flush

theorem geometryRow008_physicalVolume_field :
    geometryRowsJson008.getObjVal? "physical_volume" = .ok (.str geometryRow008_physicalVolumeText) := by rfl

theorem geometryRow008_physicalVolume_numerator_no_slash :
    geometryRow008_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeNumeratorChars = some (488506857691520479650229885835901605566512043 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow008_physicalVolumeDenominatorChars = some (24481569492172800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_physicalVolume_denominator_nonzero : (24481569492172800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_physicalVolume_parse :
    parseRational geometryRow008_physicalVolumeText = .ok geometryRowsTyped008.physicalVolume :=
  original_rational_fraction_of_chars geometryRow008_physicalVolumeNumeratorChars geometryRow008_physicalVolumeDenominatorChars
    (488506857691520479650229885835901605566512043 : Int) (24481569492172800000000000000000000000000000000000000000000000000 : Int)
    geometryRow008_physicalVolume_numerator_no_slash geometryRow008_physicalVolume_numerator_parse
    geometryRow008_physicalVolume_denominator_parse geometryRow008_physicalVolume_denominator_nonzero

theorem geometryRow008_physicalVolume_read :
    rationalField geometryRowsJson008 "physical_volume" = .ok geometryRowsTyped008.physicalVolume :=
  original_rationalField_of_string geometryRowsJson008 "physical_volume" geometryRow008_physicalVolumeText
    geometryRowsTyped008.physicalVolume geometryRow008_physicalVolume_field geometryRow008_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_physicalVolume_complete"
  err.flush

noncomputable def geometryRow008_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow008_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_meanGapText : String := String.ofList (geometryRow008_meanGapNumeratorChars ++ '/' :: geometryRow008_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_meanGap_before_field"
  err.flush

theorem geometryRow008_meanGap_field :
    geometryRowsJson008.getObjVal? "mean_gap" = .ok (.str geometryRow008_meanGapText) := by rfl

theorem geometryRow008_meanGap_numerator_no_slash :
    geometryRow008_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_meanGap_numerator_parse :
    SourceJson.intChars geometryRow008_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_parse :
    SourceJson.intChars geometryRow008_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow008_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_meanGap_parse :
    parseRational geometryRow008_meanGapText = .ok geometryRowsTyped008.meanGap :=
  original_rational_fraction_of_chars geometryRow008_meanGapNumeratorChars geometryRow008_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow008_meanGap_numerator_no_slash geometryRow008_meanGap_numerator_parse
    geometryRow008_meanGap_denominator_parse geometryRow008_meanGap_denominator_nonzero

theorem geometryRow008_meanGap_read :
    rationalField geometryRowsJson008 "mean_gap" = .ok geometryRowsTyped008.meanGap :=
  original_rationalField_of_string geometryRowsJson008 "mean_gap" geometryRow008_meanGapText
    geometryRowsTyped008.meanGap geometryRow008_meanGap_field geometryRow008_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_meanGap_complete"
  err.flush

noncomputable def geometryRow008_jensenBoundNumeratorChars : List Char := ['2', '1', '5', '3', '2', '9', '5', '1', '1', '5', '2', '8', '3', '6', '0', '5', '8', '3', '5', '1', '0', '5', '8', '6', '6', '4', '1', '0', '4', '1', '0', '5', '0', '5', '1', '7', '0', '8', '4', '2', '6', '0', '5', '7', '7', '3', '4', '6', '2', '9', '3', '9', '3', '2', '3', '7', '6', '9', '7', '0', '4', '0', '0', '6', '6', '1', '1', '7', '1', '1', '1', '0', '2', '0', '1', '2', '8', '8', '3', '3', '6', '3', '4', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow008_jensenBoundDenominatorChars : List Char := ['2', '4', '1', '2', '0', '0', '1', '5', '7', '6', '3', '5', '4', '8', '7', '2', '5', '2', '8', '2', '1', '3', '6', '5', '7', '0', '5', '8', '8', '4', '8', '5', '7', '6', '0', '1', '8', '0', '0', '6', '0', '8', '6', '0', '4', '3', '0', '1', '2', '7', '1', '4', '8', '0', '6', '3', '7', '2', '6', '0', '1', '6', '2', '4', '3', '0', '2', '3', '7', '6', '5', '8', '7', '1', '0', '5', '0', '8', '0', '6', '5', '3', '4', '9', '0', '1', '3', '5', '2', '8', '8', '9', '4', '1', '3', '8', '2', '8', '3', '2', '7', '5', '0', '0', '7', '2', '9', '0', '5', '3', '6', '9', '1', '1', '6', '9', '5', '3']
noncomputable def geometryRow008_jensenBoundText : String := String.ofList (geometryRow008_jensenBoundNumeratorChars ++ '/' :: geometryRow008_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_jensenBound_before_field"
  err.flush

theorem geometryRow008_jensenBound_field :
    geometryRowsJson008.getObjVal? "jensen_bound" = .ok (.str geometryRow008_jensenBoundText) := by rfl

theorem geometryRow008_jensenBound_numerator_no_slash :
    geometryRow008_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow008_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow008_jensenBoundNumeratorChars = some (215329511528360583510586641041050517084260577346293932376970400661171110201288336343040000000000000000000000 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow008_jensenBoundDenominatorChars = some (2412001576354872528213657058848576018006086043012714806372601624302376587105080653490135288941382832750072905369116953 : Int) := by decide +kernel

theorem geometryRow008_jensenBound_denominator_nonzero : (2412001576354872528213657058848576018006086043012714806372601624302376587105080653490135288941382832750072905369116953 : Int) ≠ 0 := by decide +kernel

theorem geometryRow008_jensenBound_parse :
    parseRational geometryRow008_jensenBoundText = .ok geometryRowsTyped008.jensenBound :=
  original_rational_fraction_of_chars geometryRow008_jensenBoundNumeratorChars geometryRow008_jensenBoundDenominatorChars
    (215329511528360583510586641041050517084260577346293932376970400661171110201288336343040000000000000000000000 : Int) (2412001576354872528213657058848576018006086043012714806372601624302376587105080653490135288941382832750072905369116953 : Int)
    geometryRow008_jensenBound_numerator_no_slash geometryRow008_jensenBound_numerator_parse
    geometryRow008_jensenBound_denominator_parse geometryRow008_jensenBound_denominator_nonzero

theorem geometryRow008_jensenBound_read :
    rationalField geometryRowsJson008 "jensen_bound" = .ok geometryRowsTyped008.jensenBound :=
  original_rationalField_of_string geometryRowsJson008 "jensen_bound" geometryRow008_jensenBoundText
    geometryRowsTyped008.jensenBound geometryRow008_jensenBound_field geometryRow008_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_factorMaxima_before"
  err.flush

theorem geometryRow008_factorMaxima_read :
    rationalArrayField geometryRowsJson008 "factor_maxima" = .ok geometryRowsTyped008.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_gapWeightedMeans_before"
  err.flush

theorem geometryRow008_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson008 "gap_weighted_means" = .ok geometryRowsTyped008.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow008_floorChars : List Char := ['7', '0', '7', '3', '0', '3', '0', '8', '3', '9', '0', '8', '7', '6', '7', '9', '0', '1', '2']
noncomputable def geometryRow008_floorText : String := String.ofList geometryRow008_floorChars

theorem geometryRow008_floor_text_read :
    geometryRowsJson008.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow008_floorText := by rfl

theorem geometryRow008_floor_chars_parse :
    SourceJson.intChars geometryRow008_floorChars = some (7073030839087679012 : Int) := by decide +kernel

theorem geometryRow008_floor_parse :
    parseInteger geometryRow008_floorText = .ok geometryRowsTyped008.jensenFloorQ96 := by
  simp only [geometryRow008_floorText, parseInteger, String.toList_ofList, geometryRow008_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_008 :
    decodeGeometryRow geometryRowsJson008 = .ok geometryRowsTyped008 :=
  original_geometryRow_of_fields geometryRowsJson008 geometryRowsTyped008 geometryRow008_floorText
    geometryRow008_simplexId_read geometryRow008_vertexIds_read
    geometryRow008_physicalVolume_read geometryRow008_meanGap_read
    geometryRow008_factorMaxima_read geometryRow008_gapWeightedMeans_read
    geometryRow008_jensenBound_read geometryRow008_floor_text_read geometryRow008_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_008_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson009 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped009 : GeometryRow :=
  { simplexId := 9,
    vertexIds := #[39, 35, 29, 28, 25, 17, 12, 2, 0],
    physicalVolume := ((234026578912290907284490465316464267894116998159 : ℚ) / (10549924346493665280000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((2784283 : ℚ) / (33600000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((13991664877411 : ℚ) / (166286400000000 : ℚ)), ((14166616156291 : ℚ) / (166286400000000 : ℚ)), ((5172468266123 : ℚ) / (35632800000000 : ℚ)), ((19398200735173 : ℚ) / (166286400000000 : ℚ)), ((5012844678563 : ℚ) / (71265600000000 : ℚ)), ((11675277640339 : ℚ) / (249429600000000 : ℚ)), ((209876774119 : ℚ) / (5817600000000 : ℚ)), ((197806457029 : ℚ) / (5817600000000 : ℚ)), ((16058038926283 : ℚ) / (498859200000000 : ℚ)), ((15270658911883 : ℚ) / (498859200000000 : ℚ))],
    jensenBound := ((7527812214418449871102223419036708436002646123935656269416746422504929071698270511409397760000000000000000000000000 : ℚ) / (70115606309865674812176075006440401697655073854635529865362570353027529690190964086105887552419259006710763017432241981131893 : ℚ)),
    jensenFloorQ96 := (8506162335173161194 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_simplexId_before"
  err.flush

theorem geometryRow009_simplexId_read :
    geometryRowsJson009.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped009.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_vertexIds_before"
  err.flush

theorem geometryRow009_vertexIds_read :
    geometryRowsJson009.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped009.vertexIds := by decide +kernel

noncomputable def geometryRow009_physicalVolumeNumeratorChars : List Char := ['2', '3', '4', '0', '2', '6', '5', '7', '8', '9', '1', '2', '2', '9', '0', '9', '0', '7', '2', '8', '4', '4', '9', '0', '4', '6', '5', '3', '1', '6', '4', '6', '4', '2', '6', '7', '8', '9', '4', '1', '1', '6', '9', '9', '8', '1', '5', '9']
noncomputable def geometryRow009_physicalVolumeDenominatorChars : List Char := ['1', '0', '5', '4', '9', '9', '2', '4', '3', '4', '6', '4', '9', '3', '6', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_physicalVolumeText : String := String.ofList (geometryRow009_physicalVolumeNumeratorChars ++ '/' :: geometryRow009_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_physicalVolume_before_field"
  err.flush

theorem geometryRow009_physicalVolume_field :
    geometryRowsJson009.getObjVal? "physical_volume" = .ok (.str geometryRow009_physicalVolumeText) := by rfl

theorem geometryRow009_physicalVolume_numerator_no_slash :
    geometryRow009_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeNumeratorChars = some (234026578912290907284490465316464267894116998159 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow009_physicalVolumeDenominatorChars = some (10549924346493665280000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_physicalVolume_denominator_nonzero : (10549924346493665280000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_physicalVolume_parse :
    parseRational geometryRow009_physicalVolumeText = .ok geometryRowsTyped009.physicalVolume :=
  original_rational_fraction_of_chars geometryRow009_physicalVolumeNumeratorChars geometryRow009_physicalVolumeDenominatorChars
    (234026578912290907284490465316464267894116998159 : Int) (10549924346493665280000000000000000000000000000000000000000000000000 : Int)
    geometryRow009_physicalVolume_numerator_no_slash geometryRow009_physicalVolume_numerator_parse
    geometryRow009_physicalVolume_denominator_parse geometryRow009_physicalVolume_denominator_nonzero

theorem geometryRow009_physicalVolume_read :
    rationalField geometryRowsJson009 "physical_volume" = .ok geometryRowsTyped009.physicalVolume :=
  original_rationalField_of_string geometryRowsJson009 "physical_volume" geometryRow009_physicalVolumeText
    geometryRowsTyped009.physicalVolume geometryRow009_physicalVolume_field geometryRow009_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_physicalVolume_complete"
  err.flush

noncomputable def geometryRow009_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow009_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_meanGapText : String := String.ofList (geometryRow009_meanGapNumeratorChars ++ '/' :: geometryRow009_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_meanGap_before_field"
  err.flush

theorem geometryRow009_meanGap_field :
    geometryRowsJson009.getObjVal? "mean_gap" = .ok (.str geometryRow009_meanGapText) := by rfl

theorem geometryRow009_meanGap_numerator_no_slash :
    geometryRow009_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_meanGap_numerator_parse :
    SourceJson.intChars geometryRow009_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_parse :
    SourceJson.intChars geometryRow009_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow009_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_meanGap_parse :
    parseRational geometryRow009_meanGapText = .ok geometryRowsTyped009.meanGap :=
  original_rational_fraction_of_chars geometryRow009_meanGapNumeratorChars geometryRow009_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow009_meanGap_numerator_no_slash geometryRow009_meanGap_numerator_parse
    geometryRow009_meanGap_denominator_parse geometryRow009_meanGap_denominator_nonzero

theorem geometryRow009_meanGap_read :
    rationalField geometryRowsJson009 "mean_gap" = .ok geometryRowsTyped009.meanGap :=
  original_rationalField_of_string geometryRowsJson009 "mean_gap" geometryRow009_meanGapText
    geometryRowsTyped009.meanGap geometryRow009_meanGap_field geometryRow009_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_meanGap_complete"
  err.flush

noncomputable def geometryRow009_jensenBoundNumeratorChars : List Char := ['7', '5', '2', '7', '8', '1', '2', '2', '1', '4', '4', '1', '8', '4', '4', '9', '8', '7', '1', '1', '0', '2', '2', '2', '3', '4', '1', '9', '0', '3', '6', '7', '0', '8', '4', '3', '6', '0', '0', '2', '6', '4', '6', '1', '2', '3', '9', '3', '5', '6', '5', '6', '2', '6', '9', '4', '1', '6', '7', '4', '6', '4', '2', '2', '5', '0', '4', '9', '2', '9', '0', '7', '1', '6', '9', '8', '2', '7', '0', '5', '1', '1', '4', '0', '9', '3', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow009_jensenBoundDenominatorChars : List Char := ['7', '0', '1', '1', '5', '6', '0', '6', '3', '0', '9', '8', '6', '5', '6', '7', '4', '8', '1', '2', '1', '7', '6', '0', '7', '5', '0', '0', '6', '4', '4', '0', '4', '0', '1', '6', '9', '7', '6', '5', '5', '0', '7', '3', '8', '5', '4', '6', '3', '5', '5', '2', '9', '8', '6', '5', '3', '6', '2', '5', '7', '0', '3', '5', '3', '0', '2', '7', '5', '2', '9', '6', '9', '0', '1', '9', '0', '9', '6', '4', '0', '8', '6', '1', '0', '5', '8', '8', '7', '5', '5', '2', '4', '1', '9', '2', '5', '9', '0', '0', '6', '7', '1', '0', '7', '6', '3', '0', '1', '7', '4', '3', '2', '2', '4', '1', '9', '8', '1', '1', '3', '1', '8', '9', '3']
noncomputable def geometryRow009_jensenBoundText : String := String.ofList (geometryRow009_jensenBoundNumeratorChars ++ '/' :: geometryRow009_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_jensenBound_before_field"
  err.flush

theorem geometryRow009_jensenBound_field :
    geometryRowsJson009.getObjVal? "jensen_bound" = .ok (.str geometryRow009_jensenBoundText) := by rfl

theorem geometryRow009_jensenBound_numerator_no_slash :
    geometryRow009_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow009_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow009_jensenBoundNumeratorChars = some (7527812214418449871102223419036708436002646123935656269416746422504929071698270511409397760000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow009_jensenBoundDenominatorChars = some (70115606309865674812176075006440401697655073854635529865362570353027529690190964086105887552419259006710763017432241981131893 : Int) := by decide +kernel

theorem geometryRow009_jensenBound_denominator_nonzero : (70115606309865674812176075006440401697655073854635529865362570353027529690190964086105887552419259006710763017432241981131893 : Int) ≠ 0 := by decide +kernel

theorem geometryRow009_jensenBound_parse :
    parseRational geometryRow009_jensenBoundText = .ok geometryRowsTyped009.jensenBound :=
  original_rational_fraction_of_chars geometryRow009_jensenBoundNumeratorChars geometryRow009_jensenBoundDenominatorChars
    (7527812214418449871102223419036708436002646123935656269416746422504929071698270511409397760000000000000000000000000 : Int) (70115606309865674812176075006440401697655073854635529865362570353027529690190964086105887552419259006710763017432241981131893 : Int)
    geometryRow009_jensenBound_numerator_no_slash geometryRow009_jensenBound_numerator_parse
    geometryRow009_jensenBound_denominator_parse geometryRow009_jensenBound_denominator_nonzero

theorem geometryRow009_jensenBound_read :
    rationalField geometryRowsJson009 "jensen_bound" = .ok geometryRowsTyped009.jensenBound :=
  original_rationalField_of_string geometryRowsJson009 "jensen_bound" geometryRow009_jensenBoundText
    geometryRowsTyped009.jensenBound geometryRow009_jensenBound_field geometryRow009_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_factorMaxima_before"
  err.flush

theorem geometryRow009_factorMaxima_read :
    rationalArrayField geometryRowsJson009 "factor_maxima" = .ok geometryRowsTyped009.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_gapWeightedMeans_before"
  err.flush

theorem geometryRow009_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson009 "gap_weighted_means" = .ok geometryRowsTyped009.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow009_floorChars : List Char := ['8', '5', '0', '6', '1', '6', '2', '3', '3', '5', '1', '7', '3', '1', '6', '1', '1', '9', '4']
noncomputable def geometryRow009_floorText : String := String.ofList geometryRow009_floorChars

theorem geometryRow009_floor_text_read :
    geometryRowsJson009.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow009_floorText := by rfl

theorem geometryRow009_floor_chars_parse :
    SourceJson.intChars geometryRow009_floorChars = some (8506162335173161194 : Int) := by decide +kernel

theorem geometryRow009_floor_parse :
    parseInteger geometryRow009_floorText = .ok geometryRowsTyped009.jensenFloorQ96 := by
  simp only [geometryRow009_floorText, parseInteger, String.toList_ofList, geometryRow009_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_009 :
    decodeGeometryRow geometryRowsJson009 = .ok geometryRowsTyped009 :=
  original_geometryRow_of_fields geometryRowsJson009 geometryRowsTyped009 geometryRow009_floorText
    geometryRow009_simplexId_read geometryRow009_vertexIds_read
    geometryRow009_physicalVolume_read geometryRow009_meanGap_read
    geometryRow009_factorMaxima_read geometryRow009_gapWeightedMeans_read
    geometryRow009_jensenBound_read geometryRow009_floor_text_read geometryRow009_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_009_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock004 : List SourceJson := [geometryRowsJson008, geometryRowsJson009]
noncomputable def geometryRowsTypedBlock004 : List (GeometryRow) := [geometryRowsTyped008, geometryRowsTyped009]
noncomputable def geometryRowsTypedThroughBlock004 : List (GeometryRow) := geometryRowsTypedThroughBlock003 ++ geometryRowsTypedBlock004

theorem geometry_Rows_block_004_push_eq (acc : List SourceJson) :
    SimplicesBlock004.blockPush acc = [geometryRowsJson009, geometryRowsJson008] ++ acc := by rfl

theorem geometry_Rows_block_004_reverse (acc : List SourceJson) :
    (SimplicesBlock004.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock004 := by
  rw [geometry_Rows_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_004 :
    geometryRowsJsonBlock004.mapM decodeGeometryRow = .ok geometryRowsTypedBlock004 := by
  simp only [geometryRowsJsonBlock004, geometryRowsTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_008, decode_geometry_Rows_009]
  rfl

theorem decode_geometry_Rows_through_block_004 :
    SimplicesValue.arrayAcc005.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock004 := by
  change (SimplicesBlock004.blockPush SimplicesValue.arrayAcc004).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_004_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_003, decode_geometry_Rows_block_004]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_004_complete"
  err.flush

#print axioms geometryRow008_simplexId_read
#print axioms geometryRow008_vertexIds_read
#print axioms geometryRow008_physicalVolume_field
#print axioms geometryRow008_physicalVolume_numerator_no_slash
#print axioms geometryRow008_physicalVolume_numerator_parse
#print axioms geometryRow008_physicalVolume_denominator_parse
#print axioms geometryRow008_physicalVolume_denominator_nonzero
#print axioms geometryRow008_physicalVolume_parse
#print axioms geometryRow008_physicalVolume_read
#print axioms geometryRow008_meanGap_field
#print axioms geometryRow008_meanGap_numerator_no_slash
#print axioms geometryRow008_meanGap_numerator_parse
#print axioms geometryRow008_meanGap_denominator_parse
#print axioms geometryRow008_meanGap_denominator_nonzero
#print axioms geometryRow008_meanGap_parse
#print axioms geometryRow008_meanGap_read
#print axioms geometryRow008_jensenBound_field
#print axioms geometryRow008_jensenBound_numerator_no_slash
#print axioms geometryRow008_jensenBound_numerator_parse
#print axioms geometryRow008_jensenBound_denominator_parse
#print axioms geometryRow008_jensenBound_denominator_nonzero
#print axioms geometryRow008_jensenBound_parse
#print axioms geometryRow008_jensenBound_read
#print axioms geometryRow008_factorMaxima_read
#print axioms geometryRow008_gapWeightedMeans_read
#print axioms geometryRow008_floor_text_read
#print axioms geometryRow008_floor_chars_parse
#print axioms geometryRow008_floor_parse
#print axioms decode_geometry_Rows_008
#print axioms geometryRow009_simplexId_read
#print axioms geometryRow009_vertexIds_read
#print axioms geometryRow009_physicalVolume_field
#print axioms geometryRow009_physicalVolume_numerator_no_slash
#print axioms geometryRow009_physicalVolume_numerator_parse
#print axioms geometryRow009_physicalVolume_denominator_parse
#print axioms geometryRow009_physicalVolume_denominator_nonzero
#print axioms geometryRow009_physicalVolume_parse
#print axioms geometryRow009_physicalVolume_read
#print axioms geometryRow009_meanGap_field
#print axioms geometryRow009_meanGap_numerator_no_slash
#print axioms geometryRow009_meanGap_numerator_parse
#print axioms geometryRow009_meanGap_denominator_parse
#print axioms geometryRow009_meanGap_denominator_nonzero
#print axioms geometryRow009_meanGap_parse
#print axioms geometryRow009_meanGap_read
#print axioms geometryRow009_jensenBound_field
#print axioms geometryRow009_jensenBound_numerator_no_slash
#print axioms geometryRow009_jensenBound_numerator_parse
#print axioms geometryRow009_jensenBound_denominator_parse
#print axioms geometryRow009_jensenBound_denominator_nonzero
#print axioms geometryRow009_jensenBound_parse
#print axioms geometryRow009_jensenBound_read
#print axioms geometryRow009_factorMaxima_read
#print axioms geometryRow009_gapWeightedMeans_read
#print axioms geometryRow009_floor_text_read
#print axioms geometryRow009_floor_chars_parse
#print axioms geometryRow009_floor_parse
#print axioms decode_geometry_Rows_009
#print axioms geometry_Rows_block_004_push_eq
#print axioms geometry_Rows_block_004_reverse
#print axioms decode_geometry_Rows_block_004
#print axioms decode_geometry_Rows_through_block_004

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
