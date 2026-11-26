import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows060

/-! Original simplices typed block 61, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson120 : SourceJson :=
  (SimplicesBlock061.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped120 : GeometryRow :=
  { simplexId := 120,
    vertexIds := #[39, 38, 34, 29, 28, 25, 13, 5, 3],
    physicalVolume := ((1157519558590766845527246629956295699057585321 : ℚ) / (2817974538718307942400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10708303 : ℚ) / (9792000000 : ℚ)),
    factorMaxima := #[((12703177 : ℚ) / (136000000 : ℚ)), ((13390549 : ℚ) / (136000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((8952953 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((3134817610405990007 : ℚ) / (37464068875800000000 : ℚ)), ((25521122987604850321 : ℚ) / (299712551006400000000 : ℚ)), ((3172336803601859671 : ℚ) / (21408039357600000000 : ℚ)), ((36128140212080987473 : ℚ) / (299712551006400000000 : ℚ)), ((175890857837748863 : ℚ) / (2518592865600000000 : ℚ)), ((3266271403034074639 : ℚ) / (74928137751600000000 : ℚ)), ((6074521754361023567 : ℚ) / (171264314860800000000 : ℚ)), ((5719183713489967597 : ℚ) / (171264314860800000000 : ℚ)), ((9170358652997655011 : ℚ) / (299712551006400000000 : ℚ)), ((9170338672160921251 : ℚ) / (299712551006400000000 : ℚ))],
    jensenBound := ((46272355762034441831262665310850445686505775584013045174144519019101780350589982467622956200536047968808610312720392236538013193013677571492793288000000000000000000000000 : ℚ) / (11064280936639636227780687723642305055266829753579684190901046982295176192216966358557611321375173691321912884259826552145988509991038521136899745079402429950944376113777590000355564853 : ℚ)),
    jensenFloorQ96 := (331343152187326 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_simplexId_before"
  err.flush

theorem geometryRow120_simplexId_read :
    geometryRowsJson120.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped120.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_vertexIds_before"
  err.flush

theorem geometryRow120_vertexIds_read :
    geometryRowsJson120.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped120.vertexIds := by decide +kernel

noncomputable def geometryRow120_physicalVolumeNumeratorChars : List Char := ['1', '1', '5', '7', '5', '1', '9', '5', '5', '8', '5', '9', '0', '7', '6', '6', '8', '4', '5', '5', '2', '7', '2', '4', '6', '6', '2', '9', '9', '5', '6', '2', '9', '5', '6', '9', '9', '0', '5', '7', '5', '8', '5', '3', '2', '1']
noncomputable def geometryRow120_physicalVolumeDenominatorChars : List Char := ['2', '8', '1', '7', '9', '7', '4', '5', '3', '8', '7', '1', '8', '3', '0', '7', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow120_physicalVolumeText : String := String.ofList (geometryRow120_physicalVolumeNumeratorChars ++ '/' :: geometryRow120_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_physicalVolume_before_field"
  err.flush

theorem geometryRow120_physicalVolume_field :
    geometryRowsJson120.getObjVal? "physical_volume" = .ok (.str geometryRow120_physicalVolumeText) := by rfl

theorem geometryRow120_physicalVolume_numerator_no_slash :
    geometryRow120_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow120_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow120_physicalVolumeNumeratorChars = some (1157519558590766845527246629956295699057585321 : Int) := by decide +kernel

theorem geometryRow120_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow120_physicalVolumeDenominatorChars = some (2817974538718307942400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow120_physicalVolume_denominator_nonzero : (2817974538718307942400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow120_physicalVolume_parse :
    parseRational geometryRow120_physicalVolumeText = .ok geometryRowsTyped120.physicalVolume :=
  original_rational_fraction_of_chars geometryRow120_physicalVolumeNumeratorChars geometryRow120_physicalVolumeDenominatorChars
    (1157519558590766845527246629956295699057585321 : Int) (2817974538718307942400000000000000000000000000000000000000000000000000 : Int)
    geometryRow120_physicalVolume_numerator_no_slash geometryRow120_physicalVolume_numerator_parse
    geometryRow120_physicalVolume_denominator_parse geometryRow120_physicalVolume_denominator_nonzero

theorem geometryRow120_physicalVolume_read :
    rationalField geometryRowsJson120 "physical_volume" = .ok geometryRowsTyped120.physicalVolume :=
  original_rationalField_of_string geometryRowsJson120 "physical_volume" geometryRow120_physicalVolumeText
    geometryRowsTyped120.physicalVolume geometryRow120_physicalVolume_field geometryRow120_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_physicalVolume_complete"
  err.flush

noncomputable def geometryRow120_meanGapNumeratorChars : List Char := ['1', '0', '7', '0', '8', '3', '0', '3']
noncomputable def geometryRow120_meanGapDenominatorChars : List Char := ['9', '7', '9', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow120_meanGapText : String := String.ofList (geometryRow120_meanGapNumeratorChars ++ '/' :: geometryRow120_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_meanGap_before_field"
  err.flush

theorem geometryRow120_meanGap_field :
    geometryRowsJson120.getObjVal? "mean_gap" = .ok (.str geometryRow120_meanGapText) := by rfl

theorem geometryRow120_meanGap_numerator_no_slash :
    geometryRow120_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow120_meanGap_numerator_parse :
    SourceJson.intChars geometryRow120_meanGapNumeratorChars = some (10708303 : Int) := by decide +kernel

theorem geometryRow120_meanGap_denominator_parse :
    SourceJson.intChars geometryRow120_meanGapDenominatorChars = some (9792000000 : Int) := by decide +kernel

theorem geometryRow120_meanGap_denominator_nonzero : (9792000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow120_meanGap_parse :
    parseRational geometryRow120_meanGapText = .ok geometryRowsTyped120.meanGap :=
  original_rational_fraction_of_chars geometryRow120_meanGapNumeratorChars geometryRow120_meanGapDenominatorChars
    (10708303 : Int) (9792000000 : Int)
    geometryRow120_meanGap_numerator_no_slash geometryRow120_meanGap_numerator_parse
    geometryRow120_meanGap_denominator_parse geometryRow120_meanGap_denominator_nonzero

theorem geometryRow120_meanGap_read :
    rationalField geometryRowsJson120 "mean_gap" = .ok geometryRowsTyped120.meanGap :=
  original_rationalField_of_string geometryRowsJson120 "mean_gap" geometryRow120_meanGapText
    geometryRowsTyped120.meanGap geometryRow120_meanGap_field geometryRow120_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_meanGap_complete"
  err.flush

noncomputable def geometryRow120_jensenBoundNumeratorChars : List Char := ['4', '6', '2', '7', '2', '3', '5', '5', '7', '6', '2', '0', '3', '4', '4', '4', '1', '8', '3', '1', '2', '6', '2', '6', '6', '5', '3', '1', '0', '8', '5', '0', '4', '4', '5', '6', '8', '6', '5', '0', '5', '7', '7', '5', '5', '8', '4', '0', '1', '3', '0', '4', '5', '1', '7', '4', '1', '4', '4', '5', '1', '9', '0', '1', '9', '1', '0', '1', '7', '8', '0', '3', '5', '0', '5', '8', '9', '9', '8', '2', '4', '6', '7', '6', '2', '2', '9', '5', '6', '2', '0', '0', '5', '3', '6', '0', '4', '7', '9', '6', '8', '8', '0', '8', '6', '1', '0', '3', '1', '2', '7', '2', '0', '3', '9', '2', '2', '3', '6', '5', '3', '8', '0', '1', '3', '1', '9', '3', '0', '1', '3', '6', '7', '7', '5', '7', '1', '4', '9', '2', '7', '9', '3', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow120_jensenBoundDenominatorChars : List Char := ['1', '1', '0', '6', '4', '2', '8', '0', '9', '3', '6', '6', '3', '9', '6', '3', '6', '2', '2', '7', '7', '8', '0', '6', '8', '7', '7', '2', '3', '6', '4', '2', '3', '0', '5', '0', '5', '5', '2', '6', '6', '8', '2', '9', '7', '5', '3', '5', '7', '9', '6', '8', '4', '1', '9', '0', '9', '0', '1', '0', '4', '6', '9', '8', '2', '2', '9', '5', '1', '7', '6', '1', '9', '2', '2', '1', '6', '9', '6', '6', '3', '5', '8', '5', '5', '7', '6', '1', '1', '3', '2', '1', '3', '7', '5', '1', '7', '3', '6', '9', '1', '3', '2', '1', '9', '1', '2', '8', '8', '4', '2', '5', '9', '8', '2', '6', '5', '5', '2', '1', '4', '5', '9', '8', '8', '5', '0', '9', '9', '9', '1', '0', '3', '8', '5', '2', '1', '1', '3', '6', '8', '9', '9', '7', '4', '5', '0', '7', '9', '4', '0', '2', '4', '2', '9', '9', '5', '0', '9', '4', '4', '3', '7', '6', '1', '1', '3', '7', '7', '7', '5', '9', '0', '0', '0', '0', '3', '5', '5', '5', '6', '4', '8', '5', '3']
noncomputable def geometryRow120_jensenBoundText : String := String.ofList (geometryRow120_jensenBoundNumeratorChars ++ '/' :: geometryRow120_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_jensenBound_before_field"
  err.flush

theorem geometryRow120_jensenBound_field :
    geometryRowsJson120.getObjVal? "jensen_bound" = .ok (.str geometryRow120_jensenBoundText) := by rfl

theorem geometryRow120_jensenBound_numerator_no_slash :
    geometryRow120_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow120_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow120_jensenBoundNumeratorChars = some (46272355762034441831262665310850445686505775584013045174144519019101780350589982467622956200536047968808610312720392236538013193013677571492793288000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow120_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow120_jensenBoundDenominatorChars = some (11064280936639636227780687723642305055266829753579684190901046982295176192216966358557611321375173691321912884259826552145988509991038521136899745079402429950944376113777590000355564853 : Int) := by decide +kernel

theorem geometryRow120_jensenBound_denominator_nonzero : (11064280936639636227780687723642305055266829753579684190901046982295176192216966358557611321375173691321912884259826552145988509991038521136899745079402429950944376113777590000355564853 : Int) ≠ 0 := by decide +kernel

theorem geometryRow120_jensenBound_parse :
    parseRational geometryRow120_jensenBoundText = .ok geometryRowsTyped120.jensenBound :=
  original_rational_fraction_of_chars geometryRow120_jensenBoundNumeratorChars geometryRow120_jensenBoundDenominatorChars
    (46272355762034441831262665310850445686505775584013045174144519019101780350589982467622956200536047968808610312720392236538013193013677571492793288000000000000000000000000 : Int) (11064280936639636227780687723642305055266829753579684190901046982295176192216966358557611321375173691321912884259826552145988509991038521136899745079402429950944376113777590000355564853 : Int)
    geometryRow120_jensenBound_numerator_no_slash geometryRow120_jensenBound_numerator_parse
    geometryRow120_jensenBound_denominator_parse geometryRow120_jensenBound_denominator_nonzero

theorem geometryRow120_jensenBound_read :
    rationalField geometryRowsJson120 "jensen_bound" = .ok geometryRowsTyped120.jensenBound :=
  original_rationalField_of_string geometryRowsJson120 "jensen_bound" geometryRow120_jensenBoundText
    geometryRowsTyped120.jensenBound geometryRow120_jensenBound_field geometryRow120_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_factorMaxima_before"
  err.flush

theorem geometryRow120_factorMaxima_read :
    rationalArrayField geometryRowsJson120 "factor_maxima" = .ok geometryRowsTyped120.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_gapWeightedMeans_before"
  err.flush

theorem geometryRow120_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson120 "gap_weighted_means" = .ok geometryRowsTyped120.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow120_floorChars : List Char := ['3', '3', '1', '3', '4', '3', '1', '5', '2', '1', '8', '7', '3', '2', '6']
noncomputable def geometryRow120_floorText : String := String.ofList geometryRow120_floorChars

theorem geometryRow120_floor_text_read :
    geometryRowsJson120.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow120_floorText := by rfl

theorem geometryRow120_floor_chars_parse :
    SourceJson.intChars geometryRow120_floorChars = some (331343152187326 : Int) := by decide +kernel

theorem geometryRow120_floor_parse :
    parseInteger geometryRow120_floorText = .ok geometryRowsTyped120.jensenFloorQ96 := by
  simp only [geometryRow120_floorText, parseInteger, String.toList_ofList, geometryRow120_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_120 :
    decodeGeometryRow geometryRowsJson120 = .ok geometryRowsTyped120 :=
  original_geometryRow_of_fields geometryRowsJson120 geometryRowsTyped120 geometryRow120_floorText
    geometryRow120_simplexId_read geometryRow120_vertexIds_read
    geometryRow120_physicalVolume_read geometryRow120_meanGap_read
    geometryRow120_factorMaxima_read geometryRow120_gapWeightedMeans_read
    geometryRow120_jensenBound_read geometryRow120_floor_text_read geometryRow120_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_120_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson121 : SourceJson :=
  (SimplicesBlock061.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped121 : GeometryRow :=
  { simplexId := 121,
    vertexIds := #[39, 38, 34, 29, 28, 25, 8, 3, 1],
    physicalVolume := ((2705953237439872711862246953887199681 : ℚ) / (2079200378880000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((31266792564451 : ℚ) / (363854400000000 : ℚ)), ((31634591574211 : ℚ) / (363854400000000 : ℚ)), ((294193485707 : ℚ) / (1999200000000 : ℚ)), ((42929425447033 : ℚ) / (363854400000000 : ℚ)), ((203247329933 : ℚ) / (3057600000000 : ℚ)), ((8166999050983 : ℚ) / (181927200000000 : ℚ)), ((2539105952839 : ℚ) / (69305600000000 : ℚ)), ((7185933489647 : ℚ) / (207916800000000 : ℚ)), ((11350138936921 : ℚ) / (363854400000000 : ℚ)), ((3783371559987 : ℚ) / (121284800000000 : ℚ))],
    jensenBound := ((33195747821023761069555407844620772227361438916785064297881317239153783011875667999457280000000000000000000000000 : ℚ) / (5415567597126457117897454462633274685165194976859712874413430231619894192584767504457673584608985270265250017178693269259920153 : ℚ)),
    jensenFloorQ96 := (485644035639426 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_simplexId_before"
  err.flush

theorem geometryRow121_simplexId_read :
    geometryRowsJson121.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped121.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_vertexIds_before"
  err.flush

theorem geometryRow121_vertexIds_read :
    geometryRowsJson121.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped121.vertexIds := by decide +kernel

noncomputable def geometryRow121_physicalVolumeNumeratorChars : List Char := ['2', '7', '0', '5', '9', '5', '3', '2', '3', '7', '4', '3', '9', '8', '7', '2', '7', '1', '1', '8', '6', '2', '2', '4', '6', '9', '5', '3', '8', '8', '7', '1', '9', '9', '6', '8', '1']
noncomputable def geometryRow121_physicalVolumeDenominatorChars : List Char := ['2', '0', '7', '9', '2', '0', '0', '3', '7', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow121_physicalVolumeText : String := String.ofList (geometryRow121_physicalVolumeNumeratorChars ++ '/' :: geometryRow121_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_physicalVolume_before_field"
  err.flush

theorem geometryRow121_physicalVolume_field :
    geometryRowsJson121.getObjVal? "physical_volume" = .ok (.str geometryRow121_physicalVolumeText) := by rfl

theorem geometryRow121_physicalVolume_numerator_no_slash :
    geometryRow121_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow121_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow121_physicalVolumeNumeratorChars = some (2705953237439872711862246953887199681 : Int) := by decide +kernel

theorem geometryRow121_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow121_physicalVolumeDenominatorChars = some (2079200378880000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow121_physicalVolume_denominator_nonzero : (2079200378880000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow121_physicalVolume_parse :
    parseRational geometryRow121_physicalVolumeText = .ok geometryRowsTyped121.physicalVolume :=
  original_rational_fraction_of_chars geometryRow121_physicalVolumeNumeratorChars geometryRow121_physicalVolumeDenominatorChars
    (2705953237439872711862246953887199681 : Int) (2079200378880000000000000000000000000000000000000000000000000 : Int)
    geometryRow121_physicalVolume_numerator_no_slash geometryRow121_physicalVolume_numerator_parse
    geometryRow121_physicalVolume_denominator_parse geometryRow121_physicalVolume_denominator_nonzero

theorem geometryRow121_physicalVolume_read :
    rationalField geometryRowsJson121 "physical_volume" = .ok geometryRowsTyped121.physicalVolume :=
  original_rationalField_of_string geometryRowsJson121 "physical_volume" geometryRow121_physicalVolumeText
    geometryRowsTyped121.physicalVolume geometryRow121_physicalVolume_field geometryRow121_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_physicalVolume_complete"
  err.flush

noncomputable def geometryRow121_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow121_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow121_meanGapText : String := String.ofList (geometryRow121_meanGapNumeratorChars ++ '/' :: geometryRow121_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_meanGap_before_field"
  err.flush

theorem geometryRow121_meanGap_field :
    geometryRowsJson121.getObjVal? "mean_gap" = .ok (.str geometryRow121_meanGapText) := by rfl

theorem geometryRow121_meanGap_numerator_no_slash :
    geometryRow121_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow121_meanGap_numerator_parse :
    SourceJson.intChars geometryRow121_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow121_meanGap_denominator_parse :
    SourceJson.intChars geometryRow121_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow121_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow121_meanGap_parse :
    parseRational geometryRow121_meanGapText = .ok geometryRowsTyped121.meanGap :=
  original_rational_fraction_of_chars geometryRow121_meanGapNumeratorChars geometryRow121_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow121_meanGap_numerator_no_slash geometryRow121_meanGap_numerator_parse
    geometryRow121_meanGap_denominator_parse geometryRow121_meanGap_denominator_nonzero

theorem geometryRow121_meanGap_read :
    rationalField geometryRowsJson121 "mean_gap" = .ok geometryRowsTyped121.meanGap :=
  original_rationalField_of_string geometryRowsJson121 "mean_gap" geometryRow121_meanGapText
    geometryRowsTyped121.meanGap geometryRow121_meanGap_field geometryRow121_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_meanGap_complete"
  err.flush

noncomputable def geometryRow121_jensenBoundNumeratorChars : List Char := ['3', '3', '1', '9', '5', '7', '4', '7', '8', '2', '1', '0', '2', '3', '7', '6', '1', '0', '6', '9', '5', '5', '5', '4', '0', '7', '8', '4', '4', '6', '2', '0', '7', '7', '2', '2', '2', '7', '3', '6', '1', '4', '3', '8', '9', '1', '6', '7', '8', '5', '0', '6', '4', '2', '9', '7', '8', '8', '1', '3', '1', '7', '2', '3', '9', '1', '5', '3', '7', '8', '3', '0', '1', '1', '8', '7', '5', '6', '6', '7', '9', '9', '9', '4', '5', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow121_jensenBoundDenominatorChars : List Char := ['5', '4', '1', '5', '5', '6', '7', '5', '9', '7', '1', '2', '6', '4', '5', '7', '1', '1', '7', '8', '9', '7', '4', '5', '4', '4', '6', '2', '6', '3', '3', '2', '7', '4', '6', '8', '5', '1', '6', '5', '1', '9', '4', '9', '7', '6', '8', '5', '9', '7', '1', '2', '8', '7', '4', '4', '1', '3', '4', '3', '0', '2', '3', '1', '6', '1', '9', '8', '9', '4', '1', '9', '2', '5', '8', '4', '7', '6', '7', '5', '0', '4', '4', '5', '7', '6', '7', '3', '5', '8', '4', '6', '0', '8', '9', '8', '5', '2', '7', '0', '2', '6', '5', '2', '5', '0', '0', '1', '7', '1', '7', '8', '6', '9', '3', '2', '6', '9', '2', '5', '9', '9', '2', '0', '1', '5', '3']
noncomputable def geometryRow121_jensenBoundText : String := String.ofList (geometryRow121_jensenBoundNumeratorChars ++ '/' :: geometryRow121_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_jensenBound_before_field"
  err.flush

theorem geometryRow121_jensenBound_field :
    geometryRowsJson121.getObjVal? "jensen_bound" = .ok (.str geometryRow121_jensenBoundText) := by rfl

theorem geometryRow121_jensenBound_numerator_no_slash :
    geometryRow121_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow121_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow121_jensenBoundNumeratorChars = some (33195747821023761069555407844620772227361438916785064297881317239153783011875667999457280000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow121_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow121_jensenBoundDenominatorChars = some (5415567597126457117897454462633274685165194976859712874413430231619894192584767504457673584608985270265250017178693269259920153 : Int) := by decide +kernel

theorem geometryRow121_jensenBound_denominator_nonzero : (5415567597126457117897454462633274685165194976859712874413430231619894192584767504457673584608985270265250017178693269259920153 : Int) ≠ 0 := by decide +kernel

theorem geometryRow121_jensenBound_parse :
    parseRational geometryRow121_jensenBoundText = .ok geometryRowsTyped121.jensenBound :=
  original_rational_fraction_of_chars geometryRow121_jensenBoundNumeratorChars geometryRow121_jensenBoundDenominatorChars
    (33195747821023761069555407844620772227361438916785064297881317239153783011875667999457280000000000000000000000000 : Int) (5415567597126457117897454462633274685165194976859712874413430231619894192584767504457673584608985270265250017178693269259920153 : Int)
    geometryRow121_jensenBound_numerator_no_slash geometryRow121_jensenBound_numerator_parse
    geometryRow121_jensenBound_denominator_parse geometryRow121_jensenBound_denominator_nonzero

theorem geometryRow121_jensenBound_read :
    rationalField geometryRowsJson121 "jensen_bound" = .ok geometryRowsTyped121.jensenBound :=
  original_rationalField_of_string geometryRowsJson121 "jensen_bound" geometryRow121_jensenBoundText
    geometryRowsTyped121.jensenBound geometryRow121_jensenBound_field geometryRow121_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_factorMaxima_before"
  err.flush

theorem geometryRow121_factorMaxima_read :
    rationalArrayField geometryRowsJson121 "factor_maxima" = .ok geometryRowsTyped121.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_gapWeightedMeans_before"
  err.flush

theorem geometryRow121_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson121 "gap_weighted_means" = .ok geometryRowsTyped121.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow121_floorChars : List Char := ['4', '8', '5', '6', '4', '4', '0', '3', '5', '6', '3', '9', '4', '2', '6']
noncomputable def geometryRow121_floorText : String := String.ofList geometryRow121_floorChars

theorem geometryRow121_floor_text_read :
    geometryRowsJson121.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow121_floorText := by rfl

theorem geometryRow121_floor_chars_parse :
    SourceJson.intChars geometryRow121_floorChars = some (485644035639426 : Int) := by decide +kernel

theorem geometryRow121_floor_parse :
    parseInteger geometryRow121_floorText = .ok geometryRowsTyped121.jensenFloorQ96 := by
  simp only [geometryRow121_floorText, parseInteger, String.toList_ofList, geometryRow121_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_121 :
    decodeGeometryRow geometryRowsJson121 = .ok geometryRowsTyped121 :=
  original_geometryRow_of_fields geometryRowsJson121 geometryRowsTyped121 geometryRow121_floorText
    geometryRow121_simplexId_read geometryRow121_vertexIds_read
    geometryRow121_physicalVolume_read geometryRow121_meanGap_read
    geometryRow121_factorMaxima_read geometryRow121_gapWeightedMeans_read
    geometryRow121_jensenBound_read geometryRow121_floor_text_read geometryRow121_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_121_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock061 : List SourceJson := [geometryRowsJson120, geometryRowsJson121]
noncomputable def geometryRowsTypedBlock061 : List (GeometryRow) := [geometryRowsTyped120, geometryRowsTyped121]
noncomputable def geometryRowsTypedThroughBlock061 : List (GeometryRow) := geometryRowsTypedThroughBlock060 ++ geometryRowsTypedBlock061

theorem geometry_Rows_block_061_push_eq (acc : List SourceJson) :
    SimplicesBlock061.blockPush acc = [geometryRowsJson121, geometryRowsJson120] ++ acc := by rfl

theorem geometry_Rows_block_061_reverse (acc : List SourceJson) :
    (SimplicesBlock061.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock061 := by
  rw [geometry_Rows_block_061_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_061 :
    geometryRowsJsonBlock061.mapM decodeGeometryRow = .ok geometryRowsTypedBlock061 := by
  simp only [geometryRowsJsonBlock061, geometryRowsTypedBlock061, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_120, decode_geometry_Rows_121]
  rfl

theorem decode_geometry_Rows_through_block_061 :
    SimplicesValue.arrayAcc062.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock061 := by
  change (SimplicesBlock061.blockPush SimplicesValue.arrayAcc061).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_061_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_060, decode_geometry_Rows_block_061]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_061_complete"
  err.flush

#print axioms geometryRow120_simplexId_read
#print axioms geometryRow120_vertexIds_read
#print axioms geometryRow120_physicalVolume_field
#print axioms geometryRow120_physicalVolume_numerator_no_slash
#print axioms geometryRow120_physicalVolume_numerator_parse
#print axioms geometryRow120_physicalVolume_denominator_parse
#print axioms geometryRow120_physicalVolume_denominator_nonzero
#print axioms geometryRow120_physicalVolume_parse
#print axioms geometryRow120_physicalVolume_read
#print axioms geometryRow120_meanGap_field
#print axioms geometryRow120_meanGap_numerator_no_slash
#print axioms geometryRow120_meanGap_numerator_parse
#print axioms geometryRow120_meanGap_denominator_parse
#print axioms geometryRow120_meanGap_denominator_nonzero
#print axioms geometryRow120_meanGap_parse
#print axioms geometryRow120_meanGap_read
#print axioms geometryRow120_jensenBound_field
#print axioms geometryRow120_jensenBound_numerator_no_slash
#print axioms geometryRow120_jensenBound_numerator_parse
#print axioms geometryRow120_jensenBound_denominator_parse
#print axioms geometryRow120_jensenBound_denominator_nonzero
#print axioms geometryRow120_jensenBound_parse
#print axioms geometryRow120_jensenBound_read
#print axioms geometryRow120_factorMaxima_read
#print axioms geometryRow120_gapWeightedMeans_read
#print axioms geometryRow120_floor_text_read
#print axioms geometryRow120_floor_chars_parse
#print axioms geometryRow120_floor_parse
#print axioms decode_geometry_Rows_120
#print axioms geometryRow121_simplexId_read
#print axioms geometryRow121_vertexIds_read
#print axioms geometryRow121_physicalVolume_field
#print axioms geometryRow121_physicalVolume_numerator_no_slash
#print axioms geometryRow121_physicalVolume_numerator_parse
#print axioms geometryRow121_physicalVolume_denominator_parse
#print axioms geometryRow121_physicalVolume_denominator_nonzero
#print axioms geometryRow121_physicalVolume_parse
#print axioms geometryRow121_physicalVolume_read
#print axioms geometryRow121_meanGap_field
#print axioms geometryRow121_meanGap_numerator_no_slash
#print axioms geometryRow121_meanGap_numerator_parse
#print axioms geometryRow121_meanGap_denominator_parse
#print axioms geometryRow121_meanGap_denominator_nonzero
#print axioms geometryRow121_meanGap_parse
#print axioms geometryRow121_meanGap_read
#print axioms geometryRow121_jensenBound_field
#print axioms geometryRow121_jensenBound_numerator_no_slash
#print axioms geometryRow121_jensenBound_numerator_parse
#print axioms geometryRow121_jensenBound_denominator_parse
#print axioms geometryRow121_jensenBound_denominator_nonzero
#print axioms geometryRow121_jensenBound_parse
#print axioms geometryRow121_jensenBound_read
#print axioms geometryRow121_factorMaxima_read
#print axioms geometryRow121_gapWeightedMeans_read
#print axioms geometryRow121_floor_text_read
#print axioms geometryRow121_floor_chars_parse
#print axioms geometryRow121_floor_parse
#print axioms decode_geometry_Rows_121
#print axioms geometry_Rows_block_061_push_eq
#print axioms geometry_Rows_block_061_reverse
#print axioms decode_geometry_Rows_block_061
#print axioms decode_geometry_Rows_through_block_061

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
