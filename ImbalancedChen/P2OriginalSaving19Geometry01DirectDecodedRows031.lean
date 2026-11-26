import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows030

/-! Original simplices typed block 31, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson061 : SourceJson :=
  (SimplicesBlock031.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped061 : GeometryRow :=
  { simplexId := 61,
    vertexIds := #[39, 35, 34, 29, 28, 25, 13, 5, 3],
    physicalVolume := ((128614575714586859316851753068181065328739289 : ℚ) / (313108282079811993600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10708303 : ℚ) / (9792000000 : ℚ)),
    factorMaxima := #[((12703177 : ℚ) / (136000000 : ℚ)), ((13390549 : ℚ) / (136000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((4640469 : ℚ) / (56000000 : ℚ)), ((8952953 : ℚ) / (168000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2992679896452975899 : ℚ) / (37464068875800000000 : ℚ)), ((24384021275980737457 : ℚ) / (299712551006400000000 : ℚ)), ((1050677257564980729 : ℚ) / (7136013119200000000 : ℚ)), ((11853199782229099307 : ℚ) / (99904183668800000000 : ℚ)), ((180668512168788271 : ℚ) / (2518592865600000000 : ℚ)), ((1112446337069428611 : ℚ) / (24976045917200000000 : ℚ)), ((6236962001616363439 : ℚ) / (171264314860800000000 : ℚ)), ((1960541320248435823 : ℚ) / (57088104953600000000 : ℚ)), ((9454649066531233547 : ℚ) / (299712551006400000000 : ℚ)), ((3151536368285922009 : ℚ) / (99904183668800000000 : ℚ))],
    jensenBound := ((550132420194827652413092889568664503929800769918204401807529280434288286067347414427976494408877997019033728257325925507533229269456560224694590744000000000000000000000000 : ℚ) / (138219499528420291917934837814309535362234852459619307411798925703621140855882365938428022985818281236436789852805415395598523794030418431191286271788566705413239172841392306863362112401 : ℚ)),
    jensenFloorQ96 := (315338869987728 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_simplexId_before"
  err.flush

theorem geometryRow061_simplexId_read :
    geometryRowsJson061.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped061.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_vertexIds_before"
  err.flush

theorem geometryRow061_vertexIds_read :
    geometryRowsJson061.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped061.vertexIds := by decide +kernel

noncomputable def geometryRow061_physicalVolumeNumeratorChars : List Char := ['1', '2', '8', '6', '1', '4', '5', '7', '5', '7', '1', '4', '5', '8', '6', '8', '5', '9', '3', '1', '6', '8', '5', '1', '7', '5', '3', '0', '6', '8', '1', '8', '1', '0', '6', '5', '3', '2', '8', '7', '3', '9', '2', '8', '9']
noncomputable def geometryRow061_physicalVolumeDenominatorChars : List Char := ['3', '1', '3', '1', '0', '8', '2', '8', '2', '0', '7', '9', '8', '1', '1', '9', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow061_physicalVolumeText : String := String.ofList (geometryRow061_physicalVolumeNumeratorChars ++ '/' :: geometryRow061_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_physicalVolume_before_field"
  err.flush

theorem geometryRow061_physicalVolume_field :
    geometryRowsJson061.getObjVal? "physical_volume" = .ok (.str geometryRow061_physicalVolumeText) := by rfl

theorem geometryRow061_physicalVolume_numerator_no_slash :
    geometryRow061_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow061_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow061_physicalVolumeNumeratorChars = some (128614575714586859316851753068181065328739289 : Int) := by decide +kernel

theorem geometryRow061_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow061_physicalVolumeDenominatorChars = some (313108282079811993600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow061_physicalVolume_denominator_nonzero : (313108282079811993600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow061_physicalVolume_parse :
    parseRational geometryRow061_physicalVolumeText = .ok geometryRowsTyped061.physicalVolume :=
  original_rational_fraction_of_chars geometryRow061_physicalVolumeNumeratorChars geometryRow061_physicalVolumeDenominatorChars
    (128614575714586859316851753068181065328739289 : Int) (313108282079811993600000000000000000000000000000000000000000000000000 : Int)
    geometryRow061_physicalVolume_numerator_no_slash geometryRow061_physicalVolume_numerator_parse
    geometryRow061_physicalVolume_denominator_parse geometryRow061_physicalVolume_denominator_nonzero

theorem geometryRow061_physicalVolume_read :
    rationalField geometryRowsJson061 "physical_volume" = .ok geometryRowsTyped061.physicalVolume :=
  original_rationalField_of_string geometryRowsJson061 "physical_volume" geometryRow061_physicalVolumeText
    geometryRowsTyped061.physicalVolume geometryRow061_physicalVolume_field geometryRow061_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_physicalVolume_complete"
  err.flush

noncomputable def geometryRow061_meanGapNumeratorChars : List Char := ['1', '0', '7', '0', '8', '3', '0', '3']
noncomputable def geometryRow061_meanGapDenominatorChars : List Char := ['9', '7', '9', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow061_meanGapText : String := String.ofList (geometryRow061_meanGapNumeratorChars ++ '/' :: geometryRow061_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_meanGap_before_field"
  err.flush

theorem geometryRow061_meanGap_field :
    geometryRowsJson061.getObjVal? "mean_gap" = .ok (.str geometryRow061_meanGapText) := by rfl

theorem geometryRow061_meanGap_numerator_no_slash :
    geometryRow061_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow061_meanGap_numerator_parse :
    SourceJson.intChars geometryRow061_meanGapNumeratorChars = some (10708303 : Int) := by decide +kernel

theorem geometryRow061_meanGap_denominator_parse :
    SourceJson.intChars geometryRow061_meanGapDenominatorChars = some (9792000000 : Int) := by decide +kernel

theorem geometryRow061_meanGap_denominator_nonzero : (9792000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow061_meanGap_parse :
    parseRational geometryRow061_meanGapText = .ok geometryRowsTyped061.meanGap :=
  original_rational_fraction_of_chars geometryRow061_meanGapNumeratorChars geometryRow061_meanGapDenominatorChars
    (10708303 : Int) (9792000000 : Int)
    geometryRow061_meanGap_numerator_no_slash geometryRow061_meanGap_numerator_parse
    geometryRow061_meanGap_denominator_parse geometryRow061_meanGap_denominator_nonzero

theorem geometryRow061_meanGap_read :
    rationalField geometryRowsJson061 "mean_gap" = .ok geometryRowsTyped061.meanGap :=
  original_rationalField_of_string geometryRowsJson061 "mean_gap" geometryRow061_meanGapText
    geometryRowsTyped061.meanGap geometryRow061_meanGap_field geometryRow061_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_meanGap_complete"
  err.flush

noncomputable def geometryRow061_jensenBoundNumeratorChars : List Char := ['5', '5', '0', '1', '3', '2', '4', '2', '0', '1', '9', '4', '8', '2', '7', '6', '5', '2', '4', '1', '3', '0', '9', '2', '8', '8', '9', '5', '6', '8', '6', '6', '4', '5', '0', '3', '9', '2', '9', '8', '0', '0', '7', '6', '9', '9', '1', '8', '2', '0', '4', '4', '0', '1', '8', '0', '7', '5', '2', '9', '2', '8', '0', '4', '3', '4', '2', '8', '8', '2', '8', '6', '0', '6', '7', '3', '4', '7', '4', '1', '4', '4', '2', '7', '9', '7', '6', '4', '9', '4', '4', '0', '8', '8', '7', '7', '9', '9', '7', '0', '1', '9', '0', '3', '3', '7', '2', '8', '2', '5', '7', '3', '2', '5', '9', '2', '5', '5', '0', '7', '5', '3', '3', '2', '2', '9', '2', '6', '9', '4', '5', '6', '5', '6', '0', '2', '2', '4', '6', '9', '4', '5', '9', '0', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow061_jensenBoundDenominatorChars : List Char := ['1', '3', '8', '2', '1', '9', '4', '9', '9', '5', '2', '8', '4', '2', '0', '2', '9', '1', '9', '1', '7', '9', '3', '4', '8', '3', '7', '8', '1', '4', '3', '0', '9', '5', '3', '5', '3', '6', '2', '2', '3', '4', '8', '5', '2', '4', '5', '9', '6', '1', '9', '3', '0', '7', '4', '1', '1', '7', '9', '8', '9', '2', '5', '7', '0', '3', '6', '2', '1', '1', '4', '0', '8', '5', '5', '8', '8', '2', '3', '6', '5', '9', '3', '8', '4', '2', '8', '0', '2', '2', '9', '8', '5', '8', '1', '8', '2', '8', '1', '2', '3', '6', '4', '3', '6', '7', '8', '9', '8', '5', '2', '8', '0', '5', '4', '1', '5', '3', '9', '5', '5', '9', '8', '5', '2', '3', '7', '9', '4', '0', '3', '0', '4', '1', '8', '4', '3', '1', '1', '9', '1', '2', '8', '6', '2', '7', '1', '7', '8', '8', '5', '6', '6', '7', '0', '5', '4', '1', '3', '2', '3', '9', '1', '7', '2', '8', '4', '1', '3', '9', '2', '3', '0', '6', '8', '6', '3', '3', '6', '2', '1', '1', '2', '4', '0', '1']
noncomputable def geometryRow061_jensenBoundText : String := String.ofList (geometryRow061_jensenBoundNumeratorChars ++ '/' :: geometryRow061_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_jensenBound_before_field"
  err.flush

theorem geometryRow061_jensenBound_field :
    geometryRowsJson061.getObjVal? "jensen_bound" = .ok (.str geometryRow061_jensenBoundText) := by rfl

theorem geometryRow061_jensenBound_numerator_no_slash :
    geometryRow061_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow061_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow061_jensenBoundNumeratorChars = some (550132420194827652413092889568664503929800769918204401807529280434288286067347414427976494408877997019033728257325925507533229269456560224694590744000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow061_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow061_jensenBoundDenominatorChars = some (138219499528420291917934837814309535362234852459619307411798925703621140855882365938428022985818281236436789852805415395598523794030418431191286271788566705413239172841392306863362112401 : Int) := by decide +kernel

theorem geometryRow061_jensenBound_denominator_nonzero : (138219499528420291917934837814309535362234852459619307411798925703621140855882365938428022985818281236436789852805415395598523794030418431191286271788566705413239172841392306863362112401 : Int) ≠ 0 := by decide +kernel

theorem geometryRow061_jensenBound_parse :
    parseRational geometryRow061_jensenBoundText = .ok geometryRowsTyped061.jensenBound :=
  original_rational_fraction_of_chars geometryRow061_jensenBoundNumeratorChars geometryRow061_jensenBoundDenominatorChars
    (550132420194827652413092889568664503929800769918204401807529280434288286067347414427976494408877997019033728257325925507533229269456560224694590744000000000000000000000000 : Int) (138219499528420291917934837814309535362234852459619307411798925703621140855882365938428022985818281236436789852805415395598523794030418431191286271788566705413239172841392306863362112401 : Int)
    geometryRow061_jensenBound_numerator_no_slash geometryRow061_jensenBound_numerator_parse
    geometryRow061_jensenBound_denominator_parse geometryRow061_jensenBound_denominator_nonzero

theorem geometryRow061_jensenBound_read :
    rationalField geometryRowsJson061 "jensen_bound" = .ok geometryRowsTyped061.jensenBound :=
  original_rationalField_of_string geometryRowsJson061 "jensen_bound" geometryRow061_jensenBoundText
    geometryRowsTyped061.jensenBound geometryRow061_jensenBound_field geometryRow061_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_factorMaxima_before"
  err.flush

theorem geometryRow061_factorMaxima_read :
    rationalArrayField geometryRowsJson061 "factor_maxima" = .ok geometryRowsTyped061.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_gapWeightedMeans_before"
  err.flush

theorem geometryRow061_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson061 "gap_weighted_means" = .ok geometryRowsTyped061.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow061_floorChars : List Char := ['3', '1', '5', '3', '3', '8', '8', '6', '9', '9', '8', '7', '7', '2', '8']
noncomputable def geometryRow061_floorText : String := String.ofList geometryRow061_floorChars

theorem geometryRow061_floor_text_read :
    geometryRowsJson061.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow061_floorText := by rfl

theorem geometryRow061_floor_chars_parse :
    SourceJson.intChars geometryRow061_floorChars = some (315338869987728 : Int) := by decide +kernel

theorem geometryRow061_floor_parse :
    parseInteger geometryRow061_floorText = .ok geometryRowsTyped061.jensenFloorQ96 := by
  simp only [geometryRow061_floorText, parseInteger, String.toList_ofList, geometryRow061_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_061 :
    decodeGeometryRow geometryRowsJson061 = .ok geometryRowsTyped061 :=
  original_geometryRow_of_fields geometryRowsJson061 geometryRowsTyped061 geometryRow061_floorText
    geometryRow061_simplexId_read geometryRow061_vertexIds_read
    geometryRow061_physicalVolume_read geometryRow061_meanGap_read
    geometryRow061_factorMaxima_read geometryRow061_gapWeightedMeans_read
    geometryRow061_jensenBound_read geometryRow061_floor_text_read geometryRow061_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_061_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson062 : SourceJson :=
  (SimplicesBlock031.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped062 : GeometryRow :=
  { simplexId := 62,
    vertexIds := #[39, 35, 34, 29, 28, 25, 8, 3, 1],
    physicalVolume := ((300664489816956794849650123884892529 : ℚ) / (231022264320000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((84373 : ℚ) / (2080000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((29886338327107 : ℚ) / (363854400000000 : ℚ)), ((30254137336867 : ℚ) / (363854400000000 : ℚ)), ((292297290679 : ℚ) / (1999200000000 : ℚ)), ((14079736818947 : ℚ) / (121284800000000 : ℚ)), ((209047455901 : ℚ) / (3057600000000 : ℚ)), ((8339552798531 : ℚ) / (181927200000000 : ℚ)), ((7814522141429 : ℚ) / (207916800000000 : ℚ)), ((7383137772559 : ℚ) / (207916800000000 : ℚ)), ((11695270688977 : ℚ) / (363854400000000 : ℚ)), ((11695222175057 : ℚ) / (363854400000000 : ℚ))],
    jensenBound := ((298764730303918093134697966175675046545327243075428358461735122263641392620950630689669120000000000000000000000000 : ℚ) / (51194889725810747689817082116529240007097578548759372446666162337962393840716174433775398017271202926605541317637670721853047753 : ℚ)),
    jensenFloorQ96 := (462362175850439 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_simplexId_before"
  err.flush

theorem geometryRow062_simplexId_read :
    geometryRowsJson062.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped062.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_vertexIds_before"
  err.flush

theorem geometryRow062_vertexIds_read :
    geometryRowsJson062.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped062.vertexIds := by decide +kernel

noncomputable def geometryRow062_physicalVolumeNumeratorChars : List Char := ['3', '0', '0', '6', '6', '4', '4', '8', '9', '8', '1', '6', '9', '5', '6', '7', '9', '4', '8', '4', '9', '6', '5', '0', '1', '2', '3', '8', '8', '4', '8', '9', '2', '5', '2', '9']
noncomputable def geometryRow062_physicalVolumeDenominatorChars : List Char := ['2', '3', '1', '0', '2', '2', '2', '6', '4', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow062_physicalVolumeText : String := String.ofList (geometryRow062_physicalVolumeNumeratorChars ++ '/' :: geometryRow062_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_physicalVolume_before_field"
  err.flush

theorem geometryRow062_physicalVolume_field :
    geometryRowsJson062.getObjVal? "physical_volume" = .ok (.str geometryRow062_physicalVolumeText) := by rfl

theorem geometryRow062_physicalVolume_numerator_no_slash :
    geometryRow062_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow062_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow062_physicalVolumeNumeratorChars = some (300664489816956794849650123884892529 : Int) := by decide +kernel

theorem geometryRow062_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow062_physicalVolumeDenominatorChars = some (231022264320000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow062_physicalVolume_denominator_nonzero : (231022264320000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow062_physicalVolume_parse :
    parseRational geometryRow062_physicalVolumeText = .ok geometryRowsTyped062.physicalVolume :=
  original_rational_fraction_of_chars geometryRow062_physicalVolumeNumeratorChars geometryRow062_physicalVolumeDenominatorChars
    (300664489816956794849650123884892529 : Int) (231022264320000000000000000000000000000000000000000000000000 : Int)
    geometryRow062_physicalVolume_numerator_no_slash geometryRow062_physicalVolume_numerator_parse
    geometryRow062_physicalVolume_denominator_parse geometryRow062_physicalVolume_denominator_nonzero

theorem geometryRow062_physicalVolume_read :
    rationalField geometryRowsJson062 "physical_volume" = .ok geometryRowsTyped062.physicalVolume :=
  original_rationalField_of_string geometryRowsJson062 "physical_volume" geometryRow062_physicalVolumeText
    geometryRowsTyped062.physicalVolume geometryRow062_physicalVolume_field geometryRow062_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_physicalVolume_complete"
  err.flush

noncomputable def geometryRow062_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow062_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow062_meanGapText : String := String.ofList (geometryRow062_meanGapNumeratorChars ++ '/' :: geometryRow062_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_meanGap_before_field"
  err.flush

theorem geometryRow062_meanGap_field :
    geometryRowsJson062.getObjVal? "mean_gap" = .ok (.str geometryRow062_meanGapText) := by rfl

theorem geometryRow062_meanGap_numerator_no_slash :
    geometryRow062_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow062_meanGap_numerator_parse :
    SourceJson.intChars geometryRow062_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow062_meanGap_denominator_parse :
    SourceJson.intChars geometryRow062_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow062_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow062_meanGap_parse :
    parseRational geometryRow062_meanGapText = .ok geometryRowsTyped062.meanGap :=
  original_rational_fraction_of_chars geometryRow062_meanGapNumeratorChars geometryRow062_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow062_meanGap_numerator_no_slash geometryRow062_meanGap_numerator_parse
    geometryRow062_meanGap_denominator_parse geometryRow062_meanGap_denominator_nonzero

theorem geometryRow062_meanGap_read :
    rationalField geometryRowsJson062 "mean_gap" = .ok geometryRowsTyped062.meanGap :=
  original_rationalField_of_string geometryRowsJson062 "mean_gap" geometryRow062_meanGapText
    geometryRowsTyped062.meanGap geometryRow062_meanGap_field geometryRow062_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_meanGap_complete"
  err.flush

noncomputable def geometryRow062_jensenBoundNumeratorChars : List Char := ['2', '9', '8', '7', '6', '4', '7', '3', '0', '3', '0', '3', '9', '1', '8', '0', '9', '3', '1', '3', '4', '6', '9', '7', '9', '6', '6', '1', '7', '5', '6', '7', '5', '0', '4', '6', '5', '4', '5', '3', '2', '7', '2', '4', '3', '0', '7', '5', '4', '2', '8', '3', '5', '8', '4', '6', '1', '7', '3', '5', '1', '2', '2', '2', '6', '3', '6', '4', '1', '3', '9', '2', '6', '2', '0', '9', '5', '0', '6', '3', '0', '6', '8', '9', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow062_jensenBoundDenominatorChars : List Char := ['5', '1', '1', '9', '4', '8', '8', '9', '7', '2', '5', '8', '1', '0', '7', '4', '7', '6', '8', '9', '8', '1', '7', '0', '8', '2', '1', '1', '6', '5', '2', '9', '2', '4', '0', '0', '0', '7', '0', '9', '7', '5', '7', '8', '5', '4', '8', '7', '5', '9', '3', '7', '2', '4', '4', '6', '6', '6', '6', '1', '6', '2', '3', '3', '7', '9', '6', '2', '3', '9', '3', '8', '4', '0', '7', '1', '6', '1', '7', '4', '4', '3', '3', '7', '7', '5', '3', '9', '8', '0', '1', '7', '2', '7', '1', '2', '0', '2', '9', '2', '6', '6', '0', '5', '5', '4', '1', '3', '1', '7', '6', '3', '7', '6', '7', '0', '7', '2', '1', '8', '5', '3', '0', '4', '7', '7', '5', '3']
noncomputable def geometryRow062_jensenBoundText : String := String.ofList (geometryRow062_jensenBoundNumeratorChars ++ '/' :: geometryRow062_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_jensenBound_before_field"
  err.flush

theorem geometryRow062_jensenBound_field :
    geometryRowsJson062.getObjVal? "jensen_bound" = .ok (.str geometryRow062_jensenBoundText) := by rfl

theorem geometryRow062_jensenBound_numerator_no_slash :
    geometryRow062_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow062_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow062_jensenBoundNumeratorChars = some (298764730303918093134697966175675046545327243075428358461735122263641392620950630689669120000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow062_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow062_jensenBoundDenominatorChars = some (51194889725810747689817082116529240007097578548759372446666162337962393840716174433775398017271202926605541317637670721853047753 : Int) := by decide +kernel

theorem geometryRow062_jensenBound_denominator_nonzero : (51194889725810747689817082116529240007097578548759372446666162337962393840716174433775398017271202926605541317637670721853047753 : Int) ≠ 0 := by decide +kernel

theorem geometryRow062_jensenBound_parse :
    parseRational geometryRow062_jensenBoundText = .ok geometryRowsTyped062.jensenBound :=
  original_rational_fraction_of_chars geometryRow062_jensenBoundNumeratorChars geometryRow062_jensenBoundDenominatorChars
    (298764730303918093134697966175675046545327243075428358461735122263641392620950630689669120000000000000000000000000 : Int) (51194889725810747689817082116529240007097578548759372446666162337962393840716174433775398017271202926605541317637670721853047753 : Int)
    geometryRow062_jensenBound_numerator_no_slash geometryRow062_jensenBound_numerator_parse
    geometryRow062_jensenBound_denominator_parse geometryRow062_jensenBound_denominator_nonzero

theorem geometryRow062_jensenBound_read :
    rationalField geometryRowsJson062 "jensen_bound" = .ok geometryRowsTyped062.jensenBound :=
  original_rationalField_of_string geometryRowsJson062 "jensen_bound" geometryRow062_jensenBoundText
    geometryRowsTyped062.jensenBound geometryRow062_jensenBound_field geometryRow062_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_factorMaxima_before"
  err.flush

theorem geometryRow062_factorMaxima_read :
    rationalArrayField geometryRowsJson062 "factor_maxima" = .ok geometryRowsTyped062.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_gapWeightedMeans_before"
  err.flush

theorem geometryRow062_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson062 "gap_weighted_means" = .ok geometryRowsTyped062.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow062_floorChars : List Char := ['4', '6', '2', '3', '6', '2', '1', '7', '5', '8', '5', '0', '4', '3', '9']
noncomputable def geometryRow062_floorText : String := String.ofList geometryRow062_floorChars

theorem geometryRow062_floor_text_read :
    geometryRowsJson062.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow062_floorText := by rfl

theorem geometryRow062_floor_chars_parse :
    SourceJson.intChars geometryRow062_floorChars = some (462362175850439 : Int) := by decide +kernel

theorem geometryRow062_floor_parse :
    parseInteger geometryRow062_floorText = .ok geometryRowsTyped062.jensenFloorQ96 := by
  simp only [geometryRow062_floorText, parseInteger, String.toList_ofList, geometryRow062_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_062 :
    decodeGeometryRow geometryRowsJson062 = .ok geometryRowsTyped062 :=
  original_geometryRow_of_fields geometryRowsJson062 geometryRowsTyped062 geometryRow062_floorText
    geometryRow062_simplexId_read geometryRow062_vertexIds_read
    geometryRow062_physicalVolume_read geometryRow062_meanGap_read
    geometryRow062_factorMaxima_read geometryRow062_gapWeightedMeans_read
    geometryRow062_jensenBound_read geometryRow062_floor_text_read geometryRow062_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_062_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock031 : List SourceJson := [geometryRowsJson061, geometryRowsJson062]
noncomputable def geometryRowsTypedBlock031 : List (GeometryRow) := [geometryRowsTyped061, geometryRowsTyped062]
noncomputable def geometryRowsTypedThroughBlock031 : List (GeometryRow) := geometryRowsTypedThroughBlock030 ++ geometryRowsTypedBlock031

theorem geometry_Rows_block_031_push_eq (acc : List SourceJson) :
    SimplicesBlock031.blockPush acc = [geometryRowsJson062, geometryRowsJson061] ++ acc := by rfl

theorem geometry_Rows_block_031_reverse (acc : List SourceJson) :
    (SimplicesBlock031.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock031 := by
  rw [geometry_Rows_block_031_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_031 :
    geometryRowsJsonBlock031.mapM decodeGeometryRow = .ok geometryRowsTypedBlock031 := by
  simp only [geometryRowsJsonBlock031, geometryRowsTypedBlock031, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_061, decode_geometry_Rows_062]
  rfl

theorem decode_geometry_Rows_through_block_031 :
    SimplicesValue.arrayAcc032.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock031 := by
  change (SimplicesBlock031.blockPush SimplicesValue.arrayAcc031).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_031_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_030, decode_geometry_Rows_block_031]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_031_complete"
  err.flush

#print axioms geometryRow061_simplexId_read
#print axioms geometryRow061_vertexIds_read
#print axioms geometryRow061_physicalVolume_field
#print axioms geometryRow061_physicalVolume_numerator_no_slash
#print axioms geometryRow061_physicalVolume_numerator_parse
#print axioms geometryRow061_physicalVolume_denominator_parse
#print axioms geometryRow061_physicalVolume_denominator_nonzero
#print axioms geometryRow061_physicalVolume_parse
#print axioms geometryRow061_physicalVolume_read
#print axioms geometryRow061_meanGap_field
#print axioms geometryRow061_meanGap_numerator_no_slash
#print axioms geometryRow061_meanGap_numerator_parse
#print axioms geometryRow061_meanGap_denominator_parse
#print axioms geometryRow061_meanGap_denominator_nonzero
#print axioms geometryRow061_meanGap_parse
#print axioms geometryRow061_meanGap_read
#print axioms geometryRow061_jensenBound_field
#print axioms geometryRow061_jensenBound_numerator_no_slash
#print axioms geometryRow061_jensenBound_numerator_parse
#print axioms geometryRow061_jensenBound_denominator_parse
#print axioms geometryRow061_jensenBound_denominator_nonzero
#print axioms geometryRow061_jensenBound_parse
#print axioms geometryRow061_jensenBound_read
#print axioms geometryRow061_factorMaxima_read
#print axioms geometryRow061_gapWeightedMeans_read
#print axioms geometryRow061_floor_text_read
#print axioms geometryRow061_floor_chars_parse
#print axioms geometryRow061_floor_parse
#print axioms decode_geometry_Rows_061
#print axioms geometryRow062_simplexId_read
#print axioms geometryRow062_vertexIds_read
#print axioms geometryRow062_physicalVolume_field
#print axioms geometryRow062_physicalVolume_numerator_no_slash
#print axioms geometryRow062_physicalVolume_numerator_parse
#print axioms geometryRow062_physicalVolume_denominator_parse
#print axioms geometryRow062_physicalVolume_denominator_nonzero
#print axioms geometryRow062_physicalVolume_parse
#print axioms geometryRow062_physicalVolume_read
#print axioms geometryRow062_meanGap_field
#print axioms geometryRow062_meanGap_numerator_no_slash
#print axioms geometryRow062_meanGap_numerator_parse
#print axioms geometryRow062_meanGap_denominator_parse
#print axioms geometryRow062_meanGap_denominator_nonzero
#print axioms geometryRow062_meanGap_parse
#print axioms geometryRow062_meanGap_read
#print axioms geometryRow062_jensenBound_field
#print axioms geometryRow062_jensenBound_numerator_no_slash
#print axioms geometryRow062_jensenBound_numerator_parse
#print axioms geometryRow062_jensenBound_denominator_parse
#print axioms geometryRow062_jensenBound_denominator_nonzero
#print axioms geometryRow062_jensenBound_parse
#print axioms geometryRow062_jensenBound_read
#print axioms geometryRow062_factorMaxima_read
#print axioms geometryRow062_gapWeightedMeans_read
#print axioms geometryRow062_floor_text_read
#print axioms geometryRow062_floor_chars_parse
#print axioms geometryRow062_floor_parse
#print axioms decode_geometry_Rows_062
#print axioms geometry_Rows_block_031_push_eq
#print axioms geometry_Rows_block_031_reverse
#print axioms decode_geometry_Rows_block_031
#print axioms decode_geometry_Rows_through_block_031

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
