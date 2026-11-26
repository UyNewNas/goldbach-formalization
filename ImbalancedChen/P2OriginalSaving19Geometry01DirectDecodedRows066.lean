import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows065

/-! Original simplices typed block 66, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson130 : SourceJson :=
  (SimplicesBlock066.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped130 : GeometryRow :=
  { simplexId := 130,
    vertexIds := #[39, 38, 36, 24, 11, 10, 8, 3, 1],
    physicalVolume := ((13198047581401550909463248246903 : ℚ) / (4177920000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((46168299169 : ℚ) / (503880000000 : ℚ)), ((46677641821 : ℚ) / (503880000000 : ℚ)), ((23589477 : ℚ) / (161500000 : ℚ)), ((5793040801 : ℚ) / (50388000000 : ℚ)), ((138460253 : ℚ) / (2470000000 : ℚ)), ((3910361577 : ℚ) / (83980000000 : ℚ)), ((9798455689 : ℚ) / (251940000000 : ℚ)), ((7537867 : ℚ) / (209950000 : ℚ)), ((2781414481 : ℚ) / (83980000000 : ℚ)), ((8344226647 : ℚ) / (251940000000 : ℚ))],
    jensenBound := ((126057569186364986030432679024117199478348220408949432963636332650918750000000 : ℚ) / (10123107820950797814604204442571207797868797339619386754828169129213107728987202097604858779 : ℚ)),
    jensenFloorQ96 := (986585320861711 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_simplexId_before"
  err.flush

theorem geometryRow130_simplexId_read :
    geometryRowsJson130.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped130.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_vertexIds_before"
  err.flush

theorem geometryRow130_vertexIds_read :
    geometryRowsJson130.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped130.vertexIds := by decide +kernel

noncomputable def geometryRow130_physicalVolumeNumeratorChars : List Char := ['1', '3', '1', '9', '8', '0', '4', '7', '5', '8', '1', '4', '0', '1', '5', '5', '0', '9', '0', '9', '4', '6', '3', '2', '4', '8', '2', '4', '6', '9', '0', '3']
noncomputable def geometryRow130_physicalVolumeDenominatorChars : List Char := ['4', '1', '7', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow130_physicalVolumeText : String := String.ofList (geometryRow130_physicalVolumeNumeratorChars ++ '/' :: geometryRow130_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_physicalVolume_before_field"
  err.flush

theorem geometryRow130_physicalVolume_field :
    geometryRowsJson130.getObjVal? "physical_volume" = .ok (.str geometryRow130_physicalVolumeText) := by rfl

theorem geometryRow130_physicalVolume_numerator_no_slash :
    geometryRow130_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow130_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow130_physicalVolumeNumeratorChars = some (13198047581401550909463248246903 : Int) := by decide +kernel

theorem geometryRow130_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow130_physicalVolumeDenominatorChars = some (4177920000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow130_physicalVolume_denominator_nonzero : (4177920000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow130_physicalVolume_parse :
    parseRational geometryRow130_physicalVolumeText = .ok geometryRowsTyped130.physicalVolume :=
  original_rational_fraction_of_chars geometryRow130_physicalVolumeNumeratorChars geometryRow130_physicalVolumeDenominatorChars
    (13198047581401550909463248246903 : Int) (4177920000000000000000000000000000000000000000000000000 : Int)
    geometryRow130_physicalVolume_numerator_no_slash geometryRow130_physicalVolume_numerator_parse
    geometryRow130_physicalVolume_denominator_parse geometryRow130_physicalVolume_denominator_nonzero

theorem geometryRow130_physicalVolume_read :
    rationalField geometryRowsJson130 "physical_volume" = .ok geometryRowsTyped130.physicalVolume :=
  original_rationalField_of_string geometryRowsJson130 "physical_volume" geometryRow130_physicalVolumeText
    geometryRowsTyped130.physicalVolume geometryRow130_physicalVolume_field geometryRow130_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_physicalVolume_complete"
  err.flush

noncomputable def geometryRow130_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow130_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow130_meanGapText : String := String.ofList (geometryRow130_meanGapNumeratorChars ++ '/' :: geometryRow130_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_meanGap_before_field"
  err.flush

theorem geometryRow130_meanGap_field :
    geometryRowsJson130.getObjVal? "mean_gap" = .ok (.str geometryRow130_meanGapText) := by rfl

theorem geometryRow130_meanGap_numerator_no_slash :
    geometryRow130_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow130_meanGap_numerator_parse :
    SourceJson.intChars geometryRow130_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow130_meanGap_denominator_parse :
    SourceJson.intChars geometryRow130_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow130_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow130_meanGap_parse :
    parseRational geometryRow130_meanGapText = .ok geometryRowsTyped130.meanGap :=
  original_rational_fraction_of_chars geometryRow130_meanGapNumeratorChars geometryRow130_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow130_meanGap_numerator_no_slash geometryRow130_meanGap_numerator_parse
    geometryRow130_meanGap_denominator_parse geometryRow130_meanGap_denominator_nonzero

theorem geometryRow130_meanGap_read :
    rationalField geometryRowsJson130 "mean_gap" = .ok geometryRowsTyped130.meanGap :=
  original_rationalField_of_string geometryRowsJson130 "mean_gap" geometryRow130_meanGapText
    geometryRowsTyped130.meanGap geometryRow130_meanGap_field geometryRow130_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_meanGap_complete"
  err.flush

noncomputable def geometryRow130_jensenBoundNumeratorChars : List Char := ['1', '2', '6', '0', '5', '7', '5', '6', '9', '1', '8', '6', '3', '6', '4', '9', '8', '6', '0', '3', '0', '4', '3', '2', '6', '7', '9', '0', '2', '4', '1', '1', '7', '1', '9', '9', '4', '7', '8', '3', '4', '8', '2', '2', '0', '4', '0', '8', '9', '4', '9', '4', '3', '2', '9', '6', '3', '6', '3', '6', '3', '3', '2', '6', '5', '0', '9', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow130_jensenBoundDenominatorChars : List Char := ['1', '0', '1', '2', '3', '1', '0', '7', '8', '2', '0', '9', '5', '0', '7', '9', '7', '8', '1', '4', '6', '0', '4', '2', '0', '4', '4', '4', '2', '5', '7', '1', '2', '0', '7', '7', '9', '7', '8', '6', '8', '7', '9', '7', '3', '3', '9', '6', '1', '9', '3', '8', '6', '7', '5', '4', '8', '2', '8', '1', '6', '9', '1', '2', '9', '2', '1', '3', '1', '0', '7', '7', '2', '8', '9', '8', '7', '2', '0', '2', '0', '9', '7', '6', '0', '4', '8', '5', '8', '7', '7', '9']
noncomputable def geometryRow130_jensenBoundText : String := String.ofList (geometryRow130_jensenBoundNumeratorChars ++ '/' :: geometryRow130_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_jensenBound_before_field"
  err.flush

theorem geometryRow130_jensenBound_field :
    geometryRowsJson130.getObjVal? "jensen_bound" = .ok (.str geometryRow130_jensenBoundText) := by rfl

theorem geometryRow130_jensenBound_numerator_no_slash :
    geometryRow130_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow130_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow130_jensenBoundNumeratorChars = some (126057569186364986030432679024117199478348220408949432963636332650918750000000 : Int) := by decide +kernel

theorem geometryRow130_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow130_jensenBoundDenominatorChars = some (10123107820950797814604204442571207797868797339619386754828169129213107728987202097604858779 : Int) := by decide +kernel

theorem geometryRow130_jensenBound_denominator_nonzero : (10123107820950797814604204442571207797868797339619386754828169129213107728987202097604858779 : Int) ≠ 0 := by decide +kernel

theorem geometryRow130_jensenBound_parse :
    parseRational geometryRow130_jensenBoundText = .ok geometryRowsTyped130.jensenBound :=
  original_rational_fraction_of_chars geometryRow130_jensenBoundNumeratorChars geometryRow130_jensenBoundDenominatorChars
    (126057569186364986030432679024117199478348220408949432963636332650918750000000 : Int) (10123107820950797814604204442571207797868797339619386754828169129213107728987202097604858779 : Int)
    geometryRow130_jensenBound_numerator_no_slash geometryRow130_jensenBound_numerator_parse
    geometryRow130_jensenBound_denominator_parse geometryRow130_jensenBound_denominator_nonzero

theorem geometryRow130_jensenBound_read :
    rationalField geometryRowsJson130 "jensen_bound" = .ok geometryRowsTyped130.jensenBound :=
  original_rationalField_of_string geometryRowsJson130 "jensen_bound" geometryRow130_jensenBoundText
    geometryRowsTyped130.jensenBound geometryRow130_jensenBound_field geometryRow130_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_factorMaxima_before"
  err.flush

theorem geometryRow130_factorMaxima_read :
    rationalArrayField geometryRowsJson130 "factor_maxima" = .ok geometryRowsTyped130.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_gapWeightedMeans_before"
  err.flush

theorem geometryRow130_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson130 "gap_weighted_means" = .ok geometryRowsTyped130.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow130_floorChars : List Char := ['9', '8', '6', '5', '8', '5', '3', '2', '0', '8', '6', '1', '7', '1', '1']
noncomputable def geometryRow130_floorText : String := String.ofList geometryRow130_floorChars

theorem geometryRow130_floor_text_read :
    geometryRowsJson130.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow130_floorText := by rfl

theorem geometryRow130_floor_chars_parse :
    SourceJson.intChars geometryRow130_floorChars = some (986585320861711 : Int) := by decide +kernel

theorem geometryRow130_floor_parse :
    parseInteger geometryRow130_floorText = .ok geometryRowsTyped130.jensenFloorQ96 := by
  simp only [geometryRow130_floorText, parseInteger, String.toList_ofList, geometryRow130_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_130 :
    decodeGeometryRow geometryRowsJson130 = .ok geometryRowsTyped130 :=
  original_geometryRow_of_fields geometryRowsJson130 geometryRowsTyped130 geometryRow130_floorText
    geometryRow130_simplexId_read geometryRow130_vertexIds_read
    geometryRow130_physicalVolume_read geometryRow130_meanGap_read
    geometryRow130_factorMaxima_read geometryRow130_gapWeightedMeans_read
    geometryRow130_jensenBound_read geometryRow130_floor_text_read geometryRow130_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_130_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson131 : SourceJson :=
  (SimplicesBlock066.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped131 : GeometryRow :=
  { simplexId := 131,
    vertexIds := #[39, 38, 36, 24, 23, 10, 8, 3, 1],
    physicalVolume := ((981786034204264484206427577001043 : ℚ) / (1428848640000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((89916799723 : ℚ) / (1007760000000 : ℚ)), ((90935485027 : ℚ) / (1007760000000 : ℚ)), ((11360176631 : ℚ) / (77520000000 : ℚ)), ((57446448287 : ℚ) / (503880000000 : ℚ)), ((3294577853 : ℚ) / (59280000000 : ℚ)), ((46440379201 : ℚ) / (1007760000000 : ℚ)), ((674400131 : ℚ) / (17680000000 : ℚ)), ((7580539267 : ℚ) / (201552000000 : ℚ)), ((11609617647 : ℚ) / (335920000000 : ℚ)), ((34828785757 : ℚ) / (1007760000000 : ℚ))],
    jensenBound := ((25677454509846292551192920414353857857484956982701049279381273693388800000000000000 : ℚ) / (9821101062703020192660767902720598997708285347167616683383552686841621542795779752442459369463741 : ℚ)),
    jensenFloorQ96 := (207143529617525 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_simplexId_before"
  err.flush

theorem geometryRow131_simplexId_read :
    geometryRowsJson131.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped131.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_vertexIds_before"
  err.flush

theorem geometryRow131_vertexIds_read :
    geometryRowsJson131.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped131.vertexIds := by decide +kernel

noncomputable def geometryRow131_physicalVolumeNumeratorChars : List Char := ['9', '8', '1', '7', '8', '6', '0', '3', '4', '2', '0', '4', '2', '6', '4', '4', '8', '4', '2', '0', '6', '4', '2', '7', '5', '7', '7', '0', '0', '1', '0', '4', '3']
noncomputable def geometryRow131_physicalVolumeDenominatorChars : List Char := ['1', '4', '2', '8', '8', '4', '8', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow131_physicalVolumeText : String := String.ofList (geometryRow131_physicalVolumeNumeratorChars ++ '/' :: geometryRow131_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_physicalVolume_before_field"
  err.flush

theorem geometryRow131_physicalVolume_field :
    geometryRowsJson131.getObjVal? "physical_volume" = .ok (.str geometryRow131_physicalVolumeText) := by rfl

theorem geometryRow131_physicalVolume_numerator_no_slash :
    geometryRow131_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow131_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow131_physicalVolumeNumeratorChars = some (981786034204264484206427577001043 : Int) := by decide +kernel

theorem geometryRow131_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow131_physicalVolumeDenominatorChars = some (1428848640000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow131_physicalVolume_denominator_nonzero : (1428848640000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow131_physicalVolume_parse :
    parseRational geometryRow131_physicalVolumeText = .ok geometryRowsTyped131.physicalVolume :=
  original_rational_fraction_of_chars geometryRow131_physicalVolumeNumeratorChars geometryRow131_physicalVolumeDenominatorChars
    (981786034204264484206427577001043 : Int) (1428848640000000000000000000000000000000000000000000000000 : Int)
    geometryRow131_physicalVolume_numerator_no_slash geometryRow131_physicalVolume_numerator_parse
    geometryRow131_physicalVolume_denominator_parse geometryRow131_physicalVolume_denominator_nonzero

theorem geometryRow131_physicalVolume_read :
    rationalField geometryRowsJson131 "physical_volume" = .ok geometryRowsTyped131.physicalVolume :=
  original_rationalField_of_string geometryRowsJson131 "physical_volume" geometryRow131_physicalVolumeText
    geometryRowsTyped131.physicalVolume geometryRow131_physicalVolume_field geometryRow131_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_physicalVolume_complete"
  err.flush

noncomputable def geometryRow131_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow131_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow131_meanGapText : String := String.ofList (geometryRow131_meanGapNumeratorChars ++ '/' :: geometryRow131_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_meanGap_before_field"
  err.flush

theorem geometryRow131_meanGap_field :
    geometryRowsJson131.getObjVal? "mean_gap" = .ok (.str geometryRow131_meanGapText) := by rfl

theorem geometryRow131_meanGap_numerator_no_slash :
    geometryRow131_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow131_meanGap_numerator_parse :
    SourceJson.intChars geometryRow131_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow131_meanGap_denominator_parse :
    SourceJson.intChars geometryRow131_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow131_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow131_meanGap_parse :
    parseRational geometryRow131_meanGapText = .ok geometryRowsTyped131.meanGap :=
  original_rational_fraction_of_chars geometryRow131_meanGapNumeratorChars geometryRow131_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow131_meanGap_numerator_no_slash geometryRow131_meanGap_numerator_parse
    geometryRow131_meanGap_denominator_parse geometryRow131_meanGap_denominator_nonzero

theorem geometryRow131_meanGap_read :
    rationalField geometryRowsJson131 "mean_gap" = .ok geometryRowsTyped131.meanGap :=
  original_rationalField_of_string geometryRowsJson131 "mean_gap" geometryRow131_meanGapText
    geometryRowsTyped131.meanGap geometryRow131_meanGap_field geometryRow131_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_meanGap_complete"
  err.flush

noncomputable def geometryRow131_jensenBoundNumeratorChars : List Char := ['2', '5', '6', '7', '7', '4', '5', '4', '5', '0', '9', '8', '4', '6', '2', '9', '2', '5', '5', '1', '1', '9', '2', '9', '2', '0', '4', '1', '4', '3', '5', '3', '8', '5', '7', '8', '5', '7', '4', '8', '4', '9', '5', '6', '9', '8', '2', '7', '0', '1', '0', '4', '9', '2', '7', '9', '3', '8', '1', '2', '7', '3', '6', '9', '3', '3', '8', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow131_jensenBoundDenominatorChars : List Char := ['9', '8', '2', '1', '1', '0', '1', '0', '6', '2', '7', '0', '3', '0', '2', '0', '1', '9', '2', '6', '6', '0', '7', '6', '7', '9', '0', '2', '7', '2', '0', '5', '9', '8', '9', '9', '7', '7', '0', '8', '2', '8', '5', '3', '4', '7', '1', '6', '7', '6', '1', '6', '6', '8', '3', '3', '8', '3', '5', '5', '2', '6', '8', '6', '8', '4', '1', '6', '2', '1', '5', '4', '2', '7', '9', '5', '7', '7', '9', '7', '5', '2', '4', '4', '2', '4', '5', '9', '3', '6', '9', '4', '6', '3', '7', '4', '1']
noncomputable def geometryRow131_jensenBoundText : String := String.ofList (geometryRow131_jensenBoundNumeratorChars ++ '/' :: geometryRow131_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_jensenBound_before_field"
  err.flush

theorem geometryRow131_jensenBound_field :
    geometryRowsJson131.getObjVal? "jensen_bound" = .ok (.str geometryRow131_jensenBoundText) := by rfl

theorem geometryRow131_jensenBound_numerator_no_slash :
    geometryRow131_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow131_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow131_jensenBoundNumeratorChars = some (25677454509846292551192920414353857857484956982701049279381273693388800000000000000 : Int) := by decide +kernel

theorem geometryRow131_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow131_jensenBoundDenominatorChars = some (9821101062703020192660767902720598997708285347167616683383552686841621542795779752442459369463741 : Int) := by decide +kernel

theorem geometryRow131_jensenBound_denominator_nonzero : (9821101062703020192660767902720598997708285347167616683383552686841621542795779752442459369463741 : Int) ≠ 0 := by decide +kernel

theorem geometryRow131_jensenBound_parse :
    parseRational geometryRow131_jensenBoundText = .ok geometryRowsTyped131.jensenBound :=
  original_rational_fraction_of_chars geometryRow131_jensenBoundNumeratorChars geometryRow131_jensenBoundDenominatorChars
    (25677454509846292551192920414353857857484956982701049279381273693388800000000000000 : Int) (9821101062703020192660767902720598997708285347167616683383552686841621542795779752442459369463741 : Int)
    geometryRow131_jensenBound_numerator_no_slash geometryRow131_jensenBound_numerator_parse
    geometryRow131_jensenBound_denominator_parse geometryRow131_jensenBound_denominator_nonzero

theorem geometryRow131_jensenBound_read :
    rationalField geometryRowsJson131 "jensen_bound" = .ok geometryRowsTyped131.jensenBound :=
  original_rationalField_of_string geometryRowsJson131 "jensen_bound" geometryRow131_jensenBoundText
    geometryRowsTyped131.jensenBound geometryRow131_jensenBound_field geometryRow131_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_factorMaxima_before"
  err.flush

theorem geometryRow131_factorMaxima_read :
    rationalArrayField geometryRowsJson131 "factor_maxima" = .ok geometryRowsTyped131.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_gapWeightedMeans_before"
  err.flush

theorem geometryRow131_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson131 "gap_weighted_means" = .ok geometryRowsTyped131.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow131_floorChars : List Char := ['2', '0', '7', '1', '4', '3', '5', '2', '9', '6', '1', '7', '5', '2', '5']
noncomputable def geometryRow131_floorText : String := String.ofList geometryRow131_floorChars

theorem geometryRow131_floor_text_read :
    geometryRowsJson131.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow131_floorText := by rfl

theorem geometryRow131_floor_chars_parse :
    SourceJson.intChars geometryRow131_floorChars = some (207143529617525 : Int) := by decide +kernel

theorem geometryRow131_floor_parse :
    parseInteger geometryRow131_floorText = .ok geometryRowsTyped131.jensenFloorQ96 := by
  simp only [geometryRow131_floorText, parseInteger, String.toList_ofList, geometryRow131_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_131 :
    decodeGeometryRow geometryRowsJson131 = .ok geometryRowsTyped131 :=
  original_geometryRow_of_fields geometryRowsJson131 geometryRowsTyped131 geometryRow131_floorText
    geometryRow131_simplexId_read geometryRow131_vertexIds_read
    geometryRow131_physicalVolume_read geometryRow131_meanGap_read
    geometryRow131_factorMaxima_read geometryRow131_gapWeightedMeans_read
    geometryRow131_jensenBound_read geometryRow131_floor_text_read geometryRow131_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_131_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock066 : List SourceJson := [geometryRowsJson130, geometryRowsJson131]
noncomputable def geometryRowsTypedBlock066 : List (GeometryRow) := [geometryRowsTyped130, geometryRowsTyped131]
noncomputable def geometryRowsTypedThroughBlock066 : List (GeometryRow) := geometryRowsTypedThroughBlock065 ++ geometryRowsTypedBlock066

theorem geometry_Rows_block_066_push_eq (acc : List SourceJson) :
    SimplicesBlock066.blockPush acc = [geometryRowsJson131, geometryRowsJson130] ++ acc := by rfl

theorem geometry_Rows_block_066_reverse (acc : List SourceJson) :
    (SimplicesBlock066.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock066 := by
  rw [geometry_Rows_block_066_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_066 :
    geometryRowsJsonBlock066.mapM decodeGeometryRow = .ok geometryRowsTypedBlock066 := by
  simp only [geometryRowsJsonBlock066, geometryRowsTypedBlock066, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_130, decode_geometry_Rows_131]
  rfl

theorem decode_geometry_Rows_through_block_066 :
    SimplicesValue.arrayAcc067.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock066 := by
  change (SimplicesBlock066.blockPush SimplicesValue.arrayAcc066).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_066_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_065, decode_geometry_Rows_block_066]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_066_complete"
  err.flush

#print axioms geometryRow130_simplexId_read
#print axioms geometryRow130_vertexIds_read
#print axioms geometryRow130_physicalVolume_field
#print axioms geometryRow130_physicalVolume_numerator_no_slash
#print axioms geometryRow130_physicalVolume_numerator_parse
#print axioms geometryRow130_physicalVolume_denominator_parse
#print axioms geometryRow130_physicalVolume_denominator_nonzero
#print axioms geometryRow130_physicalVolume_parse
#print axioms geometryRow130_physicalVolume_read
#print axioms geometryRow130_meanGap_field
#print axioms geometryRow130_meanGap_numerator_no_slash
#print axioms geometryRow130_meanGap_numerator_parse
#print axioms geometryRow130_meanGap_denominator_parse
#print axioms geometryRow130_meanGap_denominator_nonzero
#print axioms geometryRow130_meanGap_parse
#print axioms geometryRow130_meanGap_read
#print axioms geometryRow130_jensenBound_field
#print axioms geometryRow130_jensenBound_numerator_no_slash
#print axioms geometryRow130_jensenBound_numerator_parse
#print axioms geometryRow130_jensenBound_denominator_parse
#print axioms geometryRow130_jensenBound_denominator_nonzero
#print axioms geometryRow130_jensenBound_parse
#print axioms geometryRow130_jensenBound_read
#print axioms geometryRow130_factorMaxima_read
#print axioms geometryRow130_gapWeightedMeans_read
#print axioms geometryRow130_floor_text_read
#print axioms geometryRow130_floor_chars_parse
#print axioms geometryRow130_floor_parse
#print axioms decode_geometry_Rows_130
#print axioms geometryRow131_simplexId_read
#print axioms geometryRow131_vertexIds_read
#print axioms geometryRow131_physicalVolume_field
#print axioms geometryRow131_physicalVolume_numerator_no_slash
#print axioms geometryRow131_physicalVolume_numerator_parse
#print axioms geometryRow131_physicalVolume_denominator_parse
#print axioms geometryRow131_physicalVolume_denominator_nonzero
#print axioms geometryRow131_physicalVolume_parse
#print axioms geometryRow131_physicalVolume_read
#print axioms geometryRow131_meanGap_field
#print axioms geometryRow131_meanGap_numerator_no_slash
#print axioms geometryRow131_meanGap_numerator_parse
#print axioms geometryRow131_meanGap_denominator_parse
#print axioms geometryRow131_meanGap_denominator_nonzero
#print axioms geometryRow131_meanGap_parse
#print axioms geometryRow131_meanGap_read
#print axioms geometryRow131_jensenBound_field
#print axioms geometryRow131_jensenBound_numerator_no_slash
#print axioms geometryRow131_jensenBound_numerator_parse
#print axioms geometryRow131_jensenBound_denominator_parse
#print axioms geometryRow131_jensenBound_denominator_nonzero
#print axioms geometryRow131_jensenBound_parse
#print axioms geometryRow131_jensenBound_read
#print axioms geometryRow131_factorMaxima_read
#print axioms geometryRow131_gapWeightedMeans_read
#print axioms geometryRow131_floor_text_read
#print axioms geometryRow131_floor_chars_parse
#print axioms geometryRow131_floor_parse
#print axioms decode_geometry_Rows_131
#print axioms geometry_Rows_block_066_push_eq
#print axioms geometry_Rows_block_066_reverse
#print axioms decode_geometry_Rows_block_066
#print axioms decode_geometry_Rows_through_block_066

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
