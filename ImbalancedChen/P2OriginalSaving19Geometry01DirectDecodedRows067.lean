import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows066

/-! Original simplices typed block 67, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson132 : SourceJson :=
  (SimplicesBlock067.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped132 : GeometryRow :=
  { simplexId := 132,
    vertexIds := #[39, 38, 36, 24, 23, 21, 8, 3, 1],
    physicalVolume := ((1005543209216348665138554452474449807 : ℚ) / (6547698892800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((57281 : ℚ) / (102000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ)), ((5343799 : ℚ) / (117500000 : ℚ))],
    gapWeightedMeans := #[((10282377435803 : ℚ) / (118411800000000 : ℚ)), ((10402072959023 : ℚ) / (118411800000000 : ℚ)), ((1339132915739 : ℚ) / (9108600000000 : ℚ)), ((3344393758607 : ℚ) / (29602950000000 : ℚ)), ((128038690517 : ℚ) / (2321800000000 : ℚ)), ((5385350288101 : ℚ) / (118411800000000 : ℚ)), ((320722593 : ℚ) / (8309600000 : ℚ)), ((56338361153 : ℚ) / (1480147500000 : ℚ)), ((4270788634339 : ℚ) / (118411800000000 : ℚ)), ((1423593580073 : ℚ) / (39470600000000 : ℚ))],
    jensenBound := ((2376639474127167212813262084179011400153470676666669740148402542832473766833319756250000000000000000 : ℚ) / (4183774070419602752100823695533850434727748796099004641442536781026368368390508593982565668993644293446407924411899 : ℚ)),
    jensenFloorQ96 := (45006440435030 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_simplexId_before"
  err.flush

theorem geometryRow132_simplexId_read :
    geometryRowsJson132.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped132.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_vertexIds_before"
  err.flush

theorem geometryRow132_vertexIds_read :
    geometryRowsJson132.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped132.vertexIds := by decide +kernel

noncomputable def geometryRow132_physicalVolumeNumeratorChars : List Char := ['1', '0', '0', '5', '5', '4', '3', '2', '0', '9', '2', '1', '6', '3', '4', '8', '6', '6', '5', '1', '3', '8', '5', '5', '4', '4', '5', '2', '4', '7', '4', '4', '4', '9', '8', '0', '7']
noncomputable def geometryRow132_physicalVolumeDenominatorChars : List Char := ['6', '5', '4', '7', '6', '9', '8', '8', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow132_physicalVolumeText : String := String.ofList (geometryRow132_physicalVolumeNumeratorChars ++ '/' :: geometryRow132_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_physicalVolume_before_field"
  err.flush

theorem geometryRow132_physicalVolume_field :
    geometryRowsJson132.getObjVal? "physical_volume" = .ok (.str geometryRow132_physicalVolumeText) := by rfl

theorem geometryRow132_physicalVolume_numerator_no_slash :
    geometryRow132_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow132_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow132_physicalVolumeNumeratorChars = some (1005543209216348665138554452474449807 : Int) := by decide +kernel

theorem geometryRow132_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow132_physicalVolumeDenominatorChars = some (6547698892800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow132_physicalVolume_denominator_nonzero : (6547698892800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow132_physicalVolume_parse :
    parseRational geometryRow132_physicalVolumeText = .ok geometryRowsTyped132.physicalVolume :=
  original_rational_fraction_of_chars geometryRow132_physicalVolumeNumeratorChars geometryRow132_physicalVolumeDenominatorChars
    (1005543209216348665138554452474449807 : Int) (6547698892800000000000000000000000000000000000000000000000000 : Int)
    geometryRow132_physicalVolume_numerator_no_slash geometryRow132_physicalVolume_numerator_parse
    geometryRow132_physicalVolume_denominator_parse geometryRow132_physicalVolume_denominator_nonzero

theorem geometryRow132_physicalVolume_read :
    rationalField geometryRowsJson132 "physical_volume" = .ok geometryRowsTyped132.physicalVolume :=
  original_rationalField_of_string geometryRowsJson132 "physical_volume" geometryRow132_physicalVolumeText
    geometryRowsTyped132.physicalVolume geometryRow132_physicalVolume_field geometryRow132_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_physicalVolume_complete"
  err.flush

noncomputable def geometryRow132_meanGapNumeratorChars : List Char := ['5', '7', '2', '8', '1']
noncomputable def geometryRow132_meanGapDenominatorChars : List Char := ['1', '0', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow132_meanGapText : String := String.ofList (geometryRow132_meanGapNumeratorChars ++ '/' :: geometryRow132_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_meanGap_before_field"
  err.flush

theorem geometryRow132_meanGap_field :
    geometryRowsJson132.getObjVal? "mean_gap" = .ok (.str geometryRow132_meanGapText) := by rfl

theorem geometryRow132_meanGap_numerator_no_slash :
    geometryRow132_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow132_meanGap_numerator_parse :
    SourceJson.intChars geometryRow132_meanGapNumeratorChars = some (57281 : Int) := by decide +kernel

theorem geometryRow132_meanGap_denominator_parse :
    SourceJson.intChars geometryRow132_meanGapDenominatorChars = some (102000000 : Int) := by decide +kernel

theorem geometryRow132_meanGap_denominator_nonzero : (102000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow132_meanGap_parse :
    parseRational geometryRow132_meanGapText = .ok geometryRowsTyped132.meanGap :=
  original_rational_fraction_of_chars geometryRow132_meanGapNumeratorChars geometryRow132_meanGapDenominatorChars
    (57281 : Int) (102000000 : Int)
    geometryRow132_meanGap_numerator_no_slash geometryRow132_meanGap_numerator_parse
    geometryRow132_meanGap_denominator_parse geometryRow132_meanGap_denominator_nonzero

theorem geometryRow132_meanGap_read :
    rationalField geometryRowsJson132 "mean_gap" = .ok geometryRowsTyped132.meanGap :=
  original_rationalField_of_string geometryRowsJson132 "mean_gap" geometryRow132_meanGapText
    geometryRowsTyped132.meanGap geometryRow132_meanGap_field geometryRow132_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_meanGap_complete"
  err.flush

noncomputable def geometryRow132_jensenBoundNumeratorChars : List Char := ['2', '3', '7', '6', '6', '3', '9', '4', '7', '4', '1', '2', '7', '1', '6', '7', '2', '1', '2', '8', '1', '3', '2', '6', '2', '0', '8', '4', '1', '7', '9', '0', '1', '1', '4', '0', '0', '1', '5', '3', '4', '7', '0', '6', '7', '6', '6', '6', '6', '6', '6', '9', '7', '4', '0', '1', '4', '8', '4', '0', '2', '5', '4', '2', '8', '3', '2', '4', '7', '3', '7', '6', '6', '8', '3', '3', '3', '1', '9', '7', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow132_jensenBoundDenominatorChars : List Char := ['4', '1', '8', '3', '7', '7', '4', '0', '7', '0', '4', '1', '9', '6', '0', '2', '7', '5', '2', '1', '0', '0', '8', '2', '3', '6', '9', '5', '5', '3', '3', '8', '5', '0', '4', '3', '4', '7', '2', '7', '7', '4', '8', '7', '9', '6', '0', '9', '9', '0', '0', '4', '6', '4', '1', '4', '4', '2', '5', '3', '6', '7', '8', '1', '0', '2', '6', '3', '6', '8', '3', '6', '8', '3', '9', '0', '5', '0', '8', '5', '9', '3', '9', '8', '2', '5', '6', '5', '6', '6', '8', '9', '9', '3', '6', '4', '4', '2', '9', '3', '4', '4', '6', '4', '0', '7', '9', '2', '4', '4', '1', '1', '8', '9', '9']
noncomputable def geometryRow132_jensenBoundText : String := String.ofList (geometryRow132_jensenBoundNumeratorChars ++ '/' :: geometryRow132_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_jensenBound_before_field"
  err.flush

theorem geometryRow132_jensenBound_field :
    geometryRowsJson132.getObjVal? "jensen_bound" = .ok (.str geometryRow132_jensenBoundText) := by rfl

theorem geometryRow132_jensenBound_numerator_no_slash :
    geometryRow132_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow132_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow132_jensenBoundNumeratorChars = some (2376639474127167212813262084179011400153470676666669740148402542832473766833319756250000000000000000 : Int) := by decide +kernel

theorem geometryRow132_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow132_jensenBoundDenominatorChars = some (4183774070419602752100823695533850434727748796099004641442536781026368368390508593982565668993644293446407924411899 : Int) := by decide +kernel

theorem geometryRow132_jensenBound_denominator_nonzero : (4183774070419602752100823695533850434727748796099004641442536781026368368390508593982565668993644293446407924411899 : Int) ≠ 0 := by decide +kernel

theorem geometryRow132_jensenBound_parse :
    parseRational geometryRow132_jensenBoundText = .ok geometryRowsTyped132.jensenBound :=
  original_rational_fraction_of_chars geometryRow132_jensenBoundNumeratorChars geometryRow132_jensenBoundDenominatorChars
    (2376639474127167212813262084179011400153470676666669740148402542832473766833319756250000000000000000 : Int) (4183774070419602752100823695533850434727748796099004641442536781026368368390508593982565668993644293446407924411899 : Int)
    geometryRow132_jensenBound_numerator_no_slash geometryRow132_jensenBound_numerator_parse
    geometryRow132_jensenBound_denominator_parse geometryRow132_jensenBound_denominator_nonzero

theorem geometryRow132_jensenBound_read :
    rationalField geometryRowsJson132 "jensen_bound" = .ok geometryRowsTyped132.jensenBound :=
  original_rationalField_of_string geometryRowsJson132 "jensen_bound" geometryRow132_jensenBoundText
    geometryRowsTyped132.jensenBound geometryRow132_jensenBound_field geometryRow132_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_factorMaxima_before"
  err.flush

theorem geometryRow132_factorMaxima_read :
    rationalArrayField geometryRowsJson132 "factor_maxima" = .ok geometryRowsTyped132.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_gapWeightedMeans_before"
  err.flush

theorem geometryRow132_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson132 "gap_weighted_means" = .ok geometryRowsTyped132.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow132_floorChars : List Char := ['4', '5', '0', '0', '6', '4', '4', '0', '4', '3', '5', '0', '3', '0']
noncomputable def geometryRow132_floorText : String := String.ofList geometryRow132_floorChars

theorem geometryRow132_floor_text_read :
    geometryRowsJson132.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow132_floorText := by rfl

theorem geometryRow132_floor_chars_parse :
    SourceJson.intChars geometryRow132_floorChars = some (45006440435030 : Int) := by decide +kernel

theorem geometryRow132_floor_parse :
    parseInteger geometryRow132_floorText = .ok geometryRowsTyped132.jensenFloorQ96 := by
  simp only [geometryRow132_floorText, parseInteger, String.toList_ofList, geometryRow132_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_132 :
    decodeGeometryRow geometryRowsJson132 = .ok geometryRowsTyped132 :=
  original_geometryRow_of_fields geometryRowsJson132 geometryRowsTyped132 geometryRow132_floorText
    geometryRow132_simplexId_read geometryRow132_vertexIds_read
    geometryRow132_physicalVolume_read geometryRow132_meanGap_read
    geometryRow132_factorMaxima_read geometryRow132_gapWeightedMeans_read
    geometryRow132_jensenBound_read geometryRow132_floor_text_read geometryRow132_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_132_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson133 : SourceJson :=
  (SimplicesBlock067.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped133 : GeometryRow :=
  { simplexId := 133,
    vertexIds := #[39, 38, 36, 24, 23, 21, 20, 3, 1],
    physicalVolume := ((30061907784460110569379535007876303479 : ℚ) / (985176848793600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((66369109 : ℚ) / (99756000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1515629 : ℚ) / (24000000 : ℚ)), ((303113 : ℚ) / (4800000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((45614288290768363129 : ℚ) / (545918756768400000000 : ℚ)), ((877458369230302696711 : ℚ) / (10372456378599600000000 : ℚ)), ((1531715719487301218639 : ℚ) / (10372456378599600000000 : ℚ)), ((581225556136909414703 : ℚ) / (5186228189299800000000 : ℚ)), ((33126252177649775177 : ℚ) / (610144492858800000000 : ℚ)), ((471216744428630004277 : ℚ) / (10372456378599600000000 : ℚ)), ((5442084486715042589 : ℚ) / (138299418381328000000 : ℚ)), ((80523556289471202991 : ℚ) / (2074491275719920000000 : ℚ)), ((130286609011579696531 : ℚ) / (3457485459533200000000 : ℚ)), ((390859135537647182953 : ℚ) / (10372456378599600000000 : ℚ))],
    jensenBound := ((32871864880476612128194299933507533996642418453377693189439809606378847976150250775480622938073028135138736536387068381167138408703796253355803193204302498787268352000000000000000000000 : ℚ) / (253311850602964197309621335903009868600721690438485219811661991579672279009453957534084252776871890188196444940835924089703583323805493345696148045381706738760155566455944418085126430803511320838536531 : ℚ)),
    jensenFloorQ96 := (10281309171671 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_simplexId_before"
  err.flush

theorem geometryRow133_simplexId_read :
    geometryRowsJson133.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped133.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_vertexIds_before"
  err.flush

theorem geometryRow133_vertexIds_read :
    geometryRowsJson133.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped133.vertexIds := by decide +kernel

noncomputable def geometryRow133_physicalVolumeNumeratorChars : List Char := ['3', '0', '0', '6', '1', '9', '0', '7', '7', '8', '4', '4', '6', '0', '1', '1', '0', '5', '6', '9', '3', '7', '9', '5', '3', '5', '0', '0', '7', '8', '7', '6', '3', '0', '3', '4', '7', '9']
noncomputable def geometryRow133_physicalVolumeDenominatorChars : List Char := ['9', '8', '5', '1', '7', '6', '8', '4', '8', '7', '9', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow133_physicalVolumeText : String := String.ofList (geometryRow133_physicalVolumeNumeratorChars ++ '/' :: geometryRow133_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_physicalVolume_before_field"
  err.flush

theorem geometryRow133_physicalVolume_field :
    geometryRowsJson133.getObjVal? "physical_volume" = .ok (.str geometryRow133_physicalVolumeText) := by rfl

theorem geometryRow133_physicalVolume_numerator_no_slash :
    geometryRow133_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow133_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow133_physicalVolumeNumeratorChars = some (30061907784460110569379535007876303479 : Int) := by decide +kernel

theorem geometryRow133_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow133_physicalVolumeDenominatorChars = some (985176848793600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow133_physicalVolume_denominator_nonzero : (985176848793600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow133_physicalVolume_parse :
    parseRational geometryRow133_physicalVolumeText = .ok geometryRowsTyped133.physicalVolume :=
  original_rational_fraction_of_chars geometryRow133_physicalVolumeNumeratorChars geometryRow133_physicalVolumeDenominatorChars
    (30061907784460110569379535007876303479 : Int) (985176848793600000000000000000000000000000000000000000000000000 : Int)
    geometryRow133_physicalVolume_numerator_no_slash geometryRow133_physicalVolume_numerator_parse
    geometryRow133_physicalVolume_denominator_parse geometryRow133_physicalVolume_denominator_nonzero

theorem geometryRow133_physicalVolume_read :
    rationalField geometryRowsJson133 "physical_volume" = .ok geometryRowsTyped133.physicalVolume :=
  original_rationalField_of_string geometryRowsJson133 "physical_volume" geometryRow133_physicalVolumeText
    geometryRowsTyped133.physicalVolume geometryRow133_physicalVolume_field geometryRow133_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_physicalVolume_complete"
  err.flush

noncomputable def geometryRow133_meanGapNumeratorChars : List Char := ['6', '6', '3', '6', '9', '1', '0', '9']
noncomputable def geometryRow133_meanGapDenominatorChars : List Char := ['9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow133_meanGapText : String := String.ofList (geometryRow133_meanGapNumeratorChars ++ '/' :: geometryRow133_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_meanGap_before_field"
  err.flush

theorem geometryRow133_meanGap_field :
    geometryRowsJson133.getObjVal? "mean_gap" = .ok (.str geometryRow133_meanGapText) := by rfl

theorem geometryRow133_meanGap_numerator_no_slash :
    geometryRow133_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow133_meanGap_numerator_parse :
    SourceJson.intChars geometryRow133_meanGapNumeratorChars = some (66369109 : Int) := by decide +kernel

theorem geometryRow133_meanGap_denominator_parse :
    SourceJson.intChars geometryRow133_meanGapDenominatorChars = some (99756000000 : Int) := by decide +kernel

theorem geometryRow133_meanGap_denominator_nonzero : (99756000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow133_meanGap_parse :
    parseRational geometryRow133_meanGapText = .ok geometryRowsTyped133.meanGap :=
  original_rational_fraction_of_chars geometryRow133_meanGapNumeratorChars geometryRow133_meanGapDenominatorChars
    (66369109 : Int) (99756000000 : Int)
    geometryRow133_meanGap_numerator_no_slash geometryRow133_meanGap_numerator_parse
    geometryRow133_meanGap_denominator_parse geometryRow133_meanGap_denominator_nonzero

theorem geometryRow133_meanGap_read :
    rationalField geometryRowsJson133 "mean_gap" = .ok geometryRowsTyped133.meanGap :=
  original_rationalField_of_string geometryRowsJson133 "mean_gap" geometryRow133_meanGapText
    geometryRowsTyped133.meanGap geometryRow133_meanGap_field geometryRow133_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_meanGap_complete"
  err.flush

noncomputable def geometryRow133_jensenBoundNumeratorChars : List Char := ['3', '2', '8', '7', '1', '8', '6', '4', '8', '8', '0', '4', '7', '6', '6', '1', '2', '1', '2', '8', '1', '9', '4', '2', '9', '9', '9', '3', '3', '5', '0', '7', '5', '3', '3', '9', '9', '6', '6', '4', '2', '4', '1', '8', '4', '5', '3', '3', '7', '7', '6', '9', '3', '1', '8', '9', '4', '3', '9', '8', '0', '9', '6', '0', '6', '3', '7', '8', '8', '4', '7', '9', '7', '6', '1', '5', '0', '2', '5', '0', '7', '7', '5', '4', '8', '0', '6', '2', '2', '9', '3', '8', '0', '7', '3', '0', '2', '8', '1', '3', '5', '1', '3', '8', '7', '3', '6', '5', '3', '6', '3', '8', '7', '0', '6', '8', '3', '8', '1', '1', '6', '7', '1', '3', '8', '4', '0', '8', '7', '0', '3', '7', '9', '6', '2', '5', '3', '3', '5', '5', '8', '0', '3', '1', '9', '3', '2', '0', '4', '3', '0', '2', '4', '9', '8', '7', '8', '7', '2', '6', '8', '3', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow133_jensenBoundDenominatorChars : List Char := ['2', '5', '3', '3', '1', '1', '8', '5', '0', '6', '0', '2', '9', '6', '4', '1', '9', '7', '3', '0', '9', '6', '2', '1', '3', '3', '5', '9', '0', '3', '0', '0', '9', '8', '6', '8', '6', '0', '0', '7', '2', '1', '6', '9', '0', '4', '3', '8', '4', '8', '5', '2', '1', '9', '8', '1', '1', '6', '6', '1', '9', '9', '1', '5', '7', '9', '6', '7', '2', '2', '7', '9', '0', '0', '9', '4', '5', '3', '9', '5', '7', '5', '3', '4', '0', '8', '4', '2', '5', '2', '7', '7', '6', '8', '7', '1', '8', '9', '0', '1', '8', '8', '1', '9', '6', '4', '4', '4', '9', '4', '0', '8', '3', '5', '9', '2', '4', '0', '8', '9', '7', '0', '3', '5', '8', '3', '3', '2', '3', '8', '0', '5', '4', '9', '3', '3', '4', '5', '6', '9', '6', '1', '4', '8', '0', '4', '5', '3', '8', '1', '7', '0', '6', '7', '3', '8', '7', '6', '0', '1', '5', '5', '5', '6', '6', '4', '5', '5', '9', '4', '4', '4', '1', '8', '0', '8', '5', '1', '2', '6', '4', '3', '0', '8', '0', '3', '5', '1', '1', '3', '2', '0', '8', '3', '8', '5', '3', '6', '5', '3', '1']
noncomputable def geometryRow133_jensenBoundText : String := String.ofList (geometryRow133_jensenBoundNumeratorChars ++ '/' :: geometryRow133_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_jensenBound_before_field"
  err.flush

theorem geometryRow133_jensenBound_field :
    geometryRowsJson133.getObjVal? "jensen_bound" = .ok (.str geometryRow133_jensenBoundText) := by rfl

theorem geometryRow133_jensenBound_numerator_no_slash :
    geometryRow133_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow133_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow133_jensenBoundNumeratorChars = some (32871864880476612128194299933507533996642418453377693189439809606378847976150250775480622938073028135138736536387068381167138408703796253355803193204302498787268352000000000000000000000 : Int) := by decide +kernel

theorem geometryRow133_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow133_jensenBoundDenominatorChars = some (253311850602964197309621335903009868600721690438485219811661991579672279009453957534084252776871890188196444940835924089703583323805493345696148045381706738760155566455944418085126430803511320838536531 : Int) := by decide +kernel

theorem geometryRow133_jensenBound_denominator_nonzero : (253311850602964197309621335903009868600721690438485219811661991579672279009453957534084252776871890188196444940835924089703583323805493345696148045381706738760155566455944418085126430803511320838536531 : Int) ≠ 0 := by decide +kernel

theorem geometryRow133_jensenBound_parse :
    parseRational geometryRow133_jensenBoundText = .ok geometryRowsTyped133.jensenBound :=
  original_rational_fraction_of_chars geometryRow133_jensenBoundNumeratorChars geometryRow133_jensenBoundDenominatorChars
    (32871864880476612128194299933507533996642418453377693189439809606378847976150250775480622938073028135138736536387068381167138408703796253355803193204302498787268352000000000000000000000 : Int) (253311850602964197309621335903009868600721690438485219811661991579672279009453957534084252776871890188196444940835924089703583323805493345696148045381706738760155566455944418085126430803511320838536531 : Int)
    geometryRow133_jensenBound_numerator_no_slash geometryRow133_jensenBound_numerator_parse
    geometryRow133_jensenBound_denominator_parse geometryRow133_jensenBound_denominator_nonzero

theorem geometryRow133_jensenBound_read :
    rationalField geometryRowsJson133 "jensen_bound" = .ok geometryRowsTyped133.jensenBound :=
  original_rationalField_of_string geometryRowsJson133 "jensen_bound" geometryRow133_jensenBoundText
    geometryRowsTyped133.jensenBound geometryRow133_jensenBound_field geometryRow133_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_factorMaxima_before"
  err.flush

theorem geometryRow133_factorMaxima_read :
    rationalArrayField geometryRowsJson133 "factor_maxima" = .ok geometryRowsTyped133.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_gapWeightedMeans_before"
  err.flush

theorem geometryRow133_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson133 "gap_weighted_means" = .ok geometryRowsTyped133.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow133_floorChars : List Char := ['1', '0', '2', '8', '1', '3', '0', '9', '1', '7', '1', '6', '7', '1']
noncomputable def geometryRow133_floorText : String := String.ofList geometryRow133_floorChars

theorem geometryRow133_floor_text_read :
    geometryRowsJson133.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow133_floorText := by rfl

theorem geometryRow133_floor_chars_parse :
    SourceJson.intChars geometryRow133_floorChars = some (10281309171671 : Int) := by decide +kernel

theorem geometryRow133_floor_parse :
    parseInteger geometryRow133_floorText = .ok geometryRowsTyped133.jensenFloorQ96 := by
  simp only [geometryRow133_floorText, parseInteger, String.toList_ofList, geometryRow133_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_133 :
    decodeGeometryRow geometryRowsJson133 = .ok geometryRowsTyped133 :=
  original_geometryRow_of_fields geometryRowsJson133 geometryRowsTyped133 geometryRow133_floorText
    geometryRow133_simplexId_read geometryRow133_vertexIds_read
    geometryRow133_physicalVolume_read geometryRow133_meanGap_read
    geometryRow133_factorMaxima_read geometryRow133_gapWeightedMeans_read
    geometryRow133_jensenBound_read geometryRow133_floor_text_read geometryRow133_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_133_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock067 : List SourceJson := [geometryRowsJson132, geometryRowsJson133]
noncomputable def geometryRowsTypedBlock067 : List (GeometryRow) := [geometryRowsTyped132, geometryRowsTyped133]
noncomputable def geometryRowsTypedThroughBlock067 : List (GeometryRow) := geometryRowsTypedThroughBlock066 ++ geometryRowsTypedBlock067

theorem geometry_Rows_block_067_push_eq (acc : List SourceJson) :
    SimplicesBlock067.blockPush acc = [geometryRowsJson133, geometryRowsJson132] ++ acc := by rfl

theorem geometry_Rows_block_067_reverse (acc : List SourceJson) :
    (SimplicesBlock067.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock067 := by
  rw [geometry_Rows_block_067_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_067 :
    geometryRowsJsonBlock067.mapM decodeGeometryRow = .ok geometryRowsTypedBlock067 := by
  simp only [geometryRowsJsonBlock067, geometryRowsTypedBlock067, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_132, decode_geometry_Rows_133]
  rfl

theorem decode_geometry_Rows_through_block_067 :
    SimplicesValue.arrayAcc068.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock067 := by
  change (SimplicesBlock067.blockPush SimplicesValue.arrayAcc067).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_067_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_066, decode_geometry_Rows_block_067]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_067_complete"
  err.flush

#print axioms geometryRow132_simplexId_read
#print axioms geometryRow132_vertexIds_read
#print axioms geometryRow132_physicalVolume_field
#print axioms geometryRow132_physicalVolume_numerator_no_slash
#print axioms geometryRow132_physicalVolume_numerator_parse
#print axioms geometryRow132_physicalVolume_denominator_parse
#print axioms geometryRow132_physicalVolume_denominator_nonzero
#print axioms geometryRow132_physicalVolume_parse
#print axioms geometryRow132_physicalVolume_read
#print axioms geometryRow132_meanGap_field
#print axioms geometryRow132_meanGap_numerator_no_slash
#print axioms geometryRow132_meanGap_numerator_parse
#print axioms geometryRow132_meanGap_denominator_parse
#print axioms geometryRow132_meanGap_denominator_nonzero
#print axioms geometryRow132_meanGap_parse
#print axioms geometryRow132_meanGap_read
#print axioms geometryRow132_jensenBound_field
#print axioms geometryRow132_jensenBound_numerator_no_slash
#print axioms geometryRow132_jensenBound_numerator_parse
#print axioms geometryRow132_jensenBound_denominator_parse
#print axioms geometryRow132_jensenBound_denominator_nonzero
#print axioms geometryRow132_jensenBound_parse
#print axioms geometryRow132_jensenBound_read
#print axioms geometryRow132_factorMaxima_read
#print axioms geometryRow132_gapWeightedMeans_read
#print axioms geometryRow132_floor_text_read
#print axioms geometryRow132_floor_chars_parse
#print axioms geometryRow132_floor_parse
#print axioms decode_geometry_Rows_132
#print axioms geometryRow133_simplexId_read
#print axioms geometryRow133_vertexIds_read
#print axioms geometryRow133_physicalVolume_field
#print axioms geometryRow133_physicalVolume_numerator_no_slash
#print axioms geometryRow133_physicalVolume_numerator_parse
#print axioms geometryRow133_physicalVolume_denominator_parse
#print axioms geometryRow133_physicalVolume_denominator_nonzero
#print axioms geometryRow133_physicalVolume_parse
#print axioms geometryRow133_physicalVolume_read
#print axioms geometryRow133_meanGap_field
#print axioms geometryRow133_meanGap_numerator_no_slash
#print axioms geometryRow133_meanGap_numerator_parse
#print axioms geometryRow133_meanGap_denominator_parse
#print axioms geometryRow133_meanGap_denominator_nonzero
#print axioms geometryRow133_meanGap_parse
#print axioms geometryRow133_meanGap_read
#print axioms geometryRow133_jensenBound_field
#print axioms geometryRow133_jensenBound_numerator_no_slash
#print axioms geometryRow133_jensenBound_numerator_parse
#print axioms geometryRow133_jensenBound_denominator_parse
#print axioms geometryRow133_jensenBound_denominator_nonzero
#print axioms geometryRow133_jensenBound_parse
#print axioms geometryRow133_jensenBound_read
#print axioms geometryRow133_factorMaxima_read
#print axioms geometryRow133_gapWeightedMeans_read
#print axioms geometryRow133_floor_text_read
#print axioms geometryRow133_floor_chars_parse
#print axioms geometryRow133_floor_parse
#print axioms decode_geometry_Rows_133
#print axioms geometry_Rows_block_067_push_eq
#print axioms geometry_Rows_block_067_reverse
#print axioms decode_geometry_Rows_block_067
#print axioms decode_geometry_Rows_through_block_067

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
