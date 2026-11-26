import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows041

/-! Original simplices typed block 42, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson083 : SourceJson :=
  (SimplicesBlock042.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped083 : GeometryRow :=
  { simplexId := 83,
    vertexIds := #[39, 37, 24, 23, 10, 8, 3, 2, 0],
    physicalVolume := ((3180048514856247124904361585125805477691 : ℚ) / (879599222784000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1074023 : ℚ) / (937125000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((77379843873444323 : ℚ) / (865885934784000000 : ℚ)), ((19286334262504196089 : ℚ) / (212142054022080000000 : ℚ)), ((93641225565543353 : ℚ) / (652744781606400000 : ℚ)), ((35566097349551837669 : ℚ) / (318213081033120000000 : ℚ)), ((699626872179813607 : ℚ) / (12478944354240000000 : ℚ)), ((10203415279375206463 : ℚ) / (212142054022080000000 : ℚ)), ((10377959260581859 : ℚ) / (267968910343680000 : ℚ)), ((24307822329275381957 : ℚ) / (636426162066240000000 : ℚ)), ((4495225297950902779 : ℚ) / (127285232413248000000 : ℚ)), ((22138908160687248041 : ℚ) / (636426162066240000000 : ℚ))],
    jensenBound := ((797515161257732379772560351631258081677338332162083750845964659474648890312078790173366123697076993811957986084677674881358139691035299706489771149542149370937344000000000 : ℚ) / (30715710402430098059551676423731606888954137961022014490759191621073542991609073307625974579391964144262823200022673606962196774142591094629915417786740054646144484833857030017671687 : ℚ)),
    jensenFloorQ96 := (2057112141502622274 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_simplexId_before"
  err.flush

theorem geometryRow083_simplexId_read :
    geometryRowsJson083.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped083.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_vertexIds_before"
  err.flush

theorem geometryRow083_vertexIds_read :
    geometryRowsJson083.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped083.vertexIds := by decide +kernel

noncomputable def geometryRow083_physicalVolumeNumeratorChars : List Char := ['3', '1', '8', '0', '0', '4', '8', '5', '1', '4', '8', '5', '6', '2', '4', '7', '1', '2', '4', '9', '0', '4', '3', '6', '1', '5', '8', '5', '1', '2', '5', '8', '0', '5', '4', '7', '7', '6', '9', '1']
noncomputable def geometryRow083_physicalVolumeDenominatorChars : List Char := ['8', '7', '9', '5', '9', '9', '2', '2', '2', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow083_physicalVolumeText : String := String.ofList (geometryRow083_physicalVolumeNumeratorChars ++ '/' :: geometryRow083_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_physicalVolume_before_field"
  err.flush

theorem geometryRow083_physicalVolume_field :
    geometryRowsJson083.getObjVal? "physical_volume" = .ok (.str geometryRow083_physicalVolumeText) := by rfl

theorem geometryRow083_physicalVolume_numerator_no_slash :
    geometryRow083_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow083_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow083_physicalVolumeNumeratorChars = some (3180048514856247124904361585125805477691 : Int) := by decide +kernel

theorem geometryRow083_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow083_physicalVolumeDenominatorChars = some (879599222784000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow083_physicalVolume_denominator_nonzero : (879599222784000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow083_physicalVolume_parse :
    parseRational geometryRow083_physicalVolumeText = .ok geometryRowsTyped083.physicalVolume :=
  original_rational_fraction_of_chars geometryRow083_physicalVolumeNumeratorChars geometryRow083_physicalVolumeDenominatorChars
    (3180048514856247124904361585125805477691 : Int) (879599222784000000000000000000000000000000000000000000000000 : Int)
    geometryRow083_physicalVolume_numerator_no_slash geometryRow083_physicalVolume_numerator_parse
    geometryRow083_physicalVolume_denominator_parse geometryRow083_physicalVolume_denominator_nonzero

theorem geometryRow083_physicalVolume_read :
    rationalField geometryRowsJson083 "physical_volume" = .ok geometryRowsTyped083.physicalVolume :=
  original_rationalField_of_string geometryRowsJson083 "physical_volume" geometryRow083_physicalVolumeText
    geometryRowsTyped083.physicalVolume geometryRow083_physicalVolume_field geometryRow083_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_physicalVolume_complete"
  err.flush

noncomputable def geometryRow083_meanGapNumeratorChars : List Char := ['1', '0', '7', '4', '0', '2', '3']
noncomputable def geometryRow083_meanGapDenominatorChars : List Char := ['9', '3', '7', '1', '2', '5', '0', '0', '0']
noncomputable def geometryRow083_meanGapText : String := String.ofList (geometryRow083_meanGapNumeratorChars ++ '/' :: geometryRow083_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_meanGap_before_field"
  err.flush

theorem geometryRow083_meanGap_field :
    geometryRowsJson083.getObjVal? "mean_gap" = .ok (.str geometryRow083_meanGapText) := by rfl

theorem geometryRow083_meanGap_numerator_no_slash :
    geometryRow083_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow083_meanGap_numerator_parse :
    SourceJson.intChars geometryRow083_meanGapNumeratorChars = some (1074023 : Int) := by decide +kernel

theorem geometryRow083_meanGap_denominator_parse :
    SourceJson.intChars geometryRow083_meanGapDenominatorChars = some (937125000 : Int) := by decide +kernel

theorem geometryRow083_meanGap_denominator_nonzero : (937125000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow083_meanGap_parse :
    parseRational geometryRow083_meanGapText = .ok geometryRowsTyped083.meanGap :=
  original_rational_fraction_of_chars geometryRow083_meanGapNumeratorChars geometryRow083_meanGapDenominatorChars
    (1074023 : Int) (937125000 : Int)
    geometryRow083_meanGap_numerator_no_slash geometryRow083_meanGap_numerator_parse
    geometryRow083_meanGap_denominator_parse geometryRow083_meanGap_denominator_nonzero

theorem geometryRow083_meanGap_read :
    rationalField geometryRowsJson083 "mean_gap" = .ok geometryRowsTyped083.meanGap :=
  original_rationalField_of_string geometryRowsJson083 "mean_gap" geometryRow083_meanGapText
    geometryRowsTyped083.meanGap geometryRow083_meanGap_field geometryRow083_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_meanGap_complete"
  err.flush

noncomputable def geometryRow083_jensenBoundNumeratorChars : List Char := ['7', '9', '7', '5', '1', '5', '1', '6', '1', '2', '5', '7', '7', '3', '2', '3', '7', '9', '7', '7', '2', '5', '6', '0', '3', '5', '1', '6', '3', '1', '2', '5', '8', '0', '8', '1', '6', '7', '7', '3', '3', '8', '3', '3', '2', '1', '6', '2', '0', '8', '3', '7', '5', '0', '8', '4', '5', '9', '6', '4', '6', '5', '9', '4', '7', '4', '6', '4', '8', '8', '9', '0', '3', '1', '2', '0', '7', '8', '7', '9', '0', '1', '7', '3', '3', '6', '6', '1', '2', '3', '6', '9', '7', '0', '7', '6', '9', '9', '3', '8', '1', '1', '9', '5', '7', '9', '8', '6', '0', '8', '4', '6', '7', '7', '6', '7', '4', '8', '8', '1', '3', '5', '8', '1', '3', '9', '6', '9', '1', '0', '3', '5', '2', '9', '9', '7', '0', '6', '4', '8', '9', '7', '7', '1', '1', '4', '9', '5', '4', '2', '1', '4', '9', '3', '7', '0', '9', '3', '7', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow083_jensenBoundDenominatorChars : List Char := ['3', '0', '7', '1', '5', '7', '1', '0', '4', '0', '2', '4', '3', '0', '0', '9', '8', '0', '5', '9', '5', '5', '1', '6', '7', '6', '4', '2', '3', '7', '3', '1', '6', '0', '6', '8', '8', '8', '9', '5', '4', '1', '3', '7', '9', '6', '1', '0', '2', '2', '0', '1', '4', '4', '9', '0', '7', '5', '9', '1', '9', '1', '6', '2', '1', '0', '7', '3', '5', '4', '2', '9', '9', '1', '6', '0', '9', '0', '7', '3', '3', '0', '7', '6', '2', '5', '9', '7', '4', '5', '7', '9', '3', '9', '1', '9', '6', '4', '1', '4', '4', '2', '6', '2', '8', '2', '3', '2', '0', '0', '0', '2', '2', '6', '7', '3', '6', '0', '6', '9', '6', '2', '1', '9', '6', '7', '7', '4', '1', '4', '2', '5', '9', '1', '0', '9', '4', '6', '2', '9', '9', '1', '5', '4', '1', '7', '7', '8', '6', '7', '4', '0', '0', '5', '4', '6', '4', '6', '1', '4', '4', '4', '8', '4', '8', '3', '3', '8', '5', '7', '0', '3', '0', '0', '1', '7', '6', '7', '1', '6', '8', '7']
noncomputable def geometryRow083_jensenBoundText : String := String.ofList (geometryRow083_jensenBoundNumeratorChars ++ '/' :: geometryRow083_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_jensenBound_before_field"
  err.flush

theorem geometryRow083_jensenBound_field :
    geometryRowsJson083.getObjVal? "jensen_bound" = .ok (.str geometryRow083_jensenBoundText) := by rfl

theorem geometryRow083_jensenBound_numerator_no_slash :
    geometryRow083_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow083_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow083_jensenBoundNumeratorChars = some (797515161257732379772560351631258081677338332162083750845964659474648890312078790173366123697076993811957986084677674881358139691035299706489771149542149370937344000000000 : Int) := by decide +kernel

theorem geometryRow083_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow083_jensenBoundDenominatorChars = some (30715710402430098059551676423731606888954137961022014490759191621073542991609073307625974579391964144262823200022673606962196774142591094629915417786740054646144484833857030017671687 : Int) := by decide +kernel

theorem geometryRow083_jensenBound_denominator_nonzero : (30715710402430098059551676423731606888954137961022014490759191621073542991609073307625974579391964144262823200022673606962196774142591094629915417786740054646144484833857030017671687 : Int) ≠ 0 := by decide +kernel

theorem geometryRow083_jensenBound_parse :
    parseRational geometryRow083_jensenBoundText = .ok geometryRowsTyped083.jensenBound :=
  original_rational_fraction_of_chars geometryRow083_jensenBoundNumeratorChars geometryRow083_jensenBoundDenominatorChars
    (797515161257732379772560351631258081677338332162083750845964659474648890312078790173366123697076993811957986084677674881358139691035299706489771149542149370937344000000000 : Int) (30715710402430098059551676423731606888954137961022014490759191621073542991609073307625974579391964144262823200022673606962196774142591094629915417786740054646144484833857030017671687 : Int)
    geometryRow083_jensenBound_numerator_no_slash geometryRow083_jensenBound_numerator_parse
    geometryRow083_jensenBound_denominator_parse geometryRow083_jensenBound_denominator_nonzero

theorem geometryRow083_jensenBound_read :
    rationalField geometryRowsJson083 "jensen_bound" = .ok geometryRowsTyped083.jensenBound :=
  original_rationalField_of_string geometryRowsJson083 "jensen_bound" geometryRow083_jensenBoundText
    geometryRowsTyped083.jensenBound geometryRow083_jensenBound_field geometryRow083_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_factorMaxima_before"
  err.flush

theorem geometryRow083_factorMaxima_read :
    rationalArrayField geometryRowsJson083 "factor_maxima" = .ok geometryRowsTyped083.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_gapWeightedMeans_before"
  err.flush

theorem geometryRow083_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson083 "gap_weighted_means" = .ok geometryRowsTyped083.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow083_floorChars : List Char := ['2', '0', '5', '7', '1', '1', '2', '1', '4', '1', '5', '0', '2', '6', '2', '2', '2', '7', '4']
noncomputable def geometryRow083_floorText : String := String.ofList geometryRow083_floorChars

theorem geometryRow083_floor_text_read :
    geometryRowsJson083.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow083_floorText := by rfl

theorem geometryRow083_floor_chars_parse :
    SourceJson.intChars geometryRow083_floorChars = some (2057112141502622274 : Int) := by decide +kernel

theorem geometryRow083_floor_parse :
    parseInteger geometryRow083_floorText = .ok geometryRowsTyped083.jensenFloorQ96 := by
  simp only [geometryRow083_floorText, parseInteger, String.toList_ofList, geometryRow083_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_083 :
    decodeGeometryRow geometryRowsJson083 = .ok geometryRowsTyped083 :=
  original_geometryRow_of_fields geometryRowsJson083 geometryRowsTyped083 geometryRow083_floorText
    geometryRow083_simplexId_read geometryRow083_vertexIds_read
    geometryRow083_physicalVolume_read geometryRow083_meanGap_read
    geometryRow083_factorMaxima_read geometryRow083_gapWeightedMeans_read
    geometryRow083_jensenBound_read geometryRow083_floor_text_read geometryRow083_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_083_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson084 : SourceJson :=
  (SimplicesBlock042.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped084 : GeometryRow :=
  { simplexId := 84,
    vertexIds := #[39, 37, 24, 23, 10, 8, 6, 2, 0],
    physicalVolume := ((12520008294863049579206480426439291460553 : ℚ) / (1188429096960000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((184362598397 : ℚ) / (2074800000000 : ℚ)), ((1305818586899 : ℚ) / (14523600000000 : ℚ)), ((53526155401 : ℚ) / (372400000000 : ℚ)), ((2426609571499 : ℚ) / (21785400000000 : ℚ)), ((269676865093 : ℚ) / (4841200000000 : ℚ)), ((232745097419 : ℚ) / (4841200000000 : ℚ)), ((17908012583 : ℚ) / (458640000000 : ℚ)), ((67119832093 : ℚ) / (1742832000000 : ℚ)), ((314894781707 : ℚ) / (8714160000000 : ℚ)), ((1501110569239 : ℚ) / (43570800000000 : ℚ))],
    jensenBound := ((17403952912091702240247963369976394438661035074563965033896697811189309312221184000000000000000000000 : ℚ) / (453117297245643465360184397108116881897683644613091835968843335765944609296605777397804659587751807494213496033 : ℚ)),
    jensenFloorQ96 := (3043104331023334927 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_simplexId_before"
  err.flush

theorem geometryRow084_simplexId_read :
    geometryRowsJson084.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped084.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_vertexIds_before"
  err.flush

theorem geometryRow084_vertexIds_read :
    geometryRowsJson084.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped084.vertexIds := by decide +kernel

noncomputable def geometryRow084_physicalVolumeNumeratorChars : List Char := ['1', '2', '5', '2', '0', '0', '0', '8', '2', '9', '4', '8', '6', '3', '0', '4', '9', '5', '7', '9', '2', '0', '6', '4', '8', '0', '4', '2', '6', '4', '3', '9', '2', '9', '1', '4', '6', '0', '5', '5', '3']
noncomputable def geometryRow084_physicalVolumeDenominatorChars : List Char := ['1', '1', '8', '8', '4', '2', '9', '0', '9', '6', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow084_physicalVolumeText : String := String.ofList (geometryRow084_physicalVolumeNumeratorChars ++ '/' :: geometryRow084_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_physicalVolume_before_field"
  err.flush

theorem geometryRow084_physicalVolume_field :
    geometryRowsJson084.getObjVal? "physical_volume" = .ok (.str geometryRow084_physicalVolumeText) := by rfl

theorem geometryRow084_physicalVolume_numerator_no_slash :
    geometryRow084_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow084_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow084_physicalVolumeNumeratorChars = some (12520008294863049579206480426439291460553 : Int) := by decide +kernel

theorem geometryRow084_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow084_physicalVolumeDenominatorChars = some (1188429096960000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow084_physicalVolume_denominator_nonzero : (1188429096960000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow084_physicalVolume_parse :
    parseRational geometryRow084_physicalVolumeText = .ok geometryRowsTyped084.physicalVolume :=
  original_rational_fraction_of_chars geometryRow084_physicalVolumeNumeratorChars geometryRow084_physicalVolumeDenominatorChars
    (12520008294863049579206480426439291460553 : Int) (1188429096960000000000000000000000000000000000000000000000000 : Int)
    geometryRow084_physicalVolume_numerator_no_slash geometryRow084_physicalVolume_numerator_parse
    geometryRow084_physicalVolume_denominator_parse geometryRow084_physicalVolume_denominator_nonzero

theorem geometryRow084_physicalVolume_read :
    rationalField geometryRowsJson084 "physical_volume" = .ok geometryRowsTyped084.physicalVolume :=
  original_rationalField_of_string geometryRowsJson084 "physical_volume" geometryRow084_physicalVolumeText
    geometryRowsTyped084.physicalVolume geometryRow084_physicalVolume_field geometryRow084_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_physicalVolume_complete"
  err.flush

noncomputable def geometryRow084_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow084_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow084_meanGapText : String := String.ofList (geometryRow084_meanGapNumeratorChars ++ '/' :: geometryRow084_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_meanGap_before_field"
  err.flush

theorem geometryRow084_meanGap_field :
    geometryRowsJson084.getObjVal? "mean_gap" = .ok (.str geometryRow084_meanGapText) := by rfl

theorem geometryRow084_meanGap_numerator_no_slash :
    geometryRow084_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow084_meanGap_numerator_parse :
    SourceJson.intChars geometryRow084_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow084_meanGap_denominator_parse :
    SourceJson.intChars geometryRow084_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow084_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow084_meanGap_parse :
    parseRational geometryRow084_meanGapText = .ok geometryRowsTyped084.meanGap :=
  original_rational_fraction_of_chars geometryRow084_meanGapNumeratorChars geometryRow084_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow084_meanGap_numerator_no_slash geometryRow084_meanGap_numerator_parse
    geometryRow084_meanGap_denominator_parse geometryRow084_meanGap_denominator_nonzero

theorem geometryRow084_meanGap_read :
    rationalField geometryRowsJson084 "mean_gap" = .ok geometryRowsTyped084.meanGap :=
  original_rationalField_of_string geometryRowsJson084 "mean_gap" geometryRow084_meanGapText
    geometryRowsTyped084.meanGap geometryRow084_meanGap_field geometryRow084_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_meanGap_complete"
  err.flush

noncomputable def geometryRow084_jensenBoundNumeratorChars : List Char := ['1', '7', '4', '0', '3', '9', '5', '2', '9', '1', '2', '0', '9', '1', '7', '0', '2', '2', '4', '0', '2', '4', '7', '9', '6', '3', '3', '6', '9', '9', '7', '6', '3', '9', '4', '4', '3', '8', '6', '6', '1', '0', '3', '5', '0', '7', '4', '5', '6', '3', '9', '6', '5', '0', '3', '3', '8', '9', '6', '6', '9', '7', '8', '1', '1', '1', '8', '9', '3', '0', '9', '3', '1', '2', '2', '2', '1', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow084_jensenBoundDenominatorChars : List Char := ['4', '5', '3', '1', '1', '7', '2', '9', '7', '2', '4', '5', '6', '4', '3', '4', '6', '5', '3', '6', '0', '1', '8', '4', '3', '9', '7', '1', '0', '8', '1', '1', '6', '8', '8', '1', '8', '9', '7', '6', '8', '3', '6', '4', '4', '6', '1', '3', '0', '9', '1', '8', '3', '5', '9', '6', '8', '8', '4', '3', '3', '3', '5', '7', '6', '5', '9', '4', '4', '6', '0', '9', '2', '9', '6', '6', '0', '5', '7', '7', '7', '3', '9', '7', '8', '0', '4', '6', '5', '9', '5', '8', '7', '7', '5', '1', '8', '0', '7', '4', '9', '4', '2', '1', '3', '4', '9', '6', '0', '3', '3']
noncomputable def geometryRow084_jensenBoundText : String := String.ofList (geometryRow084_jensenBoundNumeratorChars ++ '/' :: geometryRow084_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_jensenBound_before_field"
  err.flush

theorem geometryRow084_jensenBound_field :
    geometryRowsJson084.getObjVal? "jensen_bound" = .ok (.str geometryRow084_jensenBoundText) := by rfl

theorem geometryRow084_jensenBound_numerator_no_slash :
    geometryRow084_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow084_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow084_jensenBoundNumeratorChars = some (17403952912091702240247963369976394438661035074563965033896697811189309312221184000000000000000000000 : Int) := by decide +kernel

theorem geometryRow084_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow084_jensenBoundDenominatorChars = some (453117297245643465360184397108116881897683644613091835968843335765944609296605777397804659587751807494213496033 : Int) := by decide +kernel

theorem geometryRow084_jensenBound_denominator_nonzero : (453117297245643465360184397108116881897683644613091835968843335765944609296605777397804659587751807494213496033 : Int) ≠ 0 := by decide +kernel

theorem geometryRow084_jensenBound_parse :
    parseRational geometryRow084_jensenBoundText = .ok geometryRowsTyped084.jensenBound :=
  original_rational_fraction_of_chars geometryRow084_jensenBoundNumeratorChars geometryRow084_jensenBoundDenominatorChars
    (17403952912091702240247963369976394438661035074563965033896697811189309312221184000000000000000000000 : Int) (453117297245643465360184397108116881897683644613091835968843335765944609296605777397804659587751807494213496033 : Int)
    geometryRow084_jensenBound_numerator_no_slash geometryRow084_jensenBound_numerator_parse
    geometryRow084_jensenBound_denominator_parse geometryRow084_jensenBound_denominator_nonzero

theorem geometryRow084_jensenBound_read :
    rationalField geometryRowsJson084 "jensen_bound" = .ok geometryRowsTyped084.jensenBound :=
  original_rationalField_of_string geometryRowsJson084 "jensen_bound" geometryRow084_jensenBoundText
    geometryRowsTyped084.jensenBound geometryRow084_jensenBound_field geometryRow084_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_factorMaxima_before"
  err.flush

theorem geometryRow084_factorMaxima_read :
    rationalArrayField geometryRowsJson084 "factor_maxima" = .ok geometryRowsTyped084.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_gapWeightedMeans_before"
  err.flush

theorem geometryRow084_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson084 "gap_weighted_means" = .ok geometryRowsTyped084.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow084_floorChars : List Char := ['3', '0', '4', '3', '1', '0', '4', '3', '3', '1', '0', '2', '3', '3', '3', '4', '9', '2', '7']
noncomputable def geometryRow084_floorText : String := String.ofList geometryRow084_floorChars

theorem geometryRow084_floor_text_read :
    geometryRowsJson084.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow084_floorText := by rfl

theorem geometryRow084_floor_chars_parse :
    SourceJson.intChars geometryRow084_floorChars = some (3043104331023334927 : Int) := by decide +kernel

theorem geometryRow084_floor_parse :
    parseInteger geometryRow084_floorText = .ok geometryRowsTyped084.jensenFloorQ96 := by
  simp only [geometryRow084_floorText, parseInteger, String.toList_ofList, geometryRow084_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_084 :
    decodeGeometryRow geometryRowsJson084 = .ok geometryRowsTyped084 :=
  original_geometryRow_of_fields geometryRowsJson084 geometryRowsTyped084 geometryRow084_floorText
    geometryRow084_simplexId_read geometryRow084_vertexIds_read
    geometryRow084_physicalVolume_read geometryRow084_meanGap_read
    geometryRow084_factorMaxima_read geometryRow084_gapWeightedMeans_read
    geometryRow084_jensenBound_read geometryRow084_floor_text_read geometryRow084_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_084_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock042 : List SourceJson := [geometryRowsJson083, geometryRowsJson084]
noncomputable def geometryRowsTypedBlock042 : List (GeometryRow) := [geometryRowsTyped083, geometryRowsTyped084]
noncomputable def geometryRowsTypedThroughBlock042 : List (GeometryRow) := geometryRowsTypedThroughBlock041 ++ geometryRowsTypedBlock042

theorem geometry_Rows_block_042_push_eq (acc : List SourceJson) :
    SimplicesBlock042.blockPush acc = [geometryRowsJson084, geometryRowsJson083] ++ acc := by rfl

theorem geometry_Rows_block_042_reverse (acc : List SourceJson) :
    (SimplicesBlock042.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock042 := by
  rw [geometry_Rows_block_042_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_042 :
    geometryRowsJsonBlock042.mapM decodeGeometryRow = .ok geometryRowsTypedBlock042 := by
  simp only [geometryRowsJsonBlock042, geometryRowsTypedBlock042, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_083, decode_geometry_Rows_084]
  rfl

theorem decode_geometry_Rows_through_block_042 :
    SimplicesValue.arrayAcc043.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock042 := by
  change (SimplicesBlock042.blockPush SimplicesValue.arrayAcc042).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_042_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_041, decode_geometry_Rows_block_042]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_042_complete"
  err.flush

#print axioms geometryRow083_simplexId_read
#print axioms geometryRow083_vertexIds_read
#print axioms geometryRow083_physicalVolume_field
#print axioms geometryRow083_physicalVolume_numerator_no_slash
#print axioms geometryRow083_physicalVolume_numerator_parse
#print axioms geometryRow083_physicalVolume_denominator_parse
#print axioms geometryRow083_physicalVolume_denominator_nonzero
#print axioms geometryRow083_physicalVolume_parse
#print axioms geometryRow083_physicalVolume_read
#print axioms geometryRow083_meanGap_field
#print axioms geometryRow083_meanGap_numerator_no_slash
#print axioms geometryRow083_meanGap_numerator_parse
#print axioms geometryRow083_meanGap_denominator_parse
#print axioms geometryRow083_meanGap_denominator_nonzero
#print axioms geometryRow083_meanGap_parse
#print axioms geometryRow083_meanGap_read
#print axioms geometryRow083_jensenBound_field
#print axioms geometryRow083_jensenBound_numerator_no_slash
#print axioms geometryRow083_jensenBound_numerator_parse
#print axioms geometryRow083_jensenBound_denominator_parse
#print axioms geometryRow083_jensenBound_denominator_nonzero
#print axioms geometryRow083_jensenBound_parse
#print axioms geometryRow083_jensenBound_read
#print axioms geometryRow083_factorMaxima_read
#print axioms geometryRow083_gapWeightedMeans_read
#print axioms geometryRow083_floor_text_read
#print axioms geometryRow083_floor_chars_parse
#print axioms geometryRow083_floor_parse
#print axioms decode_geometry_Rows_083
#print axioms geometryRow084_simplexId_read
#print axioms geometryRow084_vertexIds_read
#print axioms geometryRow084_physicalVolume_field
#print axioms geometryRow084_physicalVolume_numerator_no_slash
#print axioms geometryRow084_physicalVolume_numerator_parse
#print axioms geometryRow084_physicalVolume_denominator_parse
#print axioms geometryRow084_physicalVolume_denominator_nonzero
#print axioms geometryRow084_physicalVolume_parse
#print axioms geometryRow084_physicalVolume_read
#print axioms geometryRow084_meanGap_field
#print axioms geometryRow084_meanGap_numerator_no_slash
#print axioms geometryRow084_meanGap_numerator_parse
#print axioms geometryRow084_meanGap_denominator_parse
#print axioms geometryRow084_meanGap_denominator_nonzero
#print axioms geometryRow084_meanGap_parse
#print axioms geometryRow084_meanGap_read
#print axioms geometryRow084_jensenBound_field
#print axioms geometryRow084_jensenBound_numerator_no_slash
#print axioms geometryRow084_jensenBound_numerator_parse
#print axioms geometryRow084_jensenBound_denominator_parse
#print axioms geometryRow084_jensenBound_denominator_nonzero
#print axioms geometryRow084_jensenBound_parse
#print axioms geometryRow084_jensenBound_read
#print axioms geometryRow084_factorMaxima_read
#print axioms geometryRow084_gapWeightedMeans_read
#print axioms geometryRow084_floor_text_read
#print axioms geometryRow084_floor_chars_parse
#print axioms geometryRow084_floor_parse
#print axioms decode_geometry_Rows_084
#print axioms geometry_Rows_block_042_push_eq
#print axioms geometry_Rows_block_042_reverse
#print axioms decode_geometry_Rows_block_042
#print axioms decode_geometry_Rows_through_block_042

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
