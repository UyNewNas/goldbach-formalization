import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows039

/-! Original simplices typed block 40, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson079 : SourceJson :=
  (SimplicesBlock040.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped079 : GeometryRow :=
  { simplexId := 79,
    vertexIds := #[39, 37, 24, 11, 10, 8, 6, 2, 0],
    physicalVolume := ((3434799383696902005883599323855615237 : ℚ) / (70917120000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((31557422787 : ℚ) / (345800000000 : ℚ)), ((223448692529 : ℚ) / (2420600000000 : ℚ)), ((20005243721 : ℚ) / (139650000000 : ℚ)), ((152970857029 : ℚ) / (1361587500000 : ℚ)), ((408002654467 : ℚ) / (7261800000000 : ℚ)), ((88151250739 : ℚ) / (1815450000000 : ℚ)), ((21672725411 : ℚ) / (544635000000 : ℚ)), ((16035906829 : ℚ) / (435708000000 : ℚ)), ((37792537141 : ℚ) / (1089270000000 : ℚ)), ((179792268293 : ℚ) / (5446350000000 : ℚ))],
    jensenBound := ((3844892223274759056601390627878924314574703717657424208050060142959742583120567382812500000000000 : ℚ) / (21066297854794730442034929558287477877064761882051648909131214985475057113151409281701397516889137339976871 : ℚ)),
    jensenFloorQ96 := (14460241092912809794 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_simplexId_before"
  err.flush

theorem geometryRow079_simplexId_read :
    geometryRowsJson079.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped079.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_vertexIds_before"
  err.flush

theorem geometryRow079_vertexIds_read :
    geometryRowsJson079.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped079.vertexIds := by decide +kernel

noncomputable def geometryRow079_physicalVolumeNumeratorChars : List Char := ['3', '4', '3', '4', '7', '9', '9', '3', '8', '3', '6', '9', '6', '9', '0', '2', '0', '0', '5', '8', '8', '3', '5', '9', '9', '3', '2', '3', '8', '5', '5', '6', '1', '5', '2', '3', '7']
noncomputable def geometryRow079_physicalVolumeDenominatorChars : List Char := ['7', '0', '9', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow079_physicalVolumeText : String := String.ofList (geometryRow079_physicalVolumeNumeratorChars ++ '/' :: geometryRow079_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_physicalVolume_before_field"
  err.flush

theorem geometryRow079_physicalVolume_field :
    geometryRowsJson079.getObjVal? "physical_volume" = .ok (.str geometryRow079_physicalVolumeText) := by rfl

theorem geometryRow079_physicalVolume_numerator_no_slash :
    geometryRow079_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow079_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow079_physicalVolumeNumeratorChars = some (3434799383696902005883599323855615237 : Int) := by decide +kernel

theorem geometryRow079_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow079_physicalVolumeDenominatorChars = some (70917120000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow079_physicalVolume_denominator_nonzero : (70917120000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow079_physicalVolume_parse :
    parseRational geometryRow079_physicalVolumeText = .ok geometryRowsTyped079.physicalVolume :=
  original_rational_fraction_of_chars geometryRow079_physicalVolumeNumeratorChars geometryRow079_physicalVolumeDenominatorChars
    (3434799383696902005883599323855615237 : Int) (70917120000000000000000000000000000000000000000000000000 : Int)
    geometryRow079_physicalVolume_numerator_no_slash geometryRow079_physicalVolume_numerator_parse
    geometryRow079_physicalVolume_denominator_parse geometryRow079_physicalVolume_denominator_nonzero

theorem geometryRow079_physicalVolume_read :
    rationalField geometryRowsJson079 "physical_volume" = .ok geometryRowsTyped079.physicalVolume :=
  original_rationalField_of_string geometryRowsJson079 "physical_volume" geometryRow079_physicalVolumeText
    geometryRowsTyped079.physicalVolume geometryRow079_physicalVolume_field geometryRow079_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_physicalVolume_complete"
  err.flush

noncomputable def geometryRow079_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow079_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow079_meanGapText : String := String.ofList (geometryRow079_meanGapNumeratorChars ++ '/' :: geometryRow079_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_meanGap_before_field"
  err.flush

theorem geometryRow079_meanGap_field :
    geometryRowsJson079.getObjVal? "mean_gap" = .ok (.str geometryRow079_meanGapText) := by rfl

theorem geometryRow079_meanGap_numerator_no_slash :
    geometryRow079_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow079_meanGap_numerator_parse :
    SourceJson.intChars geometryRow079_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow079_meanGap_denominator_parse :
    SourceJson.intChars geometryRow079_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow079_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow079_meanGap_parse :
    parseRational geometryRow079_meanGapText = .ok geometryRowsTyped079.meanGap :=
  original_rational_fraction_of_chars geometryRow079_meanGapNumeratorChars geometryRow079_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow079_meanGap_numerator_no_slash geometryRow079_meanGap_numerator_parse
    geometryRow079_meanGap_denominator_parse geometryRow079_meanGap_denominator_nonzero

theorem geometryRow079_meanGap_read :
    rationalField geometryRowsJson079 "mean_gap" = .ok geometryRowsTyped079.meanGap :=
  original_rationalField_of_string geometryRowsJson079 "mean_gap" geometryRow079_meanGapText
    geometryRowsTyped079.meanGap geometryRow079_meanGap_field geometryRow079_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_meanGap_complete"
  err.flush

noncomputable def geometryRow079_jensenBoundNumeratorChars : List Char := ['3', '8', '4', '4', '8', '9', '2', '2', '2', '3', '2', '7', '4', '7', '5', '9', '0', '5', '6', '6', '0', '1', '3', '9', '0', '6', '2', '7', '8', '7', '8', '9', '2', '4', '3', '1', '4', '5', '7', '4', '7', '0', '3', '7', '1', '7', '6', '5', '7', '4', '2', '4', '2', '0', '8', '0', '5', '0', '0', '6', '0', '1', '4', '2', '9', '5', '9', '7', '4', '2', '5', '8', '3', '1', '2', '0', '5', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow079_jensenBoundDenominatorChars : List Char := ['2', '1', '0', '6', '6', '2', '9', '7', '8', '5', '4', '7', '9', '4', '7', '3', '0', '4', '4', '2', '0', '3', '4', '9', '2', '9', '5', '5', '8', '2', '8', '7', '4', '7', '7', '8', '7', '7', '0', '6', '4', '7', '6', '1', '8', '8', '2', '0', '5', '1', '6', '4', '8', '9', '0', '9', '1', '3', '1', '2', '1', '4', '9', '8', '5', '4', '7', '5', '0', '5', '7', '1', '1', '3', '1', '5', '1', '4', '0', '9', '2', '8', '1', '7', '0', '1', '3', '9', '7', '5', '1', '6', '8', '8', '9', '1', '3', '7', '3', '3', '9', '9', '7', '6', '8', '7', '1']
noncomputable def geometryRow079_jensenBoundText : String := String.ofList (geometryRow079_jensenBoundNumeratorChars ++ '/' :: geometryRow079_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_jensenBound_before_field"
  err.flush

theorem geometryRow079_jensenBound_field :
    geometryRowsJson079.getObjVal? "jensen_bound" = .ok (.str geometryRow079_jensenBoundText) := by rfl

theorem geometryRow079_jensenBound_numerator_no_slash :
    geometryRow079_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow079_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow079_jensenBoundNumeratorChars = some (3844892223274759056601390627878924314574703717657424208050060142959742583120567382812500000000000 : Int) := by decide +kernel

theorem geometryRow079_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow079_jensenBoundDenominatorChars = some (21066297854794730442034929558287477877064761882051648909131214985475057113151409281701397516889137339976871 : Int) := by decide +kernel

theorem geometryRow079_jensenBound_denominator_nonzero : (21066297854794730442034929558287477877064761882051648909131214985475057113151409281701397516889137339976871 : Int) ≠ 0 := by decide +kernel

theorem geometryRow079_jensenBound_parse :
    parseRational geometryRow079_jensenBoundText = .ok geometryRowsTyped079.jensenBound :=
  original_rational_fraction_of_chars geometryRow079_jensenBoundNumeratorChars geometryRow079_jensenBoundDenominatorChars
    (3844892223274759056601390627878924314574703717657424208050060142959742583120567382812500000000000 : Int) (21066297854794730442034929558287477877064761882051648909131214985475057113151409281701397516889137339976871 : Int)
    geometryRow079_jensenBound_numerator_no_slash geometryRow079_jensenBound_numerator_parse
    geometryRow079_jensenBound_denominator_parse geometryRow079_jensenBound_denominator_nonzero

theorem geometryRow079_jensenBound_read :
    rationalField geometryRowsJson079 "jensen_bound" = .ok geometryRowsTyped079.jensenBound :=
  original_rationalField_of_string geometryRowsJson079 "jensen_bound" geometryRow079_jensenBoundText
    geometryRowsTyped079.jensenBound geometryRow079_jensenBound_field geometryRow079_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_factorMaxima_before"
  err.flush

theorem geometryRow079_factorMaxima_read :
    rationalArrayField geometryRowsJson079 "factor_maxima" = .ok geometryRowsTyped079.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_gapWeightedMeans_before"
  err.flush

theorem geometryRow079_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson079 "gap_weighted_means" = .ok geometryRowsTyped079.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow079_floorChars : List Char := ['1', '4', '4', '6', '0', '2', '4', '1', '0', '9', '2', '9', '1', '2', '8', '0', '9', '7', '9', '4']
noncomputable def geometryRow079_floorText : String := String.ofList geometryRow079_floorChars

theorem geometryRow079_floor_text_read :
    geometryRowsJson079.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow079_floorText := by rfl

theorem geometryRow079_floor_chars_parse :
    SourceJson.intChars geometryRow079_floorChars = some (14460241092912809794 : Int) := by decide +kernel

theorem geometryRow079_floor_parse :
    parseInteger geometryRow079_floorText = .ok geometryRowsTyped079.jensenFloorQ96 := by
  simp only [geometryRow079_floorText, parseInteger, String.toList_ofList, geometryRow079_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_079 :
    decodeGeometryRow geometryRowsJson079 = .ok geometryRowsTyped079 :=
  original_geometryRow_of_fields geometryRowsJson079 geometryRowsTyped079 geometryRow079_floorText
    geometryRow079_simplexId_read geometryRow079_vertexIds_read
    geometryRow079_physicalVolume_read geometryRow079_meanGap_read
    geometryRow079_factorMaxima_read geometryRow079_gapWeightedMeans_read
    geometryRow079_jensenBound_read geometryRow079_floor_text_read geometryRow079_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_079_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson080 : SourceJson :=
  (SimplicesBlock040.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped080 : GeometryRow :=
  { simplexId := 80,
    vertexIds := #[39, 37, 24, 11, 10, 7, 6, 2, 0],
    physicalVolume := ((945189000751931490181389840247875055761709 : ℚ) / (12009388769280000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((24984443 : ℚ) / (392000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((439703 : ℚ) / (8000000 : ℚ)), ((1703193 : ℚ) / (38000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ)), ((5109503 : ℚ) / (114000000 : ℚ))],
    gapWeightedMeans := #[((2392331009 : ℚ) / (26600000000 : ℚ)), ((16942219603 : ℚ) / (186200000000 : ℚ)), ((120031457671 : ℚ) / (837900000000 : ℚ)), ((7875426617 : ℚ) / (69825000000 : ℚ)), ((93785269957 : ℚ) / (1675800000000 : ℚ)), ((20619497209 : ℚ) / (418950000000 : ℚ)), ((13373979737 : ℚ) / (335160000000 : ℚ)), ((12372230891 : ℚ) / (335160000000 : ℚ)), ((11960771717 : ℚ) / (335160000000 : ℚ)), ((27291136927 : ℚ) / (837900000000 : ℚ))],
    jensenBound := ((7071747163421645878961975302158857053365816069684786911009031121327073964843750000000000000 : ℚ) / (23963292313761892260202001780391537887526068636106792471087419468934059477092012602076552495567169263 : ℚ)),
    jensenFloorQ96 := (23380824562307476258 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_simplexId_before"
  err.flush

theorem geometryRow080_simplexId_read :
    geometryRowsJson080.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped080.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_vertexIds_before"
  err.flush

theorem geometryRow080_vertexIds_read :
    geometryRowsJson080.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped080.vertexIds := by decide +kernel

noncomputable def geometryRow080_physicalVolumeNumeratorChars : List Char := ['9', '4', '5', '1', '8', '9', '0', '0', '0', '7', '5', '1', '9', '3', '1', '4', '9', '0', '1', '8', '1', '3', '8', '9', '8', '4', '0', '2', '4', '7', '8', '7', '5', '0', '5', '5', '7', '6', '1', '7', '0', '9']
noncomputable def geometryRow080_physicalVolumeDenominatorChars : List Char := ['1', '2', '0', '0', '9', '3', '8', '8', '7', '6', '9', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow080_physicalVolumeText : String := String.ofList (geometryRow080_physicalVolumeNumeratorChars ++ '/' :: geometryRow080_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_physicalVolume_before_field"
  err.flush

theorem geometryRow080_physicalVolume_field :
    geometryRowsJson080.getObjVal? "physical_volume" = .ok (.str geometryRow080_physicalVolumeText) := by rfl

theorem geometryRow080_physicalVolume_numerator_no_slash :
    geometryRow080_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow080_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow080_physicalVolumeNumeratorChars = some (945189000751931490181389840247875055761709 : Int) := by decide +kernel

theorem geometryRow080_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow080_physicalVolumeDenominatorChars = some (12009388769280000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow080_physicalVolume_denominator_nonzero : (12009388769280000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow080_physicalVolume_parse :
    parseRational geometryRow080_physicalVolumeText = .ok geometryRowsTyped080.physicalVolume :=
  original_rational_fraction_of_chars geometryRow080_physicalVolumeNumeratorChars geometryRow080_physicalVolumeDenominatorChars
    (945189000751931490181389840247875055761709 : Int) (12009388769280000000000000000000000000000000000000000000000000 : Int)
    geometryRow080_physicalVolume_numerator_no_slash geometryRow080_physicalVolume_numerator_parse
    geometryRow080_physicalVolume_denominator_parse geometryRow080_physicalVolume_denominator_nonzero

theorem geometryRow080_physicalVolume_read :
    rationalField geometryRowsJson080 "physical_volume" = .ok geometryRowsTyped080.physicalVolume :=
  original_rationalField_of_string geometryRowsJson080 "physical_volume" geometryRow080_physicalVolumeText
    geometryRowsTyped080.physicalVolume geometryRow080_physicalVolume_field geometryRow080_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_physicalVolume_complete"
  err.flush

noncomputable def geometryRow080_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow080_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow080_meanGapText : String := String.ofList (geometryRow080_meanGapNumeratorChars ++ '/' :: geometryRow080_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_meanGap_before_field"
  err.flush

theorem geometryRow080_meanGap_field :
    geometryRowsJson080.getObjVal? "mean_gap" = .ok (.str geometryRow080_meanGapText) := by rfl

theorem geometryRow080_meanGap_numerator_no_slash :
    geometryRow080_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow080_meanGap_numerator_parse :
    SourceJson.intChars geometryRow080_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow080_meanGap_denominator_parse :
    SourceJson.intChars geometryRow080_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow080_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow080_meanGap_parse :
    parseRational geometryRow080_meanGapText = .ok geometryRowsTyped080.meanGap :=
  original_rational_fraction_of_chars geometryRow080_meanGapNumeratorChars geometryRow080_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow080_meanGap_numerator_no_slash geometryRow080_meanGap_numerator_parse
    geometryRow080_meanGap_denominator_parse geometryRow080_meanGap_denominator_nonzero

theorem geometryRow080_meanGap_read :
    rationalField geometryRowsJson080 "mean_gap" = .ok geometryRowsTyped080.meanGap :=
  original_rationalField_of_string geometryRowsJson080 "mean_gap" geometryRow080_meanGapText
    geometryRowsTyped080.meanGap geometryRow080_meanGap_field geometryRow080_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_meanGap_complete"
  err.flush

noncomputable def geometryRow080_jensenBoundNumeratorChars : List Char := ['7', '0', '7', '1', '7', '4', '7', '1', '6', '3', '4', '2', '1', '6', '4', '5', '8', '7', '8', '9', '6', '1', '9', '7', '5', '3', '0', '2', '1', '5', '8', '8', '5', '7', '0', '5', '3', '3', '6', '5', '8', '1', '6', '0', '6', '9', '6', '8', '4', '7', '8', '6', '9', '1', '1', '0', '0', '9', '0', '3', '1', '1', '2', '1', '3', '2', '7', '0', '7', '3', '9', '6', '4', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow080_jensenBoundDenominatorChars : List Char := ['2', '3', '9', '6', '3', '2', '9', '2', '3', '1', '3', '7', '6', '1', '8', '9', '2', '2', '6', '0', '2', '0', '2', '0', '0', '1', '7', '8', '0', '3', '9', '1', '5', '3', '7', '8', '8', '7', '5', '2', '6', '0', '6', '8', '6', '3', '6', '1', '0', '6', '7', '9', '2', '4', '7', '1', '0', '8', '7', '4', '1', '9', '4', '6', '8', '9', '3', '4', '0', '5', '9', '4', '7', '7', '0', '9', '2', '0', '1', '2', '6', '0', '2', '0', '7', '6', '5', '5', '2', '4', '9', '5', '5', '6', '7', '1', '6', '9', '2', '6', '3']
noncomputable def geometryRow080_jensenBoundText : String := String.ofList (geometryRow080_jensenBoundNumeratorChars ++ '/' :: geometryRow080_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_jensenBound_before_field"
  err.flush

theorem geometryRow080_jensenBound_field :
    geometryRowsJson080.getObjVal? "jensen_bound" = .ok (.str geometryRow080_jensenBoundText) := by rfl

theorem geometryRow080_jensenBound_numerator_no_slash :
    geometryRow080_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow080_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow080_jensenBoundNumeratorChars = some (7071747163421645878961975302158857053365816069684786911009031121327073964843750000000000000 : Int) := by decide +kernel

theorem geometryRow080_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow080_jensenBoundDenominatorChars = some (23963292313761892260202001780391537887526068636106792471087419468934059477092012602076552495567169263 : Int) := by decide +kernel

theorem geometryRow080_jensenBound_denominator_nonzero : (23963292313761892260202001780391537887526068636106792471087419468934059477092012602076552495567169263 : Int) ≠ 0 := by decide +kernel

theorem geometryRow080_jensenBound_parse :
    parseRational geometryRow080_jensenBoundText = .ok geometryRowsTyped080.jensenBound :=
  original_rational_fraction_of_chars geometryRow080_jensenBoundNumeratorChars geometryRow080_jensenBoundDenominatorChars
    (7071747163421645878961975302158857053365816069684786911009031121327073964843750000000000000 : Int) (23963292313761892260202001780391537887526068636106792471087419468934059477092012602076552495567169263 : Int)
    geometryRow080_jensenBound_numerator_no_slash geometryRow080_jensenBound_numerator_parse
    geometryRow080_jensenBound_denominator_parse geometryRow080_jensenBound_denominator_nonzero

theorem geometryRow080_jensenBound_read :
    rationalField geometryRowsJson080 "jensen_bound" = .ok geometryRowsTyped080.jensenBound :=
  original_rationalField_of_string geometryRowsJson080 "jensen_bound" geometryRow080_jensenBoundText
    geometryRowsTyped080.jensenBound geometryRow080_jensenBound_field geometryRow080_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_factorMaxima_before"
  err.flush

theorem geometryRow080_factorMaxima_read :
    rationalArrayField geometryRowsJson080 "factor_maxima" = .ok geometryRowsTyped080.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_gapWeightedMeans_before"
  err.flush

theorem geometryRow080_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson080 "gap_weighted_means" = .ok geometryRowsTyped080.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow080_floorChars : List Char := ['2', '3', '3', '8', '0', '8', '2', '4', '5', '6', '2', '3', '0', '7', '4', '7', '6', '2', '5', '8']
noncomputable def geometryRow080_floorText : String := String.ofList geometryRow080_floorChars

theorem geometryRow080_floor_text_read :
    geometryRowsJson080.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow080_floorText := by rfl

theorem geometryRow080_floor_chars_parse :
    SourceJson.intChars geometryRow080_floorChars = some (23380824562307476258 : Int) := by decide +kernel

theorem geometryRow080_floor_parse :
    parseInteger geometryRow080_floorText = .ok geometryRowsTyped080.jensenFloorQ96 := by
  simp only [geometryRow080_floorText, parseInteger, String.toList_ofList, geometryRow080_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_080 :
    decodeGeometryRow geometryRowsJson080 = .ok geometryRowsTyped080 :=
  original_geometryRow_of_fields geometryRowsJson080 geometryRowsTyped080 geometryRow080_floorText
    geometryRow080_simplexId_read geometryRow080_vertexIds_read
    geometryRow080_physicalVolume_read geometryRow080_meanGap_read
    geometryRow080_factorMaxima_read geometryRow080_gapWeightedMeans_read
    geometryRow080_jensenBound_read geometryRow080_floor_text_read geometryRow080_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_080_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock040 : List SourceJson := [geometryRowsJson079, geometryRowsJson080]
noncomputable def geometryRowsTypedBlock040 : List (GeometryRow) := [geometryRowsTyped079, geometryRowsTyped080]
noncomputable def geometryRowsTypedThroughBlock040 : List (GeometryRow) := geometryRowsTypedThroughBlock039 ++ geometryRowsTypedBlock040

theorem geometry_Rows_block_040_push_eq (acc : List SourceJson) :
    SimplicesBlock040.blockPush acc = [geometryRowsJson080, geometryRowsJson079] ++ acc := by rfl

theorem geometry_Rows_block_040_reverse (acc : List SourceJson) :
    (SimplicesBlock040.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock040 := by
  rw [geometry_Rows_block_040_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_040 :
    geometryRowsJsonBlock040.mapM decodeGeometryRow = .ok geometryRowsTypedBlock040 := by
  simp only [geometryRowsJsonBlock040, geometryRowsTypedBlock040, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_079, decode_geometry_Rows_080]
  rfl

theorem decode_geometry_Rows_through_block_040 :
    SimplicesValue.arrayAcc041.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock040 := by
  change (SimplicesBlock040.blockPush SimplicesValue.arrayAcc040).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_040_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_039, decode_geometry_Rows_block_040]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_040_complete"
  err.flush

#print axioms geometryRow079_simplexId_read
#print axioms geometryRow079_vertexIds_read
#print axioms geometryRow079_physicalVolume_field
#print axioms geometryRow079_physicalVolume_numerator_no_slash
#print axioms geometryRow079_physicalVolume_numerator_parse
#print axioms geometryRow079_physicalVolume_denominator_parse
#print axioms geometryRow079_physicalVolume_denominator_nonzero
#print axioms geometryRow079_physicalVolume_parse
#print axioms geometryRow079_physicalVolume_read
#print axioms geometryRow079_meanGap_field
#print axioms geometryRow079_meanGap_numerator_no_slash
#print axioms geometryRow079_meanGap_numerator_parse
#print axioms geometryRow079_meanGap_denominator_parse
#print axioms geometryRow079_meanGap_denominator_nonzero
#print axioms geometryRow079_meanGap_parse
#print axioms geometryRow079_meanGap_read
#print axioms geometryRow079_jensenBound_field
#print axioms geometryRow079_jensenBound_numerator_no_slash
#print axioms geometryRow079_jensenBound_numerator_parse
#print axioms geometryRow079_jensenBound_denominator_parse
#print axioms geometryRow079_jensenBound_denominator_nonzero
#print axioms geometryRow079_jensenBound_parse
#print axioms geometryRow079_jensenBound_read
#print axioms geometryRow079_factorMaxima_read
#print axioms geometryRow079_gapWeightedMeans_read
#print axioms geometryRow079_floor_text_read
#print axioms geometryRow079_floor_chars_parse
#print axioms geometryRow079_floor_parse
#print axioms decode_geometry_Rows_079
#print axioms geometryRow080_simplexId_read
#print axioms geometryRow080_vertexIds_read
#print axioms geometryRow080_physicalVolume_field
#print axioms geometryRow080_physicalVolume_numerator_no_slash
#print axioms geometryRow080_physicalVolume_numerator_parse
#print axioms geometryRow080_physicalVolume_denominator_parse
#print axioms geometryRow080_physicalVolume_denominator_nonzero
#print axioms geometryRow080_physicalVolume_parse
#print axioms geometryRow080_physicalVolume_read
#print axioms geometryRow080_meanGap_field
#print axioms geometryRow080_meanGap_numerator_no_slash
#print axioms geometryRow080_meanGap_numerator_parse
#print axioms geometryRow080_meanGap_denominator_parse
#print axioms geometryRow080_meanGap_denominator_nonzero
#print axioms geometryRow080_meanGap_parse
#print axioms geometryRow080_meanGap_read
#print axioms geometryRow080_jensenBound_field
#print axioms geometryRow080_jensenBound_numerator_no_slash
#print axioms geometryRow080_jensenBound_numerator_parse
#print axioms geometryRow080_jensenBound_denominator_parse
#print axioms geometryRow080_jensenBound_denominator_nonzero
#print axioms geometryRow080_jensenBound_parse
#print axioms geometryRow080_jensenBound_read
#print axioms geometryRow080_factorMaxima_read
#print axioms geometryRow080_gapWeightedMeans_read
#print axioms geometryRow080_floor_text_read
#print axioms geometryRow080_floor_chars_parse
#print axioms geometryRow080_floor_parse
#print axioms decode_geometry_Rows_080
#print axioms geometry_Rows_block_040_push_eq
#print axioms geometry_Rows_block_040_reverse
#print axioms decode_geometry_Rows_block_040
#print axioms decode_geometry_Rows_through_block_040

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
