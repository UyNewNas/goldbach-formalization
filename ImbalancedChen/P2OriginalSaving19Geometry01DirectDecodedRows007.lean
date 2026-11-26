import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows006

/-! Original simplices typed block 7, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson014 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped014 : GeometryRow :=
  { simplexId := 14,
    vertexIds := #[39, 35, 29, 28, 10, 8, 6, 2, 0],
    physicalVolume := ((4177528882355646616860664079833092577637 : ℚ) / (138726604800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((37611618839 : ℚ) / (436800000000 : ℚ)), ((266498257793 : ℚ) / (3057600000000 : ℚ)), ((10149159431 : ℚ) / (70560000000 : ℚ)), ((350637241543 : ℚ) / (3057600000000 : ℚ)), ((594648197371 : ℚ) / (9172800000000 : ℚ)), ((220016853689 : ℚ) / (4586400000000 : ℚ)), ((1400545620863 : ℚ) / (36691200000000 : ℚ)), ((1324418967533 : ℚ) / (36691200000000 : ℚ)), ((302243816057 : ℚ) / (9172800000000 : ℚ)), ((286798902521 : ℚ) / (9172800000000 : ℚ))],
    jensenBound := ((4203236424927591922585024154737640549031754988397931988438338065417140496551116800000000000000000000000 : ℚ) / (32624983270461264470528178286496408200656856956934744059126943913370340505025417169581404649881637508697945475449 : ℚ)),
    jensenFloorQ96 := (10207352316454701984 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_simplexId_before"
  err.flush

theorem geometryRow014_simplexId_read :
    geometryRowsJson014.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped014.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_vertexIds_before"
  err.flush

theorem geometryRow014_vertexIds_read :
    geometryRowsJson014.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped014.vertexIds := by decide +kernel

noncomputable def geometryRow014_physicalVolumeNumeratorChars : List Char := ['4', '1', '7', '7', '5', '2', '8', '8', '8', '2', '3', '5', '5', '6', '4', '6', '6', '1', '6', '8', '6', '0', '6', '6', '4', '0', '7', '9', '8', '3', '3', '0', '9', '2', '5', '7', '7', '6', '3', '7']
noncomputable def geometryRow014_physicalVolumeDenominatorChars : List Char := ['1', '3', '8', '7', '2', '6', '6', '0', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_physicalVolumeText : String := String.ofList (geometryRow014_physicalVolumeNumeratorChars ++ '/' :: geometryRow014_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_physicalVolume_before_field"
  err.flush

theorem geometryRow014_physicalVolume_field :
    geometryRowsJson014.getObjVal? "physical_volume" = .ok (.str geometryRow014_physicalVolumeText) := by rfl

theorem geometryRow014_physicalVolume_numerator_no_slash :
    geometryRow014_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeNumeratorChars = some (4177528882355646616860664079833092577637 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow014_physicalVolumeDenominatorChars = some (138726604800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_physicalVolume_denominator_nonzero : (138726604800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_physicalVolume_parse :
    parseRational geometryRow014_physicalVolumeText = .ok geometryRowsTyped014.physicalVolume :=
  original_rational_fraction_of_chars geometryRow014_physicalVolumeNumeratorChars geometryRow014_physicalVolumeDenominatorChars
    (4177528882355646616860664079833092577637 : Int) (138726604800000000000000000000000000000000000000000000000000 : Int)
    geometryRow014_physicalVolume_numerator_no_slash geometryRow014_physicalVolume_numerator_parse
    geometryRow014_physicalVolume_denominator_parse geometryRow014_physicalVolume_denominator_nonzero

theorem geometryRow014_physicalVolume_read :
    rationalField geometryRowsJson014 "physical_volume" = .ok geometryRowsTyped014.physicalVolume :=
  original_rationalField_of_string geometryRowsJson014 "physical_volume" geometryRow014_physicalVolumeText
    geometryRowsTyped014.physicalVolume geometryRow014_physicalVolume_field geometryRow014_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_physicalVolume_complete"
  err.flush

noncomputable def geometryRow014_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow014_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_meanGapText : String := String.ofList (geometryRow014_meanGapNumeratorChars ++ '/' :: geometryRow014_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_meanGap_before_field"
  err.flush

theorem geometryRow014_meanGap_field :
    geometryRowsJson014.getObjVal? "mean_gap" = .ok (.str geometryRow014_meanGapText) := by rfl

theorem geometryRow014_meanGap_numerator_no_slash :
    geometryRow014_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_meanGap_numerator_parse :
    SourceJson.intChars geometryRow014_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_parse :
    SourceJson.intChars geometryRow014_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow014_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_meanGap_parse :
    parseRational geometryRow014_meanGapText = .ok geometryRowsTyped014.meanGap :=
  original_rational_fraction_of_chars geometryRow014_meanGapNumeratorChars geometryRow014_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow014_meanGap_numerator_no_slash geometryRow014_meanGap_numerator_parse
    geometryRow014_meanGap_denominator_parse geometryRow014_meanGap_denominator_nonzero

theorem geometryRow014_meanGap_read :
    rationalField geometryRowsJson014 "mean_gap" = .ok geometryRowsTyped014.meanGap :=
  original_rationalField_of_string geometryRowsJson014 "mean_gap" geometryRow014_meanGapText
    geometryRowsTyped014.meanGap geometryRow014_meanGap_field geometryRow014_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_meanGap_complete"
  err.flush

noncomputable def geometryRow014_jensenBoundNumeratorChars : List Char := ['4', '2', '0', '3', '2', '3', '6', '4', '2', '4', '9', '2', '7', '5', '9', '1', '9', '2', '2', '5', '8', '5', '0', '2', '4', '1', '5', '4', '7', '3', '7', '6', '4', '0', '5', '4', '9', '0', '3', '1', '7', '5', '4', '9', '8', '8', '3', '9', '7', '9', '3', '1', '9', '8', '8', '4', '3', '8', '3', '3', '8', '0', '6', '5', '4', '1', '7', '1', '4', '0', '4', '9', '6', '5', '5', '1', '1', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow014_jensenBoundDenominatorChars : List Char := ['3', '2', '6', '2', '4', '9', '8', '3', '2', '7', '0', '4', '6', '1', '2', '6', '4', '4', '7', '0', '5', '2', '8', '1', '7', '8', '2', '8', '6', '4', '9', '6', '4', '0', '8', '2', '0', '0', '6', '5', '6', '8', '5', '6', '9', '5', '6', '9', '3', '4', '7', '4', '4', '0', '5', '9', '1', '2', '6', '9', '4', '3', '9', '1', '3', '3', '7', '0', '3', '4', '0', '5', '0', '5', '0', '2', '5', '4', '1', '7', '1', '6', '9', '5', '8', '1', '4', '0', '4', '6', '4', '9', '8', '8', '1', '6', '3', '7', '5', '0', '8', '6', '9', '7', '9', '4', '5', '4', '7', '5', '4', '4', '9']
noncomputable def geometryRow014_jensenBoundText : String := String.ofList (geometryRow014_jensenBoundNumeratorChars ++ '/' :: geometryRow014_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_jensenBound_before_field"
  err.flush

theorem geometryRow014_jensenBound_field :
    geometryRowsJson014.getObjVal? "jensen_bound" = .ok (.str geometryRow014_jensenBoundText) := by rfl

theorem geometryRow014_jensenBound_numerator_no_slash :
    geometryRow014_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow014_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow014_jensenBoundNumeratorChars = some (4203236424927591922585024154737640549031754988397931988438338065417140496551116800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow014_jensenBoundDenominatorChars = some (32624983270461264470528178286496408200656856956934744059126943913370340505025417169581404649881637508697945475449 : Int) := by decide +kernel

theorem geometryRow014_jensenBound_denominator_nonzero : (32624983270461264470528178286496408200656856956934744059126943913370340505025417169581404649881637508697945475449 : Int) ≠ 0 := by decide +kernel

theorem geometryRow014_jensenBound_parse :
    parseRational geometryRow014_jensenBoundText = .ok geometryRowsTyped014.jensenBound :=
  original_rational_fraction_of_chars geometryRow014_jensenBoundNumeratorChars geometryRow014_jensenBoundDenominatorChars
    (4203236424927591922585024154737640549031754988397931988438338065417140496551116800000000000000000000000 : Int) (32624983270461264470528178286496408200656856956934744059126943913370340505025417169581404649881637508697945475449 : Int)
    geometryRow014_jensenBound_numerator_no_slash geometryRow014_jensenBound_numerator_parse
    geometryRow014_jensenBound_denominator_parse geometryRow014_jensenBound_denominator_nonzero

theorem geometryRow014_jensenBound_read :
    rationalField geometryRowsJson014 "jensen_bound" = .ok geometryRowsTyped014.jensenBound :=
  original_rationalField_of_string geometryRowsJson014 "jensen_bound" geometryRow014_jensenBoundText
    geometryRowsTyped014.jensenBound geometryRow014_jensenBound_field geometryRow014_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_factorMaxima_before"
  err.flush

theorem geometryRow014_factorMaxima_read :
    rationalArrayField geometryRowsJson014 "factor_maxima" = .ok geometryRowsTyped014.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_gapWeightedMeans_before"
  err.flush

theorem geometryRow014_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson014 "gap_weighted_means" = .ok geometryRowsTyped014.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow014_floorChars : List Char := ['1', '0', '2', '0', '7', '3', '5', '2', '3', '1', '6', '4', '5', '4', '7', '0', '1', '9', '8', '4']
noncomputable def geometryRow014_floorText : String := String.ofList geometryRow014_floorChars

theorem geometryRow014_floor_text_read :
    geometryRowsJson014.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow014_floorText := by rfl

theorem geometryRow014_floor_chars_parse :
    SourceJson.intChars geometryRow014_floorChars = some (10207352316454701984 : Int) := by decide +kernel

theorem geometryRow014_floor_parse :
    parseInteger geometryRow014_floorText = .ok geometryRowsTyped014.jensenFloorQ96 := by
  simp only [geometryRow014_floorText, parseInteger, String.toList_ofList, geometryRow014_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_014 :
    decodeGeometryRow geometryRowsJson014 = .ok geometryRowsTyped014 :=
  original_geometryRow_of_fields geometryRowsJson014 geometryRowsTyped014 geometryRow014_floorText
    geometryRow014_simplexId_read geometryRow014_vertexIds_read
    geometryRow014_physicalVolume_read geometryRow014_meanGap_read
    geometryRow014_factorMaxima_read geometryRow014_gapWeightedMeans_read
    geometryRow014_jensenBound_read geometryRow014_floor_text_read geometryRow014_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_014_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson015 : SourceJson :=
  (SimplicesBlock007.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped015 : GeometryRow :=
  { simplexId := 15,
    vertexIds := #[39, 35, 29, 28, 10, 7, 6, 2, 0],
    physicalVolume := ((1149573500178111191230709404818506146595258509 : ℚ) / (23492518163251200000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((341507 : ℚ) / (8000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2848784963 : ℚ) / (33600000000 : ℚ)), ((20188950581 : ℚ) / (235200000000 : ℚ)), ((3383053013 : ℚ) / (23520000000 : ℚ)), ((81227197993 : ℚ) / (705600000000 : ℚ)), ((15195573709 : ℚ) / (235200000000 : ℚ)), ((5719184351 : ℚ) / (117600000000 : ℚ)), ((12005018499 : ℚ) / (313600000000 : ℚ)), ((34063090027 : ℚ) / (940800000000 : ℚ)), ((2661011181 : ℚ) / (78400000000 : ℚ)), ((21750538637 : ℚ) / (705600000000 : ℚ))],
    jensenBound := ((752623302570305973489643008861285367417024652905584014636231937228800000000000000000000000 : ℚ) / (3612068420778385764525755410214423452402499936466258565893549111408926971646795116969831895970007737 : ℚ)),
    jensenFloorQ96 := (16508259086413636744 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_simplexId_before"
  err.flush

theorem geometryRow015_simplexId_read :
    geometryRowsJson015.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped015.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_vertexIds_before"
  err.flush

theorem geometryRow015_vertexIds_read :
    geometryRowsJson015.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped015.vertexIds := by decide +kernel

noncomputable def geometryRow015_physicalVolumeNumeratorChars : List Char := ['1', '1', '4', '9', '5', '7', '3', '5', '0', '0', '1', '7', '8', '1', '1', '1', '1', '9', '1', '2', '3', '0', '7', '0', '9', '4', '0', '4', '8', '1', '8', '5', '0', '6', '1', '4', '6', '5', '9', '5', '2', '5', '8', '5', '0', '9']
noncomputable def geometryRow015_physicalVolumeDenominatorChars : List Char := ['2', '3', '4', '9', '2', '5', '1', '8', '1', '6', '3', '2', '5', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_physicalVolumeText : String := String.ofList (geometryRow015_physicalVolumeNumeratorChars ++ '/' :: geometryRow015_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_physicalVolume_before_field"
  err.flush

theorem geometryRow015_physicalVolume_field :
    geometryRowsJson015.getObjVal? "physical_volume" = .ok (.str geometryRow015_physicalVolumeText) := by rfl

theorem geometryRow015_physicalVolume_numerator_no_slash :
    geometryRow015_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeNumeratorChars = some (1149573500178111191230709404818506146595258509 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow015_physicalVolumeDenominatorChars = some (23492518163251200000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_physicalVolume_denominator_nonzero : (23492518163251200000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_physicalVolume_parse :
    parseRational geometryRow015_physicalVolumeText = .ok geometryRowsTyped015.physicalVolume :=
  original_rational_fraction_of_chars geometryRow015_physicalVolumeNumeratorChars geometryRow015_physicalVolumeDenominatorChars
    (1149573500178111191230709404818506146595258509 : Int) (23492518163251200000000000000000000000000000000000000000000000000 : Int)
    geometryRow015_physicalVolume_numerator_no_slash geometryRow015_physicalVolume_numerator_parse
    geometryRow015_physicalVolume_denominator_parse geometryRow015_physicalVolume_denominator_nonzero

theorem geometryRow015_physicalVolume_read :
    rationalField geometryRowsJson015 "physical_volume" = .ok geometryRowsTyped015.physicalVolume :=
  original_rationalField_of_string geometryRowsJson015 "physical_volume" geometryRow015_physicalVolumeText
    geometryRowsTyped015.physicalVolume geometryRow015_physicalVolume_field geometryRow015_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_physicalVolume_complete"
  err.flush

noncomputable def geometryRow015_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow015_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_meanGapText : String := String.ofList (geometryRow015_meanGapNumeratorChars ++ '/' :: geometryRow015_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_meanGap_before_field"
  err.flush

theorem geometryRow015_meanGap_field :
    geometryRowsJson015.getObjVal? "mean_gap" = .ok (.str geometryRow015_meanGapText) := by rfl

theorem geometryRow015_meanGap_numerator_no_slash :
    geometryRow015_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_meanGap_numerator_parse :
    SourceJson.intChars geometryRow015_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_parse :
    SourceJson.intChars geometryRow015_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow015_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_meanGap_parse :
    parseRational geometryRow015_meanGapText = .ok geometryRowsTyped015.meanGap :=
  original_rational_fraction_of_chars geometryRow015_meanGapNumeratorChars geometryRow015_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow015_meanGap_numerator_no_slash geometryRow015_meanGap_numerator_parse
    geometryRow015_meanGap_denominator_parse geometryRow015_meanGap_denominator_nonzero

theorem geometryRow015_meanGap_read :
    rationalField geometryRowsJson015 "mean_gap" = .ok geometryRowsTyped015.meanGap :=
  original_rationalField_of_string geometryRowsJson015 "mean_gap" geometryRow015_meanGapText
    geometryRowsTyped015.meanGap geometryRow015_meanGap_field geometryRow015_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_meanGap_complete"
  err.flush

noncomputable def geometryRow015_jensenBoundNumeratorChars : List Char := ['7', '5', '2', '6', '2', '3', '3', '0', '2', '5', '7', '0', '3', '0', '5', '9', '7', '3', '4', '8', '9', '6', '4', '3', '0', '0', '8', '8', '6', '1', '2', '8', '5', '3', '6', '7', '4', '1', '7', '0', '2', '4', '6', '5', '2', '9', '0', '5', '5', '8', '4', '0', '1', '4', '6', '3', '6', '2', '3', '1', '9', '3', '7', '2', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow015_jensenBoundDenominatorChars : List Char := ['3', '6', '1', '2', '0', '6', '8', '4', '2', '0', '7', '7', '8', '3', '8', '5', '7', '6', '4', '5', '2', '5', '7', '5', '5', '4', '1', '0', '2', '1', '4', '4', '2', '3', '4', '5', '2', '4', '0', '2', '4', '9', '9', '9', '3', '6', '4', '6', '6', '2', '5', '8', '5', '6', '5', '8', '9', '3', '5', '4', '9', '1', '1', '1', '4', '0', '8', '9', '2', '6', '9', '7', '1', '6', '4', '6', '7', '9', '5', '1', '1', '6', '9', '6', '9', '8', '3', '1', '8', '9', '5', '9', '7', '0', '0', '0', '7', '7', '3', '7']
noncomputable def geometryRow015_jensenBoundText : String := String.ofList (geometryRow015_jensenBoundNumeratorChars ++ '/' :: geometryRow015_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_jensenBound_before_field"
  err.flush

theorem geometryRow015_jensenBound_field :
    geometryRowsJson015.getObjVal? "jensen_bound" = .ok (.str geometryRow015_jensenBoundText) := by rfl

theorem geometryRow015_jensenBound_numerator_no_slash :
    geometryRow015_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow015_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow015_jensenBoundNumeratorChars = some (752623302570305973489643008861285367417024652905584014636231937228800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow015_jensenBoundDenominatorChars = some (3612068420778385764525755410214423452402499936466258565893549111408926971646795116969831895970007737 : Int) := by decide +kernel

theorem geometryRow015_jensenBound_denominator_nonzero : (3612068420778385764525755410214423452402499936466258565893549111408926971646795116969831895970007737 : Int) ≠ 0 := by decide +kernel

theorem geometryRow015_jensenBound_parse :
    parseRational geometryRow015_jensenBoundText = .ok geometryRowsTyped015.jensenBound :=
  original_rational_fraction_of_chars geometryRow015_jensenBoundNumeratorChars geometryRow015_jensenBoundDenominatorChars
    (752623302570305973489643008861285367417024652905584014636231937228800000000000000000000000 : Int) (3612068420778385764525755410214423452402499936466258565893549111408926971646795116969831895970007737 : Int)
    geometryRow015_jensenBound_numerator_no_slash geometryRow015_jensenBound_numerator_parse
    geometryRow015_jensenBound_denominator_parse geometryRow015_jensenBound_denominator_nonzero

theorem geometryRow015_jensenBound_read :
    rationalField geometryRowsJson015 "jensen_bound" = .ok geometryRowsTyped015.jensenBound :=
  original_rationalField_of_string geometryRowsJson015 "jensen_bound" geometryRow015_jensenBoundText
    geometryRowsTyped015.jensenBound geometryRow015_jensenBound_field geometryRow015_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_factorMaxima_before"
  err.flush

theorem geometryRow015_factorMaxima_read :
    rationalArrayField geometryRowsJson015 "factor_maxima" = .ok geometryRowsTyped015.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_gapWeightedMeans_before"
  err.flush

theorem geometryRow015_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson015 "gap_weighted_means" = .ok geometryRowsTyped015.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow015_floorChars : List Char := ['1', '6', '5', '0', '8', '2', '5', '9', '0', '8', '6', '4', '1', '3', '6', '3', '6', '7', '4', '4']
noncomputable def geometryRow015_floorText : String := String.ofList geometryRow015_floorChars

theorem geometryRow015_floor_text_read :
    geometryRowsJson015.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow015_floorText := by rfl

theorem geometryRow015_floor_chars_parse :
    SourceJson.intChars geometryRow015_floorChars = some (16508259086413636744 : Int) := by decide +kernel

theorem geometryRow015_floor_parse :
    parseInteger geometryRow015_floorText = .ok geometryRowsTyped015.jensenFloorQ96 := by
  simp only [geometryRow015_floorText, parseInteger, String.toList_ofList, geometryRow015_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_015 :
    decodeGeometryRow geometryRowsJson015 = .ok geometryRowsTyped015 :=
  original_geometryRow_of_fields geometryRowsJson015 geometryRowsTyped015 geometryRow015_floorText
    geometryRow015_simplexId_read geometryRow015_vertexIds_read
    geometryRow015_physicalVolume_read geometryRow015_meanGap_read
    geometryRow015_factorMaxima_read geometryRow015_gapWeightedMeans_read
    geometryRow015_jensenBound_read geometryRow015_floor_text_read geometryRow015_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_015_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock007 : List SourceJson := [geometryRowsJson014, geometryRowsJson015]
noncomputable def geometryRowsTypedBlock007 : List (GeometryRow) := [geometryRowsTyped014, geometryRowsTyped015]
noncomputable def geometryRowsTypedThroughBlock007 : List (GeometryRow) := geometryRowsTypedThroughBlock006 ++ geometryRowsTypedBlock007

theorem geometry_Rows_block_007_push_eq (acc : List SourceJson) :
    SimplicesBlock007.blockPush acc = [geometryRowsJson015, geometryRowsJson014] ++ acc := by rfl

theorem geometry_Rows_block_007_reverse (acc : List SourceJson) :
    (SimplicesBlock007.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock007 := by
  rw [geometry_Rows_block_007_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_007 :
    geometryRowsJsonBlock007.mapM decodeGeometryRow = .ok geometryRowsTypedBlock007 := by
  simp only [geometryRowsJsonBlock007, geometryRowsTypedBlock007, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_014, decode_geometry_Rows_015]
  rfl

theorem decode_geometry_Rows_through_block_007 :
    SimplicesValue.arrayAcc008.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock007 := by
  change (SimplicesBlock007.blockPush SimplicesValue.arrayAcc007).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_007_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_006, decode_geometry_Rows_block_007]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_007_complete"
  err.flush

#print axioms geometryRow014_simplexId_read
#print axioms geometryRow014_vertexIds_read
#print axioms geometryRow014_physicalVolume_field
#print axioms geometryRow014_physicalVolume_numerator_no_slash
#print axioms geometryRow014_physicalVolume_numerator_parse
#print axioms geometryRow014_physicalVolume_denominator_parse
#print axioms geometryRow014_physicalVolume_denominator_nonzero
#print axioms geometryRow014_physicalVolume_parse
#print axioms geometryRow014_physicalVolume_read
#print axioms geometryRow014_meanGap_field
#print axioms geometryRow014_meanGap_numerator_no_slash
#print axioms geometryRow014_meanGap_numerator_parse
#print axioms geometryRow014_meanGap_denominator_parse
#print axioms geometryRow014_meanGap_denominator_nonzero
#print axioms geometryRow014_meanGap_parse
#print axioms geometryRow014_meanGap_read
#print axioms geometryRow014_jensenBound_field
#print axioms geometryRow014_jensenBound_numerator_no_slash
#print axioms geometryRow014_jensenBound_numerator_parse
#print axioms geometryRow014_jensenBound_denominator_parse
#print axioms geometryRow014_jensenBound_denominator_nonzero
#print axioms geometryRow014_jensenBound_parse
#print axioms geometryRow014_jensenBound_read
#print axioms geometryRow014_factorMaxima_read
#print axioms geometryRow014_gapWeightedMeans_read
#print axioms geometryRow014_floor_text_read
#print axioms geometryRow014_floor_chars_parse
#print axioms geometryRow014_floor_parse
#print axioms decode_geometry_Rows_014
#print axioms geometryRow015_simplexId_read
#print axioms geometryRow015_vertexIds_read
#print axioms geometryRow015_physicalVolume_field
#print axioms geometryRow015_physicalVolume_numerator_no_slash
#print axioms geometryRow015_physicalVolume_numerator_parse
#print axioms geometryRow015_physicalVolume_denominator_parse
#print axioms geometryRow015_physicalVolume_denominator_nonzero
#print axioms geometryRow015_physicalVolume_parse
#print axioms geometryRow015_physicalVolume_read
#print axioms geometryRow015_meanGap_field
#print axioms geometryRow015_meanGap_numerator_no_slash
#print axioms geometryRow015_meanGap_numerator_parse
#print axioms geometryRow015_meanGap_denominator_parse
#print axioms geometryRow015_meanGap_denominator_nonzero
#print axioms geometryRow015_meanGap_parse
#print axioms geometryRow015_meanGap_read
#print axioms geometryRow015_jensenBound_field
#print axioms geometryRow015_jensenBound_numerator_no_slash
#print axioms geometryRow015_jensenBound_numerator_parse
#print axioms geometryRow015_jensenBound_denominator_parse
#print axioms geometryRow015_jensenBound_denominator_nonzero
#print axioms geometryRow015_jensenBound_parse
#print axioms geometryRow015_jensenBound_read
#print axioms geometryRow015_factorMaxima_read
#print axioms geometryRow015_gapWeightedMeans_read
#print axioms geometryRow015_floor_text_read
#print axioms geometryRow015_floor_chars_parse
#print axioms geometryRow015_floor_parse
#print axioms decode_geometry_Rows_015
#print axioms geometry_Rows_block_007_push_eq
#print axioms geometry_Rows_block_007_reverse
#print axioms decode_geometry_Rows_block_007
#print axioms decode_geometry_Rows_through_block_007

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
