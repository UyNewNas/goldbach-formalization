import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows020

/-! Original simplices typed block 21, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson042 : SourceJson :=
  (SimplicesBlock021.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped042 : GeometryRow :=
  { simplexId := 42,
    vertexIds := #[39, 35, 24, 23, 21, 20, 3, 1, 0],
    physicalVolume := ((6245658011789038731731560792489016977529 : ℚ) / (187183601270784000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((66369109 : ℚ) / (99756000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((957 : ℚ) / (20864 : ℚ)), ((957 : ℚ) / (20864 : ℚ))],
    gapWeightedMeans := #[((20320098571830423137 : ℚ) / (254762086491920000000 : ℚ)), ((391115755660773144991 : ℚ) / (4840479643346480000000 : ℚ)), ((6267115407948803906881 : ℚ) / (43564316790118320000000 : ℚ)), ((3895737327794153086993 : ℚ) / (36303597325098600000000 : ℚ)), ((756654343449768723941 : ℚ) / (12813034350034800000000 : ℚ)), ((10726004702490536146831 : ℚ) / (217821583950591600000000 : ℚ)), ((8777879388072162916229 : ℚ) / (217821583950591600000000 : ℚ)), ((8661569731890447152609 : ℚ) / (217821583950591600000000 : ℚ)), ((8414681732103351798887 : ℚ) / (217821583950591600000000 : ℚ)), ((8414638167786561680567 : ℚ) / (217821583950591600000000 : ℚ))],
    jensenBound := ((98915643846237544334945798121139503395773125527293829221934267022551057659371362156597751629259062250770197357496433410194564338882490962990658104530895771646811249032845356313600000000000000000000 : ℚ) / (770709413318582745525614664242771469156531335132568367952715389135964836566431662433544048942213080932672054877751540084475841111061903259380292122438724608342118583449585751635431216678255953290001978019593372299 : ℚ)),
    jensenFloorQ96 := (10168429982070 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_simplexId_before"
  err.flush

theorem geometryRow042_simplexId_read :
    geometryRowsJson042.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped042.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_vertexIds_before"
  err.flush

theorem geometryRow042_vertexIds_read :
    geometryRowsJson042.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped042.vertexIds := by decide +kernel

noncomputable def geometryRow042_physicalVolumeNumeratorChars : List Char := ['6', '2', '4', '5', '6', '5', '8', '0', '1', '1', '7', '8', '9', '0', '3', '8', '7', '3', '1', '7', '3', '1', '5', '6', '0', '7', '9', '2', '4', '8', '9', '0', '1', '6', '9', '7', '7', '5', '2', '9']
noncomputable def geometryRow042_physicalVolumeDenominatorChars : List Char := ['1', '8', '7', '1', '8', '3', '6', '0', '1', '2', '7', '0', '7', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_physicalVolumeText : String := String.ofList (geometryRow042_physicalVolumeNumeratorChars ++ '/' :: geometryRow042_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_physicalVolume_before_field"
  err.flush

theorem geometryRow042_physicalVolume_field :
    geometryRowsJson042.getObjVal? "physical_volume" = .ok (.str geometryRow042_physicalVolumeText) := by rfl

theorem geometryRow042_physicalVolume_numerator_no_slash :
    geometryRow042_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeNumeratorChars = some (6245658011789038731731560792489016977529 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow042_physicalVolumeDenominatorChars = some (187183601270784000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_physicalVolume_denominator_nonzero : (187183601270784000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_physicalVolume_parse :
    parseRational geometryRow042_physicalVolumeText = .ok geometryRowsTyped042.physicalVolume :=
  original_rational_fraction_of_chars geometryRow042_physicalVolumeNumeratorChars geometryRow042_physicalVolumeDenominatorChars
    (6245658011789038731731560792489016977529 : Int) (187183601270784000000000000000000000000000000000000000000000000000 : Int)
    geometryRow042_physicalVolume_numerator_no_slash geometryRow042_physicalVolume_numerator_parse
    geometryRow042_physicalVolume_denominator_parse geometryRow042_physicalVolume_denominator_nonzero

theorem geometryRow042_physicalVolume_read :
    rationalField geometryRowsJson042 "physical_volume" = .ok geometryRowsTyped042.physicalVolume :=
  original_rationalField_of_string geometryRowsJson042 "physical_volume" geometryRow042_physicalVolumeText
    geometryRowsTyped042.physicalVolume geometryRow042_physicalVolume_field geometryRow042_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_physicalVolume_complete"
  err.flush

noncomputable def geometryRow042_meanGapNumeratorChars : List Char := ['6', '6', '3', '6', '9', '1', '0', '9']
noncomputable def geometryRow042_meanGapDenominatorChars : List Char := ['9', '9', '7', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_meanGapText : String := String.ofList (geometryRow042_meanGapNumeratorChars ++ '/' :: geometryRow042_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_meanGap_before_field"
  err.flush

theorem geometryRow042_meanGap_field :
    geometryRowsJson042.getObjVal? "mean_gap" = .ok (.str geometryRow042_meanGapText) := by rfl

theorem geometryRow042_meanGap_numerator_no_slash :
    geometryRow042_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_meanGap_numerator_parse :
    SourceJson.intChars geometryRow042_meanGapNumeratorChars = some (66369109 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_parse :
    SourceJson.intChars geometryRow042_meanGapDenominatorChars = some (99756000000 : Int) := by decide +kernel

theorem geometryRow042_meanGap_denominator_nonzero : (99756000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_meanGap_parse :
    parseRational geometryRow042_meanGapText = .ok geometryRowsTyped042.meanGap :=
  original_rational_fraction_of_chars geometryRow042_meanGapNumeratorChars geometryRow042_meanGapDenominatorChars
    (66369109 : Int) (99756000000 : Int)
    geometryRow042_meanGap_numerator_no_slash geometryRow042_meanGap_numerator_parse
    geometryRow042_meanGap_denominator_parse geometryRow042_meanGap_denominator_nonzero

theorem geometryRow042_meanGap_read :
    rationalField geometryRowsJson042 "mean_gap" = .ok geometryRowsTyped042.meanGap :=
  original_rationalField_of_string geometryRowsJson042 "mean_gap" geometryRow042_meanGapText
    geometryRowsTyped042.meanGap geometryRow042_meanGap_field geometryRow042_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_meanGap_complete"
  err.flush

noncomputable def geometryRow042_jensenBoundNumeratorChars : List Char := ['9', '8', '9', '1', '5', '6', '4', '3', '8', '4', '6', '2', '3', '7', '5', '4', '4', '3', '3', '4', '9', '4', '5', '7', '9', '8', '1', '2', '1', '1', '3', '9', '5', '0', '3', '3', '9', '5', '7', '7', '3', '1', '2', '5', '5', '2', '7', '2', '9', '3', '8', '2', '9', '2', '2', '1', '9', '3', '4', '2', '6', '7', '0', '2', '2', '5', '5', '1', '0', '5', '7', '6', '5', '9', '3', '7', '1', '3', '6', '2', '1', '5', '6', '5', '9', '7', '7', '5', '1', '6', '2', '9', '2', '5', '9', '0', '6', '2', '2', '5', '0', '7', '7', '0', '1', '9', '7', '3', '5', '7', '4', '9', '6', '4', '3', '3', '4', '1', '0', '1', '9', '4', '5', '6', '4', '3', '3', '8', '8', '8', '2', '4', '9', '0', '9', '6', '2', '9', '9', '0', '6', '5', '8', '1', '0', '4', '5', '3', '0', '8', '9', '5', '7', '7', '1', '6', '4', '6', '8', '1', '1', '2', '4', '9', '0', '3', '2', '8', '4', '5', '3', '5', '6', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow042_jensenBoundDenominatorChars : List Char := ['7', '7', '0', '7', '0', '9', '4', '1', '3', '3', '1', '8', '5', '8', '2', '7', '4', '5', '5', '2', '5', '6', '1', '4', '6', '6', '4', '2', '4', '2', '7', '7', '1', '4', '6', '9', '1', '5', '6', '5', '3', '1', '3', '3', '5', '1', '3', '2', '5', '6', '8', '3', '6', '7', '9', '5', '2', '7', '1', '5', '3', '8', '9', '1', '3', '5', '9', '6', '4', '8', '3', '6', '5', '6', '6', '4', '3', '1', '6', '6', '2', '4', '3', '3', '5', '4', '4', '0', '4', '8', '9', '4', '2', '2', '1', '3', '0', '8', '0', '9', '3', '2', '6', '7', '2', '0', '5', '4', '8', '7', '7', '7', '5', '1', '5', '4', '0', '0', '8', '4', '4', '7', '5', '8', '4', '1', '1', '1', '1', '0', '6', '1', '9', '0', '3', '2', '5', '9', '3', '8', '0', '2', '9', '2', '1', '2', '2', '4', '3', '8', '7', '2', '4', '6', '0', '8', '3', '4', '2', '1', '1', '8', '5', '8', '3', '4', '4', '9', '5', '8', '5', '7', '5', '1', '6', '3', '5', '4', '3', '1', '2', '1', '6', '6', '7', '8', '2', '5', '5', '9', '5', '3', '2', '9', '0', '0', '0', '1', '9', '7', '8', '0', '1', '9', '5', '9', '3', '3', '7', '2', '2', '9', '9']
noncomputable def geometryRow042_jensenBoundText : String := String.ofList (geometryRow042_jensenBoundNumeratorChars ++ '/' :: geometryRow042_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_jensenBound_before_field"
  err.flush

theorem geometryRow042_jensenBound_field :
    geometryRowsJson042.getObjVal? "jensen_bound" = .ok (.str geometryRow042_jensenBoundText) := by rfl

theorem geometryRow042_jensenBound_numerator_no_slash :
    geometryRow042_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow042_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow042_jensenBoundNumeratorChars = some (98915643846237544334945798121139503395773125527293829221934267022551057659371362156597751629259062250770197357496433410194564338882490962990658104530895771646811249032845356313600000000000000000000 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow042_jensenBoundDenominatorChars = some (770709413318582745525614664242771469156531335132568367952715389135964836566431662433544048942213080932672054877751540084475841111061903259380292122438724608342118583449585751635431216678255953290001978019593372299 : Int) := by decide +kernel

theorem geometryRow042_jensenBound_denominator_nonzero : (770709413318582745525614664242771469156531335132568367952715389135964836566431662433544048942213080932672054877751540084475841111061903259380292122438724608342118583449585751635431216678255953290001978019593372299 : Int) ≠ 0 := by decide +kernel

theorem geometryRow042_jensenBound_parse :
    parseRational geometryRow042_jensenBoundText = .ok geometryRowsTyped042.jensenBound :=
  original_rational_fraction_of_chars geometryRow042_jensenBoundNumeratorChars geometryRow042_jensenBoundDenominatorChars
    (98915643846237544334945798121139503395773125527293829221934267022551057659371362156597751629259062250770197357496433410194564338882490962990658104530895771646811249032845356313600000000000000000000 : Int) (770709413318582745525614664242771469156531335132568367952715389135964836566431662433544048942213080932672054877751540084475841111061903259380292122438724608342118583449585751635431216678255953290001978019593372299 : Int)
    geometryRow042_jensenBound_numerator_no_slash geometryRow042_jensenBound_numerator_parse
    geometryRow042_jensenBound_denominator_parse geometryRow042_jensenBound_denominator_nonzero

theorem geometryRow042_jensenBound_read :
    rationalField geometryRowsJson042 "jensen_bound" = .ok geometryRowsTyped042.jensenBound :=
  original_rationalField_of_string geometryRowsJson042 "jensen_bound" geometryRow042_jensenBoundText
    geometryRowsTyped042.jensenBound geometryRow042_jensenBound_field geometryRow042_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_factorMaxima_before"
  err.flush

theorem geometryRow042_factorMaxima_read :
    rationalArrayField geometryRowsJson042 "factor_maxima" = .ok geometryRowsTyped042.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_gapWeightedMeans_before"
  err.flush

theorem geometryRow042_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson042 "gap_weighted_means" = .ok geometryRowsTyped042.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow042_floorChars : List Char := ['1', '0', '1', '6', '8', '4', '2', '9', '9', '8', '2', '0', '7', '0']
noncomputable def geometryRow042_floorText : String := String.ofList geometryRow042_floorChars

theorem geometryRow042_floor_text_read :
    geometryRowsJson042.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow042_floorText := by rfl

theorem geometryRow042_floor_chars_parse :
    SourceJson.intChars geometryRow042_floorChars = some (10168429982070 : Int) := by decide +kernel

theorem geometryRow042_floor_parse :
    parseInteger geometryRow042_floorText = .ok geometryRowsTyped042.jensenFloorQ96 := by
  simp only [geometryRow042_floorText, parseInteger, String.toList_ofList, geometryRow042_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_042 :
    decodeGeometryRow geometryRowsJson042 = .ok geometryRowsTyped042 :=
  original_geometryRow_of_fields geometryRowsJson042 geometryRowsTyped042 geometryRow042_floorText
    geometryRow042_simplexId_read geometryRow042_vertexIds_read
    geometryRow042_physicalVolume_read geometryRow042_meanGap_read
    geometryRow042_factorMaxima_read geometryRow042_gapWeightedMeans_read
    geometryRow042_jensenBound_read geometryRow042_floor_text_read geometryRow042_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_042_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock021 : List SourceJson := [geometryRowsJson042]
noncomputable def geometryRowsTypedBlock021 : List (GeometryRow) := [geometryRowsTyped042]
noncomputable def geometryRowsTypedThroughBlock021 : List (GeometryRow) := geometryRowsTypedThroughBlock020 ++ geometryRowsTypedBlock021

theorem geometry_Rows_block_021_push_eq (acc : List SourceJson) :
    SimplicesBlock021.blockPush acc = [geometryRowsJson042] ++ acc := by rfl

theorem geometry_Rows_block_021_reverse (acc : List SourceJson) :
    (SimplicesBlock021.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock021 := by
  rw [geometry_Rows_block_021_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_021 :
    geometryRowsJsonBlock021.mapM decodeGeometryRow = .ok geometryRowsTypedBlock021 := by
  simp only [geometryRowsJsonBlock021, geometryRowsTypedBlock021, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_042]
  rfl

theorem decode_geometry_Rows_through_block_021 :
    SimplicesValue.arrayAcc022.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock021 := by
  change (SimplicesBlock021.blockPush SimplicesValue.arrayAcc021).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_021_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_020, decode_geometry_Rows_block_021]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_021_complete"
  err.flush

#print axioms geometryRow042_simplexId_read
#print axioms geometryRow042_vertexIds_read
#print axioms geometryRow042_physicalVolume_field
#print axioms geometryRow042_physicalVolume_numerator_no_slash
#print axioms geometryRow042_physicalVolume_numerator_parse
#print axioms geometryRow042_physicalVolume_denominator_parse
#print axioms geometryRow042_physicalVolume_denominator_nonzero
#print axioms geometryRow042_physicalVolume_parse
#print axioms geometryRow042_physicalVolume_read
#print axioms geometryRow042_meanGap_field
#print axioms geometryRow042_meanGap_numerator_no_slash
#print axioms geometryRow042_meanGap_numerator_parse
#print axioms geometryRow042_meanGap_denominator_parse
#print axioms geometryRow042_meanGap_denominator_nonzero
#print axioms geometryRow042_meanGap_parse
#print axioms geometryRow042_meanGap_read
#print axioms geometryRow042_jensenBound_field
#print axioms geometryRow042_jensenBound_numerator_no_slash
#print axioms geometryRow042_jensenBound_numerator_parse
#print axioms geometryRow042_jensenBound_denominator_parse
#print axioms geometryRow042_jensenBound_denominator_nonzero
#print axioms geometryRow042_jensenBound_parse
#print axioms geometryRow042_jensenBound_read
#print axioms geometryRow042_factorMaxima_read
#print axioms geometryRow042_gapWeightedMeans_read
#print axioms geometryRow042_floor_text_read
#print axioms geometryRow042_floor_chars_parse
#print axioms geometryRow042_floor_parse
#print axioms decode_geometry_Rows_042
#print axioms geometry_Rows_block_021_push_eq
#print axioms geometry_Rows_block_021_reverse
#print axioms decode_geometry_Rows_block_021
#print axioms decode_geometry_Rows_through_block_021

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
