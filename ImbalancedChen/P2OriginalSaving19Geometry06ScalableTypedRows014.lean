import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock014

/-! Local typed certificates for original cell 06, rows 112 through 112.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry06ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson112 : SourceJson :=
  (SimplicesBlock014.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped112 : GeometryRow :=
  { simplexId := 112,
    vertexIds := #[32, 31, 19, 17, 16, 14, 12, 11, 7],
    physicalVolume := ((42962980972133876286253732258374037343 : ℚ) / (530141151232000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((3386761197779 : ℚ) / (37144800000000 : ℚ)), ((3432922644719 : ℚ) / (37144800000000 : ℚ)), ((4347611799733 : ℚ) / (37144800000000 : ℚ)), ((267522077917 : ℚ) / (3095400000000 : ℚ)), ((1061625379729 : ℚ) / (12381600000000 : ℚ)), ((2799677276747 : ℚ) / (37144800000000 : ℚ)), ((50533964887 : ℚ) / (1326600000000 : ℚ)), ((167801450027 : ℚ) / (4643100000000 : ℚ)), ((1229746524529 : ℚ) / (37144800000000 : ℚ)), ((1229744048209 : ℚ) / (37144800000000 : ℚ))],
    jensenBound := ((1524965776254239545354952802984054898179462787258229014177104606552811157026326600000000000000000000000 : ℚ) / (5663778623118704220525366200220361491726722532671484752897966882387745890335166706549078979857604440657942669348393097 : ℚ)),
    jensenFloorQ96 := (21332090180324 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_simplexId_before"
  err.flush

theorem geometryRow112_simplexId_read :
    geometryRowsJson112.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped112.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_vertexIds_before"
  err.flush

theorem geometryRow112_vertexIds_read :
    geometryRowsJson112.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped112.vertexIds := by decide +kernel

noncomputable def geometryRow112_physicalVolumeNumeratorChars : List Char := ['4', '2', '9', '6', '2', '9', '8', '0', '9', '7', '2', '1', '3', '3', '8', '7', '6', '2', '8', '6', '2', '5', '3', '7', '3', '2', '2', '5', '8', '3', '7', '4', '0', '3', '7', '3', '4', '3']
noncomputable def geometryRow112_physicalVolumeDenominatorChars : List Char := ['5', '3', '0', '1', '4', '1', '1', '5', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow112_physicalVolumeText : String := String.ofList (geometryRow112_physicalVolumeNumeratorChars ++ '/' :: geometryRow112_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_physicalVolume_before_field"
  err.flush

theorem geometryRow112_physicalVolume_field :
    geometryRowsJson112.getObjVal? "physical_volume" = .ok (.str geometryRow112_physicalVolumeText) := by rfl

theorem geometryRow112_physicalVolume_numerator_no_slash :
    geometryRow112_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow112_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow112_physicalVolumeNumeratorChars = some (42962980972133876286253732258374037343 : Int) := by decide +kernel

theorem geometryRow112_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow112_physicalVolumeDenominatorChars = some (530141151232000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow112_physicalVolume_denominator_nonzero : (530141151232000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow112_physicalVolume_parse :
    parseRational geometryRow112_physicalVolumeText = .ok geometryRowsTyped112.physicalVolume :=
  original_rational_fraction_of_chars geometryRow112_physicalVolumeNumeratorChars geometryRow112_physicalVolumeDenominatorChars
    (42962980972133876286253732258374037343 : Int) (530141151232000000000000000000000000000000000000000000000000000 : Int)
    geometryRow112_physicalVolume_numerator_no_slash geometryRow112_physicalVolume_numerator_parse
    geometryRow112_physicalVolume_denominator_parse geometryRow112_physicalVolume_denominator_nonzero

theorem geometryRow112_physicalVolume_read :
    rationalField geometryRowsJson112 "physical_volume" = .ok geometryRowsTyped112.physicalVolume :=
  original_rationalField_of_string geometryRowsJson112 "physical_volume" geometryRow112_physicalVolumeText
    geometryRowsTyped112.physicalVolume geometryRow112_physicalVolume_field geometryRow112_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_physicalVolume_complete"
  err.flush

noncomputable def geometryRow112_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow112_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow112_meanGapText : String := String.ofList (geometryRow112_meanGapNumeratorChars ++ '/' :: geometryRow112_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_meanGap_before_field"
  err.flush

theorem geometryRow112_meanGap_field :
    geometryRowsJson112.getObjVal? "mean_gap" = .ok (.str geometryRow112_meanGapText) := by rfl

theorem geometryRow112_meanGap_numerator_no_slash :
    geometryRow112_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow112_meanGap_numerator_parse :
    SourceJson.intChars geometryRow112_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow112_meanGap_denominator_parse :
    SourceJson.intChars geometryRow112_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow112_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow112_meanGap_parse :
    parseRational geometryRow112_meanGapText = .ok geometryRowsTyped112.meanGap :=
  original_rational_fraction_of_chars geometryRow112_meanGapNumeratorChars geometryRow112_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow112_meanGap_numerator_no_slash geometryRow112_meanGap_numerator_parse
    geometryRow112_meanGap_denominator_parse geometryRow112_meanGap_denominator_nonzero

theorem geometryRow112_meanGap_read :
    rationalField geometryRowsJson112 "mean_gap" = .ok geometryRowsTyped112.meanGap :=
  original_rationalField_of_string geometryRowsJson112 "mean_gap" geometryRow112_meanGapText
    geometryRowsTyped112.meanGap geometryRow112_meanGap_field geometryRow112_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_meanGap_complete"
  err.flush

noncomputable def geometryRow112_jensenBoundNumeratorChars : List Char := ['1', '5', '2', '4', '9', '6', '5', '7', '7', '6', '2', '5', '4', '2', '3', '9', '5', '4', '5', '3', '5', '4', '9', '5', '2', '8', '0', '2', '9', '8', '4', '0', '5', '4', '8', '9', '8', '1', '7', '9', '4', '6', '2', '7', '8', '7', '2', '5', '8', '2', '2', '9', '0', '1', '4', '1', '7', '7', '1', '0', '4', '6', '0', '6', '5', '5', '2', '8', '1', '1', '1', '5', '7', '0', '2', '6', '3', '2', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow112_jensenBoundDenominatorChars : List Char := ['5', '6', '6', '3', '7', '7', '8', '6', '2', '3', '1', '1', '8', '7', '0', '4', '2', '2', '0', '5', '2', '5', '3', '6', '6', '2', '0', '0', '2', '2', '0', '3', '6', '1', '4', '9', '1', '7', '2', '6', '7', '2', '2', '5', '3', '2', '6', '7', '1', '4', '8', '4', '7', '5', '2', '8', '9', '7', '9', '6', '6', '8', '8', '2', '3', '8', '7', '7', '4', '5', '8', '9', '0', '3', '3', '5', '1', '6', '6', '7', '0', '6', '5', '4', '9', '0', '7', '8', '9', '7', '9', '8', '5', '7', '6', '0', '4', '4', '4', '0', '6', '5', '7', '9', '4', '2', '6', '6', '9', '3', '4', '8', '3', '9', '3', '0', '9', '7']
noncomputable def geometryRow112_jensenBoundText : String := String.ofList (geometryRow112_jensenBoundNumeratorChars ++ '/' :: geometryRow112_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_jensenBound_before_field"
  err.flush

theorem geometryRow112_jensenBound_field :
    geometryRowsJson112.getObjVal? "jensen_bound" = .ok (.str geometryRow112_jensenBoundText) := by rfl

theorem geometryRow112_jensenBound_numerator_no_slash :
    geometryRow112_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow112_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow112_jensenBoundNumeratorChars = some (1524965776254239545354952802984054898179462787258229014177104606552811157026326600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow112_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow112_jensenBoundDenominatorChars = some (5663778623118704220525366200220361491726722532671484752897966882387745890335166706549078979857604440657942669348393097 : Int) := by decide +kernel

theorem geometryRow112_jensenBound_denominator_nonzero : (5663778623118704220525366200220361491726722532671484752897966882387745890335166706549078979857604440657942669348393097 : Int) ≠ 0 := by decide +kernel

theorem geometryRow112_jensenBound_parse :
    parseRational geometryRow112_jensenBoundText = .ok geometryRowsTyped112.jensenBound :=
  original_rational_fraction_of_chars geometryRow112_jensenBoundNumeratorChars geometryRow112_jensenBoundDenominatorChars
    (1524965776254239545354952802984054898179462787258229014177104606552811157026326600000000000000000000000 : Int) (5663778623118704220525366200220361491726722532671484752897966882387745890335166706549078979857604440657942669348393097 : Int)
    geometryRow112_jensenBound_numerator_no_slash geometryRow112_jensenBound_numerator_parse
    geometryRow112_jensenBound_denominator_parse geometryRow112_jensenBound_denominator_nonzero

theorem geometryRow112_jensenBound_read :
    rationalField geometryRowsJson112 "jensen_bound" = .ok geometryRowsTyped112.jensenBound :=
  original_rationalField_of_string geometryRowsJson112 "jensen_bound" geometryRow112_jensenBoundText
    geometryRowsTyped112.jensenBound geometryRow112_jensenBound_field geometryRow112_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_factorMaxima_before"
  err.flush

theorem geometryRow112_factorMaxima_read :
    rationalArrayField geometryRowsJson112 "factor_maxima" = .ok geometryRowsTyped112.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_gapWeightedMeans_before"
  err.flush

theorem geometryRow112_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson112 "gap_weighted_means" = .ok geometryRowsTyped112.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow112_floorChars : List Char := ['2', '1', '3', '3', '2', '0', '9', '0', '1', '8', '0', '3', '2', '4']
noncomputable def geometryRow112_floorText : String := String.ofList geometryRow112_floorChars

theorem geometryRow112_floor_text_read :
    geometryRowsJson112.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow112_floorText := by rfl

theorem geometryRow112_floor_chars_parse :
    SourceJson.intChars geometryRow112_floorChars = some (21332090180324 : Int) := by decide +kernel

theorem geometryRow112_floor_parse :
    parseInteger geometryRow112_floorText = .ok geometryRowsTyped112.jensenFloorQ96 := by
  simp only [geometryRow112_floorText, parseInteger, String.toList_ofList, geometryRow112_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_112 :
    decodeGeometryRow geometryRowsJson112 = .ok geometryRowsTyped112 :=
  original_geometryRow_of_fields geometryRowsJson112 geometryRowsTyped112 geometryRow112_floorText
    geometryRow112_simplexId_read geometryRow112_vertexIds_read
    geometryRow112_physicalVolume_read geometryRow112_meanGap_read
    geometryRow112_factorMaxima_read geometryRow112_gapWeightedMeans_read
    geometryRow112_jensenBound_read geometryRow112_floor_text_read geometryRow112_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_112_original_decoder_complete"
  err.flush

theorem geometryRow112_shape :
    geometryRowsTyped112.simplexId = 112 ∧
    geometryRowsTyped112.vertexIds.size = 9 ∧ geometryRowsTyped112.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped112.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped112.factorMaxima.size = 10 ∧ geometryRowsTyped112.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock014 : List SourceJson := [geometryRowsJson112]
noncomputable def geometryRowsTypedBlock014 : List GeometryRow := [geometryRowsTyped112]

theorem geometry_Rows_block_014_push_eq (acc : List SourceJson) :
    SimplicesBlock014.blockPush acc = [geometryRowsJson112] ++ acc := by rfl

theorem geometry_Rows_block_014_reverse (acc : List SourceJson) :
    (SimplicesBlock014.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock014 := by
  rw [geometry_Rows_block_014_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_014 :
    geometryRowsJsonBlock014.mapM decodeGeometryRow = .ok geometryRowsTypedBlock014 := by
  simp only [geometryRowsJsonBlock014, geometryRowsTypedBlock014, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_112]
  rfl

theorem geometry_Rows_block_014_length : geometryRowsTypedBlock014.length = 1 := by rfl

#print axioms geometryRow112_simplexId_read
#print axioms geometryRow112_vertexIds_read
#print axioms geometryRow112_physicalVolume_field
#print axioms geometryRow112_physicalVolume_numerator_no_slash
#print axioms geometryRow112_physicalVolume_numerator_parse
#print axioms geometryRow112_physicalVolume_denominator_parse
#print axioms geometryRow112_physicalVolume_denominator_nonzero
#print axioms geometryRow112_physicalVolume_parse
#print axioms geometryRow112_physicalVolume_read
#print axioms geometryRow112_meanGap_field
#print axioms geometryRow112_meanGap_numerator_no_slash
#print axioms geometryRow112_meanGap_numerator_parse
#print axioms geometryRow112_meanGap_denominator_parse
#print axioms geometryRow112_meanGap_denominator_nonzero
#print axioms geometryRow112_meanGap_parse
#print axioms geometryRow112_meanGap_read
#print axioms geometryRow112_jensenBound_field
#print axioms geometryRow112_jensenBound_numerator_no_slash
#print axioms geometryRow112_jensenBound_numerator_parse
#print axioms geometryRow112_jensenBound_denominator_parse
#print axioms geometryRow112_jensenBound_denominator_nonzero
#print axioms geometryRow112_jensenBound_parse
#print axioms geometryRow112_jensenBound_read
#print axioms geometryRow112_factorMaxima_read
#print axioms geometryRow112_gapWeightedMeans_read
#print axioms geometryRow112_floor_text_read
#print axioms geometryRow112_floor_chars_parse
#print axioms geometryRow112_floor_parse
#print axioms decode_geometry_Rows_112
#print axioms geometryRow112_shape
#print axioms geometry_Rows_block_014_push_eq
#print axioms geometry_Rows_block_014_reverse
#print axioms decode_geometry_Rows_block_014
#print axioms geometry_Rows_block_014_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
