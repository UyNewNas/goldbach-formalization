import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00500

/-! Original GeometryRow 23: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson023 : SourceJson :=
  (simplicesChunk023Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped023 : GeometryRow :=
  { simplexId := 23,
    vertexIds := #[27, 25, 23, 21, 19, 18, 13, 12, 2],
    physicalVolume := ((511309901209857381272943939187 : ℚ) / (29779279092773437500000000000000000000000000000000000 : ℚ)),
    meanGap := ((4620979609 : ℚ) / (3902496000000 : ℚ)),
    factorMaxima := #[((39234443 : ℚ) / (416000000 : ℚ)), ((5109339 : ℚ) / (52000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((7359347 : ℚ) / (104000000 : ℚ)), ((2203073 : ℚ) / (60000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((1703113 : ℚ) / (52000000 : ℚ))],
    gapWeightedMeans := #[((826875281516448408697471 : ℚ) / (9467511081107133600000000 : ℚ)), ((26261063763131116270583 : ℚ) / (295859721284597925000000 : ℚ)), ((119485762175430652347349 : ℚ) / (946751108110713360000000 : ℚ)), ((17983518144062142019489 : ℚ) / (182067520790521800000000 : ℚ)), ((216464982370389147721463 : ℚ) / (2366877770276783400000000 : ℚ)), ((31237695961370574036967 : ℚ) / (473375554055356680000000 : ℚ)), ((156047694911517733740859 : ℚ) / (4733755540553566800000000 : ℚ)), ((50701274779972563960937 : ℚ) / (1577918513517855600000000 : ℚ)), ((48846240996311430899977 : ℚ) / (1577918513517855600000000 : ℚ)), ((2986365948882624756767 : ℚ) / (98619907094865975000000 : ℚ))],
    jensenBound := ((60804649077667403643284261797576022426922643528010780232243709148907927048888433902839893830666510710837968938904834427142123536875832898690692796532882905272085020277540850471596982272000000000000000000000000000 : ℚ) / (432976371853652494634235568696271034488887292824075801164563558191282600730879833789943902009997647848946570108866775123009792531312697279538040190296117937735770477122866102741073136929172645486001854445519995337853827103161 : ℚ)),
    jensenFloorQ96 := (11126336058764328 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_simplexId_before"
  err.flush

theorem geometryRow023_simplexId_read :
    geometryRowsJson023.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped023.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_vertexIds_before"
  err.flush

theorem geometryRow023_vertexIds_read :
    geometryRowsJson023.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped023.vertexIds := by decide +kernel

noncomputable def geometryRow023_physicalVolumeNumeratorChars : List Char := ['5', '1', '1', '3', '0', '9', '9', '0', '1', '2', '0', '9', '8', '5', '7', '3', '8', '1', '2', '7', '2', '9', '4', '3', '9', '3', '9', '1', '8', '7']
noncomputable def geometryRow023_physicalVolumeDenominatorChars : List Char := ['2', '9', '7', '7', '9', '2', '7', '9', '0', '9', '2', '7', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_physicalVolumeText : String := String.ofList (geometryRow023_physicalVolumeNumeratorChars ++ '/' :: geometryRow023_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_physicalVolume_before_field"
  err.flush

theorem geometryRow023_physicalVolume_field :
    geometryRowsJson023.getObjVal? "physical_volume" = .ok (.str geometryRow023_physicalVolumeText) := by rfl

theorem geometryRow023_physicalVolume_numerator_no_slash :
    geometryRow023_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeNumeratorChars = some (511309901209857381272943939187 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeDenominatorChars = some (29779279092773437500000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_nonzero : (29779279092773437500000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_physicalVolume_parse :
    parseRational geometryRow023_physicalVolumeText = .ok geometryRowsTyped023.physicalVolume :=
  original_rational_fraction_of_chars geometryRow023_physicalVolumeNumeratorChars geometryRow023_physicalVolumeDenominatorChars
    (511309901209857381272943939187 : Int) (29779279092773437500000000000000000000000000000000000 : Int)
    geometryRow023_physicalVolume_numerator_no_slash geometryRow023_physicalVolume_numerator_parse
    geometryRow023_physicalVolume_denominator_parse geometryRow023_physicalVolume_denominator_nonzero

theorem geometryRow023_physicalVolume_read :
    rationalField geometryRowsJson023 "physical_volume" = .ok geometryRowsTyped023.physicalVolume :=
  original_rationalField_of_string geometryRowsJson023 "physical_volume" geometryRow023_physicalVolumeText
    geometryRowsTyped023.physicalVolume geometryRow023_physicalVolume_field geometryRow023_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_physicalVolume_complete"
  err.flush

noncomputable def geometryRow023_meanGapNumeratorChars : List Char := ['4', '6', '2', '0', '9', '7', '9', '6', '0', '9']
noncomputable def geometryRow023_meanGapDenominatorChars : List Char := ['3', '9', '0', '2', '4', '9', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_meanGapText : String := String.ofList (geometryRow023_meanGapNumeratorChars ++ '/' :: geometryRow023_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_meanGap_before_field"
  err.flush

theorem geometryRow023_meanGap_field :
    geometryRowsJson023.getObjVal? "mean_gap" = .ok (.str geometryRow023_meanGapText) := by rfl

theorem geometryRow023_meanGap_numerator_no_slash :
    geometryRow023_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_meanGap_numerator_parse :
    SourceJson.intChars geometryRow023_meanGapNumeratorChars = some (4620979609 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_parse :
    SourceJson.intChars geometryRow023_meanGapDenominatorChars = some (3902496000000 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_nonzero : (3902496000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_meanGap_parse :
    parseRational geometryRow023_meanGapText = .ok geometryRowsTyped023.meanGap :=
  original_rational_fraction_of_chars geometryRow023_meanGapNumeratorChars geometryRow023_meanGapDenominatorChars
    (4620979609 : Int) (3902496000000 : Int)
    geometryRow023_meanGap_numerator_no_slash geometryRow023_meanGap_numerator_parse
    geometryRow023_meanGap_denominator_parse geometryRow023_meanGap_denominator_nonzero

theorem geometryRow023_meanGap_read :
    rationalField geometryRowsJson023 "mean_gap" = .ok geometryRowsTyped023.meanGap :=
  original_rationalField_of_string geometryRowsJson023 "mean_gap" geometryRow023_meanGapText
    geometryRowsTyped023.meanGap geometryRow023_meanGap_field geometryRow023_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_meanGap_complete"
  err.flush

noncomputable def geometryRow023_jensenBoundNumeratorChars : List Char := ['6', '0', '8', '0', '4', '6', '4', '9', '0', '7', '7', '6', '6', '7', '4', '0', '3', '6', '4', '3', '2', '8', '4', '2', '6', '1', '7', '9', '7', '5', '7', '6', '0', '2', '2', '4', '2', '6', '9', '2', '2', '6', '4', '3', '5', '2', '8', '0', '1', '0', '7', '8', '0', '2', '3', '2', '2', '4', '3', '7', '0', '9', '1', '4', '8', '9', '0', '7', '9', '2', '7', '0', '4', '8', '8', '8', '8', '4', '3', '3', '9', '0', '2', '8', '3', '9', '8', '9', '3', '8', '3', '0', '6', '6', '6', '5', '1', '0', '7', '1', '0', '8', '3', '7', '9', '6', '8', '9', '3', '8', '9', '0', '4', '8', '3', '4', '4', '2', '7', '1', '4', '2', '1', '2', '3', '5', '3', '6', '8', '7', '5', '8', '3', '2', '8', '9', '8', '6', '9', '0', '6', '9', '2', '7', '9', '6', '5', '3', '2', '8', '8', '2', '9', '0', '5', '2', '7', '2', '0', '8', '5', '0', '2', '0', '2', '7', '7', '5', '4', '0', '8', '5', '0', '4', '7', '1', '5', '9', '6', '9', '8', '2', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_jensenBoundDenominatorChars : List Char := ['4', '3', '2', '9', '7', '6', '3', '7', '1', '8', '5', '3', '6', '5', '2', '4', '9', '4', '6', '3', '4', '2', '3', '5', '5', '6', '8', '6', '9', '6', '2', '7', '1', '0', '3', '4', '4', '8', '8', '8', '8', '7', '2', '9', '2', '8', '2', '4', '0', '7', '5', '8', '0', '1', '1', '6', '4', '5', '6', '3', '5', '5', '8', '1', '9', '1', '2', '8', '2', '6', '0', '0', '7', '3', '0', '8', '7', '9', '8', '3', '3', '7', '8', '9', '9', '4', '3', '9', '0', '2', '0', '0', '9', '9', '9', '7', '6', '4', '7', '8', '4', '8', '9', '4', '6', '5', '7', '0', '1', '0', '8', '8', '6', '6', '7', '7', '5', '1', '2', '3', '0', '0', '9', '7', '9', '2', '5', '3', '1', '3', '1', '2', '6', '9', '7', '2', '7', '9', '5', '3', '8', '0', '4', '0', '1', '9', '0', '2', '9', '6', '1', '1', '7', '9', '3', '7', '7', '3', '5', '7', '7', '0', '4', '7', '7', '1', '2', '2', '8', '6', '6', '1', '0', '2', '7', '4', '1', '0', '7', '3', '1', '3', '6', '9', '2', '9', '1', '7', '2', '6', '4', '5', '4', '8', '6', '0', '0', '1', '8', '5', '4', '4', '4', '5', '5', '1', '9', '9', '9', '5', '3', '3', '7', '8', '5', '3', '8', '2', '7', '1', '0', '3', '1', '6', '1']
noncomputable def geometryRow023_jensenBoundText : String := String.ofList (geometryRow023_jensenBoundNumeratorChars ++ '/' :: geometryRow023_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_jensenBound_before_field"
  err.flush

theorem geometryRow023_jensenBound_field :
    geometryRowsJson023.getObjVal? "jensen_bound" = .ok (.str geometryRow023_jensenBoundText) := by rfl

theorem geometryRow023_jensenBound_numerator_no_slash :
    geometryRow023_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow023_jensenBoundNumeratorChars = some (60804649077667403643284261797576022426922643528010780232243709148907927048888433902839893830666510710837968938904834427142123536875832898690692796532882905272085020277540850471596982272000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow023_jensenBoundDenominatorChars = some (432976371853652494634235568696271034488887292824075801164563558191282600730879833789943902009997647848946570108866775123009792531312697279538040190296117937735770477122866102741073136929172645486001854445519995337853827103161 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_nonzero : (432976371853652494634235568696271034488887292824075801164563558191282600730879833789943902009997647848946570108866775123009792531312697279538040190296117937735770477122866102741073136929172645486001854445519995337853827103161 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_jensenBound_parse :
    parseRational geometryRow023_jensenBoundText = .ok geometryRowsTyped023.jensenBound :=
  original_rational_fraction_of_chars geometryRow023_jensenBoundNumeratorChars geometryRow023_jensenBoundDenominatorChars
    (60804649077667403643284261797576022426922643528010780232243709148907927048888433902839893830666510710837968938904834427142123536875832898690692796532882905272085020277540850471596982272000000000000000000000000000 : Int) (432976371853652494634235568696271034488887292824075801164563558191282600730879833789943902009997647848946570108866775123009792531312697279538040190296117937735770477122866102741073136929172645486001854445519995337853827103161 : Int)
    geometryRow023_jensenBound_numerator_no_slash geometryRow023_jensenBound_numerator_parse
    geometryRow023_jensenBound_denominator_parse geometryRow023_jensenBound_denominator_nonzero

theorem geometryRow023_jensenBound_read :
    rationalField geometryRowsJson023 "jensen_bound" = .ok geometryRowsTyped023.jensenBound :=
  original_rationalField_of_string geometryRowsJson023 "jensen_bound" geometryRow023_jensenBoundText
    geometryRowsTyped023.jensenBound geometryRow023_jensenBound_field geometryRow023_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_factorMaxima_before"
  err.flush

theorem geometryRow023_factorMaxima_read :
    rationalArrayField geometryRowsJson023 "factor_maxima" = .ok geometryRowsTyped023.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_gapWeightedMeans_before"
  err.flush

theorem geometryRow023_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson023 "gap_weighted_means" = .ok geometryRowsTyped023.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow023_floorChars : List Char := ['1', '1', '1', '2', '6', '3', '3', '6', '0', '5', '8', '7', '6', '4', '3', '2', '8']
noncomputable def geometryRow023_floorText : String := String.ofList geometryRow023_floorChars

theorem geometryRow023_floor_text_read :
    geometryRowsJson023.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow023_floorText := by rfl

theorem geometryRow023_floor_chars_parse :
    SourceJson.intChars geometryRow023_floorChars = some (11126336058764328 : Int) := by decide +kernel

theorem geometryRow023_floor_parse :
    parseInteger geometryRow023_floorText = .ok geometryRowsTyped023.jensenFloorQ96 := by
  simp only [geometryRow023_floorText, parseInteger, String.toList_ofList, geometryRow023_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_023 :
    decodeGeometryRow geometryRowsJson023 = .ok geometryRowsTyped023 :=
  original_geometryRow_of_fields geometryRowsJson023 geometryRowsTyped023 geometryRow023_floorText
    geometryRow023_simplexId_read geometryRow023_vertexIds_read
    geometryRow023_physicalVolume_read geometryRow023_meanGap_read
    geometryRow023_factorMaxima_read geometryRow023_gapWeightedMeans_read
    geometryRow023_jensenBound_read geometryRow023_floor_text_read geometryRow023_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_023_original_decoder_complete"
  err.flush

#print axioms geometryRow023_simplexId_read
#print axioms geometryRow023_vertexIds_read
#print axioms geometryRow023_physicalVolume_field
#print axioms geometryRow023_physicalVolume_numerator_no_slash
#print axioms geometryRow023_physicalVolume_numerator_parse
#print axioms geometryRow023_physicalVolume_denominator_parse
#print axioms geometryRow023_physicalVolume_denominator_nonzero
#print axioms geometryRow023_physicalVolume_parse
#print axioms geometryRow023_physicalVolume_read
#print axioms geometryRow023_meanGap_field
#print axioms geometryRow023_meanGap_numerator_no_slash
#print axioms geometryRow023_meanGap_numerator_parse
#print axioms geometryRow023_meanGap_denominator_parse
#print axioms geometryRow023_meanGap_denominator_nonzero
#print axioms geometryRow023_meanGap_parse
#print axioms geometryRow023_meanGap_read
#print axioms geometryRow023_jensenBound_field
#print axioms geometryRow023_jensenBound_numerator_no_slash
#print axioms geometryRow023_jensenBound_numerator_parse
#print axioms geometryRow023_jensenBound_denominator_parse
#print axioms geometryRow023_jensenBound_denominator_nonzero
#print axioms geometryRow023_jensenBound_parse
#print axioms geometryRow023_jensenBound_read
#print axioms geometryRow023_factorMaxima_read
#print axioms geometryRow023_gapWeightedMeans_read
#print axioms geometryRow023_floor_text_read
#print axioms geometryRow023_floor_chars_parse
#print axioms geometryRow023_floor_parse
#print axioms decode_geometry_Rows_023

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
