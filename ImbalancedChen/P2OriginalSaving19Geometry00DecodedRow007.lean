import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00100

/-! Original GeometryRow 7: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson007 : SourceJson :=
  (simplicesChunk007Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped007 : GeometryRow :=
  { simplexId := 7,
    vertexIds := #[27, 25, 23, 9, 7, 5, 3, 2, 0],
    physicalVolume := ((2652850437428262551002066837289825218064191 : ℚ) / (17083472803488000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((19865249 : ℚ) / (23712000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((1886764114377059253907 : ℚ) / (20525776475349600000000 : ℚ)), ((954997448988833979101 : ℚ) / (10262888237674800000000 : ℚ)), ((2489518286272310820599 : ℚ) / (20525776475349600000000 : ℚ)), ((143569303235378711639 : ℚ) / (1578905882719200000000 : ℚ)), ((191437092640746525967 : ℚ) / (2280641830594400000000 : ℚ)), ((1466159376304720504531 : ℚ) / (20525776475349600000000 : ℚ)), ((45621242594121449111 : ℚ) / (1282861029709350000000 : ℚ)), ((2970162840442112633 : ℚ) / (85524068647290000000 : ℚ)), ((34827579500198860187 : ℚ) / (1026288823767480000000 : ℚ)), ((111603327161092612847 : ℚ) / (3420962745891600000000 : ℚ))],
    jensenBound := ((4927727627140313233323087421896728017271682873288442020916230233907713343773157525961825805322410158002531813911515977476680900711527845131585849241331862443213372420096000000000000000000000 : ℚ) / (7323327511624172629952013320275163140561070857485865054626551285491149986836539035267788714743418465915933063897956089985472279086635773039835371082145575251623804891256811460653440361170230743423618381 : ℚ)),
    jensenFloorQ96 := (53311121843097312 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_simplexId_before"
  err.flush

theorem geometryRow007_simplexId_read :
    geometryRowsJson007.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped007.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_vertexIds_before"
  err.flush

theorem geometryRow007_vertexIds_read :
    geometryRowsJson007.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped007.vertexIds := by decide +kernel

noncomputable def geometryRow007_physicalVolumeNumeratorChars : List Char := ['2', '6', '5', '2', '8', '5', '0', '4', '3', '7', '4', '2', '8', '2', '6', '2', '5', '5', '1', '0', '0', '2', '0', '6', '6', '8', '3', '7', '2', '8', '9', '8', '2', '5', '2', '1', '8', '0', '6', '4', '1', '9', '1']
noncomputable def geometryRow007_physicalVolumeDenominatorChars : List Char := ['1', '7', '0', '8', '3', '4', '7', '2', '8', '0', '3', '4', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_physicalVolumeText : String := String.ofList (geometryRow007_physicalVolumeNumeratorChars ++ '/' :: geometryRow007_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_physicalVolume_before_field"
  err.flush

theorem geometryRow007_physicalVolume_field :
    geometryRowsJson007.getObjVal? "physical_volume" = .ok (.str geometryRow007_physicalVolumeText) := by rfl

theorem geometryRow007_physicalVolume_numerator_no_slash :
    geometryRow007_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeNumeratorChars = some (2652850437428262551002066837289825218064191 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeDenominatorChars = some (17083472803488000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_nonzero : (17083472803488000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_physicalVolume_parse :
    parseRational geometryRow007_physicalVolumeText = .ok geometryRowsTyped007.physicalVolume :=
  original_rational_fraction_of_chars geometryRow007_physicalVolumeNumeratorChars geometryRow007_physicalVolumeDenominatorChars
    (2652850437428262551002066837289825218064191 : Int) (17083472803488000000000000000000000000000000000000000000000000000 : Int)
    geometryRow007_physicalVolume_numerator_no_slash geometryRow007_physicalVolume_numerator_parse
    geometryRow007_physicalVolume_denominator_parse geometryRow007_physicalVolume_denominator_nonzero

theorem geometryRow007_physicalVolume_read :
    rationalField geometryRowsJson007 "physical_volume" = .ok geometryRowsTyped007.physicalVolume :=
  original_rationalField_of_string geometryRowsJson007 "physical_volume" geometryRow007_physicalVolumeText
    geometryRowsTyped007.physicalVolume geometryRow007_physicalVolume_field geometryRow007_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_physicalVolume_complete"
  err.flush

noncomputable def geometryRow007_meanGapNumeratorChars : List Char := ['1', '9', '8', '6', '5', '2', '4', '9']
noncomputable def geometryRow007_meanGapDenominatorChars : List Char := ['2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_meanGapText : String := String.ofList (geometryRow007_meanGapNumeratorChars ++ '/' :: geometryRow007_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_meanGap_before_field"
  err.flush

theorem geometryRow007_meanGap_field :
    geometryRowsJson007.getObjVal? "mean_gap" = .ok (.str geometryRow007_meanGapText) := by rfl

theorem geometryRow007_meanGap_numerator_no_slash :
    geometryRow007_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_meanGap_numerator_parse :
    SourceJson.intChars geometryRow007_meanGapNumeratorChars = some (19865249 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_parse :
    SourceJson.intChars geometryRow007_meanGapDenominatorChars = some (23712000000 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_nonzero : (23712000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_meanGap_parse :
    parseRational geometryRow007_meanGapText = .ok geometryRowsTyped007.meanGap :=
  original_rational_fraction_of_chars geometryRow007_meanGapNumeratorChars geometryRow007_meanGapDenominatorChars
    (19865249 : Int) (23712000000 : Int)
    geometryRow007_meanGap_numerator_no_slash geometryRow007_meanGap_numerator_parse
    geometryRow007_meanGap_denominator_parse geometryRow007_meanGap_denominator_nonzero

theorem geometryRow007_meanGap_read :
    rationalField geometryRowsJson007 "mean_gap" = .ok geometryRowsTyped007.meanGap :=
  original_rationalField_of_string geometryRowsJson007 "mean_gap" geometryRow007_meanGapText
    geometryRowsTyped007.meanGap geometryRow007_meanGap_field geometryRow007_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_meanGap_complete"
  err.flush

noncomputable def geometryRow007_jensenBoundNumeratorChars : List Char := ['4', '9', '2', '7', '7', '2', '7', '6', '2', '7', '1', '4', '0', '3', '1', '3', '2', '3', '3', '3', '2', '3', '0', '8', '7', '4', '2', '1', '8', '9', '6', '7', '2', '8', '0', '1', '7', '2', '7', '1', '6', '8', '2', '8', '7', '3', '2', '8', '8', '4', '4', '2', '0', '2', '0', '9', '1', '6', '2', '3', '0', '2', '3', '3', '9', '0', '7', '7', '1', '3', '3', '4', '3', '7', '7', '3', '1', '5', '7', '5', '2', '5', '9', '6', '1', '8', '2', '5', '8', '0', '5', '3', '2', '2', '4', '1', '0', '1', '5', '8', '0', '0', '2', '5', '3', '1', '8', '1', '3', '9', '1', '1', '5', '1', '5', '9', '7', '7', '4', '7', '6', '6', '8', '0', '9', '0', '0', '7', '1', '1', '5', '2', '7', '8', '4', '5', '1', '3', '1', '5', '8', '5', '8', '4', '9', '2', '4', '1', '3', '3', '1', '8', '6', '2', '4', '4', '3', '2', '1', '3', '3', '7', '2', '4', '2', '0', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_jensenBoundDenominatorChars : List Char := ['7', '3', '2', '3', '3', '2', '7', '5', '1', '1', '6', '2', '4', '1', '7', '2', '6', '2', '9', '9', '5', '2', '0', '1', '3', '3', '2', '0', '2', '7', '5', '1', '6', '3', '1', '4', '0', '5', '6', '1', '0', '7', '0', '8', '5', '7', '4', '8', '5', '8', '6', '5', '0', '5', '4', '6', '2', '6', '5', '5', '1', '2', '8', '5', '4', '9', '1', '1', '4', '9', '9', '8', '6', '8', '3', '6', '5', '3', '9', '0', '3', '5', '2', '6', '7', '7', '8', '8', '7', '1', '4', '7', '4', '3', '4', '1', '8', '4', '6', '5', '9', '1', '5', '9', '3', '3', '0', '6', '3', '8', '9', '7', '9', '5', '6', '0', '8', '9', '9', '8', '5', '4', '7', '2', '2', '7', '9', '0', '8', '6', '6', '3', '5', '7', '7', '3', '0', '3', '9', '8', '3', '5', '3', '7', '1', '0', '8', '2', '1', '4', '5', '5', '7', '5', '2', '5', '1', '6', '2', '3', '8', '0', '4', '8', '9', '1', '2', '5', '6', '8', '1', '1', '4', '6', '0', '6', '5', '3', '4', '4', '0', '3', '6', '1', '1', '7', '0', '2', '3', '0', '7', '4', '3', '4', '2', '3', '6', '1', '8', '3', '8', '1']
noncomputable def geometryRow007_jensenBoundText : String := String.ofList (geometryRow007_jensenBoundNumeratorChars ++ '/' :: geometryRow007_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_jensenBound_before_field"
  err.flush

theorem geometryRow007_jensenBound_field :
    geometryRowsJson007.getObjVal? "jensen_bound" = .ok (.str geometryRow007_jensenBoundText) := by rfl

theorem geometryRow007_jensenBound_numerator_no_slash :
    geometryRow007_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow007_jensenBoundNumeratorChars = some (4927727627140313233323087421896728017271682873288442020916230233907713343773157525961825805322410158002531813911515977476680900711527845131585849241331862443213372420096000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow007_jensenBoundDenominatorChars = some (7323327511624172629952013320275163140561070857485865054626551285491149986836539035267788714743418465915933063897956089985472279086635773039835371082145575251623804891256811460653440361170230743423618381 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_nonzero : (7323327511624172629952013320275163140561070857485865054626551285491149986836539035267788714743418465915933063897956089985472279086635773039835371082145575251623804891256811460653440361170230743423618381 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_jensenBound_parse :
    parseRational geometryRow007_jensenBoundText = .ok geometryRowsTyped007.jensenBound :=
  original_rational_fraction_of_chars geometryRow007_jensenBoundNumeratorChars geometryRow007_jensenBoundDenominatorChars
    (4927727627140313233323087421896728017271682873288442020916230233907713343773157525961825805322410158002531813911515977476680900711527845131585849241331862443213372420096000000000000000000000 : Int) (7323327511624172629952013320275163140561070857485865054626551285491149986836539035267788714743418465915933063897956089985472279086635773039835371082145575251623804891256811460653440361170230743423618381 : Int)
    geometryRow007_jensenBound_numerator_no_slash geometryRow007_jensenBound_numerator_parse
    geometryRow007_jensenBound_denominator_parse geometryRow007_jensenBound_denominator_nonzero

theorem geometryRow007_jensenBound_read :
    rationalField geometryRowsJson007 "jensen_bound" = .ok geometryRowsTyped007.jensenBound :=
  original_rationalField_of_string geometryRowsJson007 "jensen_bound" geometryRow007_jensenBoundText
    geometryRowsTyped007.jensenBound geometryRow007_jensenBound_field geometryRow007_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_factorMaxima_before"
  err.flush

theorem geometryRow007_factorMaxima_read :
    rationalArrayField geometryRowsJson007 "factor_maxima" = .ok geometryRowsTyped007.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_gapWeightedMeans_before"
  err.flush

theorem geometryRow007_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson007 "gap_weighted_means" = .ok geometryRowsTyped007.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow007_floorChars : List Char := ['5', '3', '3', '1', '1', '1', '2', '1', '8', '4', '3', '0', '9', '7', '3', '1', '2']
noncomputable def geometryRow007_floorText : String := String.ofList geometryRow007_floorChars

theorem geometryRow007_floor_text_read :
    geometryRowsJson007.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow007_floorText := by rfl

theorem geometryRow007_floor_chars_parse :
    SourceJson.intChars geometryRow007_floorChars = some (53311121843097312 : Int) := by decide +kernel

theorem geometryRow007_floor_parse :
    parseInteger geometryRow007_floorText = .ok geometryRowsTyped007.jensenFloorQ96 := by
  simp only [geometryRow007_floorText, parseInteger, String.toList_ofList, geometryRow007_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_007 :
    decodeGeometryRow geometryRowsJson007 = .ok geometryRowsTyped007 :=
  original_geometryRow_of_fields geometryRowsJson007 geometryRowsTyped007 geometryRow007_floorText
    geometryRow007_simplexId_read geometryRow007_vertexIds_read
    geometryRow007_physicalVolume_read geometryRow007_meanGap_read
    geometryRow007_factorMaxima_read geometryRow007_gapWeightedMeans_read
    geometryRow007_jensenBound_read geometryRow007_floor_text_read geometryRow007_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_007_original_decoder_complete"
  err.flush

#print axioms geometryRow007_simplexId_read
#print axioms geometryRow007_vertexIds_read
#print axioms geometryRow007_physicalVolume_field
#print axioms geometryRow007_physicalVolume_numerator_no_slash
#print axioms geometryRow007_physicalVolume_numerator_parse
#print axioms geometryRow007_physicalVolume_denominator_parse
#print axioms geometryRow007_physicalVolume_denominator_nonzero
#print axioms geometryRow007_physicalVolume_parse
#print axioms geometryRow007_physicalVolume_read
#print axioms geometryRow007_meanGap_field
#print axioms geometryRow007_meanGap_numerator_no_slash
#print axioms geometryRow007_meanGap_numerator_parse
#print axioms geometryRow007_meanGap_denominator_parse
#print axioms geometryRow007_meanGap_denominator_nonzero
#print axioms geometryRow007_meanGap_parse
#print axioms geometryRow007_meanGap_read
#print axioms geometryRow007_jensenBound_field
#print axioms geometryRow007_jensenBound_numerator_no_slash
#print axioms geometryRow007_jensenBound_numerator_parse
#print axioms geometryRow007_jensenBound_denominator_parse
#print axioms geometryRow007_jensenBound_denominator_nonzero
#print axioms geometryRow007_jensenBound_parse
#print axioms geometryRow007_jensenBound_read
#print axioms geometryRow007_factorMaxima_read
#print axioms geometryRow007_gapWeightedMeans_read
#print axioms geometryRow007_floor_text_read
#print axioms geometryRow007_floor_chars_parse
#print axioms geometryRow007_floor_parse
#print axioms decode_geometry_Rows_007

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
