import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00000

/-! Original GeometryRow 1: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson001 : SourceJson :=
  (simplicesChunk001Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped001 : GeometryRow :=
  { simplexId := 1,
    vertexIds := #[27, 25, 11, 9, 7, 5, 3, 2, 0],
    physicalVolume := ((6477384745712663246322391033126942478007520303 : ℚ) / (37902531660005376000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((19865249 : ℚ) / (23712000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((16827881 : ℚ) / (180000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((140619 : ℚ) / (3250000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((1171847 : ℚ) / (30000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((643583878014991819289 : ℚ) / (6841925491783200000000 : ℚ)), ((108554578758088009009 : ℚ) / (1140320915297200000000 : ℚ)), ((822370895460748037393 : ℚ) / (6841925491783200000000 : ℚ)), ((1843583502113747936447 : ℚ) / (20525776475349600000000 : ℚ)), ((559511491347564641101 : ℚ) / (6841925491783200000000 : ℚ)), ((496188325398262404317 : ℚ) / (6841925491783200000000 : ℚ)), ((20887045592775035771 : ℚ) / (570160457648600000000 : ℚ)), ((1371636388004260843 : ℚ) / (39472647067980000000 : ℚ)), ((2680628577154176193 : ℚ) / (78945294135960000000 : ℚ)), ((335015901511332141761 : ℚ) / (10262888237674800000000 : ℚ))],
    jensenBound := ((5303043124036511258712160275644797675959327014222986280829308067763068735867068651151643465476904560147861631101248003305509083670421787493419324487362872026634171712000000000000000000000 : ℚ) / (7490936286502424745039414837101463170577171286972732576063115636681613392642870421318752421601770121348431256425518097703422558069460892656802515496574922304263476673074619758631857409818150108445883 : ℚ)),
    jensenFloorQ96 := (56087830196655987 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_simplexId_before"
  err.flush

theorem geometryRow001_simplexId_read :
    geometryRowsJson001.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped001.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_vertexIds_before"
  err.flush

theorem geometryRow001_vertexIds_read :
    geometryRowsJson001.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped001.vertexIds := by decide +kernel

noncomputable def geometryRow001_physicalVolumeNumeratorChars : List Char := ['6', '4', '7', '7', '3', '8', '4', '7', '4', '5', '7', '1', '2', '6', '6', '3', '2', '4', '6', '3', '2', '2', '3', '9', '1', '0', '3', '3', '1', '2', '6', '9', '4', '2', '4', '7', '8', '0', '0', '7', '5', '2', '0', '3', '0', '3']
noncomputable def geometryRow001_physicalVolumeDenominatorChars : List Char := ['3', '7', '9', '0', '2', '5', '3', '1', '6', '6', '0', '0', '0', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_physicalVolumeText : String := String.ofList (geometryRow001_physicalVolumeNumeratorChars ++ '/' :: geometryRow001_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_physicalVolume_before_field"
  err.flush

theorem geometryRow001_physicalVolume_field :
    geometryRowsJson001.getObjVal? "physical_volume" = .ok (.str geometryRow001_physicalVolumeText) := by rfl

theorem geometryRow001_physicalVolume_numerator_no_slash :
    geometryRow001_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeNumeratorChars = some (6477384745712663246322391033126942478007520303 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeDenominatorChars = some (37902531660005376000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_nonzero : (37902531660005376000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_physicalVolume_parse :
    parseRational geometryRow001_physicalVolumeText = .ok geometryRowsTyped001.physicalVolume :=
  original_rational_fraction_of_chars geometryRow001_physicalVolumeNumeratorChars geometryRow001_physicalVolumeDenominatorChars
    (6477384745712663246322391033126942478007520303 : Int) (37902531660005376000000000000000000000000000000000000000000000000000 : Int)
    geometryRow001_physicalVolume_numerator_no_slash geometryRow001_physicalVolume_numerator_parse
    geometryRow001_physicalVolume_denominator_parse geometryRow001_physicalVolume_denominator_nonzero

theorem geometryRow001_physicalVolume_read :
    rationalField geometryRowsJson001 "physical_volume" = .ok geometryRowsTyped001.physicalVolume :=
  original_rationalField_of_string geometryRowsJson001 "physical_volume" geometryRow001_physicalVolumeText
    geometryRowsTyped001.physicalVolume geometryRow001_physicalVolume_field geometryRow001_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_physicalVolume_complete"
  err.flush

noncomputable def geometryRow001_meanGapNumeratorChars : List Char := ['1', '9', '8', '6', '5', '2', '4', '9']
noncomputable def geometryRow001_meanGapDenominatorChars : List Char := ['2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_meanGapText : String := String.ofList (geometryRow001_meanGapNumeratorChars ++ '/' :: geometryRow001_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_meanGap_before_field"
  err.flush

theorem geometryRow001_meanGap_field :
    geometryRowsJson001.getObjVal? "mean_gap" = .ok (.str geometryRow001_meanGapText) := by rfl

theorem geometryRow001_meanGap_numerator_no_slash :
    geometryRow001_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_meanGap_numerator_parse :
    SourceJson.intChars geometryRow001_meanGapNumeratorChars = some (19865249 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_parse :
    SourceJson.intChars geometryRow001_meanGapDenominatorChars = some (23712000000 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_nonzero : (23712000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_meanGap_parse :
    parseRational geometryRow001_meanGapText = .ok geometryRowsTyped001.meanGap :=
  original_rational_fraction_of_chars geometryRow001_meanGapNumeratorChars geometryRow001_meanGapDenominatorChars
    (19865249 : Int) (23712000000 : Int)
    geometryRow001_meanGap_numerator_no_slash geometryRow001_meanGap_numerator_parse
    geometryRow001_meanGap_denominator_parse geometryRow001_meanGap_denominator_nonzero

theorem geometryRow001_meanGap_read :
    rationalField geometryRowsJson001 "mean_gap" = .ok geometryRowsTyped001.meanGap :=
  original_rationalField_of_string geometryRowsJson001 "mean_gap" geometryRow001_meanGapText
    geometryRowsTyped001.meanGap geometryRow001_meanGap_field geometryRow001_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_meanGap_complete"
  err.flush

noncomputable def geometryRow001_jensenBoundNumeratorChars : List Char := ['5', '3', '0', '3', '0', '4', '3', '1', '2', '4', '0', '3', '6', '5', '1', '1', '2', '5', '8', '7', '1', '2', '1', '6', '0', '2', '7', '5', '6', '4', '4', '7', '9', '7', '6', '7', '5', '9', '5', '9', '3', '2', '7', '0', '1', '4', '2', '2', '2', '9', '8', '6', '2', '8', '0', '8', '2', '9', '3', '0', '8', '0', '6', '7', '7', '6', '3', '0', '6', '8', '7', '3', '5', '8', '6', '7', '0', '6', '8', '6', '5', '1', '1', '5', '1', '6', '4', '3', '4', '6', '5', '4', '7', '6', '9', '0', '4', '5', '6', '0', '1', '4', '7', '8', '6', '1', '6', '3', '1', '1', '0', '1', '2', '4', '8', '0', '0', '3', '3', '0', '5', '5', '0', '9', '0', '8', '3', '6', '7', '0', '4', '2', '1', '7', '8', '7', '4', '9', '3', '4', '1', '9', '3', '2', '4', '4', '8', '7', '3', '6', '2', '8', '7', '2', '0', '2', '6', '6', '3', '4', '1', '7', '1', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_jensenBoundDenominatorChars : List Char := ['7', '4', '9', '0', '9', '3', '6', '2', '8', '6', '5', '0', '2', '4', '2', '4', '7', '4', '5', '0', '3', '9', '4', '1', '4', '8', '3', '7', '1', '0', '1', '4', '6', '3', '1', '7', '0', '5', '7', '7', '1', '7', '1', '2', '8', '6', '9', '7', '2', '7', '3', '2', '5', '7', '6', '0', '6', '3', '1', '1', '5', '6', '3', '6', '6', '8', '1', '6', '1', '3', '3', '9', '2', '6', '4', '2', '8', '7', '0', '4', '2', '1', '3', '1', '8', '7', '5', '2', '4', '2', '1', '6', '0', '1', '7', '7', '0', '1', '2', '1', '3', '4', '8', '4', '3', '1', '2', '5', '6', '4', '2', '5', '5', '1', '8', '0', '9', '7', '7', '0', '3', '4', '2', '2', '5', '5', '8', '0', '6', '9', '4', '6', '0', '8', '9', '2', '6', '5', '6', '8', '0', '2', '5', '1', '5', '4', '9', '6', '5', '7', '4', '9', '2', '2', '3', '0', '4', '2', '6', '3', '4', '7', '6', '6', '7', '3', '0', '7', '4', '6', '1', '9', '7', '5', '8', '6', '3', '1', '8', '5', '7', '4', '0', '9', '8', '1', '8', '1', '5', '0', '1', '0', '8', '4', '4', '5', '8', '8', '3']
noncomputable def geometryRow001_jensenBoundText : String := String.ofList (geometryRow001_jensenBoundNumeratorChars ++ '/' :: geometryRow001_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_jensenBound_before_field"
  err.flush

theorem geometryRow001_jensenBound_field :
    geometryRowsJson001.getObjVal? "jensen_bound" = .ok (.str geometryRow001_jensenBoundText) := by rfl

theorem geometryRow001_jensenBound_numerator_no_slash :
    geometryRow001_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow001_jensenBoundNumeratorChars = some (5303043124036511258712160275644797675959327014222986280829308067763068735867068651151643465476904560147861631101248003305509083670421787493419324487362872026634171712000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow001_jensenBoundDenominatorChars = some (7490936286502424745039414837101463170577171286972732576063115636681613392642870421318752421601770121348431256425518097703422558069460892656802515496574922304263476673074619758631857409818150108445883 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_nonzero : (7490936286502424745039414837101463170577171286972732576063115636681613392642870421318752421601770121348431256425518097703422558069460892656802515496574922304263476673074619758631857409818150108445883 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_jensenBound_parse :
    parseRational geometryRow001_jensenBoundText = .ok geometryRowsTyped001.jensenBound :=
  original_rational_fraction_of_chars geometryRow001_jensenBoundNumeratorChars geometryRow001_jensenBoundDenominatorChars
    (5303043124036511258712160275644797675959327014222986280829308067763068735867068651151643465476904560147861631101248003305509083670421787493419324487362872026634171712000000000000000000000 : Int) (7490936286502424745039414837101463170577171286972732576063115636681613392642870421318752421601770121348431256425518097703422558069460892656802515496574922304263476673074619758631857409818150108445883 : Int)
    geometryRow001_jensenBound_numerator_no_slash geometryRow001_jensenBound_numerator_parse
    geometryRow001_jensenBound_denominator_parse geometryRow001_jensenBound_denominator_nonzero

theorem geometryRow001_jensenBound_read :
    rationalField geometryRowsJson001 "jensen_bound" = .ok geometryRowsTyped001.jensenBound :=
  original_rationalField_of_string geometryRowsJson001 "jensen_bound" geometryRow001_jensenBoundText
    geometryRowsTyped001.jensenBound geometryRow001_jensenBound_field geometryRow001_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_factorMaxima_before"
  err.flush

theorem geometryRow001_factorMaxima_read :
    rationalArrayField geometryRowsJson001 "factor_maxima" = .ok geometryRowsTyped001.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_gapWeightedMeans_before"
  err.flush

theorem geometryRow001_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson001 "gap_weighted_means" = .ok geometryRowsTyped001.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow001_floorChars : List Char := ['5', '6', '0', '8', '7', '8', '3', '0', '1', '9', '6', '6', '5', '5', '9', '8', '7']
noncomputable def geometryRow001_floorText : String := String.ofList geometryRow001_floorChars

theorem geometryRow001_floor_text_read :
    geometryRowsJson001.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow001_floorText := by rfl

theorem geometryRow001_floor_chars_parse :
    SourceJson.intChars geometryRow001_floorChars = some (56087830196655987 : Int) := by decide +kernel

theorem geometryRow001_floor_parse :
    parseInteger geometryRow001_floorText = .ok geometryRowsTyped001.jensenFloorQ96 := by
  simp only [geometryRow001_floorText, parseInteger, String.toList_ofList, geometryRow001_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_001 :
    decodeGeometryRow geometryRowsJson001 = .ok geometryRowsTyped001 :=
  original_geometryRow_of_fields geometryRowsJson001 geometryRowsTyped001 geometryRow001_floorText
    geometryRow001_simplexId_read geometryRow001_vertexIds_read
    geometryRow001_physicalVolume_read geometryRow001_meanGap_read
    geometryRow001_factorMaxima_read geometryRow001_gapWeightedMeans_read
    geometryRow001_jensenBound_read geometryRow001_floor_text_read geometryRow001_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_001_original_decoder_complete"
  err.flush

#print axioms geometryRow001_simplexId_read
#print axioms geometryRow001_vertexIds_read
#print axioms geometryRow001_physicalVolume_field
#print axioms geometryRow001_physicalVolume_numerator_no_slash
#print axioms geometryRow001_physicalVolume_numerator_parse
#print axioms geometryRow001_physicalVolume_denominator_parse
#print axioms geometryRow001_physicalVolume_denominator_nonzero
#print axioms geometryRow001_physicalVolume_parse
#print axioms geometryRow001_physicalVolume_read
#print axioms geometryRow001_meanGap_field
#print axioms geometryRow001_meanGap_numerator_no_slash
#print axioms geometryRow001_meanGap_numerator_parse
#print axioms geometryRow001_meanGap_denominator_parse
#print axioms geometryRow001_meanGap_denominator_nonzero
#print axioms geometryRow001_meanGap_parse
#print axioms geometryRow001_meanGap_read
#print axioms geometryRow001_jensenBound_field
#print axioms geometryRow001_jensenBound_numerator_no_slash
#print axioms geometryRow001_jensenBound_numerator_parse
#print axioms geometryRow001_jensenBound_denominator_parse
#print axioms geometryRow001_jensenBound_denominator_nonzero
#print axioms geometryRow001_jensenBound_parse
#print axioms geometryRow001_jensenBound_read
#print axioms geometryRow001_factorMaxima_read
#print axioms geometryRow001_gapWeightedMeans_read
#print axioms geometryRow001_floor_text_read
#print axioms geometryRow001_floor_chars_parse
#print axioms geometryRow001_floor_parse
#print axioms decode_geometry_Rows_001

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
