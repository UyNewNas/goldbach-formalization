import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows069

/-! Original simplices typed block 70, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson138 : SourceJson :=
  (SimplicesBlock070.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped138 : GeometryRow :=
  { simplexId := 138,
    vertexIds := #[39, 33, 31, 24, 23, 21, 20, 16, 15],
    physicalVolume := ((126434239103502781078807139018324057262931 : ℚ) / (147493796051331072000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((608723 : ℚ) / (5868000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((2484379 : ℚ) / (54000000 : ℚ)), ((2484367 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((41955881546477 : ℚ) / (611347800000000 : ℚ)), ((42070035370667 : ℚ) / (611347800000000 : ℚ)), ((813329127163817 : ℚ) / (5502130200000000 : ℚ)), ((11485792478401 : ℚ) / (110042604000000 : ℚ)), ((724170906547 : ℚ) / (13755325500000 : ℚ)), ((51705458621669 : ℚ) / (1100426040000000 : ℚ)), ((240887869611 : ℚ) / (5362700000000 : ℚ)), ((6783694313111 : ℚ) / (152836950000000 : ℚ)), ((8929879391641 : ℚ) / (203782600000000 : ℚ)), ((26789475148843 : ℚ) / (611347800000000 : ℚ))],
    jensenBound := ((41469305888057683882811406132160847088862253657351107506789189981518628503598751438923824235815437500000000000000 : ℚ) / (80452627161822887034477676443360407457899264068157452374563816901629834737915709128398527154691041854702868268427626839874298129989 : ℚ)),
    jensenFloorQ96 := (40838155597 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_simplexId_before"
  err.flush

theorem geometryRow138_simplexId_read :
    geometryRowsJson138.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped138.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_vertexIds_before"
  err.flush

theorem geometryRow138_vertexIds_read :
    geometryRowsJson138.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped138.vertexIds := by decide +kernel

noncomputable def geometryRow138_physicalVolumeNumeratorChars : List Char := ['1', '2', '6', '4', '3', '4', '2', '3', '9', '1', '0', '3', '5', '0', '2', '7', '8', '1', '0', '7', '8', '8', '0', '7', '1', '3', '9', '0', '1', '8', '3', '2', '4', '0', '5', '7', '2', '6', '2', '9', '3', '1']
noncomputable def geometryRow138_physicalVolumeDenominatorChars : List Char := ['1', '4', '7', '4', '9', '3', '7', '9', '6', '0', '5', '1', '3', '3', '1', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow138_physicalVolumeText : String := String.ofList (geometryRow138_physicalVolumeNumeratorChars ++ '/' :: geometryRow138_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_physicalVolume_before_field"
  err.flush

theorem geometryRow138_physicalVolume_field :
    geometryRowsJson138.getObjVal? "physical_volume" = .ok (.str geometryRow138_physicalVolumeText) := by rfl

theorem geometryRow138_physicalVolume_numerator_no_slash :
    geometryRow138_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow138_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow138_physicalVolumeNumeratorChars = some (126434239103502781078807139018324057262931 : Int) := by decide +kernel

theorem geometryRow138_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow138_physicalVolumeDenominatorChars = some (147493796051331072000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow138_physicalVolume_denominator_nonzero : (147493796051331072000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow138_physicalVolume_parse :
    parseRational geometryRow138_physicalVolumeText = .ok geometryRowsTyped138.physicalVolume :=
  original_rational_fraction_of_chars geometryRow138_physicalVolumeNumeratorChars geometryRow138_physicalVolumeDenominatorChars
    (126434239103502781078807139018324057262931 : Int) (147493796051331072000000000000000000000000000000000000000000000000000 : Int)
    geometryRow138_physicalVolume_numerator_no_slash geometryRow138_physicalVolume_numerator_parse
    geometryRow138_physicalVolume_denominator_parse geometryRow138_physicalVolume_denominator_nonzero

theorem geometryRow138_physicalVolume_read :
    rationalField geometryRowsJson138 "physical_volume" = .ok geometryRowsTyped138.physicalVolume :=
  original_rationalField_of_string geometryRowsJson138 "physical_volume" geometryRow138_physicalVolumeText
    geometryRowsTyped138.physicalVolume geometryRow138_physicalVolume_field geometryRow138_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_physicalVolume_complete"
  err.flush

noncomputable def geometryRow138_meanGapNumeratorChars : List Char := ['6', '0', '8', '7', '2', '3']
noncomputable def geometryRow138_meanGapDenominatorChars : List Char := ['5', '8', '6', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow138_meanGapText : String := String.ofList (geometryRow138_meanGapNumeratorChars ++ '/' :: geometryRow138_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_meanGap_before_field"
  err.flush

theorem geometryRow138_meanGap_field :
    geometryRowsJson138.getObjVal? "mean_gap" = .ok (.str geometryRow138_meanGapText) := by rfl

theorem geometryRow138_meanGap_numerator_no_slash :
    geometryRow138_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow138_meanGap_numerator_parse :
    SourceJson.intChars geometryRow138_meanGapNumeratorChars = some (608723 : Int) := by decide +kernel

theorem geometryRow138_meanGap_denominator_parse :
    SourceJson.intChars geometryRow138_meanGapDenominatorChars = some (5868000000 : Int) := by decide +kernel

theorem geometryRow138_meanGap_denominator_nonzero : (5868000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow138_meanGap_parse :
    parseRational geometryRow138_meanGapText = .ok geometryRowsTyped138.meanGap :=
  original_rational_fraction_of_chars geometryRow138_meanGapNumeratorChars geometryRow138_meanGapDenominatorChars
    (608723 : Int) (5868000000 : Int)
    geometryRow138_meanGap_numerator_no_slash geometryRow138_meanGap_numerator_parse
    geometryRow138_meanGap_denominator_parse geometryRow138_meanGap_denominator_nonzero

theorem geometryRow138_meanGap_read :
    rationalField geometryRowsJson138 "mean_gap" = .ok geometryRowsTyped138.meanGap :=
  original_rationalField_of_string geometryRowsJson138 "mean_gap" geometryRow138_meanGapText
    geometryRowsTyped138.meanGap geometryRow138_meanGap_field geometryRow138_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_meanGap_complete"
  err.flush

noncomputable def geometryRow138_jensenBoundNumeratorChars : List Char := ['4', '1', '4', '6', '9', '3', '0', '5', '8', '8', '8', '0', '5', '7', '6', '8', '3', '8', '8', '2', '8', '1', '1', '4', '0', '6', '1', '3', '2', '1', '6', '0', '8', '4', '7', '0', '8', '8', '8', '6', '2', '2', '5', '3', '6', '5', '7', '3', '5', '1', '1', '0', '7', '5', '0', '6', '7', '8', '9', '1', '8', '9', '9', '8', '1', '5', '1', '8', '6', '2', '8', '5', '0', '3', '5', '9', '8', '7', '5', '1', '4', '3', '8', '9', '2', '3', '8', '2', '4', '2', '3', '5', '8', '1', '5', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow138_jensenBoundDenominatorChars : List Char := ['8', '0', '4', '5', '2', '6', '2', '7', '1', '6', '1', '8', '2', '2', '8', '8', '7', '0', '3', '4', '4', '7', '7', '6', '7', '6', '4', '4', '3', '3', '6', '0', '4', '0', '7', '4', '5', '7', '8', '9', '9', '2', '6', '4', '0', '6', '8', '1', '5', '7', '4', '5', '2', '3', '7', '4', '5', '6', '3', '8', '1', '6', '9', '0', '1', '6', '2', '9', '8', '3', '4', '7', '3', '7', '9', '1', '5', '7', '0', '9', '1', '2', '8', '3', '9', '8', '5', '2', '7', '1', '5', '4', '6', '9', '1', '0', '4', '1', '8', '5', '4', '7', '0', '2', '8', '6', '8', '2', '6', '8', '4', '2', '7', '6', '2', '6', '8', '3', '9', '8', '7', '4', '2', '9', '8', '1', '2', '9', '9', '8', '9']
noncomputable def geometryRow138_jensenBoundText : String := String.ofList (geometryRow138_jensenBoundNumeratorChars ++ '/' :: geometryRow138_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_jensenBound_before_field"
  err.flush

theorem geometryRow138_jensenBound_field :
    geometryRowsJson138.getObjVal? "jensen_bound" = .ok (.str geometryRow138_jensenBoundText) := by rfl

theorem geometryRow138_jensenBound_numerator_no_slash :
    geometryRow138_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow138_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow138_jensenBoundNumeratorChars = some (41469305888057683882811406132160847088862253657351107506789189981518628503598751438923824235815437500000000000000 : Int) := by decide +kernel

theorem geometryRow138_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow138_jensenBoundDenominatorChars = some (80452627161822887034477676443360407457899264068157452374563816901629834737915709128398527154691041854702868268427626839874298129989 : Int) := by decide +kernel

theorem geometryRow138_jensenBound_denominator_nonzero : (80452627161822887034477676443360407457899264068157452374563816901629834737915709128398527154691041854702868268427626839874298129989 : Int) ≠ 0 := by decide +kernel

theorem geometryRow138_jensenBound_parse :
    parseRational geometryRow138_jensenBoundText = .ok geometryRowsTyped138.jensenBound :=
  original_rational_fraction_of_chars geometryRow138_jensenBoundNumeratorChars geometryRow138_jensenBoundDenominatorChars
    (41469305888057683882811406132160847088862253657351107506789189981518628503598751438923824235815437500000000000000 : Int) (80452627161822887034477676443360407457899264068157452374563816901629834737915709128398527154691041854702868268427626839874298129989 : Int)
    geometryRow138_jensenBound_numerator_no_slash geometryRow138_jensenBound_numerator_parse
    geometryRow138_jensenBound_denominator_parse geometryRow138_jensenBound_denominator_nonzero

theorem geometryRow138_jensenBound_read :
    rationalField geometryRowsJson138 "jensen_bound" = .ok geometryRowsTyped138.jensenBound :=
  original_rationalField_of_string geometryRowsJson138 "jensen_bound" geometryRow138_jensenBoundText
    geometryRowsTyped138.jensenBound geometryRow138_jensenBound_field geometryRow138_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_factorMaxima_before"
  err.flush

theorem geometryRow138_factorMaxima_read :
    rationalArrayField geometryRowsJson138 "factor_maxima" = .ok geometryRowsTyped138.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_gapWeightedMeans_before"
  err.flush

theorem geometryRow138_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson138 "gap_weighted_means" = .ok geometryRowsTyped138.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow138_floorChars : List Char := ['4', '0', '8', '3', '8', '1', '5', '5', '5', '9', '7']
noncomputable def geometryRow138_floorText : String := String.ofList geometryRow138_floorChars

theorem geometryRow138_floor_text_read :
    geometryRowsJson138.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow138_floorText := by rfl

theorem geometryRow138_floor_chars_parse :
    SourceJson.intChars geometryRow138_floorChars = some (40838155597 : Int) := by decide +kernel

theorem geometryRow138_floor_parse :
    parseInteger geometryRow138_floorText = .ok geometryRowsTyped138.jensenFloorQ96 := by
  simp only [geometryRow138_floorText, parseInteger, String.toList_ofList, geometryRow138_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_138 :
    decodeGeometryRow geometryRowsJson138 = .ok geometryRowsTyped138 :=
  original_geometryRow_of_fields geometryRowsJson138 geometryRowsTyped138 geometryRow138_floorText
    geometryRow138_simplexId_read geometryRow138_vertexIds_read
    geometryRow138_physicalVolume_read geometryRow138_meanGap_read
    geometryRow138_factorMaxima_read geometryRow138_gapWeightedMeans_read
    geometryRow138_jensenBound_read geometryRow138_floor_text_read geometryRow138_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_138_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson139 : SourceJson :=
  (SimplicesBlock070.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped139 : GeometryRow :=
  { simplexId := 139,
    vertexIds := #[39, 33, 31, 24, 23, 21, 20, 19, 15],
    physicalVolume := ((1643904323013621919587460448200513936295959 : ℚ) / (1749473079563521622016000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((91924997 : ℚ) / (407826000000 : ℚ)),
    factorMaxima := #[((2484387 : ℚ) / (28000000 : ℚ)), ((2484387 : ℚ) / (28000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1921543 : ℚ) / (30000000 : ℚ)), ((1115573 : ℚ) / (21600000 : ℚ)), ((2859151 : ℚ) / (57000000 : ℚ)), ((10827881 : ℚ) / (228000000 : ℚ)), ((205 : ℚ) / (4448 : ℚ)), ((2484343 : ℚ) / (54000000 : ℚ))],
    gapWeightedMeans := #[((34124261960992871064029 : ℚ) / (498609070892742600000000 : ℚ)), ((4284538178366790278203 : ℚ) / (62326133861592825000000 : ℚ)), ((12286264718499171237251 : ℚ) / (83101511815457100000000 : ℚ)), ((31331746574070591030847 : ℚ) / (299165442535645560000000 : ℚ)), ((350353964112740647709 : ℚ) / (6648120945236568000000 : ℚ)), ((776577802622826979079 : ℚ) / (16620302363091420000000 : ℚ)), ((1767651681922533253463 : ℚ) / (39363874017848100000000 : ℚ)), ((2074126272820751416637 : ℚ) / (46744600396194618750000 : ℚ)), ((16394493229967357804977 : ℚ) / (373956803169556950000000 : ℚ)), ((65409284512706190541453 : ℚ) / (1495827212678227800000000 : ℚ))],
    jensenBound := ((5726184348623265724301994725091623677728971307311464075387284023905248762967578554285397564417875887557135881291807018200635273840433718923992862218353445529729873250650527067780243606567382812500000000 : ℚ) / (4631159010296965573131070543718806835058875448339461976782143553508095222599296509559000507846209721183974698470794498360297896395642313983999936140074179331143739045338462070197173136474331191550869896179543841033563 : ℚ)),
    jensenFloorQ96 := (97961452662423 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_simplexId_before"
  err.flush

theorem geometryRow139_simplexId_read :
    geometryRowsJson139.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped139.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_vertexIds_before"
  err.flush

theorem geometryRow139_vertexIds_read :
    geometryRowsJson139.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped139.vertexIds := by decide +kernel

noncomputable def geometryRow139_physicalVolumeNumeratorChars : List Char := ['1', '6', '4', '3', '9', '0', '4', '3', '2', '3', '0', '1', '3', '6', '2', '1', '9', '1', '9', '5', '8', '7', '4', '6', '0', '4', '4', '8', '2', '0', '0', '5', '1', '3', '9', '3', '6', '2', '9', '5', '9', '5', '9']
noncomputable def geometryRow139_physicalVolumeDenominatorChars : List Char := ['1', '7', '4', '9', '4', '7', '3', '0', '7', '9', '5', '6', '3', '5', '2', '1', '6', '2', '2', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow139_physicalVolumeText : String := String.ofList (geometryRow139_physicalVolumeNumeratorChars ++ '/' :: geometryRow139_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_physicalVolume_before_field"
  err.flush

theorem geometryRow139_physicalVolume_field :
    geometryRowsJson139.getObjVal? "physical_volume" = .ok (.str geometryRow139_physicalVolumeText) := by rfl

theorem geometryRow139_physicalVolume_numerator_no_slash :
    geometryRow139_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow139_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow139_physicalVolumeNumeratorChars = some (1643904323013621919587460448200513936295959 : Int) := by decide +kernel

theorem geometryRow139_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow139_physicalVolumeDenominatorChars = some (1749473079563521622016000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow139_physicalVolume_denominator_nonzero : (1749473079563521622016000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow139_physicalVolume_parse :
    parseRational geometryRow139_physicalVolumeText = .ok geometryRowsTyped139.physicalVolume :=
  original_rational_fraction_of_chars geometryRow139_physicalVolumeNumeratorChars geometryRow139_physicalVolumeDenominatorChars
    (1643904323013621919587460448200513936295959 : Int) (1749473079563521622016000000000000000000000000000000000000000000000 : Int)
    geometryRow139_physicalVolume_numerator_no_slash geometryRow139_physicalVolume_numerator_parse
    geometryRow139_physicalVolume_denominator_parse geometryRow139_physicalVolume_denominator_nonzero

theorem geometryRow139_physicalVolume_read :
    rationalField geometryRowsJson139 "physical_volume" = .ok geometryRowsTyped139.physicalVolume :=
  original_rationalField_of_string geometryRowsJson139 "physical_volume" geometryRow139_physicalVolumeText
    geometryRowsTyped139.physicalVolume geometryRow139_physicalVolume_field geometryRow139_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_physicalVolume_complete"
  err.flush

noncomputable def geometryRow139_meanGapNumeratorChars : List Char := ['9', '1', '9', '2', '4', '9', '9', '7']
noncomputable def geometryRow139_meanGapDenominatorChars : List Char := ['4', '0', '7', '8', '2', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow139_meanGapText : String := String.ofList (geometryRow139_meanGapNumeratorChars ++ '/' :: geometryRow139_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_meanGap_before_field"
  err.flush

theorem geometryRow139_meanGap_field :
    geometryRowsJson139.getObjVal? "mean_gap" = .ok (.str geometryRow139_meanGapText) := by rfl

theorem geometryRow139_meanGap_numerator_no_slash :
    geometryRow139_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow139_meanGap_numerator_parse :
    SourceJson.intChars geometryRow139_meanGapNumeratorChars = some (91924997 : Int) := by decide +kernel

theorem geometryRow139_meanGap_denominator_parse :
    SourceJson.intChars geometryRow139_meanGapDenominatorChars = some (407826000000 : Int) := by decide +kernel

theorem geometryRow139_meanGap_denominator_nonzero : (407826000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow139_meanGap_parse :
    parseRational geometryRow139_meanGapText = .ok geometryRowsTyped139.meanGap :=
  original_rational_fraction_of_chars geometryRow139_meanGapNumeratorChars geometryRow139_meanGapDenominatorChars
    (91924997 : Int) (407826000000 : Int)
    geometryRow139_meanGap_numerator_no_slash geometryRow139_meanGap_numerator_parse
    geometryRow139_meanGap_denominator_parse geometryRow139_meanGap_denominator_nonzero

theorem geometryRow139_meanGap_read :
    rationalField geometryRowsJson139 "mean_gap" = .ok geometryRowsTyped139.meanGap :=
  original_rationalField_of_string geometryRowsJson139 "mean_gap" geometryRow139_meanGapText
    geometryRowsTyped139.meanGap geometryRow139_meanGap_field geometryRow139_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_meanGap_complete"
  err.flush

noncomputable def geometryRow139_jensenBoundNumeratorChars : List Char := ['5', '7', '2', '6', '1', '8', '4', '3', '4', '8', '6', '2', '3', '2', '6', '5', '7', '2', '4', '3', '0', '1', '9', '9', '4', '7', '2', '5', '0', '9', '1', '6', '2', '3', '6', '7', '7', '7', '2', '8', '9', '7', '1', '3', '0', '7', '3', '1', '1', '4', '6', '4', '0', '7', '5', '3', '8', '7', '2', '8', '4', '0', '2', '3', '9', '0', '5', '2', '4', '8', '7', '6', '2', '9', '6', '7', '5', '7', '8', '5', '5', '4', '2', '8', '5', '3', '9', '7', '5', '6', '4', '4', '1', '7', '8', '7', '5', '8', '8', '7', '5', '5', '7', '1', '3', '5', '8', '8', '1', '2', '9', '1', '8', '0', '7', '0', '1', '8', '2', '0', '0', '6', '3', '5', '2', '7', '3', '8', '4', '0', '4', '3', '3', '7', '1', '8', '9', '2', '3', '9', '9', '2', '8', '6', '2', '2', '1', '8', '3', '5', '3', '4', '4', '5', '5', '2', '9', '7', '2', '9', '8', '7', '3', '2', '5', '0', '6', '5', '0', '5', '2', '7', '0', '6', '7', '7', '8', '0', '2', '4', '3', '6', '0', '6', '5', '6', '7', '3', '8', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow139_jensenBoundDenominatorChars : List Char := ['4', '6', '3', '1', '1', '5', '9', '0', '1', '0', '2', '9', '6', '9', '6', '5', '5', '7', '3', '1', '3', '1', '0', '7', '0', '5', '4', '3', '7', '1', '8', '8', '0', '6', '8', '3', '5', '0', '5', '8', '8', '7', '5', '4', '4', '8', '3', '3', '9', '4', '6', '1', '9', '7', '6', '7', '8', '2', '1', '4', '3', '5', '5', '3', '5', '0', '8', '0', '9', '5', '2', '2', '2', '5', '9', '9', '2', '9', '6', '5', '0', '9', '5', '5', '9', '0', '0', '0', '5', '0', '7', '8', '4', '6', '2', '0', '9', '7', '2', '1', '1', '8', '3', '9', '7', '4', '6', '9', '8', '4', '7', '0', '7', '9', '4', '4', '9', '8', '3', '6', '0', '2', '9', '7', '8', '9', '6', '3', '9', '5', '6', '4', '2', '3', '1', '3', '9', '8', '3', '9', '9', '9', '9', '3', '6', '1', '4', '0', '0', '7', '4', '1', '7', '9', '3', '3', '1', '1', '4', '3', '7', '3', '9', '0', '4', '5', '3', '3', '8', '4', '6', '2', '0', '7', '0', '1', '9', '7', '1', '7', '3', '1', '3', '6', '4', '7', '4', '3', '3', '1', '1', '9', '1', '5', '5', '0', '8', '6', '9', '8', '9', '6', '1', '7', '9', '5', '4', '3', '8', '4', '1', '0', '3', '3', '5', '6', '3']
noncomputable def geometryRow139_jensenBoundText : String := String.ofList (geometryRow139_jensenBoundNumeratorChars ++ '/' :: geometryRow139_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_jensenBound_before_field"
  err.flush

theorem geometryRow139_jensenBound_field :
    geometryRowsJson139.getObjVal? "jensen_bound" = .ok (.str geometryRow139_jensenBoundText) := by rfl

theorem geometryRow139_jensenBound_numerator_no_slash :
    geometryRow139_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow139_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow139_jensenBoundNumeratorChars = some (5726184348623265724301994725091623677728971307311464075387284023905248762967578554285397564417875887557135881291807018200635273840433718923992862218353445529729873250650527067780243606567382812500000000 : Int) := by decide +kernel

theorem geometryRow139_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow139_jensenBoundDenominatorChars = some (4631159010296965573131070543718806835058875448339461976782143553508095222599296509559000507846209721183974698470794498360297896395642313983999936140074179331143739045338462070197173136474331191550869896179543841033563 : Int) := by decide +kernel

theorem geometryRow139_jensenBound_denominator_nonzero : (4631159010296965573131070543718806835058875448339461976782143553508095222599296509559000507846209721183974698470794498360297896395642313983999936140074179331143739045338462070197173136474331191550869896179543841033563 : Int) ≠ 0 := by decide +kernel

theorem geometryRow139_jensenBound_parse :
    parseRational geometryRow139_jensenBoundText = .ok geometryRowsTyped139.jensenBound :=
  original_rational_fraction_of_chars geometryRow139_jensenBoundNumeratorChars geometryRow139_jensenBoundDenominatorChars
    (5726184348623265724301994725091623677728971307311464075387284023905248762967578554285397564417875887557135881291807018200635273840433718923992862218353445529729873250650527067780243606567382812500000000 : Int) (4631159010296965573131070543718806835058875448339461976782143553508095222599296509559000507846209721183974698470794498360297896395642313983999936140074179331143739045338462070197173136474331191550869896179543841033563 : Int)
    geometryRow139_jensenBound_numerator_no_slash geometryRow139_jensenBound_numerator_parse
    geometryRow139_jensenBound_denominator_parse geometryRow139_jensenBound_denominator_nonzero

theorem geometryRow139_jensenBound_read :
    rationalField geometryRowsJson139 "jensen_bound" = .ok geometryRowsTyped139.jensenBound :=
  original_rationalField_of_string geometryRowsJson139 "jensen_bound" geometryRow139_jensenBoundText
    geometryRowsTyped139.jensenBound geometryRow139_jensenBound_field geometryRow139_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_factorMaxima_before"
  err.flush

theorem geometryRow139_factorMaxima_read :
    rationalArrayField geometryRowsJson139 "factor_maxima" = .ok geometryRowsTyped139.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_gapWeightedMeans_before"
  err.flush

theorem geometryRow139_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson139 "gap_weighted_means" = .ok geometryRowsTyped139.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow139_floorChars : List Char := ['9', '7', '9', '6', '1', '4', '5', '2', '6', '6', '2', '4', '2', '3']
noncomputable def geometryRow139_floorText : String := String.ofList geometryRow139_floorChars

theorem geometryRow139_floor_text_read :
    geometryRowsJson139.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow139_floorText := by rfl

theorem geometryRow139_floor_chars_parse :
    SourceJson.intChars geometryRow139_floorChars = some (97961452662423 : Int) := by decide +kernel

theorem geometryRow139_floor_parse :
    parseInteger geometryRow139_floorText = .ok geometryRowsTyped139.jensenFloorQ96 := by
  simp only [geometryRow139_floorText, parseInteger, String.toList_ofList, geometryRow139_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_139 :
    decodeGeometryRow geometryRowsJson139 = .ok geometryRowsTyped139 :=
  original_geometryRow_of_fields geometryRowsJson139 geometryRowsTyped139 geometryRow139_floorText
    geometryRow139_simplexId_read geometryRow139_vertexIds_read
    geometryRow139_physicalVolume_read geometryRow139_meanGap_read
    geometryRow139_factorMaxima_read geometryRow139_gapWeightedMeans_read
    geometryRow139_jensenBound_read geometryRow139_floor_text_read geometryRow139_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_139_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock070 : List SourceJson := [geometryRowsJson138, geometryRowsJson139]
noncomputable def geometryRowsTypedBlock070 : List (GeometryRow) := [geometryRowsTyped138, geometryRowsTyped139]
noncomputable def geometryRowsTypedThroughBlock070 : List (GeometryRow) := geometryRowsTypedThroughBlock069 ++ geometryRowsTypedBlock070

theorem geometry_Rows_block_070_push_eq (acc : List SourceJson) :
    SimplicesBlock070.blockPush acc = [geometryRowsJson139, geometryRowsJson138] ++ acc := by rfl

theorem geometry_Rows_block_070_reverse (acc : List SourceJson) :
    (SimplicesBlock070.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock070 := by
  rw [geometry_Rows_block_070_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_070 :
    geometryRowsJsonBlock070.mapM decodeGeometryRow = .ok geometryRowsTypedBlock070 := by
  simp only [geometryRowsJsonBlock070, geometryRowsTypedBlock070, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_138, decode_geometry_Rows_139]
  rfl

theorem decode_geometry_Rows_through_block_070 :
    SimplicesValue.arrayAcc071.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock070 := by
  change (SimplicesBlock070.blockPush SimplicesValue.arrayAcc070).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_070_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_069, decode_geometry_Rows_block_070]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_070_complete"
  err.flush

#print axioms geometryRow138_simplexId_read
#print axioms geometryRow138_vertexIds_read
#print axioms geometryRow138_physicalVolume_field
#print axioms geometryRow138_physicalVolume_numerator_no_slash
#print axioms geometryRow138_physicalVolume_numerator_parse
#print axioms geometryRow138_physicalVolume_denominator_parse
#print axioms geometryRow138_physicalVolume_denominator_nonzero
#print axioms geometryRow138_physicalVolume_parse
#print axioms geometryRow138_physicalVolume_read
#print axioms geometryRow138_meanGap_field
#print axioms geometryRow138_meanGap_numerator_no_slash
#print axioms geometryRow138_meanGap_numerator_parse
#print axioms geometryRow138_meanGap_denominator_parse
#print axioms geometryRow138_meanGap_denominator_nonzero
#print axioms geometryRow138_meanGap_parse
#print axioms geometryRow138_meanGap_read
#print axioms geometryRow138_jensenBound_field
#print axioms geometryRow138_jensenBound_numerator_no_slash
#print axioms geometryRow138_jensenBound_numerator_parse
#print axioms geometryRow138_jensenBound_denominator_parse
#print axioms geometryRow138_jensenBound_denominator_nonzero
#print axioms geometryRow138_jensenBound_parse
#print axioms geometryRow138_jensenBound_read
#print axioms geometryRow138_factorMaxima_read
#print axioms geometryRow138_gapWeightedMeans_read
#print axioms geometryRow138_floor_text_read
#print axioms geometryRow138_floor_chars_parse
#print axioms geometryRow138_floor_parse
#print axioms decode_geometry_Rows_138
#print axioms geometryRow139_simplexId_read
#print axioms geometryRow139_vertexIds_read
#print axioms geometryRow139_physicalVolume_field
#print axioms geometryRow139_physicalVolume_numerator_no_slash
#print axioms geometryRow139_physicalVolume_numerator_parse
#print axioms geometryRow139_physicalVolume_denominator_parse
#print axioms geometryRow139_physicalVolume_denominator_nonzero
#print axioms geometryRow139_physicalVolume_parse
#print axioms geometryRow139_physicalVolume_read
#print axioms geometryRow139_meanGap_field
#print axioms geometryRow139_meanGap_numerator_no_slash
#print axioms geometryRow139_meanGap_numerator_parse
#print axioms geometryRow139_meanGap_denominator_parse
#print axioms geometryRow139_meanGap_denominator_nonzero
#print axioms geometryRow139_meanGap_parse
#print axioms geometryRow139_meanGap_read
#print axioms geometryRow139_jensenBound_field
#print axioms geometryRow139_jensenBound_numerator_no_slash
#print axioms geometryRow139_jensenBound_numerator_parse
#print axioms geometryRow139_jensenBound_denominator_parse
#print axioms geometryRow139_jensenBound_denominator_nonzero
#print axioms geometryRow139_jensenBound_parse
#print axioms geometryRow139_jensenBound_read
#print axioms geometryRow139_factorMaxima_read
#print axioms geometryRow139_gapWeightedMeans_read
#print axioms geometryRow139_floor_text_read
#print axioms geometryRow139_floor_chars_parse
#print axioms geometryRow139_floor_parse
#print axioms decode_geometry_Rows_139
#print axioms geometry_Rows_block_070_push_eq
#print axioms geometry_Rows_block_070_reverse
#print axioms decode_geometry_Rows_block_070
#print axioms decode_geometry_Rows_through_block_070

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
