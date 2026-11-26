import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry01DirectSimplicesValue
import ImbalancedChen.P2OriginalSaving19Geometry01DirectDecodedRows008

/-! Original simplices typed block 9, keeping exact original record order.
The original cell01 JSON, original ArchiveSchema and original rational guards
are preserved. Host quotations do not establish decoding or geometry validity. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry01DirectParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson018 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped018 : GeometryRow :=
  { simplexId := 18,
    vertexIds := #[39, 35, 29, 28, 26, 17, 6, 2, 0],
    physicalVolume := ((113652453551691414881788029823570632433468474889 : ℚ) / (4613669539282944000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((1109351 : ℚ) / (28000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((281392114243 : ℚ) / (3393600000000 : ℚ)), ((1994737839541 : ℚ) / (23755200000000 : ℚ)), ((344234565911 : ℚ) / (2375520000000 : ℚ)), ((8324679514373 : ℚ) / (71265600000000 : ℚ)), ((538691704503 : ℚ) / (7918400000000 : ℚ)), ((557098621181 : ℚ) / (11877600000000 : ℚ)), ((1175266833119 : ℚ) / (31673600000000 : ℚ)), ((3328651986887 : ℚ) / (95020800000000 : ℚ)), ((807516265303 : ℚ) / (23755200000000 : ℚ)), ((2152458233197 : ℚ) / (71265600000000 : ℚ))],
    jensenBound := ((11414190773461616520479202163518026094415611542372029257203864473493284523194976352337920000000000000000000000 : ℚ) / (99464719970221006793886505510505353730746775540617167226925268230116410632352147648301969386654527735848750691863498637 : ℚ)),
    jensenFloorQ96 := (9091920852332181310 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_simplexId_before"
  err.flush

theorem geometryRow018_simplexId_read :
    geometryRowsJson018.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped018.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_vertexIds_before"
  err.flush

theorem geometryRow018_vertexIds_read :
    geometryRowsJson018.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped018.vertexIds := by decide +kernel

noncomputable def geometryRow018_physicalVolumeNumeratorChars : List Char := ['1', '1', '3', '6', '5', '2', '4', '5', '3', '5', '5', '1', '6', '9', '1', '4', '1', '4', '8', '8', '1', '7', '8', '8', '0', '2', '9', '8', '2', '3', '5', '7', '0', '6', '3', '2', '4', '3', '3', '4', '6', '8', '4', '7', '4', '8', '8', '9']
noncomputable def geometryRow018_physicalVolumeDenominatorChars : List Char := ['4', '6', '1', '3', '6', '6', '9', '5', '3', '9', '2', '8', '2', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_physicalVolumeText : String := String.ofList (geometryRow018_physicalVolumeNumeratorChars ++ '/' :: geometryRow018_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_physicalVolume_before_field"
  err.flush

theorem geometryRow018_physicalVolume_field :
    geometryRowsJson018.getObjVal? "physical_volume" = .ok (.str geometryRow018_physicalVolumeText) := by rfl

theorem geometryRow018_physicalVolume_numerator_no_slash :
    geometryRow018_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeNumeratorChars = some (113652453551691414881788029823570632433468474889 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeDenominatorChars = some (4613669539282944000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_nonzero : (4613669539282944000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_physicalVolume_parse :
    parseRational geometryRow018_physicalVolumeText = .ok geometryRowsTyped018.physicalVolume :=
  original_rational_fraction_of_chars geometryRow018_physicalVolumeNumeratorChars geometryRow018_physicalVolumeDenominatorChars
    (113652453551691414881788029823570632433468474889 : Int) (4613669539282944000000000000000000000000000000000000000000000000000 : Int)
    geometryRow018_physicalVolume_numerator_no_slash geometryRow018_physicalVolume_numerator_parse
    geometryRow018_physicalVolume_denominator_parse geometryRow018_physicalVolume_denominator_nonzero

theorem geometryRow018_physicalVolume_read :
    rationalField geometryRowsJson018 "physical_volume" = .ok geometryRowsTyped018.physicalVolume :=
  original_rationalField_of_string geometryRowsJson018 "physical_volume" geometryRow018_physicalVolumeText
    geometryRowsTyped018.physicalVolume geometryRow018_physicalVolume_field geometryRow018_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_physicalVolume_complete"
  err.flush

noncomputable def geometryRow018_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow018_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_meanGapText : String := String.ofList (geometryRow018_meanGapNumeratorChars ++ '/' :: geometryRow018_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_meanGap_before_field"
  err.flush

theorem geometryRow018_meanGap_field :
    geometryRowsJson018.getObjVal? "mean_gap" = .ok (.str geometryRow018_meanGapText) := by rfl

theorem geometryRow018_meanGap_numerator_no_slash :
    geometryRow018_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_meanGap_numerator_parse :
    SourceJson.intChars geometryRow018_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_parse :
    SourceJson.intChars geometryRow018_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_meanGap_parse :
    parseRational geometryRow018_meanGapText = .ok geometryRowsTyped018.meanGap :=
  original_rational_fraction_of_chars geometryRow018_meanGapNumeratorChars geometryRow018_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow018_meanGap_numerator_no_slash geometryRow018_meanGap_numerator_parse
    geometryRow018_meanGap_denominator_parse geometryRow018_meanGap_denominator_nonzero

theorem geometryRow018_meanGap_read :
    rationalField geometryRowsJson018 "mean_gap" = .ok geometryRowsTyped018.meanGap :=
  original_rationalField_of_string geometryRowsJson018 "mean_gap" geometryRow018_meanGapText
    geometryRowsTyped018.meanGap geometryRow018_meanGap_field geometryRow018_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_meanGap_complete"
  err.flush

noncomputable def geometryRow018_jensenBoundNumeratorChars : List Char := ['1', '1', '4', '1', '4', '1', '9', '0', '7', '7', '3', '4', '6', '1', '6', '1', '6', '5', '2', '0', '4', '7', '9', '2', '0', '2', '1', '6', '3', '5', '1', '8', '0', '2', '6', '0', '9', '4', '4', '1', '5', '6', '1', '1', '5', '4', '2', '3', '7', '2', '0', '2', '9', '2', '5', '7', '2', '0', '3', '8', '6', '4', '4', '7', '3', '4', '9', '3', '2', '8', '4', '5', '2', '3', '1', '9', '4', '9', '7', '6', '3', '5', '2', '3', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_jensenBoundDenominatorChars : List Char := ['9', '9', '4', '6', '4', '7', '1', '9', '9', '7', '0', '2', '2', '1', '0', '0', '6', '7', '9', '3', '8', '8', '6', '5', '0', '5', '5', '1', '0', '5', '0', '5', '3', '5', '3', '7', '3', '0', '7', '4', '6', '7', '7', '5', '5', '4', '0', '6', '1', '7', '1', '6', '7', '2', '2', '6', '9', '2', '5', '2', '6', '8', '2', '3', '0', '1', '1', '6', '4', '1', '0', '6', '3', '2', '3', '5', '2', '1', '4', '7', '6', '4', '8', '3', '0', '1', '9', '6', '9', '3', '8', '6', '6', '5', '4', '5', '2', '7', '7', '3', '5', '8', '4', '8', '7', '5', '0', '6', '9', '1', '8', '6', '3', '4', '9', '8', '6', '3', '7']
noncomputable def geometryRow018_jensenBoundText : String := String.ofList (geometryRow018_jensenBoundNumeratorChars ++ '/' :: geometryRow018_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_jensenBound_before_field"
  err.flush

theorem geometryRow018_jensenBound_field :
    geometryRowsJson018.getObjVal? "jensen_bound" = .ok (.str geometryRow018_jensenBoundText) := by rfl

theorem geometryRow018_jensenBound_numerator_no_slash :
    geometryRow018_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow018_jensenBoundNumeratorChars = some (11414190773461616520479202163518026094415611542372029257203864473493284523194976352337920000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow018_jensenBoundDenominatorChars = some (99464719970221006793886505510505353730746775540617167226925268230116410632352147648301969386654527735848750691863498637 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_nonzero : (99464719970221006793886505510505353730746775540617167226925268230116410632352147648301969386654527735848750691863498637 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_jensenBound_parse :
    parseRational geometryRow018_jensenBoundText = .ok geometryRowsTyped018.jensenBound :=
  original_rational_fraction_of_chars geometryRow018_jensenBoundNumeratorChars geometryRow018_jensenBoundDenominatorChars
    (11414190773461616520479202163518026094415611542372029257203864473493284523194976352337920000000000000000000000 : Int) (99464719970221006793886505510505353730746775540617167226925268230116410632352147648301969386654527735848750691863498637 : Int)
    geometryRow018_jensenBound_numerator_no_slash geometryRow018_jensenBound_numerator_parse
    geometryRow018_jensenBound_denominator_parse geometryRow018_jensenBound_denominator_nonzero

theorem geometryRow018_jensenBound_read :
    rationalField geometryRowsJson018 "jensen_bound" = .ok geometryRowsTyped018.jensenBound :=
  original_rationalField_of_string geometryRowsJson018 "jensen_bound" geometryRow018_jensenBoundText
    geometryRowsTyped018.jensenBound geometryRow018_jensenBound_field geometryRow018_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_factorMaxima_before"
  err.flush

theorem geometryRow018_factorMaxima_read :
    rationalArrayField geometryRowsJson018 "factor_maxima" = .ok geometryRowsTyped018.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_gapWeightedMeans_before"
  err.flush

theorem geometryRow018_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson018 "gap_weighted_means" = .ok geometryRowsTyped018.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow018_floorChars : List Char := ['9', '0', '9', '1', '9', '2', '0', '8', '5', '2', '3', '3', '2', '1', '8', '1', '3', '1', '0']
noncomputable def geometryRow018_floorText : String := String.ofList geometryRow018_floorChars

theorem geometryRow018_floor_text_read :
    geometryRowsJson018.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow018_floorText := by rfl

theorem geometryRow018_floor_chars_parse :
    SourceJson.intChars geometryRow018_floorChars = some (9091920852332181310 : Int) := by decide +kernel

theorem geometryRow018_floor_parse :
    parseInteger geometryRow018_floorText = .ok geometryRowsTyped018.jensenFloorQ96 := by
  simp only [geometryRow018_floorText, parseInteger, String.toList_ofList, geometryRow018_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_018 :
    decodeGeometryRow geometryRowsJson018 = .ok geometryRowsTyped018 :=
  original_geometryRow_of_fields geometryRowsJson018 geometryRowsTyped018 geometryRow018_floorText
    geometryRow018_simplexId_read geometryRow018_vertexIds_read
    geometryRow018_physicalVolume_read geometryRow018_meanGap_read
    geometryRow018_factorMaxima_read geometryRow018_gapWeightedMeans_read
    geometryRow018_jensenBound_read geometryRow018_floor_text_read geometryRow018_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_018_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJson019 : SourceJson :=
  (SimplicesBlock009.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped019 : GeometryRow :=
  { simplexId := 19,
    vertexIds := #[39, 35, 29, 28, 26, 7, 6, 2, 0],
    physicalVolume := ((575168027572575513129255467806360673738074619 : ℚ) / (15226632142848000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((515533 : ℚ) / (882000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2784283 : ℚ) / (16800000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((1171847 : ℚ) / (15000000 : ℚ)), ((4546703 : ℚ) / (72000000 : ℚ)), ((4546631 : ℚ) / (96000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((374989 : ℚ) / (9000000 : ℚ)), ((390609 : ℚ) / (10000000 : ℚ))],
    gapWeightedMeans := #[((2787231023 : ℚ) / (33600000000 : ℚ)), ((19758073001 : ℚ) / (235200000000 : ℚ)), ((10191954757 : ℚ) / (70560000000 : ℚ)), ((82086032753 : ℚ) / (705600000000 : ℚ)), ((46873513067 : ℚ) / (705600000000 : ℚ)), ((16943574463 : ℚ) / (352800000000 : ℚ)), ((106327496971 : ℚ) / (2822400000000 : ℚ)), ((100471600561 : ℚ) / (2822400000000 : ℚ)), ((24385819009 : ℚ) / (705600000000 : ℚ)), ((21319661057 : ℚ) / (705600000000 : ℚ))],
    jensenBound := ((34306302753726043937892319491509445468106771523696947524213352361471508480000000000000000000000 : ℚ) / (203227932841185932664725004748727754404505352687438371578611781720463384559430940411537961620919002677429 : ℚ)),
    jensenFloorQ96 := (13374270415670583315 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_simplexId_before"
  err.flush

theorem geometryRow019_simplexId_read :
    geometryRowsJson019.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped019.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_vertexIds_before"
  err.flush

theorem geometryRow019_vertexIds_read :
    geometryRowsJson019.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped019.vertexIds := by decide +kernel

noncomputable def geometryRow019_physicalVolumeNumeratorChars : List Char := ['5', '7', '5', '1', '6', '8', '0', '2', '7', '5', '7', '2', '5', '7', '5', '5', '1', '3', '1', '2', '9', '2', '5', '5', '4', '6', '7', '8', '0', '6', '3', '6', '0', '6', '7', '3', '7', '3', '8', '0', '7', '4', '6', '1', '9']
noncomputable def geometryRow019_physicalVolumeDenominatorChars : List Char := ['1', '5', '2', '2', '6', '6', '3', '2', '1', '4', '2', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_physicalVolumeText : String := String.ofList (geometryRow019_physicalVolumeNumeratorChars ++ '/' :: geometryRow019_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_physicalVolume_before_field"
  err.flush

theorem geometryRow019_physicalVolume_field :
    geometryRowsJson019.getObjVal? "physical_volume" = .ok (.str geometryRow019_physicalVolumeText) := by rfl

theorem geometryRow019_physicalVolume_numerator_no_slash :
    geometryRow019_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeNumeratorChars = some (575168027572575513129255467806360673738074619 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeDenominatorChars = some (15226632142848000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_nonzero : (15226632142848000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_physicalVolume_parse :
    parseRational geometryRow019_physicalVolumeText = .ok geometryRowsTyped019.physicalVolume :=
  original_rational_fraction_of_chars geometryRow019_physicalVolumeNumeratorChars geometryRow019_physicalVolumeDenominatorChars
    (575168027572575513129255467806360673738074619 : Int) (15226632142848000000000000000000000000000000000000000000000000000 : Int)
    geometryRow019_physicalVolume_numerator_no_slash geometryRow019_physicalVolume_numerator_parse
    geometryRow019_physicalVolume_denominator_parse geometryRow019_physicalVolume_denominator_nonzero

theorem geometryRow019_physicalVolume_read :
    rationalField geometryRowsJson019 "physical_volume" = .ok geometryRowsTyped019.physicalVolume :=
  original_rationalField_of_string geometryRowsJson019 "physical_volume" geometryRow019_physicalVolumeText
    geometryRowsTyped019.physicalVolume geometryRow019_physicalVolume_field geometryRow019_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_physicalVolume_complete"
  err.flush

noncomputable def geometryRow019_meanGapNumeratorChars : List Char := ['5', '1', '5', '5', '3', '3']
noncomputable def geometryRow019_meanGapDenominatorChars : List Char := ['8', '8', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_meanGapText : String := String.ofList (geometryRow019_meanGapNumeratorChars ++ '/' :: geometryRow019_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_meanGap_before_field"
  err.flush

theorem geometryRow019_meanGap_field :
    geometryRowsJson019.getObjVal? "mean_gap" = .ok (.str geometryRow019_meanGapText) := by rfl

theorem geometryRow019_meanGap_numerator_no_slash :
    geometryRow019_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_meanGap_numerator_parse :
    SourceJson.intChars geometryRow019_meanGapNumeratorChars = some (515533 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_parse :
    SourceJson.intChars geometryRow019_meanGapDenominatorChars = some (882000000 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_nonzero : (882000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_meanGap_parse :
    parseRational geometryRow019_meanGapText = .ok geometryRowsTyped019.meanGap :=
  original_rational_fraction_of_chars geometryRow019_meanGapNumeratorChars geometryRow019_meanGapDenominatorChars
    (515533 : Int) (882000000 : Int)
    geometryRow019_meanGap_numerator_no_slash geometryRow019_meanGap_numerator_parse
    geometryRow019_meanGap_denominator_parse geometryRow019_meanGap_denominator_nonzero

theorem geometryRow019_meanGap_read :
    rationalField geometryRowsJson019 "mean_gap" = .ok geometryRowsTyped019.meanGap :=
  original_rationalField_of_string geometryRowsJson019 "mean_gap" geometryRow019_meanGapText
    geometryRowsTyped019.meanGap geometryRow019_meanGap_field geometryRow019_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_meanGap_complete"
  err.flush

noncomputable def geometryRow019_jensenBoundNumeratorChars : List Char := ['3', '4', '3', '0', '6', '3', '0', '2', '7', '5', '3', '7', '2', '6', '0', '4', '3', '9', '3', '7', '8', '9', '2', '3', '1', '9', '4', '9', '1', '5', '0', '9', '4', '4', '5', '4', '6', '8', '1', '0', '6', '7', '7', '1', '5', '2', '3', '6', '9', '6', '9', '4', '7', '5', '2', '4', '2', '1', '3', '3', '5', '2', '3', '6', '1', '4', '7', '1', '5', '0', '8', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_jensenBoundDenominatorChars : List Char := ['2', '0', '3', '2', '2', '7', '9', '3', '2', '8', '4', '1', '1', '8', '5', '9', '3', '2', '6', '6', '4', '7', '2', '5', '0', '0', '4', '7', '4', '8', '7', '2', '7', '7', '5', '4', '4', '0', '4', '5', '0', '5', '3', '5', '2', '6', '8', '7', '4', '3', '8', '3', '7', '1', '5', '7', '8', '6', '1', '1', '7', '8', '1', '7', '2', '0', '4', '6', '3', '3', '8', '4', '5', '5', '9', '4', '3', '0', '9', '4', '0', '4', '1', '1', '5', '3', '7', '9', '6', '1', '6', '2', '0', '9', '1', '9', '0', '0', '2', '6', '7', '7', '4', '2', '9']
noncomputable def geometryRow019_jensenBoundText : String := String.ofList (geometryRow019_jensenBoundNumeratorChars ++ '/' :: geometryRow019_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_jensenBound_before_field"
  err.flush

theorem geometryRow019_jensenBound_field :
    geometryRowsJson019.getObjVal? "jensen_bound" = .ok (.str geometryRow019_jensenBoundText) := by rfl

theorem geometryRow019_jensenBound_numerator_no_slash :
    geometryRow019_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow019_jensenBoundNumeratorChars = some (34306302753726043937892319491509445468106771523696947524213352361471508480000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow019_jensenBoundDenominatorChars = some (203227932841185932664725004748727754404505352687438371578611781720463384559430940411537961620919002677429 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_nonzero : (203227932841185932664725004748727754404505352687438371578611781720463384559430940411537961620919002677429 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_jensenBound_parse :
    parseRational geometryRow019_jensenBoundText = .ok geometryRowsTyped019.jensenBound :=
  original_rational_fraction_of_chars geometryRow019_jensenBoundNumeratorChars geometryRow019_jensenBoundDenominatorChars
    (34306302753726043937892319491509445468106771523696947524213352361471508480000000000000000000000 : Int) (203227932841185932664725004748727754404505352687438371578611781720463384559430940411537961620919002677429 : Int)
    geometryRow019_jensenBound_numerator_no_slash geometryRow019_jensenBound_numerator_parse
    geometryRow019_jensenBound_denominator_parse geometryRow019_jensenBound_denominator_nonzero

theorem geometryRow019_jensenBound_read :
    rationalField geometryRowsJson019 "jensen_bound" = .ok geometryRowsTyped019.jensenBound :=
  original_rationalField_of_string geometryRowsJson019 "jensen_bound" geometryRow019_jensenBoundText
    geometryRowsTyped019.jensenBound geometryRow019_jensenBound_field geometryRow019_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_factorMaxima_before"
  err.flush

theorem geometryRow019_factorMaxima_read :
    rationalArrayField geometryRowsJson019 "factor_maxima" = .ok geometryRowsTyped019.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_gapWeightedMeans_before"
  err.flush

theorem geometryRow019_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson019 "gap_weighted_means" = .ok geometryRowsTyped019.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow019_floorChars : List Char := ['1', '3', '3', '7', '4', '2', '7', '0', '4', '1', '5', '6', '7', '0', '5', '8', '3', '3', '1', '5']
noncomputable def geometryRow019_floorText : String := String.ofList geometryRow019_floorChars

theorem geometryRow019_floor_text_read :
    geometryRowsJson019.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow019_floorText := by rfl

theorem geometryRow019_floor_chars_parse :
    SourceJson.intChars geometryRow019_floorChars = some (13374270415670583315 : Int) := by decide +kernel

theorem geometryRow019_floor_parse :
    parseInteger geometryRow019_floorText = .ok geometryRowsTyped019.jensenFloorQ96 := by
  simp only [geometryRow019_floorText, parseInteger, String.toList_ofList, geometryRow019_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_019 :
    decodeGeometryRow geometryRowsJson019 = .ok geometryRowsTyped019 :=
  original_geometryRow_of_fields geometryRowsJson019 geometryRowsTyped019 geometryRow019_floorText
    geometryRow019_simplexId_read geometryRow019_vertexIds_read
    geometryRow019_physicalVolume_read geometryRow019_meanGap_read
    geometryRow019_factorMaxima_read geometryRow019_gapWeightedMeans_read
    geometryRow019_jensenBound_read geometryRow019_floor_text_read geometryRow019_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Row_019_original_decoder_complete"
  err.flush

noncomputable def geometryRowsJsonBlock009 : List SourceJson := [geometryRowsJson018, geometryRowsJson019]
noncomputable def geometryRowsTypedBlock009 : List (GeometryRow) := [geometryRowsTyped018, geometryRowsTyped019]
noncomputable def geometryRowsTypedThroughBlock009 : List (GeometryRow) := geometryRowsTypedThroughBlock008 ++ geometryRowsTypedBlock009

theorem geometry_Rows_block_009_push_eq (acc : List SourceJson) :
    SimplicesBlock009.blockPush acc = [geometryRowsJson019, geometryRowsJson018] ++ acc := by rfl

theorem geometry_Rows_block_009_reverse (acc : List SourceJson) :
    (SimplicesBlock009.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock009 := by
  rw [geometry_Rows_block_009_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_009 :
    geometryRowsJsonBlock009.mapM decodeGeometryRow = .ok geometryRowsTypedBlock009 := by
  simp only [geometryRowsJsonBlock009, geometryRowsTypedBlock009, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_018, decode_geometry_Rows_019]
  rfl

theorem decode_geometry_Rows_through_block_009 :
    SimplicesValue.arrayAcc010.reverse.mapM decodeGeometryRow = .ok geometryRowsTypedThroughBlock009 := by
  change (SimplicesBlock009.blockPush SimplicesValue.arrayAcc009).reverse.mapM decodeGeometryRow = _
  rw [geometry_Rows_block_009_reverse]
  rw [List.mapM_append, decode_geometry_Rows_through_block_008, decode_geometry_Rows_block_009]
  rfl

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY01_TYPED Rows_block_009_complete"
  err.flush

#print axioms geometryRow018_simplexId_read
#print axioms geometryRow018_vertexIds_read
#print axioms geometryRow018_physicalVolume_field
#print axioms geometryRow018_physicalVolume_numerator_no_slash
#print axioms geometryRow018_physicalVolume_numerator_parse
#print axioms geometryRow018_physicalVolume_denominator_parse
#print axioms geometryRow018_physicalVolume_denominator_nonzero
#print axioms geometryRow018_physicalVolume_parse
#print axioms geometryRow018_physicalVolume_read
#print axioms geometryRow018_meanGap_field
#print axioms geometryRow018_meanGap_numerator_no_slash
#print axioms geometryRow018_meanGap_numerator_parse
#print axioms geometryRow018_meanGap_denominator_parse
#print axioms geometryRow018_meanGap_denominator_nonzero
#print axioms geometryRow018_meanGap_parse
#print axioms geometryRow018_meanGap_read
#print axioms geometryRow018_jensenBound_field
#print axioms geometryRow018_jensenBound_numerator_no_slash
#print axioms geometryRow018_jensenBound_numerator_parse
#print axioms geometryRow018_jensenBound_denominator_parse
#print axioms geometryRow018_jensenBound_denominator_nonzero
#print axioms geometryRow018_jensenBound_parse
#print axioms geometryRow018_jensenBound_read
#print axioms geometryRow018_factorMaxima_read
#print axioms geometryRow018_gapWeightedMeans_read
#print axioms geometryRow018_floor_text_read
#print axioms geometryRow018_floor_chars_parse
#print axioms geometryRow018_floor_parse
#print axioms decode_geometry_Rows_018
#print axioms geometryRow019_simplexId_read
#print axioms geometryRow019_vertexIds_read
#print axioms geometryRow019_physicalVolume_field
#print axioms geometryRow019_physicalVolume_numerator_no_slash
#print axioms geometryRow019_physicalVolume_numerator_parse
#print axioms geometryRow019_physicalVolume_denominator_parse
#print axioms geometryRow019_physicalVolume_denominator_nonzero
#print axioms geometryRow019_physicalVolume_parse
#print axioms geometryRow019_physicalVolume_read
#print axioms geometryRow019_meanGap_field
#print axioms geometryRow019_meanGap_numerator_no_slash
#print axioms geometryRow019_meanGap_numerator_parse
#print axioms geometryRow019_meanGap_denominator_parse
#print axioms geometryRow019_meanGap_denominator_nonzero
#print axioms geometryRow019_meanGap_parse
#print axioms geometryRow019_meanGap_read
#print axioms geometryRow019_jensenBound_field
#print axioms geometryRow019_jensenBound_numerator_no_slash
#print axioms geometryRow019_jensenBound_numerator_parse
#print axioms geometryRow019_jensenBound_denominator_parse
#print axioms geometryRow019_jensenBound_denominator_nonzero
#print axioms geometryRow019_jensenBound_parse
#print axioms geometryRow019_jensenBound_read
#print axioms geometryRow019_factorMaxima_read
#print axioms geometryRow019_gapWeightedMeans_read
#print axioms geometryRow019_floor_text_read
#print axioms geometryRow019_floor_chars_parse
#print axioms geometryRow019_floor_parse
#print axioms decode_geometry_Rows_019
#print axioms geometry_Rows_block_009_push_eq
#print axioms geometry_Rows_block_009_reverse
#print axioms decode_geometry_Rows_block_009
#print axioms decode_geometry_Rows_through_block_009

end ImbalancedChen.P2OriginalSaving19Geometry01DirectDecoding
