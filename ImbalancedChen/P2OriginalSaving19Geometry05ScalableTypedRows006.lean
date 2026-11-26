import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock006

/-! Local typed certificates for original cell 05, rows 48 through 55.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry05ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson048 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped048 : GeometryRow :=
  { simplexId := 48,
    vertexIds := #[27, 25, 24, 23, 21, 19, 17, 15, 5],
    physicalVolume := ((179298825665401427018141572826131 : ℚ) / (53776170337500000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((7905277 : ℚ) / (15912000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2546871 : ℚ) / (34000000 : ℚ)), ((515593 : ℚ) / (12000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((265478802657165875191 : ℚ) / (3110127279503400000000 : ℚ)), ((2572779512712876569 : ℚ) / (29905069995225000000 : ℚ)), ((2171553463620186431 : ℚ) / (17278484886130000000 : ℚ)), ((150779443020484129159 : ℚ) / (1555063639751700000000 : ℚ)), ((145396283504847346571 : ℚ) / (1555063639751700000000 : ℚ)), ((2352250819037946897 : ℚ) / (34556969772260000000 : ℚ)), ((27857638636616827967 : ℚ) / (777531819875850000000 : ℚ)), ((48748167120450220571 : ℚ) / (1555063639751700000000 : ℚ)), ((224778619420211897 : ℚ) / (7476267498806250000 : ℚ)), ((449555245169090779 : ℚ) / (14952534997612500000 : ℚ))],
    jensenBound := ((24793351689641396052085939264300001080769065716701673728295133967242131920477771390829219133526799113427435152892798736770367623070663903789171384078593750000000000000000 : ℚ) / (2163671874370726528867502014752540945248183184726585603289339149891953375485732164764033795317815034115915711878150450094547157329742806265209744986232010065812421802110127291015130389697 : ℚ)),
    jensenFloorQ96 := (907869497315 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_simplexId_before"
  err.flush

theorem geometryRow048_simplexId_read :
    geometryRowsJson048.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped048.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_vertexIds_before"
  err.flush

theorem geometryRow048_vertexIds_read :
    geometryRowsJson048.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped048.vertexIds := by decide +kernel

noncomputable def geometryRow048_physicalVolumeNumeratorChars : List Char := ['1', '7', '9', '2', '9', '8', '8', '2', '5', '6', '6', '5', '4', '0', '1', '4', '2', '7', '0', '1', '8', '1', '4', '1', '5', '7', '2', '8', '2', '6', '1', '3', '1']
noncomputable def geometryRow048_physicalVolumeDenominatorChars : List Char := ['5', '3', '7', '7', '6', '1', '7', '0', '3', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_physicalVolumeText : String := String.ofList (geometryRow048_physicalVolumeNumeratorChars ++ '/' :: geometryRow048_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_physicalVolume_before_field"
  err.flush

theorem geometryRow048_physicalVolume_field :
    geometryRowsJson048.getObjVal? "physical_volume" = .ok (.str geometryRow048_physicalVolumeText) := by rfl

theorem geometryRow048_physicalVolume_numerator_no_slash :
    geometryRow048_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeNumeratorChars = some (179298825665401427018141572826131 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow048_physicalVolumeDenominatorChars = some (53776170337500000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow048_physicalVolume_denominator_nonzero : (53776170337500000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_physicalVolume_parse :
    parseRational geometryRow048_physicalVolumeText = .ok geometryRowsTyped048.physicalVolume :=
  original_rational_fraction_of_chars geometryRow048_physicalVolumeNumeratorChars geometryRow048_physicalVolumeDenominatorChars
    (179298825665401427018141572826131 : Int) (53776170337500000000000000000000000000000000000000000000000 : Int)
    geometryRow048_physicalVolume_numerator_no_slash geometryRow048_physicalVolume_numerator_parse
    geometryRow048_physicalVolume_denominator_parse geometryRow048_physicalVolume_denominator_nonzero

theorem geometryRow048_physicalVolume_read :
    rationalField geometryRowsJson048 "physical_volume" = .ok geometryRowsTyped048.physicalVolume :=
  original_rationalField_of_string geometryRowsJson048 "physical_volume" geometryRow048_physicalVolumeText
    geometryRowsTyped048.physicalVolume geometryRow048_physicalVolume_field geometryRow048_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_physicalVolume_complete"
  err.flush

noncomputable def geometryRow048_meanGapNumeratorChars : List Char := ['7', '9', '0', '5', '2', '7', '7']
noncomputable def geometryRow048_meanGapDenominatorChars : List Char := ['1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_meanGapText : String := String.ofList (geometryRow048_meanGapNumeratorChars ++ '/' :: geometryRow048_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_meanGap_before_field"
  err.flush

theorem geometryRow048_meanGap_field :
    geometryRowsJson048.getObjVal? "mean_gap" = .ok (.str geometryRow048_meanGapText) := by rfl

theorem geometryRow048_meanGap_numerator_no_slash :
    geometryRow048_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_meanGap_numerator_parse :
    SourceJson.intChars geometryRow048_meanGapNumeratorChars = some (7905277 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_parse :
    SourceJson.intChars geometryRow048_meanGapDenominatorChars = some (15912000000 : Int) := by decide +kernel

theorem geometryRow048_meanGap_denominator_nonzero : (15912000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_meanGap_parse :
    parseRational geometryRow048_meanGapText = .ok geometryRowsTyped048.meanGap :=
  original_rational_fraction_of_chars geometryRow048_meanGapNumeratorChars geometryRow048_meanGapDenominatorChars
    (7905277 : Int) (15912000000 : Int)
    geometryRow048_meanGap_numerator_no_slash geometryRow048_meanGap_numerator_parse
    geometryRow048_meanGap_denominator_parse geometryRow048_meanGap_denominator_nonzero

theorem geometryRow048_meanGap_read :
    rationalField geometryRowsJson048 "mean_gap" = .ok geometryRowsTyped048.meanGap :=
  original_rationalField_of_string geometryRowsJson048 "mean_gap" geometryRow048_meanGapText
    geometryRowsTyped048.meanGap geometryRow048_meanGap_field geometryRow048_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_meanGap_complete"
  err.flush

noncomputable def geometryRow048_jensenBoundNumeratorChars : List Char := ['2', '4', '7', '9', '3', '3', '5', '1', '6', '8', '9', '6', '4', '1', '3', '9', '6', '0', '5', '2', '0', '8', '5', '9', '3', '9', '2', '6', '4', '3', '0', '0', '0', '0', '1', '0', '8', '0', '7', '6', '9', '0', '6', '5', '7', '1', '6', '7', '0', '1', '6', '7', '3', '7', '2', '8', '2', '9', '5', '1', '3', '3', '9', '6', '7', '2', '4', '2', '1', '3', '1', '9', '2', '0', '4', '7', '7', '7', '7', '1', '3', '9', '0', '8', '2', '9', '2', '1', '9', '1', '3', '3', '5', '2', '6', '7', '9', '9', '1', '1', '3', '4', '2', '7', '4', '3', '5', '1', '5', '2', '8', '9', '2', '7', '9', '8', '7', '3', '6', '7', '7', '0', '3', '6', '7', '6', '2', '3', '0', '7', '0', '6', '6', '3', '9', '0', '3', '7', '8', '9', '1', '7', '1', '3', '8', '4', '0', '7', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow048_jensenBoundDenominatorChars : List Char := ['2', '1', '6', '3', '6', '7', '1', '8', '7', '4', '3', '7', '0', '7', '2', '6', '5', '2', '8', '8', '6', '7', '5', '0', '2', '0', '1', '4', '7', '5', '2', '5', '4', '0', '9', '4', '5', '2', '4', '8', '1', '8', '3', '1', '8', '4', '7', '2', '6', '5', '8', '5', '6', '0', '3', '2', '8', '9', '3', '3', '9', '1', '4', '9', '8', '9', '1', '9', '5', '3', '3', '7', '5', '4', '8', '5', '7', '3', '2', '1', '6', '4', '7', '6', '4', '0', '3', '3', '7', '9', '5', '3', '1', '7', '8', '1', '5', '0', '3', '4', '1', '1', '5', '9', '1', '5', '7', '1', '1', '8', '7', '8', '1', '5', '0', '4', '5', '0', '0', '9', '4', '5', '4', '7', '1', '5', '7', '3', '2', '9', '7', '4', '2', '8', '0', '6', '2', '6', '5', '2', '0', '9', '7', '4', '4', '9', '8', '6', '2', '3', '2', '0', '1', '0', '0', '6', '5', '8', '1', '2', '4', '2', '1', '8', '0', '2', '1', '1', '0', '1', '2', '7', '2', '9', '1', '0', '1', '5', '1', '3', '0', '3', '8', '9', '6', '9', '7']
noncomputable def geometryRow048_jensenBoundText : String := String.ofList (geometryRow048_jensenBoundNumeratorChars ++ '/' :: geometryRow048_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_jensenBound_before_field"
  err.flush

theorem geometryRow048_jensenBound_field :
    geometryRowsJson048.getObjVal? "jensen_bound" = .ok (.str geometryRow048_jensenBoundText) := by rfl

theorem geometryRow048_jensenBound_numerator_no_slash :
    geometryRow048_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow048_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow048_jensenBoundNumeratorChars = some (24793351689641396052085939264300001080769065716701673728295133967242131920477771390829219133526799113427435152892798736770367623070663903789171384078593750000000000000000 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow048_jensenBoundDenominatorChars = some (2163671874370726528867502014752540945248183184726585603289339149891953375485732164764033795317815034115915711878150450094547157329742806265209744986232010065812421802110127291015130389697 : Int) := by decide +kernel

theorem geometryRow048_jensenBound_denominator_nonzero : (2163671874370726528867502014752540945248183184726585603289339149891953375485732164764033795317815034115915711878150450094547157329742806265209744986232010065812421802110127291015130389697 : Int) ≠ 0 := by decide +kernel

theorem geometryRow048_jensenBound_parse :
    parseRational geometryRow048_jensenBoundText = .ok geometryRowsTyped048.jensenBound :=
  original_rational_fraction_of_chars geometryRow048_jensenBoundNumeratorChars geometryRow048_jensenBoundDenominatorChars
    (24793351689641396052085939264300001080769065716701673728295133967242131920477771390829219133526799113427435152892798736770367623070663903789171384078593750000000000000000 : Int) (2163671874370726528867502014752540945248183184726585603289339149891953375485732164764033795317815034115915711878150450094547157329742806265209744986232010065812421802110127291015130389697 : Int)
    geometryRow048_jensenBound_numerator_no_slash geometryRow048_jensenBound_numerator_parse
    geometryRow048_jensenBound_denominator_parse geometryRow048_jensenBound_denominator_nonzero

theorem geometryRow048_jensenBound_read :
    rationalField geometryRowsJson048 "jensen_bound" = .ok geometryRowsTyped048.jensenBound :=
  original_rationalField_of_string geometryRowsJson048 "jensen_bound" geometryRow048_jensenBoundText
    geometryRowsTyped048.jensenBound geometryRow048_jensenBound_field geometryRow048_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_factorMaxima_before"
  err.flush

theorem geometryRow048_factorMaxima_read :
    rationalArrayField geometryRowsJson048 "factor_maxima" = .ok geometryRowsTyped048.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_gapWeightedMeans_before"
  err.flush

theorem geometryRow048_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson048 "gap_weighted_means" = .ok geometryRowsTyped048.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow048_floorChars : List Char := ['9', '0', '7', '8', '6', '9', '4', '9', '7', '3', '1', '5']
noncomputable def geometryRow048_floorText : String := String.ofList geometryRow048_floorChars

theorem geometryRow048_floor_text_read :
    geometryRowsJson048.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow048_floorText := by rfl

theorem geometryRow048_floor_chars_parse :
    SourceJson.intChars geometryRow048_floorChars = some (907869497315 : Int) := by decide +kernel

theorem geometryRow048_floor_parse :
    parseInteger geometryRow048_floorText = .ok geometryRowsTyped048.jensenFloorQ96 := by
  simp only [geometryRow048_floorText, parseInteger, String.toList_ofList, geometryRow048_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_048 :
    decodeGeometryRow geometryRowsJson048 = .ok geometryRowsTyped048 :=
  original_geometryRow_of_fields geometryRowsJson048 geometryRowsTyped048 geometryRow048_floorText
    geometryRow048_simplexId_read geometryRow048_vertexIds_read
    geometryRow048_physicalVolume_read geometryRow048_meanGap_read
    geometryRow048_factorMaxima_read geometryRow048_gapWeightedMeans_read
    geometryRow048_jensenBound_read geometryRow048_floor_text_read geometryRow048_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_048_original_decoder_complete"
  err.flush

theorem geometryRow048_shape :
    geometryRowsTyped048.simplexId = 48 ∧
    geometryRowsTyped048.vertexIds.size = 9 ∧ geometryRowsTyped048.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped048.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped048.factorMaxima.size = 10 ∧ geometryRowsTyped048.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson049 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped049 : GeometryRow :=
  { simplexId := 49,
    vertexIds := #[27, 26, 12, 10, 8, 7, 5, 3, 1],
    physicalVolume := ((6361406682371378318538039786351015812603 : ℚ) / (327205530944667648000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((16828033 : ℚ) / (180000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((21326944456421 : ℚ) / (226480800000000 : ℚ)), ((21436188469481 : ℚ) / (226480800000000 : ℚ)), ((16166832509929 : ℚ) / (135888480000000 : ℚ)), ((3714734227249 : ℚ) / (42465150000000 : ℚ)), ((6222880172099 : ℚ) / (75493600000000 : ℚ)), ((2041197516811 : ℚ) / (27177696000000 : ℚ)), ((13637049909247 : ℚ) / (339721200000000 : ℚ)), ((11491013171303 : ℚ) / (339721200000000 : ℚ)), ((22055283172981 : ℚ) / (679442400000000 : ℚ)), ((22055237876821 : ℚ) / (679442400000000 : ℚ))],
    jensenBound := ((674276014915513781878532206463215066127374170318771877269139685503188975766317995389290127200000000000000000000000 : ℚ) / (26583275818886213809236289099279348524086928939574714488304637114142629152421918271450233577592170903803044934451154573745833347829 : ℚ)),
    jensenFloorQ96 := (2009596185705 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_simplexId_before"
  err.flush

theorem geometryRow049_simplexId_read :
    geometryRowsJson049.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped049.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_vertexIds_before"
  err.flush

theorem geometryRow049_vertexIds_read :
    geometryRowsJson049.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped049.vertexIds := by decide +kernel

noncomputable def geometryRow049_physicalVolumeNumeratorChars : List Char := ['6', '3', '6', '1', '4', '0', '6', '6', '8', '2', '3', '7', '1', '3', '7', '8', '3', '1', '8', '5', '3', '8', '0', '3', '9', '7', '8', '6', '3', '5', '1', '0', '1', '5', '8', '1', '2', '6', '0', '3']
noncomputable def geometryRow049_physicalVolumeDenominatorChars : List Char := ['3', '2', '7', '2', '0', '5', '5', '3', '0', '9', '4', '4', '6', '6', '7', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_physicalVolumeText : String := String.ofList (geometryRow049_physicalVolumeNumeratorChars ++ '/' :: geometryRow049_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_physicalVolume_before_field"
  err.flush

theorem geometryRow049_physicalVolume_field :
    geometryRowsJson049.getObjVal? "physical_volume" = .ok (.str geometryRow049_physicalVolumeText) := by rfl

theorem geometryRow049_physicalVolume_numerator_no_slash :
    geometryRow049_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeNumeratorChars = some (6361406682371378318538039786351015812603 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow049_physicalVolumeDenominatorChars = some (327205530944667648000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_physicalVolume_denominator_nonzero : (327205530944667648000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_physicalVolume_parse :
    parseRational geometryRow049_physicalVolumeText = .ok geometryRowsTyped049.physicalVolume :=
  original_rational_fraction_of_chars geometryRow049_physicalVolumeNumeratorChars geometryRow049_physicalVolumeDenominatorChars
    (6361406682371378318538039786351015812603 : Int) (327205530944667648000000000000000000000000000000000000000000000000 : Int)
    geometryRow049_physicalVolume_numerator_no_slash geometryRow049_physicalVolume_numerator_parse
    geometryRow049_physicalVolume_denominator_parse geometryRow049_physicalVolume_denominator_nonzero

theorem geometryRow049_physicalVolume_read :
    rationalField geometryRowsJson049 "physical_volume" = .ok geometryRowsTyped049.physicalVolume :=
  original_rationalField_of_string geometryRowsJson049 "physical_volume" geometryRow049_physicalVolumeText
    geometryRowsTyped049.physicalVolume geometryRow049_physicalVolume_field geometryRow049_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_physicalVolume_complete"
  err.flush

noncomputable def geometryRow049_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow049_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_meanGapText : String := String.ofList (geometryRow049_meanGapNumeratorChars ++ '/' :: geometryRow049_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_meanGap_before_field"
  err.flush

theorem geometryRow049_meanGap_field :
    geometryRowsJson049.getObjVal? "mean_gap" = .ok (.str geometryRow049_meanGapText) := by rfl

theorem geometryRow049_meanGap_numerator_no_slash :
    geometryRow049_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_meanGap_numerator_parse :
    SourceJson.intChars geometryRow049_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_parse :
    SourceJson.intChars geometryRow049_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow049_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_meanGap_parse :
    parseRational geometryRow049_meanGapText = .ok geometryRowsTyped049.meanGap :=
  original_rational_fraction_of_chars geometryRow049_meanGapNumeratorChars geometryRow049_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow049_meanGap_numerator_no_slash geometryRow049_meanGap_numerator_parse
    geometryRow049_meanGap_denominator_parse geometryRow049_meanGap_denominator_nonzero

theorem geometryRow049_meanGap_read :
    rationalField geometryRowsJson049 "mean_gap" = .ok geometryRowsTyped049.meanGap :=
  original_rationalField_of_string geometryRowsJson049 "mean_gap" geometryRow049_meanGapText
    geometryRowsTyped049.meanGap geometryRow049_meanGap_field geometryRow049_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_meanGap_complete"
  err.flush

noncomputable def geometryRow049_jensenBoundNumeratorChars : List Char := ['6', '7', '4', '2', '7', '6', '0', '1', '4', '9', '1', '5', '5', '1', '3', '7', '8', '1', '8', '7', '8', '5', '3', '2', '2', '0', '6', '4', '6', '3', '2', '1', '5', '0', '6', '6', '1', '2', '7', '3', '7', '4', '1', '7', '0', '3', '1', '8', '7', '7', '1', '8', '7', '7', '2', '6', '9', '1', '3', '9', '6', '8', '5', '5', '0', '3', '1', '8', '8', '9', '7', '5', '7', '6', '6', '3', '1', '7', '9', '9', '5', '3', '8', '9', '2', '9', '0', '1', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow049_jensenBoundDenominatorChars : List Char := ['2', '6', '5', '8', '3', '2', '7', '5', '8', '1', '8', '8', '8', '6', '2', '1', '3', '8', '0', '9', '2', '3', '6', '2', '8', '9', '0', '9', '9', '2', '7', '9', '3', '4', '8', '5', '2', '4', '0', '8', '6', '9', '2', '8', '9', '3', '9', '5', '7', '4', '7', '1', '4', '4', '8', '8', '3', '0', '4', '6', '3', '7', '1', '1', '4', '1', '4', '2', '6', '2', '9', '1', '5', '2', '4', '2', '1', '9', '1', '8', '2', '7', '1', '4', '5', '0', '2', '3', '3', '5', '7', '7', '5', '9', '2', '1', '7', '0', '9', '0', '3', '8', '0', '3', '0', '4', '4', '9', '3', '4', '4', '5', '1', '1', '5', '4', '5', '7', '3', '7', '4', '5', '8', '3', '3', '3', '4', '7', '8', '2', '9']
noncomputable def geometryRow049_jensenBoundText : String := String.ofList (geometryRow049_jensenBoundNumeratorChars ++ '/' :: geometryRow049_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_jensenBound_before_field"
  err.flush

theorem geometryRow049_jensenBound_field :
    geometryRowsJson049.getObjVal? "jensen_bound" = .ok (.str geometryRow049_jensenBoundText) := by rfl

theorem geometryRow049_jensenBound_numerator_no_slash :
    geometryRow049_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow049_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow049_jensenBoundNumeratorChars = some (674276014915513781878532206463215066127374170318771877269139685503188975766317995389290127200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow049_jensenBoundDenominatorChars = some (26583275818886213809236289099279348524086928939574714488304637114142629152421918271450233577592170903803044934451154573745833347829 : Int) := by decide +kernel

theorem geometryRow049_jensenBound_denominator_nonzero : (26583275818886213809236289099279348524086928939574714488304637114142629152421918271450233577592170903803044934451154573745833347829 : Int) ≠ 0 := by decide +kernel

theorem geometryRow049_jensenBound_parse :
    parseRational geometryRow049_jensenBoundText = .ok geometryRowsTyped049.jensenBound :=
  original_rational_fraction_of_chars geometryRow049_jensenBoundNumeratorChars geometryRow049_jensenBoundDenominatorChars
    (674276014915513781878532206463215066127374170318771877269139685503188975766317995389290127200000000000000000000000 : Int) (26583275818886213809236289099279348524086928939574714488304637114142629152421918271450233577592170903803044934451154573745833347829 : Int)
    geometryRow049_jensenBound_numerator_no_slash geometryRow049_jensenBound_numerator_parse
    geometryRow049_jensenBound_denominator_parse geometryRow049_jensenBound_denominator_nonzero

theorem geometryRow049_jensenBound_read :
    rationalField geometryRowsJson049 "jensen_bound" = .ok geometryRowsTyped049.jensenBound :=
  original_rationalField_of_string geometryRowsJson049 "jensen_bound" geometryRow049_jensenBoundText
    geometryRowsTyped049.jensenBound geometryRow049_jensenBound_field geometryRow049_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_factorMaxima_before"
  err.flush

theorem geometryRow049_factorMaxima_read :
    rationalArrayField geometryRowsJson049 "factor_maxima" = .ok geometryRowsTyped049.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_gapWeightedMeans_before"
  err.flush

theorem geometryRow049_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson049 "gap_weighted_means" = .ok geometryRowsTyped049.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow049_floorChars : List Char := ['2', '0', '0', '9', '5', '9', '6', '1', '8', '5', '7', '0', '5']
noncomputable def geometryRow049_floorText : String := String.ofList geometryRow049_floorChars

theorem geometryRow049_floor_text_read :
    geometryRowsJson049.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow049_floorText := by rfl

theorem geometryRow049_floor_chars_parse :
    SourceJson.intChars geometryRow049_floorChars = some (2009596185705 : Int) := by decide +kernel

theorem geometryRow049_floor_parse :
    parseInteger geometryRow049_floorText = .ok geometryRowsTyped049.jensenFloorQ96 := by
  simp only [geometryRow049_floorText, parseInteger, String.toList_ofList, geometryRow049_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_049 :
    decodeGeometryRow geometryRowsJson049 = .ok geometryRowsTyped049 :=
  original_geometryRow_of_fields geometryRowsJson049 geometryRowsTyped049 geometryRow049_floorText
    geometryRow049_simplexId_read geometryRow049_vertexIds_read
    geometryRow049_physicalVolume_read geometryRow049_meanGap_read
    geometryRow049_factorMaxima_read geometryRow049_gapWeightedMeans_read
    geometryRow049_jensenBound_read geometryRow049_floor_text_read geometryRow049_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_049_original_decoder_complete"
  err.flush

theorem geometryRow049_shape :
    geometryRowsTyped049.simplexId = 49 ∧
    geometryRowsTyped049.vertexIds.size = 9 ∧ geometryRowsTyped049.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped049.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped049.factorMaxima.size = 10 ∧ geometryRowsTyped049.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson050 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped050 : GeometryRow :=
  { simplexId := 50,
    vertexIds := #[27, 26, 24, 10, 8, 7, 5, 3, 1],
    physicalVolume := ((11909371646083968905129860221736069097 : ℚ) / (674187220353024000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ)), ((234359 : ℚ) / (6000000 : ℚ))],
    gapWeightedMeans := #[((4809606046771 : ℚ) / (52264800000000 : ℚ)), ((4834816203631 : ℚ) / (52264800000000 : ℚ)), ((1255012762049 : ℚ) / (10452960000000 : ℚ)), ((1157521235047 : ℚ) / (13066200000000 : ℚ)), ((491244153103 : ℚ) / (5807200000000 : ℚ)), ((773665706719 : ℚ) / (10452960000000 : ℚ)), ((1021004709149 : ℚ) / (26132400000000 : ℚ)), ((294465855637 : ℚ) / (8710800000000 : ℚ)), ((188389688633 : ℚ) / (5807200000000 : ℚ)), ((565167904459 : ℚ) / (17421600000000 : ℚ))],
    jensenBound := ((897790068899621321114069857398873171371667826744820625732181491357939164166912000000000000000000000000 : ℚ) / (37361297240282497432305873649082164974739350756221482477509156501815857262967209151342353318122578329882729168350771171 : ℚ)),
    jensenFloorQ96 := (1903848708063 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_simplexId_before"
  err.flush

theorem geometryRow050_simplexId_read :
    geometryRowsJson050.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped050.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_vertexIds_before"
  err.flush

theorem geometryRow050_vertexIds_read :
    geometryRowsJson050.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped050.vertexIds := by decide +kernel

noncomputable def geometryRow050_physicalVolumeNumeratorChars : List Char := ['1', '1', '9', '0', '9', '3', '7', '1', '6', '4', '6', '0', '8', '3', '9', '6', '8', '9', '0', '5', '1', '2', '9', '8', '6', '0', '2', '2', '1', '7', '3', '6', '0', '6', '9', '0', '9', '7']
noncomputable def geometryRow050_physicalVolumeDenominatorChars : List Char := ['6', '7', '4', '1', '8', '7', '2', '2', '0', '3', '5', '3', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_physicalVolumeText : String := String.ofList (geometryRow050_physicalVolumeNumeratorChars ++ '/' :: geometryRow050_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_physicalVolume_before_field"
  err.flush

theorem geometryRow050_physicalVolume_field :
    geometryRowsJson050.getObjVal? "physical_volume" = .ok (.str geometryRow050_physicalVolumeText) := by rfl

theorem geometryRow050_physicalVolume_numerator_no_slash :
    geometryRow050_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeNumeratorChars = some (11909371646083968905129860221736069097 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow050_physicalVolumeDenominatorChars = some (674187220353024000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_physicalVolume_denominator_nonzero : (674187220353024000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_physicalVolume_parse :
    parseRational geometryRow050_physicalVolumeText = .ok geometryRowsTyped050.physicalVolume :=
  original_rational_fraction_of_chars geometryRow050_physicalVolumeNumeratorChars geometryRow050_physicalVolumeDenominatorChars
    (11909371646083968905129860221736069097 : Int) (674187220353024000000000000000000000000000000000000000000000000 : Int)
    geometryRow050_physicalVolume_numerator_no_slash geometryRow050_physicalVolume_numerator_parse
    geometryRow050_physicalVolume_denominator_parse geometryRow050_physicalVolume_denominator_nonzero

theorem geometryRow050_physicalVolume_read :
    rationalField geometryRowsJson050 "physical_volume" = .ok geometryRowsTyped050.physicalVolume :=
  original_rationalField_of_string geometryRowsJson050 "physical_volume" geometryRow050_physicalVolumeText
    geometryRowsTyped050.physicalVolume geometryRow050_physicalVolume_field geometryRow050_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_physicalVolume_complete"
  err.flush

noncomputable def geometryRow050_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow050_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_meanGapText : String := String.ofList (geometryRow050_meanGapNumeratorChars ++ '/' :: geometryRow050_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_meanGap_before_field"
  err.flush

theorem geometryRow050_meanGap_field :
    geometryRowsJson050.getObjVal? "mean_gap" = .ok (.str geometryRow050_meanGapText) := by rfl

theorem geometryRow050_meanGap_numerator_no_slash :
    geometryRow050_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_meanGap_numerator_parse :
    SourceJson.intChars geometryRow050_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_parse :
    SourceJson.intChars geometryRow050_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow050_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_meanGap_parse :
    parseRational geometryRow050_meanGapText = .ok geometryRowsTyped050.meanGap :=
  original_rational_fraction_of_chars geometryRow050_meanGapNumeratorChars geometryRow050_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow050_meanGap_numerator_no_slash geometryRow050_meanGap_numerator_parse
    geometryRow050_meanGap_denominator_parse geometryRow050_meanGap_denominator_nonzero

theorem geometryRow050_meanGap_read :
    rationalField geometryRowsJson050 "mean_gap" = .ok geometryRowsTyped050.meanGap :=
  original_rationalField_of_string geometryRowsJson050 "mean_gap" geometryRow050_meanGapText
    geometryRowsTyped050.meanGap geometryRow050_meanGap_field geometryRow050_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_meanGap_complete"
  err.flush

noncomputable def geometryRow050_jensenBoundNumeratorChars : List Char := ['8', '9', '7', '7', '9', '0', '0', '6', '8', '8', '9', '9', '6', '2', '1', '3', '2', '1', '1', '1', '4', '0', '6', '9', '8', '5', '7', '3', '9', '8', '8', '7', '3', '1', '7', '1', '3', '7', '1', '6', '6', '7', '8', '2', '6', '7', '4', '4', '8', '2', '0', '6', '2', '5', '7', '3', '2', '1', '8', '1', '4', '9', '1', '3', '5', '7', '9', '3', '9', '1', '6', '4', '1', '6', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow050_jensenBoundDenominatorChars : List Char := ['3', '7', '3', '6', '1', '2', '9', '7', '2', '4', '0', '2', '8', '2', '4', '9', '7', '4', '3', '2', '3', '0', '5', '8', '7', '3', '6', '4', '9', '0', '8', '2', '1', '6', '4', '9', '7', '4', '7', '3', '9', '3', '5', '0', '7', '5', '6', '2', '2', '1', '4', '8', '2', '4', '7', '7', '5', '0', '9', '1', '5', '6', '5', '0', '1', '8', '1', '5', '8', '5', '7', '2', '6', '2', '9', '6', '7', '2', '0', '9', '1', '5', '1', '3', '4', '2', '3', '5', '3', '3', '1', '8', '1', '2', '2', '5', '7', '8', '3', '2', '9', '8', '8', '2', '7', '2', '9', '1', '6', '8', '3', '5', '0', '7', '7', '1', '1', '7', '1']
noncomputable def geometryRow050_jensenBoundText : String := String.ofList (geometryRow050_jensenBoundNumeratorChars ++ '/' :: geometryRow050_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_jensenBound_before_field"
  err.flush

theorem geometryRow050_jensenBound_field :
    geometryRowsJson050.getObjVal? "jensen_bound" = .ok (.str geometryRow050_jensenBoundText) := by rfl

theorem geometryRow050_jensenBound_numerator_no_slash :
    geometryRow050_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow050_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow050_jensenBoundNumeratorChars = some (897790068899621321114069857398873171371667826744820625732181491357939164166912000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow050_jensenBoundDenominatorChars = some (37361297240282497432305873649082164974739350756221482477509156501815857262967209151342353318122578329882729168350771171 : Int) := by decide +kernel

theorem geometryRow050_jensenBound_denominator_nonzero : (37361297240282497432305873649082164974739350756221482477509156501815857262967209151342353318122578329882729168350771171 : Int) ≠ 0 := by decide +kernel

theorem geometryRow050_jensenBound_parse :
    parseRational geometryRow050_jensenBoundText = .ok geometryRowsTyped050.jensenBound :=
  original_rational_fraction_of_chars geometryRow050_jensenBoundNumeratorChars geometryRow050_jensenBoundDenominatorChars
    (897790068899621321114069857398873171371667826744820625732181491357939164166912000000000000000000000000 : Int) (37361297240282497432305873649082164974739350756221482477509156501815857262967209151342353318122578329882729168350771171 : Int)
    geometryRow050_jensenBound_numerator_no_slash geometryRow050_jensenBound_numerator_parse
    geometryRow050_jensenBound_denominator_parse geometryRow050_jensenBound_denominator_nonzero

theorem geometryRow050_jensenBound_read :
    rationalField geometryRowsJson050 "jensen_bound" = .ok geometryRowsTyped050.jensenBound :=
  original_rationalField_of_string geometryRowsJson050 "jensen_bound" geometryRow050_jensenBoundText
    geometryRowsTyped050.jensenBound geometryRow050_jensenBound_field geometryRow050_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_factorMaxima_before"
  err.flush

theorem geometryRow050_factorMaxima_read :
    rationalArrayField geometryRowsJson050 "factor_maxima" = .ok geometryRowsTyped050.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_gapWeightedMeans_before"
  err.flush

theorem geometryRow050_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson050 "gap_weighted_means" = .ok geometryRowsTyped050.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow050_floorChars : List Char := ['1', '9', '0', '3', '8', '4', '8', '7', '0', '8', '0', '6', '3']
noncomputable def geometryRow050_floorText : String := String.ofList geometryRow050_floorChars

theorem geometryRow050_floor_text_read :
    geometryRowsJson050.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow050_floorText := by rfl

theorem geometryRow050_floor_chars_parse :
    SourceJson.intChars geometryRow050_floorChars = some (1903848708063 : Int) := by decide +kernel

theorem geometryRow050_floor_parse :
    parseInteger geometryRow050_floorText = .ok geometryRowsTyped050.jensenFloorQ96 := by
  simp only [geometryRow050_floorText, parseInteger, String.toList_ofList, geometryRow050_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_050 :
    decodeGeometryRow geometryRowsJson050 = .ok geometryRowsTyped050 :=
  original_geometryRow_of_fields geometryRowsJson050 geometryRowsTyped050 geometryRow050_floorText
    geometryRow050_simplexId_read geometryRow050_vertexIds_read
    geometryRow050_physicalVolume_read geometryRow050_meanGap_read
    geometryRow050_factorMaxima_read geometryRow050_gapWeightedMeans_read
    geometryRow050_jensenBound_read geometryRow050_floor_text_read geometryRow050_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_050_original_decoder_complete"
  err.flush

theorem geometryRow050_shape :
    geometryRowsTyped050.simplexId = 50 ∧
    geometryRowsTyped050.vertexIds.size = 9 ∧ geometryRowsTyped050.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped050.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped050.factorMaxima.size = 10 ∧ geometryRowsTyped050.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson051 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped051 : GeometryRow :=
  { simplexId := 51,
    vertexIds := #[27, 26, 24, 23, 10, 7, 5, 3, 1],
    physicalVolume := ((1069392531433020339320854225261768181 : ℚ) / (92299440881664000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((109926710092733 : ℚ) / (1202090400000000 : ℚ)), ((110506543700513 : ℚ) / (1202090400000000 : ℚ)), ((29134744180879 : ℚ) / (240418080000000 : ℚ)), ((13645732226653 : ℚ) / (150261300000000 : ℚ)), ((11523157732829 : ℚ) / (133565600000000 : ℚ)), ((3504972120157 : ℚ) / (48083616000000 : ℚ)), ((23146294993237 : ℚ) / (601045200000000 : ℚ)), ((6660443573921 : ℚ) / (200348400000000 : ℚ)), ((12556671542297 : ℚ) / (400696800000000 : ℚ)), ((12556644829177 : ℚ) / (400696800000000 : ℚ))],
    jensenBound := ((80500178127103201114991649730352501598528812448960095876314166500018125045259300239918896947200000000000000000000000 : ℚ) / (4741198475531275558450343129812677941325988646271914212222863996772849381706234348260876626433292134327118057181671151429444828223547 : ℚ)),
    jensenFloorQ96 := (1345204430482 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_simplexId_before"
  err.flush

theorem geometryRow051_simplexId_read :
    geometryRowsJson051.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped051.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_vertexIds_before"
  err.flush

theorem geometryRow051_vertexIds_read :
    geometryRowsJson051.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped051.vertexIds := by decide +kernel

noncomputable def geometryRow051_physicalVolumeNumeratorChars : List Char := ['1', '0', '6', '9', '3', '9', '2', '5', '3', '1', '4', '3', '3', '0', '2', '0', '3', '3', '9', '3', '2', '0', '8', '5', '4', '2', '2', '5', '2', '6', '1', '7', '6', '8', '1', '8', '1']
noncomputable def geometryRow051_physicalVolumeDenominatorChars : List Char := ['9', '2', '2', '9', '9', '4', '4', '0', '8', '8', '1', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_physicalVolumeText : String := String.ofList (geometryRow051_physicalVolumeNumeratorChars ++ '/' :: geometryRow051_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_physicalVolume_before_field"
  err.flush

theorem geometryRow051_physicalVolume_field :
    geometryRowsJson051.getObjVal? "physical_volume" = .ok (.str geometryRow051_physicalVolumeText) := by rfl

theorem geometryRow051_physicalVolume_numerator_no_slash :
    geometryRow051_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeNumeratorChars = some (1069392531433020339320854225261768181 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow051_physicalVolumeDenominatorChars = some (92299440881664000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_physicalVolume_denominator_nonzero : (92299440881664000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_physicalVolume_parse :
    parseRational geometryRow051_physicalVolumeText = .ok geometryRowsTyped051.physicalVolume :=
  original_rational_fraction_of_chars geometryRow051_physicalVolumeNumeratorChars geometryRow051_physicalVolumeDenominatorChars
    (1069392531433020339320854225261768181 : Int) (92299440881664000000000000000000000000000000000000000000000000 : Int)
    geometryRow051_physicalVolume_numerator_no_slash geometryRow051_physicalVolume_numerator_parse
    geometryRow051_physicalVolume_denominator_parse geometryRow051_physicalVolume_denominator_nonzero

theorem geometryRow051_physicalVolume_read :
    rationalField geometryRowsJson051 "physical_volume" = .ok geometryRowsTyped051.physicalVolume :=
  original_rationalField_of_string geometryRowsJson051 "physical_volume" geometryRow051_physicalVolumeText
    geometryRowsTyped051.physicalVolume geometryRow051_physicalVolume_field geometryRow051_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_physicalVolume_complete"
  err.flush

noncomputable def geometryRow051_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow051_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_meanGapText : String := String.ofList (geometryRow051_meanGapNumeratorChars ++ '/' :: geometryRow051_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_meanGap_before_field"
  err.flush

theorem geometryRow051_meanGap_field :
    geometryRowsJson051.getObjVal? "mean_gap" = .ok (.str geometryRow051_meanGapText) := by rfl

theorem geometryRow051_meanGap_numerator_no_slash :
    geometryRow051_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_meanGap_numerator_parse :
    SourceJson.intChars geometryRow051_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_parse :
    SourceJson.intChars geometryRow051_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow051_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_meanGap_parse :
    parseRational geometryRow051_meanGapText = .ok geometryRowsTyped051.meanGap :=
  original_rational_fraction_of_chars geometryRow051_meanGapNumeratorChars geometryRow051_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow051_meanGap_numerator_no_slash geometryRow051_meanGap_numerator_parse
    geometryRow051_meanGap_denominator_parse geometryRow051_meanGap_denominator_nonzero

theorem geometryRow051_meanGap_read :
    rationalField geometryRowsJson051 "mean_gap" = .ok geometryRowsTyped051.meanGap :=
  original_rationalField_of_string geometryRowsJson051 "mean_gap" geometryRow051_meanGapText
    geometryRowsTyped051.meanGap geometryRow051_meanGap_field geometryRow051_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_meanGap_complete"
  err.flush

noncomputable def geometryRow051_jensenBoundNumeratorChars : List Char := ['8', '0', '5', '0', '0', '1', '7', '8', '1', '2', '7', '1', '0', '3', '2', '0', '1', '1', '1', '4', '9', '9', '1', '6', '4', '9', '7', '3', '0', '3', '5', '2', '5', '0', '1', '5', '9', '8', '5', '2', '8', '8', '1', '2', '4', '4', '8', '9', '6', '0', '0', '9', '5', '8', '7', '6', '3', '1', '4', '1', '6', '6', '5', '0', '0', '0', '1', '8', '1', '2', '5', '0', '4', '5', '2', '5', '9', '3', '0', '0', '2', '3', '9', '9', '1', '8', '8', '9', '6', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow051_jensenBoundDenominatorChars : List Char := ['4', '7', '4', '1', '1', '9', '8', '4', '7', '5', '5', '3', '1', '2', '7', '5', '5', '5', '8', '4', '5', '0', '3', '4', '3', '1', '2', '9', '8', '1', '2', '6', '7', '7', '9', '4', '1', '3', '2', '5', '9', '8', '8', '6', '4', '6', '2', '7', '1', '9', '1', '4', '2', '1', '2', '2', '2', '2', '8', '6', '3', '9', '9', '6', '7', '7', '2', '8', '4', '9', '3', '8', '1', '7', '0', '6', '2', '3', '4', '3', '4', '8', '2', '6', '0', '8', '7', '6', '6', '2', '6', '4', '3', '3', '2', '9', '2', '1', '3', '4', '3', '2', '7', '1', '1', '8', '0', '5', '7', '1', '8', '1', '6', '7', '1', '1', '5', '1', '4', '2', '9', '4', '4', '4', '8', '2', '8', '2', '2', '3', '5', '4', '7']
noncomputable def geometryRow051_jensenBoundText : String := String.ofList (geometryRow051_jensenBoundNumeratorChars ++ '/' :: geometryRow051_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_jensenBound_before_field"
  err.flush

theorem geometryRow051_jensenBound_field :
    geometryRowsJson051.getObjVal? "jensen_bound" = .ok (.str geometryRow051_jensenBoundText) := by rfl

theorem geometryRow051_jensenBound_numerator_no_slash :
    geometryRow051_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow051_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow051_jensenBoundNumeratorChars = some (80500178127103201114991649730352501598528812448960095876314166500018125045259300239918896947200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow051_jensenBoundDenominatorChars = some (4741198475531275558450343129812677941325988646271914212222863996772849381706234348260876626433292134327118057181671151429444828223547 : Int) := by decide +kernel

theorem geometryRow051_jensenBound_denominator_nonzero : (4741198475531275558450343129812677941325988646271914212222863996772849381706234348260876626433292134327118057181671151429444828223547 : Int) ≠ 0 := by decide +kernel

theorem geometryRow051_jensenBound_parse :
    parseRational geometryRow051_jensenBoundText = .ok geometryRowsTyped051.jensenBound :=
  original_rational_fraction_of_chars geometryRow051_jensenBoundNumeratorChars geometryRow051_jensenBoundDenominatorChars
    (80500178127103201114991649730352501598528812448960095876314166500018125045259300239918896947200000000000000000000000 : Int) (4741198475531275558450343129812677941325988646271914212222863996772849381706234348260876626433292134327118057181671151429444828223547 : Int)
    geometryRow051_jensenBound_numerator_no_slash geometryRow051_jensenBound_numerator_parse
    geometryRow051_jensenBound_denominator_parse geometryRow051_jensenBound_denominator_nonzero

theorem geometryRow051_jensenBound_read :
    rationalField geometryRowsJson051 "jensen_bound" = .ok geometryRowsTyped051.jensenBound :=
  original_rationalField_of_string geometryRowsJson051 "jensen_bound" geometryRow051_jensenBoundText
    geometryRowsTyped051.jensenBound geometryRow051_jensenBound_field geometryRow051_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_factorMaxima_before"
  err.flush

theorem geometryRow051_factorMaxima_read :
    rationalArrayField geometryRowsJson051 "factor_maxima" = .ok geometryRowsTyped051.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_gapWeightedMeans_before"
  err.flush

theorem geometryRow051_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson051 "gap_weighted_means" = .ok geometryRowsTyped051.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow051_floorChars : List Char := ['1', '3', '4', '5', '2', '0', '4', '4', '3', '0', '4', '8', '2']
noncomputable def geometryRow051_floorText : String := String.ofList geometryRow051_floorChars

theorem geometryRow051_floor_text_read :
    geometryRowsJson051.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow051_floorText := by rfl

theorem geometryRow051_floor_chars_parse :
    SourceJson.intChars geometryRow051_floorChars = some (1345204430482 : Int) := by decide +kernel

theorem geometryRow051_floor_parse :
    parseInteger geometryRow051_floorText = .ok geometryRowsTyped051.jensenFloorQ96 := by
  simp only [geometryRow051_floorText, parseInteger, String.toList_ofList, geometryRow051_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_051 :
    decodeGeometryRow geometryRowsJson051 = .ok geometryRowsTyped051 :=
  original_geometryRow_of_fields geometryRowsJson051 geometryRowsTyped051 geometryRow051_floorText
    geometryRow051_simplexId_read geometryRow051_vertexIds_read
    geometryRow051_physicalVolume_read geometryRow051_meanGap_read
    geometryRow051_factorMaxima_read geometryRow051_gapWeightedMeans_read
    geometryRow051_jensenBound_read geometryRow051_floor_text_read geometryRow051_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_051_original_decoder_complete"
  err.flush

theorem geometryRow051_shape :
    geometryRowsTyped051.simplexId = 51 ∧
    geometryRowsTyped051.vertexIds.size = 9 ∧ geometryRowsTyped051.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped051.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped051.factorMaxima.size = 10 ∧ geometryRowsTyped051.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson052 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped052 : GeometryRow :=
  { simplexId := 52,
    vertexIds := #[27, 26, 24, 23, 21, 7, 5, 3, 1],
    physicalVolume := ((210291546429789254382016920852047513 : ℚ) / (21632681456640000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((54485392633729 : ℚ) / (601045200000000 : ℚ)), ((54775309437619 : ℚ) / (601045200000000 : ℚ)), ((29376208079527 : ℚ) / (240418080000000 : ℚ)), ((110691818914889 : ℚ) / (1202090400000000 : ℚ)), ((35351937213827 : ℚ) / (400696800000000 : ℚ)), ((17283396702137 : ℚ) / (240418080000000 : ℚ)), ((22576258716847 : ℚ) / (601045200000000 : ℚ)), ((6470431481791 : ℚ) / (200348400000000 : ℚ)), ((6225228836411 : ℚ) / (200348400000000 : ℚ)), ((2075071826617 : ℚ) / (66782800000000 : ℚ))],
    jensenBound := ((210278411555434769804571835328248904032841501155902052662037172983394288778242294340865228800000000000000000000000 : ℚ) / (13934026269668983107946762594037739027823621961012138647150927817755030470507097153548724724559804891024042141323378281982465492351 : ℚ)),
    jensenFloorQ96 := (1195632320589 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_simplexId_before"
  err.flush

theorem geometryRow052_simplexId_read :
    geometryRowsJson052.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped052.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_vertexIds_before"
  err.flush

theorem geometryRow052_vertexIds_read :
    geometryRowsJson052.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped052.vertexIds := by decide +kernel

noncomputable def geometryRow052_physicalVolumeNumeratorChars : List Char := ['2', '1', '0', '2', '9', '1', '5', '4', '6', '4', '2', '9', '7', '8', '9', '2', '5', '4', '3', '8', '2', '0', '1', '6', '9', '2', '0', '8', '5', '2', '0', '4', '7', '5', '1', '3']
noncomputable def geometryRow052_physicalVolumeDenominatorChars : List Char := ['2', '1', '6', '3', '2', '6', '8', '1', '4', '5', '6', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_physicalVolumeText : String := String.ofList (geometryRow052_physicalVolumeNumeratorChars ++ '/' :: geometryRow052_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_physicalVolume_before_field"
  err.flush

theorem geometryRow052_physicalVolume_field :
    geometryRowsJson052.getObjVal? "physical_volume" = .ok (.str geometryRow052_physicalVolumeText) := by rfl

theorem geometryRow052_physicalVolume_numerator_no_slash :
    geometryRow052_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeNumeratorChars = some (210291546429789254382016920852047513 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow052_physicalVolumeDenominatorChars = some (21632681456640000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_physicalVolume_denominator_nonzero : (21632681456640000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_physicalVolume_parse :
    parseRational geometryRow052_physicalVolumeText = .ok geometryRowsTyped052.physicalVolume :=
  original_rational_fraction_of_chars geometryRow052_physicalVolumeNumeratorChars geometryRow052_physicalVolumeDenominatorChars
    (210291546429789254382016920852047513 : Int) (21632681456640000000000000000000000000000000000000000000000000 : Int)
    geometryRow052_physicalVolume_numerator_no_slash geometryRow052_physicalVolume_numerator_parse
    geometryRow052_physicalVolume_denominator_parse geometryRow052_physicalVolume_denominator_nonzero

theorem geometryRow052_physicalVolume_read :
    rationalField geometryRowsJson052 "physical_volume" = .ok geometryRowsTyped052.physicalVolume :=
  original_rationalField_of_string geometryRowsJson052 "physical_volume" geometryRow052_physicalVolumeText
    geometryRowsTyped052.physicalVolume geometryRow052_physicalVolume_field geometryRow052_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_physicalVolume_complete"
  err.flush

noncomputable def geometryRow052_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow052_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_meanGapText : String := String.ofList (geometryRow052_meanGapNumeratorChars ++ '/' :: geometryRow052_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_meanGap_before_field"
  err.flush

theorem geometryRow052_meanGap_field :
    geometryRowsJson052.getObjVal? "mean_gap" = .ok (.str geometryRow052_meanGapText) := by rfl

theorem geometryRow052_meanGap_numerator_no_slash :
    geometryRow052_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_meanGap_numerator_parse :
    SourceJson.intChars geometryRow052_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_parse :
    SourceJson.intChars geometryRow052_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow052_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_meanGap_parse :
    parseRational geometryRow052_meanGapText = .ok geometryRowsTyped052.meanGap :=
  original_rational_fraction_of_chars geometryRow052_meanGapNumeratorChars geometryRow052_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow052_meanGap_numerator_no_slash geometryRow052_meanGap_numerator_parse
    geometryRow052_meanGap_denominator_parse geometryRow052_meanGap_denominator_nonzero

theorem geometryRow052_meanGap_read :
    rationalField geometryRowsJson052 "mean_gap" = .ok geometryRowsTyped052.meanGap :=
  original_rationalField_of_string geometryRowsJson052 "mean_gap" geometryRow052_meanGapText
    geometryRowsTyped052.meanGap geometryRow052_meanGap_field geometryRow052_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_meanGap_complete"
  err.flush

noncomputable def geometryRow052_jensenBoundNumeratorChars : List Char := ['2', '1', '0', '2', '7', '8', '4', '1', '1', '5', '5', '5', '4', '3', '4', '7', '6', '9', '8', '0', '4', '5', '7', '1', '8', '3', '5', '3', '2', '8', '2', '4', '8', '9', '0', '4', '0', '3', '2', '8', '4', '1', '5', '0', '1', '1', '5', '5', '9', '0', '2', '0', '5', '2', '6', '6', '2', '0', '3', '7', '1', '7', '2', '9', '8', '3', '3', '9', '4', '2', '8', '8', '7', '7', '8', '2', '4', '2', '2', '9', '4', '3', '4', '0', '8', '6', '5', '2', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow052_jensenBoundDenominatorChars : List Char := ['1', '3', '9', '3', '4', '0', '2', '6', '2', '6', '9', '6', '6', '8', '9', '8', '3', '1', '0', '7', '9', '4', '6', '7', '6', '2', '5', '9', '4', '0', '3', '7', '7', '3', '9', '0', '2', '7', '8', '2', '3', '6', '2', '1', '9', '6', '1', '0', '1', '2', '1', '3', '8', '6', '4', '7', '1', '5', '0', '9', '2', '7', '8', '1', '7', '7', '5', '5', '0', '3', '0', '4', '7', '0', '5', '0', '7', '0', '9', '7', '1', '5', '3', '5', '4', '8', '7', '2', '4', '7', '2', '4', '5', '5', '9', '8', '0', '4', '8', '9', '1', '0', '2', '4', '0', '4', '2', '1', '4', '1', '3', '2', '3', '3', '7', '8', '2', '8', '1', '9', '8', '2', '4', '6', '5', '4', '9', '2', '3', '5', '1']
noncomputable def geometryRow052_jensenBoundText : String := String.ofList (geometryRow052_jensenBoundNumeratorChars ++ '/' :: geometryRow052_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_jensenBound_before_field"
  err.flush

theorem geometryRow052_jensenBound_field :
    geometryRowsJson052.getObjVal? "jensen_bound" = .ok (.str geometryRow052_jensenBoundText) := by rfl

theorem geometryRow052_jensenBound_numerator_no_slash :
    geometryRow052_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow052_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow052_jensenBoundNumeratorChars = some (210278411555434769804571835328248904032841501155902052662037172983394288778242294340865228800000000000000000000000 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow052_jensenBoundDenominatorChars = some (13934026269668983107946762594037739027823621961012138647150927817755030470507097153548724724559804891024042141323378281982465492351 : Int) := by decide +kernel

theorem geometryRow052_jensenBound_denominator_nonzero : (13934026269668983107946762594037739027823621961012138647150927817755030470507097153548724724559804891024042141323378281982465492351 : Int) ≠ 0 := by decide +kernel

theorem geometryRow052_jensenBound_parse :
    parseRational geometryRow052_jensenBoundText = .ok geometryRowsTyped052.jensenBound :=
  original_rational_fraction_of_chars geometryRow052_jensenBoundNumeratorChars geometryRow052_jensenBoundDenominatorChars
    (210278411555434769804571835328248904032841501155902052662037172983394288778242294340865228800000000000000000000000 : Int) (13934026269668983107946762594037739027823621961012138647150927817755030470507097153548724724559804891024042141323378281982465492351 : Int)
    geometryRow052_jensenBound_numerator_no_slash geometryRow052_jensenBound_numerator_parse
    geometryRow052_jensenBound_denominator_parse geometryRow052_jensenBound_denominator_nonzero

theorem geometryRow052_jensenBound_read :
    rationalField geometryRowsJson052 "jensen_bound" = .ok geometryRowsTyped052.jensenBound :=
  original_rationalField_of_string geometryRowsJson052 "jensen_bound" geometryRow052_jensenBoundText
    geometryRowsTyped052.jensenBound geometryRow052_jensenBound_field geometryRow052_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_factorMaxima_before"
  err.flush

theorem geometryRow052_factorMaxima_read :
    rationalArrayField geometryRowsJson052 "factor_maxima" = .ok geometryRowsTyped052.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_gapWeightedMeans_before"
  err.flush

theorem geometryRow052_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson052 "gap_weighted_means" = .ok geometryRowsTyped052.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow052_floorChars : List Char := ['1', '1', '9', '5', '6', '3', '2', '3', '2', '0', '5', '8', '9']
noncomputable def geometryRow052_floorText : String := String.ofList geometryRow052_floorChars

theorem geometryRow052_floor_text_read :
    geometryRowsJson052.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow052_floorText := by rfl

theorem geometryRow052_floor_chars_parse :
    SourceJson.intChars geometryRow052_floorChars = some (1195632320589 : Int) := by decide +kernel

theorem geometryRow052_floor_parse :
    parseInteger geometryRow052_floorText = .ok geometryRowsTyped052.jensenFloorQ96 := by
  simp only [geometryRow052_floorText, parseInteger, String.toList_ofList, geometryRow052_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_052 :
    decodeGeometryRow geometryRowsJson052 = .ok geometryRowsTyped052 :=
  original_geometryRow_of_fields geometryRowsJson052 geometryRowsTyped052 geometryRow052_floorText
    geometryRow052_simplexId_read geometryRow052_vertexIds_read
    geometryRow052_physicalVolume_read geometryRow052_meanGap_read
    geometryRow052_factorMaxima_read geometryRow052_gapWeightedMeans_read
    geometryRow052_jensenBound_read geometryRow052_floor_text_read geometryRow052_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_052_original_decoder_complete"
  err.flush

theorem geometryRow052_shape :
    geometryRowsTyped052.simplexId = 52 ∧
    geometryRowsTyped052.vertexIds.size = 9 ∧ geometryRowsTyped052.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped052.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped052.factorMaxima.size = 10 ∧ geometryRowsTyped052.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson053 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped053 : GeometryRow :=
  { simplexId := 53,
    vertexIds := #[27, 26, 24, 23, 21, 19, 7, 5, 1],
    physicalVolume := ((4307771552777623075702250018991281 : ℚ) / (645975904608000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2999973 : ℚ) / (30500000 : ℚ)), ((2999973 : ℚ) / (30500000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))],
    gapWeightedMeans := #[((1149312045067001 : ℚ) / (12922471800000000 : ℚ)), ((288886314087659 : ℚ) / (3230617950000000 : ℚ)), ((35430153708993 : ℚ) / (287166040000000 : ℚ)), ((1212697418151223 : ℚ) / (12922471800000000 : ℚ)), ((1159105450318967 : ℚ) / (12922471800000000 : ℚ)), ((20239570508387 : ℚ) / (287166040000000 : ℚ)), ((485524709512393 : ℚ) / (12922471800000000 : ℚ)), ((206861544016291 : ℚ) / (6461235900000000 : ℚ)), ((98538156940613 : ℚ) / (3230617950000000 : ℚ)), ((98537941566083 : ℚ) / (3230617950000000 : ℚ))],
    jensenBound := ((1193685080035275139760859106489974915323219255830538780282094759427608459480533302810419734688063824140500000000000000000000000 : ℚ) / (108790862712944106413019662289576239151456749159153682164522615070905647692394169129238358108062306317691878479497629890845476946686381801464511 : ℚ)),
    jensenFloorQ96 := (869314510000 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_simplexId_before"
  err.flush

theorem geometryRow053_simplexId_read :
    geometryRowsJson053.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped053.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_vertexIds_before"
  err.flush

theorem geometryRow053_vertexIds_read :
    geometryRowsJson053.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped053.vertexIds := by decide +kernel

noncomputable def geometryRow053_physicalVolumeNumeratorChars : List Char := ['4', '3', '0', '7', '7', '7', '1', '5', '5', '2', '7', '7', '7', '6', '2', '3', '0', '7', '5', '7', '0', '2', '2', '5', '0', '0', '1', '8', '9', '9', '1', '2', '8', '1']
noncomputable def geometryRow053_physicalVolumeDenominatorChars : List Char := ['6', '4', '5', '9', '7', '5', '9', '0', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_physicalVolumeText : String := String.ofList (geometryRow053_physicalVolumeNumeratorChars ++ '/' :: geometryRow053_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_physicalVolume_before_field"
  err.flush

theorem geometryRow053_physicalVolume_field :
    geometryRowsJson053.getObjVal? "physical_volume" = .ok (.str geometryRow053_physicalVolumeText) := by rfl

theorem geometryRow053_physicalVolume_numerator_no_slash :
    geometryRow053_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeNumeratorChars = some (4307771552777623075702250018991281 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow053_physicalVolumeDenominatorChars = some (645975904608000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_physicalVolume_denominator_nonzero : (645975904608000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_physicalVolume_parse :
    parseRational geometryRow053_physicalVolumeText = .ok geometryRowsTyped053.physicalVolume :=
  original_rational_fraction_of_chars geometryRow053_physicalVolumeNumeratorChars geometryRow053_physicalVolumeDenominatorChars
    (4307771552777623075702250018991281 : Int) (645975904608000000000000000000000000000000000000000000000000 : Int)
    geometryRow053_physicalVolume_numerator_no_slash geometryRow053_physicalVolume_numerator_parse
    geometryRow053_physicalVolume_denominator_parse geometryRow053_physicalVolume_denominator_nonzero

theorem geometryRow053_physicalVolume_read :
    rationalField geometryRowsJson053 "physical_volume" = .ok geometryRowsTyped053.physicalVolume :=
  original_rationalField_of_string geometryRowsJson053 "physical_volume" geometryRow053_physicalVolumeText
    geometryRowsTyped053.physicalVolume geometryRow053_physicalVolume_field geometryRow053_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_physicalVolume_complete"
  err.flush

noncomputable def geometryRow053_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow053_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_meanGapText : String := String.ofList (geometryRow053_meanGapNumeratorChars ++ '/' :: geometryRow053_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_meanGap_before_field"
  err.flush

theorem geometryRow053_meanGap_field :
    geometryRowsJson053.getObjVal? "mean_gap" = .ok (.str geometryRow053_meanGapText) := by rfl

theorem geometryRow053_meanGap_numerator_no_slash :
    geometryRow053_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_meanGap_numerator_parse :
    SourceJson.intChars geometryRow053_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_parse :
    SourceJson.intChars geometryRow053_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow053_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_meanGap_parse :
    parseRational geometryRow053_meanGapText = .ok geometryRowsTyped053.meanGap :=
  original_rational_fraction_of_chars geometryRow053_meanGapNumeratorChars geometryRow053_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow053_meanGap_numerator_no_slash geometryRow053_meanGap_numerator_parse
    geometryRow053_meanGap_denominator_parse geometryRow053_meanGap_denominator_nonzero

theorem geometryRow053_meanGap_read :
    rationalField geometryRowsJson053 "mean_gap" = .ok geometryRowsTyped053.meanGap :=
  original_rationalField_of_string geometryRowsJson053 "mean_gap" geometryRow053_meanGapText
    geometryRowsTyped053.meanGap geometryRow053_meanGap_field geometryRow053_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_meanGap_complete"
  err.flush

noncomputable def geometryRow053_jensenBoundNumeratorChars : List Char := ['1', '1', '9', '3', '6', '8', '5', '0', '8', '0', '0', '3', '5', '2', '7', '5', '1', '3', '9', '7', '6', '0', '8', '5', '9', '1', '0', '6', '4', '8', '9', '9', '7', '4', '9', '1', '5', '3', '2', '3', '2', '1', '9', '2', '5', '5', '8', '3', '0', '5', '3', '8', '7', '8', '0', '2', '8', '2', '0', '9', '4', '7', '5', '9', '4', '2', '7', '6', '0', '8', '4', '5', '9', '4', '8', '0', '5', '3', '3', '3', '0', '2', '8', '1', '0', '4', '1', '9', '7', '3', '4', '6', '8', '8', '0', '6', '3', '8', '2', '4', '1', '4', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow053_jensenBoundDenominatorChars : List Char := ['1', '0', '8', '7', '9', '0', '8', '6', '2', '7', '1', '2', '9', '4', '4', '1', '0', '6', '4', '1', '3', '0', '1', '9', '6', '6', '2', '2', '8', '9', '5', '7', '6', '2', '3', '9', '1', '5', '1', '4', '5', '6', '7', '4', '9', '1', '5', '9', '1', '5', '3', '6', '8', '2', '1', '6', '4', '5', '2', '2', '6', '1', '5', '0', '7', '0', '9', '0', '5', '6', '4', '7', '6', '9', '2', '3', '9', '4', '1', '6', '9', '1', '2', '9', '2', '3', '8', '3', '5', '8', '1', '0', '8', '0', '6', '2', '3', '0', '6', '3', '1', '7', '6', '9', '1', '8', '7', '8', '4', '7', '9', '4', '9', '7', '6', '2', '9', '8', '9', '0', '8', '4', '5', '4', '7', '6', '9', '4', '6', '6', '8', '6', '3', '8', '1', '8', '0', '1', '4', '6', '4', '5', '1', '1']
noncomputable def geometryRow053_jensenBoundText : String := String.ofList (geometryRow053_jensenBoundNumeratorChars ++ '/' :: geometryRow053_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_jensenBound_before_field"
  err.flush

theorem geometryRow053_jensenBound_field :
    geometryRowsJson053.getObjVal? "jensen_bound" = .ok (.str geometryRow053_jensenBoundText) := by rfl

theorem geometryRow053_jensenBound_numerator_no_slash :
    geometryRow053_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow053_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow053_jensenBoundNumeratorChars = some (1193685080035275139760859106489974915323219255830538780282094759427608459480533302810419734688063824140500000000000000000000000 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow053_jensenBoundDenominatorChars = some (108790862712944106413019662289576239151456749159153682164522615070905647692394169129238358108062306317691878479497629890845476946686381801464511 : Int) := by decide +kernel

theorem geometryRow053_jensenBound_denominator_nonzero : (108790862712944106413019662289576239151456749159153682164522615070905647692394169129238358108062306317691878479497629890845476946686381801464511 : Int) ≠ 0 := by decide +kernel

theorem geometryRow053_jensenBound_parse :
    parseRational geometryRow053_jensenBoundText = .ok geometryRowsTyped053.jensenBound :=
  original_rational_fraction_of_chars geometryRow053_jensenBoundNumeratorChars geometryRow053_jensenBoundDenominatorChars
    (1193685080035275139760859106489974915323219255830538780282094759427608459480533302810419734688063824140500000000000000000000000 : Int) (108790862712944106413019662289576239151456749159153682164522615070905647692394169129238358108062306317691878479497629890845476946686381801464511 : Int)
    geometryRow053_jensenBound_numerator_no_slash geometryRow053_jensenBound_numerator_parse
    geometryRow053_jensenBound_denominator_parse geometryRow053_jensenBound_denominator_nonzero

theorem geometryRow053_jensenBound_read :
    rationalField geometryRowsJson053 "jensen_bound" = .ok geometryRowsTyped053.jensenBound :=
  original_rationalField_of_string geometryRowsJson053 "jensen_bound" geometryRow053_jensenBoundText
    geometryRowsTyped053.jensenBound geometryRow053_jensenBound_field geometryRow053_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_factorMaxima_before"
  err.flush

theorem geometryRow053_factorMaxima_read :
    rationalArrayField geometryRowsJson053 "factor_maxima" = .ok geometryRowsTyped053.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_gapWeightedMeans_before"
  err.flush

theorem geometryRow053_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson053 "gap_weighted_means" = .ok geometryRowsTyped053.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow053_floorChars : List Char := ['8', '6', '9', '3', '1', '4', '5', '1', '0', '0', '0', '0']
noncomputable def geometryRow053_floorText : String := String.ofList geometryRow053_floorChars

theorem geometryRow053_floor_text_read :
    geometryRowsJson053.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow053_floorText := by rfl

theorem geometryRow053_floor_chars_parse :
    SourceJson.intChars geometryRow053_floorChars = some (869314510000 : Int) := by decide +kernel

theorem geometryRow053_floor_parse :
    parseInteger geometryRow053_floorText = .ok geometryRowsTyped053.jensenFloorQ96 := by
  simp only [geometryRow053_floorText, parseInteger, String.toList_ofList, geometryRow053_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_053 :
    decodeGeometryRow geometryRowsJson053 = .ok geometryRowsTyped053 :=
  original_geometryRow_of_fields geometryRowsJson053 geometryRowsTyped053 geometryRow053_floorText
    geometryRow053_simplexId_read geometryRow053_vertexIds_read
    geometryRow053_physicalVolume_read geometryRow053_meanGap_read
    geometryRow053_factorMaxima_read geometryRow053_gapWeightedMeans_read
    geometryRow053_jensenBound_read geometryRow053_floor_text_read geometryRow053_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_053_original_decoder_complete"
  err.flush

theorem geometryRow053_shape :
    geometryRowsTyped053.simplexId = 53 ∧
    geometryRowsTyped053.vertexIds.size = 9 ∧ geometryRowsTyped053.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped053.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped053.factorMaxima.size = 10 ∧ geometryRowsTyped053.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson054 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped054 : GeometryRow :=
  { simplexId := 54,
    vertexIds := #[27, 26, 24, 23, 21, 19, 17, 5, 1],
    physicalVolume := ((2267075571427022258495120545121797 : ℚ) / (397116334800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((9247662222343 : ℚ) / (105921900000000 : ℚ)), ((18597508236221 : ℚ) / (211843800000000 : ℚ)), ((1754765536169 : ℚ) / (14122920000000 : ℚ)), ((10090027744439 : ℚ) / (105921900000000 : ℚ)), ((9688719253051 : ℚ) / (105921900000000 : ℚ)), ((986886746557 : ℚ) / (14122920000000 : ℚ)), ((4011558685229 : ℚ) / (105921900000000 : ℚ)), ((6591120297857 : ℚ) / (211843800000000 : ℚ)), ((6346232947247 : ℚ) / (211843800000000 : ℚ)), ((6346218824327 : ℚ) / (211843800000000 : ℚ))],
    jensenBound := ((309426188147938373930471353637807397018692617493752631447563924827674864471222905827120960000000000000000000000 : ℚ) / (31005254721755451573903579611299679888205153241330301195218088415932403539340861254976979570919575283234605080982616630701234727 : ℚ)),
    jensenFloorQ96 := (790681081021 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_simplexId_before"
  err.flush

theorem geometryRow054_simplexId_read :
    geometryRowsJson054.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped054.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_vertexIds_before"
  err.flush

theorem geometryRow054_vertexIds_read :
    geometryRowsJson054.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped054.vertexIds := by decide +kernel

noncomputable def geometryRow054_physicalVolumeNumeratorChars : List Char := ['2', '2', '6', '7', '0', '7', '5', '5', '7', '1', '4', '2', '7', '0', '2', '2', '2', '5', '8', '4', '9', '5', '1', '2', '0', '5', '4', '5', '1', '2', '1', '7', '9', '7']
noncomputable def geometryRow054_physicalVolumeDenominatorChars : List Char := ['3', '9', '7', '1', '1', '6', '3', '3', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_physicalVolumeText : String := String.ofList (geometryRow054_physicalVolumeNumeratorChars ++ '/' :: geometryRow054_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_physicalVolume_before_field"
  err.flush

theorem geometryRow054_physicalVolume_field :
    geometryRowsJson054.getObjVal? "physical_volume" = .ok (.str geometryRow054_physicalVolumeText) := by rfl

theorem geometryRow054_physicalVolume_numerator_no_slash :
    geometryRow054_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeNumeratorChars = some (2267075571427022258495120545121797 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow054_physicalVolumeDenominatorChars = some (397116334800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_physicalVolume_denominator_nonzero : (397116334800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_physicalVolume_parse :
    parseRational geometryRow054_physicalVolumeText = .ok geometryRowsTyped054.physicalVolume :=
  original_rational_fraction_of_chars geometryRow054_physicalVolumeNumeratorChars geometryRow054_physicalVolumeDenominatorChars
    (2267075571427022258495120545121797 : Int) (397116334800000000000000000000000000000000000000000000000000 : Int)
    geometryRow054_physicalVolume_numerator_no_slash geometryRow054_physicalVolume_numerator_parse
    geometryRow054_physicalVolume_denominator_parse geometryRow054_physicalVolume_denominator_nonzero

theorem geometryRow054_physicalVolume_read :
    rationalField geometryRowsJson054 "physical_volume" = .ok geometryRowsTyped054.physicalVolume :=
  original_rationalField_of_string geometryRowsJson054 "physical_volume" geometryRow054_physicalVolumeText
    geometryRowsTyped054.physicalVolume geometryRow054_physicalVolume_field geometryRow054_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_physicalVolume_complete"
  err.flush

noncomputable def geometryRow054_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow054_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_meanGapText : String := String.ofList (geometryRow054_meanGapNumeratorChars ++ '/' :: geometryRow054_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_meanGap_before_field"
  err.flush

theorem geometryRow054_meanGap_field :
    geometryRowsJson054.getObjVal? "mean_gap" = .ok (.str geometryRow054_meanGapText) := by rfl

theorem geometryRow054_meanGap_numerator_no_slash :
    geometryRow054_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_meanGap_numerator_parse :
    SourceJson.intChars geometryRow054_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_parse :
    SourceJson.intChars geometryRow054_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow054_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_meanGap_parse :
    parseRational geometryRow054_meanGapText = .ok geometryRowsTyped054.meanGap :=
  original_rational_fraction_of_chars geometryRow054_meanGapNumeratorChars geometryRow054_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow054_meanGap_numerator_no_slash geometryRow054_meanGap_numerator_parse
    geometryRow054_meanGap_denominator_parse geometryRow054_meanGap_denominator_nonzero

theorem geometryRow054_meanGap_read :
    rationalField geometryRowsJson054 "mean_gap" = .ok geometryRowsTyped054.meanGap :=
  original_rationalField_of_string geometryRowsJson054 "mean_gap" geometryRow054_meanGapText
    geometryRowsTyped054.meanGap geometryRow054_meanGap_field geometryRow054_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_meanGap_complete"
  err.flush

noncomputable def geometryRow054_jensenBoundNumeratorChars : List Char := ['3', '0', '9', '4', '2', '6', '1', '8', '8', '1', '4', '7', '9', '3', '8', '3', '7', '3', '9', '3', '0', '4', '7', '1', '3', '5', '3', '6', '3', '7', '8', '0', '7', '3', '9', '7', '0', '1', '8', '6', '9', '2', '6', '1', '7', '4', '9', '3', '7', '5', '2', '6', '3', '1', '4', '4', '7', '5', '6', '3', '9', '2', '4', '8', '2', '7', '6', '7', '4', '8', '6', '4', '4', '7', '1', '2', '2', '2', '9', '0', '5', '8', '2', '7', '1', '2', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow054_jensenBoundDenominatorChars : List Char := ['3', '1', '0', '0', '5', '2', '5', '4', '7', '2', '1', '7', '5', '5', '4', '5', '1', '5', '7', '3', '9', '0', '3', '5', '7', '9', '6', '1', '1', '2', '9', '9', '6', '7', '9', '8', '8', '8', '2', '0', '5', '1', '5', '3', '2', '4', '1', '3', '3', '0', '3', '0', '1', '1', '9', '5', '2', '1', '8', '0', '8', '8', '4', '1', '5', '9', '3', '2', '4', '0', '3', '5', '3', '9', '3', '4', '0', '8', '6', '1', '2', '5', '4', '9', '7', '6', '9', '7', '9', '5', '7', '0', '9', '1', '9', '5', '7', '5', '2', '8', '3', '2', '3', '4', '6', '0', '5', '0', '8', '0', '9', '8', '2', '6', '1', '6', '6', '3', '0', '7', '0', '1', '2', '3', '4', '7', '2', '7']
noncomputable def geometryRow054_jensenBoundText : String := String.ofList (geometryRow054_jensenBoundNumeratorChars ++ '/' :: geometryRow054_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_jensenBound_before_field"
  err.flush

theorem geometryRow054_jensenBound_field :
    geometryRowsJson054.getObjVal? "jensen_bound" = .ok (.str geometryRow054_jensenBoundText) := by rfl

theorem geometryRow054_jensenBound_numerator_no_slash :
    geometryRow054_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow054_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow054_jensenBoundNumeratorChars = some (309426188147938373930471353637807397018692617493752631447563924827674864471222905827120960000000000000000000000 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow054_jensenBoundDenominatorChars = some (31005254721755451573903579611299679888205153241330301195218088415932403539340861254976979570919575283234605080982616630701234727 : Int) := by decide +kernel

theorem geometryRow054_jensenBound_denominator_nonzero : (31005254721755451573903579611299679888205153241330301195218088415932403539340861254976979570919575283234605080982616630701234727 : Int) ≠ 0 := by decide +kernel

theorem geometryRow054_jensenBound_parse :
    parseRational geometryRow054_jensenBoundText = .ok geometryRowsTyped054.jensenBound :=
  original_rational_fraction_of_chars geometryRow054_jensenBoundNumeratorChars geometryRow054_jensenBoundDenominatorChars
    (309426188147938373930471353637807397018692617493752631447563924827674864471222905827120960000000000000000000000 : Int) (31005254721755451573903579611299679888205153241330301195218088415932403539340861254976979570919575283234605080982616630701234727 : Int)
    geometryRow054_jensenBound_numerator_no_slash geometryRow054_jensenBound_numerator_parse
    geometryRow054_jensenBound_denominator_parse geometryRow054_jensenBound_denominator_nonzero

theorem geometryRow054_jensenBound_read :
    rationalField geometryRowsJson054 "jensen_bound" = .ok geometryRowsTyped054.jensenBound :=
  original_rationalField_of_string geometryRowsJson054 "jensen_bound" geometryRow054_jensenBoundText
    geometryRowsTyped054.jensenBound geometryRow054_jensenBound_field geometryRow054_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_factorMaxima_before"
  err.flush

theorem geometryRow054_factorMaxima_read :
    rationalArrayField geometryRowsJson054 "factor_maxima" = .ok geometryRowsTyped054.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_gapWeightedMeans_before"
  err.flush

theorem geometryRow054_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson054 "gap_weighted_means" = .ok geometryRowsTyped054.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow054_floorChars : List Char := ['7', '9', '0', '6', '8', '1', '0', '8', '1', '0', '2', '1']
noncomputable def geometryRow054_floorText : String := String.ofList geometryRow054_floorChars

theorem geometryRow054_floor_text_read :
    geometryRowsJson054.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow054_floorText := by rfl

theorem geometryRow054_floor_chars_parse :
    SourceJson.intChars geometryRow054_floorChars = some (790681081021 : Int) := by decide +kernel

theorem geometryRow054_floor_parse :
    parseInteger geometryRow054_floorText = .ok geometryRowsTyped054.jensenFloorQ96 := by
  simp only [geometryRow054_floorText, parseInteger, String.toList_ofList, geometryRow054_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_054 :
    decodeGeometryRow geometryRowsJson054 = .ok geometryRowsTyped054 :=
  original_geometryRow_of_fields geometryRowsJson054 geometryRowsTyped054 geometryRow054_floorText
    geometryRow054_simplexId_read geometryRow054_vertexIds_read
    geometryRow054_physicalVolume_read geometryRow054_meanGap_read
    geometryRow054_factorMaxima_read geometryRow054_gapWeightedMeans_read
    geometryRow054_jensenBound_read geometryRow054_floor_text_read geometryRow054_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_054_original_decoder_complete"
  err.flush

theorem geometryRow054_shape :
    geometryRowsTyped054.simplexId = 54 ∧
    geometryRowsTyped054.vertexIds.size = 9 ∧ geometryRowsTyped054.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped054.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped054.factorMaxima.size = 10 ∧ geometryRowsTyped054.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson055 : SourceJson :=
  (SimplicesBlock006.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped055 : GeometryRow :=
  { simplexId := 55,
    vertexIds := #[27, 26, 24, 23, 21, 19, 17, 15, 5],
    physicalVolume := ((2868689372422588752679362924357847 : ℚ) / (860418725400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((7905277 : ℚ) / (15912000000 : ℚ)),
    factorMaxima := #[((12984403 : ℚ) / (136000000 : ℚ)), ((3328101 : ℚ) / (34000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2546871 : ℚ) / (34000000 : ℚ)), ((515593 : ℚ) / (12000000 : ℚ)), ((2328113 : ℚ) / (68000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ)), ((1109367 : ℚ) / (34000000 : ℚ))],
    gapWeightedMeans := #[((268069649263295478623 : ℚ) / (3110127279503400000000 : ℚ)), ((1298845749655138301 : ℚ) / (14952534997612500000 : ℚ)), ((2171553463620186431 : ℚ) / (17278484886130000000 : ℚ)), ((151427102836561871627 : ℚ) / (1555063639751700000000 : ℚ)), ((144748623688769604103 : ℚ) / (1555063639751700000000 : ℚ)), ((2352250819037946897 : ℚ) / (34556969772260000000 : ℚ)), ((28181468544655699201 : ℚ) / (777531819875850000000 : ℚ)), ((48100507304372478103 : ℚ) / (1555063639751700000000 : ℚ)), ((110832185943310133 : ℚ) / (3738133749403125000 : ℚ)), ((886655493875148049 : ℚ) / (29905069995225000000 : ℚ))],
    jensenBound := ((136222846047640795099418541312820997585177287347439826358617137292765403995316224836582276853355641068647753178221940499018642785279521578397987499614257812500000000000 : ℚ) / (11763562203323570775686952637987820988275818029714947387823485816577262880327908871601396355135477811669163402126990780861397252095419903600041256149207041865429105980920367626041295851 : ℚ)),
    jensenFloorQ96 := (917467481216 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_simplexId_before"
  err.flush

theorem geometryRow055_simplexId_read :
    geometryRowsJson055.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped055.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_vertexIds_before"
  err.flush

theorem geometryRow055_vertexIds_read :
    geometryRowsJson055.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped055.vertexIds := by decide +kernel

noncomputable def geometryRow055_physicalVolumeNumeratorChars : List Char := ['2', '8', '6', '8', '6', '8', '9', '3', '7', '2', '4', '2', '2', '5', '8', '8', '7', '5', '2', '6', '7', '9', '3', '6', '2', '9', '2', '4', '3', '5', '7', '8', '4', '7']
noncomputable def geometryRow055_physicalVolumeDenominatorChars : List Char := ['8', '6', '0', '4', '1', '8', '7', '2', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_physicalVolumeText : String := String.ofList (geometryRow055_physicalVolumeNumeratorChars ++ '/' :: geometryRow055_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_physicalVolume_before_field"
  err.flush

theorem geometryRow055_physicalVolume_field :
    geometryRowsJson055.getObjVal? "physical_volume" = .ok (.str geometryRow055_physicalVolumeText) := by rfl

theorem geometryRow055_physicalVolume_numerator_no_slash :
    geometryRow055_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeNumeratorChars = some (2868689372422588752679362924357847 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow055_physicalVolumeDenominatorChars = some (860418725400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow055_physicalVolume_denominator_nonzero : (860418725400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_physicalVolume_parse :
    parseRational geometryRow055_physicalVolumeText = .ok geometryRowsTyped055.physicalVolume :=
  original_rational_fraction_of_chars geometryRow055_physicalVolumeNumeratorChars geometryRow055_physicalVolumeDenominatorChars
    (2868689372422588752679362924357847 : Int) (860418725400000000000000000000000000000000000000000000000000 : Int)
    geometryRow055_physicalVolume_numerator_no_slash geometryRow055_physicalVolume_numerator_parse
    geometryRow055_physicalVolume_denominator_parse geometryRow055_physicalVolume_denominator_nonzero

theorem geometryRow055_physicalVolume_read :
    rationalField geometryRowsJson055 "physical_volume" = .ok geometryRowsTyped055.physicalVolume :=
  original_rationalField_of_string geometryRowsJson055 "physical_volume" geometryRow055_physicalVolumeText
    geometryRowsTyped055.physicalVolume geometryRow055_physicalVolume_field geometryRow055_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_physicalVolume_complete"
  err.flush

noncomputable def geometryRow055_meanGapNumeratorChars : List Char := ['7', '9', '0', '5', '2', '7', '7']
noncomputable def geometryRow055_meanGapDenominatorChars : List Char := ['1', '5', '9', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_meanGapText : String := String.ofList (geometryRow055_meanGapNumeratorChars ++ '/' :: geometryRow055_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_meanGap_before_field"
  err.flush

theorem geometryRow055_meanGap_field :
    geometryRowsJson055.getObjVal? "mean_gap" = .ok (.str geometryRow055_meanGapText) := by rfl

theorem geometryRow055_meanGap_numerator_no_slash :
    geometryRow055_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_meanGap_numerator_parse :
    SourceJson.intChars geometryRow055_meanGapNumeratorChars = some (7905277 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_parse :
    SourceJson.intChars geometryRow055_meanGapDenominatorChars = some (15912000000 : Int) := by decide +kernel

theorem geometryRow055_meanGap_denominator_nonzero : (15912000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_meanGap_parse :
    parseRational geometryRow055_meanGapText = .ok geometryRowsTyped055.meanGap :=
  original_rational_fraction_of_chars geometryRow055_meanGapNumeratorChars geometryRow055_meanGapDenominatorChars
    (7905277 : Int) (15912000000 : Int)
    geometryRow055_meanGap_numerator_no_slash geometryRow055_meanGap_numerator_parse
    geometryRow055_meanGap_denominator_parse geometryRow055_meanGap_denominator_nonzero

theorem geometryRow055_meanGap_read :
    rationalField geometryRowsJson055 "mean_gap" = .ok geometryRowsTyped055.meanGap :=
  original_rationalField_of_string geometryRowsJson055 "mean_gap" geometryRow055_meanGapText
    geometryRowsTyped055.meanGap geometryRow055_meanGap_field geometryRow055_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_meanGap_complete"
  err.flush

noncomputable def geometryRow055_jensenBoundNumeratorChars : List Char := ['1', '3', '6', '2', '2', '2', '8', '4', '6', '0', '4', '7', '6', '4', '0', '7', '9', '5', '0', '9', '9', '4', '1', '8', '5', '4', '1', '3', '1', '2', '8', '2', '0', '9', '9', '7', '5', '8', '5', '1', '7', '7', '2', '8', '7', '3', '4', '7', '4', '3', '9', '8', '2', '6', '3', '5', '8', '6', '1', '7', '1', '3', '7', '2', '9', '2', '7', '6', '5', '4', '0', '3', '9', '9', '5', '3', '1', '6', '2', '2', '4', '8', '3', '6', '5', '8', '2', '2', '7', '6', '8', '5', '3', '3', '5', '5', '6', '4', '1', '0', '6', '8', '6', '4', '7', '7', '5', '3', '1', '7', '8', '2', '2', '1', '9', '4', '0', '4', '9', '9', '0', '1', '8', '6', '4', '2', '7', '8', '5', '2', '7', '9', '5', '2', '1', '5', '7', '8', '3', '9', '7', '9', '8', '7', '4', '9', '9', '6', '1', '4', '2', '5', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow055_jensenBoundDenominatorChars : List Char := ['1', '1', '7', '6', '3', '5', '6', '2', '2', '0', '3', '3', '2', '3', '5', '7', '0', '7', '7', '5', '6', '8', '6', '9', '5', '2', '6', '3', '7', '9', '8', '7', '8', '2', '0', '9', '8', '8', '2', '7', '5', '8', '1', '8', '0', '2', '9', '7', '1', '4', '9', '4', '7', '3', '8', '7', '8', '2', '3', '4', '8', '5', '8', '1', '6', '5', '7', '7', '2', '6', '2', '8', '8', '0', '3', '2', '7', '9', '0', '8', '8', '7', '1', '6', '0', '1', '3', '9', '6', '3', '5', '5', '1', '3', '5', '4', '7', '7', '8', '1', '1', '6', '6', '9', '1', '6', '3', '4', '0', '2', '1', '2', '6', '9', '9', '0', '7', '8', '0', '8', '6', '1', '3', '9', '7', '2', '5', '2', '0', '9', '5', '4', '1', '9', '9', '0', '3', '6', '0', '0', '0', '4', '1', '2', '5', '6', '1', '4', '9', '2', '0', '7', '0', '4', '1', '8', '6', '5', '4', '2', '9', '1', '0', '5', '9', '8', '0', '9', '2', '0', '3', '6', '7', '6', '2', '6', '0', '4', '1', '2', '9', '5', '8', '5', '1']
noncomputable def geometryRow055_jensenBoundText : String := String.ofList (geometryRow055_jensenBoundNumeratorChars ++ '/' :: geometryRow055_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_jensenBound_before_field"
  err.flush

theorem geometryRow055_jensenBound_field :
    geometryRowsJson055.getObjVal? "jensen_bound" = .ok (.str geometryRow055_jensenBoundText) := by rfl

theorem geometryRow055_jensenBound_numerator_no_slash :
    geometryRow055_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow055_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow055_jensenBoundNumeratorChars = some (136222846047640795099418541312820997585177287347439826358617137292765403995316224836582276853355641068647753178221940499018642785279521578397987499614257812500000000000 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow055_jensenBoundDenominatorChars = some (11763562203323570775686952637987820988275818029714947387823485816577262880327908871601396355135477811669163402126990780861397252095419903600041256149207041865429105980920367626041295851 : Int) := by decide +kernel

theorem geometryRow055_jensenBound_denominator_nonzero : (11763562203323570775686952637987820988275818029714947387823485816577262880327908871601396355135477811669163402126990780861397252095419903600041256149207041865429105980920367626041295851 : Int) ≠ 0 := by decide +kernel

theorem geometryRow055_jensenBound_parse :
    parseRational geometryRow055_jensenBoundText = .ok geometryRowsTyped055.jensenBound :=
  original_rational_fraction_of_chars geometryRow055_jensenBoundNumeratorChars geometryRow055_jensenBoundDenominatorChars
    (136222846047640795099418541312820997585177287347439826358617137292765403995316224836582276853355641068647753178221940499018642785279521578397987499614257812500000000000 : Int) (11763562203323570775686952637987820988275818029714947387823485816577262880327908871601396355135477811669163402126990780861397252095419903600041256149207041865429105980920367626041295851 : Int)
    geometryRow055_jensenBound_numerator_no_slash geometryRow055_jensenBound_numerator_parse
    geometryRow055_jensenBound_denominator_parse geometryRow055_jensenBound_denominator_nonzero

theorem geometryRow055_jensenBound_read :
    rationalField geometryRowsJson055 "jensen_bound" = .ok geometryRowsTyped055.jensenBound :=
  original_rationalField_of_string geometryRowsJson055 "jensen_bound" geometryRow055_jensenBoundText
    geometryRowsTyped055.jensenBound geometryRow055_jensenBound_field geometryRow055_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_factorMaxima_before"
  err.flush

theorem geometryRow055_factorMaxima_read :
    rationalArrayField geometryRowsJson055 "factor_maxima" = .ok geometryRowsTyped055.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_gapWeightedMeans_before"
  err.flush

theorem geometryRow055_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson055 "gap_weighted_means" = .ok geometryRowsTyped055.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow055_floorChars : List Char := ['9', '1', '7', '4', '6', '7', '4', '8', '1', '2', '1', '6']
noncomputable def geometryRow055_floorText : String := String.ofList geometryRow055_floorChars

theorem geometryRow055_floor_text_read :
    geometryRowsJson055.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow055_floorText := by rfl

theorem geometryRow055_floor_chars_parse :
    SourceJson.intChars geometryRow055_floorChars = some (917467481216 : Int) := by decide +kernel

theorem geometryRow055_floor_parse :
    parseInteger geometryRow055_floorText = .ok geometryRowsTyped055.jensenFloorQ96 := by
  simp only [geometryRow055_floorText, parseInteger, String.toList_ofList, geometryRow055_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_055 :
    decodeGeometryRow geometryRowsJson055 = .ok geometryRowsTyped055 :=
  original_geometryRow_of_fields geometryRowsJson055 geometryRowsTyped055 geometryRow055_floorText
    geometryRow055_simplexId_read geometryRow055_vertexIds_read
    geometryRow055_physicalVolume_read geometryRow055_meanGap_read
    geometryRow055_factorMaxima_read geometryRow055_gapWeightedMeans_read
    geometryRow055_jensenBound_read geometryRow055_floor_text_read geometryRow055_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_055_original_decoder_complete"
  err.flush

theorem geometryRow055_shape :
    geometryRowsTyped055.simplexId = 55 ∧
    geometryRowsTyped055.vertexIds.size = 9 ∧ geometryRowsTyped055.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped055.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped055.factorMaxima.size = 10 ∧ geometryRowsTyped055.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock006 : List SourceJson := [geometryRowsJson048, geometryRowsJson049, geometryRowsJson050, geometryRowsJson051, geometryRowsJson052, geometryRowsJson053, geometryRowsJson054, geometryRowsJson055]
noncomputable def geometryRowsTypedBlock006 : List GeometryRow := [geometryRowsTyped048, geometryRowsTyped049, geometryRowsTyped050, geometryRowsTyped051, geometryRowsTyped052, geometryRowsTyped053, geometryRowsTyped054, geometryRowsTyped055]

theorem geometry_Rows_block_006_push_eq (acc : List SourceJson) :
    SimplicesBlock006.blockPush acc = [geometryRowsJson055, geometryRowsJson054, geometryRowsJson053, geometryRowsJson052, geometryRowsJson051, geometryRowsJson050, geometryRowsJson049, geometryRowsJson048] ++ acc := by rfl

theorem geometry_Rows_block_006_reverse (acc : List SourceJson) :
    (SimplicesBlock006.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock006 := by
  rw [geometry_Rows_block_006_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_006 :
    geometryRowsJsonBlock006.mapM decodeGeometryRow = .ok geometryRowsTypedBlock006 := by
  simp only [geometryRowsJsonBlock006, geometryRowsTypedBlock006, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_048, decode_geometry_Rows_049, decode_geometry_Rows_050, decode_geometry_Rows_051, decode_geometry_Rows_052, decode_geometry_Rows_053, decode_geometry_Rows_054, decode_geometry_Rows_055]
  rfl

theorem geometry_Rows_block_006_length : geometryRowsTypedBlock006.length = 8 := by rfl

#print axioms geometryRow048_simplexId_read
#print axioms geometryRow048_vertexIds_read
#print axioms geometryRow048_physicalVolume_field
#print axioms geometryRow048_physicalVolume_numerator_no_slash
#print axioms geometryRow048_physicalVolume_numerator_parse
#print axioms geometryRow048_physicalVolume_denominator_parse
#print axioms geometryRow048_physicalVolume_denominator_nonzero
#print axioms geometryRow048_physicalVolume_parse
#print axioms geometryRow048_physicalVolume_read
#print axioms geometryRow048_meanGap_field
#print axioms geometryRow048_meanGap_numerator_no_slash
#print axioms geometryRow048_meanGap_numerator_parse
#print axioms geometryRow048_meanGap_denominator_parse
#print axioms geometryRow048_meanGap_denominator_nonzero
#print axioms geometryRow048_meanGap_parse
#print axioms geometryRow048_meanGap_read
#print axioms geometryRow048_jensenBound_field
#print axioms geometryRow048_jensenBound_numerator_no_slash
#print axioms geometryRow048_jensenBound_numerator_parse
#print axioms geometryRow048_jensenBound_denominator_parse
#print axioms geometryRow048_jensenBound_denominator_nonzero
#print axioms geometryRow048_jensenBound_parse
#print axioms geometryRow048_jensenBound_read
#print axioms geometryRow048_factorMaxima_read
#print axioms geometryRow048_gapWeightedMeans_read
#print axioms geometryRow048_floor_text_read
#print axioms geometryRow048_floor_chars_parse
#print axioms geometryRow048_floor_parse
#print axioms decode_geometry_Rows_048
#print axioms geometryRow048_shape
#print axioms geometryRow049_simplexId_read
#print axioms geometryRow049_vertexIds_read
#print axioms geometryRow049_physicalVolume_field
#print axioms geometryRow049_physicalVolume_numerator_no_slash
#print axioms geometryRow049_physicalVolume_numerator_parse
#print axioms geometryRow049_physicalVolume_denominator_parse
#print axioms geometryRow049_physicalVolume_denominator_nonzero
#print axioms geometryRow049_physicalVolume_parse
#print axioms geometryRow049_physicalVolume_read
#print axioms geometryRow049_meanGap_field
#print axioms geometryRow049_meanGap_numerator_no_slash
#print axioms geometryRow049_meanGap_numerator_parse
#print axioms geometryRow049_meanGap_denominator_parse
#print axioms geometryRow049_meanGap_denominator_nonzero
#print axioms geometryRow049_meanGap_parse
#print axioms geometryRow049_meanGap_read
#print axioms geometryRow049_jensenBound_field
#print axioms geometryRow049_jensenBound_numerator_no_slash
#print axioms geometryRow049_jensenBound_numerator_parse
#print axioms geometryRow049_jensenBound_denominator_parse
#print axioms geometryRow049_jensenBound_denominator_nonzero
#print axioms geometryRow049_jensenBound_parse
#print axioms geometryRow049_jensenBound_read
#print axioms geometryRow049_factorMaxima_read
#print axioms geometryRow049_gapWeightedMeans_read
#print axioms geometryRow049_floor_text_read
#print axioms geometryRow049_floor_chars_parse
#print axioms geometryRow049_floor_parse
#print axioms decode_geometry_Rows_049
#print axioms geometryRow049_shape
#print axioms geometryRow050_simplexId_read
#print axioms geometryRow050_vertexIds_read
#print axioms geometryRow050_physicalVolume_field
#print axioms geometryRow050_physicalVolume_numerator_no_slash
#print axioms geometryRow050_physicalVolume_numerator_parse
#print axioms geometryRow050_physicalVolume_denominator_parse
#print axioms geometryRow050_physicalVolume_denominator_nonzero
#print axioms geometryRow050_physicalVolume_parse
#print axioms geometryRow050_physicalVolume_read
#print axioms geometryRow050_meanGap_field
#print axioms geometryRow050_meanGap_numerator_no_slash
#print axioms geometryRow050_meanGap_numerator_parse
#print axioms geometryRow050_meanGap_denominator_parse
#print axioms geometryRow050_meanGap_denominator_nonzero
#print axioms geometryRow050_meanGap_parse
#print axioms geometryRow050_meanGap_read
#print axioms geometryRow050_jensenBound_field
#print axioms geometryRow050_jensenBound_numerator_no_slash
#print axioms geometryRow050_jensenBound_numerator_parse
#print axioms geometryRow050_jensenBound_denominator_parse
#print axioms geometryRow050_jensenBound_denominator_nonzero
#print axioms geometryRow050_jensenBound_parse
#print axioms geometryRow050_jensenBound_read
#print axioms geometryRow050_factorMaxima_read
#print axioms geometryRow050_gapWeightedMeans_read
#print axioms geometryRow050_floor_text_read
#print axioms geometryRow050_floor_chars_parse
#print axioms geometryRow050_floor_parse
#print axioms decode_geometry_Rows_050
#print axioms geometryRow050_shape
#print axioms geometryRow051_simplexId_read
#print axioms geometryRow051_vertexIds_read
#print axioms geometryRow051_physicalVolume_field
#print axioms geometryRow051_physicalVolume_numerator_no_slash
#print axioms geometryRow051_physicalVolume_numerator_parse
#print axioms geometryRow051_physicalVolume_denominator_parse
#print axioms geometryRow051_physicalVolume_denominator_nonzero
#print axioms geometryRow051_physicalVolume_parse
#print axioms geometryRow051_physicalVolume_read
#print axioms geometryRow051_meanGap_field
#print axioms geometryRow051_meanGap_numerator_no_slash
#print axioms geometryRow051_meanGap_numerator_parse
#print axioms geometryRow051_meanGap_denominator_parse
#print axioms geometryRow051_meanGap_denominator_nonzero
#print axioms geometryRow051_meanGap_parse
#print axioms geometryRow051_meanGap_read
#print axioms geometryRow051_jensenBound_field
#print axioms geometryRow051_jensenBound_numerator_no_slash
#print axioms geometryRow051_jensenBound_numerator_parse
#print axioms geometryRow051_jensenBound_denominator_parse
#print axioms geometryRow051_jensenBound_denominator_nonzero
#print axioms geometryRow051_jensenBound_parse
#print axioms geometryRow051_jensenBound_read
#print axioms geometryRow051_factorMaxima_read
#print axioms geometryRow051_gapWeightedMeans_read
#print axioms geometryRow051_floor_text_read
#print axioms geometryRow051_floor_chars_parse
#print axioms geometryRow051_floor_parse
#print axioms decode_geometry_Rows_051
#print axioms geometryRow051_shape
#print axioms geometryRow052_simplexId_read
#print axioms geometryRow052_vertexIds_read
#print axioms geometryRow052_physicalVolume_field
#print axioms geometryRow052_physicalVolume_numerator_no_slash
#print axioms geometryRow052_physicalVolume_numerator_parse
#print axioms geometryRow052_physicalVolume_denominator_parse
#print axioms geometryRow052_physicalVolume_denominator_nonzero
#print axioms geometryRow052_physicalVolume_parse
#print axioms geometryRow052_physicalVolume_read
#print axioms geometryRow052_meanGap_field
#print axioms geometryRow052_meanGap_numerator_no_slash
#print axioms geometryRow052_meanGap_numerator_parse
#print axioms geometryRow052_meanGap_denominator_parse
#print axioms geometryRow052_meanGap_denominator_nonzero
#print axioms geometryRow052_meanGap_parse
#print axioms geometryRow052_meanGap_read
#print axioms geometryRow052_jensenBound_field
#print axioms geometryRow052_jensenBound_numerator_no_slash
#print axioms geometryRow052_jensenBound_numerator_parse
#print axioms geometryRow052_jensenBound_denominator_parse
#print axioms geometryRow052_jensenBound_denominator_nonzero
#print axioms geometryRow052_jensenBound_parse
#print axioms geometryRow052_jensenBound_read
#print axioms geometryRow052_factorMaxima_read
#print axioms geometryRow052_gapWeightedMeans_read
#print axioms geometryRow052_floor_text_read
#print axioms geometryRow052_floor_chars_parse
#print axioms geometryRow052_floor_parse
#print axioms decode_geometry_Rows_052
#print axioms geometryRow052_shape
#print axioms geometryRow053_simplexId_read
#print axioms geometryRow053_vertexIds_read
#print axioms geometryRow053_physicalVolume_field
#print axioms geometryRow053_physicalVolume_numerator_no_slash
#print axioms geometryRow053_physicalVolume_numerator_parse
#print axioms geometryRow053_physicalVolume_denominator_parse
#print axioms geometryRow053_physicalVolume_denominator_nonzero
#print axioms geometryRow053_physicalVolume_parse
#print axioms geometryRow053_physicalVolume_read
#print axioms geometryRow053_meanGap_field
#print axioms geometryRow053_meanGap_numerator_no_slash
#print axioms geometryRow053_meanGap_numerator_parse
#print axioms geometryRow053_meanGap_denominator_parse
#print axioms geometryRow053_meanGap_denominator_nonzero
#print axioms geometryRow053_meanGap_parse
#print axioms geometryRow053_meanGap_read
#print axioms geometryRow053_jensenBound_field
#print axioms geometryRow053_jensenBound_numerator_no_slash
#print axioms geometryRow053_jensenBound_numerator_parse
#print axioms geometryRow053_jensenBound_denominator_parse
#print axioms geometryRow053_jensenBound_denominator_nonzero
#print axioms geometryRow053_jensenBound_parse
#print axioms geometryRow053_jensenBound_read
#print axioms geometryRow053_factorMaxima_read
#print axioms geometryRow053_gapWeightedMeans_read
#print axioms geometryRow053_floor_text_read
#print axioms geometryRow053_floor_chars_parse
#print axioms geometryRow053_floor_parse
#print axioms decode_geometry_Rows_053
#print axioms geometryRow053_shape
#print axioms geometryRow054_simplexId_read
#print axioms geometryRow054_vertexIds_read
#print axioms geometryRow054_physicalVolume_field
#print axioms geometryRow054_physicalVolume_numerator_no_slash
#print axioms geometryRow054_physicalVolume_numerator_parse
#print axioms geometryRow054_physicalVolume_denominator_parse
#print axioms geometryRow054_physicalVolume_denominator_nonzero
#print axioms geometryRow054_physicalVolume_parse
#print axioms geometryRow054_physicalVolume_read
#print axioms geometryRow054_meanGap_field
#print axioms geometryRow054_meanGap_numerator_no_slash
#print axioms geometryRow054_meanGap_numerator_parse
#print axioms geometryRow054_meanGap_denominator_parse
#print axioms geometryRow054_meanGap_denominator_nonzero
#print axioms geometryRow054_meanGap_parse
#print axioms geometryRow054_meanGap_read
#print axioms geometryRow054_jensenBound_field
#print axioms geometryRow054_jensenBound_numerator_no_slash
#print axioms geometryRow054_jensenBound_numerator_parse
#print axioms geometryRow054_jensenBound_denominator_parse
#print axioms geometryRow054_jensenBound_denominator_nonzero
#print axioms geometryRow054_jensenBound_parse
#print axioms geometryRow054_jensenBound_read
#print axioms geometryRow054_factorMaxima_read
#print axioms geometryRow054_gapWeightedMeans_read
#print axioms geometryRow054_floor_text_read
#print axioms geometryRow054_floor_chars_parse
#print axioms geometryRow054_floor_parse
#print axioms decode_geometry_Rows_054
#print axioms geometryRow054_shape
#print axioms geometryRow055_simplexId_read
#print axioms geometryRow055_vertexIds_read
#print axioms geometryRow055_physicalVolume_field
#print axioms geometryRow055_physicalVolume_numerator_no_slash
#print axioms geometryRow055_physicalVolume_numerator_parse
#print axioms geometryRow055_physicalVolume_denominator_parse
#print axioms geometryRow055_physicalVolume_denominator_nonzero
#print axioms geometryRow055_physicalVolume_parse
#print axioms geometryRow055_physicalVolume_read
#print axioms geometryRow055_meanGap_field
#print axioms geometryRow055_meanGap_numerator_no_slash
#print axioms geometryRow055_meanGap_numerator_parse
#print axioms geometryRow055_meanGap_denominator_parse
#print axioms geometryRow055_meanGap_denominator_nonzero
#print axioms geometryRow055_meanGap_parse
#print axioms geometryRow055_meanGap_read
#print axioms geometryRow055_jensenBound_field
#print axioms geometryRow055_jensenBound_numerator_no_slash
#print axioms geometryRow055_jensenBound_numerator_parse
#print axioms geometryRow055_jensenBound_denominator_parse
#print axioms geometryRow055_jensenBound_denominator_nonzero
#print axioms geometryRow055_jensenBound_parse
#print axioms geometryRow055_jensenBound_read
#print axioms geometryRow055_factorMaxima_read
#print axioms geometryRow055_gapWeightedMeans_read
#print axioms geometryRow055_floor_text_read
#print axioms geometryRow055_floor_chars_parse
#print axioms geometryRow055_floor_parse
#print axioms decode_geometry_Rows_055
#print axioms geometryRow055_shape
#print axioms geometry_Rows_block_006_push_eq
#print axioms geometry_Rows_block_006_reverse
#print axioms decode_geometry_Rows_block_006
#print axioms geometry_Rows_block_006_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
