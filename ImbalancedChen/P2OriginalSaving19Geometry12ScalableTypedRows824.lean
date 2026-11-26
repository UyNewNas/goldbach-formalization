import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry12ScalableSimplicesBlock824

/-! Local typed certificates for original cell 12, rows 6592 through 6599.
This owner imports only its own original parser leaf.  No cumulative typed
prefix, whole-array parser value, or completed geometric archive is imported.
The original rational decoder and GeometryRow record fields are unchanged. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry12ScalableDecoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19Geometry12ScalableParsing
open ImbalancedChen.P2OriginalSaving19Geometry00Decoding

noncomputable def geometryRowsJson6592 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped6592 : GeometryRow :=
  { simplexId := 6592,
    vertexIds := #[139, 137, 135, 117, 115, 84, 66, 56, 27],
    physicalVolume := ((216713846281248389929814790110962902884554921 : ℚ) / (92603511539933184000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((2015269 : ℚ) / (2988000000 : ℚ)),
    factorMaxima := #[((449201 : ℚ) / (8750000 : ℚ)), ((449201 : ℚ) / (8750000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((31358779 : ℚ) / (372000000 : ℚ)), ((2656247 : ℚ) / (35000000 : ℚ)), ((12421691 : ℚ) / (186000000 : ℚ)), ((156249 : ℚ) / (4375000 : ℚ)), ((156249 : ℚ) / (4375000 : ℚ))],
    gapWeightedMeans := #[((883187470077206873 : ℚ) / (23924104957200000000 : ℚ)), ((912231751446478853 : ℚ) / (23924104957200000000 : ℚ)), ((75378364062250213 : ℚ) / (629581709400000000 : ℚ)), ((459529308437625479 : ℚ) / (4784820991440000000 : ℚ)), ((896014345333657 : ℚ) / (10493028490000000 : ℚ)), ((45420407788865303 : ℚ) / (629581709400000000 : ℚ)), ((44651531424923603 : ℚ) / (629581709400000000 : ℚ)), ((6430433641190687 : ℚ) / (104930284900000000 : ℚ)), ((655364326338320359 : ℚ) / (23924104957200000000 : ℚ)), ((624867703125839059 : ℚ) / (23924104957200000000 : ℚ))],
    jensenBound := ((31433075674188270332714944203221430386074364268854223733173501974202449761086151253945866757812337713051365514594784691094554884934000000000000000000000000 : ℚ) / (1543761631149983450014967910876207318476155219642751263940613905280867643520254908170354675306820418441005449005526906440056348872035863390553729648230834194697925499 : ℚ)),
    jensenFloorQ96 := (1613192592422842221 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_simplexId_before"
  err.flush

theorem geometryRow6592_simplexId_read :
    geometryRowsJson6592.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6592.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_vertexIds_before"
  err.flush

theorem geometryRow6592_vertexIds_read :
    geometryRowsJson6592.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6592.vertexIds := by decide +kernel

noncomputable def geometryRow6592_physicalVolumeNumeratorChars : List Char := ['2', '1', '6', '7', '1', '3', '8', '4', '6', '2', '8', '1', '2', '4', '8', '3', '8', '9', '9', '2', '9', '8', '1', '4', '7', '9', '0', '1', '1', '0', '9', '6', '2', '9', '0', '2', '8', '8', '4', '5', '5', '4', '9', '2', '1']
noncomputable def geometryRow6592_physicalVolumeDenominatorChars : List Char := ['9', '2', '6', '0', '3', '5', '1', '1', '5', '3', '9', '9', '3', '3', '1', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6592_physicalVolumeText : String := String.ofList (geometryRow6592_physicalVolumeNumeratorChars ++ '/' :: geometryRow6592_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_physicalVolume_before_field"
  err.flush

theorem geometryRow6592_physicalVolume_field :
    geometryRowsJson6592.getObjVal? "physical_volume" = .ok (.str geometryRow6592_physicalVolumeText) := by rfl

theorem geometryRow6592_physicalVolume_numerator_no_slash :
    geometryRow6592_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6592_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6592_physicalVolumeNumeratorChars = some (216713846281248389929814790110962902884554921 : Int) := by decide +kernel

theorem geometryRow6592_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6592_physicalVolumeDenominatorChars = some (92603511539933184000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6592_physicalVolume_denominator_nonzero : (92603511539933184000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6592_physicalVolume_parse :
    parseRational geometryRow6592_physicalVolumeText = .ok geometryRowsTyped6592.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6592_physicalVolumeNumeratorChars geometryRow6592_physicalVolumeDenominatorChars
    (216713846281248389929814790110962902884554921 : Int) (92603511539933184000000000000000000000000000000000000000000000000 : Int)
    geometryRow6592_physicalVolume_numerator_no_slash geometryRow6592_physicalVolume_numerator_parse
    geometryRow6592_physicalVolume_denominator_parse geometryRow6592_physicalVolume_denominator_nonzero

theorem geometryRow6592_physicalVolume_read :
    rationalField geometryRowsJson6592 "physical_volume" = .ok geometryRowsTyped6592.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6592 "physical_volume" geometryRow6592_physicalVolumeText
    geometryRowsTyped6592.physicalVolume geometryRow6592_physicalVolume_field geometryRow6592_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6592_meanGapNumeratorChars : List Char := ['2', '0', '1', '5', '2', '6', '9']
noncomputable def geometryRow6592_meanGapDenominatorChars : List Char := ['2', '9', '8', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6592_meanGapText : String := String.ofList (geometryRow6592_meanGapNumeratorChars ++ '/' :: geometryRow6592_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_meanGap_before_field"
  err.flush

theorem geometryRow6592_meanGap_field :
    geometryRowsJson6592.getObjVal? "mean_gap" = .ok (.str geometryRow6592_meanGapText) := by rfl

theorem geometryRow6592_meanGap_numerator_no_slash :
    geometryRow6592_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6592_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6592_meanGapNumeratorChars = some (2015269 : Int) := by decide +kernel

theorem geometryRow6592_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6592_meanGapDenominatorChars = some (2988000000 : Int) := by decide +kernel

theorem geometryRow6592_meanGap_denominator_nonzero : (2988000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6592_meanGap_parse :
    parseRational geometryRow6592_meanGapText = .ok geometryRowsTyped6592.meanGap :=
  original_rational_fraction_of_chars geometryRow6592_meanGapNumeratorChars geometryRow6592_meanGapDenominatorChars
    (2015269 : Int) (2988000000 : Int)
    geometryRow6592_meanGap_numerator_no_slash geometryRow6592_meanGap_numerator_parse
    geometryRow6592_meanGap_denominator_parse geometryRow6592_meanGap_denominator_nonzero

theorem geometryRow6592_meanGap_read :
    rationalField geometryRowsJson6592 "mean_gap" = .ok geometryRowsTyped6592.meanGap :=
  original_rationalField_of_string geometryRowsJson6592 "mean_gap" geometryRow6592_meanGapText
    geometryRowsTyped6592.meanGap geometryRow6592_meanGap_field geometryRow6592_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_meanGap_complete"
  err.flush

noncomputable def geometryRow6592_jensenBoundNumeratorChars : List Char := ['3', '1', '4', '3', '3', '0', '7', '5', '6', '7', '4', '1', '8', '8', '2', '7', '0', '3', '3', '2', '7', '1', '4', '9', '4', '4', '2', '0', '3', '2', '2', '1', '4', '3', '0', '3', '8', '6', '0', '7', '4', '3', '6', '4', '2', '6', '8', '8', '5', '4', '2', '2', '3', '7', '3', '3', '1', '7', '3', '5', '0', '1', '9', '7', '4', '2', '0', '2', '4', '4', '9', '7', '6', '1', '0', '8', '6', '1', '5', '1', '2', '5', '3', '9', '4', '5', '8', '6', '6', '7', '5', '7', '8', '1', '2', '3', '3', '7', '7', '1', '3', '0', '5', '1', '3', '6', '5', '5', '1', '4', '5', '9', '4', '7', '8', '4', '6', '9', '1', '0', '9', '4', '5', '5', '4', '8', '8', '4', '9', '3', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6592_jensenBoundDenominatorChars : List Char := ['1', '5', '4', '3', '7', '6', '1', '6', '3', '1', '1', '4', '9', '9', '8', '3', '4', '5', '0', '0', '1', '4', '9', '6', '7', '9', '1', '0', '8', '7', '6', '2', '0', '7', '3', '1', '8', '4', '7', '6', '1', '5', '5', '2', '1', '9', '6', '4', '2', '7', '5', '1', '2', '6', '3', '9', '4', '0', '6', '1', '3', '9', '0', '5', '2', '8', '0', '8', '6', '7', '6', '4', '3', '5', '2', '0', '2', '5', '4', '9', '0', '8', '1', '7', '0', '3', '5', '4', '6', '7', '5', '3', '0', '6', '8', '2', '0', '4', '1', '8', '4', '4', '1', '0', '0', '5', '4', '4', '9', '0', '0', '5', '5', '2', '6', '9', '0', '6', '4', '4', '0', '0', '5', '6', '3', '4', '8', '8', '7', '2', '0', '3', '5', '8', '6', '3', '3', '9', '0', '5', '5', '3', '7', '2', '9', '6', '4', '8', '2', '3', '0', '8', '3', '4', '1', '9', '4', '6', '9', '7', '9', '2', '5', '4', '9', '9']
noncomputable def geometryRow6592_jensenBoundText : String := String.ofList (geometryRow6592_jensenBoundNumeratorChars ++ '/' :: geometryRow6592_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_jensenBound_before_field"
  err.flush

theorem geometryRow6592_jensenBound_field :
    geometryRowsJson6592.getObjVal? "jensen_bound" = .ok (.str geometryRow6592_jensenBoundText) := by rfl

theorem geometryRow6592_jensenBound_numerator_no_slash :
    geometryRow6592_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6592_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6592_jensenBoundNumeratorChars = some (31433075674188270332714944203221430386074364268854223733173501974202449761086151253945866757812337713051365514594784691094554884934000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6592_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6592_jensenBoundDenominatorChars = some (1543761631149983450014967910876207318476155219642751263940613905280867643520254908170354675306820418441005449005526906440056348872035863390553729648230834194697925499 : Int) := by decide +kernel

theorem geometryRow6592_jensenBound_denominator_nonzero : (1543761631149983450014967910876207318476155219642751263940613905280867643520254908170354675306820418441005449005526906440056348872035863390553729648230834194697925499 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6592_jensenBound_parse :
    parseRational geometryRow6592_jensenBoundText = .ok geometryRowsTyped6592.jensenBound :=
  original_rational_fraction_of_chars geometryRow6592_jensenBoundNumeratorChars geometryRow6592_jensenBoundDenominatorChars
    (31433075674188270332714944203221430386074364268854223733173501974202449761086151253945866757812337713051365514594784691094554884934000000000000000000000000 : Int) (1543761631149983450014967910876207318476155219642751263940613905280867643520254908170354675306820418441005449005526906440056348872035863390553729648230834194697925499 : Int)
    geometryRow6592_jensenBound_numerator_no_slash geometryRow6592_jensenBound_numerator_parse
    geometryRow6592_jensenBound_denominator_parse geometryRow6592_jensenBound_denominator_nonzero

theorem geometryRow6592_jensenBound_read :
    rationalField geometryRowsJson6592 "jensen_bound" = .ok geometryRowsTyped6592.jensenBound :=
  original_rationalField_of_string geometryRowsJson6592 "jensen_bound" geometryRow6592_jensenBoundText
    geometryRowsTyped6592.jensenBound geometryRow6592_jensenBound_field geometryRow6592_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_factorMaxima_before"
  err.flush

theorem geometryRow6592_factorMaxima_read :
    rationalArrayField geometryRowsJson6592 "factor_maxima" = .ok geometryRowsTyped6592.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_gapWeightedMeans_before"
  err.flush

theorem geometryRow6592_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6592 "gap_weighted_means" = .ok geometryRowsTyped6592.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6592_floorChars : List Char := ['1', '6', '1', '3', '1', '9', '2', '5', '9', '2', '4', '2', '2', '8', '4', '2', '2', '2', '1']
noncomputable def geometryRow6592_floorText : String := String.ofList geometryRow6592_floorChars

theorem geometryRow6592_floor_text_read :
    geometryRowsJson6592.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6592_floorText := by rfl

theorem geometryRow6592_floor_chars_parse :
    SourceJson.intChars geometryRow6592_floorChars = some (1613192592422842221 : Int) := by decide +kernel

theorem geometryRow6592_floor_parse :
    parseInteger geometryRow6592_floorText = .ok geometryRowsTyped6592.jensenFloorQ96 := by
  simp only [geometryRow6592_floorText, parseInteger, String.toList_ofList, geometryRow6592_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6592 :
    decodeGeometryRow geometryRowsJson6592 = .ok geometryRowsTyped6592 :=
  original_geometryRow_of_fields geometryRowsJson6592 geometryRowsTyped6592 geometryRow6592_floorText
    geometryRow6592_simplexId_read geometryRow6592_vertexIds_read
    geometryRow6592_physicalVolume_read geometryRow6592_meanGap_read
    geometryRow6592_factorMaxima_read geometryRow6592_gapWeightedMeans_read
    geometryRow6592_jensenBound_read geometryRow6592_floor_text_read geometryRow6592_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6592_original_decoder_complete"
  err.flush

theorem geometryRow6592_shape :
    geometryRowsTyped6592.simplexId = 6592 ∧
    geometryRowsTyped6592.vertexIds.size = 9 ∧ geometryRowsTyped6592.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6592.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6592.factorMaxima.size = 10 ∧ geometryRowsTyped6592.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6593 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped6593 : GeometryRow :=
  { simplexId := 6593,
    vertexIds := #[139, 137, 135, 117, 115, 111, 106, 97, 55],
    physicalVolume := ((47813019883345503741095334814150051 : ℚ) / (72180740653056000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((526507 : ℚ) / (621000000 : ℚ)),
    factorMaxima := #[((1171879 : ℚ) / (24000000 : ℚ)), ((1171879 : ℚ) / (24000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((388979 : ℚ) / (4000000 : ℚ)), ((296871 : ℚ) / (4000000 : ℚ)), ((296871 : ℚ) / (4000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((11 : ℚ) / (384 : ℚ)), ((11 : ℚ) / (384 : ℚ))],
    gapWeightedMeans := #[((34983292261981 : ℚ) / (1082746160000000 : ℚ)), ((7246799992637 : ℚ) / (216549232000000 : ℚ)), ((59860734678573 : ℚ) / (484386440000000 : ℚ)), ((5548010415149737 : ℚ) / (55220054160000000 : ℚ)), ((43509214386171 : ℚ) / (484386440000000 : ℚ)), ((6717062745001 : ℚ) / (96877288000000 : ℚ)), ((16734809432173 : ℚ) / (242193220000000 : ℚ)), ((86786178193889 : ℚ) / (1453159320000000 : ℚ)), ((1474186274719853 : ℚ) / (55220054160000000 : ℚ)), ((1403795963838713 : ℚ) / (55220054160000000 : ℚ))],
    jensenBound := ((115183969514811888201953661485568134361563285525221212537370876674829396670685963695100990395379252062151731200000000000000000 : ℚ) / (12006442193098398510560374343393533265215035142770072970146175295831272153375889405506133514206559602534557700675277063477812916258072174561 : ℚ)),
    jensenFloorQ96 := (760076474694837 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_simplexId_before"
  err.flush

theorem geometryRow6593_simplexId_read :
    geometryRowsJson6593.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6593.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_vertexIds_before"
  err.flush

theorem geometryRow6593_vertexIds_read :
    geometryRowsJson6593.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6593.vertexIds := by decide +kernel

noncomputable def geometryRow6593_physicalVolumeNumeratorChars : List Char := ['4', '7', '8', '1', '3', '0', '1', '9', '8', '8', '3', '3', '4', '5', '5', '0', '3', '7', '4', '1', '0', '9', '5', '3', '3', '4', '8', '1', '4', '1', '5', '0', '0', '5', '1']
noncomputable def geometryRow6593_physicalVolumeDenominatorChars : List Char := ['7', '2', '1', '8', '0', '7', '4', '0', '6', '5', '3', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6593_physicalVolumeText : String := String.ofList (geometryRow6593_physicalVolumeNumeratorChars ++ '/' :: geometryRow6593_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_physicalVolume_before_field"
  err.flush

theorem geometryRow6593_physicalVolume_field :
    geometryRowsJson6593.getObjVal? "physical_volume" = .ok (.str geometryRow6593_physicalVolumeText) := by rfl

theorem geometryRow6593_physicalVolume_numerator_no_slash :
    geometryRow6593_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6593_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6593_physicalVolumeNumeratorChars = some (47813019883345503741095334814150051 : Int) := by decide +kernel

theorem geometryRow6593_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6593_physicalVolumeDenominatorChars = some (72180740653056000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6593_physicalVolume_denominator_nonzero : (72180740653056000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6593_physicalVolume_parse :
    parseRational geometryRow6593_physicalVolumeText = .ok geometryRowsTyped6593.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6593_physicalVolumeNumeratorChars geometryRow6593_physicalVolumeDenominatorChars
    (47813019883345503741095334814150051 : Int) (72180740653056000000000000000000000000000000000000000000000 : Int)
    geometryRow6593_physicalVolume_numerator_no_slash geometryRow6593_physicalVolume_numerator_parse
    geometryRow6593_physicalVolume_denominator_parse geometryRow6593_physicalVolume_denominator_nonzero

theorem geometryRow6593_physicalVolume_read :
    rationalField geometryRowsJson6593 "physical_volume" = .ok geometryRowsTyped6593.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6593 "physical_volume" geometryRow6593_physicalVolumeText
    geometryRowsTyped6593.physicalVolume geometryRow6593_physicalVolume_field geometryRow6593_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6593_meanGapNumeratorChars : List Char := ['5', '2', '6', '5', '0', '7']
noncomputable def geometryRow6593_meanGapDenominatorChars : List Char := ['6', '2', '1', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6593_meanGapText : String := String.ofList (geometryRow6593_meanGapNumeratorChars ++ '/' :: geometryRow6593_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_meanGap_before_field"
  err.flush

theorem geometryRow6593_meanGap_field :
    geometryRowsJson6593.getObjVal? "mean_gap" = .ok (.str geometryRow6593_meanGapText) := by rfl

theorem geometryRow6593_meanGap_numerator_no_slash :
    geometryRow6593_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6593_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6593_meanGapNumeratorChars = some (526507 : Int) := by decide +kernel

theorem geometryRow6593_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6593_meanGapDenominatorChars = some (621000000 : Int) := by decide +kernel

theorem geometryRow6593_meanGap_denominator_nonzero : (621000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6593_meanGap_parse :
    parseRational geometryRow6593_meanGapText = .ok geometryRowsTyped6593.meanGap :=
  original_rational_fraction_of_chars geometryRow6593_meanGapNumeratorChars geometryRow6593_meanGapDenominatorChars
    (526507 : Int) (621000000 : Int)
    geometryRow6593_meanGap_numerator_no_slash geometryRow6593_meanGap_numerator_parse
    geometryRow6593_meanGap_denominator_parse geometryRow6593_meanGap_denominator_nonzero

theorem geometryRow6593_meanGap_read :
    rationalField geometryRowsJson6593 "mean_gap" = .ok geometryRowsTyped6593.meanGap :=
  original_rationalField_of_string geometryRowsJson6593 "mean_gap" geometryRow6593_meanGapText
    geometryRowsTyped6593.meanGap geometryRow6593_meanGap_field geometryRow6593_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_meanGap_complete"
  err.flush

noncomputable def geometryRow6593_jensenBoundNumeratorChars : List Char := ['1', '1', '5', '1', '8', '3', '9', '6', '9', '5', '1', '4', '8', '1', '1', '8', '8', '8', '2', '0', '1', '9', '5', '3', '6', '6', '1', '4', '8', '5', '5', '6', '8', '1', '3', '4', '3', '6', '1', '5', '6', '3', '2', '8', '5', '5', '2', '5', '2', '2', '1', '2', '1', '2', '5', '3', '7', '3', '7', '0', '8', '7', '6', '6', '7', '4', '8', '2', '9', '3', '9', '6', '6', '7', '0', '6', '8', '5', '9', '6', '3', '6', '9', '5', '1', '0', '0', '9', '9', '0', '3', '9', '5', '3', '7', '9', '2', '5', '2', '0', '6', '2', '1', '5', '1', '7', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6593_jensenBoundDenominatorChars : List Char := ['1', '2', '0', '0', '6', '4', '4', '2', '1', '9', '3', '0', '9', '8', '3', '9', '8', '5', '1', '0', '5', '6', '0', '3', '7', '4', '3', '4', '3', '3', '9', '3', '5', '3', '3', '2', '6', '5', '2', '1', '5', '0', '3', '5', '1', '4', '2', '7', '7', '0', '0', '7', '2', '9', '7', '0', '1', '4', '6', '1', '7', '5', '2', '9', '5', '8', '3', '1', '2', '7', '2', '1', '5', '3', '3', '7', '5', '8', '8', '9', '4', '0', '5', '5', '0', '6', '1', '3', '3', '5', '1', '4', '2', '0', '6', '5', '5', '9', '6', '0', '2', '5', '3', '4', '5', '5', '7', '7', '0', '0', '6', '7', '5', '2', '7', '7', '0', '6', '3', '4', '7', '7', '8', '1', '2', '9', '1', '6', '2', '5', '8', '0', '7', '2', '1', '7', '4', '5', '6', '1']
noncomputable def geometryRow6593_jensenBoundText : String := String.ofList (geometryRow6593_jensenBoundNumeratorChars ++ '/' :: geometryRow6593_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_jensenBound_before_field"
  err.flush

theorem geometryRow6593_jensenBound_field :
    geometryRowsJson6593.getObjVal? "jensen_bound" = .ok (.str geometryRow6593_jensenBoundText) := by rfl

theorem geometryRow6593_jensenBound_numerator_no_slash :
    geometryRow6593_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6593_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6593_jensenBoundNumeratorChars = some (115183969514811888201953661485568134361563285525221212537370876674829396670685963695100990395379252062151731200000000000000000 : Int) := by decide +kernel

theorem geometryRow6593_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6593_jensenBoundDenominatorChars = some (12006442193098398510560374343393533265215035142770072970146175295831272153375889405506133514206559602534557700675277063477812916258072174561 : Int) := by decide +kernel

theorem geometryRow6593_jensenBound_denominator_nonzero : (12006442193098398510560374343393533265215035142770072970146175295831272153375889405506133514206559602534557700675277063477812916258072174561 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6593_jensenBound_parse :
    parseRational geometryRow6593_jensenBoundText = .ok geometryRowsTyped6593.jensenBound :=
  original_rational_fraction_of_chars geometryRow6593_jensenBoundNumeratorChars geometryRow6593_jensenBoundDenominatorChars
    (115183969514811888201953661485568134361563285525221212537370876674829396670685963695100990395379252062151731200000000000000000 : Int) (12006442193098398510560374343393533265215035142770072970146175295831272153375889405506133514206559602534557700675277063477812916258072174561 : Int)
    geometryRow6593_jensenBound_numerator_no_slash geometryRow6593_jensenBound_numerator_parse
    geometryRow6593_jensenBound_denominator_parse geometryRow6593_jensenBound_denominator_nonzero

theorem geometryRow6593_jensenBound_read :
    rationalField geometryRowsJson6593 "jensen_bound" = .ok geometryRowsTyped6593.jensenBound :=
  original_rationalField_of_string geometryRowsJson6593 "jensen_bound" geometryRow6593_jensenBoundText
    geometryRowsTyped6593.jensenBound geometryRow6593_jensenBound_field geometryRow6593_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_factorMaxima_before"
  err.flush

theorem geometryRow6593_factorMaxima_read :
    rationalArrayField geometryRowsJson6593 "factor_maxima" = .ok geometryRowsTyped6593.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_gapWeightedMeans_before"
  err.flush

theorem geometryRow6593_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6593 "gap_weighted_means" = .ok geometryRowsTyped6593.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6593_floorChars : List Char := ['7', '6', '0', '0', '7', '6', '4', '7', '4', '6', '9', '4', '8', '3', '7']
noncomputable def geometryRow6593_floorText : String := String.ofList geometryRow6593_floorChars

theorem geometryRow6593_floor_text_read :
    geometryRowsJson6593.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6593_floorText := by rfl

theorem geometryRow6593_floor_chars_parse :
    SourceJson.intChars geometryRow6593_floorChars = some (760076474694837 : Int) := by decide +kernel

theorem geometryRow6593_floor_parse :
    parseInteger geometryRow6593_floorText = .ok geometryRowsTyped6593.jensenFloorQ96 := by
  simp only [geometryRow6593_floorText, parseInteger, String.toList_ofList, geometryRow6593_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6593 :
    decodeGeometryRow geometryRowsJson6593 = .ok geometryRowsTyped6593 :=
  original_geometryRow_of_fields geometryRowsJson6593 geometryRowsTyped6593 geometryRow6593_floorText
    geometryRow6593_simplexId_read geometryRow6593_vertexIds_read
    geometryRow6593_physicalVolume_read geometryRow6593_meanGap_read
    geometryRow6593_factorMaxima_read geometryRow6593_gapWeightedMeans_read
    geometryRow6593_jensenBound_read geometryRow6593_floor_text_read geometryRow6593_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6593_original_decoder_complete"
  err.flush

theorem geometryRow6593_shape :
    geometryRowsTyped6593.simplexId = 6593 ∧
    geometryRowsTyped6593.vertexIds.size = 9 ∧ geometryRowsTyped6593.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6593.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6593.factorMaxima.size = 10 ∧ geometryRowsTyped6593.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6594 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped6594 : GeometryRow :=
  { simplexId := 6594,
    vertexIds := #[139, 137, 135, 117, 98, 84, 83, 56, 27],
    physicalVolume := ((6855835562383991943329675529956149912419919 : ℚ) / (1007398818349056000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((2015269 : ℚ) / (2988000000 : ℚ)),
    factorMaxima := #[((109369 : ℚ) / (2000000 : ℚ)), ((109369 : ℚ) / (2000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((208129 : ℚ) / (2208000 : ℚ)), ((31358779 : ℚ) / (372000000 : ℚ)), ((2656247 : ℚ) / (35000000 : ℚ)), ((12421691 : ℚ) / (186000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ))],
    gapWeightedMeans := #[((125278906631987 : ℚ) / (3148322800000000 : ℚ)), ((129101025512007 : ℚ) / (3148322800000000 : ℚ)), ((22319344899767 : ℚ) / (186413850000000 : ℚ)), ((540136679297959 : ℚ) / (5666981040000000 : ℚ)), ((2460615495109 : ℚ) / (29826216000000 : ℚ)), ((27148441533629 : ℚ) / (372827700000000 : ℚ)), ((79748160928417 : ℚ) / (1118483100000000 : ℚ)), ((33472376421499 : ℚ) / (559241550000000 : ℚ)), ((796831012673849 : ℚ) / (28334905200000000 : ℚ)), ((760711837925549 : ℚ) / (28334905200000000 : ℚ))],
    jensenBound := ((119287799872304813662298106746692880937618503164986353924728431274398867671889402071521597864201237812987581250000000000000000000 : ℚ) / (2341706899216674258025975565959211506754306189474414854029352334982234452074816352060699574855169826378204939772539495080665937852509042139 : ℚ)),
    jensenFloorQ96 := (4035924904783536464 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_simplexId_before"
  err.flush

theorem geometryRow6594_simplexId_read :
    geometryRowsJson6594.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6594.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_vertexIds_before"
  err.flush

theorem geometryRow6594_vertexIds_read :
    geometryRowsJson6594.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6594.vertexIds := by decide +kernel

noncomputable def geometryRow6594_physicalVolumeNumeratorChars : List Char := ['6', '8', '5', '5', '8', '3', '5', '5', '6', '2', '3', '8', '3', '9', '9', '1', '9', '4', '3', '3', '2', '9', '6', '7', '5', '5', '2', '9', '9', '5', '6', '1', '4', '9', '9', '1', '2', '4', '1', '9', '9', '1', '9']
noncomputable def geometryRow6594_physicalVolumeDenominatorChars : List Char := ['1', '0', '0', '7', '3', '9', '8', '8', '1', '8', '3', '4', '9', '0', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6594_physicalVolumeText : String := String.ofList (geometryRow6594_physicalVolumeNumeratorChars ++ '/' :: geometryRow6594_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_physicalVolume_before_field"
  err.flush

theorem geometryRow6594_physicalVolume_field :
    geometryRowsJson6594.getObjVal? "physical_volume" = .ok (.str geometryRow6594_physicalVolumeText) := by rfl

theorem geometryRow6594_physicalVolume_numerator_no_slash :
    geometryRow6594_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6594_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6594_physicalVolumeNumeratorChars = some (6855835562383991943329675529956149912419919 : Int) := by decide +kernel

theorem geometryRow6594_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6594_physicalVolumeDenominatorChars = some (1007398818349056000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6594_physicalVolume_denominator_nonzero : (1007398818349056000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6594_physicalVolume_parse :
    parseRational geometryRow6594_physicalVolumeText = .ok geometryRowsTyped6594.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6594_physicalVolumeNumeratorChars geometryRow6594_physicalVolumeDenominatorChars
    (6855835562383991943329675529956149912419919 : Int) (1007398818349056000000000000000000000000000000000000000000000000 : Int)
    geometryRow6594_physicalVolume_numerator_no_slash geometryRow6594_physicalVolume_numerator_parse
    geometryRow6594_physicalVolume_denominator_parse geometryRow6594_physicalVolume_denominator_nonzero

theorem geometryRow6594_physicalVolume_read :
    rationalField geometryRowsJson6594 "physical_volume" = .ok geometryRowsTyped6594.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6594 "physical_volume" geometryRow6594_physicalVolumeText
    geometryRowsTyped6594.physicalVolume geometryRow6594_physicalVolume_field geometryRow6594_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6594_meanGapNumeratorChars : List Char := ['2', '0', '1', '5', '2', '6', '9']
noncomputable def geometryRow6594_meanGapDenominatorChars : List Char := ['2', '9', '8', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6594_meanGapText : String := String.ofList (geometryRow6594_meanGapNumeratorChars ++ '/' :: geometryRow6594_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_meanGap_before_field"
  err.flush

theorem geometryRow6594_meanGap_field :
    geometryRowsJson6594.getObjVal? "mean_gap" = .ok (.str geometryRow6594_meanGapText) := by rfl

theorem geometryRow6594_meanGap_numerator_no_slash :
    geometryRow6594_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6594_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6594_meanGapNumeratorChars = some (2015269 : Int) := by decide +kernel

theorem geometryRow6594_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6594_meanGapDenominatorChars = some (2988000000 : Int) := by decide +kernel

theorem geometryRow6594_meanGap_denominator_nonzero : (2988000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6594_meanGap_parse :
    parseRational geometryRow6594_meanGapText = .ok geometryRowsTyped6594.meanGap :=
  original_rational_fraction_of_chars geometryRow6594_meanGapNumeratorChars geometryRow6594_meanGapDenominatorChars
    (2015269 : Int) (2988000000 : Int)
    geometryRow6594_meanGap_numerator_no_slash geometryRow6594_meanGap_numerator_parse
    geometryRow6594_meanGap_denominator_parse geometryRow6594_meanGap_denominator_nonzero

theorem geometryRow6594_meanGap_read :
    rationalField geometryRowsJson6594 "mean_gap" = .ok geometryRowsTyped6594.meanGap :=
  original_rationalField_of_string geometryRowsJson6594 "mean_gap" geometryRow6594_meanGapText
    geometryRowsTyped6594.meanGap geometryRow6594_meanGap_field geometryRow6594_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_meanGap_complete"
  err.flush

noncomputable def geometryRow6594_jensenBoundNumeratorChars : List Char := ['1', '1', '9', '2', '8', '7', '7', '9', '9', '8', '7', '2', '3', '0', '4', '8', '1', '3', '6', '6', '2', '2', '9', '8', '1', '0', '6', '7', '4', '6', '6', '9', '2', '8', '8', '0', '9', '3', '7', '6', '1', '8', '5', '0', '3', '1', '6', '4', '9', '8', '6', '3', '5', '3', '9', '2', '4', '7', '2', '8', '4', '3', '1', '2', '7', '4', '3', '9', '8', '8', '6', '7', '6', '7', '1', '8', '8', '9', '4', '0', '2', '0', '7', '1', '5', '2', '1', '5', '9', '7', '8', '6', '4', '2', '0', '1', '2', '3', '7', '8', '1', '2', '9', '8', '7', '5', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6594_jensenBoundDenominatorChars : List Char := ['2', '3', '4', '1', '7', '0', '6', '8', '9', '9', '2', '1', '6', '6', '7', '4', '2', '5', '8', '0', '2', '5', '9', '7', '5', '5', '6', '5', '9', '5', '9', '2', '1', '1', '5', '0', '6', '7', '5', '4', '3', '0', '6', '1', '8', '9', '4', '7', '4', '4', '1', '4', '8', '5', '4', '0', '2', '9', '3', '5', '2', '3', '3', '4', '9', '8', '2', '2', '3', '4', '4', '5', '2', '0', '7', '4', '8', '1', '6', '3', '5', '2', '0', '6', '0', '6', '9', '9', '5', '7', '4', '8', '5', '5', '1', '6', '9', '8', '2', '6', '3', '7', '8', '2', '0', '4', '9', '3', '9', '7', '7', '2', '5', '3', '9', '4', '9', '5', '0', '8', '0', '6', '6', '5', '9', '3', '7', '8', '5', '2', '5', '0', '9', '0', '4', '2', '1', '3', '9']
noncomputable def geometryRow6594_jensenBoundText : String := String.ofList (geometryRow6594_jensenBoundNumeratorChars ++ '/' :: geometryRow6594_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_jensenBound_before_field"
  err.flush

theorem geometryRow6594_jensenBound_field :
    geometryRowsJson6594.getObjVal? "jensen_bound" = .ok (.str geometryRow6594_jensenBoundText) := by rfl

theorem geometryRow6594_jensenBound_numerator_no_slash :
    geometryRow6594_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6594_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6594_jensenBoundNumeratorChars = some (119287799872304813662298106746692880937618503164986353924728431274398867671889402071521597864201237812987581250000000000000000000 : Int) := by decide +kernel

theorem geometryRow6594_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6594_jensenBoundDenominatorChars = some (2341706899216674258025975565959211506754306189474414854029352334982234452074816352060699574855169826378204939772539495080665937852509042139 : Int) := by decide +kernel

theorem geometryRow6594_jensenBound_denominator_nonzero : (2341706899216674258025975565959211506754306189474414854029352334982234452074816352060699574855169826378204939772539495080665937852509042139 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6594_jensenBound_parse :
    parseRational geometryRow6594_jensenBoundText = .ok geometryRowsTyped6594.jensenBound :=
  original_rational_fraction_of_chars geometryRow6594_jensenBoundNumeratorChars geometryRow6594_jensenBoundDenominatorChars
    (119287799872304813662298106746692880937618503164986353924728431274398867671889402071521597864201237812987581250000000000000000000 : Int) (2341706899216674258025975565959211506754306189474414854029352334982234452074816352060699574855169826378204939772539495080665937852509042139 : Int)
    geometryRow6594_jensenBound_numerator_no_slash geometryRow6594_jensenBound_numerator_parse
    geometryRow6594_jensenBound_denominator_parse geometryRow6594_jensenBound_denominator_nonzero

theorem geometryRow6594_jensenBound_read :
    rationalField geometryRowsJson6594 "jensen_bound" = .ok geometryRowsTyped6594.jensenBound :=
  original_rationalField_of_string geometryRowsJson6594 "jensen_bound" geometryRow6594_jensenBoundText
    geometryRowsTyped6594.jensenBound geometryRow6594_jensenBound_field geometryRow6594_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_factorMaxima_before"
  err.flush

theorem geometryRow6594_factorMaxima_read :
    rationalArrayField geometryRowsJson6594 "factor_maxima" = .ok geometryRowsTyped6594.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_gapWeightedMeans_before"
  err.flush

theorem geometryRow6594_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6594 "gap_weighted_means" = .ok geometryRowsTyped6594.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6594_floorChars : List Char := ['4', '0', '3', '5', '9', '2', '4', '9', '0', '4', '7', '8', '3', '5', '3', '6', '4', '6', '4']
noncomputable def geometryRow6594_floorText : String := String.ofList geometryRow6594_floorChars

theorem geometryRow6594_floor_text_read :
    geometryRowsJson6594.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6594_floorText := by rfl

theorem geometryRow6594_floor_chars_parse :
    SourceJson.intChars geometryRow6594_floorChars = some (4035924904783536464 : Int) := by decide +kernel

theorem geometryRow6594_floor_parse :
    parseInteger geometryRow6594_floorText = .ok geometryRowsTyped6594.jensenFloorQ96 := by
  simp only [geometryRow6594_floorText, parseInteger, String.toList_ofList, geometryRow6594_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6594 :
    decodeGeometryRow geometryRowsJson6594 = .ok geometryRowsTyped6594 :=
  original_geometryRow_of_fields geometryRowsJson6594 geometryRowsTyped6594 geometryRow6594_floorText
    geometryRow6594_simplexId_read geometryRow6594_vertexIds_read
    geometryRow6594_physicalVolume_read geometryRow6594_meanGap_read
    geometryRow6594_factorMaxima_read geometryRow6594_gapWeightedMeans_read
    geometryRow6594_jensenBound_read geometryRow6594_floor_text_read geometryRow6594_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6594_original_decoder_complete"
  err.flush

theorem geometryRow6594_shape :
    geometryRowsTyped6594.simplexId = 6594 ∧
    geometryRowsTyped6594.vertexIds.size = 9 ∧ geometryRowsTyped6594.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6594.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6594.factorMaxima.size = 10 ∧ geometryRowsTyped6594.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6595 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped6595 : GeometryRow :=
  { simplexId := 6595,
    vertexIds := #[139, 137, 135, 117, 98, 84, 83, 65, 27],
    physicalVolume := ((20981338176097172613367021763575134440067 : ℚ) / (10675256295424000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((26853527 : ℚ) / (25398000000 : ℚ)),
    factorMaxima := #[((109369 : ℚ) / (2000000 : ℚ)), ((109369 : ℚ) / (2000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((208129 : ℚ) / (2208000 : ℚ)), ((571867 : ℚ) / (7200000 : ℚ)), ((2656247 : ℚ) / (35000000 : ℚ)), ((12421691 : ℚ) / (186000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ))],
    gapWeightedMeans := #[((175808099018701975702939 : ℚ) / (4311722137040295600000000 : ℚ)), ((182118547703310954208549 : ℚ) / (4311722137040295600000000 : ℚ)), ((40876895558028520136897 : ℚ) / (340399116082128600000000 : ℚ)), ((246089442196705548190903 : ℚ) / (2587033282224177360000000 : ℚ)), ((350226660930136926839 : ℚ) / (4254988951026607500000 : ℚ)), ((24496299518129749096147 : ℚ) / (340399116082128600000000 : ℚ)), ((73045799133878940033551 : ℚ) / (1021197348246385800000000 : ℚ)), ((7299371294501926737473 : ℚ) / (127649668530798225000000 : ℚ)), ((377252145645492405374531 : ℚ) / (12935166411120886800000000 : ℚ)), ((360763382662032137054831 : ℚ) / (12935166411120886800000000 : ℚ))],
    jensenBound := ((4299014621367466073471693242796387844967514517447055909088631591957818421358501353935121859852580440620327481803220999918911966108016861829768859685859548191774408229065556572853473491275985912273437500000000000000000 : ℚ) / (200515754016004554644566602386002235914300340647065842136978388459890079792385648284650446514331157646537300830934467320579469643733799130483088969684709117560031884087461802918797782844639225216627935400249190052675203440994399 : ℚ)),
    jensenFloorQ96 := (1698634756876580766 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_simplexId_before"
  err.flush

theorem geometryRow6595_simplexId_read :
    geometryRowsJson6595.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6595.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_vertexIds_before"
  err.flush

theorem geometryRow6595_vertexIds_read :
    geometryRowsJson6595.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6595.vertexIds := by decide +kernel

noncomputable def geometryRow6595_physicalVolumeNumeratorChars : List Char := ['2', '0', '9', '8', '1', '3', '3', '8', '1', '7', '6', '0', '9', '7', '1', '7', '2', '6', '1', '3', '3', '6', '7', '0', '2', '1', '7', '6', '3', '5', '7', '5', '1', '3', '4', '4', '4', '0', '0', '6', '7']
noncomputable def geometryRow6595_physicalVolumeDenominatorChars : List Char := ['1', '0', '6', '7', '5', '2', '5', '6', '2', '9', '5', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6595_physicalVolumeText : String := String.ofList (geometryRow6595_physicalVolumeNumeratorChars ++ '/' :: geometryRow6595_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_physicalVolume_before_field"
  err.flush

theorem geometryRow6595_physicalVolume_field :
    geometryRowsJson6595.getObjVal? "physical_volume" = .ok (.str geometryRow6595_physicalVolumeText) := by rfl

theorem geometryRow6595_physicalVolume_numerator_no_slash :
    geometryRow6595_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6595_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6595_physicalVolumeNumeratorChars = some (20981338176097172613367021763575134440067 : Int) := by decide +kernel

theorem geometryRow6595_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6595_physicalVolumeDenominatorChars = some (10675256295424000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6595_physicalVolume_denominator_nonzero : (10675256295424000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6595_physicalVolume_parse :
    parseRational geometryRow6595_physicalVolumeText = .ok geometryRowsTyped6595.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6595_physicalVolumeNumeratorChars geometryRow6595_physicalVolumeDenominatorChars
    (20981338176097172613367021763575134440067 : Int) (10675256295424000000000000000000000000000000000000000000000000 : Int)
    geometryRow6595_physicalVolume_numerator_no_slash geometryRow6595_physicalVolume_numerator_parse
    geometryRow6595_physicalVolume_denominator_parse geometryRow6595_physicalVolume_denominator_nonzero

theorem geometryRow6595_physicalVolume_read :
    rationalField geometryRowsJson6595 "physical_volume" = .ok geometryRowsTyped6595.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6595 "physical_volume" geometryRow6595_physicalVolumeText
    geometryRowsTyped6595.physicalVolume geometryRow6595_physicalVolume_field geometryRow6595_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6595_meanGapNumeratorChars : List Char := ['2', '6', '8', '5', '3', '5', '2', '7']
noncomputable def geometryRow6595_meanGapDenominatorChars : List Char := ['2', '5', '3', '9', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6595_meanGapText : String := String.ofList (geometryRow6595_meanGapNumeratorChars ++ '/' :: geometryRow6595_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_meanGap_before_field"
  err.flush

theorem geometryRow6595_meanGap_field :
    geometryRowsJson6595.getObjVal? "mean_gap" = .ok (.str geometryRow6595_meanGapText) := by rfl

theorem geometryRow6595_meanGap_numerator_no_slash :
    geometryRow6595_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6595_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6595_meanGapNumeratorChars = some (26853527 : Int) := by decide +kernel

theorem geometryRow6595_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6595_meanGapDenominatorChars = some (25398000000 : Int) := by decide +kernel

theorem geometryRow6595_meanGap_denominator_nonzero : (25398000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6595_meanGap_parse :
    parseRational geometryRow6595_meanGapText = .ok geometryRowsTyped6595.meanGap :=
  original_rational_fraction_of_chars geometryRow6595_meanGapNumeratorChars geometryRow6595_meanGapDenominatorChars
    (26853527 : Int) (25398000000 : Int)
    geometryRow6595_meanGap_numerator_no_slash geometryRow6595_meanGap_numerator_parse
    geometryRow6595_meanGap_denominator_parse geometryRow6595_meanGap_denominator_nonzero

theorem geometryRow6595_meanGap_read :
    rationalField geometryRowsJson6595 "mean_gap" = .ok geometryRowsTyped6595.meanGap :=
  original_rationalField_of_string geometryRowsJson6595 "mean_gap" geometryRow6595_meanGapText
    geometryRowsTyped6595.meanGap geometryRow6595_meanGap_field geometryRow6595_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_meanGap_complete"
  err.flush

noncomputable def geometryRow6595_jensenBoundNumeratorChars : List Char := ['4', '2', '9', '9', '0', '1', '4', '6', '2', '1', '3', '6', '7', '4', '6', '6', '0', '7', '3', '4', '7', '1', '6', '9', '3', '2', '4', '2', '7', '9', '6', '3', '8', '7', '8', '4', '4', '9', '6', '7', '5', '1', '4', '5', '1', '7', '4', '4', '7', '0', '5', '5', '9', '0', '9', '0', '8', '8', '6', '3', '1', '5', '9', '1', '9', '5', '7', '8', '1', '8', '4', '2', '1', '3', '5', '8', '5', '0', '1', '3', '5', '3', '9', '3', '5', '1', '2', '1', '8', '5', '9', '8', '5', '2', '5', '8', '0', '4', '4', '0', '6', '2', '0', '3', '2', '7', '4', '8', '1', '8', '0', '3', '2', '2', '0', '9', '9', '9', '9', '1', '8', '9', '1', '1', '9', '6', '6', '1', '0', '8', '0', '1', '6', '8', '6', '1', '8', '2', '9', '7', '6', '8', '8', '5', '9', '6', '8', '5', '8', '5', '9', '5', '4', '8', '1', '9', '1', '7', '7', '4', '4', '0', '8', '2', '2', '9', '0', '6', '5', '5', '5', '6', '5', '7', '2', '8', '5', '3', '4', '7', '3', '4', '9', '1', '2', '7', '5', '9', '8', '5', '9', '1', '2', '2', '7', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6595_jensenBoundDenominatorChars : List Char := ['2', '0', '0', '5', '1', '5', '7', '5', '4', '0', '1', '6', '0', '0', '4', '5', '5', '4', '6', '4', '4', '5', '6', '6', '6', '0', '2', '3', '8', '6', '0', '0', '2', '2', '3', '5', '9', '1', '4', '3', '0', '0', '3', '4', '0', '6', '4', '7', '0', '6', '5', '8', '4', '2', '1', '3', '6', '9', '7', '8', '3', '8', '8', '4', '5', '9', '8', '9', '0', '0', '7', '9', '7', '9', '2', '3', '8', '5', '6', '4', '8', '2', '8', '4', '6', '5', '0', '4', '4', '6', '5', '1', '4', '3', '3', '1', '1', '5', '7', '6', '4', '6', '5', '3', '7', '3', '0', '0', '8', '3', '0', '9', '3', '4', '4', '6', '7', '3', '2', '0', '5', '7', '9', '4', '6', '9', '6', '4', '3', '7', '3', '3', '7', '9', '9', '1', '3', '0', '4', '8', '3', '0', '8', '8', '9', '6', '9', '6', '8', '4', '7', '0', '9', '1', '1', '7', '5', '6', '0', '0', '3', '1', '8', '8', '4', '0', '8', '7', '4', '6', '1', '8', '0', '2', '9', '1', '8', '7', '9', '7', '7', '8', '2', '8', '4', '4', '6', '3', '9', '2', '2', '5', '2', '1', '6', '6', '2', '7', '9', '3', '5', '4', '0', '0', '2', '4', '9', '1', '9', '0', '0', '5', '2', '6', '7', '5', '2', '0', '3', '4', '4', '0', '9', '9', '4', '3', '9', '9']
noncomputable def geometryRow6595_jensenBoundText : String := String.ofList (geometryRow6595_jensenBoundNumeratorChars ++ '/' :: geometryRow6595_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_jensenBound_before_field"
  err.flush

theorem geometryRow6595_jensenBound_field :
    geometryRowsJson6595.getObjVal? "jensen_bound" = .ok (.str geometryRow6595_jensenBoundText) := by rfl

theorem geometryRow6595_jensenBound_numerator_no_slash :
    geometryRow6595_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6595_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6595_jensenBoundNumeratorChars = some (4299014621367466073471693242796387844967514517447055909088631591957818421358501353935121859852580440620327481803220999918911966108016861829768859685859548191774408229065556572853473491275985912273437500000000000000000 : Int) := by decide +kernel

theorem geometryRow6595_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6595_jensenBoundDenominatorChars = some (200515754016004554644566602386002235914300340647065842136978388459890079792385648284650446514331157646537300830934467320579469643733799130483088969684709117560031884087461802918797782844639225216627935400249190052675203440994399 : Int) := by decide +kernel

theorem geometryRow6595_jensenBound_denominator_nonzero : (200515754016004554644566602386002235914300340647065842136978388459890079792385648284650446514331157646537300830934467320579469643733799130483088969684709117560031884087461802918797782844639225216627935400249190052675203440994399 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6595_jensenBound_parse :
    parseRational geometryRow6595_jensenBoundText = .ok geometryRowsTyped6595.jensenBound :=
  original_rational_fraction_of_chars geometryRow6595_jensenBoundNumeratorChars geometryRow6595_jensenBoundDenominatorChars
    (4299014621367466073471693242796387844967514517447055909088631591957818421358501353935121859852580440620327481803220999918911966108016861829768859685859548191774408229065556572853473491275985912273437500000000000000000 : Int) (200515754016004554644566602386002235914300340647065842136978388459890079792385648284650446514331157646537300830934467320579469643733799130483088969684709117560031884087461802918797782844639225216627935400249190052675203440994399 : Int)
    geometryRow6595_jensenBound_numerator_no_slash geometryRow6595_jensenBound_numerator_parse
    geometryRow6595_jensenBound_denominator_parse geometryRow6595_jensenBound_denominator_nonzero

theorem geometryRow6595_jensenBound_read :
    rationalField geometryRowsJson6595 "jensen_bound" = .ok geometryRowsTyped6595.jensenBound :=
  original_rationalField_of_string geometryRowsJson6595 "jensen_bound" geometryRow6595_jensenBoundText
    geometryRowsTyped6595.jensenBound geometryRow6595_jensenBound_field geometryRow6595_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_factorMaxima_before"
  err.flush

theorem geometryRow6595_factorMaxima_read :
    rationalArrayField geometryRowsJson6595 "factor_maxima" = .ok geometryRowsTyped6595.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_gapWeightedMeans_before"
  err.flush

theorem geometryRow6595_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6595 "gap_weighted_means" = .ok geometryRowsTyped6595.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6595_floorChars : List Char := ['1', '6', '9', '8', '6', '3', '4', '7', '5', '6', '8', '7', '6', '5', '8', '0', '7', '6', '6']
noncomputable def geometryRow6595_floorText : String := String.ofList geometryRow6595_floorChars

theorem geometryRow6595_floor_text_read :
    geometryRowsJson6595.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6595_floorText := by rfl

theorem geometryRow6595_floor_chars_parse :
    SourceJson.intChars geometryRow6595_floorChars = some (1698634756876580766 : Int) := by decide +kernel

theorem geometryRow6595_floor_parse :
    parseInteger geometryRow6595_floorText = .ok geometryRowsTyped6595.jensenFloorQ96 := by
  simp only [geometryRow6595_floorText, parseInteger, String.toList_ofList, geometryRow6595_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6595 :
    decodeGeometryRow geometryRowsJson6595 = .ok geometryRowsTyped6595 :=
  original_geometryRow_of_fields geometryRowsJson6595 geometryRowsTyped6595 geometryRow6595_floorText
    geometryRow6595_simplexId_read geometryRow6595_vertexIds_read
    geometryRow6595_physicalVolume_read geometryRow6595_meanGap_read
    geometryRow6595_factorMaxima_read geometryRow6595_gapWeightedMeans_read
    geometryRow6595_jensenBound_read geometryRow6595_floor_text_read geometryRow6595_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6595_original_decoder_complete"
  err.flush

theorem geometryRow6595_shape :
    geometryRowsTyped6595.simplexId = 6595 ∧
    geometryRowsTyped6595.vertexIds.size = 9 ∧ geometryRowsTyped6595.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6595.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6595.factorMaxima.size = 10 ∧ geometryRowsTyped6595.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6596 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped6596 : GeometryRow :=
  { simplexId := 6596,
    vertexIds := #[139, 137, 135, 117, 98, 84, 66, 56, 27],
    physicalVolume := ((193174212705095029939118570159946340506891939 : ℚ) / (16678047103778816000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((2015269 : ℚ) / (2988000000 : ℚ)),
    factorMaxima := #[((449201 : ℚ) / (8750000 : ℚ)), ((449201 : ℚ) / (8750000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((208129 : ℚ) / (2208000 : ℚ)), ((31358779 : ℚ) / (372000000 : ℚ)), ((2656247 : ℚ) / (35000000 : ℚ)), ((12421691 : ℚ) / (186000000 : ℚ)), ((156249 : ℚ) / (4375000 : ℚ)), ((156249 : ℚ) / (4375000 : ℚ))],
    gapWeightedMeans := #[((17882022594230563 : ℚ) / (469100097200000000 : ℚ)), ((18451518307353543 : ℚ) / (469100097200000000 : ℚ)), ((4423203906515459 : ℚ) / (37034218200000000 : ℚ)), ((359641610333569 : ℚ) / (3752800777600000 : ℚ)), ((307451849895583 : ℚ) / (3703421820000000 : ℚ)), ((2682606202373689 : ℚ) / (37034218200000000 : ℚ)), ((2642480443299659 : ℚ) / (37034218200000000 : ℚ)), ((1155478109887873 : ℚ) / (18517109100000000 : ℚ)), ((38429852464319047 : ℚ) / (1407300291600000000 : ℚ)), ((36635933451820147 : ℚ) / (1407300291600000000 : ℚ))],
    jensenBound := ((3123111880186364448271073955101679176353864400686109780728512152191449383110992885408081651623251079031914237229434832615660000000000000000000000 : ℚ) / (32648580508475629405277928647675257330673947523766521986969704894848857732188325301840689494929467436704388781561083057654489648026559467963602923336089687 : ℚ)),
    jensenFloorQ96 := (7578841460791824730 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_simplexId_before"
  err.flush

theorem geometryRow6596_simplexId_read :
    geometryRowsJson6596.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6596.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_vertexIds_before"
  err.flush

theorem geometryRow6596_vertexIds_read :
    geometryRowsJson6596.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6596.vertexIds := by decide +kernel

noncomputable def geometryRow6596_physicalVolumeNumeratorChars : List Char := ['1', '9', '3', '1', '7', '4', '2', '1', '2', '7', '0', '5', '0', '9', '5', '0', '2', '9', '9', '3', '9', '1', '1', '8', '5', '7', '0', '1', '5', '9', '9', '4', '6', '3', '4', '0', '5', '0', '6', '8', '9', '1', '9', '3', '9']
noncomputable def geometryRow6596_physicalVolumeDenominatorChars : List Char := ['1', '6', '6', '7', '8', '0', '4', '7', '1', '0', '3', '7', '7', '8', '8', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6596_physicalVolumeText : String := String.ofList (geometryRow6596_physicalVolumeNumeratorChars ++ '/' :: geometryRow6596_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_physicalVolume_before_field"
  err.flush

theorem geometryRow6596_physicalVolume_field :
    geometryRowsJson6596.getObjVal? "physical_volume" = .ok (.str geometryRow6596_physicalVolumeText) := by rfl

theorem geometryRow6596_physicalVolume_numerator_no_slash :
    geometryRow6596_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6596_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6596_physicalVolumeNumeratorChars = some (193174212705095029939118570159946340506891939 : Int) := by decide +kernel

theorem geometryRow6596_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6596_physicalVolumeDenominatorChars = some (16678047103778816000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6596_physicalVolume_denominator_nonzero : (16678047103778816000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6596_physicalVolume_parse :
    parseRational geometryRow6596_physicalVolumeText = .ok geometryRowsTyped6596.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6596_physicalVolumeNumeratorChars geometryRow6596_physicalVolumeDenominatorChars
    (193174212705095029939118570159946340506891939 : Int) (16678047103778816000000000000000000000000000000000000000000000000 : Int)
    geometryRow6596_physicalVolume_numerator_no_slash geometryRow6596_physicalVolume_numerator_parse
    geometryRow6596_physicalVolume_denominator_parse geometryRow6596_physicalVolume_denominator_nonzero

theorem geometryRow6596_physicalVolume_read :
    rationalField geometryRowsJson6596 "physical_volume" = .ok geometryRowsTyped6596.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6596 "physical_volume" geometryRow6596_physicalVolumeText
    geometryRowsTyped6596.physicalVolume geometryRow6596_physicalVolume_field geometryRow6596_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6596_meanGapNumeratorChars : List Char := ['2', '0', '1', '5', '2', '6', '9']
noncomputable def geometryRow6596_meanGapDenominatorChars : List Char := ['2', '9', '8', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6596_meanGapText : String := String.ofList (geometryRow6596_meanGapNumeratorChars ++ '/' :: geometryRow6596_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_meanGap_before_field"
  err.flush

theorem geometryRow6596_meanGap_field :
    geometryRowsJson6596.getObjVal? "mean_gap" = .ok (.str geometryRow6596_meanGapText) := by rfl

theorem geometryRow6596_meanGap_numerator_no_slash :
    geometryRow6596_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6596_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6596_meanGapNumeratorChars = some (2015269 : Int) := by decide +kernel

theorem geometryRow6596_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6596_meanGapDenominatorChars = some (2988000000 : Int) := by decide +kernel

theorem geometryRow6596_meanGap_denominator_nonzero : (2988000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6596_meanGap_parse :
    parseRational geometryRow6596_meanGapText = .ok geometryRowsTyped6596.meanGap :=
  original_rational_fraction_of_chars geometryRow6596_meanGapNumeratorChars geometryRow6596_meanGapDenominatorChars
    (2015269 : Int) (2988000000 : Int)
    geometryRow6596_meanGap_numerator_no_slash geometryRow6596_meanGap_numerator_parse
    geometryRow6596_meanGap_denominator_parse geometryRow6596_meanGap_denominator_nonzero

theorem geometryRow6596_meanGap_read :
    rationalField geometryRowsJson6596 "mean_gap" = .ok geometryRowsTyped6596.meanGap :=
  original_rationalField_of_string geometryRowsJson6596 "mean_gap" geometryRow6596_meanGapText
    geometryRowsTyped6596.meanGap geometryRow6596_meanGap_field geometryRow6596_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_meanGap_complete"
  err.flush

noncomputable def geometryRow6596_jensenBoundNumeratorChars : List Char := ['3', '1', '2', '3', '1', '1', '1', '8', '8', '0', '1', '8', '6', '3', '6', '4', '4', '4', '8', '2', '7', '1', '0', '7', '3', '9', '5', '5', '1', '0', '1', '6', '7', '9', '1', '7', '6', '3', '5', '3', '8', '6', '4', '4', '0', '0', '6', '8', '6', '1', '0', '9', '7', '8', '0', '7', '2', '8', '5', '1', '2', '1', '5', '2', '1', '9', '1', '4', '4', '9', '3', '8', '3', '1', '1', '0', '9', '9', '2', '8', '8', '5', '4', '0', '8', '0', '8', '1', '6', '5', '1', '6', '2', '3', '2', '5', '1', '0', '7', '9', '0', '3', '1', '9', '1', '4', '2', '3', '7', '2', '2', '9', '4', '3', '4', '8', '3', '2', '6', '1', '5', '6', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6596_jensenBoundDenominatorChars : List Char := ['3', '2', '6', '4', '8', '5', '8', '0', '5', '0', '8', '4', '7', '5', '6', '2', '9', '4', '0', '5', '2', '7', '7', '9', '2', '8', '6', '4', '7', '6', '7', '5', '2', '5', '7', '3', '3', '0', '6', '7', '3', '9', '4', '7', '5', '2', '3', '7', '6', '6', '5', '2', '1', '9', '8', '6', '9', '6', '9', '7', '0', '4', '8', '9', '4', '8', '4', '8', '8', '5', '7', '7', '3', '2', '1', '8', '8', '3', '2', '5', '3', '0', '1', '8', '4', '0', '6', '8', '9', '4', '9', '4', '9', '2', '9', '4', '6', '7', '4', '3', '6', '7', '0', '4', '3', '8', '8', '7', '8', '1', '5', '6', '1', '0', '8', '3', '0', '5', '7', '6', '5', '4', '4', '8', '9', '6', '4', '8', '0', '2', '6', '5', '5', '9', '4', '6', '7', '9', '6', '3', '6', '0', '2', '9', '2', '3', '3', '3', '6', '0', '8', '9', '6', '8', '7']
noncomputable def geometryRow6596_jensenBoundText : String := String.ofList (geometryRow6596_jensenBoundNumeratorChars ++ '/' :: geometryRow6596_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_jensenBound_before_field"
  err.flush

theorem geometryRow6596_jensenBound_field :
    geometryRowsJson6596.getObjVal? "jensen_bound" = .ok (.str geometryRow6596_jensenBoundText) := by rfl

theorem geometryRow6596_jensenBound_numerator_no_slash :
    geometryRow6596_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6596_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6596_jensenBoundNumeratorChars = some (3123111880186364448271073955101679176353864400686109780728512152191449383110992885408081651623251079031914237229434832615660000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6596_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6596_jensenBoundDenominatorChars = some (32648580508475629405277928647675257330673947523766521986969704894848857732188325301840689494929467436704388781561083057654489648026559467963602923336089687 : Int) := by decide +kernel

theorem geometryRow6596_jensenBound_denominator_nonzero : (32648580508475629405277928647675257330673947523766521986969704894848857732188325301840689494929467436704388781561083057654489648026559467963602923336089687 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6596_jensenBound_parse :
    parseRational geometryRow6596_jensenBoundText = .ok geometryRowsTyped6596.jensenBound :=
  original_rational_fraction_of_chars geometryRow6596_jensenBoundNumeratorChars geometryRow6596_jensenBoundDenominatorChars
    (3123111880186364448271073955101679176353864400686109780728512152191449383110992885408081651623251079031914237229434832615660000000000000000000000 : Int) (32648580508475629405277928647675257330673947523766521986969704894848857732188325301840689494929467436704388781561083057654489648026559467963602923336089687 : Int)
    geometryRow6596_jensenBound_numerator_no_slash geometryRow6596_jensenBound_numerator_parse
    geometryRow6596_jensenBound_denominator_parse geometryRow6596_jensenBound_denominator_nonzero

theorem geometryRow6596_jensenBound_read :
    rationalField geometryRowsJson6596 "jensen_bound" = .ok geometryRowsTyped6596.jensenBound :=
  original_rationalField_of_string geometryRowsJson6596 "jensen_bound" geometryRow6596_jensenBoundText
    geometryRowsTyped6596.jensenBound geometryRow6596_jensenBound_field geometryRow6596_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_factorMaxima_before"
  err.flush

theorem geometryRow6596_factorMaxima_read :
    rationalArrayField geometryRowsJson6596 "factor_maxima" = .ok geometryRowsTyped6596.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_gapWeightedMeans_before"
  err.flush

theorem geometryRow6596_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6596 "gap_weighted_means" = .ok geometryRowsTyped6596.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6596_floorChars : List Char := ['7', '5', '7', '8', '8', '4', '1', '4', '6', '0', '7', '9', '1', '8', '2', '4', '7', '3', '0']
noncomputable def geometryRow6596_floorText : String := String.ofList geometryRow6596_floorChars

theorem geometryRow6596_floor_text_read :
    geometryRowsJson6596.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6596_floorText := by rfl

theorem geometryRow6596_floor_chars_parse :
    SourceJson.intChars geometryRow6596_floorChars = some (7578841460791824730 : Int) := by decide +kernel

theorem geometryRow6596_floor_parse :
    parseInteger geometryRow6596_floorText = .ok geometryRowsTyped6596.jensenFloorQ96 := by
  simp only [geometryRow6596_floorText, parseInteger, String.toList_ofList, geometryRow6596_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6596 :
    decodeGeometryRow geometryRowsJson6596 = .ok geometryRowsTyped6596 :=
  original_geometryRow_of_fields geometryRowsJson6596 geometryRowsTyped6596 geometryRow6596_floorText
    geometryRow6596_simplexId_read geometryRow6596_vertexIds_read
    geometryRow6596_physicalVolume_read geometryRow6596_meanGap_read
    geometryRow6596_factorMaxima_read geometryRow6596_gapWeightedMeans_read
    geometryRow6596_jensenBound_read geometryRow6596_floor_text_read geometryRow6596_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6596_original_decoder_complete"
  err.flush

theorem geometryRow6596_shape :
    geometryRowsTyped6596.simplexId = 6596 ∧
    geometryRowsTyped6596.vertexIds.size = 9 ∧ geometryRowsTyped6596.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6596.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6596.factorMaxima.size = 10 ∧ geometryRowsTyped6596.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6597 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped6597 : GeometryRow :=
  { simplexId := 6597,
    vertexIds := #[139, 137, 135, 117, 98, 94, 84, 83, 65],
    physicalVolume := ((51843775515208011244001187021804194061783 : ℚ) / (41414849724416000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((234307 : ℚ) / (612000000 : ℚ)),
    factorMaxima := #[((109369 : ℚ) / (2000000 : ℚ)), ((109369 : ℚ) / (2000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((208129 : ℚ) / (2208000 : ℚ)), ((571867 : ℚ) / (7200000 : ℚ)), ((2656247 : ℚ) / (35000000 : ℚ)), ((12421691 : ℚ) / (186000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ))],
    gapWeightedMeans := #[((28396485243323 : ℚ) / (644837200000000 : ℚ)), ((28840867213383 : ℚ) / (644837200000000 : ℚ)), ((18578097532187 : ℚ) / (152724600000000 : ℚ)), ((109297300461091 : ℚ) / (1160706960000000 : ℚ)), ((306343166977 : ℚ) / (3818115000000 : ℚ)), ((10989003100807 : ℚ) / (152724600000000 : ℚ)), ((32768206842131 : ℚ) / (458173800000000 : ℚ)), ((6214160036461 : ℚ) / (114543450000000 : ℚ)), ((24984227101433 : ℚ) / (829076400000000 : ℚ)), ((23927383778333 : ℚ) / (829076400000000 : ℚ))],
    jensenBound := ((2483245081591165872975158857756450443168771561673694827571236003965173881520830848579035279465179687500000000000000000 : ℚ) / (569314395599454862314716544486405737530074367302029776556483519900327831678008483149827546121210598101223880234245670862082681589 : ℚ)),
    jensenFloorQ96 := (345578728392935937 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_simplexId_before"
  err.flush

theorem geometryRow6597_simplexId_read :
    geometryRowsJson6597.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6597.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_vertexIds_before"
  err.flush

theorem geometryRow6597_vertexIds_read :
    geometryRowsJson6597.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6597.vertexIds := by decide +kernel

noncomputable def geometryRow6597_physicalVolumeNumeratorChars : List Char := ['5', '1', '8', '4', '3', '7', '7', '5', '5', '1', '5', '2', '0', '8', '0', '1', '1', '2', '4', '4', '0', '0', '1', '1', '8', '7', '0', '2', '1', '8', '0', '4', '1', '9', '4', '0', '6', '1', '7', '8', '3']
noncomputable def geometryRow6597_physicalVolumeDenominatorChars : List Char := ['4', '1', '4', '1', '4', '8', '4', '9', '7', '2', '4', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6597_physicalVolumeText : String := String.ofList (geometryRow6597_physicalVolumeNumeratorChars ++ '/' :: geometryRow6597_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_physicalVolume_before_field"
  err.flush

theorem geometryRow6597_physicalVolume_field :
    geometryRowsJson6597.getObjVal? "physical_volume" = .ok (.str geometryRow6597_physicalVolumeText) := by rfl

theorem geometryRow6597_physicalVolume_numerator_no_slash :
    geometryRow6597_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6597_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6597_physicalVolumeNumeratorChars = some (51843775515208011244001187021804194061783 : Int) := by decide +kernel

theorem geometryRow6597_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6597_physicalVolumeDenominatorChars = some (41414849724416000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6597_physicalVolume_denominator_nonzero : (41414849724416000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6597_physicalVolume_parse :
    parseRational geometryRow6597_physicalVolumeText = .ok geometryRowsTyped6597.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6597_physicalVolumeNumeratorChars geometryRow6597_physicalVolumeDenominatorChars
    (51843775515208011244001187021804194061783 : Int) (41414849724416000000000000000000000000000000000000000000000000 : Int)
    geometryRow6597_physicalVolume_numerator_no_slash geometryRow6597_physicalVolume_numerator_parse
    geometryRow6597_physicalVolume_denominator_parse geometryRow6597_physicalVolume_denominator_nonzero

theorem geometryRow6597_physicalVolume_read :
    rationalField geometryRowsJson6597 "physical_volume" = .ok geometryRowsTyped6597.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6597 "physical_volume" geometryRow6597_physicalVolumeText
    geometryRowsTyped6597.physicalVolume geometryRow6597_physicalVolume_field geometryRow6597_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6597_meanGapNumeratorChars : List Char := ['2', '3', '4', '3', '0', '7']
noncomputable def geometryRow6597_meanGapDenominatorChars : List Char := ['6', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6597_meanGapText : String := String.ofList (geometryRow6597_meanGapNumeratorChars ++ '/' :: geometryRow6597_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_meanGap_before_field"
  err.flush

theorem geometryRow6597_meanGap_field :
    geometryRowsJson6597.getObjVal? "mean_gap" = .ok (.str geometryRow6597_meanGapText) := by rfl

theorem geometryRow6597_meanGap_numerator_no_slash :
    geometryRow6597_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6597_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6597_meanGapNumeratorChars = some (234307 : Int) := by decide +kernel

theorem geometryRow6597_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6597_meanGapDenominatorChars = some (612000000 : Int) := by decide +kernel

theorem geometryRow6597_meanGap_denominator_nonzero : (612000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6597_meanGap_parse :
    parseRational geometryRow6597_meanGapText = .ok geometryRowsTyped6597.meanGap :=
  original_rational_fraction_of_chars geometryRow6597_meanGapNumeratorChars geometryRow6597_meanGapDenominatorChars
    (234307 : Int) (612000000 : Int)
    geometryRow6597_meanGap_numerator_no_slash geometryRow6597_meanGap_numerator_parse
    geometryRow6597_meanGap_denominator_parse geometryRow6597_meanGap_denominator_nonzero

theorem geometryRow6597_meanGap_read :
    rationalField geometryRowsJson6597 "mean_gap" = .ok geometryRowsTyped6597.meanGap :=
  original_rationalField_of_string geometryRowsJson6597 "mean_gap" geometryRow6597_meanGapText
    geometryRowsTyped6597.meanGap geometryRow6597_meanGap_field geometryRow6597_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_meanGap_complete"
  err.flush

noncomputable def geometryRow6597_jensenBoundNumeratorChars : List Char := ['2', '4', '8', '3', '2', '4', '5', '0', '8', '1', '5', '9', '1', '1', '6', '5', '8', '7', '2', '9', '7', '5', '1', '5', '8', '8', '5', '7', '7', '5', '6', '4', '5', '0', '4', '4', '3', '1', '6', '8', '7', '7', '1', '5', '6', '1', '6', '7', '3', '6', '9', '4', '8', '2', '7', '5', '7', '1', '2', '3', '6', '0', '0', '3', '9', '6', '5', '1', '7', '3', '8', '8', '1', '5', '2', '0', '8', '3', '0', '8', '4', '8', '5', '7', '9', '0', '3', '5', '2', '7', '9', '4', '6', '5', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6597_jensenBoundDenominatorChars : List Char := ['5', '6', '9', '3', '1', '4', '3', '9', '5', '5', '9', '9', '4', '5', '4', '8', '6', '2', '3', '1', '4', '7', '1', '6', '5', '4', '4', '4', '8', '6', '4', '0', '5', '7', '3', '7', '5', '3', '0', '0', '7', '4', '3', '6', '7', '3', '0', '2', '0', '2', '9', '7', '7', '6', '5', '5', '6', '4', '8', '3', '5', '1', '9', '9', '0', '0', '3', '2', '7', '8', '3', '1', '6', '7', '8', '0', '0', '8', '4', '8', '3', '1', '4', '9', '8', '2', '7', '5', '4', '6', '1', '2', '1', '2', '1', '0', '5', '9', '8', '1', '0', '1', '2', '2', '3', '8', '8', '0', '2', '3', '4', '2', '4', '5', '6', '7', '0', '8', '6', '2', '0', '8', '2', '6', '8', '1', '5', '8', '9']
noncomputable def geometryRow6597_jensenBoundText : String := String.ofList (geometryRow6597_jensenBoundNumeratorChars ++ '/' :: geometryRow6597_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_jensenBound_before_field"
  err.flush

theorem geometryRow6597_jensenBound_field :
    geometryRowsJson6597.getObjVal? "jensen_bound" = .ok (.str geometryRow6597_jensenBoundText) := by rfl

theorem geometryRow6597_jensenBound_numerator_no_slash :
    geometryRow6597_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6597_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6597_jensenBoundNumeratorChars = some (2483245081591165872975158857756450443168771561673694827571236003965173881520830848579035279465179687500000000000000000 : Int) := by decide +kernel

theorem geometryRow6597_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6597_jensenBoundDenominatorChars = some (569314395599454862314716544486405737530074367302029776556483519900327831678008483149827546121210598101223880234245670862082681589 : Int) := by decide +kernel

theorem geometryRow6597_jensenBound_denominator_nonzero : (569314395599454862314716544486405737530074367302029776556483519900327831678008483149827546121210598101223880234245670862082681589 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6597_jensenBound_parse :
    parseRational geometryRow6597_jensenBoundText = .ok geometryRowsTyped6597.jensenBound :=
  original_rational_fraction_of_chars geometryRow6597_jensenBoundNumeratorChars geometryRow6597_jensenBoundDenominatorChars
    (2483245081591165872975158857756450443168771561673694827571236003965173881520830848579035279465179687500000000000000000 : Int) (569314395599454862314716544486405737530074367302029776556483519900327831678008483149827546121210598101223880234245670862082681589 : Int)
    geometryRow6597_jensenBound_numerator_no_slash geometryRow6597_jensenBound_numerator_parse
    geometryRow6597_jensenBound_denominator_parse geometryRow6597_jensenBound_denominator_nonzero

theorem geometryRow6597_jensenBound_read :
    rationalField geometryRowsJson6597 "jensen_bound" = .ok geometryRowsTyped6597.jensenBound :=
  original_rationalField_of_string geometryRowsJson6597 "jensen_bound" geometryRow6597_jensenBoundText
    geometryRowsTyped6597.jensenBound geometryRow6597_jensenBound_field geometryRow6597_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_factorMaxima_before"
  err.flush

theorem geometryRow6597_factorMaxima_read :
    rationalArrayField geometryRowsJson6597 "factor_maxima" = .ok geometryRowsTyped6597.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_gapWeightedMeans_before"
  err.flush

theorem geometryRow6597_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6597 "gap_weighted_means" = .ok geometryRowsTyped6597.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6597_floorChars : List Char := ['3', '4', '5', '5', '7', '8', '7', '2', '8', '3', '9', '2', '9', '3', '5', '9', '3', '7']
noncomputable def geometryRow6597_floorText : String := String.ofList geometryRow6597_floorChars

theorem geometryRow6597_floor_text_read :
    geometryRowsJson6597.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6597_floorText := by rfl

theorem geometryRow6597_floor_chars_parse :
    SourceJson.intChars geometryRow6597_floorChars = some (345578728392935937 : Int) := by decide +kernel

theorem geometryRow6597_floor_parse :
    parseInteger geometryRow6597_floorText = .ok geometryRowsTyped6597.jensenFloorQ96 := by
  simp only [geometryRow6597_floorText, parseInteger, String.toList_ofList, geometryRow6597_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6597 :
    decodeGeometryRow geometryRowsJson6597 = .ok geometryRowsTyped6597 :=
  original_geometryRow_of_fields geometryRowsJson6597 geometryRowsTyped6597 geometryRow6597_floorText
    geometryRow6597_simplexId_read geometryRow6597_vertexIds_read
    geometryRow6597_physicalVolume_read geometryRow6597_meanGap_read
    geometryRow6597_factorMaxima_read geometryRow6597_gapWeightedMeans_read
    geometryRow6597_jensenBound_read geometryRow6597_floor_text_read geometryRow6597_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6597_original_decoder_complete"
  err.flush

theorem geometryRow6597_shape :
    geometryRowsTyped6597.simplexId = 6597 ∧
    geometryRowsTyped6597.vertexIds.size = 9 ∧ geometryRowsTyped6597.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6597.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6597.factorMaxima.size = 10 ∧ geometryRowsTyped6597.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6598 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped6598 : GeometryRow :=
  { simplexId := 6598,
    vertexIds := #[139, 137, 135, 117, 111, 110, 106, 97, 55],
    physicalVolume := ((2481832070012360042050703396851909 : ℚ) / (2901382712524800000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((23740829 : ℚ) / (25461000000 : ℚ)),
    factorMaxima := #[((1171879 : ℚ) / (24000000 : ℚ)), ((1171879 : ℚ) / (24000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((388979 : ℚ) / (4000000 : ℚ)), ((296871 : ℚ) / (4000000 : ℚ)), ((296871 : ℚ) / (4000000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((11 : ℚ) / (384 : ℚ)), ((11 : ℚ) / (384 : ℚ))],
    gapWeightedMeans := #[((3294874709130564949 : ℚ) / (102087463966320000000 : ℚ)), ((683529061773570749 : ℚ) / (20417492793264000000 : ℚ)), ((110677385831308649 : ℚ) / (895504069880000000 : ℚ)), ((488884779975877943 : ℚ) / (4861307807920000000 : ℚ)), ((241047321368055329 : ℚ) / (2686512209640000000 : ℚ)), ((61995312447806733 : ℚ) / (895504069880000000 : ℚ)), ((5803614104048767 : ℚ) / (83953506551250000 : ℚ)), ((10701812039616917 : ℚ) / (179100813976000000 : ℚ)), ((181768019190474413 : ℚ) / (6805830931088000000 : ℚ)), ((173092465311883961 : ℚ) / (6805830931088000000 : ℚ))],
    jensenBound := ((8056758406747719524403117101033107781506527669488580935787260546313120269233396422452550851988921448187957532083342208117946673978183434595840000000000000000 : ℚ) / (591065885036481268454108430994058265338292358088922206857327451477445863233860992967922628340793740074866105861873749291914754769321641607911601753010857120680283050393753 : ℚ)),
    jensenFloorQ96 := (1079950950558710 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_simplexId_before"
  err.flush

theorem geometryRow6598_simplexId_read :
    geometryRowsJson6598.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6598.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_vertexIds_before"
  err.flush

theorem geometryRow6598_vertexIds_read :
    geometryRowsJson6598.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6598.vertexIds := by decide +kernel

noncomputable def geometryRow6598_physicalVolumeNumeratorChars : List Char := ['2', '4', '8', '1', '8', '3', '2', '0', '7', '0', '0', '1', '2', '3', '6', '0', '0', '4', '2', '0', '5', '0', '7', '0', '3', '3', '9', '6', '8', '5', '1', '9', '0', '9']
noncomputable def geometryRow6598_physicalVolumeDenominatorChars : List Char := ['2', '9', '0', '1', '3', '8', '2', '7', '1', '2', '5', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6598_physicalVolumeText : String := String.ofList (geometryRow6598_physicalVolumeNumeratorChars ++ '/' :: geometryRow6598_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_physicalVolume_before_field"
  err.flush

theorem geometryRow6598_physicalVolume_field :
    geometryRowsJson6598.getObjVal? "physical_volume" = .ok (.str geometryRow6598_physicalVolumeText) := by rfl

theorem geometryRow6598_physicalVolume_numerator_no_slash :
    geometryRow6598_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6598_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6598_physicalVolumeNumeratorChars = some (2481832070012360042050703396851909 : Int) := by decide +kernel

theorem geometryRow6598_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6598_physicalVolumeDenominatorChars = some (2901382712524800000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6598_physicalVolume_denominator_nonzero : (2901382712524800000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6598_physicalVolume_parse :
    parseRational geometryRow6598_physicalVolumeText = .ok geometryRowsTyped6598.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6598_physicalVolumeNumeratorChars geometryRow6598_physicalVolumeDenominatorChars
    (2481832070012360042050703396851909 : Int) (2901382712524800000000000000000000000000000000000000000000 : Int)
    geometryRow6598_physicalVolume_numerator_no_slash geometryRow6598_physicalVolume_numerator_parse
    geometryRow6598_physicalVolume_denominator_parse geometryRow6598_physicalVolume_denominator_nonzero

theorem geometryRow6598_physicalVolume_read :
    rationalField geometryRowsJson6598 "physical_volume" = .ok geometryRowsTyped6598.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6598 "physical_volume" geometryRow6598_physicalVolumeText
    geometryRowsTyped6598.physicalVolume geometryRow6598_physicalVolume_field geometryRow6598_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6598_meanGapNumeratorChars : List Char := ['2', '3', '7', '4', '0', '8', '2', '9']
noncomputable def geometryRow6598_meanGapDenominatorChars : List Char := ['2', '5', '4', '6', '1', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6598_meanGapText : String := String.ofList (geometryRow6598_meanGapNumeratorChars ++ '/' :: geometryRow6598_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_meanGap_before_field"
  err.flush

theorem geometryRow6598_meanGap_field :
    geometryRowsJson6598.getObjVal? "mean_gap" = .ok (.str geometryRow6598_meanGapText) := by rfl

theorem geometryRow6598_meanGap_numerator_no_slash :
    geometryRow6598_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6598_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6598_meanGapNumeratorChars = some (23740829 : Int) := by decide +kernel

theorem geometryRow6598_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6598_meanGapDenominatorChars = some (25461000000 : Int) := by decide +kernel

theorem geometryRow6598_meanGap_denominator_nonzero : (25461000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6598_meanGap_parse :
    parseRational geometryRow6598_meanGapText = .ok geometryRowsTyped6598.meanGap :=
  original_rational_fraction_of_chars geometryRow6598_meanGapNumeratorChars geometryRow6598_meanGapDenominatorChars
    (23740829 : Int) (25461000000 : Int)
    geometryRow6598_meanGap_numerator_no_slash geometryRow6598_meanGap_numerator_parse
    geometryRow6598_meanGap_denominator_parse geometryRow6598_meanGap_denominator_nonzero

theorem geometryRow6598_meanGap_read :
    rationalField geometryRowsJson6598 "mean_gap" = .ok geometryRowsTyped6598.meanGap :=
  original_rationalField_of_string geometryRowsJson6598 "mean_gap" geometryRow6598_meanGapText
    geometryRowsTyped6598.meanGap geometryRow6598_meanGap_field geometryRow6598_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_meanGap_complete"
  err.flush

noncomputable def geometryRow6598_jensenBoundNumeratorChars : List Char := ['8', '0', '5', '6', '7', '5', '8', '4', '0', '6', '7', '4', '7', '7', '1', '9', '5', '2', '4', '4', '0', '3', '1', '1', '7', '1', '0', '1', '0', '3', '3', '1', '0', '7', '7', '8', '1', '5', '0', '6', '5', '2', '7', '6', '6', '9', '4', '8', '8', '5', '8', '0', '9', '3', '5', '7', '8', '7', '2', '6', '0', '5', '4', '6', '3', '1', '3', '1', '2', '0', '2', '6', '9', '2', '3', '3', '3', '9', '6', '4', '2', '2', '4', '5', '2', '5', '5', '0', '8', '5', '1', '9', '8', '8', '9', '2', '1', '4', '4', '8', '1', '8', '7', '9', '5', '7', '5', '3', '2', '0', '8', '3', '3', '4', '2', '2', '0', '8', '1', '1', '7', '9', '4', '6', '6', '7', '3', '9', '7', '8', '1', '8', '3', '4', '3', '4', '5', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6598_jensenBoundDenominatorChars : List Char := ['5', '9', '1', '0', '6', '5', '8', '8', '5', '0', '3', '6', '4', '8', '1', '2', '6', '8', '4', '5', '4', '1', '0', '8', '4', '3', '0', '9', '9', '4', '0', '5', '8', '2', '6', '5', '3', '3', '8', '2', '9', '2', '3', '5', '8', '0', '8', '8', '9', '2', '2', '2', '0', '6', '8', '5', '7', '3', '2', '7', '4', '5', '1', '4', '7', '7', '4', '4', '5', '8', '6', '3', '2', '3', '3', '8', '6', '0', '9', '9', '2', '9', '6', '7', '9', '2', '2', '6', '2', '8', '3', '4', '0', '7', '9', '3', '7', '4', '0', '0', '7', '4', '8', '6', '6', '1', '0', '5', '8', '6', '1', '8', '7', '3', '7', '4', '9', '2', '9', '1', '9', '1', '4', '7', '5', '4', '7', '6', '9', '3', '2', '1', '6', '4', '1', '6', '0', '7', '9', '1', '1', '6', '0', '1', '7', '5', '3', '0', '1', '0', '8', '5', '7', '1', '2', '0', '6', '8', '0', '2', '8', '3', '0', '5', '0', '3', '9', '3', '7', '5', '3']
noncomputable def geometryRow6598_jensenBoundText : String := String.ofList (geometryRow6598_jensenBoundNumeratorChars ++ '/' :: geometryRow6598_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_jensenBound_before_field"
  err.flush

theorem geometryRow6598_jensenBound_field :
    geometryRowsJson6598.getObjVal? "jensen_bound" = .ok (.str geometryRow6598_jensenBoundText) := by rfl

theorem geometryRow6598_jensenBound_numerator_no_slash :
    geometryRow6598_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6598_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6598_jensenBoundNumeratorChars = some (8056758406747719524403117101033107781506527669488580935787260546313120269233396422452550851988921448187957532083342208117946673978183434595840000000000000000 : Int) := by decide +kernel

theorem geometryRow6598_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6598_jensenBoundDenominatorChars = some (591065885036481268454108430994058265338292358088922206857327451477445863233860992967922628340793740074866105861873749291914754769321641607911601753010857120680283050393753 : Int) := by decide +kernel

theorem geometryRow6598_jensenBound_denominator_nonzero : (591065885036481268454108430994058265338292358088922206857327451477445863233860992967922628340793740074866105861873749291914754769321641607911601753010857120680283050393753 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6598_jensenBound_parse :
    parseRational geometryRow6598_jensenBoundText = .ok geometryRowsTyped6598.jensenBound :=
  original_rational_fraction_of_chars geometryRow6598_jensenBoundNumeratorChars geometryRow6598_jensenBoundDenominatorChars
    (8056758406747719524403117101033107781506527669488580935787260546313120269233396422452550851988921448187957532083342208117946673978183434595840000000000000000 : Int) (591065885036481268454108430994058265338292358088922206857327451477445863233860992967922628340793740074866105861873749291914754769321641607911601753010857120680283050393753 : Int)
    geometryRow6598_jensenBound_numerator_no_slash geometryRow6598_jensenBound_numerator_parse
    geometryRow6598_jensenBound_denominator_parse geometryRow6598_jensenBound_denominator_nonzero

theorem geometryRow6598_jensenBound_read :
    rationalField geometryRowsJson6598 "jensen_bound" = .ok geometryRowsTyped6598.jensenBound :=
  original_rationalField_of_string geometryRowsJson6598 "jensen_bound" geometryRow6598_jensenBoundText
    geometryRowsTyped6598.jensenBound geometryRow6598_jensenBound_field geometryRow6598_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_factorMaxima_before"
  err.flush

theorem geometryRow6598_factorMaxima_read :
    rationalArrayField geometryRowsJson6598 "factor_maxima" = .ok geometryRowsTyped6598.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_gapWeightedMeans_before"
  err.flush

theorem geometryRow6598_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6598 "gap_weighted_means" = .ok geometryRowsTyped6598.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6598_floorChars : List Char := ['1', '0', '7', '9', '9', '5', '0', '9', '5', '0', '5', '5', '8', '7', '1', '0']
noncomputable def geometryRow6598_floorText : String := String.ofList geometryRow6598_floorChars

theorem geometryRow6598_floor_text_read :
    geometryRowsJson6598.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6598_floorText := by rfl

theorem geometryRow6598_floor_chars_parse :
    SourceJson.intChars geometryRow6598_floorChars = some (1079950950558710 : Int) := by decide +kernel

theorem geometryRow6598_floor_parse :
    parseInteger geometryRow6598_floorText = .ok geometryRowsTyped6598.jensenFloorQ96 := by
  simp only [geometryRow6598_floorText, parseInteger, String.toList_ofList, geometryRow6598_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6598 :
    decodeGeometryRow geometryRowsJson6598 = .ok geometryRowsTyped6598 :=
  original_geometryRow_of_fields geometryRowsJson6598 geometryRowsTyped6598 geometryRow6598_floorText
    geometryRow6598_simplexId_read geometryRow6598_vertexIds_read
    geometryRow6598_physicalVolume_read geometryRow6598_meanGap_read
    geometryRow6598_factorMaxima_read geometryRow6598_gapWeightedMeans_read
    geometryRow6598_jensenBound_read geometryRow6598_floor_text_read geometryRow6598_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6598_original_decoder_complete"
  err.flush

theorem geometryRow6598_shape :
    geometryRowsTyped6598.simplexId = 6598 ∧
    geometryRowsTyped6598.vertexIds.size = 9 ∧ geometryRowsTyped6598.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6598.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6598.factorMaxima.size = 10 ∧ geometryRowsTyped6598.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson6599 : SourceJson :=
  (SimplicesBlock824.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped6599 : GeometryRow :=
  { simplexId := 6599,
    vertexIds := #[139, 43, 42, 38, 36, 31, 30, 26, 14],
    physicalVolume := ((3610207271116344255866777613239426485296734473 : ℚ) / (7138091690528688046080000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((327401 : ℚ) / (6840000000 : ℚ)),
    factorMaxima := #[((1453027 : ℚ) / (23000000 : ℚ)), ((1453027 : ℚ) / (23000000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((33421959 : ℚ) / (380000000 : ℚ)), ((20952881 : ℚ) / (240000000 : ℚ)), ((328121 : ℚ) / (4500000 : ℚ)), ((1171879 : ℚ) / (18000000 : ℚ)), ((328121 : ℚ) / (9000000 : ℚ)), ((28117 : ℚ) / (1200000 : ℚ))],
    gapWeightedMeans := #[((2889097305691 : ℚ) / (48454560000000 : ℚ)), ((14466360306611 : ℚ) / (242272800000000 : ℚ)), ((332349706621 : ℚ) / (3009600000000 : ℚ)), ((43801637215411 : ℚ) / (484545600000000 : ℚ)), ((41783043421117 : ℚ) / (484545600000000 : ℚ)), ((1171819817441 : ℚ) / (13844160000000 : ℚ)), ((434297792347 : ℚ) / (6056820000000 : ℚ)), ((52644308403 : ℚ) / (1345960000000 : ℚ)), ((71038516463 : ℚ) / (2018940000000 : ℚ)), ((4895564877197 : ℚ) / (242272800000000 : ℚ))],
    jensenBound := ((2111560415779176333347018233246142236237243941841832007661411082553736057467150604081920000000000000000 : ℚ) / (11279359641982648496829610341538591577985579851716223316367504370899826167037144961260552886024889705408464161532393553117 : ℚ)),
    jensenFloorQ96 := (14831963612 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_simplexId_before"
  err.flush

theorem geometryRow6599_simplexId_read :
    geometryRowsJson6599.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped6599.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_vertexIds_before"
  err.flush

theorem geometryRow6599_vertexIds_read :
    geometryRowsJson6599.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped6599.vertexIds := by decide +kernel

noncomputable def geometryRow6599_physicalVolumeNumeratorChars : List Char := ['3', '6', '1', '0', '2', '0', '7', '2', '7', '1', '1', '1', '6', '3', '4', '4', '2', '5', '5', '8', '6', '6', '7', '7', '7', '6', '1', '3', '2', '3', '9', '4', '2', '6', '4', '8', '5', '2', '9', '6', '7', '3', '4', '4', '7', '3']
noncomputable def geometryRow6599_physicalVolumeDenominatorChars : List Char := ['7', '1', '3', '8', '0', '9', '1', '6', '9', '0', '5', '2', '8', '6', '8', '8', '0', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6599_physicalVolumeText : String := String.ofList (geometryRow6599_physicalVolumeNumeratorChars ++ '/' :: geometryRow6599_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_physicalVolume_before_field"
  err.flush

theorem geometryRow6599_physicalVolume_field :
    geometryRowsJson6599.getObjVal? "physical_volume" = .ok (.str geometryRow6599_physicalVolumeText) := by rfl

theorem geometryRow6599_physicalVolume_numerator_no_slash :
    geometryRow6599_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6599_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow6599_physicalVolumeNumeratorChars = some (3610207271116344255866777613239426485296734473 : Int) := by decide +kernel

theorem geometryRow6599_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow6599_physicalVolumeDenominatorChars = some (7138091690528688046080000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow6599_physicalVolume_denominator_nonzero : (7138091690528688046080000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6599_physicalVolume_parse :
    parseRational geometryRow6599_physicalVolumeText = .ok geometryRowsTyped6599.physicalVolume :=
  original_rational_fraction_of_chars geometryRow6599_physicalVolumeNumeratorChars geometryRow6599_physicalVolumeDenominatorChars
    (3610207271116344255866777613239426485296734473 : Int) (7138091690528688046080000000000000000000000000000000000000000000000000000 : Int)
    geometryRow6599_physicalVolume_numerator_no_slash geometryRow6599_physicalVolume_numerator_parse
    geometryRow6599_physicalVolume_denominator_parse geometryRow6599_physicalVolume_denominator_nonzero

theorem geometryRow6599_physicalVolume_read :
    rationalField geometryRowsJson6599 "physical_volume" = .ok geometryRowsTyped6599.physicalVolume :=
  original_rationalField_of_string geometryRowsJson6599 "physical_volume" geometryRow6599_physicalVolumeText
    geometryRowsTyped6599.physicalVolume geometryRow6599_physicalVolume_field geometryRow6599_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_physicalVolume_complete"
  err.flush

noncomputable def geometryRow6599_meanGapNumeratorChars : List Char := ['3', '2', '7', '4', '0', '1']
noncomputable def geometryRow6599_meanGapDenominatorChars : List Char := ['6', '8', '4', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6599_meanGapText : String := String.ofList (geometryRow6599_meanGapNumeratorChars ++ '/' :: geometryRow6599_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_meanGap_before_field"
  err.flush

theorem geometryRow6599_meanGap_field :
    geometryRowsJson6599.getObjVal? "mean_gap" = .ok (.str geometryRow6599_meanGapText) := by rfl

theorem geometryRow6599_meanGap_numerator_no_slash :
    geometryRow6599_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6599_meanGap_numerator_parse :
    SourceJson.intChars geometryRow6599_meanGapNumeratorChars = some (327401 : Int) := by decide +kernel

theorem geometryRow6599_meanGap_denominator_parse :
    SourceJson.intChars geometryRow6599_meanGapDenominatorChars = some (6840000000 : Int) := by decide +kernel

theorem geometryRow6599_meanGap_denominator_nonzero : (6840000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6599_meanGap_parse :
    parseRational geometryRow6599_meanGapText = .ok geometryRowsTyped6599.meanGap :=
  original_rational_fraction_of_chars geometryRow6599_meanGapNumeratorChars geometryRow6599_meanGapDenominatorChars
    (327401 : Int) (6840000000 : Int)
    geometryRow6599_meanGap_numerator_no_slash geometryRow6599_meanGap_numerator_parse
    geometryRow6599_meanGap_denominator_parse geometryRow6599_meanGap_denominator_nonzero

theorem geometryRow6599_meanGap_read :
    rationalField geometryRowsJson6599 "mean_gap" = .ok geometryRowsTyped6599.meanGap :=
  original_rationalField_of_string geometryRowsJson6599 "mean_gap" geometryRow6599_meanGapText
    geometryRowsTyped6599.meanGap geometryRow6599_meanGap_field geometryRow6599_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_meanGap_complete"
  err.flush

noncomputable def geometryRow6599_jensenBoundNumeratorChars : List Char := ['2', '1', '1', '1', '5', '6', '0', '4', '1', '5', '7', '7', '9', '1', '7', '6', '3', '3', '3', '3', '4', '7', '0', '1', '8', '2', '3', '3', '2', '4', '6', '1', '4', '2', '2', '3', '6', '2', '3', '7', '2', '4', '3', '9', '4', '1', '8', '4', '1', '8', '3', '2', '0', '0', '7', '6', '6', '1', '4', '1', '1', '0', '8', '2', '5', '5', '3', '7', '3', '6', '0', '5', '7', '4', '6', '7', '1', '5', '0', '6', '0', '4', '0', '8', '1', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow6599_jensenBoundDenominatorChars : List Char := ['1', '1', '2', '7', '9', '3', '5', '9', '6', '4', '1', '9', '8', '2', '6', '4', '8', '4', '9', '6', '8', '2', '9', '6', '1', '0', '3', '4', '1', '5', '3', '8', '5', '9', '1', '5', '7', '7', '9', '8', '5', '5', '7', '9', '8', '5', '1', '7', '1', '6', '2', '2', '3', '3', '1', '6', '3', '6', '7', '5', '0', '4', '3', '7', '0', '8', '9', '9', '8', '2', '6', '1', '6', '7', '0', '3', '7', '1', '4', '4', '9', '6', '1', '2', '6', '0', '5', '5', '2', '8', '8', '6', '0', '2', '4', '8', '8', '9', '7', '0', '5', '4', '0', '8', '4', '6', '4', '1', '6', '1', '5', '3', '2', '3', '9', '3', '5', '5', '3', '1', '1', '7']
noncomputable def geometryRow6599_jensenBoundText : String := String.ofList (geometryRow6599_jensenBoundNumeratorChars ++ '/' :: geometryRow6599_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_jensenBound_before_field"
  err.flush

theorem geometryRow6599_jensenBound_field :
    geometryRowsJson6599.getObjVal? "jensen_bound" = .ok (.str geometryRow6599_jensenBoundText) := by rfl

theorem geometryRow6599_jensenBound_numerator_no_slash :
    geometryRow6599_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow6599_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow6599_jensenBoundNumeratorChars = some (2111560415779176333347018233246142236237243941841832007661411082553736057467150604081920000000000000000 : Int) := by decide +kernel

theorem geometryRow6599_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow6599_jensenBoundDenominatorChars = some (11279359641982648496829610341538591577985579851716223316367504370899826167037144961260552886024889705408464161532393553117 : Int) := by decide +kernel

theorem geometryRow6599_jensenBound_denominator_nonzero : (11279359641982648496829610341538591577985579851716223316367504370899826167037144961260552886024889705408464161532393553117 : Int) ≠ 0 := by decide +kernel

theorem geometryRow6599_jensenBound_parse :
    parseRational geometryRow6599_jensenBoundText = .ok geometryRowsTyped6599.jensenBound :=
  original_rational_fraction_of_chars geometryRow6599_jensenBoundNumeratorChars geometryRow6599_jensenBoundDenominatorChars
    (2111560415779176333347018233246142236237243941841832007661411082553736057467150604081920000000000000000 : Int) (11279359641982648496829610341538591577985579851716223316367504370899826167037144961260552886024889705408464161532393553117 : Int)
    geometryRow6599_jensenBound_numerator_no_slash geometryRow6599_jensenBound_numerator_parse
    geometryRow6599_jensenBound_denominator_parse geometryRow6599_jensenBound_denominator_nonzero

theorem geometryRow6599_jensenBound_read :
    rationalField geometryRowsJson6599 "jensen_bound" = .ok geometryRowsTyped6599.jensenBound :=
  original_rationalField_of_string geometryRowsJson6599 "jensen_bound" geometryRow6599_jensenBoundText
    geometryRowsTyped6599.jensenBound geometryRow6599_jensenBound_field geometryRow6599_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_factorMaxima_before"
  err.flush

theorem geometryRow6599_factorMaxima_read :
    rationalArrayField geometryRowsJson6599 "factor_maxima" = .ok geometryRowsTyped6599.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_gapWeightedMeans_before"
  err.flush

theorem geometryRow6599_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson6599 "gap_weighted_means" = .ok geometryRowsTyped6599.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow6599_floorChars : List Char := ['1', '4', '8', '3', '1', '9', '6', '3', '6', '1', '2']
noncomputable def geometryRow6599_floorText : String := String.ofList geometryRow6599_floorChars

theorem geometryRow6599_floor_text_read :
    geometryRowsJson6599.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow6599_floorText := by rfl

theorem geometryRow6599_floor_chars_parse :
    SourceJson.intChars geometryRow6599_floorChars = some (14831963612 : Int) := by decide +kernel

theorem geometryRow6599_floor_parse :
    parseInteger geometryRow6599_floorText = .ok geometryRowsTyped6599.jensenFloorQ96 := by
  simp only [geometryRow6599_floorText, parseInteger, String.toList_ofList, geometryRow6599_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_6599 :
    decodeGeometryRow geometryRowsJson6599 = .ok geometryRowsTyped6599 :=
  original_geometryRow_of_fields geometryRowsJson6599 geometryRowsTyped6599 geometryRow6599_floorText
    geometryRow6599_simplexId_read geometryRow6599_vertexIds_read
    geometryRow6599_physicalVolume_read geometryRow6599_meanGap_read
    geometryRow6599_factorMaxima_read geometryRow6599_gapWeightedMeans_read
    geometryRow6599_jensenBound_read geometryRow6599_floor_text_read geometryRow6599_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_6599_original_decoder_complete"
  err.flush

theorem geometryRow6599_shape :
    geometryRowsTyped6599.simplexId = 6599 ∧
    geometryRowsTyped6599.vertexIds.size = 9 ∧ geometryRowsTyped6599.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped6599.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped6599.factorMaxima.size = 10 ∧ geometryRowsTyped6599.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock824 : List SourceJson := [geometryRowsJson6592, geometryRowsJson6593, geometryRowsJson6594, geometryRowsJson6595, geometryRowsJson6596, geometryRowsJson6597, geometryRowsJson6598, geometryRowsJson6599]
noncomputable def geometryRowsTypedBlock824 : List GeometryRow := [geometryRowsTyped6592, geometryRowsTyped6593, geometryRowsTyped6594, geometryRowsTyped6595, geometryRowsTyped6596, geometryRowsTyped6597, geometryRowsTyped6598, geometryRowsTyped6599]

theorem geometry_Rows_block_824_push_eq (acc : List SourceJson) :
    SimplicesBlock824.blockPush acc = [geometryRowsJson6599, geometryRowsJson6598, geometryRowsJson6597, geometryRowsJson6596, geometryRowsJson6595, geometryRowsJson6594, geometryRowsJson6593, geometryRowsJson6592] ++ acc := by rfl

theorem geometry_Rows_block_824_reverse (acc : List SourceJson) :
    (SimplicesBlock824.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock824 := by
  rw [geometry_Rows_block_824_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_824 :
    geometryRowsJsonBlock824.mapM decodeGeometryRow = .ok geometryRowsTypedBlock824 := by
  simp only [geometryRowsJsonBlock824, geometryRowsTypedBlock824, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_6592, decode_geometry_Rows_6593, decode_geometry_Rows_6594, decode_geometry_Rows_6595, decode_geometry_Rows_6596, decode_geometry_Rows_6597, decode_geometry_Rows_6598, decode_geometry_Rows_6599]
  rfl

theorem geometry_Rows_block_824_length : geometryRowsTypedBlock824.length = 8 := by rfl

#print axioms geometryRow6592_simplexId_read
#print axioms geometryRow6592_vertexIds_read
#print axioms geometryRow6592_physicalVolume_field
#print axioms geometryRow6592_physicalVolume_numerator_no_slash
#print axioms geometryRow6592_physicalVolume_numerator_parse
#print axioms geometryRow6592_physicalVolume_denominator_parse
#print axioms geometryRow6592_physicalVolume_denominator_nonzero
#print axioms geometryRow6592_physicalVolume_parse
#print axioms geometryRow6592_physicalVolume_read
#print axioms geometryRow6592_meanGap_field
#print axioms geometryRow6592_meanGap_numerator_no_slash
#print axioms geometryRow6592_meanGap_numerator_parse
#print axioms geometryRow6592_meanGap_denominator_parse
#print axioms geometryRow6592_meanGap_denominator_nonzero
#print axioms geometryRow6592_meanGap_parse
#print axioms geometryRow6592_meanGap_read
#print axioms geometryRow6592_jensenBound_field
#print axioms geometryRow6592_jensenBound_numerator_no_slash
#print axioms geometryRow6592_jensenBound_numerator_parse
#print axioms geometryRow6592_jensenBound_denominator_parse
#print axioms geometryRow6592_jensenBound_denominator_nonzero
#print axioms geometryRow6592_jensenBound_parse
#print axioms geometryRow6592_jensenBound_read
#print axioms geometryRow6592_factorMaxima_read
#print axioms geometryRow6592_gapWeightedMeans_read
#print axioms geometryRow6592_floor_text_read
#print axioms geometryRow6592_floor_chars_parse
#print axioms geometryRow6592_floor_parse
#print axioms decode_geometry_Rows_6592
#print axioms geometryRow6592_shape
#print axioms geometryRow6593_simplexId_read
#print axioms geometryRow6593_vertexIds_read
#print axioms geometryRow6593_physicalVolume_field
#print axioms geometryRow6593_physicalVolume_numerator_no_slash
#print axioms geometryRow6593_physicalVolume_numerator_parse
#print axioms geometryRow6593_physicalVolume_denominator_parse
#print axioms geometryRow6593_physicalVolume_denominator_nonzero
#print axioms geometryRow6593_physicalVolume_parse
#print axioms geometryRow6593_physicalVolume_read
#print axioms geometryRow6593_meanGap_field
#print axioms geometryRow6593_meanGap_numerator_no_slash
#print axioms geometryRow6593_meanGap_numerator_parse
#print axioms geometryRow6593_meanGap_denominator_parse
#print axioms geometryRow6593_meanGap_denominator_nonzero
#print axioms geometryRow6593_meanGap_parse
#print axioms geometryRow6593_meanGap_read
#print axioms geometryRow6593_jensenBound_field
#print axioms geometryRow6593_jensenBound_numerator_no_slash
#print axioms geometryRow6593_jensenBound_numerator_parse
#print axioms geometryRow6593_jensenBound_denominator_parse
#print axioms geometryRow6593_jensenBound_denominator_nonzero
#print axioms geometryRow6593_jensenBound_parse
#print axioms geometryRow6593_jensenBound_read
#print axioms geometryRow6593_factorMaxima_read
#print axioms geometryRow6593_gapWeightedMeans_read
#print axioms geometryRow6593_floor_text_read
#print axioms geometryRow6593_floor_chars_parse
#print axioms geometryRow6593_floor_parse
#print axioms decode_geometry_Rows_6593
#print axioms geometryRow6593_shape
#print axioms geometryRow6594_simplexId_read
#print axioms geometryRow6594_vertexIds_read
#print axioms geometryRow6594_physicalVolume_field
#print axioms geometryRow6594_physicalVolume_numerator_no_slash
#print axioms geometryRow6594_physicalVolume_numerator_parse
#print axioms geometryRow6594_physicalVolume_denominator_parse
#print axioms geometryRow6594_physicalVolume_denominator_nonzero
#print axioms geometryRow6594_physicalVolume_parse
#print axioms geometryRow6594_physicalVolume_read
#print axioms geometryRow6594_meanGap_field
#print axioms geometryRow6594_meanGap_numerator_no_slash
#print axioms geometryRow6594_meanGap_numerator_parse
#print axioms geometryRow6594_meanGap_denominator_parse
#print axioms geometryRow6594_meanGap_denominator_nonzero
#print axioms geometryRow6594_meanGap_parse
#print axioms geometryRow6594_meanGap_read
#print axioms geometryRow6594_jensenBound_field
#print axioms geometryRow6594_jensenBound_numerator_no_slash
#print axioms geometryRow6594_jensenBound_numerator_parse
#print axioms geometryRow6594_jensenBound_denominator_parse
#print axioms geometryRow6594_jensenBound_denominator_nonzero
#print axioms geometryRow6594_jensenBound_parse
#print axioms geometryRow6594_jensenBound_read
#print axioms geometryRow6594_factorMaxima_read
#print axioms geometryRow6594_gapWeightedMeans_read
#print axioms geometryRow6594_floor_text_read
#print axioms geometryRow6594_floor_chars_parse
#print axioms geometryRow6594_floor_parse
#print axioms decode_geometry_Rows_6594
#print axioms geometryRow6594_shape
#print axioms geometryRow6595_simplexId_read
#print axioms geometryRow6595_vertexIds_read
#print axioms geometryRow6595_physicalVolume_field
#print axioms geometryRow6595_physicalVolume_numerator_no_slash
#print axioms geometryRow6595_physicalVolume_numerator_parse
#print axioms geometryRow6595_physicalVolume_denominator_parse
#print axioms geometryRow6595_physicalVolume_denominator_nonzero
#print axioms geometryRow6595_physicalVolume_parse
#print axioms geometryRow6595_physicalVolume_read
#print axioms geometryRow6595_meanGap_field
#print axioms geometryRow6595_meanGap_numerator_no_slash
#print axioms geometryRow6595_meanGap_numerator_parse
#print axioms geometryRow6595_meanGap_denominator_parse
#print axioms geometryRow6595_meanGap_denominator_nonzero
#print axioms geometryRow6595_meanGap_parse
#print axioms geometryRow6595_meanGap_read
#print axioms geometryRow6595_jensenBound_field
#print axioms geometryRow6595_jensenBound_numerator_no_slash
#print axioms geometryRow6595_jensenBound_numerator_parse
#print axioms geometryRow6595_jensenBound_denominator_parse
#print axioms geometryRow6595_jensenBound_denominator_nonzero
#print axioms geometryRow6595_jensenBound_parse
#print axioms geometryRow6595_jensenBound_read
#print axioms geometryRow6595_factorMaxima_read
#print axioms geometryRow6595_gapWeightedMeans_read
#print axioms geometryRow6595_floor_text_read
#print axioms geometryRow6595_floor_chars_parse
#print axioms geometryRow6595_floor_parse
#print axioms decode_geometry_Rows_6595
#print axioms geometryRow6595_shape
#print axioms geometryRow6596_simplexId_read
#print axioms geometryRow6596_vertexIds_read
#print axioms geometryRow6596_physicalVolume_field
#print axioms geometryRow6596_physicalVolume_numerator_no_slash
#print axioms geometryRow6596_physicalVolume_numerator_parse
#print axioms geometryRow6596_physicalVolume_denominator_parse
#print axioms geometryRow6596_physicalVolume_denominator_nonzero
#print axioms geometryRow6596_physicalVolume_parse
#print axioms geometryRow6596_physicalVolume_read
#print axioms geometryRow6596_meanGap_field
#print axioms geometryRow6596_meanGap_numerator_no_slash
#print axioms geometryRow6596_meanGap_numerator_parse
#print axioms geometryRow6596_meanGap_denominator_parse
#print axioms geometryRow6596_meanGap_denominator_nonzero
#print axioms geometryRow6596_meanGap_parse
#print axioms geometryRow6596_meanGap_read
#print axioms geometryRow6596_jensenBound_field
#print axioms geometryRow6596_jensenBound_numerator_no_slash
#print axioms geometryRow6596_jensenBound_numerator_parse
#print axioms geometryRow6596_jensenBound_denominator_parse
#print axioms geometryRow6596_jensenBound_denominator_nonzero
#print axioms geometryRow6596_jensenBound_parse
#print axioms geometryRow6596_jensenBound_read
#print axioms geometryRow6596_factorMaxima_read
#print axioms geometryRow6596_gapWeightedMeans_read
#print axioms geometryRow6596_floor_text_read
#print axioms geometryRow6596_floor_chars_parse
#print axioms geometryRow6596_floor_parse
#print axioms decode_geometry_Rows_6596
#print axioms geometryRow6596_shape
#print axioms geometryRow6597_simplexId_read
#print axioms geometryRow6597_vertexIds_read
#print axioms geometryRow6597_physicalVolume_field
#print axioms geometryRow6597_physicalVolume_numerator_no_slash
#print axioms geometryRow6597_physicalVolume_numerator_parse
#print axioms geometryRow6597_physicalVolume_denominator_parse
#print axioms geometryRow6597_physicalVolume_denominator_nonzero
#print axioms geometryRow6597_physicalVolume_parse
#print axioms geometryRow6597_physicalVolume_read
#print axioms geometryRow6597_meanGap_field
#print axioms geometryRow6597_meanGap_numerator_no_slash
#print axioms geometryRow6597_meanGap_numerator_parse
#print axioms geometryRow6597_meanGap_denominator_parse
#print axioms geometryRow6597_meanGap_denominator_nonzero
#print axioms geometryRow6597_meanGap_parse
#print axioms geometryRow6597_meanGap_read
#print axioms geometryRow6597_jensenBound_field
#print axioms geometryRow6597_jensenBound_numerator_no_slash
#print axioms geometryRow6597_jensenBound_numerator_parse
#print axioms geometryRow6597_jensenBound_denominator_parse
#print axioms geometryRow6597_jensenBound_denominator_nonzero
#print axioms geometryRow6597_jensenBound_parse
#print axioms geometryRow6597_jensenBound_read
#print axioms geometryRow6597_factorMaxima_read
#print axioms geometryRow6597_gapWeightedMeans_read
#print axioms geometryRow6597_floor_text_read
#print axioms geometryRow6597_floor_chars_parse
#print axioms geometryRow6597_floor_parse
#print axioms decode_geometry_Rows_6597
#print axioms geometryRow6597_shape
#print axioms geometryRow6598_simplexId_read
#print axioms geometryRow6598_vertexIds_read
#print axioms geometryRow6598_physicalVolume_field
#print axioms geometryRow6598_physicalVolume_numerator_no_slash
#print axioms geometryRow6598_physicalVolume_numerator_parse
#print axioms geometryRow6598_physicalVolume_denominator_parse
#print axioms geometryRow6598_physicalVolume_denominator_nonzero
#print axioms geometryRow6598_physicalVolume_parse
#print axioms geometryRow6598_physicalVolume_read
#print axioms geometryRow6598_meanGap_field
#print axioms geometryRow6598_meanGap_numerator_no_slash
#print axioms geometryRow6598_meanGap_numerator_parse
#print axioms geometryRow6598_meanGap_denominator_parse
#print axioms geometryRow6598_meanGap_denominator_nonzero
#print axioms geometryRow6598_meanGap_parse
#print axioms geometryRow6598_meanGap_read
#print axioms geometryRow6598_jensenBound_field
#print axioms geometryRow6598_jensenBound_numerator_no_slash
#print axioms geometryRow6598_jensenBound_numerator_parse
#print axioms geometryRow6598_jensenBound_denominator_parse
#print axioms geometryRow6598_jensenBound_denominator_nonzero
#print axioms geometryRow6598_jensenBound_parse
#print axioms geometryRow6598_jensenBound_read
#print axioms geometryRow6598_factorMaxima_read
#print axioms geometryRow6598_gapWeightedMeans_read
#print axioms geometryRow6598_floor_text_read
#print axioms geometryRow6598_floor_chars_parse
#print axioms geometryRow6598_floor_parse
#print axioms decode_geometry_Rows_6598
#print axioms geometryRow6598_shape
#print axioms geometryRow6599_simplexId_read
#print axioms geometryRow6599_vertexIds_read
#print axioms geometryRow6599_physicalVolume_field
#print axioms geometryRow6599_physicalVolume_numerator_no_slash
#print axioms geometryRow6599_physicalVolume_numerator_parse
#print axioms geometryRow6599_physicalVolume_denominator_parse
#print axioms geometryRow6599_physicalVolume_denominator_nonzero
#print axioms geometryRow6599_physicalVolume_parse
#print axioms geometryRow6599_physicalVolume_read
#print axioms geometryRow6599_meanGap_field
#print axioms geometryRow6599_meanGap_numerator_no_slash
#print axioms geometryRow6599_meanGap_numerator_parse
#print axioms geometryRow6599_meanGap_denominator_parse
#print axioms geometryRow6599_meanGap_denominator_nonzero
#print axioms geometryRow6599_meanGap_parse
#print axioms geometryRow6599_meanGap_read
#print axioms geometryRow6599_jensenBound_field
#print axioms geometryRow6599_jensenBound_numerator_no_slash
#print axioms geometryRow6599_jensenBound_numerator_parse
#print axioms geometryRow6599_jensenBound_denominator_parse
#print axioms geometryRow6599_jensenBound_denominator_nonzero
#print axioms geometryRow6599_jensenBound_parse
#print axioms geometryRow6599_jensenBound_read
#print axioms geometryRow6599_factorMaxima_read
#print axioms geometryRow6599_gapWeightedMeans_read
#print axioms geometryRow6599_floor_text_read
#print axioms geometryRow6599_floor_chars_parse
#print axioms geometryRow6599_floor_parse
#print axioms decode_geometry_Rows_6599
#print axioms geometryRow6599_shape
#print axioms geometry_Rows_block_824_push_eq
#print axioms geometry_Rows_block_824_reverse
#print axioms decode_geometry_Rows_block_824
#print axioms geometry_Rows_block_824_length

end ImbalancedChen.P2OriginalSaving19Geometry12ScalableDecoding
