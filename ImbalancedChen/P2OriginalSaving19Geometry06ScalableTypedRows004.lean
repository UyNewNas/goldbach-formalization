import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock004

/-! Local typed certificates for original cell 06, rows 32 through 39.
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

noncomputable def geometryRowsJson032 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped032 : GeometryRow :=
  { simplexId := 32,
    vertexIds := #[32, 30, 20, 16, 14, 13, 4, 1, 0],
    physicalVolume := ((6645948989890061943333068125466984570914171 : ℚ) / (667020864351744000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((4224766360538981006213393 : ℚ) / (47296362502400091696000000 : ℚ)), ((361285478333321701143329 : ℚ) / (3928269310830572400000000 : ℚ)), ((11874309155431915441332883 : ℚ) / (102818179353043677600000000 : ℚ)), ((211484872746644897872379879 : ℚ) / (2364818125120004584800000000 : ℚ)), ((69348192859658951410816121 : ℚ) / (788272708373334861600000000 : ℚ)), ((3162043017627331339586293 : ℚ) / (42996693184000083360000000 : ℚ)), ((780673601917769419948369 : ℚ) / (21498346592000041680000000 : ℚ)), ((775857393552288402363703 : ℚ) / (21498346592000041680000000 : ℚ)), ((752473619177689684304983 : ℚ) / (21498346592000041680000000 : ℚ)), ((41052074930210755726841 : ℚ) / (1309423103610190800000000 : ℚ))],
    jensenBound := ((14463428260627460513114849617725383701963520325397341001132062716303731860219504963190071478719656534553780492119392852845997818512450010469625572894780817658616272230583818553251130444261930449706273273436113469440000000000000000 : ℚ) / (129967930339232233759212850482933784428616689825918347372290021211620568566325656950854889021419776945367168226874430506871780835556458872917252697263311842710237807353329210505795675801024846932949290581624413727823419881462618229717555753937 : ℚ)),
    jensenFloorQ96 := (8816873837687714 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_simplexId_before"
  err.flush

theorem geometryRow032_simplexId_read :
    geometryRowsJson032.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped032.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_vertexIds_before"
  err.flush

theorem geometryRow032_vertexIds_read :
    geometryRowsJson032.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped032.vertexIds := by decide +kernel

noncomputable def geometryRow032_physicalVolumeNumeratorChars : List Char := ['6', '6', '4', '5', '9', '4', '8', '9', '8', '9', '8', '9', '0', '0', '6', '1', '9', '4', '3', '3', '3', '3', '0', '6', '8', '1', '2', '5', '4', '6', '6', '9', '8', '4', '5', '7', '0', '9', '1', '4', '1', '7', '1']
noncomputable def geometryRow032_physicalVolumeDenominatorChars : List Char := ['6', '6', '7', '0', '2', '0', '8', '6', '4', '3', '5', '1', '7', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_physicalVolumeText : String := String.ofList (geometryRow032_physicalVolumeNumeratorChars ++ '/' :: geometryRow032_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_physicalVolume_before_field"
  err.flush

theorem geometryRow032_physicalVolume_field :
    geometryRowsJson032.getObjVal? "physical_volume" = .ok (.str geometryRow032_physicalVolumeText) := by rfl

theorem geometryRow032_physicalVolume_numerator_no_slash :
    geometryRow032_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeNumeratorChars = some (6645948989890061943333068125466984570914171 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow032_physicalVolumeDenominatorChars = some (667020864351744000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow032_physicalVolume_denominator_nonzero : (667020864351744000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_physicalVolume_parse :
    parseRational geometryRow032_physicalVolumeText = .ok geometryRowsTyped032.physicalVolume :=
  original_rational_fraction_of_chars geometryRow032_physicalVolumeNumeratorChars geometryRow032_physicalVolumeDenominatorChars
    (6645948989890061943333068125466984570914171 : Int) (667020864351744000000000000000000000000000000000000000000000000000 : Int)
    geometryRow032_physicalVolume_numerator_no_slash geometryRow032_physicalVolume_numerator_parse
    geometryRow032_physicalVolume_denominator_parse geometryRow032_physicalVolume_denominator_nonzero

theorem geometryRow032_physicalVolume_read :
    rationalField geometryRowsJson032 "physical_volume" = .ok geometryRowsTyped032.physicalVolume :=
  original_rationalField_of_string geometryRowsJson032 "physical_volume" geometryRow032_physicalVolumeText
    geometryRowsTyped032.physicalVolume geometryRow032_physicalVolume_field geometryRow032_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_physicalVolume_complete"
  err.flush

noncomputable def geometryRow032_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow032_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_meanGapText : String := String.ofList (geometryRow032_meanGapNumeratorChars ++ '/' :: geometryRow032_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_meanGap_before_field"
  err.flush

theorem geometryRow032_meanGap_field :
    geometryRowsJson032.getObjVal? "mean_gap" = .ok (.str geometryRow032_meanGapText) := by rfl

theorem geometryRow032_meanGap_numerator_no_slash :
    geometryRow032_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_meanGap_numerator_parse :
    SourceJson.intChars geometryRow032_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_parse :
    SourceJson.intChars geometryRow032_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow032_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_meanGap_parse :
    parseRational geometryRow032_meanGapText = .ok geometryRowsTyped032.meanGap :=
  original_rational_fraction_of_chars geometryRow032_meanGapNumeratorChars geometryRow032_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow032_meanGap_numerator_no_slash geometryRow032_meanGap_numerator_parse
    geometryRow032_meanGap_denominator_parse geometryRow032_meanGap_denominator_nonzero

theorem geometryRow032_meanGap_read :
    rationalField geometryRowsJson032 "mean_gap" = .ok geometryRowsTyped032.meanGap :=
  original_rationalField_of_string geometryRowsJson032 "mean_gap" geometryRow032_meanGapText
    geometryRowsTyped032.meanGap geometryRow032_meanGap_field geometryRow032_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_meanGap_complete"
  err.flush

noncomputable def geometryRow032_jensenBoundNumeratorChars : List Char := ['1', '4', '4', '6', '3', '4', '2', '8', '2', '6', '0', '6', '2', '7', '4', '6', '0', '5', '1', '3', '1', '1', '4', '8', '4', '9', '6', '1', '7', '7', '2', '5', '3', '8', '3', '7', '0', '1', '9', '6', '3', '5', '2', '0', '3', '2', '5', '3', '9', '7', '3', '4', '1', '0', '0', '1', '1', '3', '2', '0', '6', '2', '7', '1', '6', '3', '0', '3', '7', '3', '1', '8', '6', '0', '2', '1', '9', '5', '0', '4', '9', '6', '3', '1', '9', '0', '0', '7', '1', '4', '7', '8', '7', '1', '9', '6', '5', '6', '5', '3', '4', '5', '5', '3', '7', '8', '0', '4', '9', '2', '1', '1', '9', '3', '9', '2', '8', '5', '2', '8', '4', '5', '9', '9', '7', '8', '1', '8', '5', '1', '2', '4', '5', '0', '0', '1', '0', '4', '6', '9', '6', '2', '5', '5', '7', '2', '8', '9', '4', '7', '8', '0', '8', '1', '7', '6', '5', '8', '6', '1', '6', '2', '7', '2', '2', '3', '0', '5', '8', '3', '8', '1', '8', '5', '5', '3', '2', '5', '1', '1', '3', '0', '4', '4', '4', '2', '6', '1', '9', '3', '0', '4', '4', '9', '7', '0', '6', '2', '7', '3', '2', '7', '3', '4', '3', '6', '1', '1', '3', '4', '6', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow032_jensenBoundDenominatorChars : List Char := ['1', '2', '9', '9', '6', '7', '9', '3', '0', '3', '3', '9', '2', '3', '2', '2', '3', '3', '7', '5', '9', '2', '1', '2', '8', '5', '0', '4', '8', '2', '9', '3', '3', '7', '8', '4', '4', '2', '8', '6', '1', '6', '6', '8', '9', '8', '2', '5', '9', '1', '8', '3', '4', '7', '3', '7', '2', '2', '9', '0', '0', '2', '1', '2', '1', '1', '6', '2', '0', '5', '6', '8', '5', '6', '6', '3', '2', '5', '6', '5', '6', '9', '5', '0', '8', '5', '4', '8', '8', '9', '0', '2', '1', '4', '1', '9', '7', '7', '6', '9', '4', '5', '3', '6', '7', '1', '6', '8', '2', '2', '6', '8', '7', '4', '4', '3', '0', '5', '0', '6', '8', '7', '1', '7', '8', '0', '8', '3', '5', '5', '5', '6', '4', '5', '8', '8', '7', '2', '9', '1', '7', '2', '5', '2', '6', '9', '7', '2', '6', '3', '3', '1', '1', '8', '4', '2', '7', '1', '0', '2', '3', '7', '8', '0', '7', '3', '5', '3', '3', '2', '9', '2', '1', '0', '5', '0', '5', '7', '9', '5', '6', '7', '5', '8', '0', '1', '0', '2', '4', '8', '4', '6', '9', '3', '2', '9', '4', '9', '2', '9', '0', '5', '8', '1', '6', '2', '4', '4', '1', '3', '7', '2', '7', '8', '2', '3', '4', '1', '9', '8', '8', '1', '4', '6', '2', '6', '1', '8', '2', '2', '9', '7', '1', '7', '5', '5', '5', '7', '5', '3', '9', '3', '7']
noncomputable def geometryRow032_jensenBoundText : String := String.ofList (geometryRow032_jensenBoundNumeratorChars ++ '/' :: geometryRow032_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_jensenBound_before_field"
  err.flush

theorem geometryRow032_jensenBound_field :
    geometryRowsJson032.getObjVal? "jensen_bound" = .ok (.str geometryRow032_jensenBoundText) := by rfl

theorem geometryRow032_jensenBound_numerator_no_slash :
    geometryRow032_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow032_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow032_jensenBoundNumeratorChars = some (14463428260627460513114849617725383701963520325397341001132062716303731860219504963190071478719656534553780492119392852845997818512450010469625572894780817658616272230583818553251130444261930449706273273436113469440000000000000000 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow032_jensenBoundDenominatorChars = some (129967930339232233759212850482933784428616689825918347372290021211620568566325656950854889021419776945367168226874430506871780835556458872917252697263311842710237807353329210505795675801024846932949290581624413727823419881462618229717555753937 : Int) := by decide +kernel

theorem geometryRow032_jensenBound_denominator_nonzero : (129967930339232233759212850482933784428616689825918347372290021211620568566325656950854889021419776945367168226874430506871780835556458872917252697263311842710237807353329210505795675801024846932949290581624413727823419881462618229717555753937 : Int) ≠ 0 := by decide +kernel

theorem geometryRow032_jensenBound_parse :
    parseRational geometryRow032_jensenBoundText = .ok geometryRowsTyped032.jensenBound :=
  original_rational_fraction_of_chars geometryRow032_jensenBoundNumeratorChars geometryRow032_jensenBoundDenominatorChars
    (14463428260627460513114849617725383701963520325397341001132062716303731860219504963190071478719656534553780492119392852845997818512450010469625572894780817658616272230583818553251130444261930449706273273436113469440000000000000000 : Int) (129967930339232233759212850482933784428616689825918347372290021211620568566325656950854889021419776945367168226874430506871780835556458872917252697263311842710237807353329210505795675801024846932949290581624413727823419881462618229717555753937 : Int)
    geometryRow032_jensenBound_numerator_no_slash geometryRow032_jensenBound_numerator_parse
    geometryRow032_jensenBound_denominator_parse geometryRow032_jensenBound_denominator_nonzero

theorem geometryRow032_jensenBound_read :
    rationalField geometryRowsJson032 "jensen_bound" = .ok geometryRowsTyped032.jensenBound :=
  original_rationalField_of_string geometryRowsJson032 "jensen_bound" geometryRow032_jensenBoundText
    geometryRowsTyped032.jensenBound geometryRow032_jensenBound_field geometryRow032_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_factorMaxima_before"
  err.flush

theorem geometryRow032_factorMaxima_read :
    rationalArrayField geometryRowsJson032 "factor_maxima" = .ok geometryRowsTyped032.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_gapWeightedMeans_before"
  err.flush

theorem geometryRow032_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson032 "gap_weighted_means" = .ok geometryRowsTyped032.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow032_floorChars : List Char := ['8', '8', '1', '6', '8', '7', '3', '8', '3', '7', '6', '8', '7', '7', '1', '4']
noncomputable def geometryRow032_floorText : String := String.ofList geometryRow032_floorChars

theorem geometryRow032_floor_text_read :
    geometryRowsJson032.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow032_floorText := by rfl

theorem geometryRow032_floor_chars_parse :
    SourceJson.intChars geometryRow032_floorChars = some (8816873837687714 : Int) := by decide +kernel

theorem geometryRow032_floor_parse :
    parseInteger geometryRow032_floorText = .ok geometryRowsTyped032.jensenFloorQ96 := by
  simp only [geometryRow032_floorText, parseInteger, String.toList_ofList, geometryRow032_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_032 :
    decodeGeometryRow geometryRowsJson032 = .ok geometryRowsTyped032 :=
  original_geometryRow_of_fields geometryRowsJson032 geometryRowsTyped032 geometryRow032_floorText
    geometryRow032_simplexId_read geometryRow032_vertexIds_read
    geometryRow032_physicalVolume_read geometryRow032_meanGap_read
    geometryRow032_factorMaxima_read geometryRow032_gapWeightedMeans_read
    geometryRow032_jensenBound_read geometryRow032_floor_text_read geometryRow032_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_032_original_decoder_complete"
  err.flush

theorem geometryRow032_shape :
    geometryRowsTyped032.simplexId = 32 ∧
    geometryRowsTyped032.vertexIds.size = 9 ∧ geometryRowsTyped032.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped032.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped032.factorMaxima.size = 10 ∧ geometryRowsTyped032.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson033 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped033 : GeometryRow :=
  { simplexId := 33,
    vertexIds := #[32, 30, 20, 16, 14, 13, 10, 1, 0],
    physicalVolume := ((476003625448840488830331292548117656037300799 : ℚ) / (4002125186110464000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7712550405552708113813 : ℚ) / (85738087468923120000000 : ℚ)), ((5631137501968565298763 : ℚ) / (61241491049230800000000 : ℚ)), ((4320692241593573524247 : ℚ) / (37277429334314400000000 : ℚ)), ((75924484009168613021251 : ℚ) / (857380874689231200000000 : ℚ)), ((8297464665544524760783 : ℚ) / (95264541632136800000000 : ℚ)), ((1161310101008383893209 : ℚ) / (15588743176167840000000 : ℚ)), ((294480255554513161043 : ℚ) / (7794371588083920000000 : ℚ)), ((277295592981000860471 : ℚ) / (7794371588083920000000 : ℚ)), ((268817646743248776791 : ℚ) / (7794371588083920000000 : ℚ)), ((639857006030919585427 : ℚ) / (20413830349743600000000 : ℚ))],
    jensenBound := ((89138249750870231830764511450964784628758973532143575820523870907067953263033862671593621004726413535664204878556299227576182574299369622976796988067485511835951850096845395273554329600000000000000000 : ℚ) / (101486715471279977672420338841201577386268337936301124418311119660988213947309237619616592347672387649753777324865672039534023210708845986859719842203716306911764917148565291973690804812532009723600889145601241039 : ℚ)),
    jensenFloorQ96 := (69588021493291886 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_simplexId_before"
  err.flush

theorem geometryRow033_simplexId_read :
    geometryRowsJson033.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped033.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_vertexIds_before"
  err.flush

theorem geometryRow033_vertexIds_read :
    geometryRowsJson033.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped033.vertexIds := by decide +kernel

noncomputable def geometryRow033_physicalVolumeNumeratorChars : List Char := ['4', '7', '6', '0', '0', '3', '6', '2', '5', '4', '4', '8', '8', '4', '0', '4', '8', '8', '8', '3', '0', '3', '3', '1', '2', '9', '2', '5', '4', '8', '1', '1', '7', '6', '5', '6', '0', '3', '7', '3', '0', '0', '7', '9', '9']
noncomputable def geometryRow033_physicalVolumeDenominatorChars : List Char := ['4', '0', '0', '2', '1', '2', '5', '1', '8', '6', '1', '1', '0', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_physicalVolumeText : String := String.ofList (geometryRow033_physicalVolumeNumeratorChars ++ '/' :: geometryRow033_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_physicalVolume_before_field"
  err.flush

theorem geometryRow033_physicalVolume_field :
    geometryRowsJson033.getObjVal? "physical_volume" = .ok (.str geometryRow033_physicalVolumeText) := by rfl

theorem geometryRow033_physicalVolume_numerator_no_slash :
    geometryRow033_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeNumeratorChars = some (476003625448840488830331292548117656037300799 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow033_physicalVolumeDenominatorChars = some (4002125186110464000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow033_physicalVolume_denominator_nonzero : (4002125186110464000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_physicalVolume_parse :
    parseRational geometryRow033_physicalVolumeText = .ok geometryRowsTyped033.physicalVolume :=
  original_rational_fraction_of_chars geometryRow033_physicalVolumeNumeratorChars geometryRow033_physicalVolumeDenominatorChars
    (476003625448840488830331292548117656037300799 : Int) (4002125186110464000000000000000000000000000000000000000000000000000 : Int)
    geometryRow033_physicalVolume_numerator_no_slash geometryRow033_physicalVolume_numerator_parse
    geometryRow033_physicalVolume_denominator_parse geometryRow033_physicalVolume_denominator_nonzero

theorem geometryRow033_physicalVolume_read :
    rationalField geometryRowsJson033 "physical_volume" = .ok geometryRowsTyped033.physicalVolume :=
  original_rationalField_of_string geometryRowsJson033 "physical_volume" geometryRow033_physicalVolumeText
    geometryRowsTyped033.physicalVolume geometryRow033_physicalVolume_field geometryRow033_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_physicalVolume_complete"
  err.flush

noncomputable def geometryRow033_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow033_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_meanGapText : String := String.ofList (geometryRow033_meanGapNumeratorChars ++ '/' :: geometryRow033_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_meanGap_before_field"
  err.flush

theorem geometryRow033_meanGap_field :
    geometryRowsJson033.getObjVal? "mean_gap" = .ok (.str geometryRow033_meanGapText) := by rfl

theorem geometryRow033_meanGap_numerator_no_slash :
    geometryRow033_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_meanGap_numerator_parse :
    SourceJson.intChars geometryRow033_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_parse :
    SourceJson.intChars geometryRow033_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow033_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_meanGap_parse :
    parseRational geometryRow033_meanGapText = .ok geometryRowsTyped033.meanGap :=
  original_rational_fraction_of_chars geometryRow033_meanGapNumeratorChars geometryRow033_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow033_meanGap_numerator_no_slash geometryRow033_meanGap_numerator_parse
    geometryRow033_meanGap_denominator_parse geometryRow033_meanGap_denominator_nonzero

theorem geometryRow033_meanGap_read :
    rationalField geometryRowsJson033 "mean_gap" = .ok geometryRowsTyped033.meanGap :=
  original_rationalField_of_string geometryRowsJson033 "mean_gap" geometryRow033_meanGapText
    geometryRowsTyped033.meanGap geometryRow033_meanGap_field geometryRow033_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_meanGap_complete"
  err.flush

noncomputable def geometryRow033_jensenBoundNumeratorChars : List Char := ['8', '9', '1', '3', '8', '2', '4', '9', '7', '5', '0', '8', '7', '0', '2', '3', '1', '8', '3', '0', '7', '6', '4', '5', '1', '1', '4', '5', '0', '9', '6', '4', '7', '8', '4', '6', '2', '8', '7', '5', '8', '9', '7', '3', '5', '3', '2', '1', '4', '3', '5', '7', '5', '8', '2', '0', '5', '2', '3', '8', '7', '0', '9', '0', '7', '0', '6', '7', '9', '5', '3', '2', '6', '3', '0', '3', '3', '8', '6', '2', '6', '7', '1', '5', '9', '3', '6', '2', '1', '0', '0', '4', '7', '2', '6', '4', '1', '3', '5', '3', '5', '6', '6', '4', '2', '0', '4', '8', '7', '8', '5', '5', '6', '2', '9', '9', '2', '2', '7', '5', '7', '6', '1', '8', '2', '5', '7', '4', '2', '9', '9', '3', '6', '9', '6', '2', '2', '9', '7', '6', '7', '9', '6', '9', '8', '8', '0', '6', '7', '4', '8', '5', '5', '1', '1', '8', '3', '5', '9', '5', '1', '8', '5', '0', '0', '9', '6', '8', '4', '5', '3', '9', '5', '2', '7', '3', '5', '5', '4', '3', '2', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow033_jensenBoundDenominatorChars : List Char := ['1', '0', '1', '4', '8', '6', '7', '1', '5', '4', '7', '1', '2', '7', '9', '9', '7', '7', '6', '7', '2', '4', '2', '0', '3', '3', '8', '8', '4', '1', '2', '0', '1', '5', '7', '7', '3', '8', '6', '2', '6', '8', '3', '3', '7', '9', '3', '6', '3', '0', '1', '1', '2', '4', '4', '1', '8', '3', '1', '1', '1', '1', '9', '6', '6', '0', '9', '8', '8', '2', '1', '3', '9', '4', '7', '3', '0', '9', '2', '3', '7', '6', '1', '9', '6', '1', '6', '5', '9', '2', '3', '4', '7', '6', '7', '2', '3', '8', '7', '6', '4', '9', '7', '5', '3', '7', '7', '7', '3', '2', '4', '8', '6', '5', '6', '7', '2', '0', '3', '9', '5', '3', '4', '0', '2', '3', '2', '1', '0', '7', '0', '8', '8', '4', '5', '9', '8', '6', '8', '5', '9', '7', '1', '9', '8', '4', '2', '2', '0', '3', '7', '1', '6', '3', '0', '6', '9', '1', '1', '7', '6', '4', '9', '1', '7', '1', '4', '8', '5', '6', '5', '2', '9', '1', '9', '7', '3', '6', '9', '0', '8', '0', '4', '8', '1', '2', '5', '3', '2', '0', '0', '9', '7', '2', '3', '6', '0', '0', '8', '8', '9', '1', '4', '5', '6', '0', '1', '2', '4', '1', '0', '3', '9']
noncomputable def geometryRow033_jensenBoundText : String := String.ofList (geometryRow033_jensenBoundNumeratorChars ++ '/' :: geometryRow033_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_jensenBound_before_field"
  err.flush

theorem geometryRow033_jensenBound_field :
    geometryRowsJson033.getObjVal? "jensen_bound" = .ok (.str geometryRow033_jensenBoundText) := by rfl

theorem geometryRow033_jensenBound_numerator_no_slash :
    geometryRow033_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow033_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow033_jensenBoundNumeratorChars = some (89138249750870231830764511450964784628758973532143575820523870907067953263033862671593621004726413535664204878556299227576182574299369622976796988067485511835951850096845395273554329600000000000000000 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow033_jensenBoundDenominatorChars = some (101486715471279977672420338841201577386268337936301124418311119660988213947309237619616592347672387649753777324865672039534023210708845986859719842203716306911764917148565291973690804812532009723600889145601241039 : Int) := by decide +kernel

theorem geometryRow033_jensenBound_denominator_nonzero : (101486715471279977672420338841201577386268337936301124418311119660988213947309237619616592347672387649753777324865672039534023210708845986859719842203716306911764917148565291973690804812532009723600889145601241039 : Int) ≠ 0 := by decide +kernel

theorem geometryRow033_jensenBound_parse :
    parseRational geometryRow033_jensenBoundText = .ok geometryRowsTyped033.jensenBound :=
  original_rational_fraction_of_chars geometryRow033_jensenBoundNumeratorChars geometryRow033_jensenBoundDenominatorChars
    (89138249750870231830764511450964784628758973532143575820523870907067953263033862671593621004726413535664204878556299227576182574299369622976796988067485511835951850096845395273554329600000000000000000 : Int) (101486715471279977672420338841201577386268337936301124418311119660988213947309237619616592347672387649753777324865672039534023210708845986859719842203716306911764917148565291973690804812532009723600889145601241039 : Int)
    geometryRow033_jensenBound_numerator_no_slash geometryRow033_jensenBound_numerator_parse
    geometryRow033_jensenBound_denominator_parse geometryRow033_jensenBound_denominator_nonzero

theorem geometryRow033_jensenBound_read :
    rationalField geometryRowsJson033 "jensen_bound" = .ok geometryRowsTyped033.jensenBound :=
  original_rationalField_of_string geometryRowsJson033 "jensen_bound" geometryRow033_jensenBoundText
    geometryRowsTyped033.jensenBound geometryRow033_jensenBound_field geometryRow033_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_factorMaxima_before"
  err.flush

theorem geometryRow033_factorMaxima_read :
    rationalArrayField geometryRowsJson033 "factor_maxima" = .ok geometryRowsTyped033.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_gapWeightedMeans_before"
  err.flush

theorem geometryRow033_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson033 "gap_weighted_means" = .ok geometryRowsTyped033.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow033_floorChars : List Char := ['6', '9', '5', '8', '8', '0', '2', '1', '4', '9', '3', '2', '9', '1', '8', '8', '6']
noncomputable def geometryRow033_floorText : String := String.ofList geometryRow033_floorChars

theorem geometryRow033_floor_text_read :
    geometryRowsJson033.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow033_floorText := by rfl

theorem geometryRow033_floor_chars_parse :
    SourceJson.intChars geometryRow033_floorChars = some (69588021493291886 : Int) := by decide +kernel

theorem geometryRow033_floor_parse :
    parseInteger geometryRow033_floorText = .ok geometryRowsTyped033.jensenFloorQ96 := by
  simp only [geometryRow033_floorText, parseInteger, String.toList_ofList, geometryRow033_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_033 :
    decodeGeometryRow geometryRowsJson033 = .ok geometryRowsTyped033 :=
  original_geometryRow_of_fields geometryRowsJson033 geometryRowsTyped033 geometryRow033_floorText
    geometryRow033_simplexId_read geometryRow033_vertexIds_read
    geometryRow033_physicalVolume_read geometryRow033_meanGap_read
    geometryRow033_factorMaxima_read geometryRow033_gapWeightedMeans_read
    geometryRow033_jensenBound_read geometryRow033_floor_text_read geometryRow033_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_033_original_decoder_complete"
  err.flush

theorem geometryRow033_shape :
    geometryRowsTyped033.simplexId = 33 ∧
    geometryRowsTyped033.vertexIds.size = 9 ∧ geometryRowsTyped033.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped033.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped033.factorMaxima.size = 10 ∧ geometryRowsTyped033.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson034 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped034 : GeometryRow :=
  { simplexId := 34,
    vertexIds := #[32, 30, 20, 16, 14, 13, 10, 8, 0],
    physicalVolume := ((10533405679490809274178660683866629783020661139 : ℚ) / (8821010614284288000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((7625972305219 : ℚ) / (85433040000000 : ℚ)), ((38694061710587 : ℚ) / (427165200000000 : ℚ)), ((12940663942427 : ℚ) / (111434400000000 : ℚ)), ((225242972331911 : ℚ) / (2562991200000000 : ℚ)), ((221514379598507 : ℚ) / (2562991200000000 : ℚ)), ((3524032940501 : ℚ) / (46599840000000 : ℚ)), ((127212624677 : ℚ) / (3328560000000 : ℚ)), ((844985265521 : ℚ) / (23299920000000 : ℚ)), ((819641917841 : ℚ) / (23299920000000 : ℚ)), ((39583913270107 : ℚ) / (1281495600000000 : ℚ))],
    jensenBound := ((10103627822113807797220248905523239536907161273453293612405585639469500684553742507553830100401730355200000000000000000 : ℚ) / (2341593327280500642526064585280991430444150479443444461764766110708351575981487417672277578973816564586290588948605018874007107773 : ℚ)),
    jensenFloorQ96 := (341857767421876536 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_simplexId_before"
  err.flush

theorem geometryRow034_simplexId_read :
    geometryRowsJson034.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped034.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_vertexIds_before"
  err.flush

theorem geometryRow034_vertexIds_read :
    geometryRowsJson034.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped034.vertexIds := by decide +kernel

noncomputable def geometryRow034_physicalVolumeNumeratorChars : List Char := ['1', '0', '5', '3', '3', '4', '0', '5', '6', '7', '9', '4', '9', '0', '8', '0', '9', '2', '7', '4', '1', '7', '8', '6', '6', '0', '6', '8', '3', '8', '6', '6', '6', '2', '9', '7', '8', '3', '0', '2', '0', '6', '6', '1', '1', '3', '9']
noncomputable def geometryRow034_physicalVolumeDenominatorChars : List Char := ['8', '8', '2', '1', '0', '1', '0', '6', '1', '4', '2', '8', '4', '2', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_physicalVolumeText : String := String.ofList (geometryRow034_physicalVolumeNumeratorChars ++ '/' :: geometryRow034_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_physicalVolume_before_field"
  err.flush

theorem geometryRow034_physicalVolume_field :
    geometryRowsJson034.getObjVal? "physical_volume" = .ok (.str geometryRow034_physicalVolumeText) := by rfl

theorem geometryRow034_physicalVolume_numerator_no_slash :
    geometryRow034_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeNumeratorChars = some (10533405679490809274178660683866629783020661139 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow034_physicalVolumeDenominatorChars = some (8821010614284288000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow034_physicalVolume_denominator_nonzero : (8821010614284288000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_physicalVolume_parse :
    parseRational geometryRow034_physicalVolumeText = .ok geometryRowsTyped034.physicalVolume :=
  original_rational_fraction_of_chars geometryRow034_physicalVolumeNumeratorChars geometryRow034_physicalVolumeDenominatorChars
    (10533405679490809274178660683866629783020661139 : Int) (8821010614284288000000000000000000000000000000000000000000000000000 : Int)
    geometryRow034_physicalVolume_numerator_no_slash geometryRow034_physicalVolume_numerator_parse
    geometryRow034_physicalVolume_denominator_parse geometryRow034_physicalVolume_denominator_nonzero

theorem geometryRow034_physicalVolume_read :
    rationalField geometryRowsJson034 "physical_volume" = .ok geometryRowsTyped034.physicalVolume :=
  original_rationalField_of_string geometryRowsJson034 "physical_volume" geometryRow034_physicalVolumeText
    geometryRowsTyped034.physicalVolume geometryRow034_physicalVolume_field geometryRow034_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_physicalVolume_complete"
  err.flush

noncomputable def geometryRow034_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow034_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_meanGapText : String := String.ofList (geometryRow034_meanGapNumeratorChars ++ '/' :: geometryRow034_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_meanGap_before_field"
  err.flush

theorem geometryRow034_meanGap_field :
    geometryRowsJson034.getObjVal? "mean_gap" = .ok (.str geometryRow034_meanGapText) := by rfl

theorem geometryRow034_meanGap_numerator_no_slash :
    geometryRow034_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_meanGap_numerator_parse :
    SourceJson.intChars geometryRow034_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_parse :
    SourceJson.intChars geometryRow034_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow034_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_meanGap_parse :
    parseRational geometryRow034_meanGapText = .ok geometryRowsTyped034.meanGap :=
  original_rational_fraction_of_chars geometryRow034_meanGapNumeratorChars geometryRow034_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow034_meanGap_numerator_no_slash geometryRow034_meanGap_numerator_parse
    geometryRow034_meanGap_denominator_parse geometryRow034_meanGap_denominator_nonzero

theorem geometryRow034_meanGap_read :
    rationalField geometryRowsJson034 "mean_gap" = .ok geometryRowsTyped034.meanGap :=
  original_rationalField_of_string geometryRowsJson034 "mean_gap" geometryRow034_meanGapText
    geometryRowsTyped034.meanGap geometryRow034_meanGap_field geometryRow034_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_meanGap_complete"
  err.flush

noncomputable def geometryRow034_jensenBoundNumeratorChars : List Char := ['1', '0', '1', '0', '3', '6', '2', '7', '8', '2', '2', '1', '1', '3', '8', '0', '7', '7', '9', '7', '2', '2', '0', '2', '4', '8', '9', '0', '5', '5', '2', '3', '2', '3', '9', '5', '3', '6', '9', '0', '7', '1', '6', '1', '2', '7', '3', '4', '5', '3', '2', '9', '3', '6', '1', '2', '4', '0', '5', '5', '8', '5', '6', '3', '9', '4', '6', '9', '5', '0', '0', '6', '8', '4', '5', '5', '3', '7', '4', '2', '5', '0', '7', '5', '5', '3', '8', '3', '0', '1', '0', '0', '4', '0', '1', '7', '3', '0', '3', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow034_jensenBoundDenominatorChars : List Char := ['2', '3', '4', '1', '5', '9', '3', '3', '2', '7', '2', '8', '0', '5', '0', '0', '6', '4', '2', '5', '2', '6', '0', '6', '4', '5', '8', '5', '2', '8', '0', '9', '9', '1', '4', '3', '0', '4', '4', '4', '1', '5', '0', '4', '7', '9', '4', '4', '3', '4', '4', '4', '4', '6', '1', '7', '6', '4', '7', '6', '6', '1', '1', '0', '7', '0', '8', '3', '5', '1', '5', '7', '5', '9', '8', '1', '4', '8', '7', '4', '1', '7', '6', '7', '2', '2', '7', '7', '5', '7', '8', '9', '7', '3', '8', '1', '6', '5', '6', '4', '5', '8', '6', '2', '9', '0', '5', '8', '8', '9', '4', '8', '6', '0', '5', '0', '1', '8', '8', '7', '4', '0', '0', '7', '1', '0', '7', '7', '7', '3']
noncomputable def geometryRow034_jensenBoundText : String := String.ofList (geometryRow034_jensenBoundNumeratorChars ++ '/' :: geometryRow034_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_jensenBound_before_field"
  err.flush

theorem geometryRow034_jensenBound_field :
    geometryRowsJson034.getObjVal? "jensen_bound" = .ok (.str geometryRow034_jensenBoundText) := by rfl

theorem geometryRow034_jensenBound_numerator_no_slash :
    geometryRow034_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow034_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow034_jensenBoundNumeratorChars = some (10103627822113807797220248905523239536907161273453293612405585639469500684553742507553830100401730355200000000000000000 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow034_jensenBoundDenominatorChars = some (2341593327280500642526064585280991430444150479443444461764766110708351575981487417672277578973816564586290588948605018874007107773 : Int) := by decide +kernel

theorem geometryRow034_jensenBound_denominator_nonzero : (2341593327280500642526064585280991430444150479443444461764766110708351575981487417672277578973816564586290588948605018874007107773 : Int) ≠ 0 := by decide +kernel

theorem geometryRow034_jensenBound_parse :
    parseRational geometryRow034_jensenBoundText = .ok geometryRowsTyped034.jensenBound :=
  original_rational_fraction_of_chars geometryRow034_jensenBoundNumeratorChars geometryRow034_jensenBoundDenominatorChars
    (10103627822113807797220248905523239536907161273453293612405585639469500684553742507553830100401730355200000000000000000 : Int) (2341593327280500642526064585280991430444150479443444461764766110708351575981487417672277578973816564586290588948605018874007107773 : Int)
    geometryRow034_jensenBound_numerator_no_slash geometryRow034_jensenBound_numerator_parse
    geometryRow034_jensenBound_denominator_parse geometryRow034_jensenBound_denominator_nonzero

theorem geometryRow034_jensenBound_read :
    rationalField geometryRowsJson034 "jensen_bound" = .ok geometryRowsTyped034.jensenBound :=
  original_rationalField_of_string geometryRowsJson034 "jensen_bound" geometryRow034_jensenBoundText
    geometryRowsTyped034.jensenBound geometryRow034_jensenBound_field geometryRow034_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_factorMaxima_before"
  err.flush

theorem geometryRow034_factorMaxima_read :
    rationalArrayField geometryRowsJson034 "factor_maxima" = .ok geometryRowsTyped034.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_gapWeightedMeans_before"
  err.flush

theorem geometryRow034_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson034 "gap_weighted_means" = .ok geometryRowsTyped034.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow034_floorChars : List Char := ['3', '4', '1', '8', '5', '7', '7', '6', '7', '4', '2', '1', '8', '7', '6', '5', '3', '6']
noncomputable def geometryRow034_floorText : String := String.ofList geometryRow034_floorChars

theorem geometryRow034_floor_text_read :
    geometryRowsJson034.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow034_floorText := by rfl

theorem geometryRow034_floor_chars_parse :
    SourceJson.intChars geometryRow034_floorChars = some (341857767421876536 : Int) := by decide +kernel

theorem geometryRow034_floor_parse :
    parseInteger geometryRow034_floorText = .ok geometryRowsTyped034.jensenFloorQ96 := by
  simp only [geometryRow034_floorText, parseInteger, String.toList_ofList, geometryRow034_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_034 :
    decodeGeometryRow geometryRowsJson034 = .ok geometryRowsTyped034 :=
  original_geometryRow_of_fields geometryRowsJson034 geometryRowsTyped034 geometryRow034_floorText
    geometryRow034_simplexId_read geometryRow034_vertexIds_read
    geometryRow034_physicalVolume_read geometryRow034_meanGap_read
    geometryRow034_factorMaxima_read geometryRow034_gapWeightedMeans_read
    geometryRow034_jensenBound_read geometryRow034_floor_text_read geometryRow034_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_034_original_decoder_complete"
  err.flush

theorem geometryRow034_shape :
    geometryRowsTyped034.simplexId = 34 ∧
    geometryRowsTyped034.vertexIds.size = 9 ∧ geometryRowsTyped034.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped034.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped034.factorMaxima.size = 10 ∧ geometryRowsTyped034.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson035 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped035 : GeometryRow :=
  { simplexId := 35,
    vertexIds := #[32, 30, 20, 19, 16, 14, 12, 11, 7],
    physicalVolume := ((10875085420154409146761903909141640838340927 : ℚ) / (14964438859776000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((182269 : ℚ) / (264000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((1421823 : ℚ) / (28000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((78514457954837 : ℚ) / (854330400000000 : ℚ)), ((79576171234457 : ℚ) / (854330400000000 : ℚ)), ((99840319553539 : ℚ) / (854330400000000 : ℚ)), ((1871170749727 : ℚ) / (21358260000000 : ℚ)), ((8113335937869 : ℚ) / (94925600000000 : ℚ)), ((64547329205501 : ℚ) / (854330400000000 : ℚ)), ((1165044618121 : ℚ) / (30511800000000 : ℚ)), ((3869105340641 : ℚ) / (106791300000000 : ℚ)), ((27897347418727 : ℚ) / (854330400000000 : ℚ)), ((3013180531611 : ℚ) / (94925600000000 : ℚ))],
    jensenBound := ((63644983942414103650270967401131054874371009382568147244063844561808610961216261703201328537776520000000000000000000000 : ℚ) / (25735254087341519220410088045907529921717452217679637063159305648957805129446471584055680735896359848761343335533115795230433161869 : ℚ)),
    jensenFloorQ96 := (195936481291147887 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_simplexId_before"
  err.flush

theorem geometryRow035_simplexId_read :
    geometryRowsJson035.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped035.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_vertexIds_before"
  err.flush

theorem geometryRow035_vertexIds_read :
    geometryRowsJson035.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped035.vertexIds := by decide +kernel

noncomputable def geometryRow035_physicalVolumeNumeratorChars : List Char := ['1', '0', '8', '7', '5', '0', '8', '5', '4', '2', '0', '1', '5', '4', '4', '0', '9', '1', '4', '6', '7', '6', '1', '9', '0', '3', '9', '0', '9', '1', '4', '1', '6', '4', '0', '8', '3', '8', '3', '4', '0', '9', '2', '7']
noncomputable def geometryRow035_physicalVolumeDenominatorChars : List Char := ['1', '4', '9', '6', '4', '4', '3', '8', '8', '5', '9', '7', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_physicalVolumeText : String := String.ofList (geometryRow035_physicalVolumeNumeratorChars ++ '/' :: geometryRow035_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_physicalVolume_before_field"
  err.flush

theorem geometryRow035_physicalVolume_field :
    geometryRowsJson035.getObjVal? "physical_volume" = .ok (.str geometryRow035_physicalVolumeText) := by rfl

theorem geometryRow035_physicalVolume_numerator_no_slash :
    geometryRow035_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeNumeratorChars = some (10875085420154409146761903909141640838340927 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow035_physicalVolumeDenominatorChars = some (14964438859776000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_physicalVolume_denominator_nonzero : (14964438859776000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_physicalVolume_parse :
    parseRational geometryRow035_physicalVolumeText = .ok geometryRowsTyped035.physicalVolume :=
  original_rational_fraction_of_chars geometryRow035_physicalVolumeNumeratorChars geometryRow035_physicalVolumeDenominatorChars
    (10875085420154409146761903909141640838340927 : Int) (14964438859776000000000000000000000000000000000000000000000000000 : Int)
    geometryRow035_physicalVolume_numerator_no_slash geometryRow035_physicalVolume_numerator_parse
    geometryRow035_physicalVolume_denominator_parse geometryRow035_physicalVolume_denominator_nonzero

theorem geometryRow035_physicalVolume_read :
    rationalField geometryRowsJson035 "physical_volume" = .ok geometryRowsTyped035.physicalVolume :=
  original_rationalField_of_string geometryRowsJson035 "physical_volume" geometryRow035_physicalVolumeText
    geometryRowsTyped035.physicalVolume geometryRow035_physicalVolume_field geometryRow035_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_physicalVolume_complete"
  err.flush

noncomputable def geometryRow035_meanGapNumeratorChars : List Char := ['1', '8', '2', '2', '6', '9']
noncomputable def geometryRow035_meanGapDenominatorChars : List Char := ['2', '6', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_meanGapText : String := String.ofList (geometryRow035_meanGapNumeratorChars ++ '/' :: geometryRow035_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_meanGap_before_field"
  err.flush

theorem geometryRow035_meanGap_field :
    geometryRowsJson035.getObjVal? "mean_gap" = .ok (.str geometryRow035_meanGapText) := by rfl

theorem geometryRow035_meanGap_numerator_no_slash :
    geometryRow035_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_meanGap_numerator_parse :
    SourceJson.intChars geometryRow035_meanGapNumeratorChars = some (182269 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_parse :
    SourceJson.intChars geometryRow035_meanGapDenominatorChars = some (264000000 : Int) := by decide +kernel

theorem geometryRow035_meanGap_denominator_nonzero : (264000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_meanGap_parse :
    parseRational geometryRow035_meanGapText = .ok geometryRowsTyped035.meanGap :=
  original_rational_fraction_of_chars geometryRow035_meanGapNumeratorChars geometryRow035_meanGapDenominatorChars
    (182269 : Int) (264000000 : Int)
    geometryRow035_meanGap_numerator_no_slash geometryRow035_meanGap_numerator_parse
    geometryRow035_meanGap_denominator_parse geometryRow035_meanGap_denominator_nonzero

theorem geometryRow035_meanGap_read :
    rationalField geometryRowsJson035 "mean_gap" = .ok geometryRowsTyped035.meanGap :=
  original_rationalField_of_string geometryRowsJson035 "mean_gap" geometryRow035_meanGapText
    geometryRowsTyped035.meanGap geometryRow035_meanGap_field geometryRow035_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_meanGap_complete"
  err.flush

noncomputable def geometryRow035_jensenBoundNumeratorChars : List Char := ['6', '3', '6', '4', '4', '9', '8', '3', '9', '4', '2', '4', '1', '4', '1', '0', '3', '6', '5', '0', '2', '7', '0', '9', '6', '7', '4', '0', '1', '1', '3', '1', '0', '5', '4', '8', '7', '4', '3', '7', '1', '0', '0', '9', '3', '8', '2', '5', '6', '8', '1', '4', '7', '2', '4', '4', '0', '6', '3', '8', '4', '4', '5', '6', '1', '8', '0', '8', '6', '1', '0', '9', '6', '1', '2', '1', '6', '2', '6', '1', '7', '0', '3', '2', '0', '1', '3', '2', '8', '5', '3', '7', '7', '7', '6', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow035_jensenBoundDenominatorChars : List Char := ['2', '5', '7', '3', '5', '2', '5', '4', '0', '8', '7', '3', '4', '1', '5', '1', '9', '2', '2', '0', '4', '1', '0', '0', '8', '8', '0', '4', '5', '9', '0', '7', '5', '2', '9', '9', '2', '1', '7', '1', '7', '4', '5', '2', '2', '1', '7', '6', '7', '9', '6', '3', '7', '0', '6', '3', '1', '5', '9', '3', '0', '5', '6', '4', '8', '9', '5', '7', '8', '0', '5', '1', '2', '9', '4', '4', '6', '4', '7', '1', '5', '8', '4', '0', '5', '5', '6', '8', '0', '7', '3', '5', '8', '9', '6', '3', '5', '9', '8', '4', '8', '7', '6', '1', '3', '4', '3', '3', '3', '5', '5', '3', '3', '1', '1', '5', '7', '9', '5', '2', '3', '0', '4', '3', '3', '1', '6', '1', '8', '6', '9']
noncomputable def geometryRow035_jensenBoundText : String := String.ofList (geometryRow035_jensenBoundNumeratorChars ++ '/' :: geometryRow035_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_jensenBound_before_field"
  err.flush

theorem geometryRow035_jensenBound_field :
    geometryRowsJson035.getObjVal? "jensen_bound" = .ok (.str geometryRow035_jensenBoundText) := by rfl

theorem geometryRow035_jensenBound_numerator_no_slash :
    geometryRow035_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow035_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow035_jensenBoundNumeratorChars = some (63644983942414103650270967401131054874371009382568147244063844561808610961216261703201328537776520000000000000000000000 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow035_jensenBoundDenominatorChars = some (25735254087341519220410088045907529921717452217679637063159305648957805129446471584055680735896359848761343335533115795230433161869 : Int) := by decide +kernel

theorem geometryRow035_jensenBound_denominator_nonzero : (25735254087341519220410088045907529921717452217679637063159305648957805129446471584055680735896359848761343335533115795230433161869 : Int) ≠ 0 := by decide +kernel

theorem geometryRow035_jensenBound_parse :
    parseRational geometryRow035_jensenBoundText = .ok geometryRowsTyped035.jensenBound :=
  original_rational_fraction_of_chars geometryRow035_jensenBoundNumeratorChars geometryRow035_jensenBoundDenominatorChars
    (63644983942414103650270967401131054874371009382568147244063844561808610961216261703201328537776520000000000000000000000 : Int) (25735254087341519220410088045907529921717452217679637063159305648957805129446471584055680735896359848761343335533115795230433161869 : Int)
    geometryRow035_jensenBound_numerator_no_slash geometryRow035_jensenBound_numerator_parse
    geometryRow035_jensenBound_denominator_parse geometryRow035_jensenBound_denominator_nonzero

theorem geometryRow035_jensenBound_read :
    rationalField geometryRowsJson035 "jensen_bound" = .ok geometryRowsTyped035.jensenBound :=
  original_rationalField_of_string geometryRowsJson035 "jensen_bound" geometryRow035_jensenBoundText
    geometryRowsTyped035.jensenBound geometryRow035_jensenBound_field geometryRow035_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_factorMaxima_before"
  err.flush

theorem geometryRow035_factorMaxima_read :
    rationalArrayField geometryRowsJson035 "factor_maxima" = .ok geometryRowsTyped035.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_gapWeightedMeans_before"
  err.flush

theorem geometryRow035_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson035 "gap_weighted_means" = .ok geometryRowsTyped035.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow035_floorChars : List Char := ['1', '9', '5', '9', '3', '6', '4', '8', '1', '2', '9', '1', '1', '4', '7', '8', '8', '7']
noncomputable def geometryRow035_floorText : String := String.ofList geometryRow035_floorChars

theorem geometryRow035_floor_text_read :
    geometryRowsJson035.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow035_floorText := by rfl

theorem geometryRow035_floor_chars_parse :
    SourceJson.intChars geometryRow035_floorChars = some (195936481291147887 : Int) := by decide +kernel

theorem geometryRow035_floor_parse :
    parseInteger geometryRow035_floorText = .ok geometryRowsTyped035.jensenFloorQ96 := by
  simp only [geometryRow035_floorText, parseInteger, String.toList_ofList, geometryRow035_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_035 :
    decodeGeometryRow geometryRowsJson035 = .ok geometryRowsTyped035 :=
  original_geometryRow_of_fields geometryRowsJson035 geometryRowsTyped035 geometryRow035_floorText
    geometryRow035_simplexId_read geometryRow035_vertexIds_read
    geometryRow035_physicalVolume_read geometryRow035_meanGap_read
    geometryRow035_factorMaxima_read geometryRow035_gapWeightedMeans_read
    geometryRow035_jensenBound_read geometryRow035_floor_text_read geometryRow035_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_035_original_decoder_complete"
  err.flush

theorem geometryRow035_shape :
    geometryRowsTyped035.simplexId = 35 ∧
    geometryRowsTyped035.vertexIds.size = 9 ∧ geometryRowsTyped035.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped035.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped035.factorMaxima.size = 10 ∧ geometryRowsTyped035.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson036 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped036 : GeometryRow :=
  { simplexId := 36,
    vertexIds := #[32, 30, 28, 16, 4, 3, 2, 1, 0],
    physicalVolume := ((3180982131253511573806070825585185075280599 : ℚ) / (13089980265991372800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((474804774133 : ℚ) / (127937040000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((7328233 : ℚ) / (196000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((9987709236995379785617703 : ℚ) / (113897095088333599350000000 : ℚ)), ((11936275178924045669238301 : ℚ) / (130168108672381256400000000 : ℚ)), ((42061085284282003639016171 : ℚ) / (364470704282667517920000000 : ℚ)), ((18661116418376549917195881 : ℚ) / (202483724601481954400000000 : ℚ)), ((55653251483644113805091963 : ℚ) / (607451173804445863200000000 : ℚ)), ((11899227548811541792241023 : ℚ) / (165668501946667053600000000 : ℚ)), ((2894536387984368635643577 : ℚ) / (82834250973333526800000000 : ℚ)), ((2877880566888684789653167 : ℚ) / (82834250973333526800000000 : ℚ)), ((2813815462407306456103657 : ℚ) / (82834250973333526800000000 : ℚ)), ((4069145199220358658171647 : ℚ) / (130168108672381256400000000 : ℚ))],
    jensenBound := ((1088411186142265811145727447342794034922731880263422299833863830555653296137559524042346053734614694148783411758928331099473195889328717018590108709134084610473305019053265265358737032079033147688646119548215047040000000000000000000000 : ℚ) / (218901600484532500042171357802648004260434785073385249034698525597452078705139407171487343535956762937199761727542421562037596512309342890377548739577513016874787996352989699920607740207374917793721684120761161087724439546941826628364718775910632271 : ℚ)),
    jensenFloorQ96 := (393934161043814 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_simplexId_before"
  err.flush

theorem geometryRow036_simplexId_read :
    geometryRowsJson036.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped036.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_vertexIds_before"
  err.flush

theorem geometryRow036_vertexIds_read :
    geometryRowsJson036.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped036.vertexIds := by decide +kernel

noncomputable def geometryRow036_physicalVolumeNumeratorChars : List Char := ['3', '1', '8', '0', '9', '8', '2', '1', '3', '1', '2', '5', '3', '5', '1', '1', '5', '7', '3', '8', '0', '6', '0', '7', '0', '8', '2', '5', '5', '8', '5', '1', '8', '5', '0', '7', '5', '2', '8', '0', '5', '9', '9']
noncomputable def geometryRow036_physicalVolumeDenominatorChars : List Char := ['1', '3', '0', '8', '9', '9', '8', '0', '2', '6', '5', '9', '9', '1', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_physicalVolumeText : String := String.ofList (geometryRow036_physicalVolumeNumeratorChars ++ '/' :: geometryRow036_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_physicalVolume_before_field"
  err.flush

theorem geometryRow036_physicalVolume_field :
    geometryRowsJson036.getObjVal? "physical_volume" = .ok (.str geometryRow036_physicalVolumeText) := by rfl

theorem geometryRow036_physicalVolume_numerator_no_slash :
    geometryRow036_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeNumeratorChars = some (3180982131253511573806070825585185075280599 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow036_physicalVolumeDenominatorChars = some (13089980265991372800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_physicalVolume_denominator_nonzero : (13089980265991372800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_physicalVolume_parse :
    parseRational geometryRow036_physicalVolumeText = .ok geometryRowsTyped036.physicalVolume :=
  original_rational_fraction_of_chars geometryRow036_physicalVolumeNumeratorChars geometryRow036_physicalVolumeDenominatorChars
    (3180982131253511573806070825585185075280599 : Int) (13089980265991372800000000000000000000000000000000000000000000000000 : Int)
    geometryRow036_physicalVolume_numerator_no_slash geometryRow036_physicalVolume_numerator_parse
    geometryRow036_physicalVolume_denominator_parse geometryRow036_physicalVolume_denominator_nonzero

theorem geometryRow036_physicalVolume_read :
    rationalField geometryRowsJson036 "physical_volume" = .ok geometryRowsTyped036.physicalVolume :=
  original_rationalField_of_string geometryRowsJson036 "physical_volume" geometryRow036_physicalVolumeText
    geometryRowsTyped036.physicalVolume geometryRow036_physicalVolume_field geometryRow036_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_physicalVolume_complete"
  err.flush

noncomputable def geometryRow036_meanGapNumeratorChars : List Char := ['4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3']
noncomputable def geometryRow036_meanGapDenominatorChars : List Char := ['1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_meanGapText : String := String.ofList (geometryRow036_meanGapNumeratorChars ++ '/' :: geometryRow036_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_meanGap_before_field"
  err.flush

theorem geometryRow036_meanGap_field :
    geometryRowsJson036.getObjVal? "mean_gap" = .ok (.str geometryRow036_meanGapText) := by rfl

theorem geometryRow036_meanGap_numerator_no_slash :
    geometryRow036_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_meanGap_numerator_parse :
    SourceJson.intChars geometryRow036_meanGapNumeratorChars = some (474804774133 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_parse :
    SourceJson.intChars geometryRow036_meanGapDenominatorChars = some (127937040000000 : Int) := by decide +kernel

theorem geometryRow036_meanGap_denominator_nonzero : (127937040000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_meanGap_parse :
    parseRational geometryRow036_meanGapText = .ok geometryRowsTyped036.meanGap :=
  original_rational_fraction_of_chars geometryRow036_meanGapNumeratorChars geometryRow036_meanGapDenominatorChars
    (474804774133 : Int) (127937040000000 : Int)
    geometryRow036_meanGap_numerator_no_slash geometryRow036_meanGap_numerator_parse
    geometryRow036_meanGap_denominator_parse geometryRow036_meanGap_denominator_nonzero

theorem geometryRow036_meanGap_read :
    rationalField geometryRowsJson036 "mean_gap" = .ok geometryRowsTyped036.meanGap :=
  original_rationalField_of_string geometryRowsJson036 "mean_gap" geometryRow036_meanGapText
    geometryRowsTyped036.meanGap geometryRow036_meanGap_field geometryRow036_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_meanGap_complete"
  err.flush

noncomputable def geometryRow036_jensenBoundNumeratorChars : List Char := ['1', '0', '8', '8', '4', '1', '1', '1', '8', '6', '1', '4', '2', '2', '6', '5', '8', '1', '1', '1', '4', '5', '7', '2', '7', '4', '4', '7', '3', '4', '2', '7', '9', '4', '0', '3', '4', '9', '2', '2', '7', '3', '1', '8', '8', '0', '2', '6', '3', '4', '2', '2', '2', '9', '9', '8', '3', '3', '8', '6', '3', '8', '3', '0', '5', '5', '5', '6', '5', '3', '2', '9', '6', '1', '3', '7', '5', '5', '9', '5', '2', '4', '0', '4', '2', '3', '4', '6', '0', '5', '3', '7', '3', '4', '6', '1', '4', '6', '9', '4', '1', '4', '8', '7', '8', '3', '4', '1', '1', '7', '5', '8', '9', '2', '8', '3', '3', '1', '0', '9', '9', '4', '7', '3', '1', '9', '5', '8', '8', '9', '3', '2', '8', '7', '1', '7', '0', '1', '8', '5', '9', '0', '1', '0', '8', '7', '0', '9', '1', '3', '4', '0', '8', '4', '6', '1', '0', '4', '7', '3', '3', '0', '5', '0', '1', '9', '0', '5', '3', '2', '6', '5', '2', '6', '5', '3', '5', '8', '7', '3', '7', '0', '3', '2', '0', '7', '9', '0', '3', '3', '1', '4', '7', '6', '8', '8', '6', '4', '6', '1', '1', '9', '5', '4', '8', '2', '1', '5', '0', '4', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow036_jensenBoundDenominatorChars : List Char := ['2', '1', '8', '9', '0', '1', '6', '0', '0', '4', '8', '4', '5', '3', '2', '5', '0', '0', '0', '4', '2', '1', '7', '1', '3', '5', '7', '8', '0', '2', '6', '4', '8', '0', '0', '4', '2', '6', '0', '4', '3', '4', '7', '8', '5', '0', '7', '3', '3', '8', '5', '2', '4', '9', '0', '3', '4', '6', '9', '8', '5', '2', '5', '5', '9', '7', '4', '5', '2', '0', '7', '8', '7', '0', '5', '1', '3', '9', '4', '0', '7', '1', '7', '1', '4', '8', '7', '3', '4', '3', '5', '3', '5', '9', '5', '6', '7', '6', '2', '9', '3', '7', '1', '9', '9', '7', '6', '1', '7', '2', '7', '5', '4', '2', '4', '2', '1', '5', '6', '2', '0', '3', '7', '5', '9', '6', '5', '1', '2', '3', '0', '9', '3', '4', '2', '8', '9', '0', '3', '7', '7', '5', '4', '8', '7', '3', '9', '5', '7', '7', '5', '1', '3', '0', '1', '6', '8', '7', '4', '7', '8', '7', '9', '9', '6', '3', '5', '2', '9', '8', '9', '6', '9', '9', '9', '2', '0', '6', '0', '7', '7', '4', '0', '2', '0', '7', '3', '7', '4', '9', '1', '7', '7', '9', '3', '7', '2', '1', '6', '8', '4', '1', '2', '0', '7', '6', '1', '1', '6', '1', '0', '8', '7', '7', '2', '4', '4', '3', '9', '5', '4', '6', '9', '4', '1', '8', '2', '6', '6', '2', '8', '3', '6', '4', '7', '1', '8', '7', '7', '5', '9', '1', '0', '6', '3', '2', '2', '7', '1']
noncomputable def geometryRow036_jensenBoundText : String := String.ofList (geometryRow036_jensenBoundNumeratorChars ++ '/' :: geometryRow036_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_jensenBound_before_field"
  err.flush

theorem geometryRow036_jensenBound_field :
    geometryRowsJson036.getObjVal? "jensen_bound" = .ok (.str geometryRow036_jensenBoundText) := by rfl

theorem geometryRow036_jensenBound_numerator_no_slash :
    geometryRow036_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow036_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow036_jensenBoundNumeratorChars = some (1088411186142265811145727447342794034922731880263422299833863830555653296137559524042346053734614694148783411758928331099473195889328717018590108709134084610473305019053265265358737032079033147688646119548215047040000000000000000000000 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow036_jensenBoundDenominatorChars = some (218901600484532500042171357802648004260434785073385249034698525597452078705139407171487343535956762937199761727542421562037596512309342890377548739577513016874787996352989699920607740207374917793721684120761161087724439546941826628364718775910632271 : Int) := by decide +kernel

theorem geometryRow036_jensenBound_denominator_nonzero : (218901600484532500042171357802648004260434785073385249034698525597452078705139407171487343535956762937199761727542421562037596512309342890377548739577513016874787996352989699920607740207374917793721684120761161087724439546941826628364718775910632271 : Int) ≠ 0 := by decide +kernel

theorem geometryRow036_jensenBound_parse :
    parseRational geometryRow036_jensenBoundText = .ok geometryRowsTyped036.jensenBound :=
  original_rational_fraction_of_chars geometryRow036_jensenBoundNumeratorChars geometryRow036_jensenBoundDenominatorChars
    (1088411186142265811145727447342794034922731880263422299833863830555653296137559524042346053734614694148783411758928331099473195889328717018590108709134084610473305019053265265358737032079033147688646119548215047040000000000000000000000 : Int) (218901600484532500042171357802648004260434785073385249034698525597452078705139407171487343535956762937199761727542421562037596512309342890377548739577513016874787996352989699920607740207374917793721684120761161087724439546941826628364718775910632271 : Int)
    geometryRow036_jensenBound_numerator_no_slash geometryRow036_jensenBound_numerator_parse
    geometryRow036_jensenBound_denominator_parse geometryRow036_jensenBound_denominator_nonzero

theorem geometryRow036_jensenBound_read :
    rationalField geometryRowsJson036 "jensen_bound" = .ok geometryRowsTyped036.jensenBound :=
  original_rationalField_of_string geometryRowsJson036 "jensen_bound" geometryRow036_jensenBoundText
    geometryRowsTyped036.jensenBound geometryRow036_jensenBound_field geometryRow036_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_factorMaxima_before"
  err.flush

theorem geometryRow036_factorMaxima_read :
    rationalArrayField geometryRowsJson036 "factor_maxima" = .ok geometryRowsTyped036.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_gapWeightedMeans_before"
  err.flush

theorem geometryRow036_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson036 "gap_weighted_means" = .ok geometryRowsTyped036.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow036_floorChars : List Char := ['3', '9', '3', '9', '3', '4', '1', '6', '1', '0', '4', '3', '8', '1', '4']
noncomputable def geometryRow036_floorText : String := String.ofList geometryRow036_floorChars

theorem geometryRow036_floor_text_read :
    geometryRowsJson036.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow036_floorText := by rfl

theorem geometryRow036_floor_chars_parse :
    SourceJson.intChars geometryRow036_floorChars = some (393934161043814 : Int) := by decide +kernel

theorem geometryRow036_floor_parse :
    parseInteger geometryRow036_floorText = .ok geometryRowsTyped036.jensenFloorQ96 := by
  simp only [geometryRow036_floorText, parseInteger, String.toList_ofList, geometryRow036_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_036 :
    decodeGeometryRow geometryRowsJson036 = .ok geometryRowsTyped036 :=
  original_geometryRow_of_fields geometryRowsJson036 geometryRowsTyped036 geometryRow036_floorText
    geometryRow036_simplexId_read geometryRow036_vertexIds_read
    geometryRow036_physicalVolume_read geometryRow036_meanGap_read
    geometryRow036_factorMaxima_read geometryRow036_gapWeightedMeans_read
    geometryRow036_jensenBound_read geometryRow036_floor_text_read geometryRow036_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_036_original_decoder_complete"
  err.flush

theorem geometryRow036_shape :
    geometryRowsTyped036.simplexId = 36 ∧
    geometryRowsTyped036.vertexIds.size = 9 ∧ geometryRowsTyped036.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped036.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped036.factorMaxima.size = 10 ∧ geometryRowsTyped036.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson037 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped037 : GeometryRow :=
  { simplexId := 37,
    vertexIds := #[32, 30, 28, 16, 15, 4, 2, 1, 0],
    physicalVolume := ((5813586879971965124688658772080426433 : ℚ) / (68494082787164160000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1133902280579 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((7328233 : ℚ) / (196000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((193997068111137095620993337 : ℚ) / (2176021521397901192400000000 : ℚ)), ((334268338142645967713683 : ℚ) / (3614653690029736200000000 : ℚ)), ((2804396799386394225584623 : ℚ) / (24178016904421124360000000 : ℚ)), ((99138748297448021221286363 : ℚ) / (1088010760698950596200000000 : ℚ)), ((98547507481812317279621483 : ℚ) / (1088010760698950596200000000 : ℚ)), ((398968035522440628337067 : ℚ) / (5495003841913891900000000 : ℚ)), ((429840115584803861979781 : ℚ) / (12363758644306256775000000 : ℚ)), ((3417981823220869527785333 : ℚ) / (98910069154450054200000000 : ℚ)), ((3364212876149247370350413 : ℚ) / (98910069154450054200000000 : ℚ)), ((113932741352813600577601 : ℚ) / (3614653690029736200000000 : ℚ))],
    jensenBound := ((771679599553164333707178740016334599600886544480140035220941613739803157878275108187547984688524093668269101012213837941325279364082275996615471851699901996044889664402420391785098188338474171300961316932812500000000000000000 : ℚ) / (567819670570182323380686536746038892648360090298036208397137833743926157169083922458356459531945152174711302592041729824613634794128815362194719866326540439149683271317419535517545980180134957346425218040791600938047761603957757751128105549877 : ℚ)),
    jensenFloorQ96 := (107672840324 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_simplexId_before"
  err.flush

theorem geometryRow037_simplexId_read :
    geometryRowsJson037.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped037.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_vertexIds_before"
  err.flush

theorem geometryRow037_vertexIds_read :
    geometryRowsJson037.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped037.vertexIds := by decide +kernel

noncomputable def geometryRow037_physicalVolumeNumeratorChars : List Char := ['5', '8', '1', '3', '5', '8', '6', '8', '7', '9', '9', '7', '1', '9', '6', '5', '1', '2', '4', '6', '8', '8', '6', '5', '8', '7', '7', '2', '0', '8', '0', '4', '2', '6', '4', '3', '3']
noncomputable def geometryRow037_physicalVolumeDenominatorChars : List Char := ['6', '8', '4', '9', '4', '0', '8', '2', '7', '8', '7', '1', '6', '4', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_physicalVolumeText : String := String.ofList (geometryRow037_physicalVolumeNumeratorChars ++ '/' :: geometryRow037_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_physicalVolume_before_field"
  err.flush

theorem geometryRow037_physicalVolume_field :
    geometryRowsJson037.getObjVal? "physical_volume" = .ok (.str geometryRow037_physicalVolumeText) := by rfl

theorem geometryRow037_physicalVolume_numerator_no_slash :
    geometryRow037_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeNumeratorChars = some (5813586879971965124688658772080426433 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow037_physicalVolumeDenominatorChars = some (68494082787164160000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow037_physicalVolume_denominator_nonzero : (68494082787164160000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_physicalVolume_parse :
    parseRational geometryRow037_physicalVolumeText = .ok geometryRowsTyped037.physicalVolume :=
  original_rational_fraction_of_chars geometryRow037_physicalVolumeNumeratorChars geometryRow037_physicalVolumeDenominatorChars
    (5813586879971965124688658772080426433 : Int) (68494082787164160000000000000000000000000000000000000000000000000 : Int)
    geometryRow037_physicalVolume_numerator_no_slash geometryRow037_physicalVolume_numerator_parse
    geometryRow037_physicalVolume_denominator_parse geometryRow037_physicalVolume_denominator_nonzero

theorem geometryRow037_physicalVolume_read :
    rationalField geometryRowsJson037 "physical_volume" = .ok geometryRowsTyped037.physicalVolume :=
  original_rationalField_of_string geometryRowsJson037 "physical_volume" geometryRow037_physicalVolumeText
    geometryRowsTyped037.physicalVolume geometryRow037_physicalVolume_field geometryRow037_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_physicalVolume_complete"
  err.flush

noncomputable def geometryRow037_meanGapNumeratorChars : List Char := ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9']
noncomputable def geometryRow037_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_meanGapText : String := String.ofList (geometryRow037_meanGapNumeratorChars ++ '/' :: geometryRow037_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_meanGap_before_field"
  err.flush

theorem geometryRow037_meanGap_field :
    geometryRowsJson037.getObjVal? "mean_gap" = .ok (.str geometryRow037_meanGapText) := by rfl

theorem geometryRow037_meanGap_numerator_no_slash :
    geometryRow037_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_meanGap_numerator_parse :
    SourceJson.intChars geometryRow037_meanGapNumeratorChars = some (1133902280579 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_parse :
    SourceJson.intChars geometryRow037_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow037_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_meanGap_parse :
    parseRational geometryRow037_meanGapText = .ok geometryRowsTyped037.meanGap :=
  original_rational_fraction_of_chars geometryRow037_meanGapNumeratorChars geometryRow037_meanGapDenominatorChars
    (1133902280579 : Int) (383811120000000 : Int)
    geometryRow037_meanGap_numerator_no_slash geometryRow037_meanGap_numerator_parse
    geometryRow037_meanGap_denominator_parse geometryRow037_meanGap_denominator_nonzero

theorem geometryRow037_meanGap_read :
    rationalField geometryRowsJson037 "mean_gap" = .ok geometryRowsTyped037.meanGap :=
  original_rationalField_of_string geometryRowsJson037 "mean_gap" geometryRow037_meanGapText
    geometryRowsTyped037.meanGap geometryRow037_meanGap_field geometryRow037_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_meanGap_complete"
  err.flush

noncomputable def geometryRow037_jensenBoundNumeratorChars : List Char := ['7', '7', '1', '6', '7', '9', '5', '9', '9', '5', '5', '3', '1', '6', '4', '3', '3', '3', '7', '0', '7', '1', '7', '8', '7', '4', '0', '0', '1', '6', '3', '3', '4', '5', '9', '9', '6', '0', '0', '8', '8', '6', '5', '4', '4', '4', '8', '0', '1', '4', '0', '0', '3', '5', '2', '2', '0', '9', '4', '1', '6', '1', '3', '7', '3', '9', '8', '0', '3', '1', '5', '7', '8', '7', '8', '2', '7', '5', '1', '0', '8', '1', '8', '7', '5', '4', '7', '9', '8', '4', '6', '8', '8', '5', '2', '4', '0', '9', '3', '6', '6', '8', '2', '6', '9', '1', '0', '1', '0', '1', '2', '2', '1', '3', '8', '3', '7', '9', '4', '1', '3', '2', '5', '2', '7', '9', '3', '6', '4', '0', '8', '2', '2', '7', '5', '9', '9', '6', '6', '1', '5', '4', '7', '1', '8', '5', '1', '6', '9', '9', '9', '0', '1', '9', '9', '6', '0', '4', '4', '8', '8', '9', '6', '6', '4', '4', '0', '2', '4', '2', '0', '3', '9', '1', '7', '8', '5', '0', '9', '8', '1', '8', '8', '3', '3', '8', '4', '7', '4', '1', '7', '1', '3', '0', '0', '9', '6', '1', '3', '1', '6', '9', '3', '2', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow037_jensenBoundDenominatorChars : List Char := ['5', '6', '7', '8', '1', '9', '6', '7', '0', '5', '7', '0', '1', '8', '2', '3', '2', '3', '3', '8', '0', '6', '8', '6', '5', '3', '6', '7', '4', '6', '0', '3', '8', '8', '9', '2', '6', '4', '8', '3', '6', '0', '0', '9', '0', '2', '9', '8', '0', '3', '6', '2', '0', '8', '3', '9', '7', '1', '3', '7', '8', '3', '3', '7', '4', '3', '9', '2', '6', '1', '5', '7', '1', '6', '9', '0', '8', '3', '9', '2', '2', '4', '5', '8', '3', '5', '6', '4', '5', '9', '5', '3', '1', '9', '4', '5', '1', '5', '2', '1', '7', '4', '7', '1', '1', '3', '0', '2', '5', '9', '2', '0', '4', '1', '7', '2', '9', '8', '2', '4', '6', '1', '3', '6', '3', '4', '7', '9', '4', '1', '2', '8', '8', '1', '5', '3', '6', '2', '1', '9', '4', '7', '1', '9', '8', '6', '6', '3', '2', '6', '5', '4', '0', '4', '3', '9', '1', '4', '9', '6', '8', '3', '2', '7', '1', '3', '1', '7', '4', '1', '9', '5', '3', '5', '5', '1', '7', '5', '4', '5', '9', '8', '0', '1', '8', '0', '1', '3', '4', '9', '5', '7', '3', '4', '6', '4', '2', '5', '2', '1', '8', '0', '4', '0', '7', '9', '1', '6', '0', '0', '9', '3', '8', '0', '4', '7', '7', '6', '1', '6', '0', '3', '9', '5', '7', '7', '5', '7', '7', '5', '1', '1', '2', '8', '1', '0', '5', '5', '4', '9', '8', '7', '7']
noncomputable def geometryRow037_jensenBoundText : String := String.ofList (geometryRow037_jensenBoundNumeratorChars ++ '/' :: geometryRow037_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_jensenBound_before_field"
  err.flush

theorem geometryRow037_jensenBound_field :
    geometryRowsJson037.getObjVal? "jensen_bound" = .ok (.str geometryRow037_jensenBoundText) := by rfl

theorem geometryRow037_jensenBound_numerator_no_slash :
    geometryRow037_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow037_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow037_jensenBoundNumeratorChars = some (771679599553164333707178740016334599600886544480140035220941613739803157878275108187547984688524093668269101012213837941325279364082275996615471851699901996044889664402420391785098188338474171300961316932812500000000000000000 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow037_jensenBoundDenominatorChars = some (567819670570182323380686536746038892648360090298036208397137833743926157169083922458356459531945152174711302592041729824613634794128815362194719866326540439149683271317419535517545980180134957346425218040791600938047761603957757751128105549877 : Int) := by decide +kernel

theorem geometryRow037_jensenBound_denominator_nonzero : (567819670570182323380686536746038892648360090298036208397137833743926157169083922458356459531945152174711302592041729824613634794128815362194719866326540439149683271317419535517545980180134957346425218040791600938047761603957757751128105549877 : Int) ≠ 0 := by decide +kernel

theorem geometryRow037_jensenBound_parse :
    parseRational geometryRow037_jensenBoundText = .ok geometryRowsTyped037.jensenBound :=
  original_rational_fraction_of_chars geometryRow037_jensenBoundNumeratorChars geometryRow037_jensenBoundDenominatorChars
    (771679599553164333707178740016334599600886544480140035220941613739803157878275108187547984688524093668269101012213837941325279364082275996615471851699901996044889664402420391785098188338474171300961316932812500000000000000000 : Int) (567819670570182323380686536746038892648360090298036208397137833743926157169083922458356459531945152174711302592041729824613634794128815362194719866326540439149683271317419535517545980180134957346425218040791600938047761603957757751128105549877 : Int)
    geometryRow037_jensenBound_numerator_no_slash geometryRow037_jensenBound_numerator_parse
    geometryRow037_jensenBound_denominator_parse geometryRow037_jensenBound_denominator_nonzero

theorem geometryRow037_jensenBound_read :
    rationalField geometryRowsJson037 "jensen_bound" = .ok geometryRowsTyped037.jensenBound :=
  original_rationalField_of_string geometryRowsJson037 "jensen_bound" geometryRow037_jensenBoundText
    geometryRowsTyped037.jensenBound geometryRow037_jensenBound_field geometryRow037_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_factorMaxima_before"
  err.flush

theorem geometryRow037_factorMaxima_read :
    rationalArrayField geometryRowsJson037 "factor_maxima" = .ok geometryRowsTyped037.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_gapWeightedMeans_before"
  err.flush

theorem geometryRow037_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson037 "gap_weighted_means" = .ok geometryRowsTyped037.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow037_floorChars : List Char := ['1', '0', '7', '6', '7', '2', '8', '4', '0', '3', '2', '4']
noncomputable def geometryRow037_floorText : String := String.ofList geometryRow037_floorChars

theorem geometryRow037_floor_text_read :
    geometryRowsJson037.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow037_floorText := by rfl

theorem geometryRow037_floor_chars_parse :
    SourceJson.intChars geometryRow037_floorChars = some (107672840324 : Int) := by decide +kernel

theorem geometryRow037_floor_parse :
    parseInteger geometryRow037_floorText = .ok geometryRowsTyped037.jensenFloorQ96 := by
  simp only [geometryRow037_floorText, parseInteger, String.toList_ofList, geometryRow037_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_037 :
    decodeGeometryRow geometryRowsJson037 = .ok geometryRowsTyped037 :=
  original_geometryRow_of_fields geometryRowsJson037 geometryRowsTyped037 geometryRow037_floorText
    geometryRow037_simplexId_read geometryRow037_vertexIds_read
    geometryRow037_physicalVolume_read geometryRow037_meanGap_read
    geometryRow037_factorMaxima_read geometryRow037_gapWeightedMeans_read
    geometryRow037_jensenBound_read geometryRow037_floor_text_read geometryRow037_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_037_original_decoder_complete"
  err.flush

theorem geometryRow037_shape :
    geometryRowsTyped037.simplexId = 37 ∧
    geometryRowsTyped037.vertexIds.size = 9 ∧ geometryRowsTyped037.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped037.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped037.factorMaxima.size = 10 ∧ geometryRowsTyped037.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson038 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped038 : GeometryRow :=
  { simplexId := 38,
    vertexIds := #[32, 30, 28, 16, 15, 13, 4, 1, 0],
    physicalVolume := ((57550239386493918039818362489367801513 : ℚ) / (74915403048460800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((395859770604107247225149 : ℚ) / (4411974114029859300000000 : ℚ)), ((21155032913987743193 : ℚ) / (229026895454207812500 : ℚ)), ((1986619884125523708043 : ℚ) / (17051107687071920000000 : ℚ)), ((1593924633548225729275153 : ℚ) / (17647896456119437200000000 : ℚ)), ((1584334510847355121021873 : ℚ) / (17647896456119437200000000 : ℚ)), ((13000313896186983707909 : ℚ) / (178261580364842800000000 : ℚ)), ((28068651870812943910469 : ℚ) / (802177111641792600000000 : ℚ)), ((13944471301722124612237 : ℚ) / (401088555820896300000000 : ℚ)), ((13726433749900264790857 : ℚ) / (401088555820896300000000 : ℚ)), ((57685684169666180293 : ℚ) / (1832215163633662500000 : ℚ))],
    jensenBound := ((1531985429267992073729155675832392119989288818197711344372160653609236548906846562070473005901941328989835668732569092494853931226870733634009117671837725522373310156728556128589101637812500000000000000000 : ℚ) / (169273014589557125371173234286037193789495802222305287850602088399625699952716040885254729335945003441012131997454812814337216465111404728493841019211379669993561239151044823538354787464173197904896625453880300788706020263 : ℚ)),
    jensenFloorQ96 := (717045128863 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_simplexId_before"
  err.flush

theorem geometryRow038_simplexId_read :
    geometryRowsJson038.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped038.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_vertexIds_before"
  err.flush

theorem geometryRow038_vertexIds_read :
    geometryRowsJson038.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped038.vertexIds := by decide +kernel

noncomputable def geometryRow038_physicalVolumeNumeratorChars : List Char := ['5', '7', '5', '5', '0', '2', '3', '9', '3', '8', '6', '4', '9', '3', '9', '1', '8', '0', '3', '9', '8', '1', '8', '3', '6', '2', '4', '8', '9', '3', '6', '7', '8', '0', '1', '5', '1', '3']
noncomputable def geometryRow038_physicalVolumeDenominatorChars : List Char := ['7', '4', '9', '1', '5', '4', '0', '3', '0', '4', '8', '4', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_physicalVolumeText : String := String.ofList (geometryRow038_physicalVolumeNumeratorChars ++ '/' :: geometryRow038_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_physicalVolume_before_field"
  err.flush

theorem geometryRow038_physicalVolume_field :
    geometryRowsJson038.getObjVal? "physical_volume" = .ok (.str geometryRow038_physicalVolumeText) := by rfl

theorem geometryRow038_physicalVolume_numerator_no_slash :
    geometryRow038_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeNumeratorChars = some (57550239386493918039818362489367801513 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow038_physicalVolumeDenominatorChars = some (74915403048460800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow038_physicalVolume_denominator_nonzero : (74915403048460800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_physicalVolume_parse :
    parseRational geometryRow038_physicalVolumeText = .ok geometryRowsTyped038.physicalVolume :=
  original_rational_fraction_of_chars geometryRow038_physicalVolumeNumeratorChars geometryRow038_physicalVolumeDenominatorChars
    (57550239386493918039818362489367801513 : Int) (74915403048460800000000000000000000000000000000000000000000000000 : Int)
    geometryRow038_physicalVolume_numerator_no_slash geometryRow038_physicalVolume_numerator_parse
    geometryRow038_physicalVolume_denominator_parse geometryRow038_physicalVolume_denominator_nonzero

theorem geometryRow038_physicalVolume_read :
    rationalField geometryRowsJson038 "physical_volume" = .ok geometryRowsTyped038.physicalVolume :=
  original_rationalField_of_string geometryRowsJson038 "physical_volume" geometryRow038_physicalVolumeText
    geometryRowsTyped038.physicalVolume geometryRow038_physicalVolume_field geometryRow038_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_physicalVolume_complete"
  err.flush

noncomputable def geometryRow038_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow038_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_meanGapText : String := String.ofList (geometryRow038_meanGapNumeratorChars ++ '/' :: geometryRow038_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_meanGap_before_field"
  err.flush

theorem geometryRow038_meanGap_field :
    geometryRowsJson038.getObjVal? "mean_gap" = .ok (.str geometryRow038_meanGapText) := by rfl

theorem geometryRow038_meanGap_numerator_no_slash :
    geometryRow038_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_meanGap_numerator_parse :
    SourceJson.intChars geometryRow038_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_parse :
    SourceJson.intChars geometryRow038_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow038_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_meanGap_parse :
    parseRational geometryRow038_meanGapText = .ok geometryRowsTyped038.meanGap :=
  original_rational_fraction_of_chars geometryRow038_meanGapNumeratorChars geometryRow038_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow038_meanGap_numerator_no_slash geometryRow038_meanGap_numerator_parse
    geometryRow038_meanGap_denominator_parse geometryRow038_meanGap_denominator_nonzero

theorem geometryRow038_meanGap_read :
    rationalField geometryRowsJson038 "mean_gap" = .ok geometryRowsTyped038.meanGap :=
  original_rationalField_of_string geometryRowsJson038 "mean_gap" geometryRow038_meanGapText
    geometryRowsTyped038.meanGap geometryRow038_meanGap_field geometryRow038_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_meanGap_complete"
  err.flush

noncomputable def geometryRow038_jensenBoundNumeratorChars : List Char := ['1', '5', '3', '1', '9', '8', '5', '4', '2', '9', '2', '6', '7', '9', '9', '2', '0', '7', '3', '7', '2', '9', '1', '5', '5', '6', '7', '5', '8', '3', '2', '3', '9', '2', '1', '1', '9', '9', '8', '9', '2', '8', '8', '8', '1', '8', '1', '9', '7', '7', '1', '1', '3', '4', '4', '3', '7', '2', '1', '6', '0', '6', '5', '3', '6', '0', '9', '2', '3', '6', '5', '4', '8', '9', '0', '6', '8', '4', '6', '5', '6', '2', '0', '7', '0', '4', '7', '3', '0', '0', '5', '9', '0', '1', '9', '4', '1', '3', '2', '8', '9', '8', '9', '8', '3', '5', '6', '6', '8', '7', '3', '2', '5', '6', '9', '0', '9', '2', '4', '9', '4', '8', '5', '3', '9', '3', '1', '2', '2', '6', '8', '7', '0', '7', '3', '3', '6', '3', '4', '0', '0', '9', '1', '1', '7', '6', '7', '1', '8', '3', '7', '7', '2', '5', '5', '2', '2', '3', '7', '3', '3', '1', '0', '1', '5', '6', '7', '2', '8', '5', '5', '6', '1', '2', '8', '5', '8', '9', '1', '0', '1', '6', '3', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow038_jensenBoundDenominatorChars : List Char := ['1', '6', '9', '2', '7', '3', '0', '1', '4', '5', '8', '9', '5', '5', '7', '1', '2', '5', '3', '7', '1', '1', '7', '3', '2', '3', '4', '2', '8', '6', '0', '3', '7', '1', '9', '3', '7', '8', '9', '4', '9', '5', '8', '0', '2', '2', '2', '2', '3', '0', '5', '2', '8', '7', '8', '5', '0', '6', '0', '2', '0', '8', '8', '3', '9', '9', '6', '2', '5', '6', '9', '9', '9', '5', '2', '7', '1', '6', '0', '4', '0', '8', '8', '5', '2', '5', '4', '7', '2', '9', '3', '3', '5', '9', '4', '5', '0', '0', '3', '4', '4', '1', '0', '1', '2', '1', '3', '1', '9', '9', '7', '4', '5', '4', '8', '1', '2', '8', '1', '4', '3', '3', '7', '2', '1', '6', '4', '6', '5', '1', '1', '1', '4', '0', '4', '7', '2', '8', '4', '9', '3', '8', '4', '1', '0', '1', '9', '2', '1', '1', '3', '7', '9', '6', '6', '9', '9', '9', '3', '5', '6', '1', '2', '3', '9', '1', '5', '1', '0', '4', '4', '8', '2', '3', '5', '3', '8', '3', '5', '4', '7', '8', '7', '4', '6', '4', '1', '7', '3', '1', '9', '7', '9', '0', '4', '8', '9', '6', '6', '2', '5', '4', '5', '3', '8', '8', '0', '3', '0', '0', '7', '8', '8', '7', '0', '6', '0', '2', '0', '2', '6', '3']
noncomputable def geometryRow038_jensenBoundText : String := String.ofList (geometryRow038_jensenBoundNumeratorChars ++ '/' :: geometryRow038_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_jensenBound_before_field"
  err.flush

theorem geometryRow038_jensenBound_field :
    geometryRowsJson038.getObjVal? "jensen_bound" = .ok (.str geometryRow038_jensenBoundText) := by rfl

theorem geometryRow038_jensenBound_numerator_no_slash :
    geometryRow038_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow038_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow038_jensenBoundNumeratorChars = some (1531985429267992073729155675832392119989288818197711344372160653609236548906846562070473005901941328989835668732569092494853931226870733634009117671837725522373310156728556128589101637812500000000000000000 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow038_jensenBoundDenominatorChars = some (169273014589557125371173234286037193789495802222305287850602088399625699952716040885254729335945003441012131997454812814337216465111404728493841019211379669993561239151044823538354787464173197904896625453880300788706020263 : Int) := by decide +kernel

theorem geometryRow038_jensenBound_denominator_nonzero : (169273014589557125371173234286037193789495802222305287850602088399625699952716040885254729335945003441012131997454812814337216465111404728493841019211379669993561239151044823538354787464173197904896625453880300788706020263 : Int) ≠ 0 := by decide +kernel

theorem geometryRow038_jensenBound_parse :
    parseRational geometryRow038_jensenBoundText = .ok geometryRowsTyped038.jensenBound :=
  original_rational_fraction_of_chars geometryRow038_jensenBoundNumeratorChars geometryRow038_jensenBoundDenominatorChars
    (1531985429267992073729155675832392119989288818197711344372160653609236548906846562070473005901941328989835668732569092494853931226870733634009117671837725522373310156728556128589101637812500000000000000000 : Int) (169273014589557125371173234286037193789495802222305287850602088399625699952716040885254729335945003441012131997454812814337216465111404728493841019211379669993561239151044823538354787464173197904896625453880300788706020263 : Int)
    geometryRow038_jensenBound_numerator_no_slash geometryRow038_jensenBound_numerator_parse
    geometryRow038_jensenBound_denominator_parse geometryRow038_jensenBound_denominator_nonzero

theorem geometryRow038_jensenBound_read :
    rationalField geometryRowsJson038 "jensen_bound" = .ok geometryRowsTyped038.jensenBound :=
  original_rationalField_of_string geometryRowsJson038 "jensen_bound" geometryRow038_jensenBoundText
    geometryRowsTyped038.jensenBound geometryRow038_jensenBound_field geometryRow038_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_factorMaxima_before"
  err.flush

theorem geometryRow038_factorMaxima_read :
    rationalArrayField geometryRowsJson038 "factor_maxima" = .ok geometryRowsTyped038.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_gapWeightedMeans_before"
  err.flush

theorem geometryRow038_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson038 "gap_weighted_means" = .ok geometryRowsTyped038.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow038_floorChars : List Char := ['7', '1', '7', '0', '4', '5', '1', '2', '8', '8', '6', '3']
noncomputable def geometryRow038_floorText : String := String.ofList geometryRow038_floorChars

theorem geometryRow038_floor_text_read :
    geometryRowsJson038.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow038_floorText := by rfl

theorem geometryRow038_floor_chars_parse :
    SourceJson.intChars geometryRow038_floorChars = some (717045128863 : Int) := by decide +kernel

theorem geometryRow038_floor_parse :
    parseInteger geometryRow038_floorText = .ok geometryRowsTyped038.jensenFloorQ96 := by
  simp only [geometryRow038_floorText, parseInteger, String.toList_ofList, geometryRow038_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_038 :
    decodeGeometryRow geometryRowsJson038 = .ok geometryRowsTyped038 :=
  original_geometryRow_of_fields geometryRowsJson038 geometryRowsTyped038 geometryRow038_floorText
    geometryRow038_simplexId_read geometryRow038_vertexIds_read
    geometryRow038_physicalVolume_read geometryRow038_meanGap_read
    geometryRow038_factorMaxima_read geometryRow038_gapWeightedMeans_read
    geometryRow038_jensenBound_read geometryRow038_floor_text_read geometryRow038_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_038_original_decoder_complete"
  err.flush

theorem geometryRow038_shape :
    geometryRowsTyped038.simplexId = 38 ∧
    geometryRowsTyped038.vertexIds.size = 9 ∧ geometryRowsTyped038.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped038.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped038.factorMaxima.size = 10 ∧ geometryRowsTyped038.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson039 : SourceJson :=
  (SimplicesBlock004.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped039 : GeometryRow :=
  { simplexId := 39,
    vertexIds := #[32, 30, 28, 16, 15, 13, 10, 1, 0],
    physicalVolume := ((95858788477123238058600472615908790079 : ℚ) / (10453312053273600000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((828113 : ℚ) / (24000000 : ℚ))],
    gapWeightedMeans := #[((144528396879303582661 : ℚ) / (1599591184121700000000 : ℚ)), ((2637847871113391303 : ℚ) / (28564128287887500000 : ℚ)), ((2168539241636486203 : ℚ) / (18545984743440000000 : ℚ)), ((572285268926203726907 : ℚ) / (6398364736486800000000 : ℚ)), ((568808304798473082587 : ℚ) / (6398364736486800000000 : ℚ)), ((14325254417436671593 : ℚ) / (193889840499600000000 : ℚ)), ((2650852732805500219 : ℚ) / (72708690187350000000 : ℚ)), ((4981096089239502293 : ℚ) / (145417380374700000000 : ℚ)), ((4902045093769549073 : ℚ) / (145417380374700000000 : ℚ)), ((224779282803825479 : ℚ) / (7141032071971875000 : ℚ))],
    jensenBound := ((4002943738170186324301675654431057653293635136343713510072543216037006631150668539180903925944252975283727967965330574779644959826632229535271834368385992421875000000000000000 : ℚ) / (56091255377185326391644153796930199424884277674828499168384406112887380784318398076418149033445594328616054974508419025737435387637771866296021377495933037285750767690314772033588628825972257 : ℚ)),
    jensenFloorQ96 := (5654105526620 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_simplexId_before"
  err.flush

theorem geometryRow039_simplexId_read :
    geometryRowsJson039.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped039.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_vertexIds_before"
  err.flush

theorem geometryRow039_vertexIds_read :
    geometryRowsJson039.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped039.vertexIds := by decide +kernel

noncomputable def geometryRow039_physicalVolumeNumeratorChars : List Char := ['9', '5', '8', '5', '8', '7', '8', '8', '4', '7', '7', '1', '2', '3', '2', '3', '8', '0', '5', '8', '6', '0', '0', '4', '7', '2', '6', '1', '5', '9', '0', '8', '7', '9', '0', '0', '7', '9']
noncomputable def geometryRow039_physicalVolumeDenominatorChars : List Char := ['1', '0', '4', '5', '3', '3', '1', '2', '0', '5', '3', '2', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_physicalVolumeText : String := String.ofList (geometryRow039_physicalVolumeNumeratorChars ++ '/' :: geometryRow039_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_physicalVolume_before_field"
  err.flush

theorem geometryRow039_physicalVolume_field :
    geometryRowsJson039.getObjVal? "physical_volume" = .ok (.str geometryRow039_physicalVolumeText) := by rfl

theorem geometryRow039_physicalVolume_numerator_no_slash :
    geometryRow039_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeNumeratorChars = some (95858788477123238058600472615908790079 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow039_physicalVolumeDenominatorChars = some (10453312053273600000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow039_physicalVolume_denominator_nonzero : (10453312053273600000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_physicalVolume_parse :
    parseRational geometryRow039_physicalVolumeText = .ok geometryRowsTyped039.physicalVolume :=
  original_rational_fraction_of_chars geometryRow039_physicalVolumeNumeratorChars geometryRow039_physicalVolumeDenominatorChars
    (95858788477123238058600472615908790079 : Int) (10453312053273600000000000000000000000000000000000000000000000000 : Int)
    geometryRow039_physicalVolume_numerator_no_slash geometryRow039_physicalVolume_numerator_parse
    geometryRow039_physicalVolume_denominator_parse geometryRow039_physicalVolume_denominator_nonzero

theorem geometryRow039_physicalVolume_read :
    rationalField geometryRowsJson039 "physical_volume" = .ok geometryRowsTyped039.physicalVolume :=
  original_rationalField_of_string geometryRowsJson039 "physical_volume" geometryRow039_physicalVolumeText
    geometryRowsTyped039.physicalVolume geometryRow039_physicalVolume_field geometryRow039_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_physicalVolume_complete"
  err.flush

noncomputable def geometryRow039_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow039_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_meanGapText : String := String.ofList (geometryRow039_meanGapNumeratorChars ++ '/' :: geometryRow039_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_meanGap_before_field"
  err.flush

theorem geometryRow039_meanGap_field :
    geometryRowsJson039.getObjVal? "mean_gap" = .ok (.str geometryRow039_meanGapText) := by rfl

theorem geometryRow039_meanGap_numerator_no_slash :
    geometryRow039_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_meanGap_numerator_parse :
    SourceJson.intChars geometryRow039_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_parse :
    SourceJson.intChars geometryRow039_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow039_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_meanGap_parse :
    parseRational geometryRow039_meanGapText = .ok geometryRowsTyped039.meanGap :=
  original_rational_fraction_of_chars geometryRow039_meanGapNumeratorChars geometryRow039_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow039_meanGap_numerator_no_slash geometryRow039_meanGap_numerator_parse
    geometryRow039_meanGap_denominator_parse geometryRow039_meanGap_denominator_nonzero

theorem geometryRow039_meanGap_read :
    rationalField geometryRowsJson039 "mean_gap" = .ok geometryRowsTyped039.meanGap :=
  original_rationalField_of_string geometryRowsJson039 "mean_gap" geometryRow039_meanGapText
    geometryRowsTyped039.meanGap geometryRow039_meanGap_field geometryRow039_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_meanGap_complete"
  err.flush

noncomputable def geometryRow039_jensenBoundNumeratorChars : List Char := ['4', '0', '0', '2', '9', '4', '3', '7', '3', '8', '1', '7', '0', '1', '8', '6', '3', '2', '4', '3', '0', '1', '6', '7', '5', '6', '5', '4', '4', '3', '1', '0', '5', '7', '6', '5', '3', '2', '9', '3', '6', '3', '5', '1', '3', '6', '3', '4', '3', '7', '1', '3', '5', '1', '0', '0', '7', '2', '5', '4', '3', '2', '1', '6', '0', '3', '7', '0', '0', '6', '6', '3', '1', '1', '5', '0', '6', '6', '8', '5', '3', '9', '1', '8', '0', '9', '0', '3', '9', '2', '5', '9', '4', '4', '2', '5', '2', '9', '7', '5', '2', '8', '3', '7', '2', '7', '9', '6', '7', '9', '6', '5', '3', '3', '0', '5', '7', '4', '7', '7', '9', '6', '4', '4', '9', '5', '9', '8', '2', '6', '6', '3', '2', '2', '2', '9', '5', '3', '5', '2', '7', '1', '8', '3', '4', '3', '6', '8', '3', '8', '5', '9', '9', '2', '4', '2', '1', '8', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow039_jensenBoundDenominatorChars : List Char := ['5', '6', '0', '9', '1', '2', '5', '5', '3', '7', '7', '1', '8', '5', '3', '2', '6', '3', '9', '1', '6', '4', '4', '1', '5', '3', '7', '9', '6', '9', '3', '0', '1', '9', '9', '4', '2', '4', '8', '8', '4', '2', '7', '7', '6', '7', '4', '8', '2', '8', '4', '9', '9', '1', '6', '8', '3', '8', '4', '4', '0', '6', '1', '1', '2', '8', '8', '7', '3', '8', '0', '7', '8', '4', '3', '1', '8', '3', '9', '8', '0', '7', '6', '4', '1', '8', '1', '4', '9', '0', '3', '3', '4', '4', '5', '5', '9', '4', '3', '2', '8', '6', '1', '6', '0', '5', '4', '9', '7', '4', '5', '0', '8', '4', '1', '9', '0', '2', '5', '7', '3', '7', '4', '3', '5', '3', '8', '7', '6', '3', '7', '7', '7', '1', '8', '6', '6', '2', '9', '6', '0', '2', '1', '3', '7', '7', '4', '9', '5', '9', '3', '3', '0', '3', '7', '2', '8', '5', '7', '5', '0', '7', '6', '7', '6', '9', '0', '3', '1', '4', '7', '7', '2', '0', '3', '3', '5', '8', '8', '6', '2', '8', '8', '2', '5', '9', '7', '2', '2', '5', '7']
noncomputable def geometryRow039_jensenBoundText : String := String.ofList (geometryRow039_jensenBoundNumeratorChars ++ '/' :: geometryRow039_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_jensenBound_before_field"
  err.flush

theorem geometryRow039_jensenBound_field :
    geometryRowsJson039.getObjVal? "jensen_bound" = .ok (.str geometryRow039_jensenBoundText) := by rfl

theorem geometryRow039_jensenBound_numerator_no_slash :
    geometryRow039_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow039_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow039_jensenBoundNumeratorChars = some (4002943738170186324301675654431057653293635136343713510072543216037006631150668539180903925944252975283727967965330574779644959826632229535271834368385992421875000000000000000 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow039_jensenBoundDenominatorChars = some (56091255377185326391644153796930199424884277674828499168384406112887380784318398076418149033445594328616054974508419025737435387637771866296021377495933037285750767690314772033588628825972257 : Int) := by decide +kernel

theorem geometryRow039_jensenBound_denominator_nonzero : (56091255377185326391644153796930199424884277674828499168384406112887380784318398076418149033445594328616054974508419025737435387637771866296021377495933037285750767690314772033588628825972257 : Int) ≠ 0 := by decide +kernel

theorem geometryRow039_jensenBound_parse :
    parseRational geometryRow039_jensenBoundText = .ok geometryRowsTyped039.jensenBound :=
  original_rational_fraction_of_chars geometryRow039_jensenBoundNumeratorChars geometryRow039_jensenBoundDenominatorChars
    (4002943738170186324301675654431057653293635136343713510072543216037006631150668539180903925944252975283727967965330574779644959826632229535271834368385992421875000000000000000 : Int) (56091255377185326391644153796930199424884277674828499168384406112887380784318398076418149033445594328616054974508419025737435387637771866296021377495933037285750767690314772033588628825972257 : Int)
    geometryRow039_jensenBound_numerator_no_slash geometryRow039_jensenBound_numerator_parse
    geometryRow039_jensenBound_denominator_parse geometryRow039_jensenBound_denominator_nonzero

theorem geometryRow039_jensenBound_read :
    rationalField geometryRowsJson039 "jensen_bound" = .ok geometryRowsTyped039.jensenBound :=
  original_rationalField_of_string geometryRowsJson039 "jensen_bound" geometryRow039_jensenBoundText
    geometryRowsTyped039.jensenBound geometryRow039_jensenBound_field geometryRow039_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_factorMaxima_before"
  err.flush

theorem geometryRow039_factorMaxima_read :
    rationalArrayField geometryRowsJson039 "factor_maxima" = .ok geometryRowsTyped039.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_gapWeightedMeans_before"
  err.flush

theorem geometryRow039_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson039 "gap_weighted_means" = .ok geometryRowsTyped039.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow039_floorChars : List Char := ['5', '6', '5', '4', '1', '0', '5', '5', '2', '6', '6', '2', '0']
noncomputable def geometryRow039_floorText : String := String.ofList geometryRow039_floorChars

theorem geometryRow039_floor_text_read :
    geometryRowsJson039.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow039_floorText := by rfl

theorem geometryRow039_floor_chars_parse :
    SourceJson.intChars geometryRow039_floorChars = some (5654105526620 : Int) := by decide +kernel

theorem geometryRow039_floor_parse :
    parseInteger geometryRow039_floorText = .ok geometryRowsTyped039.jensenFloorQ96 := by
  simp only [geometryRow039_floorText, parseInteger, String.toList_ofList, geometryRow039_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_039 :
    decodeGeometryRow geometryRowsJson039 = .ok geometryRowsTyped039 :=
  original_geometryRow_of_fields geometryRowsJson039 geometryRowsTyped039 geometryRow039_floorText
    geometryRow039_simplexId_read geometryRow039_vertexIds_read
    geometryRow039_physicalVolume_read geometryRow039_meanGap_read
    geometryRow039_factorMaxima_read geometryRow039_gapWeightedMeans_read
    geometryRow039_jensenBound_read geometryRow039_floor_text_read geometryRow039_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_039_original_decoder_complete"
  err.flush

theorem geometryRow039_shape :
    geometryRowsTyped039.simplexId = 39 ∧
    geometryRowsTyped039.vertexIds.size = 9 ∧ geometryRowsTyped039.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped039.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped039.factorMaxima.size = 10 ∧ geometryRowsTyped039.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock004 : List SourceJson := [geometryRowsJson032, geometryRowsJson033, geometryRowsJson034, geometryRowsJson035, geometryRowsJson036, geometryRowsJson037, geometryRowsJson038, geometryRowsJson039]
noncomputable def geometryRowsTypedBlock004 : List GeometryRow := [geometryRowsTyped032, geometryRowsTyped033, geometryRowsTyped034, geometryRowsTyped035, geometryRowsTyped036, geometryRowsTyped037, geometryRowsTyped038, geometryRowsTyped039]

theorem geometry_Rows_block_004_push_eq (acc : List SourceJson) :
    SimplicesBlock004.blockPush acc = [geometryRowsJson039, geometryRowsJson038, geometryRowsJson037, geometryRowsJson036, geometryRowsJson035, geometryRowsJson034, geometryRowsJson033, geometryRowsJson032] ++ acc := by rfl

theorem geometry_Rows_block_004_reverse (acc : List SourceJson) :
    (SimplicesBlock004.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock004 := by
  rw [geometry_Rows_block_004_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_004 :
    geometryRowsJsonBlock004.mapM decodeGeometryRow = .ok geometryRowsTypedBlock004 := by
  simp only [geometryRowsJsonBlock004, geometryRowsTypedBlock004, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_032, decode_geometry_Rows_033, decode_geometry_Rows_034, decode_geometry_Rows_035, decode_geometry_Rows_036, decode_geometry_Rows_037, decode_geometry_Rows_038, decode_geometry_Rows_039]
  rfl

theorem geometry_Rows_block_004_length : geometryRowsTypedBlock004.length = 8 := by rfl

#print axioms geometryRow032_simplexId_read
#print axioms geometryRow032_vertexIds_read
#print axioms geometryRow032_physicalVolume_field
#print axioms geometryRow032_physicalVolume_numerator_no_slash
#print axioms geometryRow032_physicalVolume_numerator_parse
#print axioms geometryRow032_physicalVolume_denominator_parse
#print axioms geometryRow032_physicalVolume_denominator_nonzero
#print axioms geometryRow032_physicalVolume_parse
#print axioms geometryRow032_physicalVolume_read
#print axioms geometryRow032_meanGap_field
#print axioms geometryRow032_meanGap_numerator_no_slash
#print axioms geometryRow032_meanGap_numerator_parse
#print axioms geometryRow032_meanGap_denominator_parse
#print axioms geometryRow032_meanGap_denominator_nonzero
#print axioms geometryRow032_meanGap_parse
#print axioms geometryRow032_meanGap_read
#print axioms geometryRow032_jensenBound_field
#print axioms geometryRow032_jensenBound_numerator_no_slash
#print axioms geometryRow032_jensenBound_numerator_parse
#print axioms geometryRow032_jensenBound_denominator_parse
#print axioms geometryRow032_jensenBound_denominator_nonzero
#print axioms geometryRow032_jensenBound_parse
#print axioms geometryRow032_jensenBound_read
#print axioms geometryRow032_factorMaxima_read
#print axioms geometryRow032_gapWeightedMeans_read
#print axioms geometryRow032_floor_text_read
#print axioms geometryRow032_floor_chars_parse
#print axioms geometryRow032_floor_parse
#print axioms decode_geometry_Rows_032
#print axioms geometryRow032_shape
#print axioms geometryRow033_simplexId_read
#print axioms geometryRow033_vertexIds_read
#print axioms geometryRow033_physicalVolume_field
#print axioms geometryRow033_physicalVolume_numerator_no_slash
#print axioms geometryRow033_physicalVolume_numerator_parse
#print axioms geometryRow033_physicalVolume_denominator_parse
#print axioms geometryRow033_physicalVolume_denominator_nonzero
#print axioms geometryRow033_physicalVolume_parse
#print axioms geometryRow033_physicalVolume_read
#print axioms geometryRow033_meanGap_field
#print axioms geometryRow033_meanGap_numerator_no_slash
#print axioms geometryRow033_meanGap_numerator_parse
#print axioms geometryRow033_meanGap_denominator_parse
#print axioms geometryRow033_meanGap_denominator_nonzero
#print axioms geometryRow033_meanGap_parse
#print axioms geometryRow033_meanGap_read
#print axioms geometryRow033_jensenBound_field
#print axioms geometryRow033_jensenBound_numerator_no_slash
#print axioms geometryRow033_jensenBound_numerator_parse
#print axioms geometryRow033_jensenBound_denominator_parse
#print axioms geometryRow033_jensenBound_denominator_nonzero
#print axioms geometryRow033_jensenBound_parse
#print axioms geometryRow033_jensenBound_read
#print axioms geometryRow033_factorMaxima_read
#print axioms geometryRow033_gapWeightedMeans_read
#print axioms geometryRow033_floor_text_read
#print axioms geometryRow033_floor_chars_parse
#print axioms geometryRow033_floor_parse
#print axioms decode_geometry_Rows_033
#print axioms geometryRow033_shape
#print axioms geometryRow034_simplexId_read
#print axioms geometryRow034_vertexIds_read
#print axioms geometryRow034_physicalVolume_field
#print axioms geometryRow034_physicalVolume_numerator_no_slash
#print axioms geometryRow034_physicalVolume_numerator_parse
#print axioms geometryRow034_physicalVolume_denominator_parse
#print axioms geometryRow034_physicalVolume_denominator_nonzero
#print axioms geometryRow034_physicalVolume_parse
#print axioms geometryRow034_physicalVolume_read
#print axioms geometryRow034_meanGap_field
#print axioms geometryRow034_meanGap_numerator_no_slash
#print axioms geometryRow034_meanGap_numerator_parse
#print axioms geometryRow034_meanGap_denominator_parse
#print axioms geometryRow034_meanGap_denominator_nonzero
#print axioms geometryRow034_meanGap_parse
#print axioms geometryRow034_meanGap_read
#print axioms geometryRow034_jensenBound_field
#print axioms geometryRow034_jensenBound_numerator_no_slash
#print axioms geometryRow034_jensenBound_numerator_parse
#print axioms geometryRow034_jensenBound_denominator_parse
#print axioms geometryRow034_jensenBound_denominator_nonzero
#print axioms geometryRow034_jensenBound_parse
#print axioms geometryRow034_jensenBound_read
#print axioms geometryRow034_factorMaxima_read
#print axioms geometryRow034_gapWeightedMeans_read
#print axioms geometryRow034_floor_text_read
#print axioms geometryRow034_floor_chars_parse
#print axioms geometryRow034_floor_parse
#print axioms decode_geometry_Rows_034
#print axioms geometryRow034_shape
#print axioms geometryRow035_simplexId_read
#print axioms geometryRow035_vertexIds_read
#print axioms geometryRow035_physicalVolume_field
#print axioms geometryRow035_physicalVolume_numerator_no_slash
#print axioms geometryRow035_physicalVolume_numerator_parse
#print axioms geometryRow035_physicalVolume_denominator_parse
#print axioms geometryRow035_physicalVolume_denominator_nonzero
#print axioms geometryRow035_physicalVolume_parse
#print axioms geometryRow035_physicalVolume_read
#print axioms geometryRow035_meanGap_field
#print axioms geometryRow035_meanGap_numerator_no_slash
#print axioms geometryRow035_meanGap_numerator_parse
#print axioms geometryRow035_meanGap_denominator_parse
#print axioms geometryRow035_meanGap_denominator_nonzero
#print axioms geometryRow035_meanGap_parse
#print axioms geometryRow035_meanGap_read
#print axioms geometryRow035_jensenBound_field
#print axioms geometryRow035_jensenBound_numerator_no_slash
#print axioms geometryRow035_jensenBound_numerator_parse
#print axioms geometryRow035_jensenBound_denominator_parse
#print axioms geometryRow035_jensenBound_denominator_nonzero
#print axioms geometryRow035_jensenBound_parse
#print axioms geometryRow035_jensenBound_read
#print axioms geometryRow035_factorMaxima_read
#print axioms geometryRow035_gapWeightedMeans_read
#print axioms geometryRow035_floor_text_read
#print axioms geometryRow035_floor_chars_parse
#print axioms geometryRow035_floor_parse
#print axioms decode_geometry_Rows_035
#print axioms geometryRow035_shape
#print axioms geometryRow036_simplexId_read
#print axioms geometryRow036_vertexIds_read
#print axioms geometryRow036_physicalVolume_field
#print axioms geometryRow036_physicalVolume_numerator_no_slash
#print axioms geometryRow036_physicalVolume_numerator_parse
#print axioms geometryRow036_physicalVolume_denominator_parse
#print axioms geometryRow036_physicalVolume_denominator_nonzero
#print axioms geometryRow036_physicalVolume_parse
#print axioms geometryRow036_physicalVolume_read
#print axioms geometryRow036_meanGap_field
#print axioms geometryRow036_meanGap_numerator_no_slash
#print axioms geometryRow036_meanGap_numerator_parse
#print axioms geometryRow036_meanGap_denominator_parse
#print axioms geometryRow036_meanGap_denominator_nonzero
#print axioms geometryRow036_meanGap_parse
#print axioms geometryRow036_meanGap_read
#print axioms geometryRow036_jensenBound_field
#print axioms geometryRow036_jensenBound_numerator_no_slash
#print axioms geometryRow036_jensenBound_numerator_parse
#print axioms geometryRow036_jensenBound_denominator_parse
#print axioms geometryRow036_jensenBound_denominator_nonzero
#print axioms geometryRow036_jensenBound_parse
#print axioms geometryRow036_jensenBound_read
#print axioms geometryRow036_factorMaxima_read
#print axioms geometryRow036_gapWeightedMeans_read
#print axioms geometryRow036_floor_text_read
#print axioms geometryRow036_floor_chars_parse
#print axioms geometryRow036_floor_parse
#print axioms decode_geometry_Rows_036
#print axioms geometryRow036_shape
#print axioms geometryRow037_simplexId_read
#print axioms geometryRow037_vertexIds_read
#print axioms geometryRow037_physicalVolume_field
#print axioms geometryRow037_physicalVolume_numerator_no_slash
#print axioms geometryRow037_physicalVolume_numerator_parse
#print axioms geometryRow037_physicalVolume_denominator_parse
#print axioms geometryRow037_physicalVolume_denominator_nonzero
#print axioms geometryRow037_physicalVolume_parse
#print axioms geometryRow037_physicalVolume_read
#print axioms geometryRow037_meanGap_field
#print axioms geometryRow037_meanGap_numerator_no_slash
#print axioms geometryRow037_meanGap_numerator_parse
#print axioms geometryRow037_meanGap_denominator_parse
#print axioms geometryRow037_meanGap_denominator_nonzero
#print axioms geometryRow037_meanGap_parse
#print axioms geometryRow037_meanGap_read
#print axioms geometryRow037_jensenBound_field
#print axioms geometryRow037_jensenBound_numerator_no_slash
#print axioms geometryRow037_jensenBound_numerator_parse
#print axioms geometryRow037_jensenBound_denominator_parse
#print axioms geometryRow037_jensenBound_denominator_nonzero
#print axioms geometryRow037_jensenBound_parse
#print axioms geometryRow037_jensenBound_read
#print axioms geometryRow037_factorMaxima_read
#print axioms geometryRow037_gapWeightedMeans_read
#print axioms geometryRow037_floor_text_read
#print axioms geometryRow037_floor_chars_parse
#print axioms geometryRow037_floor_parse
#print axioms decode_geometry_Rows_037
#print axioms geometryRow037_shape
#print axioms geometryRow038_simplexId_read
#print axioms geometryRow038_vertexIds_read
#print axioms geometryRow038_physicalVolume_field
#print axioms geometryRow038_physicalVolume_numerator_no_slash
#print axioms geometryRow038_physicalVolume_numerator_parse
#print axioms geometryRow038_physicalVolume_denominator_parse
#print axioms geometryRow038_physicalVolume_denominator_nonzero
#print axioms geometryRow038_physicalVolume_parse
#print axioms geometryRow038_physicalVolume_read
#print axioms geometryRow038_meanGap_field
#print axioms geometryRow038_meanGap_numerator_no_slash
#print axioms geometryRow038_meanGap_numerator_parse
#print axioms geometryRow038_meanGap_denominator_parse
#print axioms geometryRow038_meanGap_denominator_nonzero
#print axioms geometryRow038_meanGap_parse
#print axioms geometryRow038_meanGap_read
#print axioms geometryRow038_jensenBound_field
#print axioms geometryRow038_jensenBound_numerator_no_slash
#print axioms geometryRow038_jensenBound_numerator_parse
#print axioms geometryRow038_jensenBound_denominator_parse
#print axioms geometryRow038_jensenBound_denominator_nonzero
#print axioms geometryRow038_jensenBound_parse
#print axioms geometryRow038_jensenBound_read
#print axioms geometryRow038_factorMaxima_read
#print axioms geometryRow038_gapWeightedMeans_read
#print axioms geometryRow038_floor_text_read
#print axioms geometryRow038_floor_chars_parse
#print axioms geometryRow038_floor_parse
#print axioms decode_geometry_Rows_038
#print axioms geometryRow038_shape
#print axioms geometryRow039_simplexId_read
#print axioms geometryRow039_vertexIds_read
#print axioms geometryRow039_physicalVolume_field
#print axioms geometryRow039_physicalVolume_numerator_no_slash
#print axioms geometryRow039_physicalVolume_numerator_parse
#print axioms geometryRow039_physicalVolume_denominator_parse
#print axioms geometryRow039_physicalVolume_denominator_nonzero
#print axioms geometryRow039_physicalVolume_parse
#print axioms geometryRow039_physicalVolume_read
#print axioms geometryRow039_meanGap_field
#print axioms geometryRow039_meanGap_numerator_no_slash
#print axioms geometryRow039_meanGap_numerator_parse
#print axioms geometryRow039_meanGap_denominator_parse
#print axioms geometryRow039_meanGap_denominator_nonzero
#print axioms geometryRow039_meanGap_parse
#print axioms geometryRow039_meanGap_read
#print axioms geometryRow039_jensenBound_field
#print axioms geometryRow039_jensenBound_numerator_no_slash
#print axioms geometryRow039_jensenBound_numerator_parse
#print axioms geometryRow039_jensenBound_denominator_parse
#print axioms geometryRow039_jensenBound_denominator_nonzero
#print axioms geometryRow039_jensenBound_parse
#print axioms geometryRow039_jensenBound_read
#print axioms geometryRow039_factorMaxima_read
#print axioms geometryRow039_gapWeightedMeans_read
#print axioms geometryRow039_floor_text_read
#print axioms geometryRow039_floor_chars_parse
#print axioms geometryRow039_floor_parse
#print axioms decode_geometry_Rows_039
#print axioms geometryRow039_shape
#print axioms geometry_Rows_block_004_push_eq
#print axioms geometry_Rows_block_004_reverse
#print axioms decode_geometry_Rows_block_004
#print axioms geometry_Rows_block_004_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
