import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock000

/-! Local typed certificates for original cell 06, rows 0 through 7.
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

noncomputable def geometryRowsJson000 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped000 : GeometryRow :=
  { simplexId := 0,
    vertexIds := #[32, 20, 6, 5, 4, 3, 2, 1, 0],
    physicalVolume := ((7906571668709174151335027175367723679946609259 : ℚ) / (2485853921976470470656000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((201938794323589 : ℚ) / (38764923120000000 : ℚ)),
    factorMaxima := #[((5390597 : ℚ) / (60000000 : ℚ)), ((525 : ℚ) / (5504 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((676082974351699529900034000049 : ℚ) / (7828141836899419987477680000000 : ℚ)), ((16027420389845598175452515041 : ℚ) / (174735308859362053291912500000 : ℚ)), ((1094904250939871511559277313703 : ℚ) / (9785177296124274984347100000000 : ℚ)), ((893101247275099273003720357513 : ℚ) / (9785177296124274984347100000000 : ℚ)), ((294425021693391688866864459097 : ℚ) / (3261725765374758328115700000000 : ℚ)), ((25846251280318221706017681427 : ℚ) / (355824628949973635794440000000 : ℚ)), ((404344515392209375796374111 : ℚ) / (11119519654686676118576250000 : ℚ)), ((12870913072282866007817426699 : ℚ) / (355824628949973635794440000000 : ℚ)), ((319828211233801556395364729 : ℚ) / (8895615723749340894861000000 : ℚ)), ((29208211600268824572011650939 : ℚ) / (931921647249930950890200000000 : ℚ))],
    jensenBound := ((36972177311071908412344058458006600614104644223998547963428213588539762597553593845048172205127154924360328734527496990225354709063256192952298776010434465561436718220740762526949194517910830595716229293233596208980704588080795226645733902931379208764781965789794921875 : ℚ) / (438610816798168341755755262708498596099788853783977978123967049154150054687609016384370900130651298793843881088645106661562999574901723680762960934126543693088735370999141218017952932633966384464222239126759337336017968767829407948636217697549065383606873537042861449780408106312502352 : ℚ)),
    jensenFloorQ96 := (6678443759985 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_simplexId_before"
  err.flush

theorem geometryRow000_simplexId_read :
    geometryRowsJson000.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped000.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_vertexIds_before"
  err.flush

theorem geometryRow000_vertexIds_read :
    geometryRowsJson000.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped000.vertexIds := by decide +kernel

noncomputable def geometryRow000_physicalVolumeNumeratorChars : List Char := ['7', '9', '0', '6', '5', '7', '1', '6', '6', '8', '7', '0', '9', '1', '7', '4', '1', '5', '1', '3', '3', '5', '0', '2', '7', '1', '7', '5', '3', '6', '7', '7', '2', '3', '6', '7', '9', '9', '4', '6', '6', '0', '9', '2', '5', '9']
noncomputable def geometryRow000_physicalVolumeDenominatorChars : List Char := ['2', '4', '8', '5', '8', '5', '3', '9', '2', '1', '9', '7', '6', '4', '7', '0', '4', '7', '0', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_physicalVolumeText : String := String.ofList (geometryRow000_physicalVolumeNumeratorChars ++ '/' :: geometryRow000_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_physicalVolume_before_field"
  err.flush

theorem geometryRow000_physicalVolume_field :
    geometryRowsJson000.getObjVal? "physical_volume" = .ok (.str geometryRow000_physicalVolumeText) := by rfl

theorem geometryRow000_physicalVolume_numerator_no_slash :
    geometryRow000_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeNumeratorChars = some (7906571668709174151335027175367723679946609259 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeDenominatorChars = some (2485853921976470470656000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_nonzero : (2485853921976470470656000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_physicalVolume_parse :
    parseRational geometryRow000_physicalVolumeText = .ok geometryRowsTyped000.physicalVolume :=
  original_rational_fraction_of_chars geometryRow000_physicalVolumeNumeratorChars geometryRow000_physicalVolumeDenominatorChars
    (7906571668709174151335027175367723679946609259 : Int) (2485853921976470470656000000000000000000000000000000000000000000000000000 : Int)
    geometryRow000_physicalVolume_numerator_no_slash geometryRow000_physicalVolume_numerator_parse
    geometryRow000_physicalVolume_denominator_parse geometryRow000_physicalVolume_denominator_nonzero

theorem geometryRow000_physicalVolume_read :
    rationalField geometryRowsJson000 "physical_volume" = .ok geometryRowsTyped000.physicalVolume :=
  original_rationalField_of_string geometryRowsJson000 "physical_volume" geometryRow000_physicalVolumeText
    geometryRowsTyped000.physicalVolume geometryRow000_physicalVolume_field geometryRow000_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_physicalVolume_complete"
  err.flush

noncomputable def geometryRow000_meanGapNumeratorChars : List Char := ['2', '0', '1', '9', '3', '8', '7', '9', '4', '3', '2', '3', '5', '8', '9']
noncomputable def geometryRow000_meanGapDenominatorChars : List Char := ['3', '8', '7', '6', '4', '9', '2', '3', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_meanGapText : String := String.ofList (geometryRow000_meanGapNumeratorChars ++ '/' :: geometryRow000_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_meanGap_before_field"
  err.flush

theorem geometryRow000_meanGap_field :
    geometryRowsJson000.getObjVal? "mean_gap" = .ok (.str geometryRow000_meanGapText) := by rfl

theorem geometryRow000_meanGap_numerator_no_slash :
    geometryRow000_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_meanGap_numerator_parse :
    SourceJson.intChars geometryRow000_meanGapNumeratorChars = some (201938794323589 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_parse :
    SourceJson.intChars geometryRow000_meanGapDenominatorChars = some (38764923120000000 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_nonzero : (38764923120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_meanGap_parse :
    parseRational geometryRow000_meanGapText = .ok geometryRowsTyped000.meanGap :=
  original_rational_fraction_of_chars geometryRow000_meanGapNumeratorChars geometryRow000_meanGapDenominatorChars
    (201938794323589 : Int) (38764923120000000 : Int)
    geometryRow000_meanGap_numerator_no_slash geometryRow000_meanGap_numerator_parse
    geometryRow000_meanGap_denominator_parse geometryRow000_meanGap_denominator_nonzero

theorem geometryRow000_meanGap_read :
    rationalField geometryRowsJson000 "mean_gap" = .ok geometryRowsTyped000.meanGap :=
  original_rationalField_of_string geometryRowsJson000 "mean_gap" geometryRow000_meanGapText
    geometryRowsTyped000.meanGap geometryRow000_meanGap_field geometryRow000_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_meanGap_complete"
  err.flush

noncomputable def geometryRow000_jensenBoundNumeratorChars : List Char := ['3', '6', '9', '7', '2', '1', '7', '7', '3', '1', '1', '0', '7', '1', '9', '0', '8', '4', '1', '2', '3', '4', '4', '0', '5', '8', '4', '5', '8', '0', '0', '6', '6', '0', '0', '6', '1', '4', '1', '0', '4', '6', '4', '4', '2', '2', '3', '9', '9', '8', '5', '4', '7', '9', '6', '3', '4', '2', '8', '2', '1', '3', '5', '8', '8', '5', '3', '9', '7', '6', '2', '5', '9', '7', '5', '5', '3', '5', '9', '3', '8', '4', '5', '0', '4', '8', '1', '7', '2', '2', '0', '5', '1', '2', '7', '1', '5', '4', '9', '2', '4', '3', '6', '0', '3', '2', '8', '7', '3', '4', '5', '2', '7', '4', '9', '6', '9', '9', '0', '2', '2', '5', '3', '5', '4', '7', '0', '9', '0', '6', '3', '2', '5', '6', '1', '9', '2', '9', '5', '2', '2', '9', '8', '7', '7', '6', '0', '1', '0', '4', '3', '4', '4', '6', '5', '5', '6', '1', '4', '3', '6', '7', '1', '8', '2', '2', '0', '7', '4', '0', '7', '6', '2', '5', '2', '6', '9', '4', '9', '1', '9', '4', '5', '1', '7', '9', '1', '0', '8', '3', '0', '5', '9', '5', '7', '1', '6', '2', '2', '9', '2', '9', '3', '2', '3', '3', '5', '9', '6', '2', '0', '8', '9', '8', '0', '7', '0', '4', '5', '8', '8', '0', '8', '0', '7', '9', '5', '2', '2', '6', '6', '4', '5', '7', '3', '3', '9', '0', '2', '9', '3', '1', '3', '7', '9', '2', '0', '8', '7', '6', '4', '7', '8', '1', '9', '6', '5', '7', '8', '9', '7', '9', '4', '9', '2', '1', '8', '7', '5']
noncomputable def geometryRow000_jensenBoundDenominatorChars : List Char := ['4', '3', '8', '6', '1', '0', '8', '1', '6', '7', '9', '8', '1', '6', '8', '3', '4', '1', '7', '5', '5', '7', '5', '5', '2', '6', '2', '7', '0', '8', '4', '9', '8', '5', '9', '6', '0', '9', '9', '7', '8', '8', '8', '5', '3', '7', '8', '3', '9', '7', '7', '9', '7', '8', '1', '2', '3', '9', '6', '7', '0', '4', '9', '1', '5', '4', '1', '5', '0', '0', '5', '4', '6', '8', '7', '6', '0', '9', '0', '1', '6', '3', '8', '4', '3', '7', '0', '9', '0', '0', '1', '3', '0', '6', '5', '1', '2', '9', '8', '7', '9', '3', '8', '4', '3', '8', '8', '1', '0', '8', '8', '6', '4', '5', '1', '0', '6', '6', '6', '1', '5', '6', '2', '9', '9', '9', '5', '7', '4', '9', '0', '1', '7', '2', '3', '6', '8', '0', '7', '6', '2', '9', '6', '0', '9', '3', '4', '1', '2', '6', '5', '4', '3', '6', '9', '3', '0', '8', '8', '7', '3', '5', '3', '7', '0', '9', '9', '9', '1', '4', '1', '2', '1', '8', '0', '1', '7', '9', '5', '2', '9', '3', '2', '6', '3', '3', '9', '6', '6', '3', '8', '4', '4', '6', '4', '2', '2', '2', '2', '3', '9', '1', '2', '6', '7', '5', '9', '3', '3', '7', '3', '3', '6', '0', '1', '7', '9', '6', '8', '7', '6', '7', '8', '2', '9', '4', '0', '7', '9', '4', '8', '6', '3', '6', '2', '1', '7', '6', '9', '7', '5', '4', '9', '0', '6', '5', '3', '8', '3', '6', '0', '6', '8', '7', '3', '5', '3', '7', '0', '4', '2', '8', '6', '1', '4', '4', '9', '7', '8', '0', '4', '0', '8', '1', '0', '6', '3', '1', '2', '5', '0', '2', '3', '5', '2']
noncomputable def geometryRow000_jensenBoundText : String := String.ofList (geometryRow000_jensenBoundNumeratorChars ++ '/' :: geometryRow000_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_jensenBound_before_field"
  err.flush

theorem geometryRow000_jensenBound_field :
    geometryRowsJson000.getObjVal? "jensen_bound" = .ok (.str geometryRow000_jensenBoundText) := by rfl

theorem geometryRow000_jensenBound_numerator_no_slash :
    geometryRow000_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow000_jensenBoundNumeratorChars = some (36972177311071908412344058458006600614104644223998547963428213588539762597553593845048172205127154924360328734527496990225354709063256192952298776010434465561436718220740762526949194517910830595716229293233596208980704588080795226645733902931379208764781965789794921875 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow000_jensenBoundDenominatorChars = some (438610816798168341755755262708498596099788853783977978123967049154150054687609016384370900130651298793843881088645106661562999574901723680762960934126543693088735370999141218017952932633966384464222239126759337336017968767829407948636217697549065383606873537042861449780408106312502352 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_nonzero : (438610816798168341755755262708498596099788853783977978123967049154150054687609016384370900130651298793843881088645106661562999574901723680762960934126543693088735370999141218017952932633966384464222239126759337336017968767829407948636217697549065383606873537042861449780408106312502352 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_jensenBound_parse :
    parseRational geometryRow000_jensenBoundText = .ok geometryRowsTyped000.jensenBound :=
  original_rational_fraction_of_chars geometryRow000_jensenBoundNumeratorChars geometryRow000_jensenBoundDenominatorChars
    (36972177311071908412344058458006600614104644223998547963428213588539762597553593845048172205127154924360328734527496990225354709063256192952298776010434465561436718220740762526949194517910830595716229293233596208980704588080795226645733902931379208764781965789794921875 : Int) (438610816798168341755755262708498596099788853783977978123967049154150054687609016384370900130651298793843881088645106661562999574901723680762960934126543693088735370999141218017952932633966384464222239126759337336017968767829407948636217697549065383606873537042861449780408106312502352 : Int)
    geometryRow000_jensenBound_numerator_no_slash geometryRow000_jensenBound_numerator_parse
    geometryRow000_jensenBound_denominator_parse geometryRow000_jensenBound_denominator_nonzero

theorem geometryRow000_jensenBound_read :
    rationalField geometryRowsJson000 "jensen_bound" = .ok geometryRowsTyped000.jensenBound :=
  original_rationalField_of_string geometryRowsJson000 "jensen_bound" geometryRow000_jensenBoundText
    geometryRowsTyped000.jensenBound geometryRow000_jensenBound_field geometryRow000_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_factorMaxima_before"
  err.flush

theorem geometryRow000_factorMaxima_read :
    rationalArrayField geometryRowsJson000 "factor_maxima" = .ok geometryRowsTyped000.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_gapWeightedMeans_before"
  err.flush

theorem geometryRow000_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson000 "gap_weighted_means" = .ok geometryRowsTyped000.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow000_floorChars : List Char := ['6', '6', '7', '8', '4', '4', '3', '7', '5', '9', '9', '8', '5']
noncomputable def geometryRow000_floorText : String := String.ofList geometryRow000_floorChars

theorem geometryRow000_floor_text_read :
    geometryRowsJson000.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow000_floorText := by rfl

theorem geometryRow000_floor_chars_parse :
    SourceJson.intChars geometryRow000_floorChars = some (6678443759985 : Int) := by decide +kernel

theorem geometryRow000_floor_parse :
    parseInteger geometryRow000_floorText = .ok geometryRowsTyped000.jensenFloorQ96 := by
  simp only [geometryRow000_floorText, parseInteger, String.toList_ofList, geometryRow000_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_000 :
    decodeGeometryRow geometryRowsJson000 = .ok geometryRowsTyped000 :=
  original_geometryRow_of_fields geometryRowsJson000 geometryRowsTyped000 geometryRow000_floorText
    geometryRow000_simplexId_read geometryRow000_vertexIds_read
    geometryRow000_physicalVolume_read geometryRow000_meanGap_read
    geometryRow000_factorMaxima_read geometryRow000_gapWeightedMeans_read
    geometryRow000_jensenBound_read geometryRow000_floor_text_read geometryRow000_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_000_original_decoder_complete"
  err.flush

theorem geometryRow000_shape :
    geometryRowsTyped000.simplexId = 0 ∧
    geometryRowsTyped000.vertexIds.size = 9 ∧ geometryRowsTyped000.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped000.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped000.factorMaxima.size = 10 ∧ geometryRowsTyped000.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson001 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped001 : GeometryRow :=
  { simplexId := 1,
    vertexIds := #[32, 20, 18, 5, 4, 3, 2, 1, 0],
    physicalVolume := ((8588860805537061331496499844433266835256610693 : ℚ) / (184593113018054737920000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1714926364219 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((5390597 : ℚ) / (60000000 : ℚ)), ((525 : ℚ) / (5504 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (5000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((285279104073973260029879953 : ℚ) / (3291039042842111576400000000 : ℚ)), ((21479980141446500024700473 : ℚ) / (235074217345865112600000000 : ℚ)), ((370869443864960765763839399 : ℚ) / (3291039042842111576400000000 : ℚ)), ((11839516107027004565167283 : ℚ) / (131641561713684463056000000 : ℚ)), ((97662852521658405969221299 : ℚ) / (1097013014280703858800000000 : ℚ)), ((21892285460220412829167193 : ℚ) / (299185367531101052400000000 : ℚ)), ((5479892843107473809002997 : ℚ) / (149592683765550526200000000 : ℚ)), ((2725332240638991819542341 : ℚ) / (74796341882775263100000000 : ℚ)), ((5417274769378757379242837 : ℚ) / (149592683765550526200000000 : ℚ)), ((2518318073331590868801511 : ℚ) / (78358072448621704200000000 : ℚ))],
    jensenBound := ((70994109080716416523384368768362354967162229018679840355060690373019855298990658570061130940329190411766334501925548062226878136369670996100386231462940658890951466037987650811450889974635255834501220346039383279144314375000000000000000 : ℚ) / (69354654452516785680914800287731181213221923013563122551517312174330086721264318225709316617872655496751504563887544138646653240089746151857358100822090058768698981678610930638290812197869477699808105343336200812459687276550782262379696397088809432141 : ℚ)),
    jensenFloorQ96 := (81101014145393 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_simplexId_before"
  err.flush

theorem geometryRow001_simplexId_read :
    geometryRowsJson001.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped001.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_vertexIds_before"
  err.flush

theorem geometryRow001_vertexIds_read :
    geometryRowsJson001.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped001.vertexIds := by decide +kernel

noncomputable def geometryRow001_physicalVolumeNumeratorChars : List Char := ['8', '5', '8', '8', '8', '6', '0', '8', '0', '5', '5', '3', '7', '0', '6', '1', '3', '3', '1', '4', '9', '6', '4', '9', '9', '8', '4', '4', '4', '3', '3', '2', '6', '6', '8', '3', '5', '2', '5', '6', '6', '1', '0', '6', '9', '3']
noncomputable def geometryRow001_physicalVolumeDenominatorChars : List Char := ['1', '8', '4', '5', '9', '3', '1', '1', '3', '0', '1', '8', '0', '5', '4', '7', '3', '7', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_physicalVolumeText : String := String.ofList (geometryRow001_physicalVolumeNumeratorChars ++ '/' :: geometryRow001_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_physicalVolume_before_field"
  err.flush

theorem geometryRow001_physicalVolume_field :
    geometryRowsJson001.getObjVal? "physical_volume" = .ok (.str geometryRow001_physicalVolumeText) := by rfl

theorem geometryRow001_physicalVolume_numerator_no_slash :
    geometryRow001_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeNumeratorChars = some (8588860805537061331496499844433266835256610693 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeDenominatorChars = some (184593113018054737920000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_nonzero : (184593113018054737920000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_physicalVolume_parse :
    parseRational geometryRow001_physicalVolumeText = .ok geometryRowsTyped001.physicalVolume :=
  original_rational_fraction_of_chars geometryRow001_physicalVolumeNumeratorChars geometryRow001_physicalVolumeDenominatorChars
    (8588860805537061331496499844433266835256610693 : Int) (184593113018054737920000000000000000000000000000000000000000000000000000 : Int)
    geometryRow001_physicalVolume_numerator_no_slash geometryRow001_physicalVolume_numerator_parse
    geometryRow001_physicalVolume_denominator_parse geometryRow001_physicalVolume_denominator_nonzero

theorem geometryRow001_physicalVolume_read :
    rationalField geometryRowsJson001 "physical_volume" = .ok geometryRowsTyped001.physicalVolume :=
  original_rationalField_of_string geometryRowsJson001 "physical_volume" geometryRow001_physicalVolumeText
    geometryRowsTyped001.physicalVolume geometryRow001_physicalVolume_field geometryRow001_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_physicalVolume_complete"
  err.flush

noncomputable def geometryRow001_meanGapNumeratorChars : List Char := ['1', '7', '1', '4', '9', '2', '6', '3', '6', '4', '2', '1', '9']
noncomputable def geometryRow001_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_meanGapText : String := String.ofList (geometryRow001_meanGapNumeratorChars ++ '/' :: geometryRow001_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_meanGap_before_field"
  err.flush

theorem geometryRow001_meanGap_field :
    geometryRowsJson001.getObjVal? "mean_gap" = .ok (.str geometryRow001_meanGapText) := by rfl

theorem geometryRow001_meanGap_numerator_no_slash :
    geometryRow001_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_meanGap_numerator_parse :
    SourceJson.intChars geometryRow001_meanGapNumeratorChars = some (1714926364219 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_parse :
    SourceJson.intChars geometryRow001_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_meanGap_parse :
    parseRational geometryRow001_meanGapText = .ok geometryRowsTyped001.meanGap :=
  original_rational_fraction_of_chars geometryRow001_meanGapNumeratorChars geometryRow001_meanGapDenominatorChars
    (1714926364219 : Int) (383811120000000 : Int)
    geometryRow001_meanGap_numerator_no_slash geometryRow001_meanGap_numerator_parse
    geometryRow001_meanGap_denominator_parse geometryRow001_meanGap_denominator_nonzero

theorem geometryRow001_meanGap_read :
    rationalField geometryRowsJson001 "mean_gap" = .ok geometryRowsTyped001.meanGap :=
  original_rationalField_of_string geometryRowsJson001 "mean_gap" geometryRow001_meanGapText
    geometryRowsTyped001.meanGap geometryRow001_meanGap_field geometryRow001_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_meanGap_complete"
  err.flush

noncomputable def geometryRow001_jensenBoundNumeratorChars : List Char := ['7', '0', '9', '9', '4', '1', '0', '9', '0', '8', '0', '7', '1', '6', '4', '1', '6', '5', '2', '3', '3', '8', '4', '3', '6', '8', '7', '6', '8', '3', '6', '2', '3', '5', '4', '9', '6', '7', '1', '6', '2', '2', '2', '9', '0', '1', '8', '6', '7', '9', '8', '4', '0', '3', '5', '5', '0', '6', '0', '6', '9', '0', '3', '7', '3', '0', '1', '9', '8', '5', '5', '2', '9', '8', '9', '9', '0', '6', '5', '8', '5', '7', '0', '0', '6', '1', '1', '3', '0', '9', '4', '0', '3', '2', '9', '1', '9', '0', '4', '1', '1', '7', '6', '6', '3', '3', '4', '5', '0', '1', '9', '2', '5', '5', '4', '8', '0', '6', '2', '2', '2', '6', '8', '7', '8', '1', '3', '6', '3', '6', '9', '6', '7', '0', '9', '9', '6', '1', '0', '0', '3', '8', '6', '2', '3', '1', '4', '6', '2', '9', '4', '0', '6', '5', '8', '8', '9', '0', '9', '5', '1', '4', '6', '6', '0', '3', '7', '9', '8', '7', '6', '5', '0', '8', '1', '1', '4', '5', '0', '8', '8', '9', '9', '7', '4', '6', '3', '5', '2', '5', '5', '8', '3', '4', '5', '0', '1', '2', '2', '0', '3', '4', '6', '0', '3', '9', '3', '8', '3', '2', '7', '9', '1', '4', '4', '3', '1', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_jensenBoundDenominatorChars : List Char := ['6', '9', '3', '5', '4', '6', '5', '4', '4', '5', '2', '5', '1', '6', '7', '8', '5', '6', '8', '0', '9', '1', '4', '8', '0', '0', '2', '8', '7', '7', '3', '1', '1', '8', '1', '2', '1', '3', '2', '2', '1', '9', '2', '3', '0', '1', '3', '5', '6', '3', '1', '2', '2', '5', '5', '1', '5', '1', '7', '3', '1', '2', '1', '7', '4', '3', '3', '0', '0', '8', '6', '7', '2', '1', '2', '6', '4', '3', '1', '8', '2', '2', '5', '7', '0', '9', '3', '1', '6', '6', '1', '7', '8', '7', '2', '6', '5', '5', '4', '9', '6', '7', '5', '1', '5', '0', '4', '5', '6', '3', '8', '8', '7', '5', '4', '4', '1', '3', '8', '6', '4', '6', '6', '5', '3', '2', '4', '0', '0', '8', '9', '7', '4', '6', '1', '5', '1', '8', '5', '7', '3', '5', '8', '1', '0', '0', '8', '2', '2', '0', '9', '0', '0', '5', '8', '7', '6', '8', '6', '9', '8', '9', '8', '1', '6', '7', '8', '6', '1', '0', '9', '3', '0', '6', '3', '8', '2', '9', '0', '8', '1', '2', '1', '9', '7', '8', '6', '9', '4', '7', '7', '6', '9', '9', '8', '0', '8', '1', '0', '5', '3', '4', '3', '3', '3', '6', '2', '0', '0', '8', '1', '2', '4', '5', '9', '6', '8', '7', '2', '7', '6', '5', '5', '0', '7', '8', '2', '2', '6', '2', '3', '7', '9', '6', '9', '6', '3', '9', '7', '0', '8', '8', '8', '0', '9', '4', '3', '2', '1', '4', '1']
noncomputable def geometryRow001_jensenBoundText : String := String.ofList (geometryRow001_jensenBoundNumeratorChars ++ '/' :: geometryRow001_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_jensenBound_before_field"
  err.flush

theorem geometryRow001_jensenBound_field :
    geometryRowsJson001.getObjVal? "jensen_bound" = .ok (.str geometryRow001_jensenBoundText) := by rfl

theorem geometryRow001_jensenBound_numerator_no_slash :
    geometryRow001_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow001_jensenBoundNumeratorChars = some (70994109080716416523384368768362354967162229018679840355060690373019855298990658570061130940329190411766334501925548062226878136369670996100386231462940658890951466037987650811450889974635255834501220346039383279144314375000000000000000 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow001_jensenBoundDenominatorChars = some (69354654452516785680914800287731181213221923013563122551517312174330086721264318225709316617872655496751504563887544138646653240089746151857358100822090058768698981678610930638290812197869477699808105343336200812459687276550782262379696397088809432141 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_nonzero : (69354654452516785680914800287731181213221923013563122551517312174330086721264318225709316617872655496751504563887544138646653240089746151857358100822090058768698981678610930638290812197869477699808105343336200812459687276550782262379696397088809432141 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_jensenBound_parse :
    parseRational geometryRow001_jensenBoundText = .ok geometryRowsTyped001.jensenBound :=
  original_rational_fraction_of_chars geometryRow001_jensenBoundNumeratorChars geometryRow001_jensenBoundDenominatorChars
    (70994109080716416523384368768362354967162229018679840355060690373019855298990658570061130940329190411766334501925548062226878136369670996100386231462940658890951466037987650811450889974635255834501220346039383279144314375000000000000000 : Int) (69354654452516785680914800287731181213221923013563122551517312174330086721264318225709316617872655496751504563887544138646653240089746151857358100822090058768698981678610930638290812197869477699808105343336200812459687276550782262379696397088809432141 : Int)
    geometryRow001_jensenBound_numerator_no_slash geometryRow001_jensenBound_numerator_parse
    geometryRow001_jensenBound_denominator_parse geometryRow001_jensenBound_denominator_nonzero

theorem geometryRow001_jensenBound_read :
    rationalField geometryRowsJson001 "jensen_bound" = .ok geometryRowsTyped001.jensenBound :=
  original_rationalField_of_string geometryRowsJson001 "jensen_bound" geometryRow001_jensenBoundText
    geometryRowsTyped001.jensenBound geometryRow001_jensenBound_field geometryRow001_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_factorMaxima_before"
  err.flush

theorem geometryRow001_factorMaxima_read :
    rationalArrayField geometryRowsJson001 "factor_maxima" = .ok geometryRowsTyped001.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_gapWeightedMeans_before"
  err.flush

theorem geometryRow001_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson001 "gap_weighted_means" = .ok geometryRowsTyped001.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow001_floorChars : List Char := ['8', '1', '1', '0', '1', '0', '1', '4', '1', '4', '5', '3', '9', '3']
noncomputable def geometryRow001_floorText : String := String.ofList geometryRow001_floorChars

theorem geometryRow001_floor_text_read :
    geometryRowsJson001.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow001_floorText := by rfl

theorem geometryRow001_floor_chars_parse :
    SourceJson.intChars geometryRow001_floorChars = some (81101014145393 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_001_original_decoder_complete"
  err.flush

theorem geometryRow001_shape :
    geometryRowsTyped001.simplexId = 1 ∧
    geometryRowsTyped001.vertexIds.size = 9 ∧ geometryRowsTyped001.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped001.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped001.factorMaxima.size = 10 ∧ geometryRowsTyped001.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson002 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped002 : GeometryRow :=
  { simplexId := 2,
    vertexIds := #[32, 20, 18, 16, 4, 3, 2, 1, 0],
    physicalVolume := ((30328286897096815994513621135603770804657225103 : ℚ) / (51514357121317601280000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((474804774133 : ℚ) / (127937040000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1258269652733938005533899 : ℚ) / (14237136886041699918750000 : ℚ)), ((12025930018782473393413717 : ℚ) / (130168108672381256400000000 : ℚ)), ((206432811923287187559635431 : ℚ) / (1822353521413337589600000000 : ℚ)), ((32399642149575219492902801 : ℚ) / (364470704282667517920000000 : ℚ)), ((17815264164573193224725457 : ℚ) / (202483724601481954400000000 : ℚ)), ((12251283412277253668190607 : ℚ) / (165668501946667053600000000 : ℚ)), ((3019525591241221897339093 : ℚ) / (82834250973333526800000000 : ℚ)), ((3002869770145538051348683 : ℚ) / (82834250973333526800000000 : ℚ)), ((2983829042706256518609733 : ℚ) / (82834250973333526800000000 : ℚ)), ((1405887031154167675457299 : ℚ) / (43389369557460418800000000 : ℚ))],
    jensenBound := ((1182339544942268877390925393103421344558862766309751664034424625880089439547721196549926280062680553954089479800340457420089357352887544207549233208808992057727340576338933741773322899229534114044763205104549025162500000000000000000 : ℚ) / (111625353597125179210539736821571533771454336010782121170608959466048387038940405019989323380591436356363154032366324547550856954002584380154315253403947211876742565071396186359217060966791958886352926176722153905177878070159947946507454420528673 : ℚ)),
    jensenFloorQ96 := (839187394217042 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_simplexId_before"
  err.flush

theorem geometryRow002_simplexId_read :
    geometryRowsJson002.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped002.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_vertexIds_before"
  err.flush

theorem geometryRow002_vertexIds_read :
    geometryRowsJson002.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped002.vertexIds := by decide +kernel

noncomputable def geometryRow002_physicalVolumeNumeratorChars : List Char := ['3', '0', '3', '2', '8', '2', '8', '6', '8', '9', '7', '0', '9', '6', '8', '1', '5', '9', '9', '4', '5', '1', '3', '6', '2', '1', '1', '3', '5', '6', '0', '3', '7', '7', '0', '8', '0', '4', '6', '5', '7', '2', '2', '5', '1', '0', '3']
noncomputable def geometryRow002_physicalVolumeDenominatorChars : List Char := ['5', '1', '5', '1', '4', '3', '5', '7', '1', '2', '1', '3', '1', '7', '6', '0', '1', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_physicalVolumeText : String := String.ofList (geometryRow002_physicalVolumeNumeratorChars ++ '/' :: geometryRow002_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_physicalVolume_before_field"
  err.flush

theorem geometryRow002_physicalVolume_field :
    geometryRowsJson002.getObjVal? "physical_volume" = .ok (.str geometryRow002_physicalVolumeText) := by rfl

theorem geometryRow002_physicalVolume_numerator_no_slash :
    geometryRow002_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeNumeratorChars = some (30328286897096815994513621135603770804657225103 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeDenominatorChars = some (51514357121317601280000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_nonzero : (51514357121317601280000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_physicalVolume_parse :
    parseRational geometryRow002_physicalVolumeText = .ok geometryRowsTyped002.physicalVolume :=
  original_rational_fraction_of_chars geometryRow002_physicalVolumeNumeratorChars geometryRow002_physicalVolumeDenominatorChars
    (30328286897096815994513621135603770804657225103 : Int) (51514357121317601280000000000000000000000000000000000000000000000000000 : Int)
    geometryRow002_physicalVolume_numerator_no_slash geometryRow002_physicalVolume_numerator_parse
    geometryRow002_physicalVolume_denominator_parse geometryRow002_physicalVolume_denominator_nonzero

theorem geometryRow002_physicalVolume_read :
    rationalField geometryRowsJson002 "physical_volume" = .ok geometryRowsTyped002.physicalVolume :=
  original_rationalField_of_string geometryRowsJson002 "physical_volume" geometryRow002_physicalVolumeText
    geometryRowsTyped002.physicalVolume geometryRow002_physicalVolume_field geometryRow002_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_physicalVolume_complete"
  err.flush

noncomputable def geometryRow002_meanGapNumeratorChars : List Char := ['4', '7', '4', '8', '0', '4', '7', '7', '4', '1', '3', '3']
noncomputable def geometryRow002_meanGapDenominatorChars : List Char := ['1', '2', '7', '9', '3', '7', '0', '4', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_meanGapText : String := String.ofList (geometryRow002_meanGapNumeratorChars ++ '/' :: geometryRow002_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_meanGap_before_field"
  err.flush

theorem geometryRow002_meanGap_field :
    geometryRowsJson002.getObjVal? "mean_gap" = .ok (.str geometryRow002_meanGapText) := by rfl

theorem geometryRow002_meanGap_numerator_no_slash :
    geometryRow002_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_meanGap_numerator_parse :
    SourceJson.intChars geometryRow002_meanGapNumeratorChars = some (474804774133 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_parse :
    SourceJson.intChars geometryRow002_meanGapDenominatorChars = some (127937040000000 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_nonzero : (127937040000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_meanGap_parse :
    parseRational geometryRow002_meanGapText = .ok geometryRowsTyped002.meanGap :=
  original_rational_fraction_of_chars geometryRow002_meanGapNumeratorChars geometryRow002_meanGapDenominatorChars
    (474804774133 : Int) (127937040000000 : Int)
    geometryRow002_meanGap_numerator_no_slash geometryRow002_meanGap_numerator_parse
    geometryRow002_meanGap_denominator_parse geometryRow002_meanGap_denominator_nonzero

theorem geometryRow002_meanGap_read :
    rationalField geometryRowsJson002 "mean_gap" = .ok geometryRowsTyped002.meanGap :=
  original_rationalField_of_string geometryRowsJson002 "mean_gap" geometryRow002_meanGapText
    geometryRowsTyped002.meanGap geometryRow002_meanGap_field geometryRow002_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_meanGap_complete"
  err.flush

noncomputable def geometryRow002_jensenBoundNumeratorChars : List Char := ['1', '1', '8', '2', '3', '3', '9', '5', '4', '4', '9', '4', '2', '2', '6', '8', '8', '7', '7', '3', '9', '0', '9', '2', '5', '3', '9', '3', '1', '0', '3', '4', '2', '1', '3', '4', '4', '5', '5', '8', '8', '6', '2', '7', '6', '6', '3', '0', '9', '7', '5', '1', '6', '6', '4', '0', '3', '4', '4', '2', '4', '6', '2', '5', '8', '8', '0', '0', '8', '9', '4', '3', '9', '5', '4', '7', '7', '2', '1', '1', '9', '6', '5', '4', '9', '9', '2', '6', '2', '8', '0', '0', '6', '2', '6', '8', '0', '5', '5', '3', '9', '5', '4', '0', '8', '9', '4', '7', '9', '8', '0', '0', '3', '4', '0', '4', '5', '7', '4', '2', '0', '0', '8', '9', '3', '5', '7', '3', '5', '2', '8', '8', '7', '5', '4', '4', '2', '0', '7', '5', '4', '9', '2', '3', '3', '2', '0', '8', '8', '0', '8', '9', '9', '2', '0', '5', '7', '7', '2', '7', '3', '4', '0', '5', '7', '6', '3', '3', '8', '9', '3', '3', '7', '4', '1', '7', '7', '3', '3', '2', '2', '8', '9', '9', '2', '2', '9', '5', '3', '4', '1', '1', '4', '0', '4', '4', '7', '6', '3', '2', '0', '5', '1', '0', '4', '5', '4', '9', '0', '2', '5', '1', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_jensenBoundDenominatorChars : List Char := ['1', '1', '1', '6', '2', '5', '3', '5', '3', '5', '9', '7', '1', '2', '5', '1', '7', '9', '2', '1', '0', '5', '3', '9', '7', '3', '6', '8', '2', '1', '5', '7', '1', '5', '3', '3', '7', '7', '1', '4', '5', '4', '3', '3', '6', '0', '1', '0', '7', '8', '2', '1', '2', '1', '1', '7', '0', '6', '0', '8', '9', '5', '9', '4', '6', '6', '0', '4', '8', '3', '8', '7', '0', '3', '8', '9', '4', '0', '4', '0', '5', '0', '1', '9', '9', '8', '9', '3', '2', '3', '3', '8', '0', '5', '9', '1', '4', '3', '6', '3', '5', '6', '3', '6', '3', '1', '5', '4', '0', '3', '2', '3', '6', '6', '3', '2', '4', '5', '4', '7', '5', '5', '0', '8', '5', '6', '9', '5', '4', '0', '0', '2', '5', '8', '4', '3', '8', '0', '1', '5', '4', '3', '1', '5', '2', '5', '3', '4', '0', '3', '9', '4', '7', '2', '1', '1', '8', '7', '6', '7', '4', '2', '5', '6', '5', '0', '7', '1', '3', '9', '6', '1', '8', '6', '3', '5', '9', '2', '1', '7', '0', '6', '0', '9', '6', '6', '7', '9', '1', '9', '5', '8', '8', '8', '6', '3', '5', '2', '9', '2', '6', '1', '7', '6', '7', '2', '2', '1', '5', '3', '9', '0', '5', '1', '7', '7', '8', '7', '8', '0', '7', '0', '1', '5', '9', '9', '4', '7', '9', '4', '6', '5', '0', '7', '4', '5', '4', '4', '2', '0', '5', '2', '8', '6', '7', '3']
noncomputable def geometryRow002_jensenBoundText : String := String.ofList (geometryRow002_jensenBoundNumeratorChars ++ '/' :: geometryRow002_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_jensenBound_before_field"
  err.flush

theorem geometryRow002_jensenBound_field :
    geometryRowsJson002.getObjVal? "jensen_bound" = .ok (.str geometryRow002_jensenBoundText) := by rfl

theorem geometryRow002_jensenBound_numerator_no_slash :
    geometryRow002_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow002_jensenBoundNumeratorChars = some (1182339544942268877390925393103421344558862766309751664034424625880089439547721196549926280062680553954089479800340457420089357352887544207549233208808992057727340576338933741773322899229534114044763205104549025162500000000000000000 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow002_jensenBoundDenominatorChars = some (111625353597125179210539736821571533771454336010782121170608959466048387038940405019989323380591436356363154032366324547550856954002584380154315253403947211876742565071396186359217060966791958886352926176722153905177878070159947946507454420528673 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_nonzero : (111625353597125179210539736821571533771454336010782121170608959466048387038940405019989323380591436356363154032366324547550856954002584380154315253403947211876742565071396186359217060966791958886352926176722153905177878070159947946507454420528673 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_jensenBound_parse :
    parseRational geometryRow002_jensenBoundText = .ok geometryRowsTyped002.jensenBound :=
  original_rational_fraction_of_chars geometryRow002_jensenBoundNumeratorChars geometryRow002_jensenBoundDenominatorChars
    (1182339544942268877390925393103421344558862766309751664034424625880089439547721196549926280062680553954089479800340457420089357352887544207549233208808992057727340576338933741773322899229534114044763205104549025162500000000000000000 : Int) (111625353597125179210539736821571533771454336010782121170608959466048387038940405019989323380591436356363154032366324547550856954002584380154315253403947211876742565071396186359217060966791958886352926176722153905177878070159947946507454420528673 : Int)
    geometryRow002_jensenBound_numerator_no_slash geometryRow002_jensenBound_numerator_parse
    geometryRow002_jensenBound_denominator_parse geometryRow002_jensenBound_denominator_nonzero

theorem geometryRow002_jensenBound_read :
    rationalField geometryRowsJson002 "jensen_bound" = .ok geometryRowsTyped002.jensenBound :=
  original_rationalField_of_string geometryRowsJson002 "jensen_bound" geometryRow002_jensenBoundText
    geometryRowsTyped002.jensenBound geometryRow002_jensenBound_field geometryRow002_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_factorMaxima_before"
  err.flush

theorem geometryRow002_factorMaxima_read :
    rationalArrayField geometryRowsJson002 "factor_maxima" = .ok geometryRowsTyped002.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_gapWeightedMeans_before"
  err.flush

theorem geometryRow002_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson002 "gap_weighted_means" = .ok geometryRowsTyped002.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow002_floorChars : List Char := ['8', '3', '9', '1', '8', '7', '3', '9', '4', '2', '1', '7', '0', '4', '2']
noncomputable def geometryRow002_floorText : String := String.ofList geometryRow002_floorChars

theorem geometryRow002_floor_text_read :
    geometryRowsJson002.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow002_floorText := by rfl

theorem geometryRow002_floor_chars_parse :
    SourceJson.intChars geometryRow002_floorChars = some (839187394217042 : Int) := by decide +kernel

theorem geometryRow002_floor_parse :
    parseInteger geometryRow002_floorText = .ok geometryRowsTyped002.jensenFloorQ96 := by
  simp only [geometryRow002_floorText, parseInteger, String.toList_ofList, geometryRow002_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_002 :
    decodeGeometryRow geometryRowsJson002 = .ok geometryRowsTyped002 :=
  original_geometryRow_of_fields geometryRowsJson002 geometryRowsTyped002 geometryRow002_floorText
    geometryRow002_simplexId_read geometryRow002_vertexIds_read
    geometryRow002_physicalVolume_read geometryRow002_meanGap_read
    geometryRow002_factorMaxima_read geometryRow002_gapWeightedMeans_read
    geometryRow002_jensenBound_read geometryRow002_floor_text_read geometryRow002_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_002_original_decoder_complete"
  err.flush

theorem geometryRow002_shape :
    geometryRowsTyped002.simplexId = 2 ∧
    geometryRowsTyped002.vertexIds.size = 9 ∧ geometryRowsTyped002.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped002.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped002.factorMaxima.size = 10 ∧ geometryRowsTyped002.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson003 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped003 : GeometryRow :=
  { simplexId := 3,
    vertexIds := #[32, 20, 18, 16, 15, 4, 2, 1, 0],
    physicalVolume := ((55428205353516969580705789680552242733001 : ℚ) / (269551868658057216000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1133902280579 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((195495828929122422770964593 : ℚ) / (2176021521397901192400000000 : ℚ)), ((336757974052920597530911 : ℚ) / (3614653690029736200000000 : ℚ)), ((41295255160847382258392069 : ℚ) / (362670253566316865400000000 : ℚ)), ((9558528699321211710127441 : ℚ) / (108801076069895059620000000 : ℚ)), ((94593709648486027549056161 : ℚ) / (1088010760698950596200000000 : ℚ)), ((1231935780655891481619259 : ℚ) / (16485011525741675700000000 : ℚ)), ((1793983523406519827666101 : ℚ) / (49455034577225027100000000 : ℚ)), ((3567227945355478287279287 : ℚ) / (98910069154450054200000000 : ℚ)), ((3567221351350867990609007 : ℚ) / (98910069154450054200000000 : ℚ)), ((59028448441174758335113 : ℚ) / (1807326845014868100000000 : ℚ))],
    jensenBound := ((11828569101731374487125909104054548610073621106282243505485889152306535568988507454594015922820135710506183426512367926267769698740430069292997456182044979264888679195403262394713177051853783509074212503867799174072265625000000000 : ℚ) / (4080728030558730132662446622122233230503128229111062506690990269058172066417130117442948715349349035187163920373917771454887085451806610693983191427965630927837988994590424556782230787250427823351331837207916969700258953627353370093058261044442061 : ℚ)),
    jensenFloorQ96 := (229654068608 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_simplexId_before"
  err.flush

theorem geometryRow003_simplexId_read :
    geometryRowsJson003.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped003.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_vertexIds_before"
  err.flush

theorem geometryRow003_vertexIds_read :
    geometryRowsJson003.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped003.vertexIds := by decide +kernel

noncomputable def geometryRow003_physicalVolumeNumeratorChars : List Char := ['5', '5', '4', '2', '8', '2', '0', '5', '3', '5', '3', '5', '1', '6', '9', '6', '9', '5', '8', '0', '7', '0', '5', '7', '8', '9', '6', '8', '0', '5', '5', '2', '2', '4', '2', '7', '3', '3', '0', '0', '1']
noncomputable def geometryRow003_physicalVolumeDenominatorChars : List Char := ['2', '6', '9', '5', '5', '1', '8', '6', '8', '6', '5', '8', '0', '5', '7', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_physicalVolumeText : String := String.ofList (geometryRow003_physicalVolumeNumeratorChars ++ '/' :: geometryRow003_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_physicalVolume_before_field"
  err.flush

theorem geometryRow003_physicalVolume_field :
    geometryRowsJson003.getObjVal? "physical_volume" = .ok (.str geometryRow003_physicalVolumeText) := by rfl

theorem geometryRow003_physicalVolume_numerator_no_slash :
    geometryRow003_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeNumeratorChars = some (55428205353516969580705789680552242733001 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeDenominatorChars = some (269551868658057216000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_nonzero : (269551868658057216000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_physicalVolume_parse :
    parseRational geometryRow003_physicalVolumeText = .ok geometryRowsTyped003.physicalVolume :=
  original_rational_fraction_of_chars geometryRow003_physicalVolumeNumeratorChars geometryRow003_physicalVolumeDenominatorChars
    (55428205353516969580705789680552242733001 : Int) (269551868658057216000000000000000000000000000000000000000000000000000 : Int)
    geometryRow003_physicalVolume_numerator_no_slash geometryRow003_physicalVolume_numerator_parse
    geometryRow003_physicalVolume_denominator_parse geometryRow003_physicalVolume_denominator_nonzero

theorem geometryRow003_physicalVolume_read :
    rationalField geometryRowsJson003 "physical_volume" = .ok geometryRowsTyped003.physicalVolume :=
  original_rationalField_of_string geometryRowsJson003 "physical_volume" geometryRow003_physicalVolumeText
    geometryRowsTyped003.physicalVolume geometryRow003_physicalVolume_field geometryRow003_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_physicalVolume_complete"
  err.flush

noncomputable def geometryRow003_meanGapNumeratorChars : List Char := ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9']
noncomputable def geometryRow003_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_meanGapText : String := String.ofList (geometryRow003_meanGapNumeratorChars ++ '/' :: geometryRow003_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_meanGap_before_field"
  err.flush

theorem geometryRow003_meanGap_field :
    geometryRowsJson003.getObjVal? "mean_gap" = .ok (.str geometryRow003_meanGapText) := by rfl

theorem geometryRow003_meanGap_numerator_no_slash :
    geometryRow003_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_meanGap_numerator_parse :
    SourceJson.intChars geometryRow003_meanGapNumeratorChars = some (1133902280579 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_parse :
    SourceJson.intChars geometryRow003_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_meanGap_parse :
    parseRational geometryRow003_meanGapText = .ok geometryRowsTyped003.meanGap :=
  original_rational_fraction_of_chars geometryRow003_meanGapNumeratorChars geometryRow003_meanGapDenominatorChars
    (1133902280579 : Int) (383811120000000 : Int)
    geometryRow003_meanGap_numerator_no_slash geometryRow003_meanGap_numerator_parse
    geometryRow003_meanGap_denominator_parse geometryRow003_meanGap_denominator_nonzero

theorem geometryRow003_meanGap_read :
    rationalField geometryRowsJson003 "mean_gap" = .ok geometryRowsTyped003.meanGap :=
  original_rationalField_of_string geometryRowsJson003 "mean_gap" geometryRow003_meanGapText
    geometryRowsTyped003.meanGap geometryRow003_meanGap_field geometryRow003_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_meanGap_complete"
  err.flush

noncomputable def geometryRow003_jensenBoundNumeratorChars : List Char := ['1', '1', '8', '2', '8', '5', '6', '9', '1', '0', '1', '7', '3', '1', '3', '7', '4', '4', '8', '7', '1', '2', '5', '9', '0', '9', '1', '0', '4', '0', '5', '4', '5', '4', '8', '6', '1', '0', '0', '7', '3', '6', '2', '1', '1', '0', '6', '2', '8', '2', '2', '4', '3', '5', '0', '5', '4', '8', '5', '8', '8', '9', '1', '5', '2', '3', '0', '6', '5', '3', '5', '5', '6', '8', '9', '8', '8', '5', '0', '7', '4', '5', '4', '5', '9', '4', '0', '1', '5', '9', '2', '2', '8', '2', '0', '1', '3', '5', '7', '1', '0', '5', '0', '6', '1', '8', '3', '4', '2', '6', '5', '1', '2', '3', '6', '7', '9', '2', '6', '2', '6', '7', '7', '6', '9', '6', '9', '8', '7', '4', '0', '4', '3', '0', '0', '6', '9', '2', '9', '2', '9', '9', '7', '4', '5', '6', '1', '8', '2', '0', '4', '4', '9', '7', '9', '2', '6', '4', '8', '8', '8', '6', '7', '9', '1', '9', '5', '4', '0', '3', '2', '6', '2', '3', '9', '4', '7', '1', '3', '1', '7', '7', '0', '5', '1', '8', '5', '3', '7', '8', '3', '5', '0', '9', '0', '7', '4', '2', '1', '2', '5', '0', '3', '8', '6', '7', '7', '9', '9', '1', '7', '4', '0', '7', '2', '2', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_jensenBoundDenominatorChars : List Char := ['4', '0', '8', '0', '7', '2', '8', '0', '3', '0', '5', '5', '8', '7', '3', '0', '1', '3', '2', '6', '6', '2', '4', '4', '6', '6', '2', '2', '1', '2', '2', '2', '3', '3', '2', '3', '0', '5', '0', '3', '1', '2', '8', '2', '2', '9', '1', '1', '1', '0', '6', '2', '5', '0', '6', '6', '9', '0', '9', '9', '0', '2', '6', '9', '0', '5', '8', '1', '7', '2', '0', '6', '6', '4', '1', '7', '1', '3', '0', '1', '1', '7', '4', '4', '2', '9', '4', '8', '7', '1', '5', '3', '4', '9', '3', '4', '9', '0', '3', '5', '1', '8', '7', '1', '6', '3', '9', '2', '0', '3', '7', '3', '9', '1', '7', '7', '7', '1', '4', '5', '4', '8', '8', '7', '0', '8', '5', '4', '5', '1', '8', '0', '6', '6', '1', '0', '6', '9', '3', '9', '8', '3', '1', '9', '1', '4', '2', '7', '9', '6', '5', '6', '3', '0', '9', '2', '7', '8', '3', '7', '9', '8', '8', '9', '9', '4', '5', '9', '0', '4', '2', '4', '5', '5', '6', '7', '8', '2', '2', '3', '0', '7', '8', '7', '2', '5', '0', '4', '2', '7', '8', '2', '3', '3', '5', '1', '3', '3', '1', '8', '3', '7', '2', '0', '7', '9', '1', '6', '9', '6', '9', '7', '0', '0', '2', '5', '8', '9', '5', '3', '6', '2', '7', '3', '5', '3', '3', '7', '0', '0', '9', '3', '0', '5', '8', '2', '6', '1', '0', '4', '4', '4', '4', '2', '0', '6', '1']
noncomputable def geometryRow003_jensenBoundText : String := String.ofList (geometryRow003_jensenBoundNumeratorChars ++ '/' :: geometryRow003_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_jensenBound_before_field"
  err.flush

theorem geometryRow003_jensenBound_field :
    geometryRowsJson003.getObjVal? "jensen_bound" = .ok (.str geometryRow003_jensenBoundText) := by rfl

theorem geometryRow003_jensenBound_numerator_no_slash :
    geometryRow003_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow003_jensenBoundNumeratorChars = some (11828569101731374487125909104054548610073621106282243505485889152306535568988507454594015922820135710506183426512367926267769698740430069292997456182044979264888679195403262394713177051853783509074212503867799174072265625000000000 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow003_jensenBoundDenominatorChars = some (4080728030558730132662446622122233230503128229111062506690990269058172066417130117442948715349349035187163920373917771454887085451806610693983191427965630927837988994590424556782230787250427823351331837207916969700258953627353370093058261044442061 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_nonzero : (4080728030558730132662446622122233230503128229111062506690990269058172066417130117442948715349349035187163920373917771454887085451806610693983191427965630927837988994590424556782230787250427823351331837207916969700258953627353370093058261044442061 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_jensenBound_parse :
    parseRational geometryRow003_jensenBoundText = .ok geometryRowsTyped003.jensenBound :=
  original_rational_fraction_of_chars geometryRow003_jensenBoundNumeratorChars geometryRow003_jensenBoundDenominatorChars
    (11828569101731374487125909104054548610073621106282243505485889152306535568988507454594015922820135710506183426512367926267769698740430069292997456182044979264888679195403262394713177051853783509074212503867799174072265625000000000 : Int) (4080728030558730132662446622122233230503128229111062506690990269058172066417130117442948715349349035187163920373917771454887085451806610693983191427965630927837988994590424556782230787250427823351331837207916969700258953627353370093058261044442061 : Int)
    geometryRow003_jensenBound_numerator_no_slash geometryRow003_jensenBound_numerator_parse
    geometryRow003_jensenBound_denominator_parse geometryRow003_jensenBound_denominator_nonzero

theorem geometryRow003_jensenBound_read :
    rationalField geometryRowsJson003 "jensen_bound" = .ok geometryRowsTyped003.jensenBound :=
  original_rationalField_of_string geometryRowsJson003 "jensen_bound" geometryRow003_jensenBoundText
    geometryRowsTyped003.jensenBound geometryRow003_jensenBound_field geometryRow003_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_factorMaxima_before"
  err.flush

theorem geometryRow003_factorMaxima_read :
    rationalArrayField geometryRowsJson003 "factor_maxima" = .ok geometryRowsTyped003.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_gapWeightedMeans_before"
  err.flush

theorem geometryRow003_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson003 "gap_weighted_means" = .ok geometryRowsTyped003.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow003_floorChars : List Char := ['2', '2', '9', '6', '5', '4', '0', '6', '8', '6', '0', '8']
noncomputable def geometryRow003_floorText : String := String.ofList geometryRow003_floorChars

theorem geometryRow003_floor_text_read :
    geometryRowsJson003.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow003_floorText := by rfl

theorem geometryRow003_floor_chars_parse :
    SourceJson.intChars geometryRow003_floorChars = some (229654068608 : Int) := by decide +kernel

theorem geometryRow003_floor_parse :
    parseInteger geometryRow003_floorText = .ok geometryRowsTyped003.jensenFloorQ96 := by
  simp only [geometryRow003_floorText, parseInteger, String.toList_ofList, geometryRow003_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_003 :
    decodeGeometryRow geometryRowsJson003 = .ok geometryRowsTyped003 :=
  original_geometryRow_of_fields geometryRowsJson003 geometryRowsTyped003 geometryRow003_floorText
    geometryRow003_simplexId_read geometryRow003_vertexIds_read
    geometryRow003_physicalVolume_read geometryRow003_meanGap_read
    geometryRow003_factorMaxima_read geometryRow003_gapWeightedMeans_read
    geometryRow003_jensenBound_read geometryRow003_floor_text_read geometryRow003_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_003_original_decoder_complete"
  err.flush

theorem geometryRow003_shape :
    geometryRowsTyped003.simplexId = 3 ∧
    geometryRowsTyped003.vertexIds.size = 9 ∧ geometryRowsTyped003.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped003.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped003.factorMaxima.size = 10 ∧ geometryRowsTyped003.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson004 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped004 : GeometryRow :=
  { simplexId := 4,
    vertexIds := #[32, 20, 18, 16, 15, 13, 4, 1, 0],
    physicalVolume := ((49881683166095527920034541501119123323251 : ℚ) / (26802032394977280000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((17343416107884222166117 : ℚ) / (191824961479559100000000 : ℚ)), ((29652560590227484289 : ℚ) / (318646115414550000000 : ℚ)), ((672882901075754816568379 : ℚ) / (5882632152039812400000000 : ℚ)), ((307257261832930870642507 : ℚ) / (3529579291223887440000000 : ℚ)), ((1520202594793375382063341 : ℚ) / (17647896456119437200000000 : ℚ)), ((40137392501974665915223 : ℚ) / (534784741094528400000000 : ℚ)), ((29279062744055087130431 : ℚ) / (802177111641792600000000 : ℚ)), ((7274838369171598111109 : ℚ) / (200544277910448150000000 : ℚ)), ((7274824999553070747899 : ℚ) / (200544277910448150000000 : ℚ)), ((41583414521388374731 : ℚ) / (1274584461658200000000 : ℚ))],
    jensenBound := ((734777948718105757720090944251730597724526409826706387139136235451162805813545686212390905154128524440313698944405653126624100350643536842940233046441350880207572709416775086423521228956250000000000000000 : ℚ) / (38003154837465728638930901108449572918311396882158238205236090775178428325152460062347401759550448955860839127089883502838821099269501990557281529094490409417733165984886839243358306194822269103734371990924228217125562807 : ℚ)),
    jensenFloorQ96 := (1531849315719 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_simplexId_before"
  err.flush

theorem geometryRow004_simplexId_read :
    geometryRowsJson004.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped004.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_vertexIds_before"
  err.flush

theorem geometryRow004_vertexIds_read :
    geometryRowsJson004.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped004.vertexIds := by decide +kernel

noncomputable def geometryRow004_physicalVolumeNumeratorChars : List Char := ['4', '9', '8', '8', '1', '6', '8', '3', '1', '6', '6', '0', '9', '5', '5', '2', '7', '9', '2', '0', '0', '3', '4', '5', '4', '1', '5', '0', '1', '1', '1', '9', '1', '2', '3', '3', '2', '3', '2', '5', '1']
noncomputable def geometryRow004_physicalVolumeDenominatorChars : List Char := ['2', '6', '8', '0', '2', '0', '3', '2', '3', '9', '4', '9', '7', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_physicalVolumeText : String := String.ofList (geometryRow004_physicalVolumeNumeratorChars ++ '/' :: geometryRow004_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_physicalVolume_before_field"
  err.flush

theorem geometryRow004_physicalVolume_field :
    geometryRowsJson004.getObjVal? "physical_volume" = .ok (.str geometryRow004_physicalVolumeText) := by rfl

theorem geometryRow004_physicalVolume_numerator_no_slash :
    geometryRow004_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeNumeratorChars = some (49881683166095527920034541501119123323251 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeDenominatorChars = some (26802032394977280000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_nonzero : (26802032394977280000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_physicalVolume_parse :
    parseRational geometryRow004_physicalVolumeText = .ok geometryRowsTyped004.physicalVolume :=
  original_rational_fraction_of_chars geometryRow004_physicalVolumeNumeratorChars geometryRow004_physicalVolumeDenominatorChars
    (49881683166095527920034541501119123323251 : Int) (26802032394977280000000000000000000000000000000000000000000000000000 : Int)
    geometryRow004_physicalVolume_numerator_no_slash geometryRow004_physicalVolume_numerator_parse
    geometryRow004_physicalVolume_denominator_parse geometryRow004_physicalVolume_denominator_nonzero

theorem geometryRow004_physicalVolume_read :
    rationalField geometryRowsJson004 "physical_volume" = .ok geometryRowsTyped004.physicalVolume :=
  original_rationalField_of_string geometryRowsJson004 "physical_volume" geometryRow004_physicalVolumeText
    geometryRowsTyped004.physicalVolume geometryRow004_physicalVolume_field geometryRow004_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_physicalVolume_complete"
  err.flush

noncomputable def geometryRow004_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow004_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_meanGapText : String := String.ofList (geometryRow004_meanGapNumeratorChars ++ '/' :: geometryRow004_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_meanGap_before_field"
  err.flush

theorem geometryRow004_meanGap_field :
    geometryRowsJson004.getObjVal? "mean_gap" = .ok (.str geometryRow004_meanGapText) := by rfl

theorem geometryRow004_meanGap_numerator_no_slash :
    geometryRow004_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_meanGap_numerator_parse :
    SourceJson.intChars geometryRow004_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_parse :
    SourceJson.intChars geometryRow004_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_meanGap_parse :
    parseRational geometryRow004_meanGapText = .ok geometryRowsTyped004.meanGap :=
  original_rational_fraction_of_chars geometryRow004_meanGapNumeratorChars geometryRow004_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow004_meanGap_numerator_no_slash geometryRow004_meanGap_numerator_parse
    geometryRow004_meanGap_denominator_parse geometryRow004_meanGap_denominator_nonzero

theorem geometryRow004_meanGap_read :
    rationalField geometryRowsJson004 "mean_gap" = .ok geometryRowsTyped004.meanGap :=
  original_rationalField_of_string geometryRowsJson004 "mean_gap" geometryRow004_meanGapText
    geometryRowsTyped004.meanGap geometryRow004_meanGap_field geometryRow004_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_meanGap_complete"
  err.flush

noncomputable def geometryRow004_jensenBoundNumeratorChars : List Char := ['7', '3', '4', '7', '7', '7', '9', '4', '8', '7', '1', '8', '1', '0', '5', '7', '5', '7', '7', '2', '0', '0', '9', '0', '9', '4', '4', '2', '5', '1', '7', '3', '0', '5', '9', '7', '7', '2', '4', '5', '2', '6', '4', '0', '9', '8', '2', '6', '7', '0', '6', '3', '8', '7', '1', '3', '9', '1', '3', '6', '2', '3', '5', '4', '5', '1', '1', '6', '2', '8', '0', '5', '8', '1', '3', '5', '4', '5', '6', '8', '6', '2', '1', '2', '3', '9', '0', '9', '0', '5', '1', '5', '4', '1', '2', '8', '5', '2', '4', '4', '4', '0', '3', '1', '3', '6', '9', '8', '9', '4', '4', '4', '0', '5', '6', '5', '3', '1', '2', '6', '6', '2', '4', '1', '0', '0', '3', '5', '0', '6', '4', '3', '5', '3', '6', '8', '4', '2', '9', '4', '0', '2', '3', '3', '0', '4', '6', '4', '4', '1', '3', '5', '0', '8', '8', '0', '2', '0', '7', '5', '7', '2', '7', '0', '9', '4', '1', '6', '7', '7', '5', '0', '8', '6', '4', '2', '3', '5', '2', '1', '2', '2', '8', '9', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_jensenBoundDenominatorChars : List Char := ['3', '8', '0', '0', '3', '1', '5', '4', '8', '3', '7', '4', '6', '5', '7', '2', '8', '6', '3', '8', '9', '3', '0', '9', '0', '1', '1', '0', '8', '4', '4', '9', '5', '7', '2', '9', '1', '8', '3', '1', '1', '3', '9', '6', '8', '8', '2', '1', '5', '8', '2', '3', '8', '2', '0', '5', '2', '3', '6', '0', '9', '0', '7', '7', '5', '1', '7', '8', '4', '2', '8', '3', '2', '5', '1', '5', '2', '4', '6', '0', '0', '6', '2', '3', '4', '7', '4', '0', '1', '7', '5', '9', '5', '5', '0', '4', '4', '8', '9', '5', '5', '8', '6', '0', '8', '3', '9', '1', '2', '7', '0', '8', '9', '8', '8', '3', '5', '0', '2', '8', '3', '8', '8', '2', '1', '0', '9', '9', '2', '6', '9', '5', '0', '1', '9', '9', '0', '5', '5', '7', '2', '8', '1', '5', '2', '9', '0', '9', '4', '4', '9', '0', '4', '0', '9', '4', '1', '7', '7', '3', '3', '1', '6', '5', '9', '8', '4', '8', '8', '6', '8', '3', '9', '2', '4', '3', '3', '5', '8', '3', '0', '6', '1', '9', '4', '8', '2', '2', '2', '6', '9', '1', '0', '3', '7', '3', '4', '3', '7', '1', '9', '9', '0', '9', '2', '4', '2', '2', '8', '2', '1', '7', '1', '2', '5', '5', '6', '2', '8', '0', '7']
noncomputable def geometryRow004_jensenBoundText : String := String.ofList (geometryRow004_jensenBoundNumeratorChars ++ '/' :: geometryRow004_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_jensenBound_before_field"
  err.flush

theorem geometryRow004_jensenBound_field :
    geometryRowsJson004.getObjVal? "jensen_bound" = .ok (.str geometryRow004_jensenBoundText) := by rfl

theorem geometryRow004_jensenBound_numerator_no_slash :
    geometryRow004_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow004_jensenBoundNumeratorChars = some (734777948718105757720090944251730597724526409826706387139136235451162805813545686212390905154128524440313698944405653126624100350643536842940233046441350880207572709416775086423521228956250000000000000000 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow004_jensenBoundDenominatorChars = some (38003154837465728638930901108449572918311396882158238205236090775178428325152460062347401759550448955860839127089883502838821099269501990557281529094490409417733165984886839243358306194822269103734371990924228217125562807 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_nonzero : (38003154837465728638930901108449572918311396882158238205236090775178428325152460062347401759550448955860839127089883502838821099269501990557281529094490409417733165984886839243358306194822269103734371990924228217125562807 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_jensenBound_parse :
    parseRational geometryRow004_jensenBoundText = .ok geometryRowsTyped004.jensenBound :=
  original_rational_fraction_of_chars geometryRow004_jensenBoundNumeratorChars geometryRow004_jensenBoundDenominatorChars
    (734777948718105757720090944251730597724526409826706387139136235451162805813545686212390905154128524440313698944405653126624100350643536842940233046441350880207572709416775086423521228956250000000000000000 : Int) (38003154837465728638930901108449572918311396882158238205236090775178428325152460062347401759550448955860839127089883502838821099269501990557281529094490409417733165984886839243358306194822269103734371990924228217125562807 : Int)
    geometryRow004_jensenBound_numerator_no_slash geometryRow004_jensenBound_numerator_parse
    geometryRow004_jensenBound_denominator_parse geometryRow004_jensenBound_denominator_nonzero

theorem geometryRow004_jensenBound_read :
    rationalField geometryRowsJson004 "jensen_bound" = .ok geometryRowsTyped004.jensenBound :=
  original_rationalField_of_string geometryRowsJson004 "jensen_bound" geometryRow004_jensenBoundText
    geometryRowsTyped004.jensenBound geometryRow004_jensenBound_field geometryRow004_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_factorMaxima_before"
  err.flush

theorem geometryRow004_factorMaxima_read :
    rationalArrayField geometryRowsJson004 "factor_maxima" = .ok geometryRowsTyped004.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_gapWeightedMeans_before"
  err.flush

theorem geometryRow004_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson004 "gap_weighted_means" = .ok geometryRowsTyped004.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow004_floorChars : List Char := ['1', '5', '3', '1', '8', '4', '9', '3', '1', '5', '7', '1', '9']
noncomputable def geometryRow004_floorText : String := String.ofList geometryRow004_floorChars

theorem geometryRow004_floor_text_read :
    geometryRowsJson004.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow004_floorText := by rfl

theorem geometryRow004_floor_chars_parse :
    SourceJson.intChars geometryRow004_floorChars = some (1531849315719 : Int) := by decide +kernel

theorem geometryRow004_floor_parse :
    parseInteger geometryRow004_floorText = .ok geometryRowsTyped004.jensenFloorQ96 := by
  simp only [geometryRow004_floorText, parseInteger, String.toList_ofList, geometryRow004_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_004 :
    decodeGeometryRow geometryRowsJson004 = .ok geometryRowsTyped004 :=
  original_geometryRow_of_fields geometryRowsJson004 geometryRowsTyped004 geometryRow004_floorText
    geometryRow004_simplexId_read geometryRow004_vertexIds_read
    geometryRow004_physicalVolume_read geometryRow004_meanGap_read
    geometryRow004_factorMaxima_read geometryRow004_gapWeightedMeans_read
    geometryRow004_jensenBound_read geometryRow004_floor_text_read geometryRow004_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_004_original_decoder_complete"
  err.flush

theorem geometryRow004_shape :
    geometryRowsTyped004.simplexId = 4 ∧
    geometryRowsTyped004.vertexIds.size = 9 ∧ geometryRowsTyped004.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped004.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped004.factorMaxima.size = 10 ∧ geometryRowsTyped004.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson005 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped005 : GeometryRow :=
  { simplexId := 5,
    vertexIds := #[32, 20, 18, 16, 15, 13, 10, 1, 0],
    physicalVolume := ((913941895485176839151001595876765325284663 : ℚ) / (41138003210895360000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((6331744974624141533 : ℚ) / (69547442787900000000 : ℚ)), ((462177696644104303 : ℚ) / (4967674484850000000 : ℚ)), ((81616568402294651427 : ℚ) / (710929415165200000000 : ℚ)), ((110277620580575138093 : ℚ) / (1279672947297360000000 : ℚ)), ((545556843006219094679 : ℚ) / (6398364736486800000000 : ℚ)), ((4912427459791374139 : ℚ) / (64629946833200000000 : ℚ)), ((5521126807618230227 : ℚ) / (145417380374700000000 : ℚ)), ((2600258715623366041 : ℚ) / (72708690187350000000 : ℚ)), ((2600253868377353551 : ℚ) / (72708690187350000000 : ℚ)), ((648144349911862697 : ℚ) / (19870697939400000000 : ℚ))],
    jensenBound := ((607758917343146384987029646888020987182868976973907450271646993092877728684927749934220122708929000997882587743698565155825548747433392693702878869521439062500000000000000 : ℚ) / (3981151961185016467108857446511725335795344141599583568324062530971549851350353773345106588007569868173191338667492834239445902259658422223601477111703328921223667460004027533842276326609 : ℚ)),
    jensenFloorQ96 := (12094896839462 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_simplexId_before"
  err.flush

theorem geometryRow005_simplexId_read :
    geometryRowsJson005.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped005.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_vertexIds_before"
  err.flush

theorem geometryRow005_vertexIds_read :
    geometryRowsJson005.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped005.vertexIds := by decide +kernel

noncomputable def geometryRow005_physicalVolumeNumeratorChars : List Char := ['9', '1', '3', '9', '4', '1', '8', '9', '5', '4', '8', '5', '1', '7', '6', '8', '3', '9', '1', '5', '1', '0', '0', '1', '5', '9', '5', '8', '7', '6', '7', '6', '5', '3', '2', '5', '2', '8', '4', '6', '6', '3']
noncomputable def geometryRow005_physicalVolumeDenominatorChars : List Char := ['4', '1', '1', '3', '8', '0', '0', '3', '2', '1', '0', '8', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_physicalVolumeText : String := String.ofList (geometryRow005_physicalVolumeNumeratorChars ++ '/' :: geometryRow005_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_physicalVolume_before_field"
  err.flush

theorem geometryRow005_physicalVolume_field :
    geometryRowsJson005.getObjVal? "physical_volume" = .ok (.str geometryRow005_physicalVolumeText) := by rfl

theorem geometryRow005_physicalVolume_numerator_no_slash :
    geometryRow005_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeNumeratorChars = some (913941895485176839151001595876765325284663 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeDenominatorChars = some (41138003210895360000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_nonzero : (41138003210895360000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_physicalVolume_parse :
    parseRational geometryRow005_physicalVolumeText = .ok geometryRowsTyped005.physicalVolume :=
  original_rational_fraction_of_chars geometryRow005_physicalVolumeNumeratorChars geometryRow005_physicalVolumeDenominatorChars
    (913941895485176839151001595876765325284663 : Int) (41138003210895360000000000000000000000000000000000000000000000000000 : Int)
    geometryRow005_physicalVolume_numerator_no_slash geometryRow005_physicalVolume_numerator_parse
    geometryRow005_physicalVolume_denominator_parse geometryRow005_physicalVolume_denominator_nonzero

theorem geometryRow005_physicalVolume_read :
    rationalField geometryRowsJson005 "physical_volume" = .ok geometryRowsTyped005.physicalVolume :=
  original_rationalField_of_string geometryRowsJson005 "physical_volume" geometryRow005_physicalVolumeText
    geometryRowsTyped005.physicalVolume geometryRow005_physicalVolume_field geometryRow005_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_physicalVolume_complete"
  err.flush

noncomputable def geometryRow005_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow005_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_meanGapText : String := String.ofList (geometryRow005_meanGapNumeratorChars ++ '/' :: geometryRow005_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_meanGap_before_field"
  err.flush

theorem geometryRow005_meanGap_field :
    geometryRowsJson005.getObjVal? "mean_gap" = .ok (.str geometryRow005_meanGapText) := by rfl

theorem geometryRow005_meanGap_numerator_no_slash :
    geometryRow005_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_meanGap_numerator_parse :
    SourceJson.intChars geometryRow005_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_parse :
    SourceJson.intChars geometryRow005_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_meanGap_parse :
    parseRational geometryRow005_meanGapText = .ok geometryRowsTyped005.meanGap :=
  original_rational_fraction_of_chars geometryRow005_meanGapNumeratorChars geometryRow005_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow005_meanGap_numerator_no_slash geometryRow005_meanGap_numerator_parse
    geometryRow005_meanGap_denominator_parse geometryRow005_meanGap_denominator_nonzero

theorem geometryRow005_meanGap_read :
    rationalField geometryRowsJson005 "mean_gap" = .ok geometryRowsTyped005.meanGap :=
  original_rationalField_of_string geometryRowsJson005 "mean_gap" geometryRow005_meanGapText
    geometryRowsTyped005.meanGap geometryRow005_meanGap_field geometryRow005_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_meanGap_complete"
  err.flush

noncomputable def geometryRow005_jensenBoundNumeratorChars : List Char := ['6', '0', '7', '7', '5', '8', '9', '1', '7', '3', '4', '3', '1', '4', '6', '3', '8', '4', '9', '8', '7', '0', '2', '9', '6', '4', '6', '8', '8', '8', '0', '2', '0', '9', '8', '7', '1', '8', '2', '8', '6', '8', '9', '7', '6', '9', '7', '3', '9', '0', '7', '4', '5', '0', '2', '7', '1', '6', '4', '6', '9', '9', '3', '0', '9', '2', '8', '7', '7', '7', '2', '8', '6', '8', '4', '9', '2', '7', '7', '4', '9', '9', '3', '4', '2', '2', '0', '1', '2', '2', '7', '0', '8', '9', '2', '9', '0', '0', '0', '9', '9', '7', '8', '8', '2', '5', '8', '7', '7', '4', '3', '6', '9', '8', '5', '6', '5', '1', '5', '5', '8', '2', '5', '5', '4', '8', '7', '4', '7', '4', '3', '3', '3', '9', '2', '6', '9', '3', '7', '0', '2', '8', '7', '8', '8', '6', '9', '5', '2', '1', '4', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_jensenBoundDenominatorChars : List Char := ['3', '9', '8', '1', '1', '5', '1', '9', '6', '1', '1', '8', '5', '0', '1', '6', '4', '6', '7', '1', '0', '8', '8', '5', '7', '4', '4', '6', '5', '1', '1', '7', '2', '5', '3', '3', '5', '7', '9', '5', '3', '4', '4', '1', '4', '1', '5', '9', '9', '5', '8', '3', '5', '6', '8', '3', '2', '4', '0', '6', '2', '5', '3', '0', '9', '7', '1', '5', '4', '9', '8', '5', '1', '3', '5', '0', '3', '5', '3', '7', '7', '3', '3', '4', '5', '1', '0', '6', '5', '8', '8', '0', '0', '7', '5', '6', '9', '8', '6', '8', '1', '7', '3', '1', '9', '1', '3', '3', '8', '6', '6', '7', '4', '9', '2', '8', '3', '4', '2', '3', '9', '4', '4', '5', '9', '0', '2', '2', '5', '9', '6', '5', '8', '4', '2', '2', '2', '2', '3', '6', '0', '1', '4', '7', '7', '1', '1', '1', '7', '0', '3', '3', '2', '8', '9', '2', '1', '2', '2', '3', '6', '6', '7', '4', '6', '0', '0', '0', '4', '0', '2', '7', '5', '3', '3', '8', '4', '2', '2', '7', '6', '3', '2', '6', '6', '0', '9']
noncomputable def geometryRow005_jensenBoundText : String := String.ofList (geometryRow005_jensenBoundNumeratorChars ++ '/' :: geometryRow005_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_jensenBound_before_field"
  err.flush

theorem geometryRow005_jensenBound_field :
    geometryRowsJson005.getObjVal? "jensen_bound" = .ok (.str geometryRow005_jensenBoundText) := by rfl

theorem geometryRow005_jensenBound_numerator_no_slash :
    geometryRow005_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow005_jensenBoundNumeratorChars = some (607758917343146384987029646888020987182868976973907450271646993092877728684927749934220122708929000997882587743698565155825548747433392693702878869521439062500000000000000 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow005_jensenBoundDenominatorChars = some (3981151961185016467108857446511725335795344141599583568324062530971549851350353773345106588007569868173191338667492834239445902259658422223601477111703328921223667460004027533842276326609 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_nonzero : (3981151961185016467108857446511725335795344141599583568324062530971549851350353773345106588007569868173191338667492834239445902259658422223601477111703328921223667460004027533842276326609 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_jensenBound_parse :
    parseRational geometryRow005_jensenBoundText = .ok geometryRowsTyped005.jensenBound :=
  original_rational_fraction_of_chars geometryRow005_jensenBoundNumeratorChars geometryRow005_jensenBoundDenominatorChars
    (607758917343146384987029646888020987182868976973907450271646993092877728684927749934220122708929000997882587743698565155825548747433392693702878869521439062500000000000000 : Int) (3981151961185016467108857446511725335795344141599583568324062530971549851350353773345106588007569868173191338667492834239445902259658422223601477111703328921223667460004027533842276326609 : Int)
    geometryRow005_jensenBound_numerator_no_slash geometryRow005_jensenBound_numerator_parse
    geometryRow005_jensenBound_denominator_parse geometryRow005_jensenBound_denominator_nonzero

theorem geometryRow005_jensenBound_read :
    rationalField geometryRowsJson005 "jensen_bound" = .ok geometryRowsTyped005.jensenBound :=
  original_rationalField_of_string geometryRowsJson005 "jensen_bound" geometryRow005_jensenBoundText
    geometryRowsTyped005.jensenBound geometryRow005_jensenBound_field geometryRow005_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_factorMaxima_before"
  err.flush

theorem geometryRow005_factorMaxima_read :
    rationalArrayField geometryRowsJson005 "factor_maxima" = .ok geometryRowsTyped005.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_gapWeightedMeans_before"
  err.flush

theorem geometryRow005_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson005 "gap_weighted_means" = .ok geometryRowsTyped005.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow005_floorChars : List Char := ['1', '2', '0', '9', '4', '8', '9', '6', '8', '3', '9', '4', '6', '2']
noncomputable def geometryRow005_floorText : String := String.ofList geometryRow005_floorChars

theorem geometryRow005_floor_text_read :
    geometryRowsJson005.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow005_floorText := by rfl

theorem geometryRow005_floor_chars_parse :
    SourceJson.intChars geometryRow005_floorChars = some (12094896839462 : Int) := by decide +kernel

theorem geometryRow005_floor_parse :
    parseInteger geometryRow005_floorText = .ok geometryRowsTyped005.jensenFloorQ96 := by
  simp only [geometryRow005_floorText, parseInteger, String.toList_ofList, geometryRow005_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_005 :
    decodeGeometryRow geometryRowsJson005 = .ok geometryRowsTyped005 :=
  original_geometryRow_of_fields geometryRowsJson005 geometryRowsTyped005 geometryRow005_floorText
    geometryRow005_simplexId_read geometryRow005_vertexIds_read
    geometryRow005_physicalVolume_read geometryRow005_meanGap_read
    geometryRow005_factorMaxima_read geometryRow005_gapWeightedMeans_read
    geometryRow005_jensenBound_read geometryRow005_floor_text_read geometryRow005_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_005_original_decoder_complete"
  err.flush

theorem geometryRow005_shape :
    geometryRowsTyped005.simplexId = 5 ∧
    geometryRowsTyped005.vertexIds.size = 9 ∧ geometryRowsTyped005.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped005.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped005.factorMaxima.size = 10 ∧ geometryRowsTyped005.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson006 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped006 : GeometryRow :=
  { simplexId := 6,
    vertexIds := #[32, 20, 18, 16, 15, 13, 10, 8, 0],
    physicalVolume := ((20224469390439193837354029916149596273683243 : ℚ) / (90671517281157120000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((782655887 : ℚ) / (8662500000 : ℚ)), ((6352778599 : ℚ) / (69300000000 : ℚ)), ((2200047398753 : ℚ) / (19126800000000 : ℚ)), ((327088501151 : ℚ) / (3825360000000 : ℚ)), ((1618010967169 : ℚ) / (19126800000000 : ℚ)), ((134122522241 : ℚ) / (1738800000000 : ℚ)), ((2384939491 : ℚ) / (62100000000 : ℚ)), ((31691275739 : ℚ) / (869400000000 : ℚ)), ((31691217779 : ℚ) / (869400000000 : ℚ)), ((13373229049 : ℚ) / (415800000000 : ℚ))],
    jensenBound := ((130524932514469644279633823169076194311032177184918987198201956197865098437500000000000000 : ℚ) / (173928729258474738362131222980011548734674780675651605186833967928235054073319833733791168702802245189043 : ℚ)),
    jensenFloorQ96 := (59456828147417 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_simplexId_before"
  err.flush

theorem geometryRow006_simplexId_read :
    geometryRowsJson006.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped006.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_vertexIds_before"
  err.flush

theorem geometryRow006_vertexIds_read :
    geometryRowsJson006.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped006.vertexIds := by decide +kernel

noncomputable def geometryRow006_physicalVolumeNumeratorChars : List Char := ['2', '0', '2', '2', '4', '4', '6', '9', '3', '9', '0', '4', '3', '9', '1', '9', '3', '8', '3', '7', '3', '5', '4', '0', '2', '9', '9', '1', '6', '1', '4', '9', '5', '9', '6', '2', '7', '3', '6', '8', '3', '2', '4', '3']
noncomputable def geometryRow006_physicalVolumeDenominatorChars : List Char := ['9', '0', '6', '7', '1', '5', '1', '7', '2', '8', '1', '1', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_physicalVolumeText : String := String.ofList (geometryRow006_physicalVolumeNumeratorChars ++ '/' :: geometryRow006_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_physicalVolume_before_field"
  err.flush

theorem geometryRow006_physicalVolume_field :
    geometryRowsJson006.getObjVal? "physical_volume" = .ok (.str geometryRow006_physicalVolumeText) := by rfl

theorem geometryRow006_physicalVolume_numerator_no_slash :
    geometryRow006_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeNumeratorChars = some (20224469390439193837354029916149596273683243 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeDenominatorChars = some (90671517281157120000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_nonzero : (90671517281157120000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_physicalVolume_parse :
    parseRational geometryRow006_physicalVolumeText = .ok geometryRowsTyped006.physicalVolume :=
  original_rational_fraction_of_chars geometryRow006_physicalVolumeNumeratorChars geometryRow006_physicalVolumeDenominatorChars
    (20224469390439193837354029916149596273683243 : Int) (90671517281157120000000000000000000000000000000000000000000000000000 : Int)
    geometryRow006_physicalVolume_numerator_no_slash geometryRow006_physicalVolume_numerator_parse
    geometryRow006_physicalVolume_denominator_parse geometryRow006_physicalVolume_denominator_nonzero

theorem geometryRow006_physicalVolume_read :
    rationalField geometryRowsJson006 "physical_volume" = .ok geometryRowsTyped006.physicalVolume :=
  original_rationalField_of_string geometryRowsJson006 "physical_volume" geometryRow006_physicalVolumeText
    geometryRowsTyped006.physicalVolume geometryRow006_physicalVolume_field geometryRow006_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_physicalVolume_complete"
  err.flush

noncomputable def geometryRow006_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow006_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_meanGapText : String := String.ofList (geometryRow006_meanGapNumeratorChars ++ '/' :: geometryRow006_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_meanGap_before_field"
  err.flush

theorem geometryRow006_meanGap_field :
    geometryRowsJson006.getObjVal? "mean_gap" = .ok (.str geometryRow006_meanGapText) := by rfl

theorem geometryRow006_meanGap_numerator_no_slash :
    geometryRow006_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_meanGap_numerator_parse :
    SourceJson.intChars geometryRow006_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_parse :
    SourceJson.intChars geometryRow006_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_meanGap_parse :
    parseRational geometryRow006_meanGapText = .ok geometryRowsTyped006.meanGap :=
  original_rational_fraction_of_chars geometryRow006_meanGapNumeratorChars geometryRow006_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow006_meanGap_numerator_no_slash geometryRow006_meanGap_numerator_parse
    geometryRow006_meanGap_denominator_parse geometryRow006_meanGap_denominator_nonzero

theorem geometryRow006_meanGap_read :
    rationalField geometryRowsJson006 "mean_gap" = .ok geometryRowsTyped006.meanGap :=
  original_rationalField_of_string geometryRowsJson006 "mean_gap" geometryRow006_meanGapText
    geometryRowsTyped006.meanGap geometryRow006_meanGap_field geometryRow006_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_meanGap_complete"
  err.flush

noncomputable def geometryRow006_jensenBoundNumeratorChars : List Char := ['1', '3', '0', '5', '2', '4', '9', '3', '2', '5', '1', '4', '4', '6', '9', '6', '4', '4', '2', '7', '9', '6', '3', '3', '8', '2', '3', '1', '6', '9', '0', '7', '6', '1', '9', '4', '3', '1', '1', '0', '3', '2', '1', '7', '7', '1', '8', '4', '9', '1', '8', '9', '8', '7', '1', '9', '8', '2', '0', '1', '9', '5', '6', '1', '9', '7', '8', '6', '5', '0', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_jensenBoundDenominatorChars : List Char := ['1', '7', '3', '9', '2', '8', '7', '2', '9', '2', '5', '8', '4', '7', '4', '7', '3', '8', '3', '6', '2', '1', '3', '1', '2', '2', '2', '9', '8', '0', '0', '1', '1', '5', '4', '8', '7', '3', '4', '6', '7', '4', '7', '8', '0', '6', '7', '5', '6', '5', '1', '6', '0', '5', '1', '8', '6', '8', '3', '3', '9', '6', '7', '9', '2', '8', '2', '3', '5', '0', '5', '4', '0', '7', '3', '3', '1', '9', '8', '3', '3', '7', '3', '3', '7', '9', '1', '1', '6', '8', '7', '0', '2', '8', '0', '2', '2', '4', '5', '1', '8', '9', '0', '4', '3']
noncomputable def geometryRow006_jensenBoundText : String := String.ofList (geometryRow006_jensenBoundNumeratorChars ++ '/' :: geometryRow006_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_jensenBound_before_field"
  err.flush

theorem geometryRow006_jensenBound_field :
    geometryRowsJson006.getObjVal? "jensen_bound" = .ok (.str geometryRow006_jensenBoundText) := by rfl

theorem geometryRow006_jensenBound_numerator_no_slash :
    geometryRow006_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow006_jensenBoundNumeratorChars = some (130524932514469644279633823169076194311032177184918987198201956197865098437500000000000000 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow006_jensenBoundDenominatorChars = some (173928729258474738362131222980011548734674780675651605186833967928235054073319833733791168702802245189043 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_nonzero : (173928729258474738362131222980011548734674780675651605186833967928235054073319833733791168702802245189043 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_jensenBound_parse :
    parseRational geometryRow006_jensenBoundText = .ok geometryRowsTyped006.jensenBound :=
  original_rational_fraction_of_chars geometryRow006_jensenBoundNumeratorChars geometryRow006_jensenBoundDenominatorChars
    (130524932514469644279633823169076194311032177184918987198201956197865098437500000000000000 : Int) (173928729258474738362131222980011548734674780675651605186833967928235054073319833733791168702802245189043 : Int)
    geometryRow006_jensenBound_numerator_no_slash geometryRow006_jensenBound_numerator_parse
    geometryRow006_jensenBound_denominator_parse geometryRow006_jensenBound_denominator_nonzero

theorem geometryRow006_jensenBound_read :
    rationalField geometryRowsJson006 "jensen_bound" = .ok geometryRowsTyped006.jensenBound :=
  original_rationalField_of_string geometryRowsJson006 "jensen_bound" geometryRow006_jensenBoundText
    geometryRowsTyped006.jensenBound geometryRow006_jensenBound_field geometryRow006_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_factorMaxima_before"
  err.flush

theorem geometryRow006_factorMaxima_read :
    rationalArrayField geometryRowsJson006 "factor_maxima" = .ok geometryRowsTyped006.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_gapWeightedMeans_before"
  err.flush

theorem geometryRow006_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson006 "gap_weighted_means" = .ok geometryRowsTyped006.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow006_floorChars : List Char := ['5', '9', '4', '5', '6', '8', '2', '8', '1', '4', '7', '4', '1', '7']
noncomputable def geometryRow006_floorText : String := String.ofList geometryRow006_floorChars

theorem geometryRow006_floor_text_read :
    geometryRowsJson006.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow006_floorText := by rfl

theorem geometryRow006_floor_chars_parse :
    SourceJson.intChars geometryRow006_floorChars = some (59456828147417 : Int) := by decide +kernel

theorem geometryRow006_floor_parse :
    parseInteger geometryRow006_floorText = .ok geometryRowsTyped006.jensenFloorQ96 := by
  simp only [geometryRow006_floorText, parseInteger, String.toList_ofList, geometryRow006_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_006 :
    decodeGeometryRow geometryRowsJson006 = .ok geometryRowsTyped006 :=
  original_geometryRow_of_fields geometryRowsJson006 geometryRowsTyped006 geometryRow006_floorText
    geometryRow006_simplexId_read geometryRow006_vertexIds_read
    geometryRow006_physicalVolume_read geometryRow006_meanGap_read
    geometryRow006_factorMaxima_read geometryRow006_gapWeightedMeans_read
    geometryRow006_jensenBound_read geometryRow006_floor_text_read geometryRow006_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_006_original_decoder_complete"
  err.flush

theorem geometryRow006_shape :
    geometryRowsTyped006.simplexId = 6 ∧
    geometryRowsTyped006.vertexIds.size = 9 ∧ geometryRowsTyped006.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped006.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped006.factorMaxima.size = 10 ∧ geometryRowsTyped006.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson007 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped007 : GeometryRow :=
  { simplexId := 7,
    vertexIds := #[32, 20, 18, 16, 14, 4, 3, 1, 0],
    physicalVolume := ((5591491845115233318513788757162050173497639167 : ℚ) / (937897262806597632000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1544234459 : ℚ) / (521482500000 : ℚ)),
    factorMaxima := #[((828113 : ℚ) / (8000000 : ℚ)), ((828113 : ℚ) / (8000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((1286441 : ℚ) / (16000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((390621 : ℚ) / (10000000 : ℚ)), ((1171843 : ℚ) / (30000000 : ℚ))],
    gapWeightedMeans := #[((1544094864824685613734689 : ℚ) / (17265444319931623200000000 : ℚ)), ((28600278370571013111031 : ℚ) / (308311505713064700000000 : ℚ)), ((245731533447416489806769 : ℚ) / (2158180539991452900000000 : ℚ)), ((151933235462353969265713 : ℚ) / (1726544431993162320000000 : ℚ)), ((250599532432208527431161 : ℚ) / (2877574053321937200000000 : ℚ)), ((58318674018157870298867 : ℚ) / (784792923633255600000000 : ℚ)), ((115178255681538187915969 : ℚ) / (3139171694533022400000000 : ℚ)), ((1877382866494271256649 : ℚ) / (51461831057918400000000 : ℚ)), ((56029813479875475123047 : ℚ) / (1569585847266511200000000 : ℚ)), ((6685665377369218214399 : ℚ) / (205541003808709800000000 : ℚ))],
    jensenBound := ((12681219764444858168435936288405425620937316075037791130066696281400143923352887348926456237185810210247715853706242247868299147330608399793915683675444615969421115853882739666854302462844481024000000000000000000000 : ℚ) / (150137652423970469736210525916237592732587188635045036485998953789522578472239783014644517374838044003203519908417276909739006889657989468802542146374065320420211042067083090195601745962561198092103711273706590976662048882748961 : ℚ)),
    jensenFloorQ96 := (6691923872229998 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_simplexId_before"
  err.flush

theorem geometryRow007_simplexId_read :
    geometryRowsJson007.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped007.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_vertexIds_before"
  err.flush

theorem geometryRow007_vertexIds_read :
    geometryRowsJson007.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped007.vertexIds := by decide +kernel

noncomputable def geometryRow007_physicalVolumeNumeratorChars : List Char := ['5', '5', '9', '1', '4', '9', '1', '8', '4', '5', '1', '1', '5', '2', '3', '3', '3', '1', '8', '5', '1', '3', '7', '8', '8', '7', '5', '7', '1', '6', '2', '0', '5', '0', '1', '7', '3', '4', '9', '7', '6', '3', '9', '1', '6', '7']
noncomputable def geometryRow007_physicalVolumeDenominatorChars : List Char := ['9', '3', '7', '8', '9', '7', '2', '6', '2', '8', '0', '6', '5', '9', '7', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_physicalVolumeText : String := String.ofList (geometryRow007_physicalVolumeNumeratorChars ++ '/' :: geometryRow007_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_physicalVolume_before_field"
  err.flush

theorem geometryRow007_physicalVolume_field :
    geometryRowsJson007.getObjVal? "physical_volume" = .ok (.str geometryRow007_physicalVolumeText) := by rfl

theorem geometryRow007_physicalVolume_numerator_no_slash :
    geometryRow007_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeNumeratorChars = some (5591491845115233318513788757162050173497639167 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeDenominatorChars = some (937897262806597632000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_nonzero : (937897262806597632000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_physicalVolume_parse :
    parseRational geometryRow007_physicalVolumeText = .ok geometryRowsTyped007.physicalVolume :=
  original_rational_fraction_of_chars geometryRow007_physicalVolumeNumeratorChars geometryRow007_physicalVolumeDenominatorChars
    (5591491845115233318513788757162050173497639167 : Int) (937897262806597632000000000000000000000000000000000000000000000000000 : Int)
    geometryRow007_physicalVolume_numerator_no_slash geometryRow007_physicalVolume_numerator_parse
    geometryRow007_physicalVolume_denominator_parse geometryRow007_physicalVolume_denominator_nonzero

theorem geometryRow007_physicalVolume_read :
    rationalField geometryRowsJson007 "physical_volume" = .ok geometryRowsTyped007.physicalVolume :=
  original_rationalField_of_string geometryRowsJson007 "physical_volume" geometryRow007_physicalVolumeText
    geometryRowsTyped007.physicalVolume geometryRow007_physicalVolume_field geometryRow007_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_physicalVolume_complete"
  err.flush

noncomputable def geometryRow007_meanGapNumeratorChars : List Char := ['1', '5', '4', '4', '2', '3', '4', '4', '5', '9']
noncomputable def geometryRow007_meanGapDenominatorChars : List Char := ['5', '2', '1', '4', '8', '2', '5', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_meanGapText : String := String.ofList (geometryRow007_meanGapNumeratorChars ++ '/' :: geometryRow007_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_meanGap_before_field"
  err.flush

theorem geometryRow007_meanGap_field :
    geometryRowsJson007.getObjVal? "mean_gap" = .ok (.str geometryRow007_meanGapText) := by rfl

theorem geometryRow007_meanGap_numerator_no_slash :
    geometryRow007_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_meanGap_numerator_parse :
    SourceJson.intChars geometryRow007_meanGapNumeratorChars = some (1544234459 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_parse :
    SourceJson.intChars geometryRow007_meanGapDenominatorChars = some (521482500000 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_nonzero : (521482500000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_meanGap_parse :
    parseRational geometryRow007_meanGapText = .ok geometryRowsTyped007.meanGap :=
  original_rational_fraction_of_chars geometryRow007_meanGapNumeratorChars geometryRow007_meanGapDenominatorChars
    (1544234459 : Int) (521482500000 : Int)
    geometryRow007_meanGap_numerator_no_slash geometryRow007_meanGap_numerator_parse
    geometryRow007_meanGap_denominator_parse geometryRow007_meanGap_denominator_nonzero

theorem geometryRow007_meanGap_read :
    rationalField geometryRowsJson007 "mean_gap" = .ok geometryRowsTyped007.meanGap :=
  original_rationalField_of_string geometryRowsJson007 "mean_gap" geometryRow007_meanGapText
    geometryRowsTyped007.meanGap geometryRow007_meanGap_field geometryRow007_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_meanGap_complete"
  err.flush

noncomputable def geometryRow007_jensenBoundNumeratorChars : List Char := ['1', '2', '6', '8', '1', '2', '1', '9', '7', '6', '4', '4', '4', '4', '8', '5', '8', '1', '6', '8', '4', '3', '5', '9', '3', '6', '2', '8', '8', '4', '0', '5', '4', '2', '5', '6', '2', '0', '9', '3', '7', '3', '1', '6', '0', '7', '5', '0', '3', '7', '7', '9', '1', '1', '3', '0', '0', '6', '6', '6', '9', '6', '2', '8', '1', '4', '0', '0', '1', '4', '3', '9', '2', '3', '3', '5', '2', '8', '8', '7', '3', '4', '8', '9', '2', '6', '4', '5', '6', '2', '3', '7', '1', '8', '5', '8', '1', '0', '2', '1', '0', '2', '4', '7', '7', '1', '5', '8', '5', '3', '7', '0', '6', '2', '4', '2', '2', '4', '7', '8', '6', '8', '2', '9', '9', '1', '4', '7', '3', '3', '0', '6', '0', '8', '3', '9', '9', '7', '9', '3', '9', '1', '5', '6', '8', '3', '6', '7', '5', '4', '4', '4', '6', '1', '5', '9', '6', '9', '4', '2', '1', '1', '1', '5', '8', '5', '3', '8', '8', '2', '7', '3', '9', '6', '6', '6', '8', '5', '4', '3', '0', '2', '4', '6', '2', '8', '4', '4', '4', '8', '1', '0', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_jensenBoundDenominatorChars : List Char := ['1', '5', '0', '1', '3', '7', '6', '5', '2', '4', '2', '3', '9', '7', '0', '4', '6', '9', '7', '3', '6', '2', '1', '0', '5', '2', '5', '9', '1', '6', '2', '3', '7', '5', '9', '2', '7', '3', '2', '5', '8', '7', '1', '8', '8', '6', '3', '5', '0', '4', '5', '0', '3', '6', '4', '8', '5', '9', '9', '8', '9', '5', '3', '7', '8', '9', '5', '2', '2', '5', '7', '8', '4', '7', '2', '2', '3', '9', '7', '8', '3', '0', '1', '4', '6', '4', '4', '5', '1', '7', '3', '7', '4', '8', '3', '8', '0', '4', '4', '0', '0', '3', '2', '0', '3', '5', '1', '9', '9', '0', '8', '4', '1', '7', '2', '7', '6', '9', '0', '9', '7', '3', '9', '0', '0', '6', '8', '8', '9', '6', '5', '7', '9', '8', '9', '4', '6', '8', '8', '0', '2', '5', '4', '2', '1', '4', '6', '3', '7', '4', '0', '6', '5', '3', '2', '0', '4', '2', '0', '2', '1', '1', '0', '4', '2', '0', '6', '7', '0', '8', '3', '0', '9', '0', '1', '9', '5', '6', '0', '1', '7', '4', '5', '9', '6', '2', '5', '6', '1', '1', '9', '8', '0', '9', '2', '1', '0', '3', '7', '1', '1', '2', '7', '3', '7', '0', '6', '5', '9', '0', '9', '7', '6', '6', '6', '2', '0', '4', '8', '8', '8', '2', '7', '4', '8', '9', '6', '1']
noncomputable def geometryRow007_jensenBoundText : String := String.ofList (geometryRow007_jensenBoundNumeratorChars ++ '/' :: geometryRow007_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_jensenBound_before_field"
  err.flush

theorem geometryRow007_jensenBound_field :
    geometryRowsJson007.getObjVal? "jensen_bound" = .ok (.str geometryRow007_jensenBoundText) := by rfl

theorem geometryRow007_jensenBound_numerator_no_slash :
    geometryRow007_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow007_jensenBoundNumeratorChars = some (12681219764444858168435936288405425620937316075037791130066696281400143923352887348926456237185810210247715853706242247868299147330608399793915683675444615969421115853882739666854302462844481024000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow007_jensenBoundDenominatorChars = some (150137652423970469736210525916237592732587188635045036485998953789522578472239783014644517374838044003203519908417276909739006889657989468802542146374065320420211042067083090195601745962561198092103711273706590976662048882748961 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_nonzero : (150137652423970469736210525916237592732587188635045036485998953789522578472239783014644517374838044003203519908417276909739006889657989468802542146374065320420211042067083090195601745962561198092103711273706590976662048882748961 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_jensenBound_parse :
    parseRational geometryRow007_jensenBoundText = .ok geometryRowsTyped007.jensenBound :=
  original_rational_fraction_of_chars geometryRow007_jensenBoundNumeratorChars geometryRow007_jensenBoundDenominatorChars
    (12681219764444858168435936288405425620937316075037791130066696281400143923352887348926456237185810210247715853706242247868299147330608399793915683675444615969421115853882739666854302462844481024000000000000000000000 : Int) (150137652423970469736210525916237592732587188635045036485998953789522578472239783014644517374838044003203519908417276909739006889657989468802542146374065320420211042067083090195601745962561198092103711273706590976662048882748961 : Int)
    geometryRow007_jensenBound_numerator_no_slash geometryRow007_jensenBound_numerator_parse
    geometryRow007_jensenBound_denominator_parse geometryRow007_jensenBound_denominator_nonzero

theorem geometryRow007_jensenBound_read :
    rationalField geometryRowsJson007 "jensen_bound" = .ok geometryRowsTyped007.jensenBound :=
  original_rationalField_of_string geometryRowsJson007 "jensen_bound" geometryRow007_jensenBoundText
    geometryRowsTyped007.jensenBound geometryRow007_jensenBound_field geometryRow007_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_factorMaxima_before"
  err.flush

theorem geometryRow007_factorMaxima_read :
    rationalArrayField geometryRowsJson007 "factor_maxima" = .ok geometryRowsTyped007.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_gapWeightedMeans_before"
  err.flush

theorem geometryRow007_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson007 "gap_weighted_means" = .ok geometryRowsTyped007.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow007_floorChars : List Char := ['6', '6', '9', '1', '9', '2', '3', '8', '7', '2', '2', '2', '9', '9', '9', '8']
noncomputable def geometryRow007_floorText : String := String.ofList geometryRow007_floorChars

theorem geometryRow007_floor_text_read :
    geometryRowsJson007.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow007_floorText := by rfl

theorem geometryRow007_floor_chars_parse :
    SourceJson.intChars geometryRow007_floorChars = some (6691923872229998 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_007_original_decoder_complete"
  err.flush

theorem geometryRow007_shape :
    geometryRowsTyped007.simplexId = 7 ∧
    geometryRowsTyped007.vertexIds.size = 9 ∧ geometryRowsTyped007.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped007.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped007.factorMaxima.size = 10 ∧ geometryRowsTyped007.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock000 : List SourceJson := [geometryRowsJson000, geometryRowsJson001, geometryRowsJson002, geometryRowsJson003, geometryRowsJson004, geometryRowsJson005, geometryRowsJson006, geometryRowsJson007]
noncomputable def geometryRowsTypedBlock000 : List GeometryRow := [geometryRowsTyped000, geometryRowsTyped001, geometryRowsTyped002, geometryRowsTyped003, geometryRowsTyped004, geometryRowsTyped005, geometryRowsTyped006, geometryRowsTyped007]

theorem geometry_Rows_block_000_push_eq (acc : List SourceJson) :
    SimplicesBlock000.blockPush acc = [geometryRowsJson007, geometryRowsJson006, geometryRowsJson005, geometryRowsJson004, geometryRowsJson003, geometryRowsJson002, geometryRowsJson001, geometryRowsJson000] ++ acc := by rfl

theorem geometry_Rows_block_000_reverse (acc : List SourceJson) :
    (SimplicesBlock000.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock000 := by
  rw [geometry_Rows_block_000_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_000 :
    geometryRowsJsonBlock000.mapM decodeGeometryRow = .ok geometryRowsTypedBlock000 := by
  simp only [geometryRowsJsonBlock000, geometryRowsTypedBlock000, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_000, decode_geometry_Rows_001, decode_geometry_Rows_002, decode_geometry_Rows_003, decode_geometry_Rows_004, decode_geometry_Rows_005, decode_geometry_Rows_006, decode_geometry_Rows_007]
  rfl

theorem geometry_Rows_block_000_length : geometryRowsTypedBlock000.length = 8 := by rfl

#print axioms geometryRow000_simplexId_read
#print axioms geometryRow000_vertexIds_read
#print axioms geometryRow000_physicalVolume_field
#print axioms geometryRow000_physicalVolume_numerator_no_slash
#print axioms geometryRow000_physicalVolume_numerator_parse
#print axioms geometryRow000_physicalVolume_denominator_parse
#print axioms geometryRow000_physicalVolume_denominator_nonzero
#print axioms geometryRow000_physicalVolume_parse
#print axioms geometryRow000_physicalVolume_read
#print axioms geometryRow000_meanGap_field
#print axioms geometryRow000_meanGap_numerator_no_slash
#print axioms geometryRow000_meanGap_numerator_parse
#print axioms geometryRow000_meanGap_denominator_parse
#print axioms geometryRow000_meanGap_denominator_nonzero
#print axioms geometryRow000_meanGap_parse
#print axioms geometryRow000_meanGap_read
#print axioms geometryRow000_jensenBound_field
#print axioms geometryRow000_jensenBound_numerator_no_slash
#print axioms geometryRow000_jensenBound_numerator_parse
#print axioms geometryRow000_jensenBound_denominator_parse
#print axioms geometryRow000_jensenBound_denominator_nonzero
#print axioms geometryRow000_jensenBound_parse
#print axioms geometryRow000_jensenBound_read
#print axioms geometryRow000_factorMaxima_read
#print axioms geometryRow000_gapWeightedMeans_read
#print axioms geometryRow000_floor_text_read
#print axioms geometryRow000_floor_chars_parse
#print axioms geometryRow000_floor_parse
#print axioms decode_geometry_Rows_000
#print axioms geometryRow000_shape
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
#print axioms geometryRow001_shape
#print axioms geometryRow002_simplexId_read
#print axioms geometryRow002_vertexIds_read
#print axioms geometryRow002_physicalVolume_field
#print axioms geometryRow002_physicalVolume_numerator_no_slash
#print axioms geometryRow002_physicalVolume_numerator_parse
#print axioms geometryRow002_physicalVolume_denominator_parse
#print axioms geometryRow002_physicalVolume_denominator_nonzero
#print axioms geometryRow002_physicalVolume_parse
#print axioms geometryRow002_physicalVolume_read
#print axioms geometryRow002_meanGap_field
#print axioms geometryRow002_meanGap_numerator_no_slash
#print axioms geometryRow002_meanGap_numerator_parse
#print axioms geometryRow002_meanGap_denominator_parse
#print axioms geometryRow002_meanGap_denominator_nonzero
#print axioms geometryRow002_meanGap_parse
#print axioms geometryRow002_meanGap_read
#print axioms geometryRow002_jensenBound_field
#print axioms geometryRow002_jensenBound_numerator_no_slash
#print axioms geometryRow002_jensenBound_numerator_parse
#print axioms geometryRow002_jensenBound_denominator_parse
#print axioms geometryRow002_jensenBound_denominator_nonzero
#print axioms geometryRow002_jensenBound_parse
#print axioms geometryRow002_jensenBound_read
#print axioms geometryRow002_factorMaxima_read
#print axioms geometryRow002_gapWeightedMeans_read
#print axioms geometryRow002_floor_text_read
#print axioms geometryRow002_floor_chars_parse
#print axioms geometryRow002_floor_parse
#print axioms decode_geometry_Rows_002
#print axioms geometryRow002_shape
#print axioms geometryRow003_simplexId_read
#print axioms geometryRow003_vertexIds_read
#print axioms geometryRow003_physicalVolume_field
#print axioms geometryRow003_physicalVolume_numerator_no_slash
#print axioms geometryRow003_physicalVolume_numerator_parse
#print axioms geometryRow003_physicalVolume_denominator_parse
#print axioms geometryRow003_physicalVolume_denominator_nonzero
#print axioms geometryRow003_physicalVolume_parse
#print axioms geometryRow003_physicalVolume_read
#print axioms geometryRow003_meanGap_field
#print axioms geometryRow003_meanGap_numerator_no_slash
#print axioms geometryRow003_meanGap_numerator_parse
#print axioms geometryRow003_meanGap_denominator_parse
#print axioms geometryRow003_meanGap_denominator_nonzero
#print axioms geometryRow003_meanGap_parse
#print axioms geometryRow003_meanGap_read
#print axioms geometryRow003_jensenBound_field
#print axioms geometryRow003_jensenBound_numerator_no_slash
#print axioms geometryRow003_jensenBound_numerator_parse
#print axioms geometryRow003_jensenBound_denominator_parse
#print axioms geometryRow003_jensenBound_denominator_nonzero
#print axioms geometryRow003_jensenBound_parse
#print axioms geometryRow003_jensenBound_read
#print axioms geometryRow003_factorMaxima_read
#print axioms geometryRow003_gapWeightedMeans_read
#print axioms geometryRow003_floor_text_read
#print axioms geometryRow003_floor_chars_parse
#print axioms geometryRow003_floor_parse
#print axioms decode_geometry_Rows_003
#print axioms geometryRow003_shape
#print axioms geometryRow004_simplexId_read
#print axioms geometryRow004_vertexIds_read
#print axioms geometryRow004_physicalVolume_field
#print axioms geometryRow004_physicalVolume_numerator_no_slash
#print axioms geometryRow004_physicalVolume_numerator_parse
#print axioms geometryRow004_physicalVolume_denominator_parse
#print axioms geometryRow004_physicalVolume_denominator_nonzero
#print axioms geometryRow004_physicalVolume_parse
#print axioms geometryRow004_physicalVolume_read
#print axioms geometryRow004_meanGap_field
#print axioms geometryRow004_meanGap_numerator_no_slash
#print axioms geometryRow004_meanGap_numerator_parse
#print axioms geometryRow004_meanGap_denominator_parse
#print axioms geometryRow004_meanGap_denominator_nonzero
#print axioms geometryRow004_meanGap_parse
#print axioms geometryRow004_meanGap_read
#print axioms geometryRow004_jensenBound_field
#print axioms geometryRow004_jensenBound_numerator_no_slash
#print axioms geometryRow004_jensenBound_numerator_parse
#print axioms geometryRow004_jensenBound_denominator_parse
#print axioms geometryRow004_jensenBound_denominator_nonzero
#print axioms geometryRow004_jensenBound_parse
#print axioms geometryRow004_jensenBound_read
#print axioms geometryRow004_factorMaxima_read
#print axioms geometryRow004_gapWeightedMeans_read
#print axioms geometryRow004_floor_text_read
#print axioms geometryRow004_floor_chars_parse
#print axioms geometryRow004_floor_parse
#print axioms decode_geometry_Rows_004
#print axioms geometryRow004_shape
#print axioms geometryRow005_simplexId_read
#print axioms geometryRow005_vertexIds_read
#print axioms geometryRow005_physicalVolume_field
#print axioms geometryRow005_physicalVolume_numerator_no_slash
#print axioms geometryRow005_physicalVolume_numerator_parse
#print axioms geometryRow005_physicalVolume_denominator_parse
#print axioms geometryRow005_physicalVolume_denominator_nonzero
#print axioms geometryRow005_physicalVolume_parse
#print axioms geometryRow005_physicalVolume_read
#print axioms geometryRow005_meanGap_field
#print axioms geometryRow005_meanGap_numerator_no_slash
#print axioms geometryRow005_meanGap_numerator_parse
#print axioms geometryRow005_meanGap_denominator_parse
#print axioms geometryRow005_meanGap_denominator_nonzero
#print axioms geometryRow005_meanGap_parse
#print axioms geometryRow005_meanGap_read
#print axioms geometryRow005_jensenBound_field
#print axioms geometryRow005_jensenBound_numerator_no_slash
#print axioms geometryRow005_jensenBound_numerator_parse
#print axioms geometryRow005_jensenBound_denominator_parse
#print axioms geometryRow005_jensenBound_denominator_nonzero
#print axioms geometryRow005_jensenBound_parse
#print axioms geometryRow005_jensenBound_read
#print axioms geometryRow005_factorMaxima_read
#print axioms geometryRow005_gapWeightedMeans_read
#print axioms geometryRow005_floor_text_read
#print axioms geometryRow005_floor_chars_parse
#print axioms geometryRow005_floor_parse
#print axioms decode_geometry_Rows_005
#print axioms geometryRow005_shape
#print axioms geometryRow006_simplexId_read
#print axioms geometryRow006_vertexIds_read
#print axioms geometryRow006_physicalVolume_field
#print axioms geometryRow006_physicalVolume_numerator_no_slash
#print axioms geometryRow006_physicalVolume_numerator_parse
#print axioms geometryRow006_physicalVolume_denominator_parse
#print axioms geometryRow006_physicalVolume_denominator_nonzero
#print axioms geometryRow006_physicalVolume_parse
#print axioms geometryRow006_physicalVolume_read
#print axioms geometryRow006_meanGap_field
#print axioms geometryRow006_meanGap_numerator_no_slash
#print axioms geometryRow006_meanGap_numerator_parse
#print axioms geometryRow006_meanGap_denominator_parse
#print axioms geometryRow006_meanGap_denominator_nonzero
#print axioms geometryRow006_meanGap_parse
#print axioms geometryRow006_meanGap_read
#print axioms geometryRow006_jensenBound_field
#print axioms geometryRow006_jensenBound_numerator_no_slash
#print axioms geometryRow006_jensenBound_numerator_parse
#print axioms geometryRow006_jensenBound_denominator_parse
#print axioms geometryRow006_jensenBound_denominator_nonzero
#print axioms geometryRow006_jensenBound_parse
#print axioms geometryRow006_jensenBound_read
#print axioms geometryRow006_factorMaxima_read
#print axioms geometryRow006_gapWeightedMeans_read
#print axioms geometryRow006_floor_text_read
#print axioms geometryRow006_floor_chars_parse
#print axioms geometryRow006_floor_parse
#print axioms decode_geometry_Rows_006
#print axioms geometryRow006_shape
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
#print axioms geometryRow007_shape
#print axioms geometry_Rows_block_000_push_eq
#print axioms geometry_Rows_block_000_reverse
#print axioms decode_geometry_Rows_block_000
#print axioms geometry_Rows_block_000_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
