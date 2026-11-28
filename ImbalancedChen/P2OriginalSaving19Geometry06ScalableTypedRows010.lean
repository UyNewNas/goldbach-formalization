import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock010

/-! Local typed certificates for original cell 06, rows 80 through 87.
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

noncomputable def geometryRowsJson080 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped080 : GeometryRow :=
  { simplexId := 80,
    vertexIds := #[32, 30, 28, 26, 25, 14, 11, 7, 3],
    physicalVolume := ((693081607123942784257018189243116801181 : ℚ) / (6786606842265600000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((49290167 : ℚ) / (34056000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((2296839 : ℚ) / (28000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((2296839 : ℚ) / (56000000 : ℚ)), ((5921703 : ℚ) / (172000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((3962263731354255456739 : ℚ) / (45268344695865060000000 : ℚ)), ((8101550809885976798987 : ℚ) / (90536689391730120000000 : ℚ)), ((1541629766242733551663 : ℚ) / (12933812770247160000000 : ℚ)), ((1397041976495810174911 : ℚ) / (15089448231955020000000 : ℚ)), ((1388842151638910281463 : ℚ) / (15089448231955020000000 : ℚ)), ((37144949531367268433 : ℚ) / (517352510809886400000 : ℚ)), ((6560986301752781902337 : ℚ) / (181073378783460240000000 : ℚ)), ((6278092344189735578381 : ℚ) / (181073378783460240000000 : ℚ)), ((1399850801537387572889 : ℚ) / (45268344695865060000000 : ℚ)), ((2763384272457989043433 : ℚ) / (90536689391730120000000 : ℚ))],
    jensenBound := ((496096126055492905944815277879553302147970901130289895919802480972015562852949077051187699640380355222987669634905958825345979028884536599529833907802488718500028638474710361792844484992000000000000000 : ℚ) / (568294699913398659213238129504025372874688040093639393470690996712753520569993792614847448553607984783855642905061904143318930658059918139064936649353494196811613831733891891959774779917306729404158722938572655019 : ℚ)),
    jensenFloorQ96 := (69162680038738949 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_simplexId_before"
  err.flush

theorem geometryRow080_simplexId_read :
    geometryRowsJson080.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped080.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_vertexIds_before"
  err.flush

theorem geometryRow080_vertexIds_read :
    geometryRowsJson080.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped080.vertexIds := by decide +kernel

noncomputable def geometryRow080_physicalVolumeNumeratorChars : List Char := ['6', '9', '3', '0', '8', '1', '6', '0', '7', '1', '2', '3', '9', '4', '2', '7', '8', '4', '2', '5', '7', '0', '1', '8', '1', '8', '9', '2', '4', '3', '1', '1', '6', '8', '0', '1', '1', '8', '1']
noncomputable def geometryRow080_physicalVolumeDenominatorChars : List Char := ['6', '7', '8', '6', '6', '0', '6', '8', '4', '2', '2', '6', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow080_physicalVolumeText : String := String.ofList (geometryRow080_physicalVolumeNumeratorChars ++ '/' :: geometryRow080_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_physicalVolume_before_field"
  err.flush

theorem geometryRow080_physicalVolume_field :
    geometryRowsJson080.getObjVal? "physical_volume" = .ok (.str geometryRow080_physicalVolumeText) := by rfl

theorem geometryRow080_physicalVolume_numerator_no_slash :
    geometryRow080_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow080_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow080_physicalVolumeNumeratorChars = some (693081607123942784257018189243116801181 : Int) := by decide +kernel

theorem geometryRow080_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow080_physicalVolumeDenominatorChars = some (6786606842265600000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow080_physicalVolume_denominator_nonzero : (6786606842265600000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow080_physicalVolume_parse :
    parseRational geometryRow080_physicalVolumeText = .ok geometryRowsTyped080.physicalVolume :=
  original_rational_fraction_of_chars geometryRow080_physicalVolumeNumeratorChars geometryRow080_physicalVolumeDenominatorChars
    (693081607123942784257018189243116801181 : Int) (6786606842265600000000000000000000000000000000000000000000000 : Int)
    geometryRow080_physicalVolume_numerator_no_slash geometryRow080_physicalVolume_numerator_parse
    geometryRow080_physicalVolume_denominator_parse geometryRow080_physicalVolume_denominator_nonzero

theorem geometryRow080_physicalVolume_read :
    rationalField geometryRowsJson080 "physical_volume" = .ok geometryRowsTyped080.physicalVolume :=
  original_rationalField_of_string geometryRowsJson080 "physical_volume" geometryRow080_physicalVolumeText
    geometryRowsTyped080.physicalVolume geometryRow080_physicalVolume_field geometryRow080_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_physicalVolume_complete"
  err.flush

noncomputable def geometryRow080_meanGapNumeratorChars : List Char := ['4', '9', '2', '9', '0', '1', '6', '7']
noncomputable def geometryRow080_meanGapDenominatorChars : List Char := ['3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow080_meanGapText : String := String.ofList (geometryRow080_meanGapNumeratorChars ++ '/' :: geometryRow080_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_meanGap_before_field"
  err.flush

theorem geometryRow080_meanGap_field :
    geometryRowsJson080.getObjVal? "mean_gap" = .ok (.str geometryRow080_meanGapText) := by rfl

theorem geometryRow080_meanGap_numerator_no_slash :
    geometryRow080_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow080_meanGap_numerator_parse :
    SourceJson.intChars geometryRow080_meanGapNumeratorChars = some (49290167 : Int) := by decide +kernel

theorem geometryRow080_meanGap_denominator_parse :
    SourceJson.intChars geometryRow080_meanGapDenominatorChars = some (34056000000 : Int) := by decide +kernel

theorem geometryRow080_meanGap_denominator_nonzero : (34056000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow080_meanGap_parse :
    parseRational geometryRow080_meanGapText = .ok geometryRowsTyped080.meanGap :=
  original_rational_fraction_of_chars geometryRow080_meanGapNumeratorChars geometryRow080_meanGapDenominatorChars
    (49290167 : Int) (34056000000 : Int)
    geometryRow080_meanGap_numerator_no_slash geometryRow080_meanGap_numerator_parse
    geometryRow080_meanGap_denominator_parse geometryRow080_meanGap_denominator_nonzero

theorem geometryRow080_meanGap_read :
    rationalField geometryRowsJson080 "mean_gap" = .ok geometryRowsTyped080.meanGap :=
  original_rationalField_of_string geometryRowsJson080 "mean_gap" geometryRow080_meanGapText
    geometryRowsTyped080.meanGap geometryRow080_meanGap_field geometryRow080_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_meanGap_complete"
  err.flush

noncomputable def geometryRow080_jensenBoundNumeratorChars : List Char := ['4', '9', '6', '0', '9', '6', '1', '2', '6', '0', '5', '5', '4', '9', '2', '9', '0', '5', '9', '4', '4', '8', '1', '5', '2', '7', '7', '8', '7', '9', '5', '5', '3', '3', '0', '2', '1', '4', '7', '9', '7', '0', '9', '0', '1', '1', '3', '0', '2', '8', '9', '8', '9', '5', '9', '1', '9', '8', '0', '2', '4', '8', '0', '9', '7', '2', '0', '1', '5', '5', '6', '2', '8', '5', '2', '9', '4', '9', '0', '7', '7', '0', '5', '1', '1', '8', '7', '6', '9', '9', '6', '4', '0', '3', '8', '0', '3', '5', '5', '2', '2', '2', '9', '8', '7', '6', '6', '9', '6', '3', '4', '9', '0', '5', '9', '5', '8', '8', '2', '5', '3', '4', '5', '9', '7', '9', '0', '2', '8', '8', '8', '4', '5', '3', '6', '5', '9', '9', '5', '2', '9', '8', '3', '3', '9', '0', '7', '8', '0', '2', '4', '8', '8', '7', '1', '8', '5', '0', '0', '0', '2', '8', '6', '3', '8', '4', '7', '4', '7', '1', '0', '3', '6', '1', '7', '9', '2', '8', '4', '4', '4', '8', '4', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow080_jensenBoundDenominatorChars : List Char := ['5', '6', '8', '2', '9', '4', '6', '9', '9', '9', '1', '3', '3', '9', '8', '6', '5', '9', '2', '1', '3', '2', '3', '8', '1', '2', '9', '5', '0', '4', '0', '2', '5', '3', '7', '2', '8', '7', '4', '6', '8', '8', '0', '4', '0', '0', '9', '3', '6', '3', '9', '3', '9', '3', '4', '7', '0', '6', '9', '0', '9', '9', '6', '7', '1', '2', '7', '5', '3', '5', '2', '0', '5', '6', '9', '9', '9', '3', '7', '9', '2', '6', '1', '4', '8', '4', '7', '4', '4', '8', '5', '5', '3', '6', '0', '7', '9', '8', '4', '7', '8', '3', '8', '5', '5', '6', '4', '2', '9', '0', '5', '0', '6', '1', '9', '0', '4', '1', '4', '3', '3', '1', '8', '9', '3', '0', '6', '5', '8', '0', '5', '9', '9', '1', '8', '1', '3', '9', '0', '6', '4', '9', '3', '6', '6', '4', '9', '3', '5', '3', '4', '9', '4', '1', '9', '6', '8', '1', '1', '6', '1', '3', '8', '3', '1', '7', '3', '3', '8', '9', '1', '8', '9', '1', '9', '5', '9', '7', '7', '4', '7', '7', '9', '9', '1', '7', '3', '0', '6', '7', '2', '9', '4', '0', '4', '1', '5', '8', '7', '2', '2', '9', '3', '8', '5', '7', '2', '6', '5', '5', '0', '1', '9']
noncomputable def geometryRow080_jensenBoundText : String := String.ofList (geometryRow080_jensenBoundNumeratorChars ++ '/' :: geometryRow080_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_jensenBound_before_field"
  err.flush

theorem geometryRow080_jensenBound_field :
    geometryRowsJson080.getObjVal? "jensen_bound" = .ok (.str geometryRow080_jensenBoundText) := by rfl

theorem geometryRow080_jensenBound_numerator_no_slash :
    geometryRow080_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow080_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow080_jensenBoundNumeratorChars = some (496096126055492905944815277879553302147970901130289895919802480972015562852949077051187699640380355222987669634905958825345979028884536599529833907802488718500028638474710361792844484992000000000000000 : Int) := by decide +kernel

theorem geometryRow080_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow080_jensenBoundDenominatorChars = some (568294699913398659213238129504025372874688040093639393470690996712753520569993792614847448553607984783855642905061904143318930658059918139064936649353494196811613831733891891959774779917306729404158722938572655019 : Int) := by decide +kernel

theorem geometryRow080_jensenBound_denominator_nonzero : (568294699913398659213238129504025372874688040093639393470690996712753520569993792614847448553607984783855642905061904143318930658059918139064936649353494196811613831733891891959774779917306729404158722938572655019 : Int) ≠ 0 := by decide +kernel

theorem geometryRow080_jensenBound_parse :
    parseRational geometryRow080_jensenBoundText = .ok geometryRowsTyped080.jensenBound :=
  original_rational_fraction_of_chars geometryRow080_jensenBoundNumeratorChars geometryRow080_jensenBoundDenominatorChars
    (496096126055492905944815277879553302147970901130289895919802480972015562852949077051187699640380355222987669634905958825345979028884536599529833907802488718500028638474710361792844484992000000000000000 : Int) (568294699913398659213238129504025372874688040093639393470690996712753520569993792614847448553607984783855642905061904143318930658059918139064936649353494196811613831733891891959774779917306729404158722938572655019 : Int)
    geometryRow080_jensenBound_numerator_no_slash geometryRow080_jensenBound_numerator_parse
    geometryRow080_jensenBound_denominator_parse geometryRow080_jensenBound_denominator_nonzero

theorem geometryRow080_jensenBound_read :
    rationalField geometryRowsJson080 "jensen_bound" = .ok geometryRowsTyped080.jensenBound :=
  original_rationalField_of_string geometryRowsJson080 "jensen_bound" geometryRow080_jensenBoundText
    geometryRowsTyped080.jensenBound geometryRow080_jensenBound_field geometryRow080_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_factorMaxima_before"
  err.flush

theorem geometryRow080_factorMaxima_read :
    rationalArrayField geometryRowsJson080 "factor_maxima" = .ok geometryRowsTyped080.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_gapWeightedMeans_before"
  err.flush

theorem geometryRow080_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson080 "gap_weighted_means" = .ok geometryRowsTyped080.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow080_floorChars : List Char := ['6', '9', '1', '6', '2', '6', '8', '0', '0', '3', '8', '7', '3', '8', '9', '4', '9']
noncomputable def geometryRow080_floorText : String := String.ofList geometryRow080_floorChars

theorem geometryRow080_floor_text_read :
    geometryRowsJson080.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow080_floorText := by rfl

theorem geometryRow080_floor_chars_parse :
    SourceJson.intChars geometryRow080_floorChars = some (69162680038738949 : Int) := by decide +kernel

theorem geometryRow080_floor_parse :
    parseInteger geometryRow080_floorText = .ok geometryRowsTyped080.jensenFloorQ96 := by
  simp only [geometryRow080_floorText, parseInteger, String.toList_ofList, geometryRow080_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_080 :
    decodeGeometryRow geometryRowsJson080 = .ok geometryRowsTyped080 :=
  original_geometryRow_of_fields geometryRowsJson080 geometryRowsTyped080 geometryRow080_floorText
    geometryRow080_simplexId_read geometryRow080_vertexIds_read
    geometryRow080_physicalVolume_read geometryRow080_meanGap_read
    geometryRow080_factorMaxima_read geometryRow080_gapWeightedMeans_read
    geometryRow080_jensenBound_read geometryRow080_floor_text_read geometryRow080_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_080_original_decoder_complete"
  err.flush

theorem geometryRow080_shape :
    geometryRowsTyped080.simplexId = 80 ∧
    geometryRowsTyped080.vertexIds.size = 9 ∧ geometryRowsTyped080.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped080.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped080.factorMaxima.size = 10 ∧ geometryRowsTyped080.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson081 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped081 : GeometryRow :=
  { simplexId := 81,
    vertexIds := #[32, 30, 28, 26, 25, 14, 13, 4, 0],
    physicalVolume := ((94633746782304287851788799543377067633 : ℚ) / (2233328786892000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((96707389 : ℚ) / (66220000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((76867314087922712937361 : ℚ) / (888165670018750200000000 : ℚ)), ((1828334345429662876721 : ℚ) / (20655015581831400000000 : ℚ)), ((76665712256498868763 : ℚ) / (643598311607790000000 : ℚ)), ((3927606194063704575323 : ℚ) / (42293603334226200000000 : ℚ)), ((3904623237061113098443 : ℚ) / (42293603334226200000000 : ℚ)), ((319595070521307170307 : ℚ) / (4485685202114900000000 : ℚ)), ((20162407820600023417 : ℚ) / (560710650264362500000 : ℚ)), ((462873605436348131453 : ℚ) / (13457055606344700000000 : ℚ)), ((291814977591231424277 : ℚ) / (8971370404229800000000 : ℚ)), ((623787318629680507787 : ℚ) / (20655015581831400000000 : ℚ))],
    jensenBound := ((10929198905706465568401738374506019115374020730257344066867746374543025867798054239166704688058167296127819058542857104234246025922839466113039801334991139863932245502697396000000000000000000000000 : ℚ) / (29904277778503070903679770567157858746983251933366501145731919877332707430746661199720731703472980999091681103912021780499437902487377054609228862630686507378763000041185504317559085898739159733941448318253577 : ℚ)),
    jensenFloorQ96 := (28955735144839083 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_simplexId_before"
  err.flush

theorem geometryRow081_simplexId_read :
    geometryRowsJson081.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped081.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_vertexIds_before"
  err.flush

theorem geometryRow081_vertexIds_read :
    geometryRowsJson081.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped081.vertexIds := by decide +kernel

noncomputable def geometryRow081_physicalVolumeNumeratorChars : List Char := ['9', '4', '6', '3', '3', '7', '4', '6', '7', '8', '2', '3', '0', '4', '2', '8', '7', '8', '5', '1', '7', '8', '8', '7', '9', '9', '5', '4', '3', '3', '7', '7', '0', '6', '7', '6', '3', '3']
noncomputable def geometryRow081_physicalVolumeDenominatorChars : List Char := ['2', '2', '3', '3', '3', '2', '8', '7', '8', '6', '8', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow081_physicalVolumeText : String := String.ofList (geometryRow081_physicalVolumeNumeratorChars ++ '/' :: geometryRow081_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_physicalVolume_before_field"
  err.flush

theorem geometryRow081_physicalVolume_field :
    geometryRowsJson081.getObjVal? "physical_volume" = .ok (.str geometryRow081_physicalVolumeText) := by rfl

theorem geometryRow081_physicalVolume_numerator_no_slash :
    geometryRow081_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow081_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow081_physicalVolumeNumeratorChars = some (94633746782304287851788799543377067633 : Int) := by decide +kernel

theorem geometryRow081_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow081_physicalVolumeDenominatorChars = some (2233328786892000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow081_physicalVolume_denominator_nonzero : (2233328786892000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow081_physicalVolume_parse :
    parseRational geometryRow081_physicalVolumeText = .ok geometryRowsTyped081.physicalVolume :=
  original_rational_fraction_of_chars geometryRow081_physicalVolumeNumeratorChars geometryRow081_physicalVolumeDenominatorChars
    (94633746782304287851788799543377067633 : Int) (2233328786892000000000000000000000000000000000000000000000000 : Int)
    geometryRow081_physicalVolume_numerator_no_slash geometryRow081_physicalVolume_numerator_parse
    geometryRow081_physicalVolume_denominator_parse geometryRow081_physicalVolume_denominator_nonzero

theorem geometryRow081_physicalVolume_read :
    rationalField geometryRowsJson081 "physical_volume" = .ok geometryRowsTyped081.physicalVolume :=
  original_rationalField_of_string geometryRowsJson081 "physical_volume" geometryRow081_physicalVolumeText
    geometryRowsTyped081.physicalVolume geometryRow081_physicalVolume_field geometryRow081_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_physicalVolume_complete"
  err.flush

noncomputable def geometryRow081_meanGapNumeratorChars : List Char := ['9', '6', '7', '0', '7', '3', '8', '9']
noncomputable def geometryRow081_meanGapDenominatorChars : List Char := ['6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow081_meanGapText : String := String.ofList (geometryRow081_meanGapNumeratorChars ++ '/' :: geometryRow081_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_meanGap_before_field"
  err.flush

theorem geometryRow081_meanGap_field :
    geometryRowsJson081.getObjVal? "mean_gap" = .ok (.str geometryRow081_meanGapText) := by rfl

theorem geometryRow081_meanGap_numerator_no_slash :
    geometryRow081_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow081_meanGap_numerator_parse :
    SourceJson.intChars geometryRow081_meanGapNumeratorChars = some (96707389 : Int) := by decide +kernel

theorem geometryRow081_meanGap_denominator_parse :
    SourceJson.intChars geometryRow081_meanGapDenominatorChars = some (66220000000 : Int) := by decide +kernel

theorem geometryRow081_meanGap_denominator_nonzero : (66220000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow081_meanGap_parse :
    parseRational geometryRow081_meanGapText = .ok geometryRowsTyped081.meanGap :=
  original_rational_fraction_of_chars geometryRow081_meanGapNumeratorChars geometryRow081_meanGapDenominatorChars
    (96707389 : Int) (66220000000 : Int)
    geometryRow081_meanGap_numerator_no_slash geometryRow081_meanGap_numerator_parse
    geometryRow081_meanGap_denominator_parse geometryRow081_meanGap_denominator_nonzero

theorem geometryRow081_meanGap_read :
    rationalField geometryRowsJson081 "mean_gap" = .ok geometryRowsTyped081.meanGap :=
  original_rationalField_of_string geometryRowsJson081 "mean_gap" geometryRow081_meanGapText
    geometryRowsTyped081.meanGap geometryRow081_meanGap_field geometryRow081_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_meanGap_complete"
  err.flush

noncomputable def geometryRow081_jensenBoundNumeratorChars : List Char := ['1', '0', '9', '2', '9', '1', '9', '8', '9', '0', '5', '7', '0', '6', '4', '6', '5', '5', '6', '8', '4', '0', '1', '7', '3', '8', '3', '7', '4', '5', '0', '6', '0', '1', '9', '1', '1', '5', '3', '7', '4', '0', '2', '0', '7', '3', '0', '2', '5', '7', '3', '4', '4', '0', '6', '6', '8', '6', '7', '7', '4', '6', '3', '7', '4', '5', '4', '3', '0', '2', '5', '8', '6', '7', '7', '9', '8', '0', '5', '4', '2', '3', '9', '1', '6', '6', '7', '0', '4', '6', '8', '8', '0', '5', '8', '1', '6', '7', '2', '9', '6', '1', '2', '7', '8', '1', '9', '0', '5', '8', '5', '4', '2', '8', '5', '7', '1', '0', '4', '2', '3', '4', '2', '4', '6', '0', '2', '5', '9', '2', '2', '8', '3', '9', '4', '6', '6', '1', '1', '3', '0', '3', '9', '8', '0', '1', '3', '3', '4', '9', '9', '1', '1', '3', '9', '8', '6', '3', '9', '3', '2', '2', '4', '5', '5', '0', '2', '6', '9', '7', '3', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow081_jensenBoundDenominatorChars : List Char := ['2', '9', '9', '0', '4', '2', '7', '7', '7', '7', '8', '5', '0', '3', '0', '7', '0', '9', '0', '3', '6', '7', '9', '7', '7', '0', '5', '6', '7', '1', '5', '7', '8', '5', '8', '7', '4', '6', '9', '8', '3', '2', '5', '1', '9', '3', '3', '3', '6', '6', '5', '0', '1', '1', '4', '5', '7', '3', '1', '9', '1', '9', '8', '7', '7', '3', '3', '2', '7', '0', '7', '4', '3', '0', '7', '4', '6', '6', '6', '1', '1', '9', '9', '7', '2', '0', '7', '3', '1', '7', '0', '3', '4', '7', '2', '9', '8', '0', '9', '9', '9', '0', '9', '1', '6', '8', '1', '1', '0', '3', '9', '1', '2', '0', '2', '1', '7', '8', '0', '4', '9', '9', '4', '3', '7', '9', '0', '2', '4', '8', '7', '3', '7', '7', '0', '5', '4', '6', '0', '9', '2', '2', '8', '8', '6', '2', '6', '3', '0', '6', '8', '6', '5', '0', '7', '3', '7', '8', '7', '6', '3', '0', '0', '0', '0', '4', '1', '1', '8', '5', '5', '0', '4', '3', '1', '7', '5', '5', '9', '0', '8', '5', '8', '9', '8', '7', '3', '9', '1', '5', '9', '7', '3', '3', '9', '4', '1', '4', '4', '8', '3', '1', '8', '2', '5', '3', '5', '7', '7']
noncomputable def geometryRow081_jensenBoundText : String := String.ofList (geometryRow081_jensenBoundNumeratorChars ++ '/' :: geometryRow081_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_jensenBound_before_field"
  err.flush

theorem geometryRow081_jensenBound_field :
    geometryRowsJson081.getObjVal? "jensen_bound" = .ok (.str geometryRow081_jensenBoundText) := by rfl

theorem geometryRow081_jensenBound_numerator_no_slash :
    geometryRow081_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow081_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow081_jensenBoundNumeratorChars = some (10929198905706465568401738374506019115374020730257344066867746374543025867798054239166704688058167296127819058542857104234246025922839466113039801334991139863932245502697396000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow081_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow081_jensenBoundDenominatorChars = some (29904277778503070903679770567157858746983251933366501145731919877332707430746661199720731703472980999091681103912021780499437902487377054609228862630686507378763000041185504317559085898739159733941448318253577 : Int) := by decide +kernel

theorem geometryRow081_jensenBound_denominator_nonzero : (29904277778503070903679770567157858746983251933366501145731919877332707430746661199720731703472980999091681103912021780499437902487377054609228862630686507378763000041185504317559085898739159733941448318253577 : Int) ≠ 0 := by decide +kernel

theorem geometryRow081_jensenBound_parse :
    parseRational geometryRow081_jensenBoundText = .ok geometryRowsTyped081.jensenBound :=
  original_rational_fraction_of_chars geometryRow081_jensenBoundNumeratorChars geometryRow081_jensenBoundDenominatorChars
    (10929198905706465568401738374506019115374020730257344066867746374543025867798054239166704688058167296127819058542857104234246025922839466113039801334991139863932245502697396000000000000000000000000 : Int) (29904277778503070903679770567157858746983251933366501145731919877332707430746661199720731703472980999091681103912021780499437902487377054609228862630686507378763000041185504317559085898739159733941448318253577 : Int)
    geometryRow081_jensenBound_numerator_no_slash geometryRow081_jensenBound_numerator_parse
    geometryRow081_jensenBound_denominator_parse geometryRow081_jensenBound_denominator_nonzero

theorem geometryRow081_jensenBound_read :
    rationalField geometryRowsJson081 "jensen_bound" = .ok geometryRowsTyped081.jensenBound :=
  original_rationalField_of_string geometryRowsJson081 "jensen_bound" geometryRow081_jensenBoundText
    geometryRowsTyped081.jensenBound geometryRow081_jensenBound_field geometryRow081_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_factorMaxima_before"
  err.flush

theorem geometryRow081_factorMaxima_read :
    rationalArrayField geometryRowsJson081 "factor_maxima" = .ok geometryRowsTyped081.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_gapWeightedMeans_before"
  err.flush

theorem geometryRow081_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson081 "gap_weighted_means" = .ok geometryRowsTyped081.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow081_floorChars : List Char := ['2', '8', '9', '5', '5', '7', '3', '5', '1', '4', '4', '8', '3', '9', '0', '8', '3']
noncomputable def geometryRow081_floorText : String := String.ofList geometryRow081_floorChars

theorem geometryRow081_floor_text_read :
    geometryRowsJson081.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow081_floorText := by rfl

theorem geometryRow081_floor_chars_parse :
    SourceJson.intChars geometryRow081_floorChars = some (28955735144839083 : Int) := by decide +kernel

theorem geometryRow081_floor_parse :
    parseInteger geometryRow081_floorText = .ok geometryRowsTyped081.jensenFloorQ96 := by
  simp only [geometryRow081_floorText, parseInteger, String.toList_ofList, geometryRow081_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_081 :
    decodeGeometryRow geometryRowsJson081 = .ok geometryRowsTyped081 :=
  original_geometryRow_of_fields geometryRowsJson081 geometryRowsTyped081 geometryRow081_floorText
    geometryRow081_simplexId_read geometryRow081_vertexIds_read
    geometryRow081_physicalVolume_read geometryRow081_meanGap_read
    geometryRow081_factorMaxima_read geometryRow081_gapWeightedMeans_read
    geometryRow081_jensenBound_read geometryRow081_floor_text_read geometryRow081_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_081_original_decoder_complete"
  err.flush

theorem geometryRow081_shape :
    geometryRowsTyped081.simplexId = 81 ∧
    geometryRowsTyped081.vertexIds.size = 9 ∧ geometryRowsTyped081.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped081.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped081.factorMaxima.size = 10 ∧ geometryRowsTyped081.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson082 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped082 : GeometryRow :=
  { simplexId := 82,
    vertexIds := #[32, 30, 28, 26, 25, 14, 13, 8, 0],
    physicalVolume := ((30016416749609598418268718212126771000869 : ℚ) / (68914145424096000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((18332072085073 : ℚ) / (213582600000000 : ℚ)), ((18614172177319 : ℚ) / (213582600000000 : ℚ)), ((166194739957 : ℚ) / (1392930000000 : ℚ)), ((8440623496031 : ℚ) / (91535400000000 : ℚ)), ((8390881833071 : ℚ) / (91535400000000 : ℚ)), ((263719830799 : ℚ) / (3640612500000 : ℚ)), ((2129259639257 : ℚ) / (58249800000000 : ℚ)), ((2038255005887 : ℚ) / (58249800000000 : ℚ)), ((964693276681 : ℚ) / (29124900000000 : ℚ)), ((19059097957079 : ℚ) / (640747800000000 : ℚ))],
    jensenBound := ((6821840764981532944809949026735450058343643258422931907536191266505626266008205059029713000000000000000000000000 : ℚ) / (3674924125627025580494480539953056600001110586362970898050922016993998598875697451397022852511468586201529161799922178236547 : ℚ)),
    jensenFloorQ96 := (147072943630413524 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_simplexId_before"
  err.flush

theorem geometryRow082_simplexId_read :
    geometryRowsJson082.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped082.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_vertexIds_before"
  err.flush

theorem geometryRow082_vertexIds_read :
    geometryRowsJson082.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped082.vertexIds := by decide +kernel

noncomputable def geometryRow082_physicalVolumeNumeratorChars : List Char := ['3', '0', '0', '1', '6', '4', '1', '6', '7', '4', '9', '6', '0', '9', '5', '9', '8', '4', '1', '8', '2', '6', '8', '7', '1', '8', '2', '1', '2', '1', '2', '6', '7', '7', '1', '0', '0', '0', '8', '6', '9']
noncomputable def geometryRow082_physicalVolumeDenominatorChars : List Char := ['6', '8', '9', '1', '4', '1', '4', '5', '4', '2', '4', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow082_physicalVolumeText : String := String.ofList (geometryRow082_physicalVolumeNumeratorChars ++ '/' :: geometryRow082_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_physicalVolume_before_field"
  err.flush

theorem geometryRow082_physicalVolume_field :
    geometryRowsJson082.getObjVal? "physical_volume" = .ok (.str geometryRow082_physicalVolumeText) := by rfl

theorem geometryRow082_physicalVolume_numerator_no_slash :
    geometryRow082_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow082_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow082_physicalVolumeNumeratorChars = some (30016416749609598418268718212126771000869 : Int) := by decide +kernel

theorem geometryRow082_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow082_physicalVolumeDenominatorChars = some (68914145424096000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow082_physicalVolume_denominator_nonzero : (68914145424096000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow082_physicalVolume_parse :
    parseRational geometryRow082_physicalVolumeText = .ok geometryRowsTyped082.physicalVolume :=
  original_rational_fraction_of_chars geometryRow082_physicalVolumeNumeratorChars geometryRow082_physicalVolumeDenominatorChars
    (30016416749609598418268718212126771000869 : Int) (68914145424096000000000000000000000000000000000000000000000000 : Int)
    geometryRow082_physicalVolume_numerator_no_slash geometryRow082_physicalVolume_numerator_parse
    geometryRow082_physicalVolume_denominator_parse geometryRow082_physicalVolume_denominator_nonzero

theorem geometryRow082_physicalVolume_read :
    rationalField geometryRowsJson082 "physical_volume" = .ok geometryRowsTyped082.physicalVolume :=
  original_rationalField_of_string geometryRowsJson082 "physical_volume" geometryRow082_physicalVolumeText
    geometryRowsTyped082.physicalVolume geometryRow082_physicalVolume_field geometryRow082_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_physicalVolume_complete"
  err.flush

noncomputable def geometryRow082_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow082_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow082_meanGapText : String := String.ofList (geometryRow082_meanGapNumeratorChars ++ '/' :: geometryRow082_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_meanGap_before_field"
  err.flush

theorem geometryRow082_meanGap_field :
    geometryRowsJson082.getObjVal? "mean_gap" = .ok (.str geometryRow082_meanGapText) := by rfl

theorem geometryRow082_meanGap_numerator_no_slash :
    geometryRow082_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow082_meanGap_numerator_parse :
    SourceJson.intChars geometryRow082_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow082_meanGap_denominator_parse :
    SourceJson.intChars geometryRow082_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow082_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow082_meanGap_parse :
    parseRational geometryRow082_meanGapText = .ok geometryRowsTyped082.meanGap :=
  original_rational_fraction_of_chars geometryRow082_meanGapNumeratorChars geometryRow082_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow082_meanGap_numerator_no_slash geometryRow082_meanGap_numerator_parse
    geometryRow082_meanGap_denominator_parse geometryRow082_meanGap_denominator_nonzero

theorem geometryRow082_meanGap_read :
    rationalField geometryRowsJson082 "mean_gap" = .ok geometryRowsTyped082.meanGap :=
  original_rationalField_of_string geometryRowsJson082 "mean_gap" geometryRow082_meanGapText
    geometryRowsTyped082.meanGap geometryRow082_meanGap_field geometryRow082_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_meanGap_complete"
  err.flush

noncomputable def geometryRow082_jensenBoundNumeratorChars : List Char := ['6', '8', '2', '1', '8', '4', '0', '7', '6', '4', '9', '8', '1', '5', '3', '2', '9', '4', '4', '8', '0', '9', '9', '4', '9', '0', '2', '6', '7', '3', '5', '4', '5', '0', '0', '5', '8', '3', '4', '3', '6', '4', '3', '2', '5', '8', '4', '2', '2', '9', '3', '1', '9', '0', '7', '5', '3', '6', '1', '9', '1', '2', '6', '6', '5', '0', '5', '6', '2', '6', '2', '6', '6', '0', '0', '8', '2', '0', '5', '0', '5', '9', '0', '2', '9', '7', '1', '3', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow082_jensenBoundDenominatorChars : List Char := ['3', '6', '7', '4', '9', '2', '4', '1', '2', '5', '6', '2', '7', '0', '2', '5', '5', '8', '0', '4', '9', '4', '4', '8', '0', '5', '3', '9', '9', '5', '3', '0', '5', '6', '6', '0', '0', '0', '0', '1', '1', '1', '0', '5', '8', '6', '3', '6', '2', '9', '7', '0', '8', '9', '8', '0', '5', '0', '9', '2', '2', '0', '1', '6', '9', '9', '3', '9', '9', '8', '5', '9', '8', '8', '7', '5', '6', '9', '7', '4', '5', '1', '3', '9', '7', '0', '2', '2', '8', '5', '2', '5', '1', '1', '4', '6', '8', '5', '8', '6', '2', '0', '1', '5', '2', '9', '1', '6', '1', '7', '9', '9', '9', '2', '2', '1', '7', '8', '2', '3', '6', '5', '4', '7']
noncomputable def geometryRow082_jensenBoundText : String := String.ofList (geometryRow082_jensenBoundNumeratorChars ++ '/' :: geometryRow082_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_jensenBound_before_field"
  err.flush

theorem geometryRow082_jensenBound_field :
    geometryRowsJson082.getObjVal? "jensen_bound" = .ok (.str geometryRow082_jensenBoundText) := by rfl

theorem geometryRow082_jensenBound_numerator_no_slash :
    geometryRow082_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow082_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow082_jensenBoundNumeratorChars = some (6821840764981532944809949026735450058343643258422931907536191266505626266008205059029713000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow082_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow082_jensenBoundDenominatorChars = some (3674924125627025580494480539953056600001110586362970898050922016993998598875697451397022852511468586201529161799922178236547 : Int) := by decide +kernel

theorem geometryRow082_jensenBound_denominator_nonzero : (3674924125627025580494480539953056600001110586362970898050922016993998598875697451397022852511468586201529161799922178236547 : Int) ≠ 0 := by decide +kernel

theorem geometryRow082_jensenBound_parse :
    parseRational geometryRow082_jensenBoundText = .ok geometryRowsTyped082.jensenBound :=
  original_rational_fraction_of_chars geometryRow082_jensenBoundNumeratorChars geometryRow082_jensenBoundDenominatorChars
    (6821840764981532944809949026735450058343643258422931907536191266505626266008205059029713000000000000000000000000 : Int) (3674924125627025580494480539953056600001110586362970898050922016993998598875697451397022852511468586201529161799922178236547 : Int)
    geometryRow082_jensenBound_numerator_no_slash geometryRow082_jensenBound_numerator_parse
    geometryRow082_jensenBound_denominator_parse geometryRow082_jensenBound_denominator_nonzero

theorem geometryRow082_jensenBound_read :
    rationalField geometryRowsJson082 "jensen_bound" = .ok geometryRowsTyped082.jensenBound :=
  original_rationalField_of_string geometryRowsJson082 "jensen_bound" geometryRow082_jensenBoundText
    geometryRowsTyped082.jensenBound geometryRow082_jensenBound_field geometryRow082_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_factorMaxima_before"
  err.flush

theorem geometryRow082_factorMaxima_read :
    rationalArrayField geometryRowsJson082 "factor_maxima" = .ok geometryRowsTyped082.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_gapWeightedMeans_before"
  err.flush

theorem geometryRow082_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson082 "gap_weighted_means" = .ok geometryRowsTyped082.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow082_floorChars : List Char := ['1', '4', '7', '0', '7', '2', '9', '4', '3', '6', '3', '0', '4', '1', '3', '5', '2', '4']
noncomputable def geometryRow082_floorText : String := String.ofList geometryRow082_floorChars

theorem geometryRow082_floor_text_read :
    geometryRowsJson082.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow082_floorText := by rfl

theorem geometryRow082_floor_chars_parse :
    SourceJson.intChars geometryRow082_floorChars = some (147072943630413524 : Int) := by decide +kernel

theorem geometryRow082_floor_parse :
    parseInteger geometryRow082_floorText = .ok geometryRowsTyped082.jensenFloorQ96 := by
  simp only [geometryRow082_floorText, parseInteger, String.toList_ofList, geometryRow082_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_082 :
    decodeGeometryRow geometryRowsJson082 = .ok geometryRowsTyped082 :=
  original_geometryRow_of_fields geometryRowsJson082 geometryRowsTyped082 geometryRow082_floorText
    geometryRow082_simplexId_read geometryRow082_vertexIds_read
    geometryRow082_physicalVolume_read geometryRow082_meanGap_read
    geometryRow082_factorMaxima_read geometryRow082_gapWeightedMeans_read
    geometryRow082_jensenBound_read geometryRow082_floor_text_read geometryRow082_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_082_original_decoder_complete"
  err.flush

theorem geometryRow082_shape :
    geometryRowsTyped082.simplexId = 82 ∧
    geometryRowsTyped082.vertexIds.size = 9 ∧ geometryRowsTyped082.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped082.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped082.factorMaxima.size = 10 ∧ geometryRowsTyped082.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson083 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped083 : GeometryRow :=
  { simplexId := 83,
    vertexIds := #[32, 30, 28, 26, 25, 22, 13, 4, 0],
    physicalVolume := ((3170678478425898091829134820666989686413 : ℚ) / (63703574020800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((96707389 : ℚ) / (66220000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((564191253477431195219 : ℚ) / (6628102015065300000000 : ℚ)), ((6712312628560271687 : ℚ) / (77070953663550000000 : ℚ)), ((576377571400716149 : ℚ) / (4802972474685000000 : ℚ)), ((7434851016237748613 : ℚ) / (78905976369825000000 : ℚ)), ((2463990788371170261 : ℚ) / (26301992123275000000 : ℚ)), ((1177422513184588799 : ℚ) / (16737631351175000000 : ℚ)), ((4754517733459149291 : ℚ) / (133901050809400000000 : ℚ)), ((13635965670286330543 : ℚ) / (401703152428200000000 : ℚ)), ((6551886734792911339 : ℚ) / (200851576214100000000 : ℚ)), ((2290954471285486889 : ℚ) / (77070953663550000000 : ℚ))],
    jensenBound := ((2227915688069898223284042400984842655063152019450798773054615650109823459146361758367254460203108249509380147685108853175169826060107422654804768944856083984375000000000000 : ℚ) / (4947281351292490803009522150588256159703369079465531155369298281007140013556982664034217668890657082893033418244426432272745702403230780251984009817895750355878262080899799121462339397 : ℚ)),
    jensenFloorQ96 := (35678922153147055 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_simplexId_before"
  err.flush

theorem geometryRow083_simplexId_read :
    geometryRowsJson083.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped083.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_vertexIds_before"
  err.flush

theorem geometryRow083_vertexIds_read :
    geometryRowsJson083.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped083.vertexIds := by decide +kernel

noncomputable def geometryRow083_physicalVolumeNumeratorChars : List Char := ['3', '1', '7', '0', '6', '7', '8', '4', '7', '8', '4', '2', '5', '8', '9', '8', '0', '9', '1', '8', '2', '9', '1', '3', '4', '8', '2', '0', '6', '6', '6', '9', '8', '9', '6', '8', '6', '4', '1', '3']
noncomputable def geometryRow083_physicalVolumeDenominatorChars : List Char := ['6', '3', '7', '0', '3', '5', '7', '4', '0', '2', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow083_physicalVolumeText : String := String.ofList (geometryRow083_physicalVolumeNumeratorChars ++ '/' :: geometryRow083_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_physicalVolume_before_field"
  err.flush

theorem geometryRow083_physicalVolume_field :
    geometryRowsJson083.getObjVal? "physical_volume" = .ok (.str geometryRow083_physicalVolumeText) := by rfl

theorem geometryRow083_physicalVolume_numerator_no_slash :
    geometryRow083_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow083_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow083_physicalVolumeNumeratorChars = some (3170678478425898091829134820666989686413 : Int) := by decide +kernel

theorem geometryRow083_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow083_physicalVolumeDenominatorChars = some (63703574020800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow083_physicalVolume_denominator_nonzero : (63703574020800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow083_physicalVolume_parse :
    parseRational geometryRow083_physicalVolumeText = .ok geometryRowsTyped083.physicalVolume :=
  original_rational_fraction_of_chars geometryRow083_physicalVolumeNumeratorChars geometryRow083_physicalVolumeDenominatorChars
    (3170678478425898091829134820666989686413 : Int) (63703574020800000000000000000000000000000000000000000000000000 : Int)
    geometryRow083_physicalVolume_numerator_no_slash geometryRow083_physicalVolume_numerator_parse
    geometryRow083_physicalVolume_denominator_parse geometryRow083_physicalVolume_denominator_nonzero

theorem geometryRow083_physicalVolume_read :
    rationalField geometryRowsJson083 "physical_volume" = .ok geometryRowsTyped083.physicalVolume :=
  original_rationalField_of_string geometryRowsJson083 "physical_volume" geometryRow083_physicalVolumeText
    geometryRowsTyped083.physicalVolume geometryRow083_physicalVolume_field geometryRow083_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_physicalVolume_complete"
  err.flush

noncomputable def geometryRow083_meanGapNumeratorChars : List Char := ['9', '6', '7', '0', '7', '3', '8', '9']
noncomputable def geometryRow083_meanGapDenominatorChars : List Char := ['6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow083_meanGapText : String := String.ofList (geometryRow083_meanGapNumeratorChars ++ '/' :: geometryRow083_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_meanGap_before_field"
  err.flush

theorem geometryRow083_meanGap_field :
    geometryRowsJson083.getObjVal? "mean_gap" = .ok (.str geometryRow083_meanGapText) := by rfl

theorem geometryRow083_meanGap_numerator_no_slash :
    geometryRow083_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow083_meanGap_numerator_parse :
    SourceJson.intChars geometryRow083_meanGapNumeratorChars = some (96707389 : Int) := by decide +kernel

theorem geometryRow083_meanGap_denominator_parse :
    SourceJson.intChars geometryRow083_meanGapDenominatorChars = some (66220000000 : Int) := by decide +kernel

theorem geometryRow083_meanGap_denominator_nonzero : (66220000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow083_meanGap_parse :
    parseRational geometryRow083_meanGapText = .ok geometryRowsTyped083.meanGap :=
  original_rational_fraction_of_chars geometryRow083_meanGapNumeratorChars geometryRow083_meanGapDenominatorChars
    (96707389 : Int) (66220000000 : Int)
    geometryRow083_meanGap_numerator_no_slash geometryRow083_meanGap_numerator_parse
    geometryRow083_meanGap_denominator_parse geometryRow083_meanGap_denominator_nonzero

theorem geometryRow083_meanGap_read :
    rationalField geometryRowsJson083 "mean_gap" = .ok geometryRowsTyped083.meanGap :=
  original_rationalField_of_string geometryRowsJson083 "mean_gap" geometryRow083_meanGapText
    geometryRowsTyped083.meanGap geometryRow083_meanGap_field geometryRow083_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_meanGap_complete"
  err.flush

noncomputable def geometryRow083_jensenBoundNumeratorChars : List Char := ['2', '2', '2', '7', '9', '1', '5', '6', '8', '8', '0', '6', '9', '8', '9', '8', '2', '2', '3', '2', '8', '4', '0', '4', '2', '4', '0', '0', '9', '8', '4', '8', '4', '2', '6', '5', '5', '0', '6', '3', '1', '5', '2', '0', '1', '9', '4', '5', '0', '7', '9', '8', '7', '7', '3', '0', '5', '4', '6', '1', '5', '6', '5', '0', '1', '0', '9', '8', '2', '3', '4', '5', '9', '1', '4', '6', '3', '6', '1', '7', '5', '8', '3', '6', '7', '2', '5', '4', '4', '6', '0', '2', '0', '3', '1', '0', '8', '2', '4', '9', '5', '0', '9', '3', '8', '0', '1', '4', '7', '6', '8', '5', '1', '0', '8', '8', '5', '3', '1', '7', '5', '1', '6', '9', '8', '2', '6', '0', '6', '0', '1', '0', '7', '4', '2', '2', '6', '5', '4', '8', '0', '4', '7', '6', '8', '9', '4', '4', '8', '5', '6', '0', '8', '3', '9', '8', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow083_jensenBoundDenominatorChars : List Char := ['4', '9', '4', '7', '2', '8', '1', '3', '5', '1', '2', '9', '2', '4', '9', '0', '8', '0', '3', '0', '0', '9', '5', '2', '2', '1', '5', '0', '5', '8', '8', '2', '5', '6', '1', '5', '9', '7', '0', '3', '3', '6', '9', '0', '7', '9', '4', '6', '5', '5', '3', '1', '1', '5', '5', '3', '6', '9', '2', '9', '8', '2', '8', '1', '0', '0', '7', '1', '4', '0', '0', '1', '3', '5', '5', '6', '9', '8', '2', '6', '6', '4', '0', '3', '4', '2', '1', '7', '6', '6', '8', '8', '9', '0', '6', '5', '7', '0', '8', '2', '8', '9', '3', '0', '3', '3', '4', '1', '8', '2', '4', '4', '4', '2', '6', '4', '3', '2', '2', '7', '2', '7', '4', '5', '7', '0', '2', '4', '0', '3', '2', '3', '0', '7', '8', '0', '2', '5', '1', '9', '8', '4', '0', '0', '9', '8', '1', '7', '8', '9', '5', '7', '5', '0', '3', '5', '5', '8', '7', '8', '2', '6', '2', '0', '8', '0', '8', '9', '9', '7', '9', '9', '1', '2', '1', '4', '6', '2', '3', '3', '9', '3', '9', '7']
noncomputable def geometryRow083_jensenBoundText : String := String.ofList (geometryRow083_jensenBoundNumeratorChars ++ '/' :: geometryRow083_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_jensenBound_before_field"
  err.flush

theorem geometryRow083_jensenBound_field :
    geometryRowsJson083.getObjVal? "jensen_bound" = .ok (.str geometryRow083_jensenBoundText) := by rfl

theorem geometryRow083_jensenBound_numerator_no_slash :
    geometryRow083_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow083_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow083_jensenBoundNumeratorChars = some (2227915688069898223284042400984842655063152019450798773054615650109823459146361758367254460203108249509380147685108853175169826060107422654804768944856083984375000000000000 : Int) := by decide +kernel

theorem geometryRow083_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow083_jensenBoundDenominatorChars = some (4947281351292490803009522150588256159703369079465531155369298281007140013556982664034217668890657082893033418244426432272745702403230780251984009817895750355878262080899799121462339397 : Int) := by decide +kernel

theorem geometryRow083_jensenBound_denominator_nonzero : (4947281351292490803009522150588256159703369079465531155369298281007140013556982664034217668890657082893033418244426432272745702403230780251984009817895750355878262080899799121462339397 : Int) ≠ 0 := by decide +kernel

theorem geometryRow083_jensenBound_parse :
    parseRational geometryRow083_jensenBoundText = .ok geometryRowsTyped083.jensenBound :=
  original_rational_fraction_of_chars geometryRow083_jensenBoundNumeratorChars geometryRow083_jensenBoundDenominatorChars
    (2227915688069898223284042400984842655063152019450798773054615650109823459146361758367254460203108249509380147685108853175169826060107422654804768944856083984375000000000000 : Int) (4947281351292490803009522150588256159703369079465531155369298281007140013556982664034217668890657082893033418244426432272745702403230780251984009817895750355878262080899799121462339397 : Int)
    geometryRow083_jensenBound_numerator_no_slash geometryRow083_jensenBound_numerator_parse
    geometryRow083_jensenBound_denominator_parse geometryRow083_jensenBound_denominator_nonzero

theorem geometryRow083_jensenBound_read :
    rationalField geometryRowsJson083 "jensen_bound" = .ok geometryRowsTyped083.jensenBound :=
  original_rationalField_of_string geometryRowsJson083 "jensen_bound" geometryRow083_jensenBoundText
    geometryRowsTyped083.jensenBound geometryRow083_jensenBound_field geometryRow083_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_factorMaxima_before"
  err.flush

theorem geometryRow083_factorMaxima_read :
    rationalArrayField geometryRowsJson083 "factor_maxima" = .ok geometryRowsTyped083.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_gapWeightedMeans_before"
  err.flush

theorem geometryRow083_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson083 "gap_weighted_means" = .ok geometryRowsTyped083.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow083_floorChars : List Char := ['3', '5', '6', '7', '8', '9', '2', '2', '1', '5', '3', '1', '4', '7', '0', '5', '5']
noncomputable def geometryRow083_floorText : String := String.ofList geometryRow083_floorChars

theorem geometryRow083_floor_text_read :
    geometryRowsJson083.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow083_floorText := by rfl

theorem geometryRow083_floor_chars_parse :
    SourceJson.intChars geometryRow083_floorChars = some (35678922153147055 : Int) := by decide +kernel

theorem geometryRow083_floor_parse :
    parseInteger geometryRow083_floorText = .ok geometryRowsTyped083.jensenFloorQ96 := by
  simp only [geometryRow083_floorText, parseInteger, String.toList_ofList, geometryRow083_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_083 :
    decodeGeometryRow geometryRowsJson083 = .ok geometryRowsTyped083 :=
  original_geometryRow_of_fields geometryRowsJson083 geometryRowsTyped083 geometryRow083_floorText
    geometryRow083_simplexId_read geometryRow083_vertexIds_read
    geometryRow083_physicalVolume_read geometryRow083_meanGap_read
    geometryRow083_factorMaxima_read geometryRow083_gapWeightedMeans_read
    geometryRow083_jensenBound_read geometryRow083_floor_text_read geometryRow083_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_083_original_decoder_complete"
  err.flush

theorem geometryRow083_shape :
    geometryRowsTyped083.simplexId = 83 ∧
    geometryRowsTyped083.vertexIds.size = 9 ∧ geometryRowsTyped083.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped083.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped083.factorMaxima.size = 10 ∧ geometryRowsTyped083.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson084 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped084 : GeometryRow :=
  { simplexId := 84,
    vertexIds := #[32, 30, 28, 26, 25, 22, 13, 8, 0],
    physicalVolume := ((23388187156902831448595540959296116762963 : ℚ) / (45714192652800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((16816888849 : ℚ) / (199237500000 : ℚ)), ((136640335361 : ℚ) / (1593900000000 : ℚ)), ((1249447487 : ℚ) / (10395000000 : ℚ)), ((63918011119 : ℚ) / (683100000000 : ℚ)), ((63546804679 : ℚ) / (683100000000 : ℚ)), ((31096859951 : ℚ) / (434700000000 : ℚ)), ((15693959773 : ℚ) / (434700000000 : ℚ)), ((7507410359 : ℚ) / (217350000000 : ℚ)), ((28877825981 : ℚ) / (869400000000 : ℚ)), ((139960677001 : ℚ) / (4781700000000 : ℚ))],
    jensenBound := ((3014846192332093080164885840299861846603164364206847519461768290672375009765625000000000000 : ℚ) / (1318250709161712575002640098534244963191979373396428527061911688648004069275414781045464647497191570101 : ℚ)),
    jensenFloorQ96 := (181195217587625483 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_simplexId_before"
  err.flush

theorem geometryRow084_simplexId_read :
    geometryRowsJson084.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped084.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_vertexIds_before"
  err.flush

theorem geometryRow084_vertexIds_read :
    geometryRowsJson084.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped084.vertexIds := by decide +kernel

noncomputable def geometryRow084_physicalVolumeNumeratorChars : List Char := ['2', '3', '3', '8', '8', '1', '8', '7', '1', '5', '6', '9', '0', '2', '8', '3', '1', '4', '4', '8', '5', '9', '5', '5', '4', '0', '9', '5', '9', '2', '9', '6', '1', '1', '6', '7', '6', '2', '9', '6', '3']
noncomputable def geometryRow084_physicalVolumeDenominatorChars : List Char := ['4', '5', '7', '1', '4', '1', '9', '2', '6', '5', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow084_physicalVolumeText : String := String.ofList (geometryRow084_physicalVolumeNumeratorChars ++ '/' :: geometryRow084_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_physicalVolume_before_field"
  err.flush

theorem geometryRow084_physicalVolume_field :
    geometryRowsJson084.getObjVal? "physical_volume" = .ok (.str geometryRow084_physicalVolumeText) := by rfl

theorem geometryRow084_physicalVolume_numerator_no_slash :
    geometryRow084_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow084_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow084_physicalVolumeNumeratorChars = some (23388187156902831448595540959296116762963 : Int) := by decide +kernel

theorem geometryRow084_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow084_physicalVolumeDenominatorChars = some (45714192652800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow084_physicalVolume_denominator_nonzero : (45714192652800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow084_physicalVolume_parse :
    parseRational geometryRow084_physicalVolumeText = .ok geometryRowsTyped084.physicalVolume :=
  original_rational_fraction_of_chars geometryRow084_physicalVolumeNumeratorChars geometryRow084_physicalVolumeDenominatorChars
    (23388187156902831448595540959296116762963 : Int) (45714192652800000000000000000000000000000000000000000000000000 : Int)
    geometryRow084_physicalVolume_numerator_no_slash geometryRow084_physicalVolume_numerator_parse
    geometryRow084_physicalVolume_denominator_parse geometryRow084_physicalVolume_denominator_nonzero

theorem geometryRow084_physicalVolume_read :
    rationalField geometryRowsJson084 "physical_volume" = .ok geometryRowsTyped084.physicalVolume :=
  original_rationalField_of_string geometryRowsJson084 "physical_volume" geometryRow084_physicalVolumeText
    geometryRowsTyped084.physicalVolume geometryRow084_physicalVolume_field geometryRow084_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_physicalVolume_complete"
  err.flush

noncomputable def geometryRow084_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow084_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow084_meanGapText : String := String.ofList (geometryRow084_meanGapNumeratorChars ++ '/' :: geometryRow084_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_meanGap_before_field"
  err.flush

theorem geometryRow084_meanGap_field :
    geometryRowsJson084.getObjVal? "mean_gap" = .ok (.str geometryRow084_meanGapText) := by rfl

theorem geometryRow084_meanGap_numerator_no_slash :
    geometryRow084_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow084_meanGap_numerator_parse :
    SourceJson.intChars geometryRow084_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow084_meanGap_denominator_parse :
    SourceJson.intChars geometryRow084_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow084_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow084_meanGap_parse :
    parseRational geometryRow084_meanGapText = .ok geometryRowsTyped084.meanGap :=
  original_rational_fraction_of_chars geometryRow084_meanGapNumeratorChars geometryRow084_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow084_meanGap_numerator_no_slash geometryRow084_meanGap_numerator_parse
    geometryRow084_meanGap_denominator_parse geometryRow084_meanGap_denominator_nonzero

theorem geometryRow084_meanGap_read :
    rationalField geometryRowsJson084 "mean_gap" = .ok geometryRowsTyped084.meanGap :=
  original_rationalField_of_string geometryRowsJson084 "mean_gap" geometryRow084_meanGapText
    geometryRowsTyped084.meanGap geometryRow084_meanGap_field geometryRow084_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_meanGap_complete"
  err.flush

noncomputable def geometryRow084_jensenBoundNumeratorChars : List Char := ['3', '0', '1', '4', '8', '4', '6', '1', '9', '2', '3', '3', '2', '0', '9', '3', '0', '8', '0', '1', '6', '4', '8', '8', '5', '8', '4', '0', '2', '9', '9', '8', '6', '1', '8', '4', '6', '6', '0', '3', '1', '6', '4', '3', '6', '4', '2', '0', '6', '8', '4', '7', '5', '1', '9', '4', '6', '1', '7', '6', '8', '2', '9', '0', '6', '7', '2', '3', '7', '5', '0', '0', '9', '7', '6', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow084_jensenBoundDenominatorChars : List Char := ['1', '3', '1', '8', '2', '5', '0', '7', '0', '9', '1', '6', '1', '7', '1', '2', '5', '7', '5', '0', '0', '2', '6', '4', '0', '0', '9', '8', '5', '3', '4', '2', '4', '4', '9', '6', '3', '1', '9', '1', '9', '7', '9', '3', '7', '3', '3', '9', '6', '4', '2', '8', '5', '2', '7', '0', '6', '1', '9', '1', '1', '6', '8', '8', '6', '4', '8', '0', '0', '4', '0', '6', '9', '2', '7', '5', '4', '1', '4', '7', '8', '1', '0', '4', '5', '4', '6', '4', '6', '4', '7', '4', '9', '7', '1', '9', '1', '5', '7', '0', '1', '0', '1']
noncomputable def geometryRow084_jensenBoundText : String := String.ofList (geometryRow084_jensenBoundNumeratorChars ++ '/' :: geometryRow084_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_jensenBound_before_field"
  err.flush

theorem geometryRow084_jensenBound_field :
    geometryRowsJson084.getObjVal? "jensen_bound" = .ok (.str geometryRow084_jensenBoundText) := by rfl

theorem geometryRow084_jensenBound_numerator_no_slash :
    geometryRow084_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow084_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow084_jensenBoundNumeratorChars = some (3014846192332093080164885840299861846603164364206847519461768290672375009765625000000000000 : Int) := by decide +kernel

theorem geometryRow084_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow084_jensenBoundDenominatorChars = some (1318250709161712575002640098534244963191979373396428527061911688648004069275414781045464647497191570101 : Int) := by decide +kernel

theorem geometryRow084_jensenBound_denominator_nonzero : (1318250709161712575002640098534244963191979373396428527061911688648004069275414781045464647497191570101 : Int) ≠ 0 := by decide +kernel

theorem geometryRow084_jensenBound_parse :
    parseRational geometryRow084_jensenBoundText = .ok geometryRowsTyped084.jensenBound :=
  original_rational_fraction_of_chars geometryRow084_jensenBoundNumeratorChars geometryRow084_jensenBoundDenominatorChars
    (3014846192332093080164885840299861846603164364206847519461768290672375009765625000000000000 : Int) (1318250709161712575002640098534244963191979373396428527061911688648004069275414781045464647497191570101 : Int)
    geometryRow084_jensenBound_numerator_no_slash geometryRow084_jensenBound_numerator_parse
    geometryRow084_jensenBound_denominator_parse geometryRow084_jensenBound_denominator_nonzero

theorem geometryRow084_jensenBound_read :
    rationalField geometryRowsJson084 "jensen_bound" = .ok geometryRowsTyped084.jensenBound :=
  original_rationalField_of_string geometryRowsJson084 "jensen_bound" geometryRow084_jensenBoundText
    geometryRowsTyped084.jensenBound geometryRow084_jensenBound_field geometryRow084_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_factorMaxima_before"
  err.flush

theorem geometryRow084_factorMaxima_read :
    rationalArrayField geometryRowsJson084 "factor_maxima" = .ok geometryRowsTyped084.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_gapWeightedMeans_before"
  err.flush

theorem geometryRow084_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson084 "gap_weighted_means" = .ok geometryRowsTyped084.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow084_floorChars : List Char := ['1', '8', '1', '1', '9', '5', '2', '1', '7', '5', '8', '7', '6', '2', '5', '4', '8', '3']
noncomputable def geometryRow084_floorText : String := String.ofList geometryRow084_floorChars

theorem geometryRow084_floor_text_read :
    geometryRowsJson084.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow084_floorText := by rfl

theorem geometryRow084_floor_chars_parse :
    SourceJson.intChars geometryRow084_floorChars = some (181195217587625483 : Int) := by decide +kernel

theorem geometryRow084_floor_parse :
    parseInteger geometryRow084_floorText = .ok geometryRowsTyped084.jensenFloorQ96 := by
  simp only [geometryRow084_floorText, parseInteger, String.toList_ofList, geometryRow084_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_084 :
    decodeGeometryRow geometryRowsJson084 = .ok geometryRowsTyped084 :=
  original_geometryRow_of_fields geometryRowsJson084 geometryRowsTyped084 geometryRow084_floorText
    geometryRow084_simplexId_read geometryRow084_vertexIds_read
    geometryRow084_physicalVolume_read geometryRow084_meanGap_read
    geometryRow084_factorMaxima_read geometryRow084_gapWeightedMeans_read
    geometryRow084_jensenBound_read geometryRow084_floor_text_read geometryRow084_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_084_original_decoder_complete"
  err.flush

theorem geometryRow084_shape :
    geometryRowsTyped084.simplexId = 84 ∧
    geometryRowsTyped084.vertexIds.size = 9 ∧ geometryRowsTyped084.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped084.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped084.factorMaxima.size = 10 ∧ geometryRowsTyped084.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson085 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped085 : GeometryRow :=
  { simplexId := 85,
    vertexIds := #[32, 30, 28, 26, 25, 22, 21, 8, 0],
    physicalVolume := ((986461703442331831143011943986162775211 : ℚ) / (2129543136000000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((496879 : ℚ) / (5600000 : ℚ)), ((10171707 : ℚ) / (110000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((262346803003 : ℚ) / (3187800000000 : ℚ)), ((266557252141 : ℚ) / (3187800000000 : ℚ)), ((289224171421 : ℚ) / (2390850000000 : ℚ)), ((129854367413 : ℚ) / (1366200000000 : ℚ)), ((129111954533 : ℚ) / (1366200000000 : ℚ)), ((3872716423 : ℚ) / (54337500000 : ℚ)), ((31272790979 : ℚ) / (869400000000 : ℚ)), ((29914512869 : ℚ) / (869400000000 : ℚ)), ((14381348707 : ℚ) / (434700000000 : ℚ)), ((273197935421 : ℚ) / (9563400000000 : ℚ))],
    jensenBound := ((957039490966232269473230280649513504869203929062104006902825722270624793185000000000000000000000 : ℚ) / (438805942383738650721778212434351936747164169911437558096770234303306098481375717304109124037109418237349247 : ℚ)),
    jensenFloorQ96 := (172797296023244064 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_simplexId_before"
  err.flush

theorem geometryRow085_simplexId_read :
    geometryRowsJson085.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped085.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_vertexIds_before"
  err.flush

theorem geometryRow085_vertexIds_read :
    geometryRowsJson085.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped085.vertexIds := by decide +kernel

noncomputable def geometryRow085_physicalVolumeNumeratorChars : List Char := ['9', '8', '6', '4', '6', '1', '7', '0', '3', '4', '4', '2', '3', '3', '1', '8', '3', '1', '1', '4', '3', '0', '1', '1', '9', '4', '3', '9', '8', '6', '1', '6', '2', '7', '7', '5', '2', '1', '1']
noncomputable def geometryRow085_physicalVolumeDenominatorChars : List Char := ['2', '1', '2', '9', '5', '4', '3', '1', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow085_physicalVolumeText : String := String.ofList (geometryRow085_physicalVolumeNumeratorChars ++ '/' :: geometryRow085_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_physicalVolume_before_field"
  err.flush

theorem geometryRow085_physicalVolume_field :
    geometryRowsJson085.getObjVal? "physical_volume" = .ok (.str geometryRow085_physicalVolumeText) := by rfl

theorem geometryRow085_physicalVolume_numerator_no_slash :
    geometryRow085_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow085_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow085_physicalVolumeNumeratorChars = some (986461703442331831143011943986162775211 : Int) := by decide +kernel

theorem geometryRow085_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow085_physicalVolumeDenominatorChars = some (2129543136000000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow085_physicalVolume_denominator_nonzero : (2129543136000000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow085_physicalVolume_parse :
    parseRational geometryRow085_physicalVolumeText = .ok geometryRowsTyped085.physicalVolume :=
  original_rational_fraction_of_chars geometryRow085_physicalVolumeNumeratorChars geometryRow085_physicalVolumeDenominatorChars
    (986461703442331831143011943986162775211 : Int) (2129543136000000000000000000000000000000000000000000000000000 : Int)
    geometryRow085_physicalVolume_numerator_no_slash geometryRow085_physicalVolume_numerator_parse
    geometryRow085_physicalVolume_denominator_parse geometryRow085_physicalVolume_denominator_nonzero

theorem geometryRow085_physicalVolume_read :
    rationalField geometryRowsJson085 "physical_volume" = .ok geometryRowsTyped085.physicalVolume :=
  original_rationalField_of_string geometryRowsJson085 "physical_volume" geometryRow085_physicalVolumeText
    geometryRowsTyped085.physicalVolume geometryRow085_physicalVolume_field geometryRow085_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_physicalVolume_complete"
  err.flush

noncomputable def geometryRow085_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow085_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow085_meanGapText : String := String.ofList (geometryRow085_meanGapNumeratorChars ++ '/' :: geometryRow085_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_meanGap_before_field"
  err.flush

theorem geometryRow085_meanGap_field :
    geometryRowsJson085.getObjVal? "mean_gap" = .ok (.str geometryRow085_meanGapText) := by rfl

theorem geometryRow085_meanGap_numerator_no_slash :
    geometryRow085_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow085_meanGap_numerator_parse :
    SourceJson.intChars geometryRow085_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow085_meanGap_denominator_parse :
    SourceJson.intChars geometryRow085_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow085_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow085_meanGap_parse :
    parseRational geometryRow085_meanGapText = .ok geometryRowsTyped085.meanGap :=
  original_rational_fraction_of_chars geometryRow085_meanGapNumeratorChars geometryRow085_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow085_meanGap_numerator_no_slash geometryRow085_meanGap_numerator_parse
    geometryRow085_meanGap_denominator_parse geometryRow085_meanGap_denominator_nonzero

theorem geometryRow085_meanGap_read :
    rationalField geometryRowsJson085 "mean_gap" = .ok geometryRowsTyped085.meanGap :=
  original_rationalField_of_string geometryRowsJson085 "mean_gap" geometryRow085_meanGapText
    geometryRowsTyped085.meanGap geometryRow085_meanGap_field geometryRow085_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_meanGap_complete"
  err.flush

noncomputable def geometryRow085_jensenBoundNumeratorChars : List Char := ['9', '5', '7', '0', '3', '9', '4', '9', '0', '9', '6', '6', '2', '3', '2', '2', '6', '9', '4', '7', '3', '2', '3', '0', '2', '8', '0', '6', '4', '9', '5', '1', '3', '5', '0', '4', '8', '6', '9', '2', '0', '3', '9', '2', '9', '0', '6', '2', '1', '0', '4', '0', '0', '6', '9', '0', '2', '8', '2', '5', '7', '2', '2', '2', '7', '0', '6', '2', '4', '7', '9', '3', '1', '8', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow085_jensenBoundDenominatorChars : List Char := ['4', '3', '8', '8', '0', '5', '9', '4', '2', '3', '8', '3', '7', '3', '8', '6', '5', '0', '7', '2', '1', '7', '7', '8', '2', '1', '2', '4', '3', '4', '3', '5', '1', '9', '3', '6', '7', '4', '7', '1', '6', '4', '1', '6', '9', '9', '1', '1', '4', '3', '7', '5', '5', '8', '0', '9', '6', '7', '7', '0', '2', '3', '4', '3', '0', '3', '3', '0', '6', '0', '9', '8', '4', '8', '1', '3', '7', '5', '7', '1', '7', '3', '0', '4', '1', '0', '9', '1', '2', '4', '0', '3', '7', '1', '0', '9', '4', '1', '8', '2', '3', '7', '3', '4', '9', '2', '4', '7']
noncomputable def geometryRow085_jensenBoundText : String := String.ofList (geometryRow085_jensenBoundNumeratorChars ++ '/' :: geometryRow085_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_jensenBound_before_field"
  err.flush

theorem geometryRow085_jensenBound_field :
    geometryRowsJson085.getObjVal? "jensen_bound" = .ok (.str geometryRow085_jensenBoundText) := by rfl

theorem geometryRow085_jensenBound_numerator_no_slash :
    geometryRow085_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow085_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow085_jensenBoundNumeratorChars = some (957039490966232269473230280649513504869203929062104006902825722270624793185000000000000000000000 : Int) := by decide +kernel

theorem geometryRow085_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow085_jensenBoundDenominatorChars = some (438805942383738650721778212434351936747164169911437558096770234303306098481375717304109124037109418237349247 : Int) := by decide +kernel

theorem geometryRow085_jensenBound_denominator_nonzero : (438805942383738650721778212434351936747164169911437558096770234303306098481375717304109124037109418237349247 : Int) ≠ 0 := by decide +kernel

theorem geometryRow085_jensenBound_parse :
    parseRational geometryRow085_jensenBoundText = .ok geometryRowsTyped085.jensenBound :=
  original_rational_fraction_of_chars geometryRow085_jensenBoundNumeratorChars geometryRow085_jensenBoundDenominatorChars
    (957039490966232269473230280649513504869203929062104006902825722270624793185000000000000000000000 : Int) (438805942383738650721778212434351936747164169911437558096770234303306098481375717304109124037109418237349247 : Int)
    geometryRow085_jensenBound_numerator_no_slash geometryRow085_jensenBound_numerator_parse
    geometryRow085_jensenBound_denominator_parse geometryRow085_jensenBound_denominator_nonzero

theorem geometryRow085_jensenBound_read :
    rationalField geometryRowsJson085 "jensen_bound" = .ok geometryRowsTyped085.jensenBound :=
  original_rationalField_of_string geometryRowsJson085 "jensen_bound" geometryRow085_jensenBoundText
    geometryRowsTyped085.jensenBound geometryRow085_jensenBound_field geometryRow085_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_factorMaxima_before"
  err.flush

theorem geometryRow085_factorMaxima_read :
    rationalArrayField geometryRowsJson085 "factor_maxima" = .ok geometryRowsTyped085.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_gapWeightedMeans_before"
  err.flush

theorem geometryRow085_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson085 "gap_weighted_means" = .ok geometryRowsTyped085.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow085_floorChars : List Char := ['1', '7', '2', '7', '9', '7', '2', '9', '6', '0', '2', '3', '2', '4', '4', '0', '6', '4']
noncomputable def geometryRow085_floorText : String := String.ofList geometryRow085_floorChars

theorem geometryRow085_floor_text_read :
    geometryRowsJson085.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow085_floorText := by rfl

theorem geometryRow085_floor_chars_parse :
    SourceJson.intChars geometryRow085_floorChars = some (172797296023244064 : Int) := by decide +kernel

theorem geometryRow085_floor_parse :
    parseInteger geometryRow085_floorText = .ok geometryRowsTyped085.jensenFloorQ96 := by
  simp only [geometryRow085_floorText, parseInteger, String.toList_ofList, geometryRow085_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_085 :
    decodeGeometryRow geometryRowsJson085 = .ok geometryRowsTyped085 :=
  original_geometryRow_of_fields geometryRowsJson085 geometryRowsTyped085 geometryRow085_floorText
    geometryRow085_simplexId_read geometryRow085_vertexIds_read
    geometryRow085_physicalVolume_read geometryRow085_meanGap_read
    geometryRow085_factorMaxima_read geometryRow085_gapWeightedMeans_read
    geometryRow085_jensenBound_read geometryRow085_floor_text_read geometryRow085_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_085_original_decoder_complete"
  err.flush

theorem geometryRow085_shape :
    geometryRowsTyped085.simplexId = 85 ∧
    geometryRowsTyped085.vertexIds.size = 9 ∧ geometryRowsTyped085.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped085.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped085.factorMaxima.size = 10 ∧ geometryRowsTyped085.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson086 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped086 : GeometryRow :=
  { simplexId := 86,
    vertexIds := #[32, 30, 28, 26, 25, 24, 14, 4, 3],
    physicalVolume := ((89821842529680456552887621424182973442583 : ℚ) / (1149057370981094400000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1071703 : ℚ) / (722400000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((25 : ℚ) / (688 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((6176444194305340097 : ℚ) / (71582369936112000000 : ℚ)), ((157995673745976818357 : ℚ) / (1789559248402800000000 : ℚ)), ((2008124215171 : ℚ) / (16698276000000 : ℚ)), ((3493424815151 : ℚ) / (37107280000000 : ℚ)), ((10419780544237 : ℚ) / (111321840000000 : ℚ)), ((2345137377493 : ℚ) / (33396552000000 : ℚ)), ((11837492579891 : ℚ) / (333965520000000 : ℚ)), ((11315732681903 : ℚ) / (333965520000000 : ℚ)), ((7996580802625593373 : ℚ) / (255651321200400000000 : ℚ)), ((53907868012094311879 : ℚ) / (1789559248402800000000 : ℚ))],
    jensenBound := ((634989529025741278929223469015166418100873696910219581834786117318353474317345008051711985418356701258712176210906870710272000000000000000000 : ℚ) / (878129874215927894304483710805811606753339155792653302612318194401309305160815774608928863254386649017205684312908739673240030304942152037387516923246589 : ℚ)),
    jensenFloorQ96 := (57291130933710664 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_simplexId_before"
  err.flush

theorem geometryRow086_simplexId_read :
    geometryRowsJson086.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped086.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_vertexIds_before"
  err.flush

theorem geometryRow086_vertexIds_read :
    geometryRowsJson086.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped086.vertexIds := by decide +kernel

noncomputable def geometryRow086_physicalVolumeNumeratorChars : List Char := ['8', '9', '8', '2', '1', '8', '4', '2', '5', '2', '9', '6', '8', '0', '4', '5', '6', '5', '5', '2', '8', '8', '7', '6', '2', '1', '4', '2', '4', '1', '8', '2', '9', '7', '3', '4', '4', '2', '5', '8', '3']
noncomputable def geometryRow086_physicalVolumeDenominatorChars : List Char := ['1', '1', '4', '9', '0', '5', '7', '3', '7', '0', '9', '8', '1', '0', '9', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow086_physicalVolumeText : String := String.ofList (geometryRow086_physicalVolumeNumeratorChars ++ '/' :: geometryRow086_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_physicalVolume_before_field"
  err.flush

theorem geometryRow086_physicalVolume_field :
    geometryRowsJson086.getObjVal? "physical_volume" = .ok (.str geometryRow086_physicalVolumeText) := by rfl

theorem geometryRow086_physicalVolume_numerator_no_slash :
    geometryRow086_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow086_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow086_physicalVolumeNumeratorChars = some (89821842529680456552887621424182973442583 : Int) := by decide +kernel

theorem geometryRow086_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow086_physicalVolumeDenominatorChars = some (1149057370981094400000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow086_physicalVolume_denominator_nonzero : (1149057370981094400000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow086_physicalVolume_parse :
    parseRational geometryRow086_physicalVolumeText = .ok geometryRowsTyped086.physicalVolume :=
  original_rational_fraction_of_chars geometryRow086_physicalVolumeNumeratorChars geometryRow086_physicalVolumeDenominatorChars
    (89821842529680456552887621424182973442583 : Int) (1149057370981094400000000000000000000000000000000000000000000000 : Int)
    geometryRow086_physicalVolume_numerator_no_slash geometryRow086_physicalVolume_numerator_parse
    geometryRow086_physicalVolume_denominator_parse geometryRow086_physicalVolume_denominator_nonzero

theorem geometryRow086_physicalVolume_read :
    rationalField geometryRowsJson086 "physical_volume" = .ok geometryRowsTyped086.physicalVolume :=
  original_rationalField_of_string geometryRowsJson086 "physical_volume" geometryRow086_physicalVolumeText
    geometryRowsTyped086.physicalVolume geometryRow086_physicalVolume_field geometryRow086_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_physicalVolume_complete"
  err.flush

noncomputable def geometryRow086_meanGapNumeratorChars : List Char := ['1', '0', '7', '1', '7', '0', '3']
noncomputable def geometryRow086_meanGapDenominatorChars : List Char := ['7', '2', '2', '4', '0', '0', '0', '0', '0']
noncomputable def geometryRow086_meanGapText : String := String.ofList (geometryRow086_meanGapNumeratorChars ++ '/' :: geometryRow086_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_meanGap_before_field"
  err.flush

theorem geometryRow086_meanGap_field :
    geometryRowsJson086.getObjVal? "mean_gap" = .ok (.str geometryRow086_meanGapText) := by rfl

theorem geometryRow086_meanGap_numerator_no_slash :
    geometryRow086_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow086_meanGap_numerator_parse :
    SourceJson.intChars geometryRow086_meanGapNumeratorChars = some (1071703 : Int) := by decide +kernel

theorem geometryRow086_meanGap_denominator_parse :
    SourceJson.intChars geometryRow086_meanGapDenominatorChars = some (722400000 : Int) := by decide +kernel

theorem geometryRow086_meanGap_denominator_nonzero : (722400000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow086_meanGap_parse :
    parseRational geometryRow086_meanGapText = .ok geometryRowsTyped086.meanGap :=
  original_rational_fraction_of_chars geometryRow086_meanGapNumeratorChars geometryRow086_meanGapDenominatorChars
    (1071703 : Int) (722400000 : Int)
    geometryRow086_meanGap_numerator_no_slash geometryRow086_meanGap_numerator_parse
    geometryRow086_meanGap_denominator_parse geometryRow086_meanGap_denominator_nonzero

theorem geometryRow086_meanGap_read :
    rationalField geometryRowsJson086 "mean_gap" = .ok geometryRowsTyped086.meanGap :=
  original_rationalField_of_string geometryRowsJson086 "mean_gap" geometryRow086_meanGapText
    geometryRowsTyped086.meanGap geometryRow086_meanGap_field geometryRow086_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_meanGap_complete"
  err.flush

noncomputable def geometryRow086_jensenBoundNumeratorChars : List Char := ['6', '3', '4', '9', '8', '9', '5', '2', '9', '0', '2', '5', '7', '4', '1', '2', '7', '8', '9', '2', '9', '2', '2', '3', '4', '6', '9', '0', '1', '5', '1', '6', '6', '4', '1', '8', '1', '0', '0', '8', '7', '3', '6', '9', '6', '9', '1', '0', '2', '1', '9', '5', '8', '1', '8', '3', '4', '7', '8', '6', '1', '1', '7', '3', '1', '8', '3', '5', '3', '4', '7', '4', '3', '1', '7', '3', '4', '5', '0', '0', '8', '0', '5', '1', '7', '1', '1', '9', '8', '5', '4', '1', '8', '3', '5', '6', '7', '0', '1', '2', '5', '8', '7', '1', '2', '1', '7', '6', '2', '1', '0', '9', '0', '6', '8', '7', '0', '7', '1', '0', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow086_jensenBoundDenominatorChars : List Char := ['8', '7', '8', '1', '2', '9', '8', '7', '4', '2', '1', '5', '9', '2', '7', '8', '9', '4', '3', '0', '4', '4', '8', '3', '7', '1', '0', '8', '0', '5', '8', '1', '1', '6', '0', '6', '7', '5', '3', '3', '3', '9', '1', '5', '5', '7', '9', '2', '6', '5', '3', '3', '0', '2', '6', '1', '2', '3', '1', '8', '1', '9', '4', '4', '0', '1', '3', '0', '9', '3', '0', '5', '1', '6', '0', '8', '1', '5', '7', '7', '4', '6', '0', '8', '9', '2', '8', '8', '6', '3', '2', '5', '4', '3', '8', '6', '6', '4', '9', '0', '1', '7', '2', '0', '5', '6', '8', '4', '3', '1', '2', '9', '0', '8', '7', '3', '9', '6', '7', '3', '2', '4', '0', '0', '3', '0', '3', '0', '4', '9', '4', '2', '1', '5', '2', '0', '3', '7', '3', '8', '7', '5', '1', '6', '9', '2', '3', '2', '4', '6', '5', '8', '9']
noncomputable def geometryRow086_jensenBoundText : String := String.ofList (geometryRow086_jensenBoundNumeratorChars ++ '/' :: geometryRow086_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_jensenBound_before_field"
  err.flush

theorem geometryRow086_jensenBound_field :
    geometryRowsJson086.getObjVal? "jensen_bound" = .ok (.str geometryRow086_jensenBoundText) := by rfl

theorem geometryRow086_jensenBound_numerator_no_slash :
    geometryRow086_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow086_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow086_jensenBoundNumeratorChars = some (634989529025741278929223469015166418100873696910219581834786117318353474317345008051711985418356701258712176210906870710272000000000000000000 : Int) := by decide +kernel

theorem geometryRow086_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow086_jensenBoundDenominatorChars = some (878129874215927894304483710805811606753339155792653302612318194401309305160815774608928863254386649017205684312908739673240030304942152037387516923246589 : Int) := by decide +kernel

theorem geometryRow086_jensenBound_denominator_nonzero : (878129874215927894304483710805811606753339155792653302612318194401309305160815774608928863254386649017205684312908739673240030304942152037387516923246589 : Int) ≠ 0 := by decide +kernel

theorem geometryRow086_jensenBound_parse :
    parseRational geometryRow086_jensenBoundText = .ok geometryRowsTyped086.jensenBound :=
  original_rational_fraction_of_chars geometryRow086_jensenBoundNumeratorChars geometryRow086_jensenBoundDenominatorChars
    (634989529025741278929223469015166418100873696910219581834786117318353474317345008051711985418356701258712176210906870710272000000000000000000 : Int) (878129874215927894304483710805811606753339155792653302612318194401309305160815774608928863254386649017205684312908739673240030304942152037387516923246589 : Int)
    geometryRow086_jensenBound_numerator_no_slash geometryRow086_jensenBound_numerator_parse
    geometryRow086_jensenBound_denominator_parse geometryRow086_jensenBound_denominator_nonzero

theorem geometryRow086_jensenBound_read :
    rationalField geometryRowsJson086 "jensen_bound" = .ok geometryRowsTyped086.jensenBound :=
  original_rationalField_of_string geometryRowsJson086 "jensen_bound" geometryRow086_jensenBoundText
    geometryRowsTyped086.jensenBound geometryRow086_jensenBound_field geometryRow086_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_factorMaxima_before"
  err.flush

theorem geometryRow086_factorMaxima_read :
    rationalArrayField geometryRowsJson086 "factor_maxima" = .ok geometryRowsTyped086.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_gapWeightedMeans_before"
  err.flush

theorem geometryRow086_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson086 "gap_weighted_means" = .ok geometryRowsTyped086.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow086_floorChars : List Char := ['5', '7', '2', '9', '1', '1', '3', '0', '9', '3', '3', '7', '1', '0', '6', '6', '4']
noncomputable def geometryRow086_floorText : String := String.ofList geometryRow086_floorChars

theorem geometryRow086_floor_text_read :
    geometryRowsJson086.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow086_floorText := by rfl

theorem geometryRow086_floor_chars_parse :
    SourceJson.intChars geometryRow086_floorChars = some (57291130933710664 : Int) := by decide +kernel

theorem geometryRow086_floor_parse :
    parseInteger geometryRow086_floorText = .ok geometryRowsTyped086.jensenFloorQ96 := by
  simp only [geometryRow086_floorText, parseInteger, String.toList_ofList, geometryRow086_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_086 :
    decodeGeometryRow geometryRowsJson086 = .ok geometryRowsTyped086 :=
  original_geometryRow_of_fields geometryRowsJson086 geometryRowsTyped086 geometryRow086_floorText
    geometryRow086_simplexId_read geometryRow086_vertexIds_read
    geometryRow086_physicalVolume_read geometryRow086_meanGap_read
    geometryRow086_factorMaxima_read geometryRow086_gapWeightedMeans_read
    geometryRow086_jensenBound_read geometryRow086_floor_text_read geometryRow086_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_086_original_decoder_complete"
  err.flush

theorem geometryRow086_shape :
    geometryRowsTyped086.simplexId = 86 ∧
    geometryRowsTyped086.vertexIds.size = 9 ∧ geometryRowsTyped086.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped086.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped086.factorMaxima.size = 10 ∧ geometryRowsTyped086.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson087 : SourceJson :=
  (SimplicesBlock010.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped087 : GeometryRow :=
  { simplexId := 87,
    vertexIds := #[32, 30, 28, 26, 25, 24, 14, 7, 3],
    physicalVolume := ((7468330536965648057443652938814764449349 : ℚ) / (101799102633984000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((49290167 : ℚ) / (34056000000 : ℚ)),
    factorMaxima := #[((1648423 : ℚ) / (16750000 : ℚ)), ((1648423 : ℚ) / (16750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((27702761 : ℚ) / (276000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((32031 : ℚ) / (418750 : ℚ)), ((515617 : ℚ) / (12000000 : ℚ)), ((32031 : ℚ) / (837500 : ℚ)), ((5921703 : ℚ) / (172000000 : ℚ)), ((1648423 : ℚ) / (50250000 : ℚ))],
    gapWeightedMeans := #[((2246831727833192123707 : ℚ) / (25867625540494320000000 : ℚ)), ((2297409827026753805281 : ℚ) / (25867625540494320000000 : ℚ)), ((5448744939657052893533 : ℚ) / (45268344695865060000000 : ℚ)), ((5672359230902629867817 : ℚ) / (60357792927820080000000 : ℚ)), ((75194132419667070587 : ℚ) / (804770572370934400000 : ℚ)), ((6363974585492546087069 : ℚ) / (90536689391730120000000 : ℚ)), ((6424594719256056013631 : ℚ) / (181073378783460240000000 : ℚ)), ((245668030467720387587 : ℚ) / (7242935151338409600000 : ℚ)), ((794141751803046376841 : ℚ) / (25867625540494320000000 : ℚ)), ((783765371626821776171 : ℚ) / (25867625540494320000000 : ℚ))],
    jensenBound := ((7092973076169660839978901292881172000649095804513270417138870328915934563791976245694301227912223223137213497575419557275705834109489285818451026927250617048419704498557271344291099705344000000000000 : ℚ) / (10714256990100998485525886390069085214997437985524936698524260626177669754846200122177727498168264197831787673836895415203777625510012253353317005778777573206594789531011621330274204377817210479634079265809922041 : ℚ)),
    jensenFloorQ96 := (52450041482790115 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_simplexId_before"
  err.flush

theorem geometryRow087_simplexId_read :
    geometryRowsJson087.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped087.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_vertexIds_before"
  err.flush

theorem geometryRow087_vertexIds_read :
    geometryRowsJson087.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped087.vertexIds := by decide +kernel

noncomputable def geometryRow087_physicalVolumeNumeratorChars : List Char := ['7', '4', '6', '8', '3', '3', '0', '5', '3', '6', '9', '6', '5', '6', '4', '8', '0', '5', '7', '4', '4', '3', '6', '5', '2', '9', '3', '8', '8', '1', '4', '7', '6', '4', '4', '4', '9', '3', '4', '9']
noncomputable def geometryRow087_physicalVolumeDenominatorChars : List Char := ['1', '0', '1', '7', '9', '9', '1', '0', '2', '6', '3', '3', '9', '8', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow087_physicalVolumeText : String := String.ofList (geometryRow087_physicalVolumeNumeratorChars ++ '/' :: geometryRow087_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_physicalVolume_before_field"
  err.flush

theorem geometryRow087_physicalVolume_field :
    geometryRowsJson087.getObjVal? "physical_volume" = .ok (.str geometryRow087_physicalVolumeText) := by rfl

theorem geometryRow087_physicalVolume_numerator_no_slash :
    geometryRow087_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow087_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow087_physicalVolumeNumeratorChars = some (7468330536965648057443652938814764449349 : Int) := by decide +kernel

theorem geometryRow087_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow087_physicalVolumeDenominatorChars = some (101799102633984000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow087_physicalVolume_denominator_nonzero : (101799102633984000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow087_physicalVolume_parse :
    parseRational geometryRow087_physicalVolumeText = .ok geometryRowsTyped087.physicalVolume :=
  original_rational_fraction_of_chars geometryRow087_physicalVolumeNumeratorChars geometryRow087_physicalVolumeDenominatorChars
    (7468330536965648057443652938814764449349 : Int) (101799102633984000000000000000000000000000000000000000000000000 : Int)
    geometryRow087_physicalVolume_numerator_no_slash geometryRow087_physicalVolume_numerator_parse
    geometryRow087_physicalVolume_denominator_parse geometryRow087_physicalVolume_denominator_nonzero

theorem geometryRow087_physicalVolume_read :
    rationalField geometryRowsJson087 "physical_volume" = .ok geometryRowsTyped087.physicalVolume :=
  original_rationalField_of_string geometryRowsJson087 "physical_volume" geometryRow087_physicalVolumeText
    geometryRowsTyped087.physicalVolume geometryRow087_physicalVolume_field geometryRow087_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_physicalVolume_complete"
  err.flush

noncomputable def geometryRow087_meanGapNumeratorChars : List Char := ['4', '9', '2', '9', '0', '1', '6', '7']
noncomputable def geometryRow087_meanGapDenominatorChars : List Char := ['3', '4', '0', '5', '6', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow087_meanGapText : String := String.ofList (geometryRow087_meanGapNumeratorChars ++ '/' :: geometryRow087_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_meanGap_before_field"
  err.flush

theorem geometryRow087_meanGap_field :
    geometryRowsJson087.getObjVal? "mean_gap" = .ok (.str geometryRow087_meanGapText) := by rfl

theorem geometryRow087_meanGap_numerator_no_slash :
    geometryRow087_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow087_meanGap_numerator_parse :
    SourceJson.intChars geometryRow087_meanGapNumeratorChars = some (49290167 : Int) := by decide +kernel

theorem geometryRow087_meanGap_denominator_parse :
    SourceJson.intChars geometryRow087_meanGapDenominatorChars = some (34056000000 : Int) := by decide +kernel

theorem geometryRow087_meanGap_denominator_nonzero : (34056000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow087_meanGap_parse :
    parseRational geometryRow087_meanGapText = .ok geometryRowsTyped087.meanGap :=
  original_rational_fraction_of_chars geometryRow087_meanGapNumeratorChars geometryRow087_meanGapDenominatorChars
    (49290167 : Int) (34056000000 : Int)
    geometryRow087_meanGap_numerator_no_slash geometryRow087_meanGap_numerator_parse
    geometryRow087_meanGap_denominator_parse geometryRow087_meanGap_denominator_nonzero

theorem geometryRow087_meanGap_read :
    rationalField geometryRowsJson087 "mean_gap" = .ok geometryRowsTyped087.meanGap :=
  original_rationalField_of_string geometryRowsJson087 "mean_gap" geometryRow087_meanGapText
    geometryRowsTyped087.meanGap geometryRow087_meanGap_field geometryRow087_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_meanGap_complete"
  err.flush

noncomputable def geometryRow087_jensenBoundNumeratorChars : List Char := ['7', '0', '9', '2', '9', '7', '3', '0', '7', '6', '1', '6', '9', '6', '6', '0', '8', '3', '9', '9', '7', '8', '9', '0', '1', '2', '9', '2', '8', '8', '1', '1', '7', '2', '0', '0', '0', '6', '4', '9', '0', '9', '5', '8', '0', '4', '5', '1', '3', '2', '7', '0', '4', '1', '7', '1', '3', '8', '8', '7', '0', '3', '2', '8', '9', '1', '5', '9', '3', '4', '5', '6', '3', '7', '9', '1', '9', '7', '6', '2', '4', '5', '6', '9', '4', '3', '0', '1', '2', '2', '7', '9', '1', '2', '2', '2', '3', '2', '2', '3', '1', '3', '7', '2', '1', '3', '4', '9', '7', '5', '7', '5', '4', '1', '9', '5', '5', '7', '2', '7', '5', '7', '0', '5', '8', '3', '4', '1', '0', '9', '4', '8', '9', '2', '8', '5', '8', '1', '8', '4', '5', '1', '0', '2', '6', '9', '2', '7', '2', '5', '0', '6', '1', '7', '0', '4', '8', '4', '1', '9', '7', '0', '4', '4', '9', '8', '5', '5', '7', '2', '7', '1', '3', '4', '4', '2', '9', '1', '0', '9', '9', '7', '0', '5', '3', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow087_jensenBoundDenominatorChars : List Char := ['1', '0', '7', '1', '4', '2', '5', '6', '9', '9', '0', '1', '0', '0', '9', '9', '8', '4', '8', '5', '5', '2', '5', '8', '8', '6', '3', '9', '0', '0', '6', '9', '0', '8', '5', '2', '1', '4', '9', '9', '7', '4', '3', '7', '9', '8', '5', '5', '2', '4', '9', '3', '6', '6', '9', '8', '5', '2', '4', '2', '6', '0', '6', '2', '6', '1', '7', '7', '6', '6', '9', '7', '5', '4', '8', '4', '6', '2', '0', '0', '1', '2', '2', '1', '7', '7', '7', '2', '7', '4', '9', '8', '1', '6', '8', '2', '6', '4', '1', '9', '7', '8', '3', '1', '7', '8', '7', '6', '7', '3', '8', '3', '6', '8', '9', '5', '4', '1', '5', '2', '0', '3', '7', '7', '7', '6', '2', '5', '5', '1', '0', '0', '1', '2', '2', '5', '3', '3', '5', '3', '3', '1', '7', '0', '0', '5', '7', '7', '8', '7', '7', '7', '5', '7', '3', '2', '0', '6', '5', '9', '4', '7', '8', '9', '5', '3', '1', '0', '1', '1', '6', '2', '1', '3', '3', '0', '2', '7', '4', '2', '0', '4', '3', '7', '7', '8', '1', '7', '2', '1', '0', '4', '7', '9', '6', '3', '4', '0', '7', '9', '2', '6', '5', '8', '0', '9', '9', '2', '2', '0', '4', '1']
noncomputable def geometryRow087_jensenBoundText : String := String.ofList (geometryRow087_jensenBoundNumeratorChars ++ '/' :: geometryRow087_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_jensenBound_before_field"
  err.flush

theorem geometryRow087_jensenBound_field :
    geometryRowsJson087.getObjVal? "jensen_bound" = .ok (.str geometryRow087_jensenBoundText) := by rfl

theorem geometryRow087_jensenBound_numerator_no_slash :
    geometryRow087_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow087_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow087_jensenBoundNumeratorChars = some (7092973076169660839978901292881172000649095804513270417138870328915934563791976245694301227912223223137213497575419557275705834109489285818451026927250617048419704498557271344291099705344000000000000 : Int) := by decide +kernel

theorem geometryRow087_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow087_jensenBoundDenominatorChars = some (10714256990100998485525886390069085214997437985524936698524260626177669754846200122177727498168264197831787673836895415203777625510012253353317005778777573206594789531011621330274204377817210479634079265809922041 : Int) := by decide +kernel

theorem geometryRow087_jensenBound_denominator_nonzero : (10714256990100998485525886390069085214997437985524936698524260626177669754846200122177727498168264197831787673836895415203777625510012253353317005778777573206594789531011621330274204377817210479634079265809922041 : Int) ≠ 0 := by decide +kernel

theorem geometryRow087_jensenBound_parse :
    parseRational geometryRow087_jensenBoundText = .ok geometryRowsTyped087.jensenBound :=
  original_rational_fraction_of_chars geometryRow087_jensenBoundNumeratorChars geometryRow087_jensenBoundDenominatorChars
    (7092973076169660839978901292881172000649095804513270417138870328915934563791976245694301227912223223137213497575419557275705834109489285818451026927250617048419704498557271344291099705344000000000000 : Int) (10714256990100998485525886390069085214997437985524936698524260626177669754846200122177727498168264197831787673836895415203777625510012253353317005778777573206594789531011621330274204377817210479634079265809922041 : Int)
    geometryRow087_jensenBound_numerator_no_slash geometryRow087_jensenBound_numerator_parse
    geometryRow087_jensenBound_denominator_parse geometryRow087_jensenBound_denominator_nonzero

theorem geometryRow087_jensenBound_read :
    rationalField geometryRowsJson087 "jensen_bound" = .ok geometryRowsTyped087.jensenBound :=
  original_rationalField_of_string geometryRowsJson087 "jensen_bound" geometryRow087_jensenBoundText
    geometryRowsTyped087.jensenBound geometryRow087_jensenBound_field geometryRow087_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_factorMaxima_before"
  err.flush

theorem geometryRow087_factorMaxima_read :
    rationalArrayField geometryRowsJson087 "factor_maxima" = .ok geometryRowsTyped087.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_gapWeightedMeans_before"
  err.flush

theorem geometryRow087_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson087 "gap_weighted_means" = .ok geometryRowsTyped087.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow087_floorChars : List Char := ['5', '2', '4', '5', '0', '0', '4', '1', '4', '8', '2', '7', '9', '0', '1', '1', '5']
noncomputable def geometryRow087_floorText : String := String.ofList geometryRow087_floorChars

theorem geometryRow087_floor_text_read :
    geometryRowsJson087.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow087_floorText := by rfl

theorem geometryRow087_floor_chars_parse :
    SourceJson.intChars geometryRow087_floorChars = some (52450041482790115 : Int) := by decide +kernel

theorem geometryRow087_floor_parse :
    parseInteger geometryRow087_floorText = .ok geometryRowsTyped087.jensenFloorQ96 := by
  simp only [geometryRow087_floorText, parseInteger, String.toList_ofList, geometryRow087_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_087 :
    decodeGeometryRow geometryRowsJson087 = .ok geometryRowsTyped087 :=
  original_geometryRow_of_fields geometryRowsJson087 geometryRowsTyped087 geometryRow087_floorText
    geometryRow087_simplexId_read geometryRow087_vertexIds_read
    geometryRow087_physicalVolume_read geometryRow087_meanGap_read
    geometryRow087_factorMaxima_read geometryRow087_gapWeightedMeans_read
    geometryRow087_jensenBound_read geometryRow087_floor_text_read geometryRow087_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_087_original_decoder_complete"
  err.flush

theorem geometryRow087_shape :
    geometryRowsTyped087.simplexId = 87 ∧
    geometryRowsTyped087.vertexIds.size = 9 ∧ geometryRowsTyped087.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped087.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped087.factorMaxima.size = 10 ∧ geometryRowsTyped087.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock010 : List SourceJson := [geometryRowsJson080, geometryRowsJson081, geometryRowsJson082, geometryRowsJson083, geometryRowsJson084, geometryRowsJson085, geometryRowsJson086, geometryRowsJson087]
noncomputable def geometryRowsTypedBlock010 : List GeometryRow := [geometryRowsTyped080, geometryRowsTyped081, geometryRowsTyped082, geometryRowsTyped083, geometryRowsTyped084, geometryRowsTyped085, geometryRowsTyped086, geometryRowsTyped087]

theorem geometry_Rows_block_010_push_eq (acc : List SourceJson) :
    SimplicesBlock010.blockPush acc = [geometryRowsJson087, geometryRowsJson086, geometryRowsJson085, geometryRowsJson084, geometryRowsJson083, geometryRowsJson082, geometryRowsJson081, geometryRowsJson080] ++ acc := by rfl

theorem geometry_Rows_block_010_reverse (acc : List SourceJson) :
    (SimplicesBlock010.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock010 := by
  rw [geometry_Rows_block_010_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_010 :
    geometryRowsJsonBlock010.mapM decodeGeometryRow = .ok geometryRowsTypedBlock010 := by
  simp only [geometryRowsJsonBlock010, geometryRowsTypedBlock010, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_080, decode_geometry_Rows_081, decode_geometry_Rows_082, decode_geometry_Rows_083, decode_geometry_Rows_084, decode_geometry_Rows_085, decode_geometry_Rows_086, decode_geometry_Rows_087]
  rfl

theorem geometry_Rows_block_010_length : geometryRowsTypedBlock010.length = 8 := by rfl

#print axioms geometryRow080_simplexId_read
#print axioms geometryRow080_vertexIds_read
#print axioms geometryRow080_physicalVolume_field
#print axioms geometryRow080_physicalVolume_numerator_no_slash
#print axioms geometryRow080_physicalVolume_numerator_parse
#print axioms geometryRow080_physicalVolume_denominator_parse
#print axioms geometryRow080_physicalVolume_denominator_nonzero
#print axioms geometryRow080_physicalVolume_parse
#print axioms geometryRow080_physicalVolume_read
#print axioms geometryRow080_meanGap_field
#print axioms geometryRow080_meanGap_numerator_no_slash
#print axioms geometryRow080_meanGap_numerator_parse
#print axioms geometryRow080_meanGap_denominator_parse
#print axioms geometryRow080_meanGap_denominator_nonzero
#print axioms geometryRow080_meanGap_parse
#print axioms geometryRow080_meanGap_read
#print axioms geometryRow080_jensenBound_field
#print axioms geometryRow080_jensenBound_numerator_no_slash
#print axioms geometryRow080_jensenBound_numerator_parse
#print axioms geometryRow080_jensenBound_denominator_parse
#print axioms geometryRow080_jensenBound_denominator_nonzero
#print axioms geometryRow080_jensenBound_parse
#print axioms geometryRow080_jensenBound_read
#print axioms geometryRow080_factorMaxima_read
#print axioms geometryRow080_gapWeightedMeans_read
#print axioms geometryRow080_floor_text_read
#print axioms geometryRow080_floor_chars_parse
#print axioms geometryRow080_floor_parse
#print axioms decode_geometry_Rows_080
#print axioms geometryRow080_shape
#print axioms geometryRow081_simplexId_read
#print axioms geometryRow081_vertexIds_read
#print axioms geometryRow081_physicalVolume_field
#print axioms geometryRow081_physicalVolume_numerator_no_slash
#print axioms geometryRow081_physicalVolume_numerator_parse
#print axioms geometryRow081_physicalVolume_denominator_parse
#print axioms geometryRow081_physicalVolume_denominator_nonzero
#print axioms geometryRow081_physicalVolume_parse
#print axioms geometryRow081_physicalVolume_read
#print axioms geometryRow081_meanGap_field
#print axioms geometryRow081_meanGap_numerator_no_slash
#print axioms geometryRow081_meanGap_numerator_parse
#print axioms geometryRow081_meanGap_denominator_parse
#print axioms geometryRow081_meanGap_denominator_nonzero
#print axioms geometryRow081_meanGap_parse
#print axioms geometryRow081_meanGap_read
#print axioms geometryRow081_jensenBound_field
#print axioms geometryRow081_jensenBound_numerator_no_slash
#print axioms geometryRow081_jensenBound_numerator_parse
#print axioms geometryRow081_jensenBound_denominator_parse
#print axioms geometryRow081_jensenBound_denominator_nonzero
#print axioms geometryRow081_jensenBound_parse
#print axioms geometryRow081_jensenBound_read
#print axioms geometryRow081_factorMaxima_read
#print axioms geometryRow081_gapWeightedMeans_read
#print axioms geometryRow081_floor_text_read
#print axioms geometryRow081_floor_chars_parse
#print axioms geometryRow081_floor_parse
#print axioms decode_geometry_Rows_081
#print axioms geometryRow081_shape
#print axioms geometryRow082_simplexId_read
#print axioms geometryRow082_vertexIds_read
#print axioms geometryRow082_physicalVolume_field
#print axioms geometryRow082_physicalVolume_numerator_no_slash
#print axioms geometryRow082_physicalVolume_numerator_parse
#print axioms geometryRow082_physicalVolume_denominator_parse
#print axioms geometryRow082_physicalVolume_denominator_nonzero
#print axioms geometryRow082_physicalVolume_parse
#print axioms geometryRow082_physicalVolume_read
#print axioms geometryRow082_meanGap_field
#print axioms geometryRow082_meanGap_numerator_no_slash
#print axioms geometryRow082_meanGap_numerator_parse
#print axioms geometryRow082_meanGap_denominator_parse
#print axioms geometryRow082_meanGap_denominator_nonzero
#print axioms geometryRow082_meanGap_parse
#print axioms geometryRow082_meanGap_read
#print axioms geometryRow082_jensenBound_field
#print axioms geometryRow082_jensenBound_numerator_no_slash
#print axioms geometryRow082_jensenBound_numerator_parse
#print axioms geometryRow082_jensenBound_denominator_parse
#print axioms geometryRow082_jensenBound_denominator_nonzero
#print axioms geometryRow082_jensenBound_parse
#print axioms geometryRow082_jensenBound_read
#print axioms geometryRow082_factorMaxima_read
#print axioms geometryRow082_gapWeightedMeans_read
#print axioms geometryRow082_floor_text_read
#print axioms geometryRow082_floor_chars_parse
#print axioms geometryRow082_floor_parse
#print axioms decode_geometry_Rows_082
#print axioms geometryRow082_shape
#print axioms geometryRow083_simplexId_read
#print axioms geometryRow083_vertexIds_read
#print axioms geometryRow083_physicalVolume_field
#print axioms geometryRow083_physicalVolume_numerator_no_slash
#print axioms geometryRow083_physicalVolume_numerator_parse
#print axioms geometryRow083_physicalVolume_denominator_parse
#print axioms geometryRow083_physicalVolume_denominator_nonzero
#print axioms geometryRow083_physicalVolume_parse
#print axioms geometryRow083_physicalVolume_read
#print axioms geometryRow083_meanGap_field
#print axioms geometryRow083_meanGap_numerator_no_slash
#print axioms geometryRow083_meanGap_numerator_parse
#print axioms geometryRow083_meanGap_denominator_parse
#print axioms geometryRow083_meanGap_denominator_nonzero
#print axioms geometryRow083_meanGap_parse
#print axioms geometryRow083_meanGap_read
#print axioms geometryRow083_jensenBound_field
#print axioms geometryRow083_jensenBound_numerator_no_slash
#print axioms geometryRow083_jensenBound_numerator_parse
#print axioms geometryRow083_jensenBound_denominator_parse
#print axioms geometryRow083_jensenBound_denominator_nonzero
#print axioms geometryRow083_jensenBound_parse
#print axioms geometryRow083_jensenBound_read
#print axioms geometryRow083_factorMaxima_read
#print axioms geometryRow083_gapWeightedMeans_read
#print axioms geometryRow083_floor_text_read
#print axioms geometryRow083_floor_chars_parse
#print axioms geometryRow083_floor_parse
#print axioms decode_geometry_Rows_083
#print axioms geometryRow083_shape
#print axioms geometryRow084_simplexId_read
#print axioms geometryRow084_vertexIds_read
#print axioms geometryRow084_physicalVolume_field
#print axioms geometryRow084_physicalVolume_numerator_no_slash
#print axioms geometryRow084_physicalVolume_numerator_parse
#print axioms geometryRow084_physicalVolume_denominator_parse
#print axioms geometryRow084_physicalVolume_denominator_nonzero
#print axioms geometryRow084_physicalVolume_parse
#print axioms geometryRow084_physicalVolume_read
#print axioms geometryRow084_meanGap_field
#print axioms geometryRow084_meanGap_numerator_no_slash
#print axioms geometryRow084_meanGap_numerator_parse
#print axioms geometryRow084_meanGap_denominator_parse
#print axioms geometryRow084_meanGap_denominator_nonzero
#print axioms geometryRow084_meanGap_parse
#print axioms geometryRow084_meanGap_read
#print axioms geometryRow084_jensenBound_field
#print axioms geometryRow084_jensenBound_numerator_no_slash
#print axioms geometryRow084_jensenBound_numerator_parse
#print axioms geometryRow084_jensenBound_denominator_parse
#print axioms geometryRow084_jensenBound_denominator_nonzero
#print axioms geometryRow084_jensenBound_parse
#print axioms geometryRow084_jensenBound_read
#print axioms geometryRow084_factorMaxima_read
#print axioms geometryRow084_gapWeightedMeans_read
#print axioms geometryRow084_floor_text_read
#print axioms geometryRow084_floor_chars_parse
#print axioms geometryRow084_floor_parse
#print axioms decode_geometry_Rows_084
#print axioms geometryRow084_shape
#print axioms geometryRow085_simplexId_read
#print axioms geometryRow085_vertexIds_read
#print axioms geometryRow085_physicalVolume_field
#print axioms geometryRow085_physicalVolume_numerator_no_slash
#print axioms geometryRow085_physicalVolume_numerator_parse
#print axioms geometryRow085_physicalVolume_denominator_parse
#print axioms geometryRow085_physicalVolume_denominator_nonzero
#print axioms geometryRow085_physicalVolume_parse
#print axioms geometryRow085_physicalVolume_read
#print axioms geometryRow085_meanGap_field
#print axioms geometryRow085_meanGap_numerator_no_slash
#print axioms geometryRow085_meanGap_numerator_parse
#print axioms geometryRow085_meanGap_denominator_parse
#print axioms geometryRow085_meanGap_denominator_nonzero
#print axioms geometryRow085_meanGap_parse
#print axioms geometryRow085_meanGap_read
#print axioms geometryRow085_jensenBound_field
#print axioms geometryRow085_jensenBound_numerator_no_slash
#print axioms geometryRow085_jensenBound_numerator_parse
#print axioms geometryRow085_jensenBound_denominator_parse
#print axioms geometryRow085_jensenBound_denominator_nonzero
#print axioms geometryRow085_jensenBound_parse
#print axioms geometryRow085_jensenBound_read
#print axioms geometryRow085_factorMaxima_read
#print axioms geometryRow085_gapWeightedMeans_read
#print axioms geometryRow085_floor_text_read
#print axioms geometryRow085_floor_chars_parse
#print axioms geometryRow085_floor_parse
#print axioms decode_geometry_Rows_085
#print axioms geometryRow085_shape
#print axioms geometryRow086_simplexId_read
#print axioms geometryRow086_vertexIds_read
#print axioms geometryRow086_physicalVolume_field
#print axioms geometryRow086_physicalVolume_numerator_no_slash
#print axioms geometryRow086_physicalVolume_numerator_parse
#print axioms geometryRow086_physicalVolume_denominator_parse
#print axioms geometryRow086_physicalVolume_denominator_nonzero
#print axioms geometryRow086_physicalVolume_parse
#print axioms geometryRow086_physicalVolume_read
#print axioms geometryRow086_meanGap_field
#print axioms geometryRow086_meanGap_numerator_no_slash
#print axioms geometryRow086_meanGap_numerator_parse
#print axioms geometryRow086_meanGap_denominator_parse
#print axioms geometryRow086_meanGap_denominator_nonzero
#print axioms geometryRow086_meanGap_parse
#print axioms geometryRow086_meanGap_read
#print axioms geometryRow086_jensenBound_field
#print axioms geometryRow086_jensenBound_numerator_no_slash
#print axioms geometryRow086_jensenBound_numerator_parse
#print axioms geometryRow086_jensenBound_denominator_parse
#print axioms geometryRow086_jensenBound_denominator_nonzero
#print axioms geometryRow086_jensenBound_parse
#print axioms geometryRow086_jensenBound_read
#print axioms geometryRow086_factorMaxima_read
#print axioms geometryRow086_gapWeightedMeans_read
#print axioms geometryRow086_floor_text_read
#print axioms geometryRow086_floor_chars_parse
#print axioms geometryRow086_floor_parse
#print axioms decode_geometry_Rows_086
#print axioms geometryRow086_shape
#print axioms geometryRow087_simplexId_read
#print axioms geometryRow087_vertexIds_read
#print axioms geometryRow087_physicalVolume_field
#print axioms geometryRow087_physicalVolume_numerator_no_slash
#print axioms geometryRow087_physicalVolume_numerator_parse
#print axioms geometryRow087_physicalVolume_denominator_parse
#print axioms geometryRow087_physicalVolume_denominator_nonzero
#print axioms geometryRow087_physicalVolume_parse
#print axioms geometryRow087_physicalVolume_read
#print axioms geometryRow087_meanGap_field
#print axioms geometryRow087_meanGap_numerator_no_slash
#print axioms geometryRow087_meanGap_numerator_parse
#print axioms geometryRow087_meanGap_denominator_parse
#print axioms geometryRow087_meanGap_denominator_nonzero
#print axioms geometryRow087_meanGap_parse
#print axioms geometryRow087_meanGap_read
#print axioms geometryRow087_jensenBound_field
#print axioms geometryRow087_jensenBound_numerator_no_slash
#print axioms geometryRow087_jensenBound_numerator_parse
#print axioms geometryRow087_jensenBound_denominator_parse
#print axioms geometryRow087_jensenBound_denominator_nonzero
#print axioms geometryRow087_jensenBound_parse
#print axioms geometryRow087_jensenBound_read
#print axioms geometryRow087_factorMaxima_read
#print axioms geometryRow087_gapWeightedMeans_read
#print axioms geometryRow087_floor_text_read
#print axioms geometryRow087_floor_chars_parse
#print axioms geometryRow087_floor_parse
#print axioms decode_geometry_Rows_087
#print axioms geometryRow087_shape
#print axioms geometry_Rows_block_010_push_eq
#print axioms geometry_Rows_block_010_reverse
#print axioms decode_geometry_Rows_block_010
#print axioms geometry_Rows_block_010_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
