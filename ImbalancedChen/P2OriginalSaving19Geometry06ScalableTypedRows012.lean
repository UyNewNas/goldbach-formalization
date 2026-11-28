import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry06ScalableSimplicesBlock012

/-! Local typed certificates for original cell 06, rows 96 through 103.
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

noncomputable def geometryRowsJson096 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped096 : GeometryRow :=
  { simplexId := 96,
    vertexIds := #[32, 30, 29, 27, 15, 4, 2, 1, 0],
    physicalVolume := ((327025418590581543577176795699226716864863 : ℚ) / (349319822214537216000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1133902280579 : ℚ) / (383811120000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((7328233 : ℚ) / (196000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((734379 : ℚ) / (20000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1604141666273841171215697317 : ℚ) / (18496182931882160135400000000 : ℚ)), ((11067227067143490200851627 : ℚ) / (122898225461011030800000000 : ℚ)), ((578433205790264205731196059 : ℚ) / (4932315448501909369440000000 : ℚ)), ((6896256648519161054143461919 : ℚ) / (73984731727528640541600000000 : ℚ)), ((6801656377200231305156127199 : ℚ) / (73984731727528640541600000000 : ℚ)), ((159898840895228601947008351 : ℚ) / (2241961567500867895200000000 : ℚ)), ((116671875634275878892006257 : ℚ) / (3362942351251301842800000000 : ℚ)), ((115966746184718792378207147 : ℚ) / (3362942351251301842800000000 : ℚ)), ((114139050376597139198998907 : ℚ) / (3362942351251301842800000000 : ℚ)), ((3774414396093504852500569 : ℚ) / (122898225461011030800000000 : ℚ))],
    jensenBound := ((7114938739859814685744303853675155709420968404077038320354919875746056241893770614414703856386540379904524981116290509693044670053823957670657162961260481748069209983137282122771399923610420460134606827896356850448750889483264000000000000000000000000 : ℚ) / (448943472357987100374384529126977962191960487950500434793574122749765770781881713010206829430649479723600398949752108981034901136586520630078491474232624965802096951668690914002299353631492194605846671247738776774705237972495377437726268285330176040431200340485027 : ℚ)),
    jensenFloorQ96 := (1255622494742838 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_simplexId_before"
  err.flush

theorem geometryRow096_simplexId_read :
    geometryRowsJson096.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped096.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_vertexIds_before"
  err.flush

theorem geometryRow096_vertexIds_read :
    geometryRowsJson096.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped096.vertexIds := by decide +kernel

noncomputable def geometryRow096_physicalVolumeNumeratorChars : List Char := ['3', '2', '7', '0', '2', '5', '4', '1', '8', '5', '9', '0', '5', '8', '1', '5', '4', '3', '5', '7', '7', '1', '7', '6', '7', '9', '5', '6', '9', '9', '2', '2', '6', '7', '1', '6', '8', '6', '4', '8', '6', '3']
noncomputable def geometryRow096_physicalVolumeDenominatorChars : List Char := ['3', '4', '9', '3', '1', '9', '8', '2', '2', '2', '1', '4', '5', '3', '7', '2', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow096_physicalVolumeText : String := String.ofList (geometryRow096_physicalVolumeNumeratorChars ++ '/' :: geometryRow096_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_physicalVolume_before_field"
  err.flush

theorem geometryRow096_physicalVolume_field :
    geometryRowsJson096.getObjVal? "physical_volume" = .ok (.str geometryRow096_physicalVolumeText) := by rfl

theorem geometryRow096_physicalVolume_numerator_no_slash :
    geometryRow096_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow096_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow096_physicalVolumeNumeratorChars = some (327025418590581543577176795699226716864863 : Int) := by decide +kernel

theorem geometryRow096_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow096_physicalVolumeDenominatorChars = some (349319822214537216000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow096_physicalVolume_denominator_nonzero : (349319822214537216000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow096_physicalVolume_parse :
    parseRational geometryRow096_physicalVolumeText = .ok geometryRowsTyped096.physicalVolume :=
  original_rational_fraction_of_chars geometryRow096_physicalVolumeNumeratorChars geometryRow096_physicalVolumeDenominatorChars
    (327025418590581543577176795699226716864863 : Int) (349319822214537216000000000000000000000000000000000000000000000000 : Int)
    geometryRow096_physicalVolume_numerator_no_slash geometryRow096_physicalVolume_numerator_parse
    geometryRow096_physicalVolume_denominator_parse geometryRow096_physicalVolume_denominator_nonzero

theorem geometryRow096_physicalVolume_read :
    rationalField geometryRowsJson096 "physical_volume" = .ok geometryRowsTyped096.physicalVolume :=
  original_rationalField_of_string geometryRowsJson096 "physical_volume" geometryRow096_physicalVolumeText
    geometryRowsTyped096.physicalVolume geometryRow096_physicalVolume_field geometryRow096_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_physicalVolume_complete"
  err.flush

noncomputable def geometryRow096_meanGapNumeratorChars : List Char := ['1', '1', '3', '3', '9', '0', '2', '2', '8', '0', '5', '7', '9']
noncomputable def geometryRow096_meanGapDenominatorChars : List Char := ['3', '8', '3', '8', '1', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow096_meanGapText : String := String.ofList (geometryRow096_meanGapNumeratorChars ++ '/' :: geometryRow096_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_meanGap_before_field"
  err.flush

theorem geometryRow096_meanGap_field :
    geometryRowsJson096.getObjVal? "mean_gap" = .ok (.str geometryRow096_meanGapText) := by rfl

theorem geometryRow096_meanGap_numerator_no_slash :
    geometryRow096_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow096_meanGap_numerator_parse :
    SourceJson.intChars geometryRow096_meanGapNumeratorChars = some (1133902280579 : Int) := by decide +kernel

theorem geometryRow096_meanGap_denominator_parse :
    SourceJson.intChars geometryRow096_meanGapDenominatorChars = some (383811120000000 : Int) := by decide +kernel

theorem geometryRow096_meanGap_denominator_nonzero : (383811120000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow096_meanGap_parse :
    parseRational geometryRow096_meanGapText = .ok geometryRowsTyped096.meanGap :=
  original_rational_fraction_of_chars geometryRow096_meanGapNumeratorChars geometryRow096_meanGapDenominatorChars
    (1133902280579 : Int) (383811120000000 : Int)
    geometryRow096_meanGap_numerator_no_slash geometryRow096_meanGap_numerator_parse
    geometryRow096_meanGap_denominator_parse geometryRow096_meanGap_denominator_nonzero

theorem geometryRow096_meanGap_read :
    rationalField geometryRowsJson096 "mean_gap" = .ok geometryRowsTyped096.meanGap :=
  original_rationalField_of_string geometryRowsJson096 "mean_gap" geometryRow096_meanGapText
    geometryRowsTyped096.meanGap geometryRow096_meanGap_field geometryRow096_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_meanGap_complete"
  err.flush

noncomputable def geometryRow096_jensenBoundNumeratorChars : List Char := ['7', '1', '1', '4', '9', '3', '8', '7', '3', '9', '8', '5', '9', '8', '1', '4', '6', '8', '5', '7', '4', '4', '3', '0', '3', '8', '5', '3', '6', '7', '5', '1', '5', '5', '7', '0', '9', '4', '2', '0', '9', '6', '8', '4', '0', '4', '0', '7', '7', '0', '3', '8', '3', '2', '0', '3', '5', '4', '9', '1', '9', '8', '7', '5', '7', '4', '6', '0', '5', '6', '2', '4', '1', '8', '9', '3', '7', '7', '0', '6', '1', '4', '4', '1', '4', '7', '0', '3', '8', '5', '6', '3', '8', '6', '5', '4', '0', '3', '7', '9', '9', '0', '4', '5', '2', '4', '9', '8', '1', '1', '1', '6', '2', '9', '0', '5', '0', '9', '6', '9', '3', '0', '4', '4', '6', '7', '0', '0', '5', '3', '8', '2', '3', '9', '5', '7', '6', '7', '0', '6', '5', '7', '1', '6', '2', '9', '6', '1', '2', '6', '0', '4', '8', '1', '7', '4', '8', '0', '6', '9', '2', '0', '9', '9', '8', '3', '1', '3', '7', '2', '8', '2', '1', '2', '2', '7', '7', '1', '3', '9', '9', '9', '2', '3', '6', '1', '0', '4', '2', '0', '4', '6', '0', '1', '3', '4', '6', '0', '6', '8', '2', '7', '8', '9', '6', '3', '5', '6', '8', '5', '0', '4', '4', '8', '7', '5', '0', '8', '8', '9', '4', '8', '3', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow096_jensenBoundDenominatorChars : List Char := ['4', '4', '8', '9', '4', '3', '4', '7', '2', '3', '5', '7', '9', '8', '7', '1', '0', '0', '3', '7', '4', '3', '8', '4', '5', '2', '9', '1', '2', '6', '9', '7', '7', '9', '6', '2', '1', '9', '1', '9', '6', '0', '4', '8', '7', '9', '5', '0', '5', '0', '0', '4', '3', '4', '7', '9', '3', '5', '7', '4', '1', '2', '2', '7', '4', '9', '7', '6', '5', '7', '7', '0', '7', '8', '1', '8', '8', '1', '7', '1', '3', '0', '1', '0', '2', '0', '6', '8', '2', '9', '4', '3', '0', '6', '4', '9', '4', '7', '9', '7', '2', '3', '6', '0', '0', '3', '9', '8', '9', '4', '9', '7', '5', '2', '1', '0', '8', '9', '8', '1', '0', '3', '4', '9', '0', '1', '1', '3', '6', '5', '8', '6', '5', '2', '0', '6', '3', '0', '0', '7', '8', '4', '9', '1', '4', '7', '4', '2', '3', '2', '6', '2', '4', '9', '6', '5', '8', '0', '2', '0', '9', '6', '9', '5', '1', '6', '6', '8', '6', '9', '0', '9', '1', '4', '0', '0', '2', '2', '9', '9', '3', '5', '3', '6', '3', '1', '4', '9', '2', '1', '9', '4', '6', '0', '5', '8', '4', '6', '6', '7', '1', '2', '4', '7', '7', '3', '8', '7', '7', '6', '7', '7', '4', '7', '0', '5', '2', '3', '7', '9', '7', '2', '4', '9', '5', '3', '7', '7', '4', '3', '7', '7', '2', '6', '2', '6', '8', '2', '8', '5', '3', '3', '0', '1', '7', '6', '0', '4', '0', '4', '3', '1', '2', '0', '0', '3', '4', '0', '4', '8', '5', '0', '2', '7']
noncomputable def geometryRow096_jensenBoundText : String := String.ofList (geometryRow096_jensenBoundNumeratorChars ++ '/' :: geometryRow096_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_jensenBound_before_field"
  err.flush

theorem geometryRow096_jensenBound_field :
    geometryRowsJson096.getObjVal? "jensen_bound" = .ok (.str geometryRow096_jensenBoundText) := by rfl

theorem geometryRow096_jensenBound_numerator_no_slash :
    geometryRow096_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow096_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow096_jensenBoundNumeratorChars = some (7114938739859814685744303853675155709420968404077038320354919875746056241893770614414703856386540379904524981116290509693044670053823957670657162961260481748069209983137282122771399923610420460134606827896356850448750889483264000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow096_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow096_jensenBoundDenominatorChars = some (448943472357987100374384529126977962191960487950500434793574122749765770781881713010206829430649479723600398949752108981034901136586520630078491474232624965802096951668690914002299353631492194605846671247738776774705237972495377437726268285330176040431200340485027 : Int) := by decide +kernel

theorem geometryRow096_jensenBound_denominator_nonzero : (448943472357987100374384529126977962191960487950500434793574122749765770781881713010206829430649479723600398949752108981034901136586520630078491474232624965802096951668690914002299353631492194605846671247738776774705237972495377437726268285330176040431200340485027 : Int) ≠ 0 := by decide +kernel

theorem geometryRow096_jensenBound_parse :
    parseRational geometryRow096_jensenBoundText = .ok geometryRowsTyped096.jensenBound :=
  original_rational_fraction_of_chars geometryRow096_jensenBoundNumeratorChars geometryRow096_jensenBoundDenominatorChars
    (7114938739859814685744303853675155709420968404077038320354919875746056241893770614414703856386540379904524981116290509693044670053823957670657162961260481748069209983137282122771399923610420460134606827896356850448750889483264000000000000000000000000 : Int) (448943472357987100374384529126977962191960487950500434793574122749765770781881713010206829430649479723600398949752108981034901136586520630078491474232624965802096951668690914002299353631492194605846671247738776774705237972495377437726268285330176040431200340485027 : Int)
    geometryRow096_jensenBound_numerator_no_slash geometryRow096_jensenBound_numerator_parse
    geometryRow096_jensenBound_denominator_parse geometryRow096_jensenBound_denominator_nonzero

theorem geometryRow096_jensenBound_read :
    rationalField geometryRowsJson096 "jensen_bound" = .ok geometryRowsTyped096.jensenBound :=
  original_rationalField_of_string geometryRowsJson096 "jensen_bound" geometryRow096_jensenBoundText
    geometryRowsTyped096.jensenBound geometryRow096_jensenBound_field geometryRow096_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_factorMaxima_before"
  err.flush

theorem geometryRow096_factorMaxima_read :
    rationalArrayField geometryRowsJson096 "factor_maxima" = .ok geometryRowsTyped096.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_gapWeightedMeans_before"
  err.flush

theorem geometryRow096_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson096 "gap_weighted_means" = .ok geometryRowsTyped096.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow096_floorChars : List Char := ['1', '2', '5', '5', '6', '2', '2', '4', '9', '4', '7', '4', '2', '8', '3', '8']
noncomputable def geometryRow096_floorText : String := String.ofList geometryRow096_floorChars

theorem geometryRow096_floor_text_read :
    geometryRowsJson096.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow096_floorText := by rfl

theorem geometryRow096_floor_chars_parse :
    SourceJson.intChars geometryRow096_floorChars = some (1255622494742838 : Int) := by decide +kernel

theorem geometryRow096_floor_parse :
    parseInteger geometryRow096_floorText = .ok geometryRowsTyped096.jensenFloorQ96 := by
  simp only [geometryRow096_floorText, parseInteger, String.toList_ofList, geometryRow096_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_096 :
    decodeGeometryRow geometryRowsJson096 = .ok geometryRowsTyped096 :=
  original_geometryRow_of_fields geometryRowsJson096 geometryRowsTyped096 geometryRow096_floorText
    geometryRow096_simplexId_read geometryRow096_vertexIds_read
    geometryRow096_physicalVolume_read geometryRow096_meanGap_read
    geometryRow096_factorMaxima_read geometryRow096_gapWeightedMeans_read
    geometryRow096_jensenBound_read geometryRow096_floor_text_read geometryRow096_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_096_original_decoder_complete"
  err.flush

theorem geometryRow096_shape :
    geometryRowsTyped096.simplexId = 96 ∧
    geometryRowsTyped096.vertexIds.size = 9 ∧ geometryRowsTyped096.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped096.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped096.factorMaxima.size = 10 ∧ geometryRowsTyped096.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson097 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped097 : GeometryRow :=
  { simplexId := 97,
    vertexIds := #[32, 30, 29, 27, 15, 13, 4, 1, 0],
    physicalVolume := ((3237311407556896084985625091401377512506743 : ℚ) / (382068555547150080000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((11577977 : ℚ) / (144000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((26191251534102782603982097 : ℚ) / (300014239754030432400000000 : ℚ)), ((89650713650390571308401 : ℚ) / (996725049016712400000000 : ℚ)), ((204869493921397631552623 : ℚ) / (1739212984081335840000000 : ℚ)), ((55449067799129018533195657 : ℚ) / (600028479508060864800000000 : ℚ)), ((54681843864742204977383497 : ℚ) / (600028479508060864800000000 : ℚ)), ((1302673784668496471551513 : ℚ) / (18182681197213965600000000 : ℚ)), ((952350126542770671909671 : ℚ) / (27274021795820948400000000 : ℚ)), ((946240011452235052585841 : ℚ) / (27274021795820948400000000 : ℚ)), ((931417094464588027525121 : ℚ) / (27274021795820948400000000 : ℚ)), ((30575682324537039723547 : ℚ) / (996725049016712400000000 : ℚ))],
    jensenBound := ((1353954678886784531551236370934411362874206667857460118775524432223118745270203251449833064020763526861609729441337561794149770194456835396809322603101745100601258562948347259740615140699360100606751539200000000000000000000000 : ℚ) / (12835399497225081361233111756311364989830544933311495540292046387056772291402789857015869567419095693263237772425373025028883994756787982654914561886455571624672611172847388041092066939114813527059518123496812592825574570107831548493971741 : ℚ)),
    jensenFloorQ96 := (8357460269077095 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_simplexId_before"
  err.flush

theorem geometryRow097_simplexId_read :
    geometryRowsJson097.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped097.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_vertexIds_before"
  err.flush

theorem geometryRow097_vertexIds_read :
    geometryRowsJson097.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped097.vertexIds := by decide +kernel

noncomputable def geometryRow097_physicalVolumeNumeratorChars : List Char := ['3', '2', '3', '7', '3', '1', '1', '4', '0', '7', '5', '5', '6', '8', '9', '6', '0', '8', '4', '9', '8', '5', '6', '2', '5', '0', '9', '1', '4', '0', '1', '3', '7', '7', '5', '1', '2', '5', '0', '6', '7', '4', '3']
noncomputable def geometryRow097_physicalVolumeDenominatorChars : List Char := ['3', '8', '2', '0', '6', '8', '5', '5', '5', '5', '4', '7', '1', '5', '0', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow097_physicalVolumeText : String := String.ofList (geometryRow097_physicalVolumeNumeratorChars ++ '/' :: geometryRow097_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_physicalVolume_before_field"
  err.flush

theorem geometryRow097_physicalVolume_field :
    geometryRowsJson097.getObjVal? "physical_volume" = .ok (.str geometryRow097_physicalVolumeText) := by rfl

theorem geometryRow097_physicalVolume_numerator_no_slash :
    geometryRow097_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow097_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow097_physicalVolumeNumeratorChars = some (3237311407556896084985625091401377512506743 : Int) := by decide +kernel

theorem geometryRow097_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow097_physicalVolumeDenominatorChars = some (382068555547150080000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow097_physicalVolume_denominator_nonzero : (382068555547150080000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow097_physicalVolume_parse :
    parseRational geometryRow097_physicalVolumeText = .ok geometryRowsTyped097.physicalVolume :=
  original_rational_fraction_of_chars geometryRow097_physicalVolumeNumeratorChars geometryRow097_physicalVolumeDenominatorChars
    (3237311407556896084985625091401377512506743 : Int) (382068555547150080000000000000000000000000000000000000000000000000 : Int)
    geometryRow097_physicalVolume_numerator_no_slash geometryRow097_physicalVolume_numerator_parse
    geometryRow097_physicalVolume_denominator_parse geometryRow097_physicalVolume_denominator_nonzero

theorem geometryRow097_physicalVolume_read :
    rationalField geometryRowsJson097 "physical_volume" = .ok geometryRowsTyped097.physicalVolume :=
  original_rationalField_of_string geometryRowsJson097 "physical_volume" geometryRow097_physicalVolumeText
    geometryRowsTyped097.physicalVolume geometryRow097_physicalVolume_field geometryRow097_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_physicalVolume_complete"
  err.flush

noncomputable def geometryRow097_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow097_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow097_meanGapText : String := String.ofList (geometryRow097_meanGapNumeratorChars ++ '/' :: geometryRow097_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_meanGap_before_field"
  err.flush

theorem geometryRow097_meanGap_field :
    geometryRowsJson097.getObjVal? "mean_gap" = .ok (.str geometryRow097_meanGapText) := by rfl

theorem geometryRow097_meanGap_numerator_no_slash :
    geometryRow097_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow097_meanGap_numerator_parse :
    SourceJson.intChars geometryRow097_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow097_meanGap_denominator_parse :
    SourceJson.intChars geometryRow097_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow097_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow097_meanGap_parse :
    parseRational geometryRow097_meanGapText = .ok geometryRowsTyped097.meanGap :=
  original_rational_fraction_of_chars geometryRow097_meanGapNumeratorChars geometryRow097_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow097_meanGap_numerator_no_slash geometryRow097_meanGap_numerator_parse
    geometryRow097_meanGap_denominator_parse geometryRow097_meanGap_denominator_nonzero

theorem geometryRow097_meanGap_read :
    rationalField geometryRowsJson097 "mean_gap" = .ok geometryRowsTyped097.meanGap :=
  original_rationalField_of_string geometryRowsJson097 "mean_gap" geometryRow097_meanGapText
    geometryRowsTyped097.meanGap geometryRow097_meanGap_field geometryRow097_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_meanGap_complete"
  err.flush

noncomputable def geometryRow097_jensenBoundNumeratorChars : List Char := ['1', '3', '5', '3', '9', '5', '4', '6', '7', '8', '8', '8', '6', '7', '8', '4', '5', '3', '1', '5', '5', '1', '2', '3', '6', '3', '7', '0', '9', '3', '4', '4', '1', '1', '3', '6', '2', '8', '7', '4', '2', '0', '6', '6', '6', '7', '8', '5', '7', '4', '6', '0', '1', '1', '8', '7', '7', '5', '5', '2', '4', '4', '3', '2', '2', '2', '3', '1', '1', '8', '7', '4', '5', '2', '7', '0', '2', '0', '3', '2', '5', '1', '4', '4', '9', '8', '3', '3', '0', '6', '4', '0', '2', '0', '7', '6', '3', '5', '2', '6', '8', '6', '1', '6', '0', '9', '7', '2', '9', '4', '4', '1', '3', '3', '7', '5', '6', '1', '7', '9', '4', '1', '4', '9', '7', '7', '0', '1', '9', '4', '4', '5', '6', '8', '3', '5', '3', '9', '6', '8', '0', '9', '3', '2', '2', '6', '0', '3', '1', '0', '1', '7', '4', '5', '1', '0', '0', '6', '0', '1', '2', '5', '8', '5', '6', '2', '9', '4', '8', '3', '4', '7', '2', '5', '9', '7', '4', '0', '6', '1', '5', '1', '4', '0', '6', '9', '9', '3', '6', '0', '1', '0', '0', '6', '0', '6', '7', '5', '1', '5', '3', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow097_jensenBoundDenominatorChars : List Char := ['1', '2', '8', '3', '5', '3', '9', '9', '4', '9', '7', '2', '2', '5', '0', '8', '1', '3', '6', '1', '2', '3', '3', '1', '1', '1', '7', '5', '6', '3', '1', '1', '3', '6', '4', '9', '8', '9', '8', '3', '0', '5', '4', '4', '9', '3', '3', '3', '1', '1', '4', '9', '5', '5', '4', '0', '2', '9', '2', '0', '4', '6', '3', '8', '7', '0', '5', '6', '7', '7', '2', '2', '9', '1', '4', '0', '2', '7', '8', '9', '8', '5', '7', '0', '1', '5', '8', '6', '9', '5', '6', '7', '4', '1', '9', '0', '9', '5', '6', '9', '3', '2', '6', '3', '2', '3', '7', '7', '7', '2', '4', '2', '5', '3', '7', '3', '0', '2', '5', '0', '2', '8', '8', '8', '3', '9', '9', '4', '7', '5', '6', '7', '8', '7', '9', '8', '2', '6', '5', '4', '9', '1', '4', '5', '6', '1', '8', '8', '6', '4', '5', '5', '5', '7', '1', '6', '2', '4', '6', '7', '2', '6', '1', '1', '1', '7', '2', '8', '4', '7', '3', '8', '8', '0', '4', '1', '0', '9', '2', '0', '6', '6', '9', '3', '9', '1', '1', '4', '8', '1', '3', '5', '2', '7', '0', '5', '9', '5', '1', '8', '1', '2', '3', '4', '9', '6', '8', '1', '2', '5', '9', '2', '8', '2', '5', '5', '7', '4', '5', '7', '0', '1', '0', '7', '8', '3', '1', '5', '4', '8', '4', '9', '3', '9', '7', '1', '7', '4', '1']
noncomputable def geometryRow097_jensenBoundText : String := String.ofList (geometryRow097_jensenBoundNumeratorChars ++ '/' :: geometryRow097_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_jensenBound_before_field"
  err.flush

theorem geometryRow097_jensenBound_field :
    geometryRowsJson097.getObjVal? "jensen_bound" = .ok (.str geometryRow097_jensenBoundText) := by rfl

theorem geometryRow097_jensenBound_numerator_no_slash :
    geometryRow097_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow097_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow097_jensenBoundNumeratorChars = some (1353954678886784531551236370934411362874206667857460118775524432223118745270203251449833064020763526861609729441337561794149770194456835396809322603101745100601258562948347259740615140699360100606751539200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow097_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow097_jensenBoundDenominatorChars = some (12835399497225081361233111756311364989830544933311495540292046387056772291402789857015869567419095693263237772425373025028883994756787982654914561886455571624672611172847388041092066939114813527059518123496812592825574570107831548493971741 : Int) := by decide +kernel

theorem geometryRow097_jensenBound_denominator_nonzero : (12835399497225081361233111756311364989830544933311495540292046387056772291402789857015869567419095693263237772425373025028883994756787982654914561886455571624672611172847388041092066939114813527059518123496812592825574570107831548493971741 : Int) ≠ 0 := by decide +kernel

theorem geometryRow097_jensenBound_parse :
    parseRational geometryRow097_jensenBoundText = .ok geometryRowsTyped097.jensenBound :=
  original_rational_fraction_of_chars geometryRow097_jensenBoundNumeratorChars geometryRow097_jensenBoundDenominatorChars
    (1353954678886784531551236370934411362874206667857460118775524432223118745270203251449833064020763526861609729441337561794149770194456835396809322603101745100601258562948347259740615140699360100606751539200000000000000000000000 : Int) (12835399497225081361233111756311364989830544933311495540292046387056772291402789857015869567419095693263237772425373025028883994756787982654914561886455571624672611172847388041092066939114813527059518123496812592825574570107831548493971741 : Int)
    geometryRow097_jensenBound_numerator_no_slash geometryRow097_jensenBound_numerator_parse
    geometryRow097_jensenBound_denominator_parse geometryRow097_jensenBound_denominator_nonzero

theorem geometryRow097_jensenBound_read :
    rationalField geometryRowsJson097 "jensen_bound" = .ok geometryRowsTyped097.jensenBound :=
  original_rationalField_of_string geometryRowsJson097 "jensen_bound" geometryRow097_jensenBoundText
    geometryRowsTyped097.jensenBound geometryRow097_jensenBound_field geometryRow097_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_factorMaxima_before"
  err.flush

theorem geometryRow097_factorMaxima_read :
    rationalArrayField geometryRowsJson097 "factor_maxima" = .ok geometryRowsTyped097.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_gapWeightedMeans_before"
  err.flush

theorem geometryRow097_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson097 "gap_weighted_means" = .ok geometryRowsTyped097.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow097_floorChars : List Char := ['8', '3', '5', '7', '4', '6', '0', '2', '6', '9', '0', '7', '7', '0', '9', '5']
noncomputable def geometryRow097_floorText : String := String.ofList geometryRow097_floorChars

theorem geometryRow097_floor_text_read :
    geometryRowsJson097.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow097_floorText := by rfl

theorem geometryRow097_floor_chars_parse :
    SourceJson.intChars geometryRow097_floorChars = some (8357460269077095 : Int) := by decide +kernel

theorem geometryRow097_floor_parse :
    parseInteger geometryRow097_floorText = .ok geometryRowsTyped097.jensenFloorQ96 := by
  simp only [geometryRow097_floorText, parseInteger, String.toList_ofList, geometryRow097_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_097 :
    decodeGeometryRow geometryRowsJson097 = .ok geometryRowsTyped097 :=
  original_geometryRow_of_fields geometryRowsJson097 geometryRowsTyped097 geometryRow097_floorText
    geometryRow097_simplexId_read geometryRow097_vertexIds_read
    geometryRow097_physicalVolume_read geometryRow097_meanGap_read
    geometryRow097_factorMaxima_read geometryRow097_gapWeightedMeans_read
    geometryRow097_jensenBound_read geometryRow097_floor_text_read geometryRow097_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_097_original_decoder_complete"
  err.flush

theorem geometryRow097_shape :
    geometryRowsTyped097.simplexId = 97 ∧
    geometryRowsTyped097.vertexIds.size = 9 ∧ geometryRowsTyped097.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped097.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped097.factorMaxima.size = 10 ∧ geometryRowsTyped097.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson098 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped098 : GeometryRow :=
  { simplexId := 98,
    vertexIds := #[32, 30, 29, 27, 15, 13, 10, 1, 0],
    physicalVolume := ((5392240810112123485913240115167273628619169 : ℚ) / (53311891471695360000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((9564275023153949078033 : ℚ) / (108772200520275600000000 : ℚ)), ((1397324104080157076987 : ℚ) / (15538885788610800000000 : ℚ)), ((4969358829101385997 : ℚ) / (42037565418464000000 : ℚ)), ((19912936422787079116733 : ℚ) / (217544401040551200000000 : ℚ)), ((19634774173876838381693 : ℚ) / (217544401040551200000000 : ℚ)), ((159529988082426829839 : ℚ) / (2197418192328800000000 : ℚ)), ((359796645546772384309 : ℚ) / (9888381865479600000000 : ℚ)), ((337995207953510510449 : ℚ) / (9888381865479600000000 : ℚ)), ((332621058712469088769 : ℚ) / (9888381865479600000000 : ℚ)), ((476564673445948311689 : ℚ) / (15538885788610800000000 : ℚ))],
    jensenBound := ((11668518485359278172597442470876800174036376467006150117658235500860921274397235682666837761676712071165738858557915747180970055548786197102985574751719325094676429537280000000000000000000000 : ℚ) / (14038956524995674937956078171917949155642260254626312699824841077679853257025255850928898605768961463770771415685981459127490397394261766113509350697915566958980728566539794955253052750390600248279845649 : ℚ)),
    jensenFloorQ96 := (65850711711569122 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_simplexId_before"
  err.flush

theorem geometryRow098_simplexId_read :
    geometryRowsJson098.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped098.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_vertexIds_before"
  err.flush

theorem geometryRow098_vertexIds_read :
    geometryRowsJson098.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped098.vertexIds := by decide +kernel

noncomputable def geometryRow098_physicalVolumeNumeratorChars : List Char := ['5', '3', '9', '2', '2', '4', '0', '8', '1', '0', '1', '1', '2', '1', '2', '3', '4', '8', '5', '9', '1', '3', '2', '4', '0', '1', '1', '5', '1', '6', '7', '2', '7', '3', '6', '2', '8', '6', '1', '9', '1', '6', '9']
noncomputable def geometryRow098_physicalVolumeDenominatorChars : List Char := ['5', '3', '3', '1', '1', '8', '9', '1', '4', '7', '1', '6', '9', '5', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow098_physicalVolumeText : String := String.ofList (geometryRow098_physicalVolumeNumeratorChars ++ '/' :: geometryRow098_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_physicalVolume_before_field"
  err.flush

theorem geometryRow098_physicalVolume_field :
    geometryRowsJson098.getObjVal? "physical_volume" = .ok (.str geometryRow098_physicalVolumeText) := by rfl

theorem geometryRow098_physicalVolume_numerator_no_slash :
    geometryRow098_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow098_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow098_physicalVolumeNumeratorChars = some (5392240810112123485913240115167273628619169 : Int) := by decide +kernel

theorem geometryRow098_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow098_physicalVolumeDenominatorChars = some (53311891471695360000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow098_physicalVolume_denominator_nonzero : (53311891471695360000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow098_physicalVolume_parse :
    parseRational geometryRow098_physicalVolumeText = .ok geometryRowsTyped098.physicalVolume :=
  original_rational_fraction_of_chars geometryRow098_physicalVolumeNumeratorChars geometryRow098_physicalVolumeDenominatorChars
    (5392240810112123485913240115167273628619169 : Int) (53311891471695360000000000000000000000000000000000000000000000000 : Int)
    geometryRow098_physicalVolume_numerator_no_slash geometryRow098_physicalVolume_numerator_parse
    geometryRow098_physicalVolume_denominator_parse geometryRow098_physicalVolume_denominator_nonzero

theorem geometryRow098_physicalVolume_read :
    rationalField geometryRowsJson098 "physical_volume" = .ok geometryRowsTyped098.physicalVolume :=
  original_rationalField_of_string geometryRowsJson098 "physical_volume" geometryRow098_physicalVolumeText
    geometryRowsTyped098.physicalVolume geometryRow098_physicalVolume_field geometryRow098_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_physicalVolume_complete"
  err.flush

noncomputable def geometryRow098_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow098_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow098_meanGapText : String := String.ofList (geometryRow098_meanGapNumeratorChars ++ '/' :: geometryRow098_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_meanGap_before_field"
  err.flush

theorem geometryRow098_meanGap_field :
    geometryRowsJson098.getObjVal? "mean_gap" = .ok (.str geometryRow098_meanGapText) := by rfl

theorem geometryRow098_meanGap_numerator_no_slash :
    geometryRow098_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow098_meanGap_numerator_parse :
    SourceJson.intChars geometryRow098_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow098_meanGap_denominator_parse :
    SourceJson.intChars geometryRow098_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow098_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow098_meanGap_parse :
    parseRational geometryRow098_meanGapText = .ok geometryRowsTyped098.meanGap :=
  original_rational_fraction_of_chars geometryRow098_meanGapNumeratorChars geometryRow098_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow098_meanGap_numerator_no_slash geometryRow098_meanGap_numerator_parse
    geometryRow098_meanGap_denominator_parse geometryRow098_meanGap_denominator_nonzero

theorem geometryRow098_meanGap_read :
    rationalField geometryRowsJson098 "mean_gap" = .ok geometryRowsTyped098.meanGap :=
  original_rationalField_of_string geometryRowsJson098 "mean_gap" geometryRow098_meanGapText
    geometryRowsTyped098.meanGap geometryRow098_meanGap_field geometryRow098_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_meanGap_complete"
  err.flush

noncomputable def geometryRow098_jensenBoundNumeratorChars : List Char := ['1', '1', '6', '6', '8', '5', '1', '8', '4', '8', '5', '3', '5', '9', '2', '7', '8', '1', '7', '2', '5', '9', '7', '4', '4', '2', '4', '7', '0', '8', '7', '6', '8', '0', '0', '1', '7', '4', '0', '3', '6', '3', '7', '6', '4', '6', '7', '0', '0', '6', '1', '5', '0', '1', '1', '7', '6', '5', '8', '2', '3', '5', '5', '0', '0', '8', '6', '0', '9', '2', '1', '2', '7', '4', '3', '9', '7', '2', '3', '5', '6', '8', '2', '6', '6', '6', '8', '3', '7', '7', '6', '1', '6', '7', '6', '7', '1', '2', '0', '7', '1', '1', '6', '5', '7', '3', '8', '8', '5', '8', '5', '5', '7', '9', '1', '5', '7', '4', '7', '1', '8', '0', '9', '7', '0', '0', '5', '5', '5', '4', '8', '7', '8', '6', '1', '9', '7', '1', '0', '2', '9', '8', '5', '5', '7', '4', '7', '5', '1', '7', '1', '9', '3', '2', '5', '0', '9', '4', '6', '7', '6', '4', '2', '9', '5', '3', '7', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow098_jensenBoundDenominatorChars : List Char := ['1', '4', '0', '3', '8', '9', '5', '6', '5', '2', '4', '9', '9', '5', '6', '7', '4', '9', '3', '7', '9', '5', '6', '0', '7', '8', '1', '7', '1', '9', '1', '7', '9', '4', '9', '1', '5', '5', '6', '4', '2', '2', '6', '0', '2', '5', '4', '6', '2', '6', '3', '1', '2', '6', '9', '9', '8', '2', '4', '8', '4', '1', '0', '7', '7', '6', '7', '9', '8', '5', '3', '2', '5', '7', '0', '2', '5', '2', '5', '5', '8', '5', '0', '9', '2', '8', '8', '9', '8', '6', '0', '5', '7', '6', '8', '9', '6', '1', '4', '6', '3', '7', '7', '0', '7', '7', '1', '4', '1', '5', '6', '8', '5', '9', '8', '1', '4', '5', '9', '1', '2', '7', '4', '9', '0', '3', '9', '7', '3', '9', '4', '2', '6', '1', '7', '6', '6', '1', '1', '3', '5', '0', '9', '3', '5', '0', '6', '9', '7', '9', '1', '5', '5', '6', '6', '9', '5', '8', '9', '8', '0', '7', '2', '8', '5', '6', '6', '5', '3', '9', '7', '9', '4', '9', '5', '5', '2', '5', '3', '0', '5', '2', '7', '5', '0', '3', '9', '0', '6', '0', '0', '2', '4', '8', '2', '7', '9', '8', '4', '5', '6', '4', '9']
noncomputable def geometryRow098_jensenBoundText : String := String.ofList (geometryRow098_jensenBoundNumeratorChars ++ '/' :: geometryRow098_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_jensenBound_before_field"
  err.flush

theorem geometryRow098_jensenBound_field :
    geometryRowsJson098.getObjVal? "jensen_bound" = .ok (.str geometryRow098_jensenBoundText) := by rfl

theorem geometryRow098_jensenBound_numerator_no_slash :
    geometryRow098_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow098_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow098_jensenBoundNumeratorChars = some (11668518485359278172597442470876800174036376467006150117658235500860921274397235682666837761676712071165738858557915747180970055548786197102985574751719325094676429537280000000000000000000000 : Int) := by decide +kernel

theorem geometryRow098_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow098_jensenBoundDenominatorChars = some (14038956524995674937956078171917949155642260254626312699824841077679853257025255850928898605768961463770771415685981459127490397394261766113509350697915566958980728566539794955253052750390600248279845649 : Int) := by decide +kernel

theorem geometryRow098_jensenBound_denominator_nonzero : (14038956524995674937956078171917949155642260254626312699824841077679853257025255850928898605768961463770771415685981459127490397394261766113509350697915566958980728566539794955253052750390600248279845649 : Int) ≠ 0 := by decide +kernel

theorem geometryRow098_jensenBound_parse :
    parseRational geometryRow098_jensenBoundText = .ok geometryRowsTyped098.jensenBound :=
  original_rational_fraction_of_chars geometryRow098_jensenBoundNumeratorChars geometryRow098_jensenBoundDenominatorChars
    (11668518485359278172597442470876800174036376467006150117658235500860921274397235682666837761676712071165738858557915747180970055548786197102985574751719325094676429537280000000000000000000000 : Int) (14038956524995674937956078171917949155642260254626312699824841077679853257025255850928898605768961463770771415685981459127490397394261766113509350697915566958980728566539794955253052750390600248279845649 : Int)
    geometryRow098_jensenBound_numerator_no_slash geometryRow098_jensenBound_numerator_parse
    geometryRow098_jensenBound_denominator_parse geometryRow098_jensenBound_denominator_nonzero

theorem geometryRow098_jensenBound_read :
    rationalField geometryRowsJson098 "jensen_bound" = .ok geometryRowsTyped098.jensenBound :=
  original_rationalField_of_string geometryRowsJson098 "jensen_bound" geometryRow098_jensenBoundText
    geometryRowsTyped098.jensenBound geometryRow098_jensenBound_field geometryRow098_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_factorMaxima_before"
  err.flush

theorem geometryRow098_factorMaxima_read :
    rationalArrayField geometryRowsJson098 "factor_maxima" = .ok geometryRowsTyped098.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_gapWeightedMeans_before"
  err.flush

theorem geometryRow098_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson098 "gap_weighted_means" = .ok geometryRowsTyped098.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow098_floorChars : List Char := ['6', '5', '8', '5', '0', '7', '1', '1', '7', '1', '1', '5', '6', '9', '1', '2', '2']
noncomputable def geometryRow098_floorText : String := String.ofList geometryRow098_floorChars

theorem geometryRow098_floor_text_read :
    geometryRowsJson098.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow098_floorText := by rfl

theorem geometryRow098_floor_chars_parse :
    SourceJson.intChars geometryRow098_floorChars = some (65850711711569122 : Int) := by decide +kernel

theorem geometryRow098_floor_parse :
    parseInteger geometryRow098_floorText = .ok geometryRowsTyped098.jensenFloorQ96 := by
  simp only [geometryRow098_floorText, parseInteger, String.toList_ofList, geometryRow098_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_098 :
    decodeGeometryRow geometryRowsJson098 = .ok geometryRowsTyped098 :=
  original_geometryRow_of_fields geometryRowsJson098 geometryRowsTyped098 geometryRow098_floorText
    geometryRow098_simplexId_read geometryRow098_vertexIds_read
    geometryRow098_physicalVolume_read geometryRow098_meanGap_read
    geometryRow098_factorMaxima_read geometryRow098_gapWeightedMeans_read
    geometryRow098_jensenBound_read geometryRow098_floor_text_read geometryRow098_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_098_original_decoder_complete"
  err.flush

theorem geometryRow098_shape :
    geometryRowsTyped098.simplexId = 98 ∧
    geometryRowsTyped098.vertexIds.size = 9 ∧ geometryRowsTyped098.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped098.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped098.factorMaxima.size = 10 ∧ geometryRowsTyped098.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson099 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped099 : GeometryRow :=
  { simplexId := 99,
    vertexIds := #[32, 30, 29, 27, 15, 13, 10, 8, 0],
    physicalVolume := ((119324007082634545657739227755247742831893709 : ℚ) / (117503760794757120000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((9455220953551 : ℚ) / (108385200000000 : ℚ)), ((9598376224243 : ℚ) / (108385200000000 : ℚ)), ((669730262981 : ℚ) / (5654880000000 : ℚ)), ((59089825201993 : ℚ) / (650311200000000 : ℚ)), ((58258307474953 : ℚ) / (650311200000000 : ℚ)), ((622655254973 : ℚ) / (8445600000000 : ℚ)), ((1088478201989 : ℚ) / (29559600000000 : ℚ)), ((1030750379399 : ℚ) / (29559600000000 : ℚ)), ((1014685293719 : ℚ) / (29559600000000 : ℚ)), ((9824159455763 : ℚ) / (325155600000000 : ℚ))],
    jensenBound := ((204798203529528115642654193576840515882344051317255682431368331330003256877767352037847859200000000000000000000000 : ℚ) / (50244625263935511134843139754192108785999015444710100621598174892172607315661171505155837763419226169743080903242590325924703 : ℚ)),
    jensenFloorQ96 := (322935742213871187 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_simplexId_before"
  err.flush

theorem geometryRow099_simplexId_read :
    geometryRowsJson099.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped099.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_vertexIds_before"
  err.flush

theorem geometryRow099_vertexIds_read :
    geometryRowsJson099.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped099.vertexIds := by decide +kernel

noncomputable def geometryRow099_physicalVolumeNumeratorChars : List Char := ['1', '1', '9', '3', '2', '4', '0', '0', '7', '0', '8', '2', '6', '3', '4', '5', '4', '5', '6', '5', '7', '7', '3', '9', '2', '2', '7', '7', '5', '5', '2', '4', '7', '7', '4', '2', '8', '3', '1', '8', '9', '3', '7', '0', '9']
noncomputable def geometryRow099_physicalVolumeDenominatorChars : List Char := ['1', '1', '7', '5', '0', '3', '7', '6', '0', '7', '9', '4', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow099_physicalVolumeText : String := String.ofList (geometryRow099_physicalVolumeNumeratorChars ++ '/' :: geometryRow099_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_physicalVolume_before_field"
  err.flush

theorem geometryRow099_physicalVolume_field :
    geometryRowsJson099.getObjVal? "physical_volume" = .ok (.str geometryRow099_physicalVolumeText) := by rfl

theorem geometryRow099_physicalVolume_numerator_no_slash :
    geometryRow099_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow099_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow099_physicalVolumeNumeratorChars = some (119324007082634545657739227755247742831893709 : Int) := by decide +kernel

theorem geometryRow099_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow099_physicalVolumeDenominatorChars = some (117503760794757120000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow099_physicalVolume_denominator_nonzero : (117503760794757120000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow099_physicalVolume_parse :
    parseRational geometryRow099_physicalVolumeText = .ok geometryRowsTyped099.physicalVolume :=
  original_rational_fraction_of_chars geometryRow099_physicalVolumeNumeratorChars geometryRow099_physicalVolumeDenominatorChars
    (119324007082634545657739227755247742831893709 : Int) (117503760794757120000000000000000000000000000000000000000000000000 : Int)
    geometryRow099_physicalVolume_numerator_no_slash geometryRow099_physicalVolume_numerator_parse
    geometryRow099_physicalVolume_denominator_parse geometryRow099_physicalVolume_denominator_nonzero

theorem geometryRow099_physicalVolume_read :
    rationalField geometryRowsJson099 "physical_volume" = .ok geometryRowsTyped099.physicalVolume :=
  original_rationalField_of_string geometryRowsJson099 "physical_volume" geometryRow099_physicalVolumeText
    geometryRowsTyped099.physicalVolume geometryRow099_physicalVolume_field geometryRow099_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_physicalVolume_complete"
  err.flush

noncomputable def geometryRow099_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow099_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow099_meanGapText : String := String.ofList (geometryRow099_meanGapNumeratorChars ++ '/' :: geometryRow099_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_meanGap_before_field"
  err.flush

theorem geometryRow099_meanGap_field :
    geometryRowsJson099.getObjVal? "mean_gap" = .ok (.str geometryRow099_meanGapText) := by rfl

theorem geometryRow099_meanGap_numerator_no_slash :
    geometryRow099_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow099_meanGap_numerator_parse :
    SourceJson.intChars geometryRow099_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow099_meanGap_denominator_parse :
    SourceJson.intChars geometryRow099_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow099_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow099_meanGap_parse :
    parseRational geometryRow099_meanGapText = .ok geometryRowsTyped099.meanGap :=
  original_rational_fraction_of_chars geometryRow099_meanGapNumeratorChars geometryRow099_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow099_meanGap_numerator_no_slash geometryRow099_meanGap_numerator_parse
    geometryRow099_meanGap_denominator_parse geometryRow099_meanGap_denominator_nonzero

theorem geometryRow099_meanGap_read :
    rationalField geometryRowsJson099 "mean_gap" = .ok geometryRowsTyped099.meanGap :=
  original_rationalField_of_string geometryRowsJson099 "mean_gap" geometryRow099_meanGapText
    geometryRowsTyped099.meanGap geometryRow099_meanGap_field geometryRow099_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_meanGap_complete"
  err.flush

noncomputable def geometryRow099_jensenBoundNumeratorChars : List Char := ['2', '0', '4', '7', '9', '8', '2', '0', '3', '5', '2', '9', '5', '2', '8', '1', '1', '5', '6', '4', '2', '6', '5', '4', '1', '9', '3', '5', '7', '6', '8', '4', '0', '5', '1', '5', '8', '8', '2', '3', '4', '4', '0', '5', '1', '3', '1', '7', '2', '5', '5', '6', '8', '2', '4', '3', '1', '3', '6', '8', '3', '3', '1', '3', '3', '0', '0', '0', '3', '2', '5', '6', '8', '7', '7', '7', '6', '7', '3', '5', '2', '0', '3', '7', '8', '4', '7', '8', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow099_jensenBoundDenominatorChars : List Char := ['5', '0', '2', '4', '4', '6', '2', '5', '2', '6', '3', '9', '3', '5', '5', '1', '1', '1', '3', '4', '8', '4', '3', '1', '3', '9', '7', '5', '4', '1', '9', '2', '1', '0', '8', '7', '8', '5', '9', '9', '9', '0', '1', '5', '4', '4', '4', '7', '1', '0', '1', '0', '0', '6', '2', '1', '5', '9', '8', '1', '7', '4', '8', '9', '2', '1', '7', '2', '6', '0', '7', '3', '1', '5', '6', '6', '1', '1', '7', '1', '5', '0', '5', '1', '5', '5', '8', '3', '7', '7', '6', '3', '4', '1', '9', '2', '2', '6', '1', '6', '9', '7', '4', '3', '0', '8', '0', '9', '0', '3', '2', '4', '2', '5', '9', '0', '3', '2', '5', '9', '2', '4', '7', '0', '3']
noncomputable def geometryRow099_jensenBoundText : String := String.ofList (geometryRow099_jensenBoundNumeratorChars ++ '/' :: geometryRow099_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_jensenBound_before_field"
  err.flush

theorem geometryRow099_jensenBound_field :
    geometryRowsJson099.getObjVal? "jensen_bound" = .ok (.str geometryRow099_jensenBoundText) := by rfl

theorem geometryRow099_jensenBound_numerator_no_slash :
    geometryRow099_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow099_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow099_jensenBoundNumeratorChars = some (204798203529528115642654193576840515882344051317255682431368331330003256877767352037847859200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow099_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow099_jensenBoundDenominatorChars = some (50244625263935511134843139754192108785999015444710100621598174892172607315661171505155837763419226169743080903242590325924703 : Int) := by decide +kernel

theorem geometryRow099_jensenBound_denominator_nonzero : (50244625263935511134843139754192108785999015444710100621598174892172607315661171505155837763419226169743080903242590325924703 : Int) ≠ 0 := by decide +kernel

theorem geometryRow099_jensenBound_parse :
    parseRational geometryRow099_jensenBoundText = .ok geometryRowsTyped099.jensenBound :=
  original_rational_fraction_of_chars geometryRow099_jensenBoundNumeratorChars geometryRow099_jensenBoundDenominatorChars
    (204798203529528115642654193576840515882344051317255682431368331330003256877767352037847859200000000000000000000000 : Int) (50244625263935511134843139754192108785999015444710100621598174892172607315661171505155837763419226169743080903242590325924703 : Int)
    geometryRow099_jensenBound_numerator_no_slash geometryRow099_jensenBound_numerator_parse
    geometryRow099_jensenBound_denominator_parse geometryRow099_jensenBound_denominator_nonzero

theorem geometryRow099_jensenBound_read :
    rationalField geometryRowsJson099 "jensen_bound" = .ok geometryRowsTyped099.jensenBound :=
  original_rationalField_of_string geometryRowsJson099 "jensen_bound" geometryRow099_jensenBoundText
    geometryRowsTyped099.jensenBound geometryRow099_jensenBound_field geometryRow099_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_factorMaxima_before"
  err.flush

theorem geometryRow099_factorMaxima_read :
    rationalArrayField geometryRowsJson099 "factor_maxima" = .ok geometryRowsTyped099.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_gapWeightedMeans_before"
  err.flush

theorem geometryRow099_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson099 "gap_weighted_means" = .ok geometryRowsTyped099.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow099_floorChars : List Char := ['3', '2', '2', '9', '3', '5', '7', '4', '2', '2', '1', '3', '8', '7', '1', '1', '8', '7']
noncomputable def geometryRow099_floorText : String := String.ofList geometryRow099_floorChars

theorem geometryRow099_floor_text_read :
    geometryRowsJson099.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow099_floorText := by rfl

theorem geometryRow099_floor_chars_parse :
    SourceJson.intChars geometryRow099_floorChars = some (322935742213871187 : Int) := by decide +kernel

theorem geometryRow099_floor_parse :
    parseInteger geometryRow099_floorText = .ok geometryRowsTyped099.jensenFloorQ96 := by
  simp only [geometryRow099_floorText, parseInteger, String.toList_ofList, geometryRow099_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_099 :
    decodeGeometryRow geometryRowsJson099 = .ok geometryRowsTyped099 :=
  original_geometryRow_of_fields geometryRowsJson099 geometryRowsTyped099 geometryRow099_floorText
    geometryRow099_simplexId_read geometryRow099_vertexIds_read
    geometryRow099_physicalVolume_read geometryRow099_meanGap_read
    geometryRow099_factorMaxima_read geometryRow099_gapWeightedMeans_read
    geometryRow099_jensenBound_read geometryRow099_floor_text_read geometryRow099_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_099_original_decoder_complete"
  err.flush

theorem geometryRow099_shape :
    geometryRowsTyped099.simplexId = 99 ∧
    geometryRowsTyped099.vertexIds.size = 9 ∧ geometryRowsTyped099.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped099.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped099.factorMaxima.size = 10 ∧ geometryRowsTyped099.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson100 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped100 : GeometryRow :=
  { simplexId := 100,
    vertexIds := #[32, 30, 29, 27, 23, 13, 4, 1, 0],
    physicalVolume := ((61081903695850544427114371581995258275971 : ℚ) / (9949701967373700000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((9196136087 : ℚ) / (4171860000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((12773387347457914911080951 : ℚ) / (150007119877015216200000000 : ℚ)), ((43754797291662141498353 : ℚ) / (498362524508356200000000 : ℚ)), ((154968198305384200381423 : ℚ) / (1304409738061001880000000 : ℚ)), ((2353504785118675125453143 : ℚ) / (25001186646169202700000000 : ℚ)), ((2321537121185891227294303 : ℚ) / (25001186646169202700000000 : ℚ)), ((963246342646950778895461 : ℚ) / (13637010897910474200000000 : ℚ)), ((243858136968754510840159 : ℚ) / (6818505448955237100000000 : ℚ)), ((463355205132375817477463 : ℚ) / (13637010897910474200000000 : ℚ)), ((455943746638552304947103 : ℚ) / (13637010897910474200000000 : ℚ)), ((14930987984424138476491 : ℚ) / (498362524508356200000000 : ℚ))],
    jensenBound := ((1496474098769163610781414012097785555239236678201263600753591095466921270526108620625680084448100693425803966623710997969860026764144254986440642465073962649336252772815854768104490349702503270491386880000000000000000000000 : ℚ) / (18454400233579837810540770516835721608471184373935328144386966457710496224815287819954605577497855064356449239010119170366176240909918848957507111394543123753857169781881578925098872967870148902378522808546304956323347312483633788446779 : ℚ)),
    jensenFloorQ96 := (6424640822514088 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_simplexId_before"
  err.flush

theorem geometryRow100_simplexId_read :
    geometryRowsJson100.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped100.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_vertexIds_before"
  err.flush

theorem geometryRow100_vertexIds_read :
    geometryRowsJson100.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped100.vertexIds := by decide +kernel

noncomputable def geometryRow100_physicalVolumeNumeratorChars : List Char := ['6', '1', '0', '8', '1', '9', '0', '3', '6', '9', '5', '8', '5', '0', '5', '4', '4', '4', '2', '7', '1', '1', '4', '3', '7', '1', '5', '8', '1', '9', '9', '5', '2', '5', '8', '2', '7', '5', '9', '7', '1']
noncomputable def geometryRow100_physicalVolumeDenominatorChars : List Char := ['9', '9', '4', '9', '7', '0', '1', '9', '6', '7', '3', '7', '3', '7', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow100_physicalVolumeText : String := String.ofList (geometryRow100_physicalVolumeNumeratorChars ++ '/' :: geometryRow100_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_physicalVolume_before_field"
  err.flush

theorem geometryRow100_physicalVolume_field :
    geometryRowsJson100.getObjVal? "physical_volume" = .ok (.str geometryRow100_physicalVolumeText) := by rfl

theorem geometryRow100_physicalVolume_numerator_no_slash :
    geometryRow100_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow100_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow100_physicalVolumeNumeratorChars = some (61081903695850544427114371581995258275971 : Int) := by decide +kernel

theorem geometryRow100_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow100_physicalVolumeDenominatorChars = some (9949701967373700000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow100_physicalVolume_denominator_nonzero : (9949701967373700000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow100_physicalVolume_parse :
    parseRational geometryRow100_physicalVolumeText = .ok geometryRowsTyped100.physicalVolume :=
  original_rational_fraction_of_chars geometryRow100_physicalVolumeNumeratorChars geometryRow100_physicalVolumeDenominatorChars
    (61081903695850544427114371581995258275971 : Int) (9949701967373700000000000000000000000000000000000000000000000000 : Int)
    geometryRow100_physicalVolume_numerator_no_slash geometryRow100_physicalVolume_numerator_parse
    geometryRow100_physicalVolume_denominator_parse geometryRow100_physicalVolume_denominator_nonzero

theorem geometryRow100_physicalVolume_read :
    rationalField geometryRowsJson100 "physical_volume" = .ok geometryRowsTyped100.physicalVolume :=
  original_rationalField_of_string geometryRowsJson100 "physical_volume" geometryRow100_physicalVolumeText
    geometryRowsTyped100.physicalVolume geometryRow100_physicalVolume_field geometryRow100_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_physicalVolume_complete"
  err.flush

noncomputable def geometryRow100_meanGapNumeratorChars : List Char := ['9', '1', '9', '6', '1', '3', '6', '0', '8', '7']
noncomputable def geometryRow100_meanGapDenominatorChars : List Char := ['4', '1', '7', '1', '8', '6', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow100_meanGapText : String := String.ofList (geometryRow100_meanGapNumeratorChars ++ '/' :: geometryRow100_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_meanGap_before_field"
  err.flush

theorem geometryRow100_meanGap_field :
    geometryRowsJson100.getObjVal? "mean_gap" = .ok (.str geometryRow100_meanGapText) := by rfl

theorem geometryRow100_meanGap_numerator_no_slash :
    geometryRow100_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow100_meanGap_numerator_parse :
    SourceJson.intChars geometryRow100_meanGapNumeratorChars = some (9196136087 : Int) := by decide +kernel

theorem geometryRow100_meanGap_denominator_parse :
    SourceJson.intChars geometryRow100_meanGapDenominatorChars = some (4171860000000 : Int) := by decide +kernel

theorem geometryRow100_meanGap_denominator_nonzero : (4171860000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow100_meanGap_parse :
    parseRational geometryRow100_meanGapText = .ok geometryRowsTyped100.meanGap :=
  original_rational_fraction_of_chars geometryRow100_meanGapNumeratorChars geometryRow100_meanGapDenominatorChars
    (9196136087 : Int) (4171860000000 : Int)
    geometryRow100_meanGap_numerator_no_slash geometryRow100_meanGap_numerator_parse
    geometryRow100_meanGap_denominator_parse geometryRow100_meanGap_denominator_nonzero

theorem geometryRow100_meanGap_read :
    rationalField geometryRowsJson100 "mean_gap" = .ok geometryRowsTyped100.meanGap :=
  original_rationalField_of_string geometryRowsJson100 "mean_gap" geometryRow100_meanGapText
    geometryRowsTyped100.meanGap geometryRow100_meanGap_field geometryRow100_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_meanGap_complete"
  err.flush

noncomputable def geometryRow100_jensenBoundNumeratorChars : List Char := ['1', '4', '9', '6', '4', '7', '4', '0', '9', '8', '7', '6', '9', '1', '6', '3', '6', '1', '0', '7', '8', '1', '4', '1', '4', '0', '1', '2', '0', '9', '7', '7', '8', '5', '5', '5', '5', '2', '3', '9', '2', '3', '6', '6', '7', '8', '2', '0', '1', '2', '6', '3', '6', '0', '0', '7', '5', '3', '5', '9', '1', '0', '9', '5', '4', '6', '6', '9', '2', '1', '2', '7', '0', '5', '2', '6', '1', '0', '8', '6', '2', '0', '6', '2', '5', '6', '8', '0', '0', '8', '4', '4', '4', '8', '1', '0', '0', '6', '9', '3', '4', '2', '5', '8', '0', '3', '9', '6', '6', '6', '2', '3', '7', '1', '0', '9', '9', '7', '9', '6', '9', '8', '6', '0', '0', '2', '6', '7', '6', '4', '1', '4', '4', '2', '5', '4', '9', '8', '6', '4', '4', '0', '6', '4', '2', '4', '6', '5', '0', '7', '3', '9', '6', '2', '6', '4', '9', '3', '3', '6', '2', '5', '2', '7', '7', '2', '8', '1', '5', '8', '5', '4', '7', '6', '8', '1', '0', '4', '4', '9', '0', '3', '4', '9', '7', '0', '2', '5', '0', '3', '2', '7', '0', '4', '9', '1', '3', '8', '6', '8', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow100_jensenBoundDenominatorChars : List Char := ['1', '8', '4', '5', '4', '4', '0', '0', '2', '3', '3', '5', '7', '9', '8', '3', '7', '8', '1', '0', '5', '4', '0', '7', '7', '0', '5', '1', '6', '8', '3', '5', '7', '2', '1', '6', '0', '8', '4', '7', '1', '1', '8', '4', '3', '7', '3', '9', '3', '5', '3', '2', '8', '1', '4', '4', '3', '8', '6', '9', '6', '6', '4', '5', '7', '7', '1', '0', '4', '9', '6', '2', '2', '4', '8', '1', '5', '2', '8', '7', '8', '1', '9', '9', '5', '4', '6', '0', '5', '5', '7', '7', '4', '9', '7', '8', '5', '5', '0', '6', '4', '3', '5', '6', '4', '4', '9', '2', '3', '9', '0', '1', '0', '1', '1', '9', '1', '7', '0', '3', '6', '6', '1', '7', '6', '2', '4', '0', '9', '0', '9', '9', '1', '8', '8', '4', '8', '9', '5', '7', '5', '0', '7', '1', '1', '1', '3', '9', '4', '5', '4', '3', '1', '2', '3', '7', '5', '3', '8', '5', '7', '1', '6', '9', '7', '8', '1', '8', '8', '1', '5', '7', '8', '9', '2', '5', '0', '9', '8', '8', '7', '2', '9', '6', '7', '8', '7', '0', '1', '4', '8', '9', '0', '2', '3', '7', '8', '5', '2', '2', '8', '0', '8', '5', '4', '6', '3', '0', '4', '9', '5', '6', '3', '2', '3', '3', '4', '7', '3', '1', '2', '4', '8', '3', '6', '3', '3', '7', '8', '8', '4', '4', '6', '7', '7', '9']
noncomputable def geometryRow100_jensenBoundText : String := String.ofList (geometryRow100_jensenBoundNumeratorChars ++ '/' :: geometryRow100_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_jensenBound_before_field"
  err.flush

theorem geometryRow100_jensenBound_field :
    geometryRowsJson100.getObjVal? "jensen_bound" = .ok (.str geometryRow100_jensenBoundText) := by rfl

theorem geometryRow100_jensenBound_numerator_no_slash :
    geometryRow100_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow100_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow100_jensenBoundNumeratorChars = some (1496474098769163610781414012097785555239236678201263600753591095466921270526108620625680084448100693425803966623710997969860026764144254986440642465073962649336252772815854768104490349702503270491386880000000000000000000000 : Int) := by decide +kernel

theorem geometryRow100_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow100_jensenBoundDenominatorChars = some (18454400233579837810540770516835721608471184373935328144386966457710496224815287819954605577497855064356449239010119170366176240909918848957507111394543123753857169781881578925098872967870148902378522808546304956323347312483633788446779 : Int) := by decide +kernel

theorem geometryRow100_jensenBound_denominator_nonzero : (18454400233579837810540770516835721608471184373935328144386966457710496224815287819954605577497855064356449239010119170366176240909918848957507111394543123753857169781881578925098872967870148902378522808546304956323347312483633788446779 : Int) ≠ 0 := by decide +kernel

theorem geometryRow100_jensenBound_parse :
    parseRational geometryRow100_jensenBoundText = .ok geometryRowsTyped100.jensenBound :=
  original_rational_fraction_of_chars geometryRow100_jensenBoundNumeratorChars geometryRow100_jensenBoundDenominatorChars
    (1496474098769163610781414012097785555239236678201263600753591095466921270526108620625680084448100693425803966623710997969860026764144254986440642465073962649336252772815854768104490349702503270491386880000000000000000000000 : Int) (18454400233579837810540770516835721608471184373935328144386966457710496224815287819954605577497855064356449239010119170366176240909918848957507111394543123753857169781881578925098872967870148902378522808546304956323347312483633788446779 : Int)
    geometryRow100_jensenBound_numerator_no_slash geometryRow100_jensenBound_numerator_parse
    geometryRow100_jensenBound_denominator_parse geometryRow100_jensenBound_denominator_nonzero

theorem geometryRow100_jensenBound_read :
    rationalField geometryRowsJson100 "jensen_bound" = .ok geometryRowsTyped100.jensenBound :=
  original_rationalField_of_string geometryRowsJson100 "jensen_bound" geometryRow100_jensenBoundText
    geometryRowsTyped100.jensenBound geometryRow100_jensenBound_field geometryRow100_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_factorMaxima_before"
  err.flush

theorem geometryRow100_factorMaxima_read :
    rationalArrayField geometryRowsJson100 "factor_maxima" = .ok geometryRowsTyped100.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_gapWeightedMeans_before"
  err.flush

theorem geometryRow100_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson100 "gap_weighted_means" = .ok geometryRowsTyped100.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow100_floorChars : List Char := ['6', '4', '2', '4', '6', '4', '0', '8', '2', '2', '5', '1', '4', '0', '8', '8']
noncomputable def geometryRow100_floorText : String := String.ofList geometryRow100_floorChars

theorem geometryRow100_floor_text_read :
    geometryRowsJson100.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow100_floorText := by rfl

theorem geometryRow100_floor_chars_parse :
    SourceJson.intChars geometryRow100_floorChars = some (6424640822514088 : Int) := by decide +kernel

theorem geometryRow100_floor_parse :
    parseInteger geometryRow100_floorText = .ok geometryRowsTyped100.jensenFloorQ96 := by
  simp only [geometryRow100_floorText, parseInteger, String.toList_ofList, geometryRow100_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_100 :
    decodeGeometryRow geometryRowsJson100 = .ok geometryRowsTyped100 :=
  original_geometryRow_of_fields geometryRowsJson100 geometryRowsTyped100 geometryRow100_floorText
    geometryRow100_simplexId_read geometryRow100_vertexIds_read
    geometryRow100_physicalVolume_read geometryRow100_meanGap_read
    geometryRow100_factorMaxima_read geometryRow100_gapWeightedMeans_read
    geometryRow100_jensenBound_read geometryRow100_floor_text_read geometryRow100_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_100_original_decoder_complete"
  err.flush

theorem geometryRow100_shape :
    geometryRowsTyped100.simplexId = 100 ∧
    geometryRowsTyped100.vertexIds.size = 9 ∧ geometryRowsTyped100.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped100.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped100.factorMaxima.size = 10 ∧ geometryRowsTyped100.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson101 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped101 : GeometryRow :=
  { simplexId := 101,
    vertexIds := #[32, 30, 29, 27, 23, 13, 10, 1, 0],
    physicalVolume := ((101741319385974197953295217312333422527093 : ℚ) / (1388330507075400000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((143367229 : ℚ) / (97020000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((275621 : ℚ) / (3360000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((4665307783694408440039 : ℚ) / (54386100260137800000000 : ℚ)), ((681972090913997667211 : ℚ) / (7769442894305400000000 : ℚ)), ((28191219898393512619 : ℚ) / (236461305478860000000 : ℚ)), ((563561104422764620103 : ℚ) / (6042900028904200000000 : ℚ)), ((1667503125859107132389 : ℚ) / (18128700086712600000000 : ℚ)), ((88488513944533506131 : ℚ) / (1236047733184950000000 : ℚ)), ((184082667096014246197 : ℚ) / (4944190932739800000000 : ℚ)), ((165457309192435070407 : ℚ) / (4944190932739800000000 : ℚ)), ((162770234571914359567 : ℚ) / (4944190932739800000000 : ℚ)), ((232719016347613865417 : ℚ) / (7769442894305400000000 : ℚ))],
    jensenBound := ((500289286862678748796974174289687517040247856686369226092042472041047794662188951963825761764913540920047254876565049525143051641952362576384886582321719303641813731095040000000000000000000000 : ℚ) / (782291071826790568006129140950005737850927182404333965124522346878867498383654856134957604595321536178655491936421309857000781096868108778641457532275080290266127574171920937939355851270606914220653125017 : ℚ)),
    jensenFloorQ96 := (50667842637066258 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_simplexId_before"
  err.flush

theorem geometryRow101_simplexId_read :
    geometryRowsJson101.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped101.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_vertexIds_before"
  err.flush

theorem geometryRow101_vertexIds_read :
    geometryRowsJson101.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped101.vertexIds := by decide +kernel

noncomputable def geometryRow101_physicalVolumeNumeratorChars : List Char := ['1', '0', '1', '7', '4', '1', '3', '1', '9', '3', '8', '5', '9', '7', '4', '1', '9', '7', '9', '5', '3', '2', '9', '5', '2', '1', '7', '3', '1', '2', '3', '3', '3', '4', '2', '2', '5', '2', '7', '0', '9', '3']
noncomputable def geometryRow101_physicalVolumeDenominatorChars : List Char := ['1', '3', '8', '8', '3', '3', '0', '5', '0', '7', '0', '7', '5', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow101_physicalVolumeText : String := String.ofList (geometryRow101_physicalVolumeNumeratorChars ++ '/' :: geometryRow101_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_physicalVolume_before_field"
  err.flush

theorem geometryRow101_physicalVolume_field :
    geometryRowsJson101.getObjVal? "physical_volume" = .ok (.str geometryRow101_physicalVolumeText) := by rfl

theorem geometryRow101_physicalVolume_numerator_no_slash :
    geometryRow101_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow101_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow101_physicalVolumeNumeratorChars = some (101741319385974197953295217312333422527093 : Int) := by decide +kernel

theorem geometryRow101_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow101_physicalVolumeDenominatorChars = some (1388330507075400000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow101_physicalVolume_denominator_nonzero : (1388330507075400000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow101_physicalVolume_parse :
    parseRational geometryRow101_physicalVolumeText = .ok geometryRowsTyped101.physicalVolume :=
  original_rational_fraction_of_chars geometryRow101_physicalVolumeNumeratorChars geometryRow101_physicalVolumeDenominatorChars
    (101741319385974197953295217312333422527093 : Int) (1388330507075400000000000000000000000000000000000000000000000000 : Int)
    geometryRow101_physicalVolume_numerator_no_slash geometryRow101_physicalVolume_numerator_parse
    geometryRow101_physicalVolume_denominator_parse geometryRow101_physicalVolume_denominator_nonzero

theorem geometryRow101_physicalVolume_read :
    rationalField geometryRowsJson101 "physical_volume" = .ok geometryRowsTyped101.physicalVolume :=
  original_rationalField_of_string geometryRowsJson101 "physical_volume" geometryRow101_physicalVolumeText
    geometryRowsTyped101.physicalVolume geometryRow101_physicalVolume_field geometryRow101_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_physicalVolume_complete"
  err.flush

noncomputable def geometryRow101_meanGapNumeratorChars : List Char := ['1', '4', '3', '3', '6', '7', '2', '2', '9']
noncomputable def geometryRow101_meanGapDenominatorChars : List Char := ['9', '7', '0', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow101_meanGapText : String := String.ofList (geometryRow101_meanGapNumeratorChars ++ '/' :: geometryRow101_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_meanGap_before_field"
  err.flush

theorem geometryRow101_meanGap_field :
    geometryRowsJson101.getObjVal? "mean_gap" = .ok (.str geometryRow101_meanGapText) := by rfl

theorem geometryRow101_meanGap_numerator_no_slash :
    geometryRow101_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow101_meanGap_numerator_parse :
    SourceJson.intChars geometryRow101_meanGapNumeratorChars = some (143367229 : Int) := by decide +kernel

theorem geometryRow101_meanGap_denominator_parse :
    SourceJson.intChars geometryRow101_meanGapDenominatorChars = some (97020000000 : Int) := by decide +kernel

theorem geometryRow101_meanGap_denominator_nonzero : (97020000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow101_meanGap_parse :
    parseRational geometryRow101_meanGapText = .ok geometryRowsTyped101.meanGap :=
  original_rational_fraction_of_chars geometryRow101_meanGapNumeratorChars geometryRow101_meanGapDenominatorChars
    (143367229 : Int) (97020000000 : Int)
    geometryRow101_meanGap_numerator_no_slash geometryRow101_meanGap_numerator_parse
    geometryRow101_meanGap_denominator_parse geometryRow101_meanGap_denominator_nonzero

theorem geometryRow101_meanGap_read :
    rationalField geometryRowsJson101 "mean_gap" = .ok geometryRowsTyped101.meanGap :=
  original_rationalField_of_string geometryRowsJson101 "mean_gap" geometryRow101_meanGapText
    geometryRowsTyped101.meanGap geometryRow101_meanGap_field geometryRow101_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_meanGap_complete"
  err.flush

noncomputable def geometryRow101_jensenBoundNumeratorChars : List Char := ['5', '0', '0', '2', '8', '9', '2', '8', '6', '8', '6', '2', '6', '7', '8', '7', '4', '8', '7', '9', '6', '9', '7', '4', '1', '7', '4', '2', '8', '9', '6', '8', '7', '5', '1', '7', '0', '4', '0', '2', '4', '7', '8', '5', '6', '6', '8', '6', '3', '6', '9', '2', '2', '6', '0', '9', '2', '0', '4', '2', '4', '7', '2', '0', '4', '1', '0', '4', '7', '7', '9', '4', '6', '6', '2', '1', '8', '8', '9', '5', '1', '9', '6', '3', '8', '2', '5', '7', '6', '1', '7', '6', '4', '9', '1', '3', '5', '4', '0', '9', '2', '0', '0', '4', '7', '2', '5', '4', '8', '7', '6', '5', '6', '5', '0', '4', '9', '5', '2', '5', '1', '4', '3', '0', '5', '1', '6', '4', '1', '9', '5', '2', '3', '6', '2', '5', '7', '6', '3', '8', '4', '8', '8', '6', '5', '8', '2', '3', '2', '1', '7', '1', '9', '3', '0', '3', '6', '4', '1', '8', '1', '3', '7', '3', '1', '0', '9', '5', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow101_jensenBoundDenominatorChars : List Char := ['7', '8', '2', '2', '9', '1', '0', '7', '1', '8', '2', '6', '7', '9', '0', '5', '6', '8', '0', '0', '6', '1', '2', '9', '1', '4', '0', '9', '5', '0', '0', '0', '5', '7', '3', '7', '8', '5', '0', '9', '2', '7', '1', '8', '2', '4', '0', '4', '3', '3', '3', '9', '6', '5', '1', '2', '4', '5', '2', '2', '3', '4', '6', '8', '7', '8', '8', '6', '7', '4', '9', '8', '3', '8', '3', '6', '5', '4', '8', '5', '6', '1', '3', '4', '9', '5', '7', '6', '0', '4', '5', '9', '5', '3', '2', '1', '5', '3', '6', '1', '7', '8', '6', '5', '5', '4', '9', '1', '9', '3', '6', '4', '2', '1', '3', '0', '9', '8', '5', '7', '0', '0', '0', '7', '8', '1', '0', '9', '6', '8', '6', '8', '1', '0', '8', '7', '7', '8', '6', '4', '1', '4', '5', '7', '5', '3', '2', '2', '7', '5', '0', '8', '0', '2', '9', '0', '2', '6', '6', '1', '2', '7', '5', '7', '4', '1', '7', '1', '9', '2', '0', '9', '3', '7', '9', '3', '9', '3', '5', '5', '8', '5', '1', '2', '7', '0', '6', '0', '6', '9', '1', '4', '2', '2', '0', '6', '5', '3', '1', '2', '5', '0', '1', '7']
noncomputable def geometryRow101_jensenBoundText : String := String.ofList (geometryRow101_jensenBoundNumeratorChars ++ '/' :: geometryRow101_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_jensenBound_before_field"
  err.flush

theorem geometryRow101_jensenBound_field :
    geometryRowsJson101.getObjVal? "jensen_bound" = .ok (.str geometryRow101_jensenBoundText) := by rfl

theorem geometryRow101_jensenBound_numerator_no_slash :
    geometryRow101_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow101_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow101_jensenBoundNumeratorChars = some (500289286862678748796974174289687517040247856686369226092042472041047794662188951963825761764913540920047254876565049525143051641952362576384886582321719303641813731095040000000000000000000000 : Int) := by decide +kernel

theorem geometryRow101_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow101_jensenBoundDenominatorChars = some (782291071826790568006129140950005737850927182404333965124522346878867498383654856134957604595321536178655491936421309857000781096868108778641457532275080290266127574171920937939355851270606914220653125017 : Int) := by decide +kernel

theorem geometryRow101_jensenBound_denominator_nonzero : (782291071826790568006129140950005737850927182404333965124522346878867498383654856134957604595321536178655491936421309857000781096868108778641457532275080290266127574171920937939355851270606914220653125017 : Int) ≠ 0 := by decide +kernel

theorem geometryRow101_jensenBound_parse :
    parseRational geometryRow101_jensenBoundText = .ok geometryRowsTyped101.jensenBound :=
  original_rational_fraction_of_chars geometryRow101_jensenBoundNumeratorChars geometryRow101_jensenBoundDenominatorChars
    (500289286862678748796974174289687517040247856686369226092042472041047794662188951963825761764913540920047254876565049525143051641952362576384886582321719303641813731095040000000000000000000000 : Int) (782291071826790568006129140950005737850927182404333965124522346878867498383654856134957604595321536178655491936421309857000781096868108778641457532275080290266127574171920937939355851270606914220653125017 : Int)
    geometryRow101_jensenBound_numerator_no_slash geometryRow101_jensenBound_numerator_parse
    geometryRow101_jensenBound_denominator_parse geometryRow101_jensenBound_denominator_nonzero

theorem geometryRow101_jensenBound_read :
    rationalField geometryRowsJson101 "jensen_bound" = .ok geometryRowsTyped101.jensenBound :=
  original_rationalField_of_string geometryRowsJson101 "jensen_bound" geometryRow101_jensenBoundText
    geometryRowsTyped101.jensenBound geometryRow101_jensenBound_field geometryRow101_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_factorMaxima_before"
  err.flush

theorem geometryRow101_factorMaxima_read :
    rationalArrayField geometryRowsJson101 "factor_maxima" = .ok geometryRowsTyped101.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_gapWeightedMeans_before"
  err.flush

theorem geometryRow101_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson101 "gap_weighted_means" = .ok geometryRowsTyped101.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow101_floorChars : List Char := ['5', '0', '6', '6', '7', '8', '4', '2', '6', '3', '7', '0', '6', '6', '2', '5', '8']
noncomputable def geometryRow101_floorText : String := String.ofList geometryRow101_floorChars

theorem geometryRow101_floor_text_read :
    geometryRowsJson101.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow101_floorText := by rfl

theorem geometryRow101_floor_chars_parse :
    SourceJson.intChars geometryRow101_floorChars = some (50667842637066258 : Int) := by decide +kernel

theorem geometryRow101_floor_parse :
    parseInteger geometryRow101_floorText = .ok geometryRowsTyped101.jensenFloorQ96 := by
  simp only [geometryRow101_floorText, parseInteger, String.toList_ofList, geometryRow101_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_101 :
    decodeGeometryRow geometryRowsJson101 = .ok geometryRowsTyped101 :=
  original_geometryRow_of_fields geometryRowsJson101 geometryRowsTyped101 geometryRow101_floorText
    geometryRow101_simplexId_read geometryRow101_vertexIds_read
    geometryRow101_physicalVolume_read geometryRow101_meanGap_read
    geometryRow101_factorMaxima_read geometryRow101_gapWeightedMeans_read
    geometryRow101_jensenBound_read geometryRow101_floor_text_read geometryRow101_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_101_original_decoder_complete"
  err.flush

theorem geometryRow101_shape :
    geometryRowsTyped101.simplexId = 101 ∧
    geometryRowsTyped101.vertexIds.size = 9 ∧ geometryRowsTyped101.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped101.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped101.factorMaxima.size = 10 ∧ geometryRowsTyped101.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson102 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped102 : GeometryRow :=
  { simplexId := 102,
    vertexIds := #[32, 30, 29, 27, 23, 13, 10, 8, 0],
    physicalVolume := ((2251416867778227414331322304677981134739473 : ℚ) / (3059993770696800000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((1452881 : ℚ) / (1980000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((4546799 : ℚ) / (54000000 : ℚ)), ((1421831 : ℚ) / (28000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((4546799 : ℚ) / (108000000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((4611196417283 : ℚ) / (54192600000000 : ℚ)), ((4682774052629 : ℚ) / (54192600000000 : ℚ)), ((168858931667 : ℚ) / (1413720000000 : ℚ)), ((470403201281 : ℚ) / (5080556250000 : ℚ)), ((927813938077 : ℚ) / (10161112500000 : ℚ)), ((153533526977 : ℚ) / (2111400000000 : ℚ)), ((556747471537 : ℚ) / (14779800000000 : ℚ)), ((252396046691 : ℚ) / (7389900000000 : ℚ)), ((248379775271 : ℚ) / (7389900000000 : ℚ)), ((4795665668389 : ℚ) / (162577800000000 : ℚ))],
    jensenBound := ((6749629881273365205494326102413115123850202405021244551334008016274875322797752686767500000000000000000000 : ℚ) / (2152422775644740966263421146115933656658414529666648658190394598762137539606883820368668979559355795480811663482212427 : ℚ)),
    jensenFloorQ96 := (248445974088188872 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_simplexId_before"
  err.flush

theorem geometryRow102_simplexId_read :
    geometryRowsJson102.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped102.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_vertexIds_before"
  err.flush

theorem geometryRow102_vertexIds_read :
    geometryRowsJson102.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped102.vertexIds := by decide +kernel

noncomputable def geometryRow102_physicalVolumeNumeratorChars : List Char := ['2', '2', '5', '1', '4', '1', '6', '8', '6', '7', '7', '7', '8', '2', '2', '7', '4', '1', '4', '3', '3', '1', '3', '2', '2', '3', '0', '4', '6', '7', '7', '9', '8', '1', '1', '3', '4', '7', '3', '9', '4', '7', '3']
noncomputable def geometryRow102_physicalVolumeDenominatorChars : List Char := ['3', '0', '5', '9', '9', '9', '3', '7', '7', '0', '6', '9', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow102_physicalVolumeText : String := String.ofList (geometryRow102_physicalVolumeNumeratorChars ++ '/' :: geometryRow102_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_physicalVolume_before_field"
  err.flush

theorem geometryRow102_physicalVolume_field :
    geometryRowsJson102.getObjVal? "physical_volume" = .ok (.str geometryRow102_physicalVolumeText) := by rfl

theorem geometryRow102_physicalVolume_numerator_no_slash :
    geometryRow102_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow102_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow102_physicalVolumeNumeratorChars = some (2251416867778227414331322304677981134739473 : Int) := by decide +kernel

theorem geometryRow102_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow102_physicalVolumeDenominatorChars = some (3059993770696800000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow102_physicalVolume_denominator_nonzero : (3059993770696800000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow102_physicalVolume_parse :
    parseRational geometryRow102_physicalVolumeText = .ok geometryRowsTyped102.physicalVolume :=
  original_rational_fraction_of_chars geometryRow102_physicalVolumeNumeratorChars geometryRow102_physicalVolumeDenominatorChars
    (2251416867778227414331322304677981134739473 : Int) (3059993770696800000000000000000000000000000000000000000000000000 : Int)
    geometryRow102_physicalVolume_numerator_no_slash geometryRow102_physicalVolume_numerator_parse
    geometryRow102_physicalVolume_denominator_parse geometryRow102_physicalVolume_denominator_nonzero

theorem geometryRow102_physicalVolume_read :
    rationalField geometryRowsJson102 "physical_volume" = .ok geometryRowsTyped102.physicalVolume :=
  original_rationalField_of_string geometryRowsJson102 "physical_volume" geometryRow102_physicalVolumeText
    geometryRowsTyped102.physicalVolume geometryRow102_physicalVolume_field geometryRow102_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_physicalVolume_complete"
  err.flush

noncomputable def geometryRow102_meanGapNumeratorChars : List Char := ['1', '4', '5', '2', '8', '8', '1']
noncomputable def geometryRow102_meanGapDenominatorChars : List Char := ['1', '9', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow102_meanGapText : String := String.ofList (geometryRow102_meanGapNumeratorChars ++ '/' :: geometryRow102_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_meanGap_before_field"
  err.flush

theorem geometryRow102_meanGap_field :
    geometryRowsJson102.getObjVal? "mean_gap" = .ok (.str geometryRow102_meanGapText) := by rfl

theorem geometryRow102_meanGap_numerator_no_slash :
    geometryRow102_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow102_meanGap_numerator_parse :
    SourceJson.intChars geometryRow102_meanGapNumeratorChars = some (1452881 : Int) := by decide +kernel

theorem geometryRow102_meanGap_denominator_parse :
    SourceJson.intChars geometryRow102_meanGapDenominatorChars = some (1980000000 : Int) := by decide +kernel

theorem geometryRow102_meanGap_denominator_nonzero : (1980000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow102_meanGap_parse :
    parseRational geometryRow102_meanGapText = .ok geometryRowsTyped102.meanGap :=
  original_rational_fraction_of_chars geometryRow102_meanGapNumeratorChars geometryRow102_meanGapDenominatorChars
    (1452881 : Int) (1980000000 : Int)
    geometryRow102_meanGap_numerator_no_slash geometryRow102_meanGap_numerator_parse
    geometryRow102_meanGap_denominator_parse geometryRow102_meanGap_denominator_nonzero

theorem geometryRow102_meanGap_read :
    rationalField geometryRowsJson102 "mean_gap" = .ok geometryRowsTyped102.meanGap :=
  original_rationalField_of_string geometryRowsJson102 "mean_gap" geometryRow102_meanGapText
    geometryRowsTyped102.meanGap geometryRow102_meanGap_field geometryRow102_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_meanGap_complete"
  err.flush

noncomputable def geometryRow102_jensenBoundNumeratorChars : List Char := ['6', '7', '4', '9', '6', '2', '9', '8', '8', '1', '2', '7', '3', '3', '6', '5', '2', '0', '5', '4', '9', '4', '3', '2', '6', '1', '0', '2', '4', '1', '3', '1', '1', '5', '1', '2', '3', '8', '5', '0', '2', '0', '2', '4', '0', '5', '0', '2', '1', '2', '4', '4', '5', '5', '1', '3', '3', '4', '0', '0', '8', '0', '1', '6', '2', '7', '4', '8', '7', '5', '3', '2', '2', '7', '9', '7', '7', '5', '2', '6', '8', '6', '7', '6', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow102_jensenBoundDenominatorChars : List Char := ['2', '1', '5', '2', '4', '2', '2', '7', '7', '5', '6', '4', '4', '7', '4', '0', '9', '6', '6', '2', '6', '3', '4', '2', '1', '1', '4', '6', '1', '1', '5', '9', '3', '3', '6', '5', '6', '6', '5', '8', '4', '1', '4', '5', '2', '9', '6', '6', '6', '6', '4', '8', '6', '5', '8', '1', '9', '0', '3', '9', '4', '5', '9', '8', '7', '6', '2', '1', '3', '7', '5', '3', '9', '6', '0', '6', '8', '8', '3', '8', '2', '0', '3', '6', '8', '6', '6', '8', '9', '7', '9', '5', '5', '9', '3', '5', '5', '7', '9', '5', '4', '8', '0', '8', '1', '1', '6', '6', '3', '4', '8', '2', '2', '1', '2', '4', '2', '7']
noncomputable def geometryRow102_jensenBoundText : String := String.ofList (geometryRow102_jensenBoundNumeratorChars ++ '/' :: geometryRow102_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_jensenBound_before_field"
  err.flush

theorem geometryRow102_jensenBound_field :
    geometryRowsJson102.getObjVal? "jensen_bound" = .ok (.str geometryRow102_jensenBoundText) := by rfl

theorem geometryRow102_jensenBound_numerator_no_slash :
    geometryRow102_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow102_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow102_jensenBoundNumeratorChars = some (6749629881273365205494326102413115123850202405021244551334008016274875322797752686767500000000000000000000 : Int) := by decide +kernel

theorem geometryRow102_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow102_jensenBoundDenominatorChars = some (2152422775644740966263421146115933656658414529666648658190394598762137539606883820368668979559355795480811663482212427 : Int) := by decide +kernel

theorem geometryRow102_jensenBound_denominator_nonzero : (2152422775644740966263421146115933656658414529666648658190394598762137539606883820368668979559355795480811663482212427 : Int) ≠ 0 := by decide +kernel

theorem geometryRow102_jensenBound_parse :
    parseRational geometryRow102_jensenBoundText = .ok geometryRowsTyped102.jensenBound :=
  original_rational_fraction_of_chars geometryRow102_jensenBoundNumeratorChars geometryRow102_jensenBoundDenominatorChars
    (6749629881273365205494326102413115123850202405021244551334008016274875322797752686767500000000000000000000 : Int) (2152422775644740966263421146115933656658414529666648658190394598762137539606883820368668979559355795480811663482212427 : Int)
    geometryRow102_jensenBound_numerator_no_slash geometryRow102_jensenBound_numerator_parse
    geometryRow102_jensenBound_denominator_parse geometryRow102_jensenBound_denominator_nonzero

theorem geometryRow102_jensenBound_read :
    rationalField geometryRowsJson102 "jensen_bound" = .ok geometryRowsTyped102.jensenBound :=
  original_rationalField_of_string geometryRowsJson102 "jensen_bound" geometryRow102_jensenBoundText
    geometryRowsTyped102.jensenBound geometryRow102_jensenBound_field geometryRow102_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_factorMaxima_before"
  err.flush

theorem geometryRow102_factorMaxima_read :
    rationalArrayField geometryRowsJson102 "factor_maxima" = .ok geometryRowsTyped102.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_gapWeightedMeans_before"
  err.flush

theorem geometryRow102_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson102 "gap_weighted_means" = .ok geometryRowsTyped102.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow102_floorChars : List Char := ['2', '4', '8', '4', '4', '5', '9', '7', '4', '0', '8', '8', '1', '8', '8', '8', '7', '2']
noncomputable def geometryRow102_floorText : String := String.ofList geometryRow102_floorChars

theorem geometryRow102_floor_text_read :
    geometryRowsJson102.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow102_floorText := by rfl

theorem geometryRow102_floor_chars_parse :
    SourceJson.intChars geometryRow102_floorChars = some (248445974088188872 : Int) := by decide +kernel

theorem geometryRow102_floor_parse :
    parseInteger geometryRow102_floorText = .ok geometryRowsTyped102.jensenFloorQ96 := by
  simp only [geometryRow102_floorText, parseInteger, String.toList_ofList, geometryRow102_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_102 :
    decodeGeometryRow geometryRowsJson102 = .ok geometryRowsTyped102 :=
  original_geometryRow_of_fields geometryRowsJson102 geometryRowsTyped102 geometryRow102_floorText
    geometryRow102_simplexId_read geometryRow102_vertexIds_read
    geometryRow102_physicalVolume_read geometryRow102_meanGap_read
    geometryRow102_factorMaxima_read geometryRow102_gapWeightedMeans_read
    geometryRow102_jensenBound_read geometryRow102_floor_text_read geometryRow102_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_102_original_decoder_complete"
  err.flush

theorem geometryRow102_shape :
    geometryRowsTyped102.simplexId = 102 ∧
    geometryRowsTyped102.vertexIds.size = 9 ∧ geometryRowsTyped102.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped102.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped102.factorMaxima.size = 10 ∧ geometryRowsTyped102.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson103 : SourceJson :=
  (SimplicesBlock012.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped103 : GeometryRow :=
  { simplexId := 103,
    vertexIds := #[32, 30, 29, 27, 23, 22, 13, 4, 0],
    physicalVolume := ((2378325972128685232160377794709853146453 : ℚ) / (50763785547825000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((96707389 : ℚ) / (66220000000 : ℚ)),
    factorMaxima := #[((164061 : ℚ) / (1750000 : ℚ)), ((164061 : ℚ) / (1750000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((20671607 : ℚ) / (204000000 : ℚ)), ((390621 : ℚ) / (4000000 : ℚ)), ((765619 : ℚ) / (10062500 : ℚ)), ((515621 : ℚ) / (12000000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((765619 : ℚ) / (20125000 : ℚ)), ((1171871 : ℚ) / (36000000 : ℚ))],
    gapWeightedMeans := #[((9560170245024256251223 : ℚ) / (112677734256110100000000 : ℚ)), ((113747906963523757429 : ℚ) / (1310206212280350000000 : ℚ)), ((701494801913553809 : ℚ) / (5832180862117500000 : ℚ)), ((42295195848388578477 : ℚ) / (447133866095675000000 : ℚ)), ((125170409937805674301 : ℚ) / (1341401598287025000000 : ℚ)), ((4984435991697975417 : ℚ) / (71134933242493750000 : ℚ)), ((40256535414270537571 : ℚ) / (1138158931879900000000 : ℚ)), ((115434941513197333423 : ℚ) / (3414476795639700000000 : ℚ)), ((37859745901829797721 : ℚ) / (1138158931879900000000 : ℚ)), ((38825756771186323363 : ℚ) / (1310206212280350000000 : ℚ))],
    jensenBound := ((694843410517899322191696518147347400119640234583171354994282465295244390690331999725812741083189708161978495865526452334962162424605782865068407981759963703172050781250000000000000 : ℚ) / (1639815314219387587081676283674753418417299282499931219341835407511082447850513028399051645865919201276442699830116429264881084339787462702144389992150269519194232263322468408429277552416342881 : ℚ)),
    jensenFloorQ96 := (33571565147069136 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_simplexId_before"
  err.flush

theorem geometryRow103_simplexId_read :
    geometryRowsJson103.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped103.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_vertexIds_before"
  err.flush

theorem geometryRow103_vertexIds_read :
    geometryRowsJson103.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped103.vertexIds := by decide +kernel

noncomputable def geometryRow103_physicalVolumeNumeratorChars : List Char := ['2', '3', '7', '8', '3', '2', '5', '9', '7', '2', '1', '2', '8', '6', '8', '5', '2', '3', '2', '1', '6', '0', '3', '7', '7', '7', '9', '4', '7', '0', '9', '8', '5', '3', '1', '4', '6', '4', '5', '3']
noncomputable def geometryRow103_physicalVolumeDenominatorChars : List Char := ['5', '0', '7', '6', '3', '7', '8', '5', '5', '4', '7', '8', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow103_physicalVolumeText : String := String.ofList (geometryRow103_physicalVolumeNumeratorChars ++ '/' :: geometryRow103_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_physicalVolume_before_field"
  err.flush

theorem geometryRow103_physicalVolume_field :
    geometryRowsJson103.getObjVal? "physical_volume" = .ok (.str geometryRow103_physicalVolumeText) := by rfl

theorem geometryRow103_physicalVolume_numerator_no_slash :
    geometryRow103_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow103_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow103_physicalVolumeNumeratorChars = some (2378325972128685232160377794709853146453 : Int) := by decide +kernel

theorem geometryRow103_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow103_physicalVolumeDenominatorChars = some (50763785547825000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow103_physicalVolume_denominator_nonzero : (50763785547825000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow103_physicalVolume_parse :
    parseRational geometryRow103_physicalVolumeText = .ok geometryRowsTyped103.physicalVolume :=
  original_rational_fraction_of_chars geometryRow103_physicalVolumeNumeratorChars geometryRow103_physicalVolumeDenominatorChars
    (2378325972128685232160377794709853146453 : Int) (50763785547825000000000000000000000000000000000000000000000000 : Int)
    geometryRow103_physicalVolume_numerator_no_slash geometryRow103_physicalVolume_numerator_parse
    geometryRow103_physicalVolume_denominator_parse geometryRow103_physicalVolume_denominator_nonzero

theorem geometryRow103_physicalVolume_read :
    rationalField geometryRowsJson103 "physical_volume" = .ok geometryRowsTyped103.physicalVolume :=
  original_rationalField_of_string geometryRowsJson103 "physical_volume" geometryRow103_physicalVolumeText
    geometryRowsTyped103.physicalVolume geometryRow103_physicalVolume_field geometryRow103_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_physicalVolume_complete"
  err.flush

noncomputable def geometryRow103_meanGapNumeratorChars : List Char := ['9', '6', '7', '0', '7', '3', '8', '9']
noncomputable def geometryRow103_meanGapDenominatorChars : List Char := ['6', '6', '2', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow103_meanGapText : String := String.ofList (geometryRow103_meanGapNumeratorChars ++ '/' :: geometryRow103_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_meanGap_before_field"
  err.flush

theorem geometryRow103_meanGap_field :
    geometryRowsJson103.getObjVal? "mean_gap" = .ok (.str geometryRow103_meanGapText) := by rfl

theorem geometryRow103_meanGap_numerator_no_slash :
    geometryRow103_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow103_meanGap_numerator_parse :
    SourceJson.intChars geometryRow103_meanGapNumeratorChars = some (96707389 : Int) := by decide +kernel

theorem geometryRow103_meanGap_denominator_parse :
    SourceJson.intChars geometryRow103_meanGapDenominatorChars = some (66220000000 : Int) := by decide +kernel

theorem geometryRow103_meanGap_denominator_nonzero : (66220000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow103_meanGap_parse :
    parseRational geometryRow103_meanGapText = .ok geometryRowsTyped103.meanGap :=
  original_rational_fraction_of_chars geometryRow103_meanGapNumeratorChars geometryRow103_meanGapDenominatorChars
    (96707389 : Int) (66220000000 : Int)
    geometryRow103_meanGap_numerator_no_slash geometryRow103_meanGap_numerator_parse
    geometryRow103_meanGap_denominator_parse geometryRow103_meanGap_denominator_nonzero

theorem geometryRow103_meanGap_read :
    rationalField geometryRowsJson103 "mean_gap" = .ok geometryRowsTyped103.meanGap :=
  original_rationalField_of_string geometryRowsJson103 "mean_gap" geometryRow103_meanGapText
    geometryRowsTyped103.meanGap geometryRow103_meanGap_field geometryRow103_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_meanGap_complete"
  err.flush

noncomputable def geometryRow103_jensenBoundNumeratorChars : List Char := ['6', '9', '4', '8', '4', '3', '4', '1', '0', '5', '1', '7', '8', '9', '9', '3', '2', '2', '1', '9', '1', '6', '9', '6', '5', '1', '8', '1', '4', '7', '3', '4', '7', '4', '0', '0', '1', '1', '9', '6', '4', '0', '2', '3', '4', '5', '8', '3', '1', '7', '1', '3', '5', '4', '9', '9', '4', '2', '8', '2', '4', '6', '5', '2', '9', '5', '2', '4', '4', '3', '9', '0', '6', '9', '0', '3', '3', '1', '9', '9', '9', '7', '2', '5', '8', '1', '2', '7', '4', '1', '0', '8', '3', '1', '8', '9', '7', '0', '8', '1', '6', '1', '9', '7', '8', '4', '9', '5', '8', '6', '5', '5', '2', '6', '4', '5', '2', '3', '3', '4', '9', '6', '2', '1', '6', '2', '4', '2', '4', '6', '0', '5', '7', '8', '2', '8', '6', '5', '0', '6', '8', '4', '0', '7', '9', '8', '1', '7', '5', '9', '9', '6', '3', '7', '0', '3', '1', '7', '2', '0', '5', '0', '7', '8', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow103_jensenBoundDenominatorChars : List Char := ['1', '6', '3', '9', '8', '1', '5', '3', '1', '4', '2', '1', '9', '3', '8', '7', '5', '8', '7', '0', '8', '1', '6', '7', '6', '2', '8', '3', '6', '7', '4', '7', '5', '3', '4', '1', '8', '4', '1', '7', '2', '9', '9', '2', '8', '2', '4', '9', '9', '9', '3', '1', '2', '1', '9', '3', '4', '1', '8', '3', '5', '4', '0', '7', '5', '1', '1', '0', '8', '2', '4', '4', '7', '8', '5', '0', '5', '1', '3', '0', '2', '8', '3', '9', '9', '0', '5', '1', '6', '4', '5', '8', '6', '5', '9', '1', '9', '2', '0', '1', '2', '7', '6', '4', '4', '2', '6', '9', '9', '8', '3', '0', '1', '1', '6', '4', '2', '9', '2', '6', '4', '8', '8', '1', '0', '8', '4', '3', '3', '9', '7', '8', '7', '4', '6', '2', '7', '0', '2', '1', '4', '4', '3', '8', '9', '9', '9', '2', '1', '5', '0', '2', '6', '9', '5', '1', '9', '1', '9', '4', '2', '3', '2', '2', '6', '3', '3', '2', '2', '4', '6', '8', '4', '0', '8', '4', '2', '9', '2', '7', '7', '5', '5', '2', '4', '1', '6', '3', '4', '2', '8', '8', '1']
noncomputable def geometryRow103_jensenBoundText : String := String.ofList (geometryRow103_jensenBoundNumeratorChars ++ '/' :: geometryRow103_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_jensenBound_before_field"
  err.flush

theorem geometryRow103_jensenBound_field :
    geometryRowsJson103.getObjVal? "jensen_bound" = .ok (.str geometryRow103_jensenBoundText) := by rfl

theorem geometryRow103_jensenBound_numerator_no_slash :
    geometryRow103_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow103_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow103_jensenBoundNumeratorChars = some (694843410517899322191696518147347400119640234583171354994282465295244390690331999725812741083189708161978495865526452334962162424605782865068407981759963703172050781250000000000000 : Int) := by decide +kernel

theorem geometryRow103_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow103_jensenBoundDenominatorChars = some (1639815314219387587081676283674753418417299282499931219341835407511082447850513028399051645865919201276442699830116429264881084339787462702144389992150269519194232263322468408429277552416342881 : Int) := by decide +kernel

theorem geometryRow103_jensenBound_denominator_nonzero : (1639815314219387587081676283674753418417299282499931219341835407511082447850513028399051645865919201276442699830116429264881084339787462702144389992150269519194232263322468408429277552416342881 : Int) ≠ 0 := by decide +kernel

theorem geometryRow103_jensenBound_parse :
    parseRational geometryRow103_jensenBoundText = .ok geometryRowsTyped103.jensenBound :=
  original_rational_fraction_of_chars geometryRow103_jensenBoundNumeratorChars geometryRow103_jensenBoundDenominatorChars
    (694843410517899322191696518147347400119640234583171354994282465295244390690331999725812741083189708161978495865526452334962162424605782865068407981759963703172050781250000000000000 : Int) (1639815314219387587081676283674753418417299282499931219341835407511082447850513028399051645865919201276442699830116429264881084339787462702144389992150269519194232263322468408429277552416342881 : Int)
    geometryRow103_jensenBound_numerator_no_slash geometryRow103_jensenBound_numerator_parse
    geometryRow103_jensenBound_denominator_parse geometryRow103_jensenBound_denominator_nonzero

theorem geometryRow103_jensenBound_read :
    rationalField geometryRowsJson103 "jensen_bound" = .ok geometryRowsTyped103.jensenBound :=
  original_rationalField_of_string geometryRowsJson103 "jensen_bound" geometryRow103_jensenBoundText
    geometryRowsTyped103.jensenBound geometryRow103_jensenBound_field geometryRow103_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_factorMaxima_before"
  err.flush

theorem geometryRow103_factorMaxima_read :
    rationalArrayField geometryRowsJson103 "factor_maxima" = .ok geometryRowsTyped103.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_gapWeightedMeans_before"
  err.flush

theorem geometryRow103_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson103 "gap_weighted_means" = .ok geometryRowsTyped103.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow103_floorChars : List Char := ['3', '3', '5', '7', '1', '5', '6', '5', '1', '4', '7', '0', '6', '9', '1', '3', '6']
noncomputable def geometryRow103_floorText : String := String.ofList geometryRow103_floorChars

theorem geometryRow103_floor_text_read :
    geometryRowsJson103.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow103_floorText := by rfl

theorem geometryRow103_floor_chars_parse :
    SourceJson.intChars geometryRow103_floorChars = some (33571565147069136 : Int) := by decide +kernel

theorem geometryRow103_floor_parse :
    parseInteger geometryRow103_floorText = .ok geometryRowsTyped103.jensenFloorQ96 := by
  simp only [geometryRow103_floorText, parseInteger, String.toList_ofList, geometryRow103_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_103 :
    decodeGeometryRow geometryRowsJson103 = .ok geometryRowsTyped103 :=
  original_geometryRow_of_fields geometryRowsJson103 geometryRowsTyped103 geometryRow103_floorText
    geometryRow103_simplexId_read geometryRow103_vertexIds_read
    geometryRow103_physicalVolume_read geometryRow103_meanGap_read
    geometryRow103_factorMaxima_read geometryRow103_gapWeightedMeans_read
    geometryRow103_jensenBound_read geometryRow103_floor_text_read geometryRow103_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_06_Row_103_original_decoder_complete"
  err.flush

theorem geometryRow103_shape :
    geometryRowsTyped103.simplexId = 103 ∧
    geometryRowsTyped103.vertexIds.size = 9 ∧ geometryRowsTyped103.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped103.vertexIds[i.val]! < 33) ∧
    geometryRowsTyped103.factorMaxima.size = 10 ∧ geometryRowsTyped103.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock012 : List SourceJson := [geometryRowsJson096, geometryRowsJson097, geometryRowsJson098, geometryRowsJson099, geometryRowsJson100, geometryRowsJson101, geometryRowsJson102, geometryRowsJson103]
noncomputable def geometryRowsTypedBlock012 : List GeometryRow := [geometryRowsTyped096, geometryRowsTyped097, geometryRowsTyped098, geometryRowsTyped099, geometryRowsTyped100, geometryRowsTyped101, geometryRowsTyped102, geometryRowsTyped103]

theorem geometry_Rows_block_012_push_eq (acc : List SourceJson) :
    SimplicesBlock012.blockPush acc = [geometryRowsJson103, geometryRowsJson102, geometryRowsJson101, geometryRowsJson100, geometryRowsJson099, geometryRowsJson098, geometryRowsJson097, geometryRowsJson096] ++ acc := by rfl

theorem geometry_Rows_block_012_reverse (acc : List SourceJson) :
    (SimplicesBlock012.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock012 := by
  rw [geometry_Rows_block_012_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_012 :
    geometryRowsJsonBlock012.mapM decodeGeometryRow = .ok geometryRowsTypedBlock012 := by
  simp only [geometryRowsJsonBlock012, geometryRowsTypedBlock012, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_096, decode_geometry_Rows_097, decode_geometry_Rows_098, decode_geometry_Rows_099, decode_geometry_Rows_100, decode_geometry_Rows_101, decode_geometry_Rows_102, decode_geometry_Rows_103]
  rfl

theorem geometry_Rows_block_012_length : geometryRowsTypedBlock012.length = 8 := by rfl

#print axioms geometryRow096_simplexId_read
#print axioms geometryRow096_vertexIds_read
#print axioms geometryRow096_physicalVolume_field
#print axioms geometryRow096_physicalVolume_numerator_no_slash
#print axioms geometryRow096_physicalVolume_numerator_parse
#print axioms geometryRow096_physicalVolume_denominator_parse
#print axioms geometryRow096_physicalVolume_denominator_nonzero
#print axioms geometryRow096_physicalVolume_parse
#print axioms geometryRow096_physicalVolume_read
#print axioms geometryRow096_meanGap_field
#print axioms geometryRow096_meanGap_numerator_no_slash
#print axioms geometryRow096_meanGap_numerator_parse
#print axioms geometryRow096_meanGap_denominator_parse
#print axioms geometryRow096_meanGap_denominator_nonzero
#print axioms geometryRow096_meanGap_parse
#print axioms geometryRow096_meanGap_read
#print axioms geometryRow096_jensenBound_field
#print axioms geometryRow096_jensenBound_numerator_no_slash
#print axioms geometryRow096_jensenBound_numerator_parse
#print axioms geometryRow096_jensenBound_denominator_parse
#print axioms geometryRow096_jensenBound_denominator_nonzero
#print axioms geometryRow096_jensenBound_parse
#print axioms geometryRow096_jensenBound_read
#print axioms geometryRow096_factorMaxima_read
#print axioms geometryRow096_gapWeightedMeans_read
#print axioms geometryRow096_floor_text_read
#print axioms geometryRow096_floor_chars_parse
#print axioms geometryRow096_floor_parse
#print axioms decode_geometry_Rows_096
#print axioms geometryRow096_shape
#print axioms geometryRow097_simplexId_read
#print axioms geometryRow097_vertexIds_read
#print axioms geometryRow097_physicalVolume_field
#print axioms geometryRow097_physicalVolume_numerator_no_slash
#print axioms geometryRow097_physicalVolume_numerator_parse
#print axioms geometryRow097_physicalVolume_denominator_parse
#print axioms geometryRow097_physicalVolume_denominator_nonzero
#print axioms geometryRow097_physicalVolume_parse
#print axioms geometryRow097_physicalVolume_read
#print axioms geometryRow097_meanGap_field
#print axioms geometryRow097_meanGap_numerator_no_slash
#print axioms geometryRow097_meanGap_numerator_parse
#print axioms geometryRow097_meanGap_denominator_parse
#print axioms geometryRow097_meanGap_denominator_nonzero
#print axioms geometryRow097_meanGap_parse
#print axioms geometryRow097_meanGap_read
#print axioms geometryRow097_jensenBound_field
#print axioms geometryRow097_jensenBound_numerator_no_slash
#print axioms geometryRow097_jensenBound_numerator_parse
#print axioms geometryRow097_jensenBound_denominator_parse
#print axioms geometryRow097_jensenBound_denominator_nonzero
#print axioms geometryRow097_jensenBound_parse
#print axioms geometryRow097_jensenBound_read
#print axioms geometryRow097_factorMaxima_read
#print axioms geometryRow097_gapWeightedMeans_read
#print axioms geometryRow097_floor_text_read
#print axioms geometryRow097_floor_chars_parse
#print axioms geometryRow097_floor_parse
#print axioms decode_geometry_Rows_097
#print axioms geometryRow097_shape
#print axioms geometryRow098_simplexId_read
#print axioms geometryRow098_vertexIds_read
#print axioms geometryRow098_physicalVolume_field
#print axioms geometryRow098_physicalVolume_numerator_no_slash
#print axioms geometryRow098_physicalVolume_numerator_parse
#print axioms geometryRow098_physicalVolume_denominator_parse
#print axioms geometryRow098_physicalVolume_denominator_nonzero
#print axioms geometryRow098_physicalVolume_parse
#print axioms geometryRow098_physicalVolume_read
#print axioms geometryRow098_meanGap_field
#print axioms geometryRow098_meanGap_numerator_no_slash
#print axioms geometryRow098_meanGap_numerator_parse
#print axioms geometryRow098_meanGap_denominator_parse
#print axioms geometryRow098_meanGap_denominator_nonzero
#print axioms geometryRow098_meanGap_parse
#print axioms geometryRow098_meanGap_read
#print axioms geometryRow098_jensenBound_field
#print axioms geometryRow098_jensenBound_numerator_no_slash
#print axioms geometryRow098_jensenBound_numerator_parse
#print axioms geometryRow098_jensenBound_denominator_parse
#print axioms geometryRow098_jensenBound_denominator_nonzero
#print axioms geometryRow098_jensenBound_parse
#print axioms geometryRow098_jensenBound_read
#print axioms geometryRow098_factorMaxima_read
#print axioms geometryRow098_gapWeightedMeans_read
#print axioms geometryRow098_floor_text_read
#print axioms geometryRow098_floor_chars_parse
#print axioms geometryRow098_floor_parse
#print axioms decode_geometry_Rows_098
#print axioms geometryRow098_shape
#print axioms geometryRow099_simplexId_read
#print axioms geometryRow099_vertexIds_read
#print axioms geometryRow099_physicalVolume_field
#print axioms geometryRow099_physicalVolume_numerator_no_slash
#print axioms geometryRow099_physicalVolume_numerator_parse
#print axioms geometryRow099_physicalVolume_denominator_parse
#print axioms geometryRow099_physicalVolume_denominator_nonzero
#print axioms geometryRow099_physicalVolume_parse
#print axioms geometryRow099_physicalVolume_read
#print axioms geometryRow099_meanGap_field
#print axioms geometryRow099_meanGap_numerator_no_slash
#print axioms geometryRow099_meanGap_numerator_parse
#print axioms geometryRow099_meanGap_denominator_parse
#print axioms geometryRow099_meanGap_denominator_nonzero
#print axioms geometryRow099_meanGap_parse
#print axioms geometryRow099_meanGap_read
#print axioms geometryRow099_jensenBound_field
#print axioms geometryRow099_jensenBound_numerator_no_slash
#print axioms geometryRow099_jensenBound_numerator_parse
#print axioms geometryRow099_jensenBound_denominator_parse
#print axioms geometryRow099_jensenBound_denominator_nonzero
#print axioms geometryRow099_jensenBound_parse
#print axioms geometryRow099_jensenBound_read
#print axioms geometryRow099_factorMaxima_read
#print axioms geometryRow099_gapWeightedMeans_read
#print axioms geometryRow099_floor_text_read
#print axioms geometryRow099_floor_chars_parse
#print axioms geometryRow099_floor_parse
#print axioms decode_geometry_Rows_099
#print axioms geometryRow099_shape
#print axioms geometryRow100_simplexId_read
#print axioms geometryRow100_vertexIds_read
#print axioms geometryRow100_physicalVolume_field
#print axioms geometryRow100_physicalVolume_numerator_no_slash
#print axioms geometryRow100_physicalVolume_numerator_parse
#print axioms geometryRow100_physicalVolume_denominator_parse
#print axioms geometryRow100_physicalVolume_denominator_nonzero
#print axioms geometryRow100_physicalVolume_parse
#print axioms geometryRow100_physicalVolume_read
#print axioms geometryRow100_meanGap_field
#print axioms geometryRow100_meanGap_numerator_no_slash
#print axioms geometryRow100_meanGap_numerator_parse
#print axioms geometryRow100_meanGap_denominator_parse
#print axioms geometryRow100_meanGap_denominator_nonzero
#print axioms geometryRow100_meanGap_parse
#print axioms geometryRow100_meanGap_read
#print axioms geometryRow100_jensenBound_field
#print axioms geometryRow100_jensenBound_numerator_no_slash
#print axioms geometryRow100_jensenBound_numerator_parse
#print axioms geometryRow100_jensenBound_denominator_parse
#print axioms geometryRow100_jensenBound_denominator_nonzero
#print axioms geometryRow100_jensenBound_parse
#print axioms geometryRow100_jensenBound_read
#print axioms geometryRow100_factorMaxima_read
#print axioms geometryRow100_gapWeightedMeans_read
#print axioms geometryRow100_floor_text_read
#print axioms geometryRow100_floor_chars_parse
#print axioms geometryRow100_floor_parse
#print axioms decode_geometry_Rows_100
#print axioms geometryRow100_shape
#print axioms geometryRow101_simplexId_read
#print axioms geometryRow101_vertexIds_read
#print axioms geometryRow101_physicalVolume_field
#print axioms geometryRow101_physicalVolume_numerator_no_slash
#print axioms geometryRow101_physicalVolume_numerator_parse
#print axioms geometryRow101_physicalVolume_denominator_parse
#print axioms geometryRow101_physicalVolume_denominator_nonzero
#print axioms geometryRow101_physicalVolume_parse
#print axioms geometryRow101_physicalVolume_read
#print axioms geometryRow101_meanGap_field
#print axioms geometryRow101_meanGap_numerator_no_slash
#print axioms geometryRow101_meanGap_numerator_parse
#print axioms geometryRow101_meanGap_denominator_parse
#print axioms geometryRow101_meanGap_denominator_nonzero
#print axioms geometryRow101_meanGap_parse
#print axioms geometryRow101_meanGap_read
#print axioms geometryRow101_jensenBound_field
#print axioms geometryRow101_jensenBound_numerator_no_slash
#print axioms geometryRow101_jensenBound_numerator_parse
#print axioms geometryRow101_jensenBound_denominator_parse
#print axioms geometryRow101_jensenBound_denominator_nonzero
#print axioms geometryRow101_jensenBound_parse
#print axioms geometryRow101_jensenBound_read
#print axioms geometryRow101_factorMaxima_read
#print axioms geometryRow101_gapWeightedMeans_read
#print axioms geometryRow101_floor_text_read
#print axioms geometryRow101_floor_chars_parse
#print axioms geometryRow101_floor_parse
#print axioms decode_geometry_Rows_101
#print axioms geometryRow101_shape
#print axioms geometryRow102_simplexId_read
#print axioms geometryRow102_vertexIds_read
#print axioms geometryRow102_physicalVolume_field
#print axioms geometryRow102_physicalVolume_numerator_no_slash
#print axioms geometryRow102_physicalVolume_numerator_parse
#print axioms geometryRow102_physicalVolume_denominator_parse
#print axioms geometryRow102_physicalVolume_denominator_nonzero
#print axioms geometryRow102_physicalVolume_parse
#print axioms geometryRow102_physicalVolume_read
#print axioms geometryRow102_meanGap_field
#print axioms geometryRow102_meanGap_numerator_no_slash
#print axioms geometryRow102_meanGap_numerator_parse
#print axioms geometryRow102_meanGap_denominator_parse
#print axioms geometryRow102_meanGap_denominator_nonzero
#print axioms geometryRow102_meanGap_parse
#print axioms geometryRow102_meanGap_read
#print axioms geometryRow102_jensenBound_field
#print axioms geometryRow102_jensenBound_numerator_no_slash
#print axioms geometryRow102_jensenBound_numerator_parse
#print axioms geometryRow102_jensenBound_denominator_parse
#print axioms geometryRow102_jensenBound_denominator_nonzero
#print axioms geometryRow102_jensenBound_parse
#print axioms geometryRow102_jensenBound_read
#print axioms geometryRow102_factorMaxima_read
#print axioms geometryRow102_gapWeightedMeans_read
#print axioms geometryRow102_floor_text_read
#print axioms geometryRow102_floor_chars_parse
#print axioms geometryRow102_floor_parse
#print axioms decode_geometry_Rows_102
#print axioms geometryRow102_shape
#print axioms geometryRow103_simplexId_read
#print axioms geometryRow103_vertexIds_read
#print axioms geometryRow103_physicalVolume_field
#print axioms geometryRow103_physicalVolume_numerator_no_slash
#print axioms geometryRow103_physicalVolume_numerator_parse
#print axioms geometryRow103_physicalVolume_denominator_parse
#print axioms geometryRow103_physicalVolume_denominator_nonzero
#print axioms geometryRow103_physicalVolume_parse
#print axioms geometryRow103_physicalVolume_read
#print axioms geometryRow103_meanGap_field
#print axioms geometryRow103_meanGap_numerator_no_slash
#print axioms geometryRow103_meanGap_numerator_parse
#print axioms geometryRow103_meanGap_denominator_parse
#print axioms geometryRow103_meanGap_denominator_nonzero
#print axioms geometryRow103_meanGap_parse
#print axioms geometryRow103_meanGap_read
#print axioms geometryRow103_jensenBound_field
#print axioms geometryRow103_jensenBound_numerator_no_slash
#print axioms geometryRow103_jensenBound_numerator_parse
#print axioms geometryRow103_jensenBound_denominator_parse
#print axioms geometryRow103_jensenBound_denominator_nonzero
#print axioms geometryRow103_jensenBound_parse
#print axioms geometryRow103_jensenBound_read
#print axioms geometryRow103_factorMaxima_read
#print axioms geometryRow103_gapWeightedMeans_read
#print axioms geometryRow103_floor_text_read
#print axioms geometryRow103_floor_chars_parse
#print axioms geometryRow103_floor_parse
#print axioms decode_geometry_Rows_103
#print axioms geometryRow103_shape
#print axioms geometry_Rows_block_012_push_eq
#print axioms geometry_Rows_block_012_reverse
#print axioms decode_geometry_Rows_block_012
#print axioms geometry_Rows_block_012_length

end ImbalancedChen.P2OriginalSaving19Geometry06ScalableDecoding
