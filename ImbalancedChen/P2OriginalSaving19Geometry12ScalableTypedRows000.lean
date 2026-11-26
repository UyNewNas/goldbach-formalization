import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry12ScalableSimplicesBlock000

/-! Local typed certificates for original cell 12, rows 0 through 7.
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

noncomputable def geometryRowsJson000 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped000 : GeometryRow :=
  { simplexId := 0,
    vertexIds := #[139, 115, 85, 50, 47, 9, 3, 1, 0],
    physicalVolume := ((716462409670504700495220246068759450813907679 : ℚ) / (25422914558619648000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((371389673 : ℚ) / (235720000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((37046941 : ℚ) / (426000000 : ℚ)), ((62734339 : ℚ) / (852000000 : ℚ)), ((22690517 : ℚ) / (332000000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((2324513475196949115925291 : ℚ) / (48989388833531477100000000 : ℚ)), ((4823986827999269496516611 : ℚ) / (97978777667062954200000000 : ℚ)), ((171640905293865296609911 : ℚ) / (1547033331585204540000000 : ℚ)), ((27726365026399967761002863 : ℚ) / (293936333001188862600000000 : ℚ)), ((1396944118895585965146977 : ℚ) / (15470333315852045400000000 : ℚ)), ((13724996806034534466293 : ℚ) / (175799242225591425000000 : ℚ)), ((147034445320066327963819 : ℚ) / (2109590906707097100000000 : ℚ)), ((5483778077339223869256241 : ℚ) / (92821999895112272400000000 : ℚ)), ((14369896574663551342037047 : ℚ) / (587872666002377725200000000 : ℚ)), ((5935754117732668560601601 : ℚ) / (293936333001188862600000000 : ℚ))],
    jensenBound := ((5562750356312508317865247688766296024564097676624390108237425180525495645129371260530566800033373907073760381462348601640877281265506775028268945183827060406722558868117790191924492817605639409743100906135343750000000000000000000 : ℚ) / (10972623146328131638314277818617460917075631394127555151884355072505989282822681890088833386730394640401050032437095315128939849494763216718612920913969555488468906721782370754945099762841657453050832771087578282726872462064366192103092973 : ℚ)),
    jensenFloorQ96 := (40166009839105206084 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_simplexId_before"
  err.flush

theorem geometryRow000_simplexId_read :
    geometryRowsJson000.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped000.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_vertexIds_before"
  err.flush

theorem geometryRow000_vertexIds_read :
    geometryRowsJson000.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped000.vertexIds := by decide +kernel

noncomputable def geometryRow000_physicalVolumeNumeratorChars : List Char := ['7', '1', '6', '4', '6', '2', '4', '0', '9', '6', '7', '0', '5', '0', '4', '7', '0', '0', '4', '9', '5', '2', '2', '0', '2', '4', '6', '0', '6', '8', '7', '5', '9', '4', '5', '0', '8', '1', '3', '9', '0', '7', '6', '7', '9']
noncomputable def geometryRow000_physicalVolumeDenominatorChars : List Char := ['2', '5', '4', '2', '2', '9', '1', '4', '5', '5', '8', '6', '1', '9', '6', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_physicalVolumeText : String := String.ofList (geometryRow000_physicalVolumeNumeratorChars ++ '/' :: geometryRow000_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_physicalVolume_before_field"
  err.flush

theorem geometryRow000_physicalVolume_field :
    geometryRowsJson000.getObjVal? "physical_volume" = .ok (.str geometryRow000_physicalVolumeText) := by rfl

theorem geometryRow000_physicalVolume_numerator_no_slash :
    geometryRow000_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeNumeratorChars = some (716462409670504700495220246068759450813907679 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow000_physicalVolumeDenominatorChars = some (25422914558619648000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_physicalVolume_denominator_nonzero : (25422914558619648000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_physicalVolume_parse :
    parseRational geometryRow000_physicalVolumeText = .ok geometryRowsTyped000.physicalVolume :=
  original_rational_fraction_of_chars geometryRow000_physicalVolumeNumeratorChars geometryRow000_physicalVolumeDenominatorChars
    (716462409670504700495220246068759450813907679 : Int) (25422914558619648000000000000000000000000000000000000000000000000 : Int)
    geometryRow000_physicalVolume_numerator_no_slash geometryRow000_physicalVolume_numerator_parse
    geometryRow000_physicalVolume_denominator_parse geometryRow000_physicalVolume_denominator_nonzero

theorem geometryRow000_physicalVolume_read :
    rationalField geometryRowsJson000 "physical_volume" = .ok geometryRowsTyped000.physicalVolume :=
  original_rationalField_of_string geometryRowsJson000 "physical_volume" geometryRow000_physicalVolumeText
    geometryRowsTyped000.physicalVolume geometryRow000_physicalVolume_field geometryRow000_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_physicalVolume_complete"
  err.flush

noncomputable def geometryRow000_meanGapNumeratorChars : List Char := ['3', '7', '1', '3', '8', '9', '6', '7', '3']
noncomputable def geometryRow000_meanGapDenominatorChars : List Char := ['2', '3', '5', '7', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_meanGapText : String := String.ofList (geometryRow000_meanGapNumeratorChars ++ '/' :: geometryRow000_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_meanGap_before_field"
  err.flush

theorem geometryRow000_meanGap_field :
    geometryRowsJson000.getObjVal? "mean_gap" = .ok (.str geometryRow000_meanGapText) := by rfl

theorem geometryRow000_meanGap_numerator_no_slash :
    geometryRow000_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_meanGap_numerator_parse :
    SourceJson.intChars geometryRow000_meanGapNumeratorChars = some (371389673 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_parse :
    SourceJson.intChars geometryRow000_meanGapDenominatorChars = some (235720000000 : Int) := by decide +kernel

theorem geometryRow000_meanGap_denominator_nonzero : (235720000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_meanGap_parse :
    parseRational geometryRow000_meanGapText = .ok geometryRowsTyped000.meanGap :=
  original_rational_fraction_of_chars geometryRow000_meanGapNumeratorChars geometryRow000_meanGapDenominatorChars
    (371389673 : Int) (235720000000 : Int)
    geometryRow000_meanGap_numerator_no_slash geometryRow000_meanGap_numerator_parse
    geometryRow000_meanGap_denominator_parse geometryRow000_meanGap_denominator_nonzero

theorem geometryRow000_meanGap_read :
    rationalField geometryRowsJson000 "mean_gap" = .ok geometryRowsTyped000.meanGap :=
  original_rationalField_of_string geometryRowsJson000 "mean_gap" geometryRow000_meanGapText
    geometryRowsTyped000.meanGap geometryRow000_meanGap_field geometryRow000_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_meanGap_complete"
  err.flush

noncomputable def geometryRow000_jensenBoundNumeratorChars : List Char := ['5', '5', '6', '2', '7', '5', '0', '3', '5', '6', '3', '1', '2', '5', '0', '8', '3', '1', '7', '8', '6', '5', '2', '4', '7', '6', '8', '8', '7', '6', '6', '2', '9', '6', '0', '2', '4', '5', '6', '4', '0', '9', '7', '6', '7', '6', '6', '2', '4', '3', '9', '0', '1', '0', '8', '2', '3', '7', '4', '2', '5', '1', '8', '0', '5', '2', '5', '4', '9', '5', '6', '4', '5', '1', '2', '9', '3', '7', '1', '2', '6', '0', '5', '3', '0', '5', '6', '6', '8', '0', '0', '0', '3', '3', '3', '7', '3', '9', '0', '7', '0', '7', '3', '7', '6', '0', '3', '8', '1', '4', '6', '2', '3', '4', '8', '6', '0', '1', '6', '4', '0', '8', '7', '7', '2', '8', '1', '2', '6', '5', '5', '0', '6', '7', '7', '5', '0', '2', '8', '2', '6', '8', '9', '4', '5', '1', '8', '3', '8', '2', '7', '0', '6', '0', '4', '0', '6', '7', '2', '2', '5', '5', '8', '8', '6', '8', '1', '1', '7', '7', '9', '0', '1', '9', '1', '9', '2', '4', '4', '9', '2', '8', '1', '7', '6', '0', '5', '6', '3', '9', '4', '0', '9', '7', '4', '3', '1', '0', '0', '9', '0', '6', '1', '3', '5', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow000_jensenBoundDenominatorChars : List Char := ['1', '0', '9', '7', '2', '6', '2', '3', '1', '4', '6', '3', '2', '8', '1', '3', '1', '6', '3', '8', '3', '1', '4', '2', '7', '7', '8', '1', '8', '6', '1', '7', '4', '6', '0', '9', '1', '7', '0', '7', '5', '6', '3', '1', '3', '9', '4', '1', '2', '7', '5', '5', '5', '1', '5', '1', '8', '8', '4', '3', '5', '5', '0', '7', '2', '5', '0', '5', '9', '8', '9', '2', '8', '2', '8', '2', '2', '6', '8', '1', '8', '9', '0', '0', '8', '8', '8', '3', '3', '3', '8', '6', '7', '3', '0', '3', '9', '4', '6', '4', '0', '4', '0', '1', '0', '5', '0', '0', '3', '2', '4', '3', '7', '0', '9', '5', '3', '1', '5', '1', '2', '8', '9', '3', '9', '8', '4', '9', '4', '9', '4', '7', '6', '3', '2', '1', '6', '7', '1', '8', '6', '1', '2', '9', '2', '0', '9', '1', '3', '9', '6', '9', '5', '5', '5', '4', '8', '8', '4', '6', '8', '9', '0', '6', '7', '2', '1', '7', '8', '2', '3', '7', '0', '7', '5', '4', '9', '4', '5', '0', '9', '9', '7', '6', '2', '8', '4', '1', '6', '5', '7', '4', '5', '3', '0', '5', '0', '8', '3', '2', '7', '7', '1', '0', '8', '7', '5', '7', '8', '2', '8', '2', '7', '2', '6', '8', '7', '2', '4', '6', '2', '0', '6', '4', '3', '6', '6', '1', '9', '2', '1', '0', '3', '0', '9', '2', '9', '7', '3']
noncomputable def geometryRow000_jensenBoundText : String := String.ofList (geometryRow000_jensenBoundNumeratorChars ++ '/' :: geometryRow000_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_jensenBound_before_field"
  err.flush

theorem geometryRow000_jensenBound_field :
    geometryRowsJson000.getObjVal? "jensen_bound" = .ok (.str geometryRow000_jensenBoundText) := by rfl

theorem geometryRow000_jensenBound_numerator_no_slash :
    geometryRow000_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow000_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow000_jensenBoundNumeratorChars = some (5562750356312508317865247688766296024564097676624390108237425180525495645129371260530566800033373907073760381462348601640877281265506775028268945183827060406722558868117790191924492817605639409743100906135343750000000000000000000 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow000_jensenBoundDenominatorChars = some (10972623146328131638314277818617460917075631394127555151884355072505989282822681890088833386730394640401050032437095315128939849494763216718612920913969555488468906721782370754945099762841657453050832771087578282726872462064366192103092973 : Int) := by decide +kernel

theorem geometryRow000_jensenBound_denominator_nonzero : (10972623146328131638314277818617460917075631394127555151884355072505989282822681890088833386730394640401050032437095315128939849494763216718612920913969555488468906721782370754945099762841657453050832771087578282726872462064366192103092973 : Int) ≠ 0 := by decide +kernel

theorem geometryRow000_jensenBound_parse :
    parseRational geometryRow000_jensenBoundText = .ok geometryRowsTyped000.jensenBound :=
  original_rational_fraction_of_chars geometryRow000_jensenBoundNumeratorChars geometryRow000_jensenBoundDenominatorChars
    (5562750356312508317865247688766296024564097676624390108237425180525495645129371260530566800033373907073760381462348601640877281265506775028268945183827060406722558868117790191924492817605639409743100906135343750000000000000000000 : Int) (10972623146328131638314277818617460917075631394127555151884355072505989282822681890088833386730394640401050032437095315128939849494763216718612920913969555488468906721782370754945099762841657453050832771087578282726872462064366192103092973 : Int)
    geometryRow000_jensenBound_numerator_no_slash geometryRow000_jensenBound_numerator_parse
    geometryRow000_jensenBound_denominator_parse geometryRow000_jensenBound_denominator_nonzero

theorem geometryRow000_jensenBound_read :
    rationalField geometryRowsJson000 "jensen_bound" = .ok geometryRowsTyped000.jensenBound :=
  original_rationalField_of_string geometryRowsJson000 "jensen_bound" geometryRow000_jensenBoundText
    geometryRowsTyped000.jensenBound geometryRow000_jensenBound_field geometryRow000_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_factorMaxima_before"
  err.flush

theorem geometryRow000_factorMaxima_read :
    rationalArrayField geometryRowsJson000 "factor_maxima" = .ok geometryRowsTyped000.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_gapWeightedMeans_before"
  err.flush

theorem geometryRow000_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson000 "gap_weighted_means" = .ok geometryRowsTyped000.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow000_floorChars : List Char := ['4', '0', '1', '6', '6', '0', '0', '9', '8', '3', '9', '1', '0', '5', '2', '0', '6', '0', '8', '4']
noncomputable def geometryRow000_floorText : String := String.ofList geometryRow000_floorChars

theorem geometryRow000_floor_text_read :
    geometryRowsJson000.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow000_floorText := by rfl

theorem geometryRow000_floor_chars_parse :
    SourceJson.intChars geometryRow000_floorChars = some (40166009839105206084 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_000_original_decoder_complete"
  err.flush

theorem geometryRow000_shape :
    geometryRowsTyped000.simplexId = 0 ∧
    geometryRowsTyped000.vertexIds.size = 9 ∧ geometryRowsTyped000.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped000.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped000.factorMaxima.size = 10 ∧ geometryRowsTyped000.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson001 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped001 : GeometryRow :=
  { simplexId := 1,
    vertexIds := #[139, 115, 85, 50, 47, 9, 3, 2, 0],
    physicalVolume := ((45467326039022769928863815195433505813679549627 : ℚ) / (1364567281429524480000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((4893079703 : ℚ) / (2990520000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((37046941 : ℚ) / (426000000 : ℚ)), ((62734339 : ℚ) / (852000000 : ℚ)), ((340991 : ℚ) / (5000000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((375569594396573541975847 : ℚ) / (7776360680242700700000000 : ℚ)), ((1126558136013824138606859 : ℚ) / (22465041965145579800000000 : ℚ)), ((354538475805200877453031 : ℚ) / (3192400700310161340000000 : ℚ)), ((57175581096860528656755823 : ℚ) / (606556133058930654600000000 : ℚ)), ((2880602204001485904366817 : ℚ) / (31924007003101613400000000 : ℚ)), ((28235730439024409232353 : ℚ) / (362772806853427425000000 : ℚ)), ((9551432318107850519887 : ℚ) / (136039802570035284375000 : ℚ)), ((11267762322818193396121091 : ℚ) / (191544042018609680400000000 : ℚ)), ((1043649189376992981258251 : ℚ) / (44930083930291159600000000 : ℚ)), ((1381469448586087428574169 : ℚ) / (67395125895436739400000000 : ℚ))],
    jensenBound := ((150805442317588439291001565989077469696695307315521345612849507990026601263587883215824459608194215331575411933214957484125045982225455925917927181843960366321484581945081553246989433716048023939109254956400585937500000000000000 : ℚ) / (242155753334406057263335216583222521006654888537149384260984043916311617258813235169968039534018657095316260307358599089706818085232764336488689923988617977756023042765524896376810589349435671950329661298522338722939881384827431363471741 : ℚ)),
    jensenFloorQ96 := (49340302377510383716 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_simplexId_before"
  err.flush

theorem geometryRow001_simplexId_read :
    geometryRowsJson001.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped001.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_vertexIds_before"
  err.flush

theorem geometryRow001_vertexIds_read :
    geometryRowsJson001.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped001.vertexIds := by decide +kernel

noncomputable def geometryRow001_physicalVolumeNumeratorChars : List Char := ['4', '5', '4', '6', '7', '3', '2', '6', '0', '3', '9', '0', '2', '2', '7', '6', '9', '9', '2', '8', '8', '6', '3', '8', '1', '5', '1', '9', '5', '4', '3', '3', '5', '0', '5', '8', '1', '3', '6', '7', '9', '5', '4', '9', '6', '2', '7']
noncomputable def geometryRow001_physicalVolumeDenominatorChars : List Char := ['1', '3', '6', '4', '5', '6', '7', '2', '8', '1', '4', '2', '9', '5', '2', '4', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_physicalVolumeText : String := String.ofList (geometryRow001_physicalVolumeNumeratorChars ++ '/' :: geometryRow001_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_physicalVolume_before_field"
  err.flush

theorem geometryRow001_physicalVolume_field :
    geometryRowsJson001.getObjVal? "physical_volume" = .ok (.str geometryRow001_physicalVolumeText) := by rfl

theorem geometryRow001_physicalVolume_numerator_no_slash :
    geometryRow001_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeNumeratorChars = some (45467326039022769928863815195433505813679549627 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow001_physicalVolumeDenominatorChars = some (1364567281429524480000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow001_physicalVolume_denominator_nonzero : (1364567281429524480000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_physicalVolume_parse :
    parseRational geometryRow001_physicalVolumeText = .ok geometryRowsTyped001.physicalVolume :=
  original_rational_fraction_of_chars geometryRow001_physicalVolumeNumeratorChars geometryRow001_physicalVolumeDenominatorChars
    (45467326039022769928863815195433505813679549627 : Int) (1364567281429524480000000000000000000000000000000000000000000000000 : Int)
    geometryRow001_physicalVolume_numerator_no_slash geometryRow001_physicalVolume_numerator_parse
    geometryRow001_physicalVolume_denominator_parse geometryRow001_physicalVolume_denominator_nonzero

theorem geometryRow001_physicalVolume_read :
    rationalField geometryRowsJson001 "physical_volume" = .ok geometryRowsTyped001.physicalVolume :=
  original_rationalField_of_string geometryRowsJson001 "physical_volume" geometryRow001_physicalVolumeText
    geometryRowsTyped001.physicalVolume geometryRow001_physicalVolume_field geometryRow001_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_physicalVolume_complete"
  err.flush

noncomputable def geometryRow001_meanGapNumeratorChars : List Char := ['4', '8', '9', '3', '0', '7', '9', '7', '0', '3']
noncomputable def geometryRow001_meanGapDenominatorChars : List Char := ['2', '9', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_meanGapText : String := String.ofList (geometryRow001_meanGapNumeratorChars ++ '/' :: geometryRow001_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_meanGap_before_field"
  err.flush

theorem geometryRow001_meanGap_field :
    geometryRowsJson001.getObjVal? "mean_gap" = .ok (.str geometryRow001_meanGapText) := by rfl

theorem geometryRow001_meanGap_numerator_no_slash :
    geometryRow001_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_meanGap_numerator_parse :
    SourceJson.intChars geometryRow001_meanGapNumeratorChars = some (4893079703 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_parse :
    SourceJson.intChars geometryRow001_meanGapDenominatorChars = some (2990520000000 : Int) := by decide +kernel

theorem geometryRow001_meanGap_denominator_nonzero : (2990520000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_meanGap_parse :
    parseRational geometryRow001_meanGapText = .ok geometryRowsTyped001.meanGap :=
  original_rational_fraction_of_chars geometryRow001_meanGapNumeratorChars geometryRow001_meanGapDenominatorChars
    (4893079703 : Int) (2990520000000 : Int)
    geometryRow001_meanGap_numerator_no_slash geometryRow001_meanGap_numerator_parse
    geometryRow001_meanGap_denominator_parse geometryRow001_meanGap_denominator_nonzero

theorem geometryRow001_meanGap_read :
    rationalField geometryRowsJson001 "mean_gap" = .ok geometryRowsTyped001.meanGap :=
  original_rationalField_of_string geometryRowsJson001 "mean_gap" geometryRow001_meanGapText
    geometryRowsTyped001.meanGap geometryRow001_meanGap_field geometryRow001_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_meanGap_complete"
  err.flush

noncomputable def geometryRow001_jensenBoundNumeratorChars : List Char := ['1', '5', '0', '8', '0', '5', '4', '4', '2', '3', '1', '7', '5', '8', '8', '4', '3', '9', '2', '9', '1', '0', '0', '1', '5', '6', '5', '9', '8', '9', '0', '7', '7', '4', '6', '9', '6', '9', '6', '6', '9', '5', '3', '0', '7', '3', '1', '5', '5', '2', '1', '3', '4', '5', '6', '1', '2', '8', '4', '9', '5', '0', '7', '9', '9', '0', '0', '2', '6', '6', '0', '1', '2', '6', '3', '5', '8', '7', '8', '8', '3', '2', '1', '5', '8', '2', '4', '4', '5', '9', '6', '0', '8', '1', '9', '4', '2', '1', '5', '3', '3', '1', '5', '7', '5', '4', '1', '1', '9', '3', '3', '2', '1', '4', '9', '5', '7', '4', '8', '4', '1', '2', '5', '0', '4', '5', '9', '8', '2', '2', '2', '5', '4', '5', '5', '9', '2', '5', '9', '1', '7', '9', '2', '7', '1', '8', '1', '8', '4', '3', '9', '6', '0', '3', '6', '6', '3', '2', '1', '4', '8', '4', '5', '8', '1', '9', '4', '5', '0', '8', '1', '5', '5', '3', '2', '4', '6', '9', '8', '9', '4', '3', '3', '7', '1', '6', '0', '4', '8', '0', '2', '3', '9', '3', '9', '1', '0', '9', '2', '5', '4', '9', '5', '6', '4', '0', '0', '5', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow001_jensenBoundDenominatorChars : List Char := ['2', '4', '2', '1', '5', '5', '7', '5', '3', '3', '3', '4', '4', '0', '6', '0', '5', '7', '2', '6', '3', '3', '3', '5', '2', '1', '6', '5', '8', '3', '2', '2', '2', '5', '2', '1', '0', '0', '6', '6', '5', '4', '8', '8', '8', '5', '3', '7', '1', '4', '9', '3', '8', '4', '2', '6', '0', '9', '8', '4', '0', '4', '3', '9', '1', '6', '3', '1', '1', '6', '1', '7', '2', '5', '8', '8', '1', '3', '2', '3', '5', '1', '6', '9', '9', '6', '8', '0', '3', '9', '5', '3', '4', '0', '1', '8', '6', '5', '7', '0', '9', '5', '3', '1', '6', '2', '6', '0', '3', '0', '7', '3', '5', '8', '5', '9', '9', '0', '8', '9', '7', '0', '6', '8', '1', '8', '0', '8', '5', '2', '3', '2', '7', '6', '4', '3', '3', '6', '4', '8', '8', '6', '8', '9', '9', '2', '3', '9', '8', '8', '6', '1', '7', '9', '7', '7', '7', '5', '6', '0', '2', '3', '0', '4', '2', '7', '6', '5', '5', '2', '4', '8', '9', '6', '3', '7', '6', '8', '1', '0', '5', '8', '9', '3', '4', '9', '4', '3', '5', '6', '7', '1', '9', '5', '0', '3', '2', '9', '6', '6', '1', '2', '9', '8', '5', '2', '2', '3', '3', '8', '7', '2', '2', '9', '3', '9', '8', '8', '1', '3', '8', '4', '8', '2', '7', '4', '3', '1', '3', '6', '3', '4', '7', '1', '7', '4', '1']
noncomputable def geometryRow001_jensenBoundText : String := String.ofList (geometryRow001_jensenBoundNumeratorChars ++ '/' :: geometryRow001_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_jensenBound_before_field"
  err.flush

theorem geometryRow001_jensenBound_field :
    geometryRowsJson001.getObjVal? "jensen_bound" = .ok (.str geometryRow001_jensenBoundText) := by rfl

theorem geometryRow001_jensenBound_numerator_no_slash :
    geometryRow001_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow001_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow001_jensenBoundNumeratorChars = some (150805442317588439291001565989077469696695307315521345612849507990026601263587883215824459608194215331575411933214957484125045982225455925917927181843960366321484581945081553246989433716048023939109254956400585937500000000000000 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow001_jensenBoundDenominatorChars = some (242155753334406057263335216583222521006654888537149384260984043916311617258813235169968039534018657095316260307358599089706818085232764336488689923988617977756023042765524896376810589349435671950329661298522338722939881384827431363471741 : Int) := by decide +kernel

theorem geometryRow001_jensenBound_denominator_nonzero : (242155753334406057263335216583222521006654888537149384260984043916311617258813235169968039534018657095316260307358599089706818085232764336488689923988617977756023042765524896376810589349435671950329661298522338722939881384827431363471741 : Int) ≠ 0 := by decide +kernel

theorem geometryRow001_jensenBound_parse :
    parseRational geometryRow001_jensenBoundText = .ok geometryRowsTyped001.jensenBound :=
  original_rational_fraction_of_chars geometryRow001_jensenBoundNumeratorChars geometryRow001_jensenBoundDenominatorChars
    (150805442317588439291001565989077469696695307315521345612849507990026601263587883215824459608194215331575411933214957484125045982225455925917927181843960366321484581945081553246989433716048023939109254956400585937500000000000000 : Int) (242155753334406057263335216583222521006654888537149384260984043916311617258813235169968039534018657095316260307358599089706818085232764336488689923988617977756023042765524896376810589349435671950329661298522338722939881384827431363471741 : Int)
    geometryRow001_jensenBound_numerator_no_slash geometryRow001_jensenBound_numerator_parse
    geometryRow001_jensenBound_denominator_parse geometryRow001_jensenBound_denominator_nonzero

theorem geometryRow001_jensenBound_read :
    rationalField geometryRowsJson001 "jensen_bound" = .ok geometryRowsTyped001.jensenBound :=
  original_rationalField_of_string geometryRowsJson001 "jensen_bound" geometryRow001_jensenBoundText
    geometryRowsTyped001.jensenBound geometryRow001_jensenBound_field geometryRow001_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_factorMaxima_before"
  err.flush

theorem geometryRow001_factorMaxima_read :
    rationalArrayField geometryRowsJson001 "factor_maxima" = .ok geometryRowsTyped001.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_gapWeightedMeans_before"
  err.flush

theorem geometryRow001_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson001 "gap_weighted_means" = .ok geometryRowsTyped001.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow001_floorChars : List Char := ['4', '9', '3', '4', '0', '3', '0', '2', '3', '7', '7', '5', '1', '0', '3', '8', '3', '7', '1', '6']
noncomputable def geometryRow001_floorText : String := String.ofList geometryRow001_floorChars

theorem geometryRow001_floor_text_read :
    geometryRowsJson001.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow001_floorText := by rfl

theorem geometryRow001_floor_chars_parse :
    SourceJson.intChars geometryRow001_floorChars = some (49340302377510383716 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_001_original_decoder_complete"
  err.flush

theorem geometryRow001_shape :
    geometryRowsTyped001.simplexId = 1 ∧
    geometryRowsTyped001.vertexIds.size = 9 ∧ geometryRowsTyped001.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped001.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped001.factorMaxima.size = 10 ∧ geometryRowsTyped001.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson002 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped002 : GeometryRow :=
  { simplexId := 2,
    vertexIds := #[139, 115, 85, 50, 47, 9, 5, 1, 0],
    physicalVolume := ((4967015052527067074948416554503647831372258992671 : ℚ) / (122592471865983770112000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((18968929561 : ℚ) / (11809572000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((37046941 : ℚ) / (426000000 : ℚ)), ((62734339 : ℚ) / (852000000 : ℚ)), ((22690517 : ℚ) / (332000000 : ℚ)), ((5796879 : ℚ) / (167000000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((12811330194289206889937437 : ℚ) / (267430826791420719932736000 : ℚ)), ((8311410910054923315513206467 : ℚ) / (167144266744637949957960000000 : ℚ)), ((2929604449886766827781736979 : ℚ) / (26391200012311255256520000000 : ℚ)), ((2955091509920303916500629099 : ℚ) / (31339550014619615617117500000 : ℚ)), ((595538461790117964014558269 : ℚ) / (6597800003077813814130000000 : ℚ)), ((37400364776699129289590719 : ℚ) / (479840000223841004664000000 : ℚ)), ((505964098069881469383369637 : ℚ) / (7197600003357615069960000000 : ℚ)), ((4412325292977239918503898827 : ℚ) / (79173600036933765769560000000 : ℚ)), ((3344569092653617509965961877 : ℚ) / (125358200058478462468470000000 : ℚ)), ((10208000486469188947356534829 : ℚ) / (501432800233913849873880000000 : ℚ))],
    jensenBound := ((1091401030835312026353134588072377013980048488921258085358826203807617267748999184345447363431302527718439526412122828313722343230045077184952986607390387784496536202075174185928754124468040772467576881300629859703696031942232101374464499248243328691200000000000 : ℚ) / (1564957799193063308979776222593400372245975804727067720438900626337939408337775074175053656632963461085827673715417998495539206503525802650431270459356892684699086909720298144694830188352039624478490999369958900793986991832779589842372039439547627378954414681126011715283 : ℚ)),
    jensenFloorQ96 := (55253693284152427075 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_simplexId_before"
  err.flush

theorem geometryRow002_simplexId_read :
    geometryRowsJson002.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped002.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_vertexIds_before"
  err.flush

theorem geometryRow002_vertexIds_read :
    geometryRowsJson002.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped002.vertexIds := by decide +kernel

noncomputable def geometryRow002_physicalVolumeNumeratorChars : List Char := ['4', '9', '6', '7', '0', '1', '5', '0', '5', '2', '5', '2', '7', '0', '6', '7', '0', '7', '4', '9', '4', '8', '4', '1', '6', '5', '5', '4', '5', '0', '3', '6', '4', '7', '8', '3', '1', '3', '7', '2', '2', '5', '8', '9', '9', '2', '6', '7', '1']
noncomputable def geometryRow002_physicalVolumeDenominatorChars : List Char := ['1', '2', '2', '5', '9', '2', '4', '7', '1', '8', '6', '5', '9', '8', '3', '7', '7', '0', '1', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_physicalVolumeText : String := String.ofList (geometryRow002_physicalVolumeNumeratorChars ++ '/' :: geometryRow002_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_physicalVolume_before_field"
  err.flush

theorem geometryRow002_physicalVolume_field :
    geometryRowsJson002.getObjVal? "physical_volume" = .ok (.str geometryRow002_physicalVolumeText) := by rfl

theorem geometryRow002_physicalVolume_numerator_no_slash :
    geometryRow002_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeNumeratorChars = some (4967015052527067074948416554503647831372258992671 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow002_physicalVolumeDenominatorChars = some (122592471865983770112000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow002_physicalVolume_denominator_nonzero : (122592471865983770112000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_physicalVolume_parse :
    parseRational geometryRow002_physicalVolumeText = .ok geometryRowsTyped002.physicalVolume :=
  original_rational_fraction_of_chars geometryRow002_physicalVolumeNumeratorChars geometryRow002_physicalVolumeDenominatorChars
    (4967015052527067074948416554503647831372258992671 : Int) (122592471865983770112000000000000000000000000000000000000000000000000 : Int)
    geometryRow002_physicalVolume_numerator_no_slash geometryRow002_physicalVolume_numerator_parse
    geometryRow002_physicalVolume_denominator_parse geometryRow002_physicalVolume_denominator_nonzero

theorem geometryRow002_physicalVolume_read :
    rationalField geometryRowsJson002 "physical_volume" = .ok geometryRowsTyped002.physicalVolume :=
  original_rationalField_of_string geometryRowsJson002 "physical_volume" geometryRow002_physicalVolumeText
    geometryRowsTyped002.physicalVolume geometryRow002_physicalVolume_field geometryRow002_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_physicalVolume_complete"
  err.flush

noncomputable def geometryRow002_meanGapNumeratorChars : List Char := ['1', '8', '9', '6', '8', '9', '2', '9', '5', '6', '1']
noncomputable def geometryRow002_meanGapDenominatorChars : List Char := ['1', '1', '8', '0', '9', '5', '7', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_meanGapText : String := String.ofList (geometryRow002_meanGapNumeratorChars ++ '/' :: geometryRow002_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_meanGap_before_field"
  err.flush

theorem geometryRow002_meanGap_field :
    geometryRowsJson002.getObjVal? "mean_gap" = .ok (.str geometryRow002_meanGapText) := by rfl

theorem geometryRow002_meanGap_numerator_no_slash :
    geometryRow002_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_meanGap_numerator_parse :
    SourceJson.intChars geometryRow002_meanGapNumeratorChars = some (18968929561 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_parse :
    SourceJson.intChars geometryRow002_meanGapDenominatorChars = some (11809572000000 : Int) := by decide +kernel

theorem geometryRow002_meanGap_denominator_nonzero : (11809572000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_meanGap_parse :
    parseRational geometryRow002_meanGapText = .ok geometryRowsTyped002.meanGap :=
  original_rational_fraction_of_chars geometryRow002_meanGapNumeratorChars geometryRow002_meanGapDenominatorChars
    (18968929561 : Int) (11809572000000 : Int)
    geometryRow002_meanGap_numerator_no_slash geometryRow002_meanGap_numerator_parse
    geometryRow002_meanGap_denominator_parse geometryRow002_meanGap_denominator_nonzero

theorem geometryRow002_meanGap_read :
    rationalField geometryRowsJson002 "mean_gap" = .ok geometryRowsTyped002.meanGap :=
  original_rationalField_of_string geometryRowsJson002 "mean_gap" geometryRow002_meanGapText
    geometryRowsTyped002.meanGap geometryRow002_meanGap_field geometryRow002_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_meanGap_complete"
  err.flush

noncomputable def geometryRow002_jensenBoundNumeratorChars : List Char := ['1', '0', '9', '1', '4', '0', '1', '0', '3', '0', '8', '3', '5', '3', '1', '2', '0', '2', '6', '3', '5', '3', '1', '3', '4', '5', '8', '8', '0', '7', '2', '3', '7', '7', '0', '1', '3', '9', '8', '0', '0', '4', '8', '4', '8', '8', '9', '2', '1', '2', '5', '8', '0', '8', '5', '3', '5', '8', '8', '2', '6', '2', '0', '3', '8', '0', '7', '6', '1', '7', '2', '6', '7', '7', '4', '8', '9', '9', '9', '1', '8', '4', '3', '4', '5', '4', '4', '7', '3', '6', '3', '4', '3', '1', '3', '0', '2', '5', '2', '7', '7', '1', '8', '4', '3', '9', '5', '2', '6', '4', '1', '2', '1', '2', '2', '8', '2', '8', '3', '1', '3', '7', '2', '2', '3', '4', '3', '2', '3', '0', '0', '4', '5', '0', '7', '7', '1', '8', '4', '9', '5', '2', '9', '8', '6', '6', '0', '7', '3', '9', '0', '3', '8', '7', '7', '8', '4', '4', '9', '6', '5', '3', '6', '2', '0', '2', '0', '7', '5', '1', '7', '4', '1', '8', '5', '9', '2', '8', '7', '5', '4', '1', '2', '4', '4', '6', '8', '0', '4', '0', '7', '7', '2', '4', '6', '7', '5', '7', '6', '8', '8', '1', '3', '0', '0', '6', '2', '9', '8', '5', '9', '7', '0', '3', '6', '9', '6', '0', '3', '1', '9', '4', '2', '2', '3', '2', '1', '0', '1', '3', '7', '4', '4', '6', '4', '4', '9', '9', '2', '4', '8', '2', '4', '3', '3', '2', '8', '6', '9', '1', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow002_jensenBoundDenominatorChars : List Char := ['1', '5', '6', '4', '9', '5', '7', '7', '9', '9', '1', '9', '3', '0', '6', '3', '3', '0', '8', '9', '7', '9', '7', '7', '6', '2', '2', '2', '5', '9', '3', '4', '0', '0', '3', '7', '2', '2', '4', '5', '9', '7', '5', '8', '0', '4', '7', '2', '7', '0', '6', '7', '7', '2', '0', '4', '3', '8', '9', '0', '0', '6', '2', '6', '3', '3', '7', '9', '3', '9', '4', '0', '8', '3', '3', '7', '7', '7', '5', '0', '7', '4', '1', '7', '5', '0', '5', '3', '6', '5', '6', '6', '3', '2', '9', '6', '3', '4', '6', '1', '0', '8', '5', '8', '2', '7', '6', '7', '3', '7', '1', '5', '4', '1', '7', '9', '9', '8', '4', '9', '5', '5', '3', '9', '2', '0', '6', '5', '0', '3', '5', '2', '5', '8', '0', '2', '6', '5', '0', '4', '3', '1', '2', '7', '0', '4', '5', '9', '3', '5', '6', '8', '9', '2', '6', '8', '4', '6', '9', '9', '0', '8', '6', '9', '0', '9', '7', '2', '0', '2', '9', '8', '1', '4', '4', '6', '9', '4', '8', '3', '0', '1', '8', '8', '3', '5', '2', '0', '3', '9', '6', '2', '4', '4', '7', '8', '4', '9', '0', '9', '9', '9', '3', '6', '9', '9', '5', '8', '9', '0', '0', '7', '9', '3', '9', '8', '6', '9', '9', '1', '8', '3', '2', '7', '7', '9', '5', '8', '9', '8', '4', '2', '3', '7', '2', '0', '3', '9', '4', '3', '9', '5', '4', '7', '6', '2', '7', '3', '7', '8', '9', '5', '4', '4', '1', '4', '6', '8', '1', '1', '2', '6', '0', '1', '1', '7', '1', '5', '2', '8', '3']
noncomputable def geometryRow002_jensenBoundText : String := String.ofList (geometryRow002_jensenBoundNumeratorChars ++ '/' :: geometryRow002_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_jensenBound_before_field"
  err.flush

theorem geometryRow002_jensenBound_field :
    geometryRowsJson002.getObjVal? "jensen_bound" = .ok (.str geometryRow002_jensenBoundText) := by rfl

theorem geometryRow002_jensenBound_numerator_no_slash :
    geometryRow002_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow002_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow002_jensenBoundNumeratorChars = some (1091401030835312026353134588072377013980048488921258085358826203807617267748999184345447363431302527718439526412122828313722343230045077184952986607390387784496536202075174185928754124468040772467576881300629859703696031942232101374464499248243328691200000000000 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow002_jensenBoundDenominatorChars = some (1564957799193063308979776222593400372245975804727067720438900626337939408337775074175053656632963461085827673715417998495539206503525802650431270459356892684699086909720298144694830188352039624478490999369958900793986991832779589842372039439547627378954414681126011715283 : Int) := by decide +kernel

theorem geometryRow002_jensenBound_denominator_nonzero : (1564957799193063308979776222593400372245975804727067720438900626337939408337775074175053656632963461085827673715417998495539206503525802650431270459356892684699086909720298144694830188352039624478490999369958900793986991832779589842372039439547627378954414681126011715283 : Int) ≠ 0 := by decide +kernel

theorem geometryRow002_jensenBound_parse :
    parseRational geometryRow002_jensenBoundText = .ok geometryRowsTyped002.jensenBound :=
  original_rational_fraction_of_chars geometryRow002_jensenBoundNumeratorChars geometryRow002_jensenBoundDenominatorChars
    (1091401030835312026353134588072377013980048488921258085358826203807617267748999184345447363431302527718439526412122828313722343230045077184952986607390387784496536202075174185928754124468040772467576881300629859703696031942232101374464499248243328691200000000000 : Int) (1564957799193063308979776222593400372245975804727067720438900626337939408337775074175053656632963461085827673715417998495539206503525802650431270459356892684699086909720298144694830188352039624478490999369958900793986991832779589842372039439547627378954414681126011715283 : Int)
    geometryRow002_jensenBound_numerator_no_slash geometryRow002_jensenBound_numerator_parse
    geometryRow002_jensenBound_denominator_parse geometryRow002_jensenBound_denominator_nonzero

theorem geometryRow002_jensenBound_read :
    rationalField geometryRowsJson002 "jensen_bound" = .ok geometryRowsTyped002.jensenBound :=
  original_rationalField_of_string geometryRowsJson002 "jensen_bound" geometryRow002_jensenBoundText
    geometryRowsTyped002.jensenBound geometryRow002_jensenBound_field geometryRow002_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_factorMaxima_before"
  err.flush

theorem geometryRow002_factorMaxima_read :
    rationalArrayField geometryRowsJson002 "factor_maxima" = .ok geometryRowsTyped002.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_gapWeightedMeans_before"
  err.flush

theorem geometryRow002_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson002 "gap_weighted_means" = .ok geometryRowsTyped002.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow002_floorChars : List Char := ['5', '5', '2', '5', '3', '6', '9', '3', '2', '8', '4', '1', '5', '2', '4', '2', '7', '0', '7', '5']
noncomputable def geometryRow002_floorText : String := String.ofList geometryRow002_floorChars

theorem geometryRow002_floor_text_read :
    geometryRowsJson002.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow002_floorText := by rfl

theorem geometryRow002_floor_chars_parse :
    SourceJson.intChars geometryRow002_floorChars = some (55253693284152427075 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_002_original_decoder_complete"
  err.flush

theorem geometryRow002_shape :
    geometryRowsTyped002.simplexId = 2 ∧
    geometryRowsTyped002.vertexIds.size = 9 ∧ geometryRowsTyped002.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped002.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped002.factorMaxima.size = 10 ∧ geometryRowsTyped002.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson003 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped003 : GeometryRow :=
  { simplexId := 3,
    vertexIds := #[139, 115, 85, 50, 47, 9, 5, 4, 1],
    physicalVolume := ((1614364177450106626435252438819091417215823449879 : ℚ) / (10117589721581067264000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((30448613621 : ℚ) / (17714358000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((28778169 : ℚ) / (332000000 : ℚ)), ((62734339 : ℚ) / (852000000 : ℚ)), ((22690517 : ℚ) / (332000000 : ℚ)), ((5796879 : ℚ) / (167000000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((13277066119282866057801197831 : ℚ) / (268297226825937097579560000000 : ℚ)), ((2759640805901582338157822671 : ℚ) / (53659445365187419515912000000 : ℚ)), ((4711140528931847775199721809 : ℚ) / (42362720025147962775720000000 : ℚ)), ((37898764441444114042529892319 : ℚ) / (402445840238905646369340000000 : ℚ)), ((1909320779331303615324405871 : ℚ) / (21181360012573981387860000000 : ℚ)), ((298454717014046279428373197 : ℚ) / (3851156365922542070520000000 : ℚ)), ((1582061126128499742202206661 : ℚ) / (23106938195535252423120000000 : ℚ)), ((13893379111874082054860702647 : ℚ) / (254176320150887776654320000000 : ℚ)), ((4474365787630689881173970371 : ℚ) / (160978336095562258547736000000 : ℚ)), ((16842578411528109064247900237 : ℚ) / (804891680477811292738680000000 : ℚ))],
    jensenBound := ((315378204370830781442815467036184399548488445905969220484291273685907610421058045381736579599393208171176514419655831910327190081553130040658180519085787689664541829501943186789923750477982769274066237733732048130651179559881006400561524362274516907622400000000000000 : ℚ) / (116508731199738878192829257599999862863290618198286372170104233992877358620159596066747355394956934124230131985259759371893186883532754191393065470928592733291967167635781849452900683470653756499634166036020509855861940049252842072351602126691561144187273783021337155716438981 : ℚ)),
    jensenFloorQ96 := (214463202646267025934 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_simplexId_before"
  err.flush

theorem geometryRow003_simplexId_read :
    geometryRowsJson003.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped003.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_vertexIds_before"
  err.flush

theorem geometryRow003_vertexIds_read :
    geometryRowsJson003.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped003.vertexIds := by decide +kernel

noncomputable def geometryRow003_physicalVolumeNumeratorChars : List Char := ['1', '6', '1', '4', '3', '6', '4', '1', '7', '7', '4', '5', '0', '1', '0', '6', '6', '2', '6', '4', '3', '5', '2', '5', '2', '4', '3', '8', '8', '1', '9', '0', '9', '1', '4', '1', '7', '2', '1', '5', '8', '2', '3', '4', '4', '9', '8', '7', '9']
noncomputable def geometryRow003_physicalVolumeDenominatorChars : List Char := ['1', '0', '1', '1', '7', '5', '8', '9', '7', '2', '1', '5', '8', '1', '0', '6', '7', '2', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_physicalVolumeText : String := String.ofList (geometryRow003_physicalVolumeNumeratorChars ++ '/' :: geometryRow003_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_physicalVolume_before_field"
  err.flush

theorem geometryRow003_physicalVolume_field :
    geometryRowsJson003.getObjVal? "physical_volume" = .ok (.str geometryRow003_physicalVolumeText) := by rfl

theorem geometryRow003_physicalVolume_numerator_no_slash :
    geometryRow003_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeNumeratorChars = some (1614364177450106626435252438819091417215823449879 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow003_physicalVolumeDenominatorChars = some (10117589721581067264000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow003_physicalVolume_denominator_nonzero : (10117589721581067264000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_physicalVolume_parse :
    parseRational geometryRow003_physicalVolumeText = .ok geometryRowsTyped003.physicalVolume :=
  original_rational_fraction_of_chars geometryRow003_physicalVolumeNumeratorChars geometryRow003_physicalVolumeDenominatorChars
    (1614364177450106626435252438819091417215823449879 : Int) (10117589721581067264000000000000000000000000000000000000000000000000 : Int)
    geometryRow003_physicalVolume_numerator_no_slash geometryRow003_physicalVolume_numerator_parse
    geometryRow003_physicalVolume_denominator_parse geometryRow003_physicalVolume_denominator_nonzero

theorem geometryRow003_physicalVolume_read :
    rationalField geometryRowsJson003 "physical_volume" = .ok geometryRowsTyped003.physicalVolume :=
  original_rationalField_of_string geometryRowsJson003 "physical_volume" geometryRow003_physicalVolumeText
    geometryRowsTyped003.physicalVolume geometryRow003_physicalVolume_field geometryRow003_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_physicalVolume_complete"
  err.flush

noncomputable def geometryRow003_meanGapNumeratorChars : List Char := ['3', '0', '4', '4', '8', '6', '1', '3', '6', '2', '1']
noncomputable def geometryRow003_meanGapDenominatorChars : List Char := ['1', '7', '7', '1', '4', '3', '5', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_meanGapText : String := String.ofList (geometryRow003_meanGapNumeratorChars ++ '/' :: geometryRow003_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_meanGap_before_field"
  err.flush

theorem geometryRow003_meanGap_field :
    geometryRowsJson003.getObjVal? "mean_gap" = .ok (.str geometryRow003_meanGapText) := by rfl

theorem geometryRow003_meanGap_numerator_no_slash :
    geometryRow003_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_meanGap_numerator_parse :
    SourceJson.intChars geometryRow003_meanGapNumeratorChars = some (30448613621 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_parse :
    SourceJson.intChars geometryRow003_meanGapDenominatorChars = some (17714358000000 : Int) := by decide +kernel

theorem geometryRow003_meanGap_denominator_nonzero : (17714358000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_meanGap_parse :
    parseRational geometryRow003_meanGapText = .ok geometryRowsTyped003.meanGap :=
  original_rational_fraction_of_chars geometryRow003_meanGapNumeratorChars geometryRow003_meanGapDenominatorChars
    (30448613621 : Int) (17714358000000 : Int)
    geometryRow003_meanGap_numerator_no_slash geometryRow003_meanGap_numerator_parse
    geometryRow003_meanGap_denominator_parse geometryRow003_meanGap_denominator_nonzero

theorem geometryRow003_meanGap_read :
    rationalField geometryRowsJson003 "mean_gap" = .ok geometryRowsTyped003.meanGap :=
  original_rationalField_of_string geometryRowsJson003 "mean_gap" geometryRow003_meanGapText
    geometryRowsTyped003.meanGap geometryRow003_meanGap_field geometryRow003_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_meanGap_complete"
  err.flush

noncomputable def geometryRow003_jensenBoundNumeratorChars : List Char := ['3', '1', '5', '3', '7', '8', '2', '0', '4', '3', '7', '0', '8', '3', '0', '7', '8', '1', '4', '4', '2', '8', '1', '5', '4', '6', '7', '0', '3', '6', '1', '8', '4', '3', '9', '9', '5', '4', '8', '4', '8', '8', '4', '4', '5', '9', '0', '5', '9', '6', '9', '2', '2', '0', '4', '8', '4', '2', '9', '1', '2', '7', '3', '6', '8', '5', '9', '0', '7', '6', '1', '0', '4', '2', '1', '0', '5', '8', '0', '4', '5', '3', '8', '1', '7', '3', '6', '5', '7', '9', '5', '9', '9', '3', '9', '3', '2', '0', '8', '1', '7', '1', '1', '7', '6', '5', '1', '4', '4', '1', '9', '6', '5', '5', '8', '3', '1', '9', '1', '0', '3', '2', '7', '1', '9', '0', '0', '8', '1', '5', '5', '3', '1', '3', '0', '0', '4', '0', '6', '5', '8', '1', '8', '0', '5', '1', '9', '0', '8', '5', '7', '8', '7', '6', '8', '9', '6', '6', '4', '5', '4', '1', '8', '2', '9', '5', '0', '1', '9', '4', '3', '1', '8', '6', '7', '8', '9', '9', '2', '3', '7', '5', '0', '4', '7', '7', '9', '8', '2', '7', '6', '9', '2', '7', '4', '0', '6', '6', '2', '3', '7', '7', '3', '3', '7', '3', '2', '0', '4', '8', '1', '3', '0', '6', '5', '1', '1', '7', '9', '5', '5', '9', '8', '8', '1', '0', '0', '6', '4', '0', '0', '5', '6', '1', '5', '2', '4', '3', '6', '2', '2', '7', '4', '5', '1', '6', '9', '0', '7', '6', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow003_jensenBoundDenominatorChars : List Char := ['1', '1', '6', '5', '0', '8', '7', '3', '1', '1', '9', '9', '7', '3', '8', '8', '7', '8', '1', '9', '2', '8', '2', '9', '2', '5', '7', '5', '9', '9', '9', '9', '9', '8', '6', '2', '8', '6', '3', '2', '9', '0', '6', '1', '8', '1', '9', '8', '2', '8', '6', '3', '7', '2', '1', '7', '0', '1', '0', '4', '2', '3', '3', '9', '9', '2', '8', '7', '7', '3', '5', '8', '6', '2', '0', '1', '5', '9', '5', '9', '6', '0', '6', '6', '7', '4', '7', '3', '5', '5', '3', '9', '4', '9', '5', '6', '9', '3', '4', '1', '2', '4', '2', '3', '0', '1', '3', '1', '9', '8', '5', '2', '5', '9', '7', '5', '9', '3', '7', '1', '8', '9', '3', '1', '8', '6', '8', '8', '3', '5', '3', '2', '7', '5', '4', '1', '9', '1', '3', '9', '3', '0', '6', '5', '4', '7', '0', '9', '2', '8', '5', '9', '2', '7', '3', '3', '2', '9', '1', '9', '6', '7', '1', '6', '7', '6', '3', '5', '7', '8', '1', '8', '4', '9', '4', '5', '2', '9', '0', '0', '6', '8', '3', '4', '7', '0', '6', '5', '3', '7', '5', '6', '4', '9', '9', '6', '3', '4', '1', '6', '6', '0', '3', '6', '0', '2', '0', '5', '0', '9', '8', '5', '5', '8', '6', '1', '9', '4', '0', '0', '4', '9', '2', '5', '2', '8', '4', '2', '0', '7', '2', '3', '5', '1', '6', '0', '2', '1', '2', '6', '6', '9', '1', '5', '6', '1', '1', '4', '4', '1', '8', '7', '2', '7', '3', '7', '8', '3', '0', '2', '1', '3', '3', '7', '1', '5', '5', '7', '1', '6', '4', '3', '8', '9', '8', '1']
noncomputable def geometryRow003_jensenBoundText : String := String.ofList (geometryRow003_jensenBoundNumeratorChars ++ '/' :: geometryRow003_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_jensenBound_before_field"
  err.flush

theorem geometryRow003_jensenBound_field :
    geometryRowsJson003.getObjVal? "jensen_bound" = .ok (.str geometryRow003_jensenBoundText) := by rfl

theorem geometryRow003_jensenBound_numerator_no_slash :
    geometryRow003_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow003_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow003_jensenBoundNumeratorChars = some (315378204370830781442815467036184399548488445905969220484291273685907610421058045381736579599393208171176514419655831910327190081553130040658180519085787689664541829501943186789923750477982769274066237733732048130651179559881006400561524362274516907622400000000000000 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow003_jensenBoundDenominatorChars = some (116508731199738878192829257599999862863290618198286372170104233992877358620159596066747355394956934124230131985259759371893186883532754191393065470928592733291967167635781849452900683470653756499634166036020509855861940049252842072351602126691561144187273783021337155716438981 : Int) := by decide +kernel

theorem geometryRow003_jensenBound_denominator_nonzero : (116508731199738878192829257599999862863290618198286372170104233992877358620159596066747355394956934124230131985259759371893186883532754191393065470928592733291967167635781849452900683470653756499634166036020509855861940049252842072351602126691561144187273783021337155716438981 : Int) ≠ 0 := by decide +kernel

theorem geometryRow003_jensenBound_parse :
    parseRational geometryRow003_jensenBoundText = .ok geometryRowsTyped003.jensenBound :=
  original_rational_fraction_of_chars geometryRow003_jensenBoundNumeratorChars geometryRow003_jensenBoundDenominatorChars
    (315378204370830781442815467036184399548488445905969220484291273685907610421058045381736579599393208171176514419655831910327190081553130040658180519085787689664541829501943186789923750477982769274066237733732048130651179559881006400561524362274516907622400000000000000 : Int) (116508731199738878192829257599999862863290618198286372170104233992877358620159596066747355394956934124230131985259759371893186883532754191393065470928592733291967167635781849452900683470653756499634166036020509855861940049252842072351602126691561144187273783021337155716438981 : Int)
    geometryRow003_jensenBound_numerator_no_slash geometryRow003_jensenBound_numerator_parse
    geometryRow003_jensenBound_denominator_parse geometryRow003_jensenBound_denominator_nonzero

theorem geometryRow003_jensenBound_read :
    rationalField geometryRowsJson003 "jensen_bound" = .ok geometryRowsTyped003.jensenBound :=
  original_rationalField_of_string geometryRowsJson003 "jensen_bound" geometryRow003_jensenBoundText
    geometryRowsTyped003.jensenBound geometryRow003_jensenBound_field geometryRow003_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_factorMaxima_before"
  err.flush

theorem geometryRow003_factorMaxima_read :
    rationalArrayField geometryRowsJson003 "factor_maxima" = .ok geometryRowsTyped003.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_gapWeightedMeans_before"
  err.flush

theorem geometryRow003_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson003 "gap_weighted_means" = .ok geometryRowsTyped003.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow003_floorChars : List Char := ['2', '1', '4', '4', '6', '3', '2', '0', '2', '6', '4', '6', '2', '6', '7', '0', '2', '5', '9', '3', '4']
noncomputable def geometryRow003_floorText : String := String.ofList geometryRow003_floorChars

theorem geometryRow003_floor_text_read :
    geometryRowsJson003.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow003_floorText := by rfl

theorem geometryRow003_floor_chars_parse :
    SourceJson.intChars geometryRow003_floorChars = some (214463202646267025934 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_003_original_decoder_complete"
  err.flush

theorem geometryRow003_shape :
    geometryRowsTyped003.simplexId = 3 ∧
    geometryRowsTyped003.vertexIds.size = 9 ∧ geometryRowsTyped003.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped003.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped003.factorMaxima.size = 10 ∧ geometryRowsTyped003.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson004 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped004 : GeometryRow :=
  { simplexId := 4,
    vertexIds := #[139, 115, 85, 50, 47, 9, 8, 3, 1],
    physicalVolume := ((3534768100865549877939601211789940718486239529 : ℚ) / (34894196453007360000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((3744538307 : ℚ) / (2121480000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((28778169 : ℚ) / (332000000 : ℚ)), ((62734339 : ℚ) / (852000000 : ℚ)), ((22690517 : ℚ) / (332000000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((24798078928728665695827619 : ℚ) / (493935767362267668900000000 : ℚ)), ((51569600923170145057868249 : ℚ) / (987871534724535337800000000 : ℚ)), ((1736081087303662804801699 : ℚ) / (15597971600913715860000000 : ℚ)), ((278922991814815970488557017 : ℚ) / (2963614604173606013400000000 : ℚ)), ((14051631725306372928041543 : ℚ) / (155979716009137158600000000 : ℚ)), ((274009319075010692033899 : ℚ) / (3544993545662208150000000 : ℚ)), ((5787253992554593117592749 : ℚ) / (85079845095892995600000000 : ℚ)), ((54421143427455212639134009 : ℚ) / (935878296054822951600000000 : ℚ)), ((35474633297149914378773827 : ℚ) / (1481807302086803006700000000 : ℚ)), ((62779000396365191633070659 : ℚ) / (2963614604173606013400000000 : ℚ))],
    jensenBound := ((12627983196975677774929050053836996231043166818604650113725155975887760516358824848348597466563759776019277261521125686004264777440941809711609932942314817724438785062478133693843389047236649031706233798960287509692355356250000000000000000000 : ℚ) / (6770703338033791548444936642589425048654239041924404846536286208203796070238398950109674899066534850794596467183511341177383109238386924446229498566190318575137209896912732292272240886741970490391948372254091910759145629262309512905471798124444918119 : ℚ)),
    jensenFloorQ96 := (147767795309716022907 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_simplexId_before"
  err.flush

theorem geometryRow004_simplexId_read :
    geometryRowsJson004.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped004.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_vertexIds_before"
  err.flush

theorem geometryRow004_vertexIds_read :
    geometryRowsJson004.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped004.vertexIds := by decide +kernel

noncomputable def geometryRow004_physicalVolumeNumeratorChars : List Char := ['3', '5', '3', '4', '7', '6', '8', '1', '0', '0', '8', '6', '5', '5', '4', '9', '8', '7', '7', '9', '3', '9', '6', '0', '1', '2', '1', '1', '7', '8', '9', '9', '4', '0', '7', '1', '8', '4', '8', '6', '2', '3', '9', '5', '2', '9']
noncomputable def geometryRow004_physicalVolumeDenominatorChars : List Char := ['3', '4', '8', '9', '4', '1', '9', '6', '4', '5', '3', '0', '0', '7', '3', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_physicalVolumeText : String := String.ofList (geometryRow004_physicalVolumeNumeratorChars ++ '/' :: geometryRow004_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_physicalVolume_before_field"
  err.flush

theorem geometryRow004_physicalVolume_field :
    geometryRowsJson004.getObjVal? "physical_volume" = .ok (.str geometryRow004_physicalVolumeText) := by rfl

theorem geometryRow004_physicalVolume_numerator_no_slash :
    geometryRow004_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeNumeratorChars = some (3534768100865549877939601211789940718486239529 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow004_physicalVolumeDenominatorChars = some (34894196453007360000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_physicalVolume_denominator_nonzero : (34894196453007360000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_physicalVolume_parse :
    parseRational geometryRow004_physicalVolumeText = .ok geometryRowsTyped004.physicalVolume :=
  original_rational_fraction_of_chars geometryRow004_physicalVolumeNumeratorChars geometryRow004_physicalVolumeDenominatorChars
    (3534768100865549877939601211789940718486239529 : Int) (34894196453007360000000000000000000000000000000000000000000000000 : Int)
    geometryRow004_physicalVolume_numerator_no_slash geometryRow004_physicalVolume_numerator_parse
    geometryRow004_physicalVolume_denominator_parse geometryRow004_physicalVolume_denominator_nonzero

theorem geometryRow004_physicalVolume_read :
    rationalField geometryRowsJson004 "physical_volume" = .ok geometryRowsTyped004.physicalVolume :=
  original_rationalField_of_string geometryRowsJson004 "physical_volume" geometryRow004_physicalVolumeText
    geometryRowsTyped004.physicalVolume geometryRow004_physicalVolume_field geometryRow004_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_physicalVolume_complete"
  err.flush

noncomputable def geometryRow004_meanGapNumeratorChars : List Char := ['3', '7', '4', '4', '5', '3', '8', '3', '0', '7']
noncomputable def geometryRow004_meanGapDenominatorChars : List Char := ['2', '1', '2', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_meanGapText : String := String.ofList (geometryRow004_meanGapNumeratorChars ++ '/' :: geometryRow004_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_meanGap_before_field"
  err.flush

theorem geometryRow004_meanGap_field :
    geometryRowsJson004.getObjVal? "mean_gap" = .ok (.str geometryRow004_meanGapText) := by rfl

theorem geometryRow004_meanGap_numerator_no_slash :
    geometryRow004_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_meanGap_numerator_parse :
    SourceJson.intChars geometryRow004_meanGapNumeratorChars = some (3744538307 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_parse :
    SourceJson.intChars geometryRow004_meanGapDenominatorChars = some (2121480000000 : Int) := by decide +kernel

theorem geometryRow004_meanGap_denominator_nonzero : (2121480000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_meanGap_parse :
    parseRational geometryRow004_meanGapText = .ok geometryRowsTyped004.meanGap :=
  original_rational_fraction_of_chars geometryRow004_meanGapNumeratorChars geometryRow004_meanGapDenominatorChars
    (3744538307 : Int) (2121480000000 : Int)
    geometryRow004_meanGap_numerator_no_slash geometryRow004_meanGap_numerator_parse
    geometryRow004_meanGap_denominator_parse geometryRow004_meanGap_denominator_nonzero

theorem geometryRow004_meanGap_read :
    rationalField geometryRowsJson004 "mean_gap" = .ok geometryRowsTyped004.meanGap :=
  original_rationalField_of_string geometryRowsJson004 "mean_gap" geometryRow004_meanGapText
    geometryRowsTyped004.meanGap geometryRow004_meanGap_field geometryRow004_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_meanGap_complete"
  err.flush

noncomputable def geometryRow004_jensenBoundNumeratorChars : List Char := ['1', '2', '6', '2', '7', '9', '8', '3', '1', '9', '6', '9', '7', '5', '6', '7', '7', '7', '7', '4', '9', '2', '9', '0', '5', '0', '0', '5', '3', '8', '3', '6', '9', '9', '6', '2', '3', '1', '0', '4', '3', '1', '6', '6', '8', '1', '8', '6', '0', '4', '6', '5', '0', '1', '1', '3', '7', '2', '5', '1', '5', '5', '9', '7', '5', '8', '8', '7', '7', '6', '0', '5', '1', '6', '3', '5', '8', '8', '2', '4', '8', '4', '8', '3', '4', '8', '5', '9', '7', '4', '6', '6', '5', '6', '3', '7', '5', '9', '7', '7', '6', '0', '1', '9', '2', '7', '7', '2', '6', '1', '5', '2', '1', '1', '2', '5', '6', '8', '6', '0', '0', '4', '2', '6', '4', '7', '7', '7', '4', '4', '0', '9', '4', '1', '8', '0', '9', '7', '1', '1', '6', '0', '9', '9', '3', '2', '9', '4', '2', '3', '1', '4', '8', '1', '7', '7', '2', '4', '4', '3', '8', '7', '8', '5', '0', '6', '2', '4', '7', '8', '1', '3', '3', '6', '9', '3', '8', '4', '3', '3', '8', '9', '0', '4', '7', '2', '3', '6', '6', '4', '9', '0', '3', '1', '7', '0', '6', '2', '3', '3', '7', '9', '8', '9', '6', '0', '2', '8', '7', '5', '0', '9', '6', '9', '2', '3', '5', '5', '3', '5', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow004_jensenBoundDenominatorChars : List Char := ['6', '7', '7', '0', '7', '0', '3', '3', '3', '8', '0', '3', '3', '7', '9', '1', '5', '4', '8', '4', '4', '4', '9', '3', '6', '6', '4', '2', '5', '8', '9', '4', '2', '5', '0', '4', '8', '6', '5', '4', '2', '3', '9', '0', '4', '1', '9', '2', '4', '4', '0', '4', '8', '4', '6', '5', '3', '6', '2', '8', '6', '2', '0', '8', '2', '0', '3', '7', '9', '6', '0', '7', '0', '2', '3', '8', '3', '9', '8', '9', '5', '0', '1', '0', '9', '6', '7', '4', '8', '9', '9', '0', '6', '6', '5', '3', '4', '8', '5', '0', '7', '9', '4', '5', '9', '6', '4', '6', '7', '1', '8', '3', '5', '1', '1', '3', '4', '1', '1', '7', '7', '3', '8', '3', '1', '0', '9', '2', '3', '8', '3', '8', '6', '9', '2', '4', '4', '4', '6', '2', '2', '9', '4', '9', '8', '5', '6', '6', '1', '9', '0', '3', '1', '8', '5', '7', '5', '1', '3', '7', '2', '0', '9', '8', '9', '6', '9', '1', '2', '7', '3', '2', '2', '9', '2', '2', '7', '2', '2', '4', '0', '8', '8', '6', '7', '4', '1', '9', '7', '0', '4', '9', '0', '3', '9', '1', '9', '4', '8', '3', '7', '2', '2', '5', '4', '0', '9', '1', '9', '1', '0', '7', '5', '9', '1', '4', '5', '6', '2', '9', '2', '6', '2', '3', '0', '9', '5', '1', '2', '9', '0', '5', '4', '7', '1', '7', '9', '8', '1', '2', '4', '4', '4', '4', '9', '1', '8', '1', '1', '9']
noncomputable def geometryRow004_jensenBoundText : String := String.ofList (geometryRow004_jensenBoundNumeratorChars ++ '/' :: geometryRow004_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_jensenBound_before_field"
  err.flush

theorem geometryRow004_jensenBound_field :
    geometryRowsJson004.getObjVal? "jensen_bound" = .ok (.str geometryRow004_jensenBoundText) := by rfl

theorem geometryRow004_jensenBound_numerator_no_slash :
    geometryRow004_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow004_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow004_jensenBoundNumeratorChars = some (12627983196975677774929050053836996231043166818604650113725155975887760516358824848348597466563759776019277261521125686004264777440941809711609932942314817724438785062478133693843389047236649031706233798960287509692355356250000000000000000000 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow004_jensenBoundDenominatorChars = some (6770703338033791548444936642589425048654239041924404846536286208203796070238398950109674899066534850794596467183511341177383109238386924446229498566190318575137209896912732292272240886741970490391948372254091910759145629262309512905471798124444918119 : Int) := by decide +kernel

theorem geometryRow004_jensenBound_denominator_nonzero : (6770703338033791548444936642589425048654239041924404846536286208203796070238398950109674899066534850794596467183511341177383109238386924446229498566190318575137209896912732292272240886741970490391948372254091910759145629262309512905471798124444918119 : Int) ≠ 0 := by decide +kernel

theorem geometryRow004_jensenBound_parse :
    parseRational geometryRow004_jensenBoundText = .ok geometryRowsTyped004.jensenBound :=
  original_rational_fraction_of_chars geometryRow004_jensenBoundNumeratorChars geometryRow004_jensenBoundDenominatorChars
    (12627983196975677774929050053836996231043166818604650113725155975887760516358824848348597466563759776019277261521125686004264777440941809711609932942314817724438785062478133693843389047236649031706233798960287509692355356250000000000000000000 : Int) (6770703338033791548444936642589425048654239041924404846536286208203796070238398950109674899066534850794596467183511341177383109238386924446229498566190318575137209896912732292272240886741970490391948372254091910759145629262309512905471798124444918119 : Int)
    geometryRow004_jensenBound_numerator_no_slash geometryRow004_jensenBound_numerator_parse
    geometryRow004_jensenBound_denominator_parse geometryRow004_jensenBound_denominator_nonzero

theorem geometryRow004_jensenBound_read :
    rationalField geometryRowsJson004 "jensen_bound" = .ok geometryRowsTyped004.jensenBound :=
  original_rationalField_of_string geometryRowsJson004 "jensen_bound" geometryRow004_jensenBoundText
    geometryRowsTyped004.jensenBound geometryRow004_jensenBound_field geometryRow004_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_factorMaxima_before"
  err.flush

theorem geometryRow004_factorMaxima_read :
    rationalArrayField geometryRowsJson004 "factor_maxima" = .ok geometryRowsTyped004.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_gapWeightedMeans_before"
  err.flush

theorem geometryRow004_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson004 "gap_weighted_means" = .ok geometryRowsTyped004.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow004_floorChars : List Char := ['1', '4', '7', '7', '6', '7', '7', '9', '5', '3', '0', '9', '7', '1', '6', '0', '2', '2', '9', '0', '7']
noncomputable def geometryRow004_floorText : String := String.ofList geometryRow004_floorChars

theorem geometryRow004_floor_text_read :
    geometryRowsJson004.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow004_floorText := by rfl

theorem geometryRow004_floor_chars_parse :
    SourceJson.intChars geometryRow004_floorChars = some (147767795309716022907 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_004_original_decoder_complete"
  err.flush

theorem geometryRow004_shape :
    geometryRowsTyped004.simplexId = 4 ∧
    geometryRowsTyped004.vertexIds.size = 9 ∧ geometryRowsTyped004.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped004.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped004.factorMaxima.size = 10 ∧ geometryRowsTyped004.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson005 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped005 : GeometryRow :=
  { simplexId := 5,
    vertexIds := #[139, 115, 85, 50, 47, 9, 8, 4, 1],
    physicalVolume := ((650829192820699362152955035459508536978479827043 : ℚ) / (4301490240911711232000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((31810355279 : ℚ) / (17714358000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((28778169 : ℚ) / (332000000 : ℚ)), ((62734339 : ℚ) / (852000000 : ℚ)), ((22690517 : ℚ) / (332000000 : ℚ)), ((5796879 : ℚ) / (167000000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((22711400699328852011965493 : ℚ) / (448473889126684639399104000 : ℚ)), ((14763975704673352727336942513 : ℚ) / (280296180704177899624440000000 : ℚ)), ((4928389191573255009324394531 : ℚ) / (44257291690133352572280000000 : ℚ)), ((39556337774531301417048064813 : ℚ) / (420444271056266849436660000000 : ℚ)), ((1992744359572605829971518557 : ℚ) / (22128645845066676286140000000 : ℚ)), ((62098313216390176375118891 : ℚ) / (804678030729697319496000000 : ℚ)), ((32190595343415404478250133 : ℚ) / (482806818437818391697600000 : ℚ)), ((471480604079677458349406789 : ℚ) / (8298242191900003607302500000 : ℚ)), ((21970876980034303821321124883 : ℚ) / (840888542112533698873320000000 : ℚ)), ((17944502473470388729616169431 : ℚ) / (840888542112533698873320000000 : ℚ))],
    jensenBound := ((9864357272969725884124265418516316611613299265452413810510464726806236606861314630917655917293598701337994579557250085596386365645494104346398363605588301647354210626294194325092836986132581314843323514049986338094846788076794775173628518730959152279552000000000 : ℚ) / (3723299813013118869591813130493018183016175592103619067463883787852684240228157010691559635586321144044185453935212501788794337876244870490878685403202560527834849215450185273474707794087704796385058650246863066258628068841192706509685634843801263616583580378756404475373 : ℚ)),
    jensenFloorQ96 := (209903832721208025157 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_simplexId_before"
  err.flush

theorem geometryRow005_simplexId_read :
    geometryRowsJson005.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped005.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_vertexIds_before"
  err.flush

theorem geometryRow005_vertexIds_read :
    geometryRowsJson005.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped005.vertexIds := by decide +kernel

noncomputable def geometryRow005_physicalVolumeNumeratorChars : List Char := ['6', '5', '0', '8', '2', '9', '1', '9', '2', '8', '2', '0', '6', '9', '9', '3', '6', '2', '1', '5', '2', '9', '5', '5', '0', '3', '5', '4', '5', '9', '5', '0', '8', '5', '3', '6', '9', '7', '8', '4', '7', '9', '8', '2', '7', '0', '4', '3']
noncomputable def geometryRow005_physicalVolumeDenominatorChars : List Char := ['4', '3', '0', '1', '4', '9', '0', '2', '4', '0', '9', '1', '1', '7', '1', '1', '2', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_physicalVolumeText : String := String.ofList (geometryRow005_physicalVolumeNumeratorChars ++ '/' :: geometryRow005_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_physicalVolume_before_field"
  err.flush

theorem geometryRow005_physicalVolume_field :
    geometryRowsJson005.getObjVal? "physical_volume" = .ok (.str geometryRow005_physicalVolumeText) := by rfl

theorem geometryRow005_physicalVolume_numerator_no_slash :
    geometryRow005_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeNumeratorChars = some (650829192820699362152955035459508536978479827043 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow005_physicalVolumeDenominatorChars = some (4301490240911711232000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow005_physicalVolume_denominator_nonzero : (4301490240911711232000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_physicalVolume_parse :
    parseRational geometryRow005_physicalVolumeText = .ok geometryRowsTyped005.physicalVolume :=
  original_rational_fraction_of_chars geometryRow005_physicalVolumeNumeratorChars geometryRow005_physicalVolumeDenominatorChars
    (650829192820699362152955035459508536978479827043 : Int) (4301490240911711232000000000000000000000000000000000000000000000000 : Int)
    geometryRow005_physicalVolume_numerator_no_slash geometryRow005_physicalVolume_numerator_parse
    geometryRow005_physicalVolume_denominator_parse geometryRow005_physicalVolume_denominator_nonzero

theorem geometryRow005_physicalVolume_read :
    rationalField geometryRowsJson005 "physical_volume" = .ok geometryRowsTyped005.physicalVolume :=
  original_rationalField_of_string geometryRowsJson005 "physical_volume" geometryRow005_physicalVolumeText
    geometryRowsTyped005.physicalVolume geometryRow005_physicalVolume_field geometryRow005_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_physicalVolume_complete"
  err.flush

noncomputable def geometryRow005_meanGapNumeratorChars : List Char := ['3', '1', '8', '1', '0', '3', '5', '5', '2', '7', '9']
noncomputable def geometryRow005_meanGapDenominatorChars : List Char := ['1', '7', '7', '1', '4', '3', '5', '8', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_meanGapText : String := String.ofList (geometryRow005_meanGapNumeratorChars ++ '/' :: geometryRow005_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_meanGap_before_field"
  err.flush

theorem geometryRow005_meanGap_field :
    geometryRowsJson005.getObjVal? "mean_gap" = .ok (.str geometryRow005_meanGapText) := by rfl

theorem geometryRow005_meanGap_numerator_no_slash :
    geometryRow005_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_meanGap_numerator_parse :
    SourceJson.intChars geometryRow005_meanGapNumeratorChars = some (31810355279 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_parse :
    SourceJson.intChars geometryRow005_meanGapDenominatorChars = some (17714358000000 : Int) := by decide +kernel

theorem geometryRow005_meanGap_denominator_nonzero : (17714358000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_meanGap_parse :
    parseRational geometryRow005_meanGapText = .ok geometryRowsTyped005.meanGap :=
  original_rational_fraction_of_chars geometryRow005_meanGapNumeratorChars geometryRow005_meanGapDenominatorChars
    (31810355279 : Int) (17714358000000 : Int)
    geometryRow005_meanGap_numerator_no_slash geometryRow005_meanGap_numerator_parse
    geometryRow005_meanGap_denominator_parse geometryRow005_meanGap_denominator_nonzero

theorem geometryRow005_meanGap_read :
    rationalField geometryRowsJson005 "mean_gap" = .ok geometryRowsTyped005.meanGap :=
  original_rationalField_of_string geometryRowsJson005 "mean_gap" geometryRow005_meanGapText
    geometryRowsTyped005.meanGap geometryRow005_meanGap_field geometryRow005_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_meanGap_complete"
  err.flush

noncomputable def geometryRow005_jensenBoundNumeratorChars : List Char := ['9', '8', '6', '4', '3', '5', '7', '2', '7', '2', '9', '6', '9', '7', '2', '5', '8', '8', '4', '1', '2', '4', '2', '6', '5', '4', '1', '8', '5', '1', '6', '3', '1', '6', '6', '1', '1', '6', '1', '3', '2', '9', '9', '2', '6', '5', '4', '5', '2', '4', '1', '3', '8', '1', '0', '5', '1', '0', '4', '6', '4', '7', '2', '6', '8', '0', '6', '2', '3', '6', '6', '0', '6', '8', '6', '1', '3', '1', '4', '6', '3', '0', '9', '1', '7', '6', '5', '5', '9', '1', '7', '2', '9', '3', '5', '9', '8', '7', '0', '1', '3', '3', '7', '9', '9', '4', '5', '7', '9', '5', '5', '7', '2', '5', '0', '0', '8', '5', '5', '9', '6', '3', '8', '6', '3', '6', '5', '6', '4', '5', '4', '9', '4', '1', '0', '4', '3', '4', '6', '3', '9', '8', '3', '6', '3', '6', '0', '5', '5', '8', '8', '3', '0', '1', '6', '4', '7', '3', '5', '4', '2', '1', '0', '6', '2', '6', '2', '9', '4', '1', '9', '4', '3', '2', '5', '0', '9', '2', '8', '3', '6', '9', '8', '6', '1', '3', '2', '5', '8', '1', '3', '1', '4', '8', '4', '3', '3', '2', '3', '5', '1', '4', '0', '4', '9', '9', '8', '6', '3', '3', '8', '0', '9', '4', '8', '4', '6', '7', '8', '8', '0', '7', '6', '7', '9', '4', '7', '7', '5', '1', '7', '3', '6', '2', '8', '5', '1', '8', '7', '3', '0', '9', '5', '9', '1', '5', '2', '2', '7', '9', '5', '5', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow005_jensenBoundDenominatorChars : List Char := ['3', '7', '2', '3', '2', '9', '9', '8', '1', '3', '0', '1', '3', '1', '1', '8', '8', '6', '9', '5', '9', '1', '8', '1', '3', '1', '3', '0', '4', '9', '3', '0', '1', '8', '1', '8', '3', '0', '1', '6', '1', '7', '5', '5', '9', '2', '1', '0', '3', '6', '1', '9', '0', '6', '7', '4', '6', '3', '8', '8', '3', '7', '8', '7', '8', '5', '2', '6', '8', '4', '2', '4', '0', '2', '2', '8', '1', '5', '7', '0', '1', '0', '6', '9', '1', '5', '5', '9', '6', '3', '5', '5', '8', '6', '3', '2', '1', '1', '4', '4', '0', '4', '4', '1', '8', '5', '4', '5', '3', '9', '3', '5', '2', '1', '2', '5', '0', '1', '7', '8', '8', '7', '9', '4', '3', '3', '7', '8', '7', '6', '2', '4', '4', '8', '7', '0', '4', '9', '0', '8', '7', '8', '6', '8', '5', '4', '0', '3', '2', '0', '2', '5', '6', '0', '5', '2', '7', '8', '3', '4', '8', '4', '9', '2', '1', '5', '4', '5', '0', '1', '8', '5', '2', '7', '3', '4', '7', '4', '7', '0', '7', '7', '9', '4', '0', '8', '7', '7', '0', '4', '7', '9', '6', '3', '8', '5', '0', '5', '8', '6', '5', '0', '2', '4', '6', '8', '6', '3', '0', '6', '6', '2', '5', '8', '6', '2', '8', '0', '6', '8', '8', '4', '1', '1', '9', '2', '7', '0', '6', '5', '0', '9', '6', '8', '5', '6', '3', '4', '8', '4', '3', '8', '0', '1', '2', '6', '3', '6', '1', '6', '5', '8', '3', '5', '8', '0', '3', '7', '8', '7', '5', '6', '4', '0', '4', '4', '7', '5', '3', '7', '3']
noncomputable def geometryRow005_jensenBoundText : String := String.ofList (geometryRow005_jensenBoundNumeratorChars ++ '/' :: geometryRow005_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_jensenBound_before_field"
  err.flush

theorem geometryRow005_jensenBound_field :
    geometryRowsJson005.getObjVal? "jensen_bound" = .ok (.str geometryRow005_jensenBoundText) := by rfl

theorem geometryRow005_jensenBound_numerator_no_slash :
    geometryRow005_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow005_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow005_jensenBoundNumeratorChars = some (9864357272969725884124265418516316611613299265452413810510464726806236606861314630917655917293598701337994579557250085596386365645494104346398363605588301647354210626294194325092836986132581314843323514049986338094846788076794775173628518730959152279552000000000 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow005_jensenBoundDenominatorChars = some (3723299813013118869591813130493018183016175592103619067463883787852684240228157010691559635586321144044185453935212501788794337876244870490878685403202560527834849215450185273474707794087704796385058650246863066258628068841192706509685634843801263616583580378756404475373 : Int) := by decide +kernel

theorem geometryRow005_jensenBound_denominator_nonzero : (3723299813013118869591813130493018183016175592103619067463883787852684240228157010691559635586321144044185453935212501788794337876244870490878685403202560527834849215450185273474707794087704796385058650246863066258628068841192706509685634843801263616583580378756404475373 : Int) ≠ 0 := by decide +kernel

theorem geometryRow005_jensenBound_parse :
    parseRational geometryRow005_jensenBoundText = .ok geometryRowsTyped005.jensenBound :=
  original_rational_fraction_of_chars geometryRow005_jensenBoundNumeratorChars geometryRow005_jensenBoundDenominatorChars
    (9864357272969725884124265418516316611613299265452413810510464726806236606861314630917655917293598701337994579557250085596386365645494104346398363605588301647354210626294194325092836986132581314843323514049986338094846788076794775173628518730959152279552000000000 : Int) (3723299813013118869591813130493018183016175592103619067463883787852684240228157010691559635586321144044185453935212501788794337876244870490878685403202560527834849215450185273474707794087704796385058650246863066258628068841192706509685634843801263616583580378756404475373 : Int)
    geometryRow005_jensenBound_numerator_no_slash geometryRow005_jensenBound_numerator_parse
    geometryRow005_jensenBound_denominator_parse geometryRow005_jensenBound_denominator_nonzero

theorem geometryRow005_jensenBound_read :
    rationalField geometryRowsJson005 "jensen_bound" = .ok geometryRowsTyped005.jensenBound :=
  original_rationalField_of_string geometryRowsJson005 "jensen_bound" geometryRow005_jensenBoundText
    geometryRowsTyped005.jensenBound geometryRow005_jensenBound_field geometryRow005_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_factorMaxima_before"
  err.flush

theorem geometryRow005_factorMaxima_read :
    rationalArrayField geometryRowsJson005 "factor_maxima" = .ok geometryRowsTyped005.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_gapWeightedMeans_before"
  err.flush

theorem geometryRow005_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson005 "gap_weighted_means" = .ok geometryRowsTyped005.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow005_floorChars : List Char := ['2', '0', '9', '9', '0', '3', '8', '3', '2', '7', '2', '1', '2', '0', '8', '0', '2', '5', '1', '5', '7']
noncomputable def geometryRow005_floorText : String := String.ofList geometryRow005_floorChars

theorem geometryRow005_floor_text_read :
    geometryRowsJson005.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow005_floorText := by rfl

theorem geometryRow005_floor_chars_parse :
    SourceJson.intChars geometryRow005_floorChars = some (209903832721208025157 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_005_original_decoder_complete"
  err.flush

theorem geometryRow005_shape :
    geometryRowsTyped005.simplexId = 5 ∧
    geometryRowsTyped005.vertexIds.size = 9 ∧ geometryRowsTyped005.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped005.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped005.factorMaxima.size = 10 ∧ geometryRowsTyped005.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson006 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped006 : GeometryRow :=
  { simplexId := 6,
    vertexIds := #[139, 115, 85, 50, 47, 12, 3, 1, 0],
    physicalVolume := ((1216639703394178440610585224828336837391759109 : ℚ) / (42462796810420224000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((2253377737 : ℚ) / (2121480000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((25640261 : ℚ) / (288000000 : ℚ)), ((23671903 : ℚ) / (324000000 : ℚ)), ((496871 : ℚ) / (7200000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((8418595710542080324829779 : ℚ) / (182916478582887218400000000 : ℚ)), ((112480825758365829213362731 : ℚ) / (2377914221577533839200000000 : ℚ)), ((666605349573782544919769 : ℚ) / (6007362243985348646400000 : ℚ)), ((1340759079692396186923877081 : ℚ) / (14267485329465203035200000000 : ℚ)), ((67540407733883990483218499 : ℚ) / (750920280498168580800000000 : ℚ)), ((5397817815621677605409233 : ℚ) / (68265480045288052800000000 : ℚ)), ((884430979543273416164861 : ℚ) / (12799777508491509900000000 : ℚ)), ((35112996445075170603475499 : ℚ) / (563190210373626435600000000 : ℚ)), ((4636465465020275228478313 : ℚ) / (192803855803583824800000000 : ℚ)), ((139463069385910853776775971 : ℚ) / (7133742664732601517600000000 : ℚ))],
    jensenBound := ((2306611025472691121762156773242950653928054164137780245563558466157857286234759644171959716617480668451850890609970689207884544105783027905538292852675351598714856198270837916128525618189773709895625794265856776206992670720000000000000000000000 : ℚ) / (6195804117892418755514888398436820556213961511368445926863968809680504058299380517683244634790651042940043190788708307703633456229248263730653176303675115537045319821006583848227267592908967822281828602413376649156312585307253801686382315151377842839039 : ℚ)),
    jensenFloorQ96 := (29495534349705769081 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_simplexId_before"
  err.flush

theorem geometryRow006_simplexId_read :
    geometryRowsJson006.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped006.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_vertexIds_before"
  err.flush

theorem geometryRow006_vertexIds_read :
    geometryRowsJson006.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped006.vertexIds := by decide +kernel

noncomputable def geometryRow006_physicalVolumeNumeratorChars : List Char := ['1', '2', '1', '6', '6', '3', '9', '7', '0', '3', '3', '9', '4', '1', '7', '8', '4', '4', '0', '6', '1', '0', '5', '8', '5', '2', '2', '4', '8', '2', '8', '3', '3', '6', '8', '3', '7', '3', '9', '1', '7', '5', '9', '1', '0', '9']
noncomputable def geometryRow006_physicalVolumeDenominatorChars : List Char := ['4', '2', '4', '6', '2', '7', '9', '6', '8', '1', '0', '4', '2', '0', '2', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_physicalVolumeText : String := String.ofList (geometryRow006_physicalVolumeNumeratorChars ++ '/' :: geometryRow006_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_physicalVolume_before_field"
  err.flush

theorem geometryRow006_physicalVolume_field :
    geometryRowsJson006.getObjVal? "physical_volume" = .ok (.str geometryRow006_physicalVolumeText) := by rfl

theorem geometryRow006_physicalVolume_numerator_no_slash :
    geometryRow006_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeNumeratorChars = some (1216639703394178440610585224828336837391759109 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow006_physicalVolumeDenominatorChars = some (42462796810420224000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_physicalVolume_denominator_nonzero : (42462796810420224000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_physicalVolume_parse :
    parseRational geometryRow006_physicalVolumeText = .ok geometryRowsTyped006.physicalVolume :=
  original_rational_fraction_of_chars geometryRow006_physicalVolumeNumeratorChars geometryRow006_physicalVolumeDenominatorChars
    (1216639703394178440610585224828336837391759109 : Int) (42462796810420224000000000000000000000000000000000000000000000000 : Int)
    geometryRow006_physicalVolume_numerator_no_slash geometryRow006_physicalVolume_numerator_parse
    geometryRow006_physicalVolume_denominator_parse geometryRow006_physicalVolume_denominator_nonzero

theorem geometryRow006_physicalVolume_read :
    rationalField geometryRowsJson006 "physical_volume" = .ok geometryRowsTyped006.physicalVolume :=
  original_rationalField_of_string geometryRowsJson006 "physical_volume" geometryRow006_physicalVolumeText
    geometryRowsTyped006.physicalVolume geometryRow006_physicalVolume_field geometryRow006_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_physicalVolume_complete"
  err.flush

noncomputable def geometryRow006_meanGapNumeratorChars : List Char := ['2', '2', '5', '3', '3', '7', '7', '7', '3', '7']
noncomputable def geometryRow006_meanGapDenominatorChars : List Char := ['2', '1', '2', '1', '4', '8', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_meanGapText : String := String.ofList (geometryRow006_meanGapNumeratorChars ++ '/' :: geometryRow006_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_meanGap_before_field"
  err.flush

theorem geometryRow006_meanGap_field :
    geometryRowsJson006.getObjVal? "mean_gap" = .ok (.str geometryRow006_meanGapText) := by rfl

theorem geometryRow006_meanGap_numerator_no_slash :
    geometryRow006_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_meanGap_numerator_parse :
    SourceJson.intChars geometryRow006_meanGapNumeratorChars = some (2253377737 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_parse :
    SourceJson.intChars geometryRow006_meanGapDenominatorChars = some (2121480000000 : Int) := by decide +kernel

theorem geometryRow006_meanGap_denominator_nonzero : (2121480000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_meanGap_parse :
    parseRational geometryRow006_meanGapText = .ok geometryRowsTyped006.meanGap :=
  original_rational_fraction_of_chars geometryRow006_meanGapNumeratorChars geometryRow006_meanGapDenominatorChars
    (2253377737 : Int) (2121480000000 : Int)
    geometryRow006_meanGap_numerator_no_slash geometryRow006_meanGap_numerator_parse
    geometryRow006_meanGap_denominator_parse geometryRow006_meanGap_denominator_nonzero

theorem geometryRow006_meanGap_read :
    rationalField geometryRowsJson006 "mean_gap" = .ok geometryRowsTyped006.meanGap :=
  original_rationalField_of_string geometryRowsJson006 "mean_gap" geometryRow006_meanGapText
    geometryRowsTyped006.meanGap geometryRow006_meanGap_field geometryRow006_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_meanGap_complete"
  err.flush

noncomputable def geometryRow006_jensenBoundNumeratorChars : List Char := ['2', '3', '0', '6', '6', '1', '1', '0', '2', '5', '4', '7', '2', '6', '9', '1', '1', '2', '1', '7', '6', '2', '1', '5', '6', '7', '7', '3', '2', '4', '2', '9', '5', '0', '6', '5', '3', '9', '2', '8', '0', '5', '4', '1', '6', '4', '1', '3', '7', '7', '8', '0', '2', '4', '5', '5', '6', '3', '5', '5', '8', '4', '6', '6', '1', '5', '7', '8', '5', '7', '2', '8', '6', '2', '3', '4', '7', '5', '9', '6', '4', '4', '1', '7', '1', '9', '5', '9', '7', '1', '6', '6', '1', '7', '4', '8', '0', '6', '6', '8', '4', '5', '1', '8', '5', '0', '8', '9', '0', '6', '0', '9', '9', '7', '0', '6', '8', '9', '2', '0', '7', '8', '8', '4', '5', '4', '4', '1', '0', '5', '7', '8', '3', '0', '2', '7', '9', '0', '5', '5', '3', '8', '2', '9', '2', '8', '5', '2', '6', '7', '5', '3', '5', '1', '5', '9', '8', '7', '1', '4', '8', '5', '6', '1', '9', '8', '2', '7', '0', '8', '3', '7', '9', '1', '6', '1', '2', '8', '5', '2', '5', '6', '1', '8', '1', '8', '9', '7', '7', '3', '7', '0', '9', '8', '9', '5', '6', '2', '5', '7', '9', '4', '2', '6', '5', '8', '5', '6', '7', '7', '6', '2', '0', '6', '9', '9', '2', '6', '7', '0', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow006_jensenBoundDenominatorChars : List Char := ['6', '1', '9', '5', '8', '0', '4', '1', '1', '7', '8', '9', '2', '4', '1', '8', '7', '5', '5', '5', '1', '4', '8', '8', '8', '3', '9', '8', '4', '3', '6', '8', '2', '0', '5', '5', '6', '2', '1', '3', '9', '6', '1', '5', '1', '1', '3', '6', '8', '4', '4', '5', '9', '2', '6', '8', '6', '3', '9', '6', '8', '8', '0', '9', '6', '8', '0', '5', '0', '4', '0', '5', '8', '2', '9', '9', '3', '8', '0', '5', '1', '7', '6', '8', '3', '2', '4', '4', '6', '3', '4', '7', '9', '0', '6', '5', '1', '0', '4', '2', '9', '4', '0', '0', '4', '3', '1', '9', '0', '7', '8', '8', '7', '0', '8', '3', '0', '7', '7', '0', '3', '6', '3', '3', '4', '5', '6', '2', '2', '9', '2', '4', '8', '2', '6', '3', '7', '3', '0', '6', '5', '3', '1', '7', '6', '3', '0', '3', '6', '7', '5', '1', '1', '5', '5', '3', '7', '0', '4', '5', '3', '1', '9', '8', '2', '1', '0', '0', '6', '5', '8', '3', '8', '4', '8', '2', '2', '7', '2', '6', '7', '5', '9', '2', '9', '0', '8', '9', '6', '7', '8', '2', '2', '2', '8', '1', '8', '2', '8', '6', '0', '2', '4', '1', '3', '3', '7', '6', '6', '4', '9', '1', '5', '6', '3', '1', '2', '5', '8', '5', '3', '0', '7', '2', '5', '3', '8', '0', '1', '6', '8', '6', '3', '8', '2', '3', '1', '5', '1', '5', '1', '3', '7', '7', '8', '4', '2', '8', '3', '9', '0', '3', '9']
noncomputable def geometryRow006_jensenBoundText : String := String.ofList (geometryRow006_jensenBoundNumeratorChars ++ '/' :: geometryRow006_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_jensenBound_before_field"
  err.flush

theorem geometryRow006_jensenBound_field :
    geometryRowsJson006.getObjVal? "jensen_bound" = .ok (.str geometryRow006_jensenBoundText) := by rfl

theorem geometryRow006_jensenBound_numerator_no_slash :
    geometryRow006_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow006_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow006_jensenBoundNumeratorChars = some (2306611025472691121762156773242950653928054164137780245563558466157857286234759644171959716617480668451850890609970689207884544105783027905538292852675351598714856198270837916128525618189773709895625794265856776206992670720000000000000000000000 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow006_jensenBoundDenominatorChars = some (6195804117892418755514888398436820556213961511368445926863968809680504058299380517683244634790651042940043190788708307703633456229248263730653176303675115537045319821006583848227267592908967822281828602413376649156312585307253801686382315151377842839039 : Int) := by decide +kernel

theorem geometryRow006_jensenBound_denominator_nonzero : (6195804117892418755514888398436820556213961511368445926863968809680504058299380517683244634790651042940043190788708307703633456229248263730653176303675115537045319821006583848227267592908967822281828602413376649156312585307253801686382315151377842839039 : Int) ≠ 0 := by decide +kernel

theorem geometryRow006_jensenBound_parse :
    parseRational geometryRow006_jensenBoundText = .ok geometryRowsTyped006.jensenBound :=
  original_rational_fraction_of_chars geometryRow006_jensenBoundNumeratorChars geometryRow006_jensenBoundDenominatorChars
    (2306611025472691121762156773242950653928054164137780245563558466157857286234759644171959716617480668451850890609970689207884544105783027905538292852675351598714856198270837916128525618189773709895625794265856776206992670720000000000000000000000 : Int) (6195804117892418755514888398436820556213961511368445926863968809680504058299380517683244634790651042940043190788708307703633456229248263730653176303675115537045319821006583848227267592908967822281828602413376649156312585307253801686382315151377842839039 : Int)
    geometryRow006_jensenBound_numerator_no_slash geometryRow006_jensenBound_numerator_parse
    geometryRow006_jensenBound_denominator_parse geometryRow006_jensenBound_denominator_nonzero

theorem geometryRow006_jensenBound_read :
    rationalField geometryRowsJson006 "jensen_bound" = .ok geometryRowsTyped006.jensenBound :=
  original_rationalField_of_string geometryRowsJson006 "jensen_bound" geometryRow006_jensenBoundText
    geometryRowsTyped006.jensenBound geometryRow006_jensenBound_field geometryRow006_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_factorMaxima_before"
  err.flush

theorem geometryRow006_factorMaxima_read :
    rationalArrayField geometryRowsJson006 "factor_maxima" = .ok geometryRowsTyped006.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_gapWeightedMeans_before"
  err.flush

theorem geometryRow006_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson006 "gap_weighted_means" = .ok geometryRowsTyped006.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow006_floorChars : List Char := ['2', '9', '4', '9', '5', '5', '3', '4', '3', '4', '9', '7', '0', '5', '7', '6', '9', '0', '8', '1']
noncomputable def geometryRow006_floorText : String := String.ofList geometryRow006_floorChars

theorem geometryRow006_floor_text_read :
    geometryRowsJson006.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow006_floorText := by rfl

theorem geometryRow006_floor_chars_parse :
    SourceJson.intChars geometryRow006_floorChars = some (29495534349705769081 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_006_original_decoder_complete"
  err.flush

theorem geometryRow006_shape :
    geometryRowsTyped006.simplexId = 6 ∧
    geometryRowsTyped006.vertexIds.size = 9 ∧ geometryRowsTyped006.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped006.vertexIds[i.val]! < 140) ∧
    geometryRowsTyped006.factorMaxima.size = 10 ∧ geometryRowsTyped006.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson007 : SourceJson :=
  (SimplicesBlock000.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped007 : GeometryRow :=
  { simplexId := 7,
    vertexIds := #[139, 115, 85, 50, 47, 12, 3, 2, 0],
    physicalVolume := ((77209010995682348632603689643863583252324284217 : ℚ) / (2279177828800266240000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((3357801023 : ℚ) / (2990520000000 : ℚ)),
    factorMaxima := #[((164057 : ℚ) / (2250000 : ℚ)), ((164057 : ℚ) / (2250000 : ℚ)), ((234371 : ℚ) / (1800000 : ℚ)), ((3204371 : ℚ) / (27360000 : ℚ)), ((6609359 : ℚ) / (68000000 : ℚ)), ((25640261 : ℚ) / (288000000 : ℚ)), ((23671903 : ℚ) / (324000000 : ℚ)), ((496871 : ℚ) / (7200000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ)), ((531247 : ℚ) / (15750000 : ℚ))],
    gapWeightedMeans := #[((2005043605474385412017051 : ℚ) / (42691267557038469600000000 : ℚ)), ((8938358057331435666237713 : ℚ) / (184995492747166701600000000 : ℚ)), ((155749749553499044397617 : ℚ) / (1402071102925895001600000 : ℚ)), ((312681367370890689001162289 : ℚ) / (3329918869449000628800000000 : ℚ)), ((15750702234062492832078731 : ℚ) / (175258887865736875200000000 : ℚ)), ((1255575640303255539971177 : ℚ) / (15932626169612443200000000 : ℚ)), ((104049145773206542645297 : ℚ) / (1493683703401166550000000 : ℚ)), ((8154983541124086644839061 : ℚ) / (131444165899302656400000000 : ℚ)), ((12613776842400316734780323 : ℚ) / (554986478241500104800000000 : ℚ)), ((11037505877722666525722233 : ℚ) / (554986478241500104800000000 : ℚ))],
    jensenBound := ((1624895843464935226879785751232797560181692806270227542994878205291849335471411002333667326396470845507298767511167979576434392179696810938306053856079187811578411230799341777396772238954516390309766403339843076096000000000000000000000 : ℚ) / (3497541500113762689777385463710225176828294472106382149001591076218929513879619924145182711730217822486900774731415154696332863262102139368209046899182308491834594043083770802765373341662725994314849228055137184370644123672261278386662639669073 : ℚ)),
    jensenFloorQ96 := (36808001263346020867 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_simplexId_before"
  err.flush

theorem geometryRow007_simplexId_read :
    geometryRowsJson007.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped007.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_vertexIds_before"
  err.flush

theorem geometryRow007_vertexIds_read :
    geometryRowsJson007.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped007.vertexIds := by decide +kernel

noncomputable def geometryRow007_physicalVolumeNumeratorChars : List Char := ['7', '7', '2', '0', '9', '0', '1', '0', '9', '9', '5', '6', '8', '2', '3', '4', '8', '6', '3', '2', '6', '0', '3', '6', '8', '9', '6', '4', '3', '8', '6', '3', '5', '8', '3', '2', '5', '2', '3', '2', '4', '2', '8', '4', '2', '1', '7']
noncomputable def geometryRow007_physicalVolumeDenominatorChars : List Char := ['2', '2', '7', '9', '1', '7', '7', '8', '2', '8', '8', '0', '0', '2', '6', '6', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_physicalVolumeText : String := String.ofList (geometryRow007_physicalVolumeNumeratorChars ++ '/' :: geometryRow007_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_physicalVolume_before_field"
  err.flush

theorem geometryRow007_physicalVolume_field :
    geometryRowsJson007.getObjVal? "physical_volume" = .ok (.str geometryRow007_physicalVolumeText) := by rfl

theorem geometryRow007_physicalVolume_numerator_no_slash :
    geometryRow007_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeNumeratorChars = some (77209010995682348632603689643863583252324284217 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow007_physicalVolumeDenominatorChars = some (2279177828800266240000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_physicalVolume_denominator_nonzero : (2279177828800266240000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_physicalVolume_parse :
    parseRational geometryRow007_physicalVolumeText = .ok geometryRowsTyped007.physicalVolume :=
  original_rational_fraction_of_chars geometryRow007_physicalVolumeNumeratorChars geometryRow007_physicalVolumeDenominatorChars
    (77209010995682348632603689643863583252324284217 : Int) (2279177828800266240000000000000000000000000000000000000000000000000 : Int)
    geometryRow007_physicalVolume_numerator_no_slash geometryRow007_physicalVolume_numerator_parse
    geometryRow007_physicalVolume_denominator_parse geometryRow007_physicalVolume_denominator_nonzero

theorem geometryRow007_physicalVolume_read :
    rationalField geometryRowsJson007 "physical_volume" = .ok geometryRowsTyped007.physicalVolume :=
  original_rationalField_of_string geometryRowsJson007 "physical_volume" geometryRow007_physicalVolumeText
    geometryRowsTyped007.physicalVolume geometryRow007_physicalVolume_field geometryRow007_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_physicalVolume_complete"
  err.flush

noncomputable def geometryRow007_meanGapNumeratorChars : List Char := ['3', '3', '5', '7', '8', '0', '1', '0', '2', '3']
noncomputable def geometryRow007_meanGapDenominatorChars : List Char := ['2', '9', '9', '0', '5', '2', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_meanGapText : String := String.ofList (geometryRow007_meanGapNumeratorChars ++ '/' :: geometryRow007_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_meanGap_before_field"
  err.flush

theorem geometryRow007_meanGap_field :
    geometryRowsJson007.getObjVal? "mean_gap" = .ok (.str geometryRow007_meanGapText) := by rfl

theorem geometryRow007_meanGap_numerator_no_slash :
    geometryRow007_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_meanGap_numerator_parse :
    SourceJson.intChars geometryRow007_meanGapNumeratorChars = some (3357801023 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_parse :
    SourceJson.intChars geometryRow007_meanGapDenominatorChars = some (2990520000000 : Int) := by decide +kernel

theorem geometryRow007_meanGap_denominator_nonzero : (2990520000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_meanGap_parse :
    parseRational geometryRow007_meanGapText = .ok geometryRowsTyped007.meanGap :=
  original_rational_fraction_of_chars geometryRow007_meanGapNumeratorChars geometryRow007_meanGapDenominatorChars
    (3357801023 : Int) (2990520000000 : Int)
    geometryRow007_meanGap_numerator_no_slash geometryRow007_meanGap_numerator_parse
    geometryRow007_meanGap_denominator_parse geometryRow007_meanGap_denominator_nonzero

theorem geometryRow007_meanGap_read :
    rationalField geometryRowsJson007 "mean_gap" = .ok geometryRowsTyped007.meanGap :=
  original_rationalField_of_string geometryRowsJson007 "mean_gap" geometryRow007_meanGapText
    geometryRowsTyped007.meanGap geometryRow007_meanGap_field geometryRow007_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_meanGap_complete"
  err.flush

noncomputable def geometryRow007_jensenBoundNumeratorChars : List Char := ['1', '6', '2', '4', '8', '9', '5', '8', '4', '3', '4', '6', '4', '9', '3', '5', '2', '2', '6', '8', '7', '9', '7', '8', '5', '7', '5', '1', '2', '3', '2', '7', '9', '7', '5', '6', '0', '1', '8', '1', '6', '9', '2', '8', '0', '6', '2', '7', '0', '2', '2', '7', '5', '4', '2', '9', '9', '4', '8', '7', '8', '2', '0', '5', '2', '9', '1', '8', '4', '9', '3', '3', '5', '4', '7', '1', '4', '1', '1', '0', '0', '2', '3', '3', '3', '6', '6', '7', '3', '2', '6', '3', '9', '6', '4', '7', '0', '8', '4', '5', '5', '0', '7', '2', '9', '8', '7', '6', '7', '5', '1', '1', '1', '6', '7', '9', '7', '9', '5', '7', '6', '4', '3', '4', '3', '9', '2', '1', '7', '9', '6', '9', '6', '8', '1', '0', '9', '3', '8', '3', '0', '6', '0', '5', '3', '8', '5', '6', '0', '7', '9', '1', '8', '7', '8', '1', '1', '5', '7', '8', '4', '1', '1', '2', '3', '0', '7', '9', '9', '3', '4', '1', '7', '7', '7', '3', '9', '6', '7', '7', '2', '2', '3', '8', '9', '5', '4', '5', '1', '6', '3', '9', '0', '3', '0', '9', '7', '6', '6', '4', '0', '3', '3', '3', '9', '8', '4', '3', '0', '7', '6', '0', '9', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow007_jensenBoundDenominatorChars : List Char := ['3', '4', '9', '7', '5', '4', '1', '5', '0', '0', '1', '1', '3', '7', '6', '2', '6', '8', '9', '7', '7', '7', '3', '8', '5', '4', '6', '3', '7', '1', '0', '2', '2', '5', '1', '7', '6', '8', '2', '8', '2', '9', '4', '4', '7', '2', '1', '0', '6', '3', '8', '2', '1', '4', '9', '0', '0', '1', '5', '9', '1', '0', '7', '6', '2', '1', '8', '9', '2', '9', '5', '1', '3', '8', '7', '9', '6', '1', '9', '9', '2', '4', '1', '4', '5', '1', '8', '2', '7', '1', '1', '7', '3', '0', '2', '1', '7', '8', '2', '2', '4', '8', '6', '9', '0', '0', '7', '7', '4', '7', '3', '1', '4', '1', '5', '1', '5', '4', '6', '9', '6', '3', '3', '2', '8', '6', '3', '2', '6', '2', '1', '0', '2', '1', '3', '9', '3', '6', '8', '2', '0', '9', '0', '4', '6', '8', '9', '9', '1', '8', '2', '3', '0', '8', '4', '9', '1', '8', '3', '4', '5', '9', '4', '0', '4', '3', '0', '8', '3', '7', '7', '0', '8', '0', '2', '7', '6', '5', '3', '7', '3', '3', '4', '1', '6', '6', '2', '7', '2', '5', '9', '9', '4', '3', '1', '4', '8', '4', '9', '2', '2', '8', '0', '5', '5', '1', '3', '7', '1', '8', '4', '3', '7', '0', '6', '4', '4', '1', '2', '3', '6', '7', '2', '2', '6', '1', '2', '7', '8', '3', '8', '6', '6', '6', '2', '6', '3', '9', '6', '6', '9', '0', '7', '3']
noncomputable def geometryRow007_jensenBoundText : String := String.ofList (geometryRow007_jensenBoundNumeratorChars ++ '/' :: geometryRow007_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_jensenBound_before_field"
  err.flush

theorem geometryRow007_jensenBound_field :
    geometryRowsJson007.getObjVal? "jensen_bound" = .ok (.str geometryRow007_jensenBoundText) := by rfl

theorem geometryRow007_jensenBound_numerator_no_slash :
    geometryRow007_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow007_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow007_jensenBoundNumeratorChars = some (1624895843464935226879785751232797560181692806270227542994878205291849335471411002333667326396470845507298767511167979576434392179696810938306053856079187811578411230799341777396772238954516390309766403339843076096000000000000000000000 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow007_jensenBoundDenominatorChars = some (3497541500113762689777385463710225176828294472106382149001591076218929513879619924145182711730217822486900774731415154696332863262102139368209046899182308491834594043083770802765373341662725994314849228055137184370644123672261278386662639669073 : Int) := by decide +kernel

theorem geometryRow007_jensenBound_denominator_nonzero : (3497541500113762689777385463710225176828294472106382149001591076218929513879619924145182711730217822486900774731415154696332863262102139368209046899182308491834594043083770802765373341662725994314849228055137184370644123672261278386662639669073 : Int) ≠ 0 := by decide +kernel

theorem geometryRow007_jensenBound_parse :
    parseRational geometryRow007_jensenBoundText = .ok geometryRowsTyped007.jensenBound :=
  original_rational_fraction_of_chars geometryRow007_jensenBoundNumeratorChars geometryRow007_jensenBoundDenominatorChars
    (1624895843464935226879785751232797560181692806270227542994878205291849335471411002333667326396470845507298767511167979576434392179696810938306053856079187811578411230799341777396772238954516390309766403339843076096000000000000000000000 : Int) (3497541500113762689777385463710225176828294472106382149001591076218929513879619924145182711730217822486900774731415154696332863262102139368209046899182308491834594043083770802765373341662725994314849228055137184370644123672261278386662639669073 : Int)
    geometryRow007_jensenBound_numerator_no_slash geometryRow007_jensenBound_numerator_parse
    geometryRow007_jensenBound_denominator_parse geometryRow007_jensenBound_denominator_nonzero

theorem geometryRow007_jensenBound_read :
    rationalField geometryRowsJson007 "jensen_bound" = .ok geometryRowsTyped007.jensenBound :=
  original_rationalField_of_string geometryRowsJson007 "jensen_bound" geometryRow007_jensenBoundText
    geometryRowsTyped007.jensenBound geometryRow007_jensenBound_field geometryRow007_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_factorMaxima_before"
  err.flush

theorem geometryRow007_factorMaxima_read :
    rationalArrayField geometryRowsJson007 "factor_maxima" = .ok geometryRowsTyped007.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_gapWeightedMeans_before"
  err.flush

theorem geometryRow007_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson007 "gap_weighted_means" = .ok geometryRowsTyped007.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow007_floorChars : List Char := ['3', '6', '8', '0', '8', '0', '0', '1', '2', '6', '3', '3', '4', '6', '0', '2', '0', '8', '6', '7']
noncomputable def geometryRow007_floorText : String := String.ofList geometryRow007_floorChars

theorem geometryRow007_floor_text_read :
    geometryRowsJson007.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow007_floorText := by rfl

theorem geometryRow007_floor_chars_parse :
    SourceJson.intChars geometryRow007_floorChars = some (36808001263346020867 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_12_Row_007_original_decoder_complete"
  err.flush

theorem geometryRow007_shape :
    geometryRowsTyped007.simplexId = 7 ∧
    geometryRowsTyped007.vertexIds.size = 9 ∧ geometryRowsTyped007.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped007.vertexIds[i.val]! < 140) ∧
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

end ImbalancedChen.P2OriginalSaving19Geometry12ScalableDecoding
