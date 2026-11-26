import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19Geometry05ScalableSimplicesBlock002

/-! Local typed certificates for original cell 05, rows 16 through 23.
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

noncomputable def geometryRowsJson016 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨7, by decide +kernel⟩

noncomputable def geometryRowsTyped016 : GeometryRow :=
  { simplexId := 16,
    vertexIds := #[27, 25, 23, 11, 7, 6, 4, 2, 0],
    physicalVolume := ((1599079572209838372224823211067463628471 : ℚ) / (15736715334144000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1372066765471691 : ℚ) / (14990774400000000 : ℚ)), ((43117179629983 : ℚ) / (468461700000000 : ℚ)), ((59842450642729 : ℚ) / (499692480000000 : ℚ)), ((55847785129657 : ℚ) / (624615600000000 : ℚ)), ((8847018273853 : ℚ) / (104102600000000 : ℚ)), ((9237892149551 : ℚ) / (124923120000000 : ℚ)), ((97109687281153 : ℚ) / (2498462400000000 : ℚ)), ((254407819698751 : ℚ) / (7495387200000000 : ℚ)), ((247648142594431 : ℚ) / (7495387200000000 : ℚ)), ((4899193990567 : ℚ) / (156153900000000 : ℚ))],
    jensenBound := ((675767774471613266081173953068526038646013822127309441294177613918064685079124173342297378433646592000000000000000000000000 : ℚ) / (4526678719821909924398431687366612564620017651918410279067081012096312810775320662172548003495038766404637898826839804023451127590377691 : ℚ)),
    jensenFloorQ96 := (11827620728481054 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_simplexId_before"
  err.flush

theorem geometryRow016_simplexId_read :
    geometryRowsJson016.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped016.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_vertexIds_before"
  err.flush

theorem geometryRow016_vertexIds_read :
    geometryRowsJson016.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped016.vertexIds := by decide +kernel

noncomputable def geometryRow016_physicalVolumeNumeratorChars : List Char := ['1', '5', '9', '9', '0', '7', '9', '5', '7', '2', '2', '0', '9', '8', '3', '8', '3', '7', '2', '2', '2', '4', '8', '2', '3', '2', '1', '1', '0', '6', '7', '4', '6', '3', '6', '2', '8', '4', '7', '1']
noncomputable def geometryRow016_physicalVolumeDenominatorChars : List Char := ['1', '5', '7', '3', '6', '7', '1', '5', '3', '3', '4', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_physicalVolumeText : String := String.ofList (geometryRow016_physicalVolumeNumeratorChars ++ '/' :: geometryRow016_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_physicalVolume_before_field"
  err.flush

theorem geometryRow016_physicalVolume_field :
    geometryRowsJson016.getObjVal? "physical_volume" = .ok (.str geometryRow016_physicalVolumeText) := by rfl

theorem geometryRow016_physicalVolume_numerator_no_slash :
    geometryRow016_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeNumeratorChars = some (1599079572209838372224823211067463628471 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeDenominatorChars = some (15736715334144000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_nonzero : (15736715334144000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_physicalVolume_parse :
    parseRational geometryRow016_physicalVolumeText = .ok geometryRowsTyped016.physicalVolume :=
  original_rational_fraction_of_chars geometryRow016_physicalVolumeNumeratorChars geometryRow016_physicalVolumeDenominatorChars
    (1599079572209838372224823211067463628471 : Int) (15736715334144000000000000000000000000000000000000000000000000 : Int)
    geometryRow016_physicalVolume_numerator_no_slash geometryRow016_physicalVolume_numerator_parse
    geometryRow016_physicalVolume_denominator_parse geometryRow016_physicalVolume_denominator_nonzero

theorem geometryRow016_physicalVolume_read :
    rationalField geometryRowsJson016 "physical_volume" = .ok geometryRowsTyped016.physicalVolume :=
  original_rationalField_of_string geometryRowsJson016 "physical_volume" geometryRow016_physicalVolumeText
    geometryRowsTyped016.physicalVolume geometryRow016_physicalVolume_field geometryRow016_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_physicalVolume_complete"
  err.flush

noncomputable def geometryRow016_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow016_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_meanGapText : String := String.ofList (geometryRow016_meanGapNumeratorChars ++ '/' :: geometryRow016_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_meanGap_before_field"
  err.flush

theorem geometryRow016_meanGap_field :
    geometryRowsJson016.getObjVal? "mean_gap" = .ok (.str geometryRow016_meanGapText) := by rfl

theorem geometryRow016_meanGap_numerator_no_slash :
    geometryRow016_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_meanGap_numerator_parse :
    SourceJson.intChars geometryRow016_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_parse :
    SourceJson.intChars geometryRow016_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_meanGap_parse :
    parseRational geometryRow016_meanGapText = .ok geometryRowsTyped016.meanGap :=
  original_rational_fraction_of_chars geometryRow016_meanGapNumeratorChars geometryRow016_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow016_meanGap_numerator_no_slash geometryRow016_meanGap_numerator_parse
    geometryRow016_meanGap_denominator_parse geometryRow016_meanGap_denominator_nonzero

theorem geometryRow016_meanGap_read :
    rationalField geometryRowsJson016 "mean_gap" = .ok geometryRowsTyped016.meanGap :=
  original_rationalField_of_string geometryRowsJson016 "mean_gap" geometryRow016_meanGapText
    geometryRowsTyped016.meanGap geometryRow016_meanGap_field geometryRow016_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_meanGap_complete"
  err.flush

noncomputable def geometryRow016_jensenBoundNumeratorChars : List Char := ['6', '7', '5', '7', '6', '7', '7', '7', '4', '4', '7', '1', '6', '1', '3', '2', '6', '6', '0', '8', '1', '1', '7', '3', '9', '5', '3', '0', '6', '8', '5', '2', '6', '0', '3', '8', '6', '4', '6', '0', '1', '3', '8', '2', '2', '1', '2', '7', '3', '0', '9', '4', '4', '1', '2', '9', '4', '1', '7', '7', '6', '1', '3', '9', '1', '8', '0', '6', '4', '6', '8', '5', '0', '7', '9', '1', '2', '4', '1', '7', '3', '3', '4', '2', '2', '9', '7', '3', '7', '8', '4', '3', '3', '6', '4', '6', '5', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_jensenBoundDenominatorChars : List Char := ['4', '5', '2', '6', '6', '7', '8', '7', '1', '9', '8', '2', '1', '9', '0', '9', '9', '2', '4', '3', '9', '8', '4', '3', '1', '6', '8', '7', '3', '6', '6', '6', '1', '2', '5', '6', '4', '6', '2', '0', '0', '1', '7', '6', '5', '1', '9', '1', '8', '4', '1', '0', '2', '7', '9', '0', '6', '7', '0', '8', '1', '0', '1', '2', '0', '9', '6', '3', '1', '2', '8', '1', '0', '7', '7', '5', '3', '2', '0', '6', '6', '2', '1', '7', '2', '5', '4', '8', '0', '0', '3', '4', '9', '5', '0', '3', '8', '7', '6', '6', '4', '0', '4', '6', '3', '7', '8', '9', '8', '8', '2', '6', '8', '3', '9', '8', '0', '4', '0', '2', '3', '4', '5', '1', '1', '2', '7', '5', '9', '0', '3', '7', '7', '6', '9', '1']
noncomputable def geometryRow016_jensenBoundText : String := String.ofList (geometryRow016_jensenBoundNumeratorChars ++ '/' :: geometryRow016_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_jensenBound_before_field"
  err.flush

theorem geometryRow016_jensenBound_field :
    geometryRowsJson016.getObjVal? "jensen_bound" = .ok (.str geometryRow016_jensenBoundText) := by rfl

theorem geometryRow016_jensenBound_numerator_no_slash :
    geometryRow016_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow016_jensenBoundNumeratorChars = some (675767774471613266081173953068526038646013822127309441294177613918064685079124173342297378433646592000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow016_jensenBoundDenominatorChars = some (4526678719821909924398431687366612564620017651918410279067081012096312810775320662172548003495038766404637898826839804023451127590377691 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_nonzero : (4526678719821909924398431687366612564620017651918410279067081012096312810775320662172548003495038766404637898826839804023451127590377691 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_jensenBound_parse :
    parseRational geometryRow016_jensenBoundText = .ok geometryRowsTyped016.jensenBound :=
  original_rational_fraction_of_chars geometryRow016_jensenBoundNumeratorChars geometryRow016_jensenBoundDenominatorChars
    (675767774471613266081173953068526038646013822127309441294177613918064685079124173342297378433646592000000000000000000000000 : Int) (4526678719821909924398431687366612564620017651918410279067081012096312810775320662172548003495038766404637898826839804023451127590377691 : Int)
    geometryRow016_jensenBound_numerator_no_slash geometryRow016_jensenBound_numerator_parse
    geometryRow016_jensenBound_denominator_parse geometryRow016_jensenBound_denominator_nonzero

theorem geometryRow016_jensenBound_read :
    rationalField geometryRowsJson016 "jensen_bound" = .ok geometryRowsTyped016.jensenBound :=
  original_rationalField_of_string geometryRowsJson016 "jensen_bound" geometryRow016_jensenBoundText
    geometryRowsTyped016.jensenBound geometryRow016_jensenBound_field geometryRow016_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_factorMaxima_before"
  err.flush

theorem geometryRow016_factorMaxima_read :
    rationalArrayField geometryRowsJson016 "factor_maxima" = .ok geometryRowsTyped016.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_gapWeightedMeans_before"
  err.flush

theorem geometryRow016_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson016 "gap_weighted_means" = .ok geometryRowsTyped016.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow016_floorChars : List Char := ['1', '1', '8', '2', '7', '6', '2', '0', '7', '2', '8', '4', '8', '1', '0', '5', '4']
noncomputable def geometryRow016_floorText : String := String.ofList geometryRow016_floorChars

theorem geometryRow016_floor_text_read :
    geometryRowsJson016.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow016_floorText := by rfl

theorem geometryRow016_floor_chars_parse :
    SourceJson.intChars geometryRow016_floorChars = some (11827620728481054 : Int) := by decide +kernel

theorem geometryRow016_floor_parse :
    parseInteger geometryRow016_floorText = .ok geometryRowsTyped016.jensenFloorQ96 := by
  simp only [geometryRow016_floorText, parseInteger, String.toList_ofList, geometryRow016_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_016 :
    decodeGeometryRow geometryRowsJson016 = .ok geometryRowsTyped016 :=
  original_geometryRow_of_fields geometryRowsJson016 geometryRowsTyped016 geometryRow016_floorText
    geometryRow016_simplexId_read geometryRow016_vertexIds_read
    geometryRow016_physicalVolume_read geometryRow016_meanGap_read
    geometryRow016_factorMaxima_read geometryRow016_gapWeightedMeans_read
    geometryRow016_jensenBound_read geometryRow016_floor_text_read geometryRow016_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_016_original_decoder_complete"
  err.flush

theorem geometryRow016_shape :
    geometryRowsTyped016.simplexId = 16 ∧
    geometryRowsTyped016.vertexIds.size = 9 ∧ geometryRowsTyped016.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped016.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped016.factorMaxima.size = 10 ∧ geometryRowsTyped016.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson017 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨6, by decide +kernel⟩

noncomputable def geometryRowsTyped017 : GeometryRow :=
  { simplexId := 17,
    vertexIds := #[27, 25, 23, 11, 10, 7, 5, 3, 1],
    physicalVolume := ((67148853782161559239314044327297676081533 : ℚ) / (424000556550144000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((6890389 : ℚ) / (84000000 : ℚ)), ((4265309 : ℚ) / (84000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((78121 : ℚ) / (2000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((110490173939861 : ℚ) / (1202090400000000 : ℚ)), ((111070007547641 : ℚ) / (1202090400000000 : ℚ)), ((28821758574743 : ℚ) / (240418080000000 : ℚ)), ((13426635223381 : ℚ) / (150261300000000 : ℚ)), ((101861679501857 : ℚ) / (1202090400000000 : ℚ)), ((17837846206921 : ℚ) / (240418080000000 : ℚ)), ((23287201024699 : ℚ) / (601045200000000 : ℚ)), ((20622888705641 : ℚ) / (601045200000000 : ℚ)), ((38953290873367 : ℚ) / (1202090400000000 : ℚ)), ((37857782483027 : ℚ) / (1202090400000000 : ℚ))],
    jensenBound := ((6786424060765292033180569471624533182937944690082095061834292229080086218671898529531875509174272000000000000000000000000 : ℚ) / (31021390601599262383487804022593625288618862588005887121427703141026436716314933693798953443531182064478069929584848785158222089878973 : ℚ)),
    jensenFloorQ96 := (17332424431975888 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_simplexId_before"
  err.flush

theorem geometryRow017_simplexId_read :
    geometryRowsJson017.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped017.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_vertexIds_before"
  err.flush

theorem geometryRow017_vertexIds_read :
    geometryRowsJson017.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped017.vertexIds := by decide +kernel

noncomputable def geometryRow017_physicalVolumeNumeratorChars : List Char := ['6', '7', '1', '4', '8', '8', '5', '3', '7', '8', '2', '1', '6', '1', '5', '5', '9', '2', '3', '9', '3', '1', '4', '0', '4', '4', '3', '2', '7', '2', '9', '7', '6', '7', '6', '0', '8', '1', '5', '3', '3']
noncomputable def geometryRow017_physicalVolumeDenominatorChars : List Char := ['4', '2', '4', '0', '0', '0', '5', '5', '6', '5', '5', '0', '1', '4', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_physicalVolumeText : String := String.ofList (geometryRow017_physicalVolumeNumeratorChars ++ '/' :: geometryRow017_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_physicalVolume_before_field"
  err.flush

theorem geometryRow017_physicalVolume_field :
    geometryRowsJson017.getObjVal? "physical_volume" = .ok (.str geometryRow017_physicalVolumeText) := by rfl

theorem geometryRow017_physicalVolume_numerator_no_slash :
    geometryRow017_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeNumeratorChars = some (67148853782161559239314044327297676081533 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow017_physicalVolumeDenominatorChars = some (424000556550144000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_physicalVolume_denominator_nonzero : (424000556550144000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_physicalVolume_parse :
    parseRational geometryRow017_physicalVolumeText = .ok geometryRowsTyped017.physicalVolume :=
  original_rational_fraction_of_chars geometryRow017_physicalVolumeNumeratorChars geometryRow017_physicalVolumeDenominatorChars
    (67148853782161559239314044327297676081533 : Int) (424000556550144000000000000000000000000000000000000000000000000 : Int)
    geometryRow017_physicalVolume_numerator_no_slash geometryRow017_physicalVolume_numerator_parse
    geometryRow017_physicalVolume_denominator_parse geometryRow017_physicalVolume_denominator_nonzero

theorem geometryRow017_physicalVolume_read :
    rationalField geometryRowsJson017 "physical_volume" = .ok geometryRowsTyped017.physicalVolume :=
  original_rationalField_of_string geometryRowsJson017 "physical_volume" geometryRow017_physicalVolumeText
    geometryRowsTyped017.physicalVolume geometryRow017_physicalVolume_field geometryRow017_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_physicalVolume_complete"
  err.flush

noncomputable def geometryRow017_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow017_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_meanGapText : String := String.ofList (geometryRow017_meanGapNumeratorChars ++ '/' :: geometryRow017_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_meanGap_before_field"
  err.flush

theorem geometryRow017_meanGap_field :
    geometryRowsJson017.getObjVal? "mean_gap" = .ok (.str geometryRow017_meanGapText) := by rfl

theorem geometryRow017_meanGap_numerator_no_slash :
    geometryRow017_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_meanGap_numerator_parse :
    SourceJson.intChars geometryRow017_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_parse :
    SourceJson.intChars geometryRow017_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow017_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_meanGap_parse :
    parseRational geometryRow017_meanGapText = .ok geometryRowsTyped017.meanGap :=
  original_rational_fraction_of_chars geometryRow017_meanGapNumeratorChars geometryRow017_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow017_meanGap_numerator_no_slash geometryRow017_meanGap_numerator_parse
    geometryRow017_meanGap_denominator_parse geometryRow017_meanGap_denominator_nonzero

theorem geometryRow017_meanGap_read :
    rationalField geometryRowsJson017 "mean_gap" = .ok geometryRowsTyped017.meanGap :=
  original_rationalField_of_string geometryRowsJson017 "mean_gap" geometryRow017_meanGapText
    geometryRowsTyped017.meanGap geometryRow017_meanGap_field geometryRow017_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_meanGap_complete"
  err.flush

noncomputable def geometryRow017_jensenBoundNumeratorChars : List Char := ['6', '7', '8', '6', '4', '2', '4', '0', '6', '0', '7', '6', '5', '2', '9', '2', '0', '3', '3', '1', '8', '0', '5', '6', '9', '4', '7', '1', '6', '2', '4', '5', '3', '3', '1', '8', '2', '9', '3', '7', '9', '4', '4', '6', '9', '0', '0', '8', '2', '0', '9', '5', '0', '6', '1', '8', '3', '4', '2', '9', '2', '2', '2', '9', '0', '8', '0', '0', '8', '6', '2', '1', '8', '6', '7', '1', '8', '9', '8', '5', '2', '9', '5', '3', '1', '8', '7', '5', '5', '0', '9', '1', '7', '4', '2', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow017_jensenBoundDenominatorChars : List Char := ['3', '1', '0', '2', '1', '3', '9', '0', '6', '0', '1', '5', '9', '9', '2', '6', '2', '3', '8', '3', '4', '8', '7', '8', '0', '4', '0', '2', '2', '5', '9', '3', '6', '2', '5', '2', '8', '8', '6', '1', '8', '8', '6', '2', '5', '8', '8', '0', '0', '5', '8', '8', '7', '1', '2', '1', '4', '2', '7', '7', '0', '3', '1', '4', '1', '0', '2', '6', '4', '3', '6', '7', '1', '6', '3', '1', '4', '9', '3', '3', '6', '9', '3', '7', '9', '8', '9', '5', '3', '4', '4', '3', '5', '3', '1', '1', '8', '2', '0', '6', '4', '4', '7', '8', '0', '6', '9', '9', '2', '9', '5', '8', '4', '8', '4', '8', '7', '8', '5', '1', '5', '8', '2', '2', '2', '0', '8', '9', '8', '7', '8', '9', '7', '3']
noncomputable def geometryRow017_jensenBoundText : String := String.ofList (geometryRow017_jensenBoundNumeratorChars ++ '/' :: geometryRow017_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_jensenBound_before_field"
  err.flush

theorem geometryRow017_jensenBound_field :
    geometryRowsJson017.getObjVal? "jensen_bound" = .ok (.str geometryRow017_jensenBoundText) := by rfl

theorem geometryRow017_jensenBound_numerator_no_slash :
    geometryRow017_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow017_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow017_jensenBoundNumeratorChars = some (6786424060765292033180569471624533182937944690082095061834292229080086218671898529531875509174272000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow017_jensenBoundDenominatorChars = some (31021390601599262383487804022593625288618862588005887121427703141026436716314933693798953443531182064478069929584848785158222089878973 : Int) := by decide +kernel

theorem geometryRow017_jensenBound_denominator_nonzero : (31021390601599262383487804022593625288618862588005887121427703141026436716314933693798953443531182064478069929584848785158222089878973 : Int) ≠ 0 := by decide +kernel

theorem geometryRow017_jensenBound_parse :
    parseRational geometryRow017_jensenBoundText = .ok geometryRowsTyped017.jensenBound :=
  original_rational_fraction_of_chars geometryRow017_jensenBoundNumeratorChars geometryRow017_jensenBoundDenominatorChars
    (6786424060765292033180569471624533182937944690082095061834292229080086218671898529531875509174272000000000000000000000000 : Int) (31021390601599262383487804022593625288618862588005887121427703141026436716314933693798953443531182064478069929584848785158222089878973 : Int)
    geometryRow017_jensenBound_numerator_no_slash geometryRow017_jensenBound_numerator_parse
    geometryRow017_jensenBound_denominator_parse geometryRow017_jensenBound_denominator_nonzero

theorem geometryRow017_jensenBound_read :
    rationalField geometryRowsJson017 "jensen_bound" = .ok geometryRowsTyped017.jensenBound :=
  original_rationalField_of_string geometryRowsJson017 "jensen_bound" geometryRow017_jensenBoundText
    geometryRowsTyped017.jensenBound geometryRow017_jensenBound_field geometryRow017_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_factorMaxima_before"
  err.flush

theorem geometryRow017_factorMaxima_read :
    rationalArrayField geometryRowsJson017 "factor_maxima" = .ok geometryRowsTyped017.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_gapWeightedMeans_before"
  err.flush

theorem geometryRow017_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson017 "gap_weighted_means" = .ok geometryRowsTyped017.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow017_floorChars : List Char := ['1', '7', '3', '3', '2', '4', '2', '4', '4', '3', '1', '9', '7', '5', '8', '8', '8']
noncomputable def geometryRow017_floorText : String := String.ofList geometryRow017_floorChars

theorem geometryRow017_floor_text_read :
    geometryRowsJson017.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow017_floorText := by rfl

theorem geometryRow017_floor_chars_parse :
    SourceJson.intChars geometryRow017_floorChars = some (17332424431975888 : Int) := by decide +kernel

theorem geometryRow017_floor_parse :
    parseInteger geometryRow017_floorText = .ok geometryRowsTyped017.jensenFloorQ96 := by
  simp only [geometryRow017_floorText, parseInteger, String.toList_ofList, geometryRow017_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_017 :
    decodeGeometryRow geometryRowsJson017 = .ok geometryRowsTyped017 :=
  original_geometryRow_of_fields geometryRowsJson017 geometryRowsTyped017 geometryRow017_floorText
    geometryRow017_simplexId_read geometryRow017_vertexIds_read
    geometryRow017_physicalVolume_read geometryRow017_meanGap_read
    geometryRow017_factorMaxima_read geometryRow017_gapWeightedMeans_read
    geometryRow017_jensenBound_read geometryRow017_floor_text_read geometryRow017_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_017_original_decoder_complete"
  err.flush

theorem geometryRow017_shape :
    geometryRowsTyped017.simplexId = 17 ∧
    geometryRowsTyped017.vertexIds.size = 9 ∧ geometryRowsTyped017.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped017.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped017.factorMaxima.size = 10 ∧ geometryRowsTyped017.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson018 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨5, by decide +kernel⟩

noncomputable def geometryRowsTyped018 : GeometryRow :=
  { simplexId := 18,
    vertexIds := #[27, 25, 23, 21, 7, 5, 3, 1, 0],
    physicalVolume := ((5750527649802665708455728850602839 : ℚ) / (591518633580000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((55001824837063 : ℚ) / (601045200000000 : ℚ)), ((55291741640953 : ℚ) / (601045200000000 : ℚ)), ((28969342361483 : ℚ) / (240418080000000 : ℚ)), ((36104391825331 : ℚ) / (400696800000000 : ℚ)), ((104678472107417 : ℚ) / (1202090400000000 : ℚ)), ((17690262420181 : ℚ) / (240418080000000 : ℚ)), ((23421265587619 : ℚ) / (601045200000000 : ℚ)), ((19583451869711 : ℚ) / (601045200000000 : ℚ)), ((18847924072931 : ℚ) / (601045200000000 : ℚ)), ((18847803863891 : ℚ) / (601045200000000 : ℚ))],
    jensenBound := ((13678014456677536410574828029662345498296182287911307077179287323758992049675037918696509643161600000000000000000000000 : ℚ) / (959735524060016884257286121895755848209481816670827486790788116887738336127247176644439752013946415067686930919677714347099815681170591 : ℚ)),
    jensenFloorQ96 := (1129148525899 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_simplexId_before"
  err.flush

theorem geometryRow018_simplexId_read :
    geometryRowsJson018.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped018.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_vertexIds_before"
  err.flush

theorem geometryRow018_vertexIds_read :
    geometryRowsJson018.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped018.vertexIds := by decide +kernel

noncomputable def geometryRow018_physicalVolumeNumeratorChars : List Char := ['5', '7', '5', '0', '5', '2', '7', '6', '4', '9', '8', '0', '2', '6', '6', '5', '7', '0', '8', '4', '5', '5', '7', '2', '8', '8', '5', '0', '6', '0', '2', '8', '3', '9']
noncomputable def geometryRow018_physicalVolumeDenominatorChars : List Char := ['5', '9', '1', '5', '1', '8', '6', '3', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_physicalVolumeText : String := String.ofList (geometryRow018_physicalVolumeNumeratorChars ++ '/' :: geometryRow018_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_physicalVolume_before_field"
  err.flush

theorem geometryRow018_physicalVolume_field :
    geometryRowsJson018.getObjVal? "physical_volume" = .ok (.str geometryRow018_physicalVolumeText) := by rfl

theorem geometryRow018_physicalVolume_numerator_no_slash :
    geometryRow018_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeNumeratorChars = some (5750527649802665708455728850602839 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow018_physicalVolumeDenominatorChars = some (591518633580000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_physicalVolume_denominator_nonzero : (591518633580000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_physicalVolume_parse :
    parseRational geometryRow018_physicalVolumeText = .ok geometryRowsTyped018.physicalVolume :=
  original_rational_fraction_of_chars geometryRow018_physicalVolumeNumeratorChars geometryRow018_physicalVolumeDenominatorChars
    (5750527649802665708455728850602839 : Int) (591518633580000000000000000000000000000000000000000000000000 : Int)
    geometryRow018_physicalVolume_numerator_no_slash geometryRow018_physicalVolume_numerator_parse
    geometryRow018_physicalVolume_denominator_parse geometryRow018_physicalVolume_denominator_nonzero

theorem geometryRow018_physicalVolume_read :
    rationalField geometryRowsJson018 "physical_volume" = .ok geometryRowsTyped018.physicalVolume :=
  original_rationalField_of_string geometryRowsJson018 "physical_volume" geometryRow018_physicalVolumeText
    geometryRowsTyped018.physicalVolume geometryRow018_physicalVolume_field geometryRow018_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_physicalVolume_complete"
  err.flush

noncomputable def geometryRow018_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow018_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_meanGapText : String := String.ofList (geometryRow018_meanGapNumeratorChars ++ '/' :: geometryRow018_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_meanGap_before_field"
  err.flush

theorem geometryRow018_meanGap_field :
    geometryRowsJson018.getObjVal? "mean_gap" = .ok (.str geometryRow018_meanGapText) := by rfl

theorem geometryRow018_meanGap_numerator_no_slash :
    geometryRow018_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_meanGap_numerator_parse :
    SourceJson.intChars geometryRow018_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_parse :
    SourceJson.intChars geometryRow018_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow018_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_meanGap_parse :
    parseRational geometryRow018_meanGapText = .ok geometryRowsTyped018.meanGap :=
  original_rational_fraction_of_chars geometryRow018_meanGapNumeratorChars geometryRow018_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow018_meanGap_numerator_no_slash geometryRow018_meanGap_numerator_parse
    geometryRow018_meanGap_denominator_parse geometryRow018_meanGap_denominator_nonzero

theorem geometryRow018_meanGap_read :
    rationalField geometryRowsJson018 "mean_gap" = .ok geometryRowsTyped018.meanGap :=
  original_rationalField_of_string geometryRowsJson018 "mean_gap" geometryRow018_meanGapText
    geometryRowsTyped018.meanGap geometryRow018_meanGap_field geometryRow018_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_meanGap_complete"
  err.flush

noncomputable def geometryRow018_jensenBoundNumeratorChars : List Char := ['1', '3', '6', '7', '8', '0', '1', '4', '4', '5', '6', '6', '7', '7', '5', '3', '6', '4', '1', '0', '5', '7', '4', '8', '2', '8', '0', '2', '9', '6', '6', '2', '3', '4', '5', '4', '9', '8', '2', '9', '6', '1', '8', '2', '2', '8', '7', '9', '1', '1', '3', '0', '7', '0', '7', '7', '1', '7', '9', '2', '8', '7', '3', '2', '3', '7', '5', '8', '9', '9', '2', '0', '4', '9', '6', '7', '5', '0', '3', '7', '9', '1', '8', '6', '9', '6', '5', '0', '9', '6', '4', '3', '1', '6', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow018_jensenBoundDenominatorChars : List Char := ['9', '5', '9', '7', '3', '5', '5', '2', '4', '0', '6', '0', '0', '1', '6', '8', '8', '4', '2', '5', '7', '2', '8', '6', '1', '2', '1', '8', '9', '5', '7', '5', '5', '8', '4', '8', '2', '0', '9', '4', '8', '1', '8', '1', '6', '6', '7', '0', '8', '2', '7', '4', '8', '6', '7', '9', '0', '7', '8', '8', '1', '1', '6', '8', '8', '7', '7', '3', '8', '3', '3', '6', '1', '2', '7', '2', '4', '7', '1', '7', '6', '6', '4', '4', '4', '3', '9', '7', '5', '2', '0', '1', '3', '9', '4', '6', '4', '1', '5', '0', '6', '7', '6', '8', '6', '9', '3', '0', '9', '1', '9', '6', '7', '7', '7', '1', '4', '3', '4', '7', '0', '9', '9', '8', '1', '5', '6', '8', '1', '1', '7', '0', '5', '9', '1']
noncomputable def geometryRow018_jensenBoundText : String := String.ofList (geometryRow018_jensenBoundNumeratorChars ++ '/' :: geometryRow018_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_jensenBound_before_field"
  err.flush

theorem geometryRow018_jensenBound_field :
    geometryRowsJson018.getObjVal? "jensen_bound" = .ok (.str geometryRow018_jensenBoundText) := by rfl

theorem geometryRow018_jensenBound_numerator_no_slash :
    geometryRow018_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow018_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow018_jensenBoundNumeratorChars = some (13678014456677536410574828029662345498296182287911307077179287323758992049675037918696509643161600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow018_jensenBoundDenominatorChars = some (959735524060016884257286121895755848209481816670827486790788116887738336127247176644439752013946415067686930919677714347099815681170591 : Int) := by decide +kernel

theorem geometryRow018_jensenBound_denominator_nonzero : (959735524060016884257286121895755848209481816670827486790788116887738336127247176644439752013946415067686930919677714347099815681170591 : Int) ≠ 0 := by decide +kernel

theorem geometryRow018_jensenBound_parse :
    parseRational geometryRow018_jensenBoundText = .ok geometryRowsTyped018.jensenBound :=
  original_rational_fraction_of_chars geometryRow018_jensenBoundNumeratorChars geometryRow018_jensenBoundDenominatorChars
    (13678014456677536410574828029662345498296182287911307077179287323758992049675037918696509643161600000000000000000000000 : Int) (959735524060016884257286121895755848209481816670827486790788116887738336127247176644439752013946415067686930919677714347099815681170591 : Int)
    geometryRow018_jensenBound_numerator_no_slash geometryRow018_jensenBound_numerator_parse
    geometryRow018_jensenBound_denominator_parse geometryRow018_jensenBound_denominator_nonzero

theorem geometryRow018_jensenBound_read :
    rationalField geometryRowsJson018 "jensen_bound" = .ok geometryRowsTyped018.jensenBound :=
  original_rationalField_of_string geometryRowsJson018 "jensen_bound" geometryRow018_jensenBoundText
    geometryRowsTyped018.jensenBound geometryRow018_jensenBound_field geometryRow018_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_factorMaxima_before"
  err.flush

theorem geometryRow018_factorMaxima_read :
    rationalArrayField geometryRowsJson018 "factor_maxima" = .ok geometryRowsTyped018.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_gapWeightedMeans_before"
  err.flush

theorem geometryRow018_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson018 "gap_weighted_means" = .ok geometryRowsTyped018.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow018_floorChars : List Char := ['1', '1', '2', '9', '1', '4', '8', '5', '2', '5', '8', '9', '9']
noncomputable def geometryRow018_floorText : String := String.ofList geometryRow018_floorChars

theorem geometryRow018_floor_text_read :
    geometryRowsJson018.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow018_floorText := by rfl

theorem geometryRow018_floor_chars_parse :
    SourceJson.intChars geometryRow018_floorChars = some (1129148525899 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_018_original_decoder_complete"
  err.flush

theorem geometryRow018_shape :
    geometryRowsTyped018.simplexId = 18 ∧
    geometryRowsTyped018.vertexIds.size = 9 ∧ geometryRowsTyped018.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped018.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped018.factorMaxima.size = 10 ∧ geometryRowsTyped018.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson019 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨4, by decide +kernel⟩

noncomputable def geometryRowsTyped019 : GeometryRow :=
  { simplexId := 19,
    vertexIds := #[27, 25, 23, 21, 7, 5, 3, 2, 0],
    physicalVolume := ((5750667906147001309035201613889551 : ℚ) / (591518633580000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2484307 : ℚ) / (24000000 : ℚ)), ((2484307 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((2484347 : ℚ) / (72000000 : ℚ)), ((2484307 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((6948567648881 : ℚ) / (75130650000000 : ℚ)), ((27939228997469 : ℚ) / (300522600000000 : ℚ)), ((14504228392541 : ℚ) / (120209040000000 : ℚ)), ((54058801678999 : ℚ) / (601045200000000 : ℚ)), ((52241449994711 : ℚ) / (601045200000000 : ℚ)), ((8825573998291 : ℚ) / (120209040000000 : ℚ)), ((5610841231991 : ℚ) / (150261300000000 : ℚ)), ((3296503997951 : ℚ) / (100174200000000 : ℚ)), ((3173922710101 : ℚ) / (100174200000000 : ℚ)), ((1057965332327 : ℚ) / (33391400000000 : ℚ))],
    jensenBound := ((23327608350059500385454093601773763633972172776902375084320635728396015835573977839001600000000000000000000000 : ℚ) / (1644252751591062915253217056551121323747561125254516047596163472250381517800886728325561430052657969695548444317300226301506907 : ℚ)),
    jensenFloorQ96 := (1124038590562 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_simplexId_before"
  err.flush

theorem geometryRow019_simplexId_read :
    geometryRowsJson019.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped019.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_vertexIds_before"
  err.flush

theorem geometryRow019_vertexIds_read :
    geometryRowsJson019.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped019.vertexIds := by decide +kernel

noncomputable def geometryRow019_physicalVolumeNumeratorChars : List Char := ['5', '7', '5', '0', '6', '6', '7', '9', '0', '6', '1', '4', '7', '0', '0', '1', '3', '0', '9', '0', '3', '5', '2', '0', '1', '6', '1', '3', '8', '8', '9', '5', '5', '1']
noncomputable def geometryRow019_physicalVolumeDenominatorChars : List Char := ['5', '9', '1', '5', '1', '8', '6', '3', '3', '5', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_physicalVolumeText : String := String.ofList (geometryRow019_physicalVolumeNumeratorChars ++ '/' :: geometryRow019_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_physicalVolume_before_field"
  err.flush

theorem geometryRow019_physicalVolume_field :
    geometryRowsJson019.getObjVal? "physical_volume" = .ok (.str geometryRow019_physicalVolumeText) := by rfl

theorem geometryRow019_physicalVolume_numerator_no_slash :
    geometryRow019_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeNumeratorChars = some (5750667906147001309035201613889551 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow019_physicalVolumeDenominatorChars = some (591518633580000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_physicalVolume_denominator_nonzero : (591518633580000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_physicalVolume_parse :
    parseRational geometryRow019_physicalVolumeText = .ok geometryRowsTyped019.physicalVolume :=
  original_rational_fraction_of_chars geometryRow019_physicalVolumeNumeratorChars geometryRow019_physicalVolumeDenominatorChars
    (5750667906147001309035201613889551 : Int) (591518633580000000000000000000000000000000000000000000000000 : Int)
    geometryRow019_physicalVolume_numerator_no_slash geometryRow019_physicalVolume_numerator_parse
    geometryRow019_physicalVolume_denominator_parse geometryRow019_physicalVolume_denominator_nonzero

theorem geometryRow019_physicalVolume_read :
    rationalField geometryRowsJson019 "physical_volume" = .ok geometryRowsTyped019.physicalVolume :=
  original_rationalField_of_string geometryRowsJson019 "physical_volume" geometryRow019_physicalVolumeText
    geometryRowsTyped019.physicalVolume geometryRow019_physicalVolume_field geometryRow019_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_physicalVolume_complete"
  err.flush

noncomputable def geometryRow019_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow019_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_meanGapText : String := String.ofList (geometryRow019_meanGapNumeratorChars ++ '/' :: geometryRow019_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_meanGap_before_field"
  err.flush

theorem geometryRow019_meanGap_field :
    geometryRowsJson019.getObjVal? "mean_gap" = .ok (.str geometryRow019_meanGapText) := by rfl

theorem geometryRow019_meanGap_numerator_no_slash :
    geometryRow019_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_meanGap_numerator_parse :
    SourceJson.intChars geometryRow019_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_parse :
    SourceJson.intChars geometryRow019_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow019_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_meanGap_parse :
    parseRational geometryRow019_meanGapText = .ok geometryRowsTyped019.meanGap :=
  original_rational_fraction_of_chars geometryRow019_meanGapNumeratorChars geometryRow019_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow019_meanGap_numerator_no_slash geometryRow019_meanGap_numerator_parse
    geometryRow019_meanGap_denominator_parse geometryRow019_meanGap_denominator_nonzero

theorem geometryRow019_meanGap_read :
    rationalField geometryRowsJson019 "mean_gap" = .ok geometryRowsTyped019.meanGap :=
  original_rationalField_of_string geometryRowsJson019 "mean_gap" geometryRow019_meanGapText
    geometryRowsTyped019.meanGap geometryRow019_meanGap_field geometryRow019_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_meanGap_complete"
  err.flush

noncomputable def geometryRow019_jensenBoundNumeratorChars : List Char := ['2', '3', '3', '2', '7', '6', '0', '8', '3', '5', '0', '0', '5', '9', '5', '0', '0', '3', '8', '5', '4', '5', '4', '0', '9', '3', '6', '0', '1', '7', '7', '3', '7', '6', '3', '6', '3', '3', '9', '7', '2', '1', '7', '2', '7', '7', '6', '9', '0', '2', '3', '7', '5', '0', '8', '4', '3', '2', '0', '6', '3', '5', '7', '2', '8', '3', '9', '6', '0', '1', '5', '8', '3', '5', '5', '7', '3', '9', '7', '7', '8', '3', '9', '0', '0', '1', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow019_jensenBoundDenominatorChars : List Char := ['1', '6', '4', '4', '2', '5', '2', '7', '5', '1', '5', '9', '1', '0', '6', '2', '9', '1', '5', '2', '5', '3', '2', '1', '7', '0', '5', '6', '5', '5', '1', '1', '2', '1', '3', '2', '3', '7', '4', '7', '5', '6', '1', '1', '2', '5', '2', '5', '4', '5', '1', '6', '0', '4', '7', '5', '9', '6', '1', '6', '3', '4', '7', '2', '2', '5', '0', '3', '8', '1', '5', '1', '7', '8', '0', '0', '8', '8', '6', '7', '2', '8', '3', '2', '5', '5', '6', '1', '4', '3', '0', '0', '5', '2', '6', '5', '7', '9', '6', '9', '6', '9', '5', '5', '4', '8', '4', '4', '4', '3', '1', '7', '3', '0', '0', '2', '2', '6', '3', '0', '1', '5', '0', '6', '9', '0', '7']
noncomputable def geometryRow019_jensenBoundText : String := String.ofList (geometryRow019_jensenBoundNumeratorChars ++ '/' :: geometryRow019_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_jensenBound_before_field"
  err.flush

theorem geometryRow019_jensenBound_field :
    geometryRowsJson019.getObjVal? "jensen_bound" = .ok (.str geometryRow019_jensenBoundText) := by rfl

theorem geometryRow019_jensenBound_numerator_no_slash :
    geometryRow019_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow019_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow019_jensenBoundNumeratorChars = some (23327608350059500385454093601773763633972172776902375084320635728396015835573977839001600000000000000000000000 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow019_jensenBoundDenominatorChars = some (1644252751591062915253217056551121323747561125254516047596163472250381517800886728325561430052657969695548444317300226301506907 : Int) := by decide +kernel

theorem geometryRow019_jensenBound_denominator_nonzero : (1644252751591062915253217056551121323747561125254516047596163472250381517800886728325561430052657969695548444317300226301506907 : Int) ≠ 0 := by decide +kernel

theorem geometryRow019_jensenBound_parse :
    parseRational geometryRow019_jensenBoundText = .ok geometryRowsTyped019.jensenBound :=
  original_rational_fraction_of_chars geometryRow019_jensenBoundNumeratorChars geometryRow019_jensenBoundDenominatorChars
    (23327608350059500385454093601773763633972172776902375084320635728396015835573977839001600000000000000000000000 : Int) (1644252751591062915253217056551121323747561125254516047596163472250381517800886728325561430052657969695548444317300226301506907 : Int)
    geometryRow019_jensenBound_numerator_no_slash geometryRow019_jensenBound_numerator_parse
    geometryRow019_jensenBound_denominator_parse geometryRow019_jensenBound_denominator_nonzero

theorem geometryRow019_jensenBound_read :
    rationalField geometryRowsJson019 "jensen_bound" = .ok geometryRowsTyped019.jensenBound :=
  original_rationalField_of_string geometryRowsJson019 "jensen_bound" geometryRow019_jensenBoundText
    geometryRowsTyped019.jensenBound geometryRow019_jensenBound_field geometryRow019_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_factorMaxima_before"
  err.flush

theorem geometryRow019_factorMaxima_read :
    rationalArrayField geometryRowsJson019 "factor_maxima" = .ok geometryRowsTyped019.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_gapWeightedMeans_before"
  err.flush

theorem geometryRow019_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson019 "gap_weighted_means" = .ok geometryRowsTyped019.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow019_floorChars : List Char := ['1', '1', '2', '4', '0', '3', '8', '5', '9', '0', '5', '6', '2']
noncomputable def geometryRow019_floorText : String := String.ofList geometryRow019_floorChars

theorem geometryRow019_floor_text_read :
    geometryRowsJson019.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow019_floorText := by rfl

theorem geometryRow019_floor_chars_parse :
    SourceJson.intChars geometryRow019_floorChars = some (1124038590562 : Int) := by decide +kernel

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
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_019_original_decoder_complete"
  err.flush

theorem geometryRow019_shape :
    geometryRowsTyped019.simplexId = 19 ∧
    geometryRowsTyped019.vertexIds.size = 9 ∧ geometryRowsTyped019.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped019.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped019.factorMaxima.size = 10 ∧ geometryRowsTyped019.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson020 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨3, by decide +kernel⟩

noncomputable def geometryRowsTyped020 : GeometryRow :=
  { simplexId := 20,
    vertexIds := #[27, 25, 23, 21, 7, 5, 4, 2, 0],
    physicalVolume := ((629017646379311937777814521097987493461 : ℚ) / (25238128366080000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10824169 : ℚ) / (19584000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((2484347 : ℚ) / (72000000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((4761054092197382946311 : ℚ) / (52046518571510400000000 : ℚ)), ((149996892783541190503 : ℚ) / (1626453705359700000000 : ℚ)), ((41883618514794712121 : ℚ) / (346976790476736000000 : ℚ)), ((590530525263367612751 : ℚ) / (6505814821438800000000 : ℚ)), ((47189888929850709937 : ℚ) / (542151235119900000000 : ℚ)), ((31591691311063592543 : ℚ) / (433720988095920000000 : ℚ)), ((109795412495835104351 : ℚ) / (2891473253972800000000 : ℚ)), ((854479460650665409411 : ℚ) / (26023259285755200000000 : ℚ)), ((824793409392073551211 : ℚ) / (26023259285755200000000 : ℚ)), ((51127988184414976141 : ℚ) / (1626453705359700000000 : ℚ))],
    jensenBound := ((7885141784529403565426404201836749036443797389837986671450961047180347475838045651840461704454017717587483550665822158543603958422170387566119570158519188715423663063040000000000000000000000 : ℚ) / (104179787318943250619516000050643860045071185631873819380409429951469720555540609636550309077446527733641747142074175752174035017534372365166512970143977739024562006622063866454993593182688694319619011243 : ℚ)),
    jensenFloorQ96 := (5996607507367378 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_simplexId_before"
  err.flush

theorem geometryRow020_simplexId_read :
    geometryRowsJson020.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped020.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_vertexIds_before"
  err.flush

theorem geometryRow020_vertexIds_read :
    geometryRowsJson020.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped020.vertexIds := by decide +kernel

noncomputable def geometryRow020_physicalVolumeNumeratorChars : List Char := ['6', '2', '9', '0', '1', '7', '6', '4', '6', '3', '7', '9', '3', '1', '1', '9', '3', '7', '7', '7', '7', '8', '1', '4', '5', '2', '1', '0', '9', '7', '9', '8', '7', '4', '9', '3', '4', '6', '1']
noncomputable def geometryRow020_physicalVolumeDenominatorChars : List Char := ['2', '5', '2', '3', '8', '1', '2', '8', '3', '6', '6', '0', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_physicalVolumeText : String := String.ofList (geometryRow020_physicalVolumeNumeratorChars ++ '/' :: geometryRow020_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_physicalVolume_before_field"
  err.flush

theorem geometryRow020_physicalVolume_field :
    geometryRowsJson020.getObjVal? "physical_volume" = .ok (.str geometryRow020_physicalVolumeText) := by rfl

theorem geometryRow020_physicalVolume_numerator_no_slash :
    geometryRow020_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeNumeratorChars = some (629017646379311937777814521097987493461 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow020_physicalVolumeDenominatorChars = some (25238128366080000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_physicalVolume_denominator_nonzero : (25238128366080000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_physicalVolume_parse :
    parseRational geometryRow020_physicalVolumeText = .ok geometryRowsTyped020.physicalVolume :=
  original_rational_fraction_of_chars geometryRow020_physicalVolumeNumeratorChars geometryRow020_physicalVolumeDenominatorChars
    (629017646379311937777814521097987493461 : Int) (25238128366080000000000000000000000000000000000000000000000000 : Int)
    geometryRow020_physicalVolume_numerator_no_slash geometryRow020_physicalVolume_numerator_parse
    geometryRow020_physicalVolume_denominator_parse geometryRow020_physicalVolume_denominator_nonzero

theorem geometryRow020_physicalVolume_read :
    rationalField geometryRowsJson020 "physical_volume" = .ok geometryRowsTyped020.physicalVolume :=
  original_rationalField_of_string geometryRowsJson020 "physical_volume" geometryRow020_physicalVolumeText
    geometryRowsTyped020.physicalVolume geometryRow020_physicalVolume_field geometryRow020_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_physicalVolume_complete"
  err.flush

noncomputable def geometryRow020_meanGapNumeratorChars : List Char := ['1', '0', '8', '2', '4', '1', '6', '9']
noncomputable def geometryRow020_meanGapDenominatorChars : List Char := ['1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_meanGapText : String := String.ofList (geometryRow020_meanGapNumeratorChars ++ '/' :: geometryRow020_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_meanGap_before_field"
  err.flush

theorem geometryRow020_meanGap_field :
    geometryRowsJson020.getObjVal? "mean_gap" = .ok (.str geometryRow020_meanGapText) := by rfl

theorem geometryRow020_meanGap_numerator_no_slash :
    geometryRow020_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_meanGap_numerator_parse :
    SourceJson.intChars geometryRow020_meanGapNumeratorChars = some (10824169 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_parse :
    SourceJson.intChars geometryRow020_meanGapDenominatorChars = some (19584000000 : Int) := by decide +kernel

theorem geometryRow020_meanGap_denominator_nonzero : (19584000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_meanGap_parse :
    parseRational geometryRow020_meanGapText = .ok geometryRowsTyped020.meanGap :=
  original_rational_fraction_of_chars geometryRow020_meanGapNumeratorChars geometryRow020_meanGapDenominatorChars
    (10824169 : Int) (19584000000 : Int)
    geometryRow020_meanGap_numerator_no_slash geometryRow020_meanGap_numerator_parse
    geometryRow020_meanGap_denominator_parse geometryRow020_meanGap_denominator_nonzero

theorem geometryRow020_meanGap_read :
    rationalField geometryRowsJson020 "mean_gap" = .ok geometryRowsTyped020.meanGap :=
  original_rationalField_of_string geometryRowsJson020 "mean_gap" geometryRow020_meanGapText
    geometryRowsTyped020.meanGap geometryRow020_meanGap_field geometryRow020_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_meanGap_complete"
  err.flush

noncomputable def geometryRow020_jensenBoundNumeratorChars : List Char := ['7', '8', '8', '5', '1', '4', '1', '7', '8', '4', '5', '2', '9', '4', '0', '3', '5', '6', '5', '4', '2', '6', '4', '0', '4', '2', '0', '1', '8', '3', '6', '7', '4', '9', '0', '3', '6', '4', '4', '3', '7', '9', '7', '3', '8', '9', '8', '3', '7', '9', '8', '6', '6', '7', '1', '4', '5', '0', '9', '6', '1', '0', '4', '7', '1', '8', '0', '3', '4', '7', '4', '7', '5', '8', '3', '8', '0', '4', '5', '6', '5', '1', '8', '4', '0', '4', '6', '1', '7', '0', '4', '4', '5', '4', '0', '1', '7', '7', '1', '7', '5', '8', '7', '4', '8', '3', '5', '5', '0', '6', '6', '5', '8', '2', '2', '1', '5', '8', '5', '4', '3', '6', '0', '3', '9', '5', '8', '4', '2', '2', '1', '7', '0', '3', '8', '7', '5', '6', '6', '1', '1', '9', '5', '7', '0', '1', '5', '8', '5', '1', '9', '1', '8', '8', '7', '1', '5', '4', '2', '3', '6', '6', '3', '0', '6', '3', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow020_jensenBoundDenominatorChars : List Char := ['1', '0', '4', '1', '7', '9', '7', '8', '7', '3', '1', '8', '9', '4', '3', '2', '5', '0', '6', '1', '9', '5', '1', '6', '0', '0', '0', '0', '5', '0', '6', '4', '3', '8', '6', '0', '0', '4', '5', '0', '7', '1', '1', '8', '5', '6', '3', '1', '8', '7', '3', '8', '1', '9', '3', '8', '0', '4', '0', '9', '4', '2', '9', '9', '5', '1', '4', '6', '9', '7', '2', '0', '5', '5', '5', '5', '4', '0', '6', '0', '9', '6', '3', '6', '5', '5', '0', '3', '0', '9', '0', '7', '7', '4', '4', '6', '5', '2', '7', '7', '3', '3', '6', '4', '1', '7', '4', '7', '1', '4', '2', '0', '7', '4', '1', '7', '5', '7', '5', '2', '1', '7', '4', '0', '3', '5', '0', '1', '7', '5', '3', '4', '3', '7', '2', '3', '6', '5', '1', '6', '6', '5', '1', '2', '9', '7', '0', '1', '4', '3', '9', '7', '7', '7', '3', '9', '0', '2', '4', '5', '6', '2', '0', '0', '6', '6', '2', '2', '0', '6', '3', '8', '6', '6', '4', '5', '4', '9', '9', '3', '5', '9', '3', '1', '8', '2', '6', '8', '8', '6', '9', '4', '3', '1', '9', '6', '1', '9', '0', '1', '1', '2', '4', '3']
noncomputable def geometryRow020_jensenBoundText : String := String.ofList (geometryRow020_jensenBoundNumeratorChars ++ '/' :: geometryRow020_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_jensenBound_before_field"
  err.flush

theorem geometryRow020_jensenBound_field :
    geometryRowsJson020.getObjVal? "jensen_bound" = .ok (.str geometryRow020_jensenBoundText) := by rfl

theorem geometryRow020_jensenBound_numerator_no_slash :
    geometryRow020_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow020_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow020_jensenBoundNumeratorChars = some (7885141784529403565426404201836749036443797389837986671450961047180347475838045651840461704454017717587483550665822158543603958422170387566119570158519188715423663063040000000000000000000000 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow020_jensenBoundDenominatorChars = some (104179787318943250619516000050643860045071185631873819380409429951469720555540609636550309077446527733641747142074175752174035017534372365166512970143977739024562006622063866454993593182688694319619011243 : Int) := by decide +kernel

theorem geometryRow020_jensenBound_denominator_nonzero : (104179787318943250619516000050643860045071185631873819380409429951469720555540609636550309077446527733641747142074175752174035017534372365166512970143977739024562006622063866454993593182688694319619011243 : Int) ≠ 0 := by decide +kernel

theorem geometryRow020_jensenBound_parse :
    parseRational geometryRow020_jensenBoundText = .ok geometryRowsTyped020.jensenBound :=
  original_rational_fraction_of_chars geometryRow020_jensenBoundNumeratorChars geometryRow020_jensenBoundDenominatorChars
    (7885141784529403565426404201836749036443797389837986671450961047180347475838045651840461704454017717587483550665822158543603958422170387566119570158519188715423663063040000000000000000000000 : Int) (104179787318943250619516000050643860045071185631873819380409429951469720555540609636550309077446527733641747142074175752174035017534372365166512970143977739024562006622063866454993593182688694319619011243 : Int)
    geometryRow020_jensenBound_numerator_no_slash geometryRow020_jensenBound_numerator_parse
    geometryRow020_jensenBound_denominator_parse geometryRow020_jensenBound_denominator_nonzero

theorem geometryRow020_jensenBound_read :
    rationalField geometryRowsJson020 "jensen_bound" = .ok geometryRowsTyped020.jensenBound :=
  original_rationalField_of_string geometryRowsJson020 "jensen_bound" geometryRow020_jensenBoundText
    geometryRowsTyped020.jensenBound geometryRow020_jensenBound_field geometryRow020_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_factorMaxima_before"
  err.flush

theorem geometryRow020_factorMaxima_read :
    rationalArrayField geometryRowsJson020 "factor_maxima" = .ok geometryRowsTyped020.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_gapWeightedMeans_before"
  err.flush

theorem geometryRow020_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson020 "gap_weighted_means" = .ok geometryRowsTyped020.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow020_floorChars : List Char := ['5', '9', '9', '6', '6', '0', '7', '5', '0', '7', '3', '6', '7', '3', '7', '8']
noncomputable def geometryRow020_floorText : String := String.ofList geometryRow020_floorChars

theorem geometryRow020_floor_text_read :
    geometryRowsJson020.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow020_floorText := by rfl

theorem geometryRow020_floor_chars_parse :
    SourceJson.intChars geometryRow020_floorChars = some (5996607507367378 : Int) := by decide +kernel

theorem geometryRow020_floor_parse :
    parseInteger geometryRow020_floorText = .ok geometryRowsTyped020.jensenFloorQ96 := by
  simp only [geometryRow020_floorText, parseInteger, String.toList_ofList, geometryRow020_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_020 :
    decodeGeometryRow geometryRowsJson020 = .ok geometryRowsTyped020 :=
  original_geometryRow_of_fields geometryRowsJson020 geometryRowsTyped020 geometryRow020_floorText
    geometryRow020_simplexId_read geometryRow020_vertexIds_read
    geometryRow020_physicalVolume_read geometryRow020_meanGap_read
    geometryRow020_factorMaxima_read geometryRow020_gapWeightedMeans_read
    geometryRow020_jensenBound_read geometryRow020_floor_text_read geometryRow020_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_020_original_decoder_complete"
  err.flush

theorem geometryRow020_shape :
    geometryRowsTyped020.simplexId = 20 ∧
    geometryRowsTyped020.vertexIds.size = 9 ∧ geometryRowsTyped020.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped020.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped020.factorMaxima.size = 10 ∧ geometryRowsTyped020.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson021 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨2, by decide +kernel⟩

noncomputable def geometryRowsTyped021 : GeometryRow :=
  { simplexId := 21,
    vertexIds := #[27, 25, 23, 21, 7, 6, 4, 2, 0],
    physicalVolume := ((44920658179687477416730696944695159741 : ℚ) / (702531934560000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328009 : ℚ) / (1152000000 : ℚ)),
    factorMaxima := #[((2484299 : ℚ) / (24000000 : ℚ)), ((2484299 : ℚ) / (24000000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((953101 : ℚ) / (26500000 : ℚ)), ((2484299 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1370390547047531 : ℚ) / (14990774400000000 : ℚ)), ((10766199451057 : ℚ) / (117115425000000 : ℚ)), ((60344316785017 : ℚ) / (499692480000000 : ℚ)), ((169495195856891 : ℚ) / (1873846800000000 : ℚ)), ((13575458240287 : ℚ) / (156153900000000 : ℚ)), ((9112425613979 : ℚ) / (124923120000000 : ℚ)), ((31580041573491 : ℚ) / (832820800000000 : ℚ)), ((247299132016711 : ℚ) / (7495387200000000 : ℚ)), ((240538955219911 : ℚ) / (7495387200000000 : ℚ)), ((3670030340779 : ℚ) / (117115425000000 : ℚ))],
    jensenBound := ((387778655461535082835717862103713992705618833428534916691176580766159815952428839223278530886239846400000000000000000000000 : ℚ) / (3900007676687678658117860802643511386514139460549705498413142093618942714233457399885954079518445976389135791425787853183420734839134261 : ℚ)),
    jensenFloorQ96 := (7877674323083078 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_simplexId_before"
  err.flush

theorem geometryRow021_simplexId_read :
    geometryRowsJson021.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped021.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_vertexIds_before"
  err.flush

theorem geometryRow021_vertexIds_read :
    geometryRowsJson021.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped021.vertexIds := by decide +kernel

noncomputable def geometryRow021_physicalVolumeNumeratorChars : List Char := ['4', '4', '9', '2', '0', '6', '5', '8', '1', '7', '9', '6', '8', '7', '4', '7', '7', '4', '1', '6', '7', '3', '0', '6', '9', '6', '9', '4', '4', '6', '9', '5', '1', '5', '9', '7', '4', '1']
noncomputable def geometryRow021_physicalVolumeDenominatorChars : List Char := ['7', '0', '2', '5', '3', '1', '9', '3', '4', '5', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_physicalVolumeText : String := String.ofList (geometryRow021_physicalVolumeNumeratorChars ++ '/' :: geometryRow021_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_physicalVolume_before_field"
  err.flush

theorem geometryRow021_physicalVolume_field :
    geometryRowsJson021.getObjVal? "physical_volume" = .ok (.str geometryRow021_physicalVolumeText) := by rfl

theorem geometryRow021_physicalVolume_numerator_no_slash :
    geometryRow021_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeNumeratorChars = some (44920658179687477416730696944695159741 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow021_physicalVolumeDenominatorChars = some (702531934560000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_physicalVolume_denominator_nonzero : (702531934560000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_physicalVolume_parse :
    parseRational geometryRow021_physicalVolumeText = .ok geometryRowsTyped021.physicalVolume :=
  original_rational_fraction_of_chars geometryRow021_physicalVolumeNumeratorChars geometryRow021_physicalVolumeDenominatorChars
    (44920658179687477416730696944695159741 : Int) (702531934560000000000000000000000000000000000000000000000000 : Int)
    geometryRow021_physicalVolume_numerator_no_slash geometryRow021_physicalVolume_numerator_parse
    geometryRow021_physicalVolume_denominator_parse geometryRow021_physicalVolume_denominator_nonzero

theorem geometryRow021_physicalVolume_read :
    rationalField geometryRowsJson021 "physical_volume" = .ok geometryRowsTyped021.physicalVolume :=
  original_rationalField_of_string geometryRowsJson021 "physical_volume" geometryRow021_physicalVolumeText
    geometryRowsTyped021.physicalVolume geometryRow021_physicalVolume_field geometryRow021_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_physicalVolume_complete"
  err.flush

noncomputable def geometryRow021_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '9']
noncomputable def geometryRow021_meanGapDenominatorChars : List Char := ['1', '1', '5', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_meanGapText : String := String.ofList (geometryRow021_meanGapNumeratorChars ++ '/' :: geometryRow021_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_meanGap_before_field"
  err.flush

theorem geometryRow021_meanGap_field :
    geometryRowsJson021.getObjVal? "mean_gap" = .ok (.str geometryRow021_meanGapText) := by rfl

theorem geometryRow021_meanGap_numerator_no_slash :
    geometryRow021_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_meanGap_numerator_parse :
    SourceJson.intChars geometryRow021_meanGapNumeratorChars = some (328009 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_parse :
    SourceJson.intChars geometryRow021_meanGapDenominatorChars = some (1152000000 : Int) := by decide +kernel

theorem geometryRow021_meanGap_denominator_nonzero : (1152000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_meanGap_parse :
    parseRational geometryRow021_meanGapText = .ok geometryRowsTyped021.meanGap :=
  original_rational_fraction_of_chars geometryRow021_meanGapNumeratorChars geometryRow021_meanGapDenominatorChars
    (328009 : Int) (1152000000 : Int)
    geometryRow021_meanGap_numerator_no_slash geometryRow021_meanGap_numerator_parse
    geometryRow021_meanGap_denominator_parse geometryRow021_meanGap_denominator_nonzero

theorem geometryRow021_meanGap_read :
    rationalField geometryRowsJson021 "mean_gap" = .ok geometryRowsTyped021.meanGap :=
  original_rationalField_of_string geometryRowsJson021 "mean_gap" geometryRow021_meanGapText
    geometryRowsTyped021.meanGap geometryRow021_meanGap_field geometryRow021_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_meanGap_complete"
  err.flush

noncomputable def geometryRow021_jensenBoundNumeratorChars : List Char := ['3', '8', '7', '7', '7', '8', '6', '5', '5', '4', '6', '1', '5', '3', '5', '0', '8', '2', '8', '3', '5', '7', '1', '7', '8', '6', '2', '1', '0', '3', '7', '1', '3', '9', '9', '2', '7', '0', '5', '6', '1', '8', '8', '3', '3', '4', '2', '8', '5', '3', '4', '9', '1', '6', '6', '9', '1', '1', '7', '6', '5', '8', '0', '7', '6', '6', '1', '5', '9', '8', '1', '5', '9', '5', '2', '4', '2', '8', '8', '3', '9', '2', '2', '3', '2', '7', '8', '5', '3', '0', '8', '8', '6', '2', '3', '9', '8', '4', '6', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow021_jensenBoundDenominatorChars : List Char := ['3', '9', '0', '0', '0', '0', '7', '6', '7', '6', '6', '8', '7', '6', '7', '8', '6', '5', '8', '1', '1', '7', '8', '6', '0', '8', '0', '2', '6', '4', '3', '5', '1', '1', '3', '8', '6', '5', '1', '4', '1', '3', '9', '4', '6', '0', '5', '4', '9', '7', '0', '5', '4', '9', '8', '4', '1', '3', '1', '4', '2', '0', '9', '3', '6', '1', '8', '9', '4', '2', '7', '1', '4', '2', '3', '3', '4', '5', '7', '3', '9', '9', '8', '8', '5', '9', '5', '4', '0', '7', '9', '5', '1', '8', '4', '4', '5', '9', '7', '6', '3', '8', '9', '1', '3', '5', '7', '9', '1', '4', '2', '5', '7', '8', '7', '8', '5', '3', '1', '8', '3', '4', '2', '0', '7', '3', '4', '8', '3', '9', '1', '3', '4', '2', '6', '1']
noncomputable def geometryRow021_jensenBoundText : String := String.ofList (geometryRow021_jensenBoundNumeratorChars ++ '/' :: geometryRow021_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_jensenBound_before_field"
  err.flush

theorem geometryRow021_jensenBound_field :
    geometryRowsJson021.getObjVal? "jensen_bound" = .ok (.str geometryRow021_jensenBoundText) := by rfl

theorem geometryRow021_jensenBound_numerator_no_slash :
    geometryRow021_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow021_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow021_jensenBoundNumeratorChars = some (387778655461535082835717862103713992705618833428534916691176580766159815952428839223278530886239846400000000000000000000000 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow021_jensenBoundDenominatorChars = some (3900007676687678658117860802643511386514139460549705498413142093618942714233457399885954079518445976389135791425787853183420734839134261 : Int) := by decide +kernel

theorem geometryRow021_jensenBound_denominator_nonzero : (3900007676687678658117860802643511386514139460549705498413142093618942714233457399885954079518445976389135791425787853183420734839134261 : Int) ≠ 0 := by decide +kernel

theorem geometryRow021_jensenBound_parse :
    parseRational geometryRow021_jensenBoundText = .ok geometryRowsTyped021.jensenBound :=
  original_rational_fraction_of_chars geometryRow021_jensenBoundNumeratorChars geometryRow021_jensenBoundDenominatorChars
    (387778655461535082835717862103713992705618833428534916691176580766159815952428839223278530886239846400000000000000000000000 : Int) (3900007676687678658117860802643511386514139460549705498413142093618942714233457399885954079518445976389135791425787853183420734839134261 : Int)
    geometryRow021_jensenBound_numerator_no_slash geometryRow021_jensenBound_numerator_parse
    geometryRow021_jensenBound_denominator_parse geometryRow021_jensenBound_denominator_nonzero

theorem geometryRow021_jensenBound_read :
    rationalField geometryRowsJson021 "jensen_bound" = .ok geometryRowsTyped021.jensenBound :=
  original_rationalField_of_string geometryRowsJson021 "jensen_bound" geometryRow021_jensenBoundText
    geometryRowsTyped021.jensenBound geometryRow021_jensenBound_field geometryRow021_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_factorMaxima_before"
  err.flush

theorem geometryRow021_factorMaxima_read :
    rationalArrayField geometryRowsJson021 "factor_maxima" = .ok geometryRowsTyped021.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_gapWeightedMeans_before"
  err.flush

theorem geometryRow021_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson021 "gap_weighted_means" = .ok geometryRowsTyped021.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow021_floorChars : List Char := ['7', '8', '7', '7', '6', '7', '4', '3', '2', '3', '0', '8', '3', '0', '7', '8']
noncomputable def geometryRow021_floorText : String := String.ofList geometryRow021_floorChars

theorem geometryRow021_floor_text_read :
    geometryRowsJson021.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow021_floorText := by rfl

theorem geometryRow021_floor_chars_parse :
    SourceJson.intChars geometryRow021_floorChars = some (7877674323083078 : Int) := by decide +kernel

theorem geometryRow021_floor_parse :
    parseInteger geometryRow021_floorText = .ok geometryRowsTyped021.jensenFloorQ96 := by
  simp only [geometryRow021_floorText, parseInteger, String.toList_ofList, geometryRow021_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_021 :
    decodeGeometryRow geometryRowsJson021 = .ok geometryRowsTyped021 :=
  original_geometryRow_of_fields geometryRowsJson021 geometryRowsTyped021 geometryRow021_floorText
    geometryRow021_simplexId_read geometryRow021_vertexIds_read
    geometryRow021_physicalVolume_read geometryRow021_meanGap_read
    geometryRow021_factorMaxima_read geometryRow021_gapWeightedMeans_read
    geometryRow021_jensenBound_read geometryRow021_floor_text_read geometryRow021_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_021_original_decoder_complete"
  err.flush

theorem geometryRow021_shape :
    geometryRowsTyped021.simplexId = 21 ∧
    geometryRowsTyped021.vertexIds.size = 9 ∧ geometryRowsTyped021.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped021.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped021.factorMaxima.size = 10 ∧ geometryRowsTyped021.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson022 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨1, by decide +kernel⟩

noncomputable def geometryRowsTyped022 : GeometryRow :=
  { simplexId := 22,
    vertexIds := #[27, 25, 23, 21, 19, 7, 5, 1, 0],
    physicalVolume := ((117798170415527293332784072234943 : ℚ) / (17663403641625000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((328001 : ℚ) / (1224000000 : ℚ)),
    factorMaxima := #[((2999973 : ℚ) / (30500000 : ℚ)), ((2999973 : ℚ) / (30500000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))],
    gapWeightedMeans := #[((580207668719341 : ℚ) / (6461235900000000 : ℚ)), ((1166648548722317 : ℚ) / (12922471800000000 : ℚ)), ((78624394227991 : ℚ) / (646123590000000 : ℚ)), ((1187127001183091 : ℚ) / (12922471800000000 : ℚ)), ((1144299050327779 : ℚ) / (12922471800000000 : ℚ)), ((23316242630557 : ℚ) / (323061795000000 : ℚ)), ((503692357233991 : ℚ) / (12922471800000000 : ℚ)), ((46380496961761 : ℚ) / (1435830200000000 : ℚ)), ((132618578460653 : ℚ) / (4307490600000000 : ℚ)), ((132617716962533 : ℚ) / (4307490600000000 : ℚ))],
    jensenBound := ((59194785646059582733563418364262232241353408276272975541580503259707428531601717407127473353927092992000000000000000000000000 : ℚ) / (5723970843903956617005717427603193195827150915014867773464522240570756409966968166820888595586002243738521623574695930424439398938398910308549 : ℚ)),
    jensenFloorQ96 := (819342764849 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_simplexId_before"
  err.flush

theorem geometryRow022_simplexId_read :
    geometryRowsJson022.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped022.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_vertexIds_before"
  err.flush

theorem geometryRow022_vertexIds_read :
    geometryRowsJson022.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped022.vertexIds := by decide +kernel

noncomputable def geometryRow022_physicalVolumeNumeratorChars : List Char := ['1', '1', '7', '7', '9', '8', '1', '7', '0', '4', '1', '5', '5', '2', '7', '2', '9', '3', '3', '3', '2', '7', '8', '4', '0', '7', '2', '2', '3', '4', '9', '4', '3']
noncomputable def geometryRow022_physicalVolumeDenominatorChars : List Char := ['1', '7', '6', '6', '3', '4', '0', '3', '6', '4', '1', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_physicalVolumeText : String := String.ofList (geometryRow022_physicalVolumeNumeratorChars ++ '/' :: geometryRow022_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_physicalVolume_before_field"
  err.flush

theorem geometryRow022_physicalVolume_field :
    geometryRowsJson022.getObjVal? "physical_volume" = .ok (.str geometryRow022_physicalVolumeText) := by rfl

theorem geometryRow022_physicalVolume_numerator_no_slash :
    geometryRow022_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeNumeratorChars = some (117798170415527293332784072234943 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow022_physicalVolumeDenominatorChars = some (17663403641625000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_physicalVolume_denominator_nonzero : (17663403641625000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_physicalVolume_parse :
    parseRational geometryRow022_physicalVolumeText = .ok geometryRowsTyped022.physicalVolume :=
  original_rational_fraction_of_chars geometryRow022_physicalVolumeNumeratorChars geometryRow022_physicalVolumeDenominatorChars
    (117798170415527293332784072234943 : Int) (17663403641625000000000000000000000000000000000000000000000 : Int)
    geometryRow022_physicalVolume_numerator_no_slash geometryRow022_physicalVolume_numerator_parse
    geometryRow022_physicalVolume_denominator_parse geometryRow022_physicalVolume_denominator_nonzero

theorem geometryRow022_physicalVolume_read :
    rationalField geometryRowsJson022 "physical_volume" = .ok geometryRowsTyped022.physicalVolume :=
  original_rationalField_of_string geometryRowsJson022 "physical_volume" geometryRow022_physicalVolumeText
    geometryRowsTyped022.physicalVolume geometryRow022_physicalVolume_field geometryRow022_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_physicalVolume_complete"
  err.flush

noncomputable def geometryRow022_meanGapNumeratorChars : List Char := ['3', '2', '8', '0', '0', '1']
noncomputable def geometryRow022_meanGapDenominatorChars : List Char := ['1', '2', '2', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_meanGapText : String := String.ofList (geometryRow022_meanGapNumeratorChars ++ '/' :: geometryRow022_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_meanGap_before_field"
  err.flush

theorem geometryRow022_meanGap_field :
    geometryRowsJson022.getObjVal? "mean_gap" = .ok (.str geometryRow022_meanGapText) := by rfl

theorem geometryRow022_meanGap_numerator_no_slash :
    geometryRow022_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_meanGap_numerator_parse :
    SourceJson.intChars geometryRow022_meanGapNumeratorChars = some (328001 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_parse :
    SourceJson.intChars geometryRow022_meanGapDenominatorChars = some (1224000000 : Int) := by decide +kernel

theorem geometryRow022_meanGap_denominator_nonzero : (1224000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_meanGap_parse :
    parseRational geometryRow022_meanGapText = .ok geometryRowsTyped022.meanGap :=
  original_rational_fraction_of_chars geometryRow022_meanGapNumeratorChars geometryRow022_meanGapDenominatorChars
    (328001 : Int) (1224000000 : Int)
    geometryRow022_meanGap_numerator_no_slash geometryRow022_meanGap_numerator_parse
    geometryRow022_meanGap_denominator_parse geometryRow022_meanGap_denominator_nonzero

theorem geometryRow022_meanGap_read :
    rationalField geometryRowsJson022 "mean_gap" = .ok geometryRowsTyped022.meanGap :=
  original_rationalField_of_string geometryRowsJson022 "mean_gap" geometryRow022_meanGapText
    geometryRowsTyped022.meanGap geometryRow022_meanGap_field geometryRow022_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_meanGap_complete"
  err.flush

noncomputable def geometryRow022_jensenBoundNumeratorChars : List Char := ['5', '9', '1', '9', '4', '7', '8', '5', '6', '4', '6', '0', '5', '9', '5', '8', '2', '7', '3', '3', '5', '6', '3', '4', '1', '8', '3', '6', '4', '2', '6', '2', '2', '3', '2', '2', '4', '1', '3', '5', '3', '4', '0', '8', '2', '7', '6', '2', '7', '2', '9', '7', '5', '5', '4', '1', '5', '8', '0', '5', '0', '3', '2', '5', '9', '7', '0', '7', '4', '2', '8', '5', '3', '1', '6', '0', '1', '7', '1', '7', '4', '0', '7', '1', '2', '7', '4', '7', '3', '3', '5', '3', '9', '2', '7', '0', '9', '2', '9', '9', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow022_jensenBoundDenominatorChars : List Char := ['5', '7', '2', '3', '9', '7', '0', '8', '4', '3', '9', '0', '3', '9', '5', '6', '6', '1', '7', '0', '0', '5', '7', '1', '7', '4', '2', '7', '6', '0', '3', '1', '9', '3', '1', '9', '5', '8', '2', '7', '1', '5', '0', '9', '1', '5', '0', '1', '4', '8', '6', '7', '7', '7', '3', '4', '6', '4', '5', '2', '2', '2', '4', '0', '5', '7', '0', '7', '5', '6', '4', '0', '9', '9', '6', '6', '9', '6', '8', '1', '6', '6', '8', '2', '0', '8', '8', '8', '5', '9', '5', '5', '8', '6', '0', '0', '2', '2', '4', '3', '7', '3', '8', '5', '2', '1', '6', '2', '3', '5', '7', '4', '6', '9', '5', '9', '3', '0', '4', '2', '4', '4', '3', '9', '3', '9', '8', '9', '3', '8', '3', '9', '8', '9', '1', '0', '3', '0', '8', '5', '4', '9']
noncomputable def geometryRow022_jensenBoundText : String := String.ofList (geometryRow022_jensenBoundNumeratorChars ++ '/' :: geometryRow022_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_jensenBound_before_field"
  err.flush

theorem geometryRow022_jensenBound_field :
    geometryRowsJson022.getObjVal? "jensen_bound" = .ok (.str geometryRow022_jensenBoundText) := by rfl

theorem geometryRow022_jensenBound_numerator_no_slash :
    geometryRow022_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow022_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow022_jensenBoundNumeratorChars = some (59194785646059582733563418364262232241353408276272975541580503259707428531601717407127473353927092992000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow022_jensenBoundDenominatorChars = some (5723970843903956617005717427603193195827150915014867773464522240570756409966968166820888595586002243738521623574695930424439398938398910308549 : Int) := by decide +kernel

theorem geometryRow022_jensenBound_denominator_nonzero : (5723970843903956617005717427603193195827150915014867773464522240570756409966968166820888595586002243738521623574695930424439398938398910308549 : Int) ≠ 0 := by decide +kernel

theorem geometryRow022_jensenBound_parse :
    parseRational geometryRow022_jensenBoundText = .ok geometryRowsTyped022.jensenBound :=
  original_rational_fraction_of_chars geometryRow022_jensenBoundNumeratorChars geometryRow022_jensenBoundDenominatorChars
    (59194785646059582733563418364262232241353408276272975541580503259707428531601717407127473353927092992000000000000000000000000 : Int) (5723970843903956617005717427603193195827150915014867773464522240570756409966968166820888595586002243738521623574695930424439398938398910308549 : Int)
    geometryRow022_jensenBound_numerator_no_slash geometryRow022_jensenBound_numerator_parse
    geometryRow022_jensenBound_denominator_parse geometryRow022_jensenBound_denominator_nonzero

theorem geometryRow022_jensenBound_read :
    rationalField geometryRowsJson022 "jensen_bound" = .ok geometryRowsTyped022.jensenBound :=
  original_rationalField_of_string geometryRowsJson022 "jensen_bound" geometryRow022_jensenBoundText
    geometryRowsTyped022.jensenBound geometryRow022_jensenBound_field geometryRow022_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_factorMaxima_before"
  err.flush

theorem geometryRow022_factorMaxima_read :
    rationalArrayField geometryRowsJson022 "factor_maxima" = .ok geometryRowsTyped022.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_gapWeightedMeans_before"
  err.flush

theorem geometryRow022_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson022 "gap_weighted_means" = .ok geometryRowsTyped022.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow022_floorChars : List Char := ['8', '1', '9', '3', '4', '2', '7', '6', '4', '8', '4', '9']
noncomputable def geometryRow022_floorText : String := String.ofList geometryRow022_floorChars

theorem geometryRow022_floor_text_read :
    geometryRowsJson022.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow022_floorText := by rfl

theorem geometryRow022_floor_chars_parse :
    SourceJson.intChars geometryRow022_floorChars = some (819342764849 : Int) := by decide +kernel

theorem geometryRow022_floor_parse :
    parseInteger geometryRow022_floorText = .ok geometryRowsTyped022.jensenFloorQ96 := by
  simp only [geometryRow022_floorText, parseInteger, String.toList_ofList, geometryRow022_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_022 :
    decodeGeometryRow geometryRowsJson022 = .ok geometryRowsTyped022 :=
  original_geometryRow_of_fields geometryRowsJson022 geometryRowsTyped022 geometryRow022_floorText
    geometryRow022_simplexId_read geometryRow022_vertexIds_read
    geometryRow022_physicalVolume_read geometryRow022_meanGap_read
    geometryRow022_factorMaxima_read geometryRow022_gapWeightedMeans_read
    geometryRow022_jensenBound_read geometryRow022_floor_text_read geometryRow022_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_022_original_decoder_complete"
  err.flush

theorem geometryRow022_shape :
    geometryRowsTyped022.simplexId = 22 ∧
    geometryRowsTyped022.vertexIds.size = 9 ∧ geometryRowsTyped022.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped022.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped022.factorMaxima.size = 10 ∧ geometryRowsTyped022.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJson023 : SourceJson :=
  (SimplicesBlock002.blockPush []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped023 : GeometryRow :=
  { simplexId := 23,
    vertexIds := #[27, 25, 23, 21, 19, 7, 5, 4, 0],
    physicalVolume := ((12884960340582387674918180808694745573 : ℚ) / (753638555376000000000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((10824169 : ℚ) / (19584000000 : ℚ)),
    factorMaxima := #[((2999973 : ℚ) / (30500000 : ℚ)), ((2999973 : ℚ) / (30500000 : ℚ)), ((1171847 : ℚ) / (9000000 : ℚ)), ((18327881 : ℚ) / (180000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2296799 : ℚ) / (28000000 : ℚ)), ((4265333 : ℚ) / (84000000 : ℚ)), ((221869 : ℚ) / (6100000 : ℚ)), ((2171863 : ℚ) / (64000000 : ℚ)), ((999991 : ℚ) / (30500000 : ℚ))],
    gapWeightedMeans := #[((200893835839950579651173 : ℚ) / (2238000298574947200000000 : ℚ)), ((25320529293201973886491 : ℚ) / (279750037321868400000000 : ℚ)), ((5456279123531893416751 : ℚ) / (44760005971498944000000 : ℚ)), ((51771070205403216364211 : ℚ) / (559500074643736800000000 : ℚ)), ((49522836168065612053489 : ℚ) / (559500074643736800000000 : ℚ)), ((7993039384401879652871 : ℚ) / (111900014928747360000000 : ℚ)), ((42502539909641059953617 : ℚ) / (1119000149287473600000000 : ℚ)), ((12143061200381214212071 : ℚ) / (373000049762491200000000 : ℚ)), ((11609153438808798565711 : ℚ) / (373000049762491200000000 : ℚ)), ((2878122848621224089859 : ℚ) / (93250012440622800000000 : ℚ))],
    jensenBound := ((48969778693798720148646164590891721349695453612326030584275951007408871106819311220500533724044473500083847007583312916712628040956798213498146513899138554075164981380528154461556912947200000000000000000000000 : ℚ) / (891663184544390277301986401391905529736989771350789236771489971993382117104860790405250967422262305350806377492452946607125938328441805934380358812177597996441168469998021305080477711039206888814856598272279795672418362781 : ℚ)),
    jensenFloorQ96 := (4351178395486052 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_simplexId_before"
  err.flush

theorem geometryRow023_simplexId_read :
    geometryRowsJson023.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped023.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_vertexIds_before"
  err.flush

theorem geometryRow023_vertexIds_read :
    geometryRowsJson023.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped023.vertexIds := by decide +kernel

noncomputable def geometryRow023_physicalVolumeNumeratorChars : List Char := ['1', '2', '8', '8', '4', '9', '6', '0', '3', '4', '0', '5', '8', '2', '3', '8', '7', '6', '7', '4', '9', '1', '8', '1', '8', '0', '8', '0', '8', '6', '9', '4', '7', '4', '5', '5', '7', '3']
noncomputable def geometryRow023_physicalVolumeDenominatorChars : List Char := ['7', '5', '3', '6', '3', '8', '5', '5', '5', '3', '7', '6', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_physicalVolumeText : String := String.ofList (geometryRow023_physicalVolumeNumeratorChars ++ '/' :: geometryRow023_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_physicalVolume_before_field"
  err.flush

theorem geometryRow023_physicalVolume_field :
    geometryRowsJson023.getObjVal? "physical_volume" = .ok (.str geometryRow023_physicalVolumeText) := by rfl

theorem geometryRow023_physicalVolume_numerator_no_slash :
    geometryRow023_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeNumeratorChars = some (12884960340582387674918180808694745573 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow023_physicalVolumeDenominatorChars = some (753638555376000000000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_physicalVolume_denominator_nonzero : (753638555376000000000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_physicalVolume_parse :
    parseRational geometryRow023_physicalVolumeText = .ok geometryRowsTyped023.physicalVolume :=
  original_rational_fraction_of_chars geometryRow023_physicalVolumeNumeratorChars geometryRow023_physicalVolumeDenominatorChars
    (12884960340582387674918180808694745573 : Int) (753638555376000000000000000000000000000000000000000000000000 : Int)
    geometryRow023_physicalVolume_numerator_no_slash geometryRow023_physicalVolume_numerator_parse
    geometryRow023_physicalVolume_denominator_parse geometryRow023_physicalVolume_denominator_nonzero

theorem geometryRow023_physicalVolume_read :
    rationalField geometryRowsJson023 "physical_volume" = .ok geometryRowsTyped023.physicalVolume :=
  original_rationalField_of_string geometryRowsJson023 "physical_volume" geometryRow023_physicalVolumeText
    geometryRowsTyped023.physicalVolume geometryRow023_physicalVolume_field geometryRow023_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_physicalVolume_complete"
  err.flush

noncomputable def geometryRow023_meanGapNumeratorChars : List Char := ['1', '0', '8', '2', '4', '1', '6', '9']
noncomputable def geometryRow023_meanGapDenominatorChars : List Char := ['1', '9', '5', '8', '4', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_meanGapText : String := String.ofList (geometryRow023_meanGapNumeratorChars ++ '/' :: geometryRow023_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_meanGap_before_field"
  err.flush

theorem geometryRow023_meanGap_field :
    geometryRowsJson023.getObjVal? "mean_gap" = .ok (.str geometryRow023_meanGapText) := by rfl

theorem geometryRow023_meanGap_numerator_no_slash :
    geometryRow023_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_meanGap_numerator_parse :
    SourceJson.intChars geometryRow023_meanGapNumeratorChars = some (10824169 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_parse :
    SourceJson.intChars geometryRow023_meanGapDenominatorChars = some (19584000000 : Int) := by decide +kernel

theorem geometryRow023_meanGap_denominator_nonzero : (19584000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_meanGap_parse :
    parseRational geometryRow023_meanGapText = .ok geometryRowsTyped023.meanGap :=
  original_rational_fraction_of_chars geometryRow023_meanGapNumeratorChars geometryRow023_meanGapDenominatorChars
    (10824169 : Int) (19584000000 : Int)
    geometryRow023_meanGap_numerator_no_slash geometryRow023_meanGap_numerator_parse
    geometryRow023_meanGap_denominator_parse geometryRow023_meanGap_denominator_nonzero

theorem geometryRow023_meanGap_read :
    rationalField geometryRowsJson023 "mean_gap" = .ok geometryRowsTyped023.meanGap :=
  original_rationalField_of_string geometryRowsJson023 "mean_gap" geometryRow023_meanGapText
    geometryRowsTyped023.meanGap geometryRow023_meanGap_field geometryRow023_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_meanGap_complete"
  err.flush

noncomputable def geometryRow023_jensenBoundNumeratorChars : List Char := ['4', '8', '9', '6', '9', '7', '7', '8', '6', '9', '3', '7', '9', '8', '7', '2', '0', '1', '4', '8', '6', '4', '6', '1', '6', '4', '5', '9', '0', '8', '9', '1', '7', '2', '1', '3', '4', '9', '6', '9', '5', '4', '5', '3', '6', '1', '2', '3', '2', '6', '0', '3', '0', '5', '8', '4', '2', '7', '5', '9', '5', '1', '0', '0', '7', '4', '0', '8', '8', '7', '1', '1', '0', '6', '8', '1', '9', '3', '1', '1', '2', '2', '0', '5', '0', '0', '5', '3', '3', '7', '2', '4', '0', '4', '4', '4', '7', '3', '5', '0', '0', '0', '8', '3', '8', '4', '7', '0', '0', '7', '5', '8', '3', '3', '1', '2', '9', '1', '6', '7', '1', '2', '6', '2', '8', '0', '4', '0', '9', '5', '6', '7', '9', '8', '2', '1', '3', '4', '9', '8', '1', '4', '6', '5', '1', '3', '8', '9', '9', '1', '3', '8', '5', '5', '4', '0', '7', '5', '1', '6', '4', '9', '8', '1', '3', '8', '0', '5', '2', '8', '1', '5', '4', '4', '6', '1', '5', '5', '6', '9', '1', '2', '9', '4', '7', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow023_jensenBoundDenominatorChars : List Char := ['8', '9', '1', '6', '6', '3', '1', '8', '4', '5', '4', '4', '3', '9', '0', '2', '7', '7', '3', '0', '1', '9', '8', '6', '4', '0', '1', '3', '9', '1', '9', '0', '5', '5', '2', '9', '7', '3', '6', '9', '8', '9', '7', '7', '1', '3', '5', '0', '7', '8', '9', '2', '3', '6', '7', '7', '1', '4', '8', '9', '9', '7', '1', '9', '9', '3', '3', '8', '2', '1', '1', '7', '1', '0', '4', '8', '6', '0', '7', '9', '0', '4', '0', '5', '2', '5', '0', '9', '6', '7', '4', '2', '2', '2', '6', '2', '3', '0', '5', '3', '5', '0', '8', '0', '6', '3', '7', '7', '4', '9', '2', '4', '5', '2', '9', '4', '6', '6', '0', '7', '1', '2', '5', '9', '3', '8', '3', '2', '8', '4', '4', '1', '8', '0', '5', '9', '3', '4', '3', '8', '0', '3', '5', '8', '8', '1', '2', '1', '7', '7', '5', '9', '7', '9', '9', '6', '4', '4', '1', '1', '6', '8', '4', '6', '9', '9', '9', '8', '0', '2', '1', '3', '0', '5', '0', '8', '0', '4', '7', '7', '7', '1', '1', '0', '3', '9', '2', '0', '6', '8', '8', '8', '8', '1', '4', '8', '5', '6', '5', '9', '8', '2', '7', '2', '2', '7', '9', '7', '9', '5', '6', '7', '2', '4', '1', '8', '3', '6', '2', '7', '8', '1']
noncomputable def geometryRow023_jensenBoundText : String := String.ofList (geometryRow023_jensenBoundNumeratorChars ++ '/' :: geometryRow023_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_jensenBound_before_field"
  err.flush

theorem geometryRow023_jensenBound_field :
    geometryRowsJson023.getObjVal? "jensen_bound" = .ok (.str geometryRow023_jensenBoundText) := by rfl

theorem geometryRow023_jensenBound_numerator_no_slash :
    geometryRow023_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow023_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow023_jensenBoundNumeratorChars = some (48969778693798720148646164590891721349695453612326030584275951007408871106819311220500533724044473500083847007583312916712628040956798213498146513899138554075164981380528154461556912947200000000000000000000000 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow023_jensenBoundDenominatorChars = some (891663184544390277301986401391905529736989771350789236771489971993382117104860790405250967422262305350806377492452946607125938328441805934380358812177597996441168469998021305080477711039206888814856598272279795672418362781 : Int) := by decide +kernel

theorem geometryRow023_jensenBound_denominator_nonzero : (891663184544390277301986401391905529736989771350789236771489971993382117104860790405250967422262305350806377492452946607125938328441805934380358812177597996441168469998021305080477711039206888814856598272279795672418362781 : Int) ≠ 0 := by decide +kernel

theorem geometryRow023_jensenBound_parse :
    parseRational geometryRow023_jensenBoundText = .ok geometryRowsTyped023.jensenBound :=
  original_rational_fraction_of_chars geometryRow023_jensenBoundNumeratorChars geometryRow023_jensenBoundDenominatorChars
    (48969778693798720148646164590891721349695453612326030584275951007408871106819311220500533724044473500083847007583312916712628040956798213498146513899138554075164981380528154461556912947200000000000000000000000 : Int) (891663184544390277301986401391905529736989771350789236771489971993382117104860790405250967422262305350806377492452946607125938328441805934380358812177597996441168469998021305080477711039206888814856598272279795672418362781 : Int)
    geometryRow023_jensenBound_numerator_no_slash geometryRow023_jensenBound_numerator_parse
    geometryRow023_jensenBound_denominator_parse geometryRow023_jensenBound_denominator_nonzero

theorem geometryRow023_jensenBound_read :
    rationalField geometryRowsJson023 "jensen_bound" = .ok geometryRowsTyped023.jensenBound :=
  original_rationalField_of_string geometryRowsJson023 "jensen_bound" geometryRow023_jensenBoundText
    geometryRowsTyped023.jensenBound geometryRow023_jensenBound_field geometryRow023_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_factorMaxima_before"
  err.flush

theorem geometryRow023_factorMaxima_read :
    rationalArrayField geometryRowsJson023 "factor_maxima" = .ok geometryRowsTyped023.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_gapWeightedMeans_before"
  err.flush

theorem geometryRow023_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson023 "gap_weighted_means" = .ok geometryRowsTyped023.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow023_floorChars : List Char := ['4', '3', '5', '1', '1', '7', '8', '3', '9', '5', '4', '8', '6', '0', '5', '2']
noncomputable def geometryRow023_floorText : String := String.ofList geometryRow023_floorChars

theorem geometryRow023_floor_text_read :
    geometryRowsJson023.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow023_floorText := by rfl

theorem geometryRow023_floor_chars_parse :
    SourceJson.intChars geometryRow023_floorChars = some (4351178395486052 : Int) := by decide +kernel

theorem geometryRow023_floor_parse :
    parseInteger geometryRow023_floorText = .ok geometryRowsTyped023.jensenFloorQ96 := by
  simp only [geometryRow023_floorText, parseInteger, String.toList_ofList, geometryRow023_floor_chars_parse]
  rfl

theorem decode_geometry_Rows_023 :
    decodeGeometryRow geometryRowsJson023 = .ok geometryRowsTyped023 :=
  original_geometryRow_of_fields geometryRowsJson023 geometryRowsTyped023 geometryRow023_floorText
    geometryRow023_simplexId_read geometryRow023_vertexIds_read
    geometryRow023_physicalVolume_read geometryRow023_meanGap_read
    geometryRow023_factorMaxima_read geometryRow023_gapWeightedMeans_read
    geometryRow023_jensenBound_read geometryRow023_floor_text_read geometryRow023_floor_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_DIRECT_PACKED SCALABLE_05_Row_023_original_decoder_complete"
  err.flush

theorem geometryRow023_shape :
    geometryRowsTyped023.simplexId = 23 ∧
    geometryRowsTyped023.vertexIds.size = 9 ∧ geometryRowsTyped023.vertexIds.toList.Nodup ∧
    (∀ i : Fin 9, geometryRowsTyped023.vertexIds[i.val]! < 28) ∧
    geometryRowsTyped023.factorMaxima.size = 10 ∧ geometryRowsTyped023.gapWeightedMeans.size = 10 := by
  decide +kernel

noncomputable def geometryRowsJsonBlock002 : List SourceJson := [geometryRowsJson016, geometryRowsJson017, geometryRowsJson018, geometryRowsJson019, geometryRowsJson020, geometryRowsJson021, geometryRowsJson022, geometryRowsJson023]
noncomputable def geometryRowsTypedBlock002 : List GeometryRow := [geometryRowsTyped016, geometryRowsTyped017, geometryRowsTyped018, geometryRowsTyped019, geometryRowsTyped020, geometryRowsTyped021, geometryRowsTyped022, geometryRowsTyped023]

theorem geometry_Rows_block_002_push_eq (acc : List SourceJson) :
    SimplicesBlock002.blockPush acc = [geometryRowsJson023, geometryRowsJson022, geometryRowsJson021, geometryRowsJson020, geometryRowsJson019, geometryRowsJson018, geometryRowsJson017, geometryRowsJson016] ++ acc := by rfl

theorem geometry_Rows_block_002_reverse (acc : List SourceJson) :
    (SimplicesBlock002.blockPush acc).reverse = acc.reverse ++ geometryRowsJsonBlock002 := by
  rw [geometry_Rows_block_002_push_eq, List.reverse_append]
  rfl

theorem decode_geometry_Rows_block_002 :
    geometryRowsJsonBlock002.mapM decodeGeometryRow = .ok geometryRowsTypedBlock002 := by
  simp only [geometryRowsJsonBlock002, geometryRowsTypedBlock002, List.mapM_cons, List.mapM_nil,
    decode_geometry_Rows_016, decode_geometry_Rows_017, decode_geometry_Rows_018, decode_geometry_Rows_019, decode_geometry_Rows_020, decode_geometry_Rows_021, decode_geometry_Rows_022, decode_geometry_Rows_023]
  rfl

theorem geometry_Rows_block_002_length : geometryRowsTypedBlock002.length = 8 := by rfl

#print axioms geometryRow016_simplexId_read
#print axioms geometryRow016_vertexIds_read
#print axioms geometryRow016_physicalVolume_field
#print axioms geometryRow016_physicalVolume_numerator_no_slash
#print axioms geometryRow016_physicalVolume_numerator_parse
#print axioms geometryRow016_physicalVolume_denominator_parse
#print axioms geometryRow016_physicalVolume_denominator_nonzero
#print axioms geometryRow016_physicalVolume_parse
#print axioms geometryRow016_physicalVolume_read
#print axioms geometryRow016_meanGap_field
#print axioms geometryRow016_meanGap_numerator_no_slash
#print axioms geometryRow016_meanGap_numerator_parse
#print axioms geometryRow016_meanGap_denominator_parse
#print axioms geometryRow016_meanGap_denominator_nonzero
#print axioms geometryRow016_meanGap_parse
#print axioms geometryRow016_meanGap_read
#print axioms geometryRow016_jensenBound_field
#print axioms geometryRow016_jensenBound_numerator_no_slash
#print axioms geometryRow016_jensenBound_numerator_parse
#print axioms geometryRow016_jensenBound_denominator_parse
#print axioms geometryRow016_jensenBound_denominator_nonzero
#print axioms geometryRow016_jensenBound_parse
#print axioms geometryRow016_jensenBound_read
#print axioms geometryRow016_factorMaxima_read
#print axioms geometryRow016_gapWeightedMeans_read
#print axioms geometryRow016_floor_text_read
#print axioms geometryRow016_floor_chars_parse
#print axioms geometryRow016_floor_parse
#print axioms decode_geometry_Rows_016
#print axioms geometryRow016_shape
#print axioms geometryRow017_simplexId_read
#print axioms geometryRow017_vertexIds_read
#print axioms geometryRow017_physicalVolume_field
#print axioms geometryRow017_physicalVolume_numerator_no_slash
#print axioms geometryRow017_physicalVolume_numerator_parse
#print axioms geometryRow017_physicalVolume_denominator_parse
#print axioms geometryRow017_physicalVolume_denominator_nonzero
#print axioms geometryRow017_physicalVolume_parse
#print axioms geometryRow017_physicalVolume_read
#print axioms geometryRow017_meanGap_field
#print axioms geometryRow017_meanGap_numerator_no_slash
#print axioms geometryRow017_meanGap_numerator_parse
#print axioms geometryRow017_meanGap_denominator_parse
#print axioms geometryRow017_meanGap_denominator_nonzero
#print axioms geometryRow017_meanGap_parse
#print axioms geometryRow017_meanGap_read
#print axioms geometryRow017_jensenBound_field
#print axioms geometryRow017_jensenBound_numerator_no_slash
#print axioms geometryRow017_jensenBound_numerator_parse
#print axioms geometryRow017_jensenBound_denominator_parse
#print axioms geometryRow017_jensenBound_denominator_nonzero
#print axioms geometryRow017_jensenBound_parse
#print axioms geometryRow017_jensenBound_read
#print axioms geometryRow017_factorMaxima_read
#print axioms geometryRow017_gapWeightedMeans_read
#print axioms geometryRow017_floor_text_read
#print axioms geometryRow017_floor_chars_parse
#print axioms geometryRow017_floor_parse
#print axioms decode_geometry_Rows_017
#print axioms geometryRow017_shape
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
#print axioms geometryRow018_shape
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
#print axioms geometryRow019_shape
#print axioms geometryRow020_simplexId_read
#print axioms geometryRow020_vertexIds_read
#print axioms geometryRow020_physicalVolume_field
#print axioms geometryRow020_physicalVolume_numerator_no_slash
#print axioms geometryRow020_physicalVolume_numerator_parse
#print axioms geometryRow020_physicalVolume_denominator_parse
#print axioms geometryRow020_physicalVolume_denominator_nonzero
#print axioms geometryRow020_physicalVolume_parse
#print axioms geometryRow020_physicalVolume_read
#print axioms geometryRow020_meanGap_field
#print axioms geometryRow020_meanGap_numerator_no_slash
#print axioms geometryRow020_meanGap_numerator_parse
#print axioms geometryRow020_meanGap_denominator_parse
#print axioms geometryRow020_meanGap_denominator_nonzero
#print axioms geometryRow020_meanGap_parse
#print axioms geometryRow020_meanGap_read
#print axioms geometryRow020_jensenBound_field
#print axioms geometryRow020_jensenBound_numerator_no_slash
#print axioms geometryRow020_jensenBound_numerator_parse
#print axioms geometryRow020_jensenBound_denominator_parse
#print axioms geometryRow020_jensenBound_denominator_nonzero
#print axioms geometryRow020_jensenBound_parse
#print axioms geometryRow020_jensenBound_read
#print axioms geometryRow020_factorMaxima_read
#print axioms geometryRow020_gapWeightedMeans_read
#print axioms geometryRow020_floor_text_read
#print axioms geometryRow020_floor_chars_parse
#print axioms geometryRow020_floor_parse
#print axioms decode_geometry_Rows_020
#print axioms geometryRow020_shape
#print axioms geometryRow021_simplexId_read
#print axioms geometryRow021_vertexIds_read
#print axioms geometryRow021_physicalVolume_field
#print axioms geometryRow021_physicalVolume_numerator_no_slash
#print axioms geometryRow021_physicalVolume_numerator_parse
#print axioms geometryRow021_physicalVolume_denominator_parse
#print axioms geometryRow021_physicalVolume_denominator_nonzero
#print axioms geometryRow021_physicalVolume_parse
#print axioms geometryRow021_physicalVolume_read
#print axioms geometryRow021_meanGap_field
#print axioms geometryRow021_meanGap_numerator_no_slash
#print axioms geometryRow021_meanGap_numerator_parse
#print axioms geometryRow021_meanGap_denominator_parse
#print axioms geometryRow021_meanGap_denominator_nonzero
#print axioms geometryRow021_meanGap_parse
#print axioms geometryRow021_meanGap_read
#print axioms geometryRow021_jensenBound_field
#print axioms geometryRow021_jensenBound_numerator_no_slash
#print axioms geometryRow021_jensenBound_numerator_parse
#print axioms geometryRow021_jensenBound_denominator_parse
#print axioms geometryRow021_jensenBound_denominator_nonzero
#print axioms geometryRow021_jensenBound_parse
#print axioms geometryRow021_jensenBound_read
#print axioms geometryRow021_factorMaxima_read
#print axioms geometryRow021_gapWeightedMeans_read
#print axioms geometryRow021_floor_text_read
#print axioms geometryRow021_floor_chars_parse
#print axioms geometryRow021_floor_parse
#print axioms decode_geometry_Rows_021
#print axioms geometryRow021_shape
#print axioms geometryRow022_simplexId_read
#print axioms geometryRow022_vertexIds_read
#print axioms geometryRow022_physicalVolume_field
#print axioms geometryRow022_physicalVolume_numerator_no_slash
#print axioms geometryRow022_physicalVolume_numerator_parse
#print axioms geometryRow022_physicalVolume_denominator_parse
#print axioms geometryRow022_physicalVolume_denominator_nonzero
#print axioms geometryRow022_physicalVolume_parse
#print axioms geometryRow022_physicalVolume_read
#print axioms geometryRow022_meanGap_field
#print axioms geometryRow022_meanGap_numerator_no_slash
#print axioms geometryRow022_meanGap_numerator_parse
#print axioms geometryRow022_meanGap_denominator_parse
#print axioms geometryRow022_meanGap_denominator_nonzero
#print axioms geometryRow022_meanGap_parse
#print axioms geometryRow022_meanGap_read
#print axioms geometryRow022_jensenBound_field
#print axioms geometryRow022_jensenBound_numerator_no_slash
#print axioms geometryRow022_jensenBound_numerator_parse
#print axioms geometryRow022_jensenBound_denominator_parse
#print axioms geometryRow022_jensenBound_denominator_nonzero
#print axioms geometryRow022_jensenBound_parse
#print axioms geometryRow022_jensenBound_read
#print axioms geometryRow022_factorMaxima_read
#print axioms geometryRow022_gapWeightedMeans_read
#print axioms geometryRow022_floor_text_read
#print axioms geometryRow022_floor_chars_parse
#print axioms geometryRow022_floor_parse
#print axioms decode_geometry_Rows_022
#print axioms geometryRow022_shape
#print axioms geometryRow023_simplexId_read
#print axioms geometryRow023_vertexIds_read
#print axioms geometryRow023_physicalVolume_field
#print axioms geometryRow023_physicalVolume_numerator_no_slash
#print axioms geometryRow023_physicalVolume_numerator_parse
#print axioms geometryRow023_physicalVolume_denominator_parse
#print axioms geometryRow023_physicalVolume_denominator_nonzero
#print axioms geometryRow023_physicalVolume_parse
#print axioms geometryRow023_physicalVolume_read
#print axioms geometryRow023_meanGap_field
#print axioms geometryRow023_meanGap_numerator_no_slash
#print axioms geometryRow023_meanGap_numerator_parse
#print axioms geometryRow023_meanGap_denominator_parse
#print axioms geometryRow023_meanGap_denominator_nonzero
#print axioms geometryRow023_meanGap_parse
#print axioms geometryRow023_meanGap_read
#print axioms geometryRow023_jensenBound_field
#print axioms geometryRow023_jensenBound_numerator_no_slash
#print axioms geometryRow023_jensenBound_numerator_parse
#print axioms geometryRow023_jensenBound_denominator_parse
#print axioms geometryRow023_jensenBound_denominator_nonzero
#print axioms geometryRow023_jensenBound_parse
#print axioms geometryRow023_jensenBound_read
#print axioms geometryRow023_factorMaxima_read
#print axioms geometryRow023_gapWeightedMeans_read
#print axioms geometryRow023_floor_text_read
#print axioms geometryRow023_floor_chars_parse
#print axioms geometryRow023_floor_parse
#print axioms decode_geometry_Rows_023
#print axioms geometryRow023_shape
#print axioms geometry_Rows_block_002_push_eq
#print axioms geometry_Rows_block_002_reverse
#print axioms decode_geometry_Rows_block_002
#print axioms geometry_Rows_block_002_length

end ImbalancedChen.P2OriginalSaving19Geometry05ScalableDecoding
