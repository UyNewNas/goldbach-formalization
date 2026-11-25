import ImbalancedChen.P2OriginalSaving19ArchiveRationalChars
import ImbalancedChen.P2OriginalSaving19SimplicesArrayBlock00400

/-! Original GeometryRow 16: field-wise decoder certificates.
All actual reader/transport objects and the genuine original ArchiveSchema are
reused. Candidate typed values below require original-decoder Lean equalities.
No source JSON or mathematical certificate field is deleted or normalized. -/
namespace ImbalancedChen.P2OriginalSaving19Geometry00Decoding
set_option maxRecDepth 1000000
set_option Elab.async false
set_option stderrAsMessages false
open ImbalancedChen.P2OriginalSaving19Archive
open ImbalancedChen.P2OriginalSaving19CharacterCoreDiagnostic

noncomputable def geometryRowsJson016 : SourceJson :=
  (simplicesChunk016Push00 []).get ⟨0, by decide +kernel⟩

noncomputable def geometryRowsTyped016 : GeometryRow :=
  { simplexId := 16,
    vertexIds := #[27, 25, 23, 21, 19, 5, 3, 2, 0],
    physicalVolume := ((287479201945717047845535428386117681 : ℚ) / (5190291216337500000000000000000000000000000000000000000000 : ℚ)),
    meanGap := ((19865249 : ℚ) / (23712000000 : ℚ)),
    factorMaxima := #[((2484331 : ℚ) / (24000000 : ℚ)), ((2484331 : ℚ) / (24000000 : ℚ)), ((2859299 : ℚ) / (21000000 : ℚ)), ((8952977 : ℚ) / (84000000 : ℚ)), ((1171847 : ℚ) / (12000000 : ℚ)), ((2315557 : ℚ) / (28800000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((934361 : ℚ) / (24900000 : ℚ)), ((7359347 : ℚ) / (208000000 : ℚ)), ((2484331 : ℚ) / (72000000 : ℚ))],
    gapWeightedMeans := #[((1869873345399522054331 : ℚ) / (20525776475349600000000 : ℚ)), ((946552064500065379313 : ℚ) / (10262888237674800000000 : ℚ)), ((506627514952671831931 : ℚ) / (4105155295069920000000 : ℚ)), ((148796524411611811771 : ℚ) / (1578905882719200000000 : ℚ)), ((199012335706739049343 : ℚ) / (2280641830594400000000 : ℚ)), ((323895674994046117 : ℚ) / (4691606051508480000 : ℚ)), ((6298053414313025129 : ℚ) / (183265861387050000000 : ℚ)), ((2048455900604829347 : ℚ) / (61088620462350000000 : ℚ)), ((163377483989915574583 : ℚ) / (5131444118837400000000 : ℚ)), ((322642688083286857211 : ℚ) / (10262888237674800000000 : ℚ))],
    jensenBound := ((1598767341162082085063545501714575888901964153300346990957678387588985339452240585966970615762961964263226877979301446589363473716537154490517939602383222454123233280000000000000000000000 : ℚ) / (5848848777527831187598845575606253618208036185348342148610423095146496300720884427142454785299120118821471785750565681133834191373337794138009871830674537365304726281228555987818610619115828035103167 : ℚ)),
    jensenFloorQ96 := (21656808638096986 : Int) }

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_simplexId_before"
  err.flush

theorem geometryRow016_simplexId_read :
    geometryRowsJson016.getObjValAs? Nat "simplex_id" = .ok geometryRowsTyped016.simplexId := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_vertexIds_before"
  err.flush

theorem geometryRow016_vertexIds_read :
    geometryRowsJson016.getObjValAs? (Array Nat) "vertex_ids" = .ok geometryRowsTyped016.vertexIds := by decide +kernel

noncomputable def geometryRow016_physicalVolumeNumeratorChars : List Char := ['2', '8', '7', '4', '7', '9', '2', '0', '1', '9', '4', '5', '7', '1', '7', '0', '4', '7', '8', '4', '5', '5', '3', '5', '4', '2', '8', '3', '8', '6', '1', '1', '7', '6', '8', '1']
noncomputable def geometryRow016_physicalVolumeDenominatorChars : List Char := ['5', '1', '9', '0', '2', '9', '1', '2', '1', '6', '3', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_physicalVolumeText : String := String.ofList (geometryRow016_physicalVolumeNumeratorChars ++ '/' :: geometryRow016_physicalVolumeDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_physicalVolume_before_field"
  err.flush

theorem geometryRow016_physicalVolume_field :
    geometryRowsJson016.getObjVal? "physical_volume" = .ok (.str geometryRow016_physicalVolumeText) := by rfl

theorem geometryRow016_physicalVolume_numerator_no_slash :
    geometryRow016_physicalVolumeNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_physicalVolume_numerator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeNumeratorChars = some (287479201945717047845535428386117681 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_parse :
    SourceJson.intChars geometryRow016_physicalVolumeDenominatorChars = some (5190291216337500000000000000000000000000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_physicalVolume_denominator_nonzero : (5190291216337500000000000000000000000000000000000000000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_physicalVolume_parse :
    parseRational geometryRow016_physicalVolumeText = .ok geometryRowsTyped016.physicalVolume :=
  original_rational_fraction_of_chars geometryRow016_physicalVolumeNumeratorChars geometryRow016_physicalVolumeDenominatorChars
    (287479201945717047845535428386117681 : Int) (5190291216337500000000000000000000000000000000000000000000 : Int)
    geometryRow016_physicalVolume_numerator_no_slash geometryRow016_physicalVolume_numerator_parse
    geometryRow016_physicalVolume_denominator_parse geometryRow016_physicalVolume_denominator_nonzero

theorem geometryRow016_physicalVolume_read :
    rationalField geometryRowsJson016 "physical_volume" = .ok geometryRowsTyped016.physicalVolume :=
  original_rationalField_of_string geometryRowsJson016 "physical_volume" geometryRow016_physicalVolumeText
    geometryRowsTyped016.physicalVolume geometryRow016_physicalVolume_field geometryRow016_physicalVolume_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_physicalVolume_complete"
  err.flush

noncomputable def geometryRow016_meanGapNumeratorChars : List Char := ['1', '9', '8', '6', '5', '2', '4', '9']
noncomputable def geometryRow016_meanGapDenominatorChars : List Char := ['2', '3', '7', '1', '2', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_meanGapText : String := String.ofList (geometryRow016_meanGapNumeratorChars ++ '/' :: geometryRow016_meanGapDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_meanGap_before_field"
  err.flush

theorem geometryRow016_meanGap_field :
    geometryRowsJson016.getObjVal? "mean_gap" = .ok (.str geometryRow016_meanGapText) := by rfl

theorem geometryRow016_meanGap_numerator_no_slash :
    geometryRow016_meanGapNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_meanGap_numerator_parse :
    SourceJson.intChars geometryRow016_meanGapNumeratorChars = some (19865249 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_parse :
    SourceJson.intChars geometryRow016_meanGapDenominatorChars = some (23712000000 : Int) := by decide +kernel

theorem geometryRow016_meanGap_denominator_nonzero : (23712000000 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_meanGap_parse :
    parseRational geometryRow016_meanGapText = .ok geometryRowsTyped016.meanGap :=
  original_rational_fraction_of_chars geometryRow016_meanGapNumeratorChars geometryRow016_meanGapDenominatorChars
    (19865249 : Int) (23712000000 : Int)
    geometryRow016_meanGap_numerator_no_slash geometryRow016_meanGap_numerator_parse
    geometryRow016_meanGap_denominator_parse geometryRow016_meanGap_denominator_nonzero

theorem geometryRow016_meanGap_read :
    rationalField geometryRowsJson016 "mean_gap" = .ok geometryRowsTyped016.meanGap :=
  original_rationalField_of_string geometryRowsJson016 "mean_gap" geometryRow016_meanGapText
    geometryRowsTyped016.meanGap geometryRow016_meanGap_field geometryRow016_meanGap_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_meanGap_complete"
  err.flush

noncomputable def geometryRow016_jensenBoundNumeratorChars : List Char := ['1', '5', '9', '8', '7', '6', '7', '3', '4', '1', '1', '6', '2', '0', '8', '2', '0', '8', '5', '0', '6', '3', '5', '4', '5', '5', '0', '1', '7', '1', '4', '5', '7', '5', '8', '8', '8', '9', '0', '1', '9', '6', '4', '1', '5', '3', '3', '0', '0', '3', '4', '6', '9', '9', '0', '9', '5', '7', '6', '7', '8', '3', '8', '7', '5', '8', '8', '9', '8', '5', '3', '3', '9', '4', '5', '2', '2', '4', '0', '5', '8', '5', '9', '6', '6', '9', '7', '0', '6', '1', '5', '7', '6', '2', '9', '6', '1', '9', '6', '4', '2', '6', '3', '2', '2', '6', '8', '7', '7', '9', '7', '9', '3', '0', '1', '4', '4', '6', '5', '8', '9', '3', '6', '3', '4', '7', '3', '7', '1', '6', '5', '3', '7', '1', '5', '4', '4', '9', '0', '5', '1', '7', '9', '3', '9', '6', '0', '2', '3', '8', '3', '2', '2', '2', '4', '5', '4', '1', '2', '3', '2', '3', '3', '2', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
noncomputable def geometryRow016_jensenBoundDenominatorChars : List Char := ['5', '8', '4', '8', '8', '4', '8', '7', '7', '7', '5', '2', '7', '8', '3', '1', '1', '8', '7', '5', '9', '8', '8', '4', '5', '5', '7', '5', '6', '0', '6', '2', '5', '3', '6', '1', '8', '2', '0', '8', '0', '3', '6', '1', '8', '5', '3', '4', '8', '3', '4', '2', '1', '4', '8', '6', '1', '0', '4', '2', '3', '0', '9', '5', '1', '4', '6', '4', '9', '6', '3', '0', '0', '7', '2', '0', '8', '8', '4', '4', '2', '7', '1', '4', '2', '4', '5', '4', '7', '8', '5', '2', '9', '9', '1', '2', '0', '1', '1', '8', '8', '2', '1', '4', '7', '1', '7', '8', '5', '7', '5', '0', '5', '6', '5', '6', '8', '1', '1', '3', '3', '8', '3', '4', '1', '9', '1', '3', '7', '3', '3', '3', '7', '7', '9', '4', '1', '3', '8', '0', '0', '9', '8', '7', '1', '8', '3', '0', '6', '7', '4', '5', '3', '7', '3', '6', '5', '3', '0', '4', '7', '2', '6', '2', '8', '1', '2', '2', '8', '5', '5', '5', '9', '8', '7', '8', '1', '8', '6', '1', '0', '6', '1', '9', '1', '1', '5', '8', '2', '8', '0', '3', '5', '1', '0', '3', '1', '6', '7']
noncomputable def geometryRow016_jensenBoundText : String := String.ofList (geometryRow016_jensenBoundNumeratorChars ++ '/' :: geometryRow016_jensenBoundDenominatorChars)

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_jensenBound_before_field"
  err.flush

theorem geometryRow016_jensenBound_field :
    geometryRowsJson016.getObjVal? "jensen_bound" = .ok (.str geometryRow016_jensenBoundText) := by rfl

theorem geometryRow016_jensenBound_numerator_no_slash :
    geometryRow016_jensenBoundNumeratorChars.all (fun c => c != '/') = true := by decide +kernel

theorem geometryRow016_jensenBound_numerator_parse :
    SourceJson.intChars geometryRow016_jensenBoundNumeratorChars = some (1598767341162082085063545501714575888901964153300346990957678387588985339452240585966970615762961964263226877979301446589363473716537154490517939602383222454123233280000000000000000000000 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_parse :
    SourceJson.intChars geometryRow016_jensenBoundDenominatorChars = some (5848848777527831187598845575606253618208036185348342148610423095146496300720884427142454785299120118821471785750565681133834191373337794138009871830674537365304726281228555987818610619115828035103167 : Int) := by decide +kernel

theorem geometryRow016_jensenBound_denominator_nonzero : (5848848777527831187598845575606253618208036185348342148610423095146496300720884427142454785299120118821471785750565681133834191373337794138009871830674537365304726281228555987818610619115828035103167 : Int) ≠ 0 := by decide +kernel

theorem geometryRow016_jensenBound_parse :
    parseRational geometryRow016_jensenBoundText = .ok geometryRowsTyped016.jensenBound :=
  original_rational_fraction_of_chars geometryRow016_jensenBoundNumeratorChars geometryRow016_jensenBoundDenominatorChars
    (1598767341162082085063545501714575888901964153300346990957678387588985339452240585966970615762961964263226877979301446589363473716537154490517939602383222454123233280000000000000000000000 : Int) (5848848777527831187598845575606253618208036185348342148610423095146496300720884427142454785299120118821471785750565681133834191373337794138009871830674537365304726281228555987818610619115828035103167 : Int)
    geometryRow016_jensenBound_numerator_no_slash geometryRow016_jensenBound_numerator_parse
    geometryRow016_jensenBound_denominator_parse geometryRow016_jensenBound_denominator_nonzero

theorem geometryRow016_jensenBound_read :
    rationalField geometryRowsJson016 "jensen_bound" = .ok geometryRowsTyped016.jensenBound :=
  original_rationalField_of_string geometryRowsJson016 "jensen_bound" geometryRow016_jensenBoundText
    geometryRowsTyped016.jensenBound geometryRow016_jensenBound_field geometryRow016_jensenBound_parse

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_jensenBound_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_factorMaxima_before"
  err.flush

theorem geometryRow016_factorMaxima_read :
    rationalArrayField geometryRowsJson016 "factor_maxima" = .ok geometryRowsTyped016.factorMaxima := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_factorMaxima_complete"
  err.flush

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_gapWeightedMeans_before"
  err.flush

theorem geometryRow016_gapWeightedMeans_read :
    rationalArrayField geometryRowsJson016 "gap_weighted_means" = .ok geometryRowsTyped016.gapWeightedMeans := by decide +kernel

run_cmd do
  let err ← IO.getStderr
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_gapWeightedMeans_complete"
  err.flush

noncomputable def geometryRow016_floorChars : List Char := ['2', '1', '6', '5', '6', '8', '0', '8', '6', '3', '8', '0', '9', '6', '9', '8', '6']
noncomputable def geometryRow016_floorText : String := String.ofList geometryRow016_floorChars

theorem geometryRow016_floor_text_read :
    geometryRowsJson016.getObjValAs? String "jensen_floor_Q96" = .ok geometryRow016_floorText := by rfl

theorem geometryRow016_floor_chars_parse :
    SourceJson.intChars geometryRow016_floorChars = some (21656808638096986 : Int) := by decide +kernel

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
  err.putStrLn "P26_GEOMETRY00_TYPED Row_016_original_decoder_complete"
  err.flush

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

end ImbalancedChen.P2OriginalSaving19Geometry00Decoding
