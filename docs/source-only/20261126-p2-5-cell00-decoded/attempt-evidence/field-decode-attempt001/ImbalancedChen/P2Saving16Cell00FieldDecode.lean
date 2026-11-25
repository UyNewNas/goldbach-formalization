import ImbalancedChen.P2OriginalSaving16DecoderCompose
import ImbalancedChen.P2Saving16Cell00ScalarDecode

/-!
Candidate compositional certificate for the complete proposed cell00 record.
Every field and scalar must be checked against the unchanged original decoder.
This module does not replace JSON parsing or assume any closed success guard.
-/
namespace ImbalancedChen.P2Saving16Cell00FieldDecode
open P2OriginalSaving19Archive (SourceJson)
open P2OriginalSaving16OriginalArchive
open P2Saving16Cell00TypedPayload
open P2Saving16Cell00ScalarDecode

attribute [local simp] decodeString_str decodeNat_number_ofList decodeArray_arr rationalArray_arr
attribute [local simp] SourceJson.getStr? SourceJson.getArr? SourceJson.getObjValAs?
attribute [local simp] SourceJson.natChars SourceJson.digitsNat
attribute [local simp] rational000_decoded rational001_decoded rational002_decoded rational003_decoded rational004_decoded rational005_decoded rational006_decoded rational007_decoded rational008_decoded rational009_decoded rational010_decoded rational011_decoded rational012_decoded rational013_decoded rational014_decoded rational015_decoded rational016_decoded rational017_decoded rational018_decoded rational019_decoded rational020_decoded rational021_decoded rational022_decoded rational023_decoded rational024_decoded rational025_decoded rational026_decoded rational027_decoded rational028_decoded rational029_decoded rational030_decoded rational031_decoded rational032_decoded rational033_decoded rational034_decoded rational035_decoded rational036_decoded rational037_decoded rational038_decoded rational039_decoded rational040_decoded rational041_decoded rational042_decoded rational043_decoded rational044_decoded rational045_decoded rational046_decoded rational047_decoded rational048_decoded rational049_decoded rational050_decoded rational051_decoded rational052_decoded rational053_decoded rational054_decoded rational055_decoded rational056_decoded rational057_decoded rational058_decoded rational059_decoded rational060_decoded rational061_decoded rational062_decoded rational063_decoded rational064_decoded rational065_decoded rational066_decoded rational067_decoded rational068_decoded rational069_decoded rational070_decoded rational071_decoded rational072_decoded rational073_decoded rational074_decoded rational075_decoded rational076_decoded rational077_decoded rational078_decoded rational079_decoded rational080_decoded rational081_decoded rational082_decoded rational083_decoded rational084_decoded rational085_decoded rational086_decoded rational087_decoded rational088_decoded rational089_decoded rational090_decoded rational091_decoded rational092_decoded rational093_decoded rational094_decoded rational095_decoded rational096_decoded rational097_decoded rational098_decoded rational099_decoded rational100_decoded rational101_decoded rational102_decoded rational103_decoded rational104_decoded rational105_decoded rational106_decoded rational107_decoded rational108_decoded rational109_decoded rational110_decoded rational111_decoded rational112_decoded rational113_decoded rational114_decoded rational115_decoded rational116_decoded rational117_decoded rational118_decoded rational119_decoded rational120_decoded rational121_decoded rational122_decoded rational123_decoded rational124_decoded rational125_decoded rational126_decoded rational127_decoded rational128_decoded rational129_decoded rational130_decoded rational131_decoded rational132_decoded rational133_decoded rational134_decoded rational135_decoded rational136_decoded rational137_decoded rational138_decoded rational139_decoded rational140_decoded rational141_decoded rational142_decoded rational143_decoded rational144_decoded rational145_decoded rational146_decoded rational147_decoded rational148_decoded rational149_decoded rational150_decoded rational151_decoded rational152_decoded rational153_decoded rational154_decoded rational155_decoded rational156_decoded rational157_decoded rational158_decoded rational159_decoded rational160_decoded rational161_decoded rational162_decoded rational163_decoded rational164_decoded rational165_decoded rational166_decoded rational167_decoded rational168_decoded rational169_decoded rational170_decoded rational171_decoded rational172_decoded rational173_decoded rational174_decoded rational175_decoded rational176_decoded rational177_decoded rational178_decoded rational179_decoded rational180_decoded rational181_decoded rational182_decoded rational183_decoded rational184_decoded rational185_decoded rational186_decoded rational187_decoded rational188_decoded rational189_decoded rational190_decoded rational191_decoded rational192_decoded rational193_decoded rational194_decoded rational195_decoded rational196_decoded rational197_decoded rational198_decoded rational199_decoded rational200_decoded rational201_decoded rational202_decoded rational203_decoded rational204_decoded rational205_decoded rational206_decoded rational207_decoded rational208_decoded rational209_decoded rational210_decoded integer000_decoded integer001_decoded integer002_decoded integer003_decoded integer004_decoded integer005_decoded integer006_decoded integer007_decoded integer008_decoded integer009_decoded integer010_decoded integer011_decoded integer012_decoded integer013_decoded integer014_decoded integer015_decoded

theorem lookup_dimension : rawRoot.getObjVal? "dimension" = .ok rawDimension := by
  rfl

attribute [local simp] lookup_dimension

theorem lookup_physical_jacobian : rawRoot.getObjVal? "physical_jacobian" = .ok rawPhysicalJacobian := by
  rfl

attribute [local simp] lookup_physical_jacobian

theorem lookup_cell_id : rawRoot.getObjVal? "cell_id" = .ok rawCellId := by
  rfl

attribute [local simp] lookup_cell_id

theorem lookup_left_masks : rawRoot.getObjVal? "left_masks" = .ok rawLeftMasks := by
  rfl

attribute [local simp] lookup_left_masks

theorem lookup_right_masks : rawRoot.getObjVal? "right_masks" = .ok rawRightMasks := by
  rfl

attribute [local simp] lookup_right_masks

theorem lookup_facet_original_indices : rawRoot.getObjVal? "facet_original_indices" = .ok rawFacetOriginalIndices := by
  rfl

attribute [local simp] lookup_facet_original_indices

theorem lookup_positive_normal_balance : rawRoot.getObjVal? "positive_normal_balance" = .ok rawPositiveNormalBalance := by
  rfl

attribute [local simp] lookup_positive_normal_balance

theorem lookup_normal_rank : rawRoot.getObjVal? "normal_rank" = .ok rawNormalRank := by
  rfl

attribute [local simp] lookup_normal_rank

theorem lookup_active8_enumeration : rawRoot.getObjVal? "active8_enumeration" = .ok rawActive8 := by
  rfl

attribute [local simp] lookup_active8_enumeration

theorem lookup_vertices : rawRoot.getObjVal? "vertices" = .ok rawVertices := by
  rfl

attribute [local simp] lookup_vertices

theorem lookup_vertex_values : rawRoot.getObjVal? "vertex_values" = .ok rawVertexValues := by
  rfl

attribute [local simp] lookup_vertex_values

theorem lookup_all_original_constraint_minima : rawRoot.getObjVal? "all_original_constraint_minima" = .ok rawAllOriginalMinima := by
  rfl

attribute [local simp] lookup_all_original_constraint_minima

theorem lookup_facet_vertices : rawRoot.getObjVal? "facet_vertices" = .ok rawFacetVertices := by
  rfl

attribute [local simp] lookup_facet_vertices

theorem lookup_face_ledger : rawRoot.getObjVal? "face_ledger" = .ok rawFaceLedger := by
  rfl

attribute [local simp] lookup_face_ledger

theorem lookup_simplices : rawRoot.getObjVal? "simplices" = .ok rawSimplices := by
  rfl

attribute [local simp] lookup_simplices

theorem lookup_physical_volume : rawRoot.getObjVal? "physical_volume" = .ok rawPhysicalVolume := by
  rfl

attribute [local simp] lookup_physical_volume

theorem lookup_integral_gap : rawRoot.getObjVal? "integral_gap" = .ok rawIntegralGap := by
  rfl

attribute [local simp] lookup_integral_gap

theorem cellId_decoded :
    (SourceJson.Decode.read rawCellId : Except String (Nat)) = .ok cellId := by
  unfold rawCellId cellId
  simp

attribute [local simp] cellId_decoded

theorem cellId_field : rawRoot.getObjValAs? (Nat) "cell_id" = .ok cellId := by
  rw [getObjValAs_of_lookup rawRoot "cell_id" rawCellId lookup_cell_id]
  exact cellId_decoded

attribute [local simp] cellId_field

theorem dimension_decoded :
    (SourceJson.Decode.read rawDimension : Except String (Nat)) = .ok dimension := by
  unfold rawDimension dimension
  simp

attribute [local simp] dimension_decoded

theorem dimension_field : rawRoot.getObjValAs? (Nat) "dimension" = .ok dimension := by
  rw [getObjValAs_of_lookup rawRoot "dimension" rawDimension lookup_dimension]
  exact dimension_decoded

attribute [local simp] dimension_field

theorem physicalJacobian_decoded :
    (SourceJson.Decode.read rawPhysicalJacobian : Except String (Nat)) = .ok physicalJacobian := by
  unfold rawPhysicalJacobian physicalJacobian
  simp

attribute [local simp] physicalJacobian_decoded

theorem physicalJacobian_field : rawRoot.getObjValAs? (Nat) "physical_jacobian" = .ok physicalJacobian := by
  rw [getObjValAs_of_lookup rawRoot "physical_jacobian" rawPhysicalJacobian lookup_physical_jacobian]
  exact physicalJacobian_decoded

attribute [local simp] physicalJacobian_field

theorem leftMasks_decoded :
    (SourceJson.Decode.read rawLeftMasks : Except String (Array Nat)) = .ok leftMasks := by
  unfold rawLeftMasks leftMasks
  simp

attribute [local simp] leftMasks_decoded

theorem leftMasks_field : rawRoot.getObjValAs? (Array Nat) "left_masks" = .ok leftMasks := by
  rw [getObjValAs_of_lookup rawRoot "left_masks" rawLeftMasks lookup_left_masks]
  exact leftMasks_decoded

attribute [local simp] leftMasks_field

theorem rightMasks_decoded :
    (SourceJson.Decode.read rawRightMasks : Except String (Array Nat)) = .ok rightMasks := by
  unfold rawRightMasks rightMasks
  simp

attribute [local simp] rightMasks_decoded

theorem rightMasks_field : rawRoot.getObjValAs? (Array Nat) "right_masks" = .ok rightMasks := by
  rw [getObjValAs_of_lookup rawRoot "right_masks" rawRightMasks lookup_right_masks]
  exact rightMasks_decoded

attribute [local simp] rightMasks_field

theorem facetOriginalIndices_decoded :
    (SourceJson.Decode.read rawFacetOriginalIndices : Except String (Array Nat)) = .ok facetOriginalIndices := by
  unfold rawFacetOriginalIndices facetOriginalIndices
  simp

attribute [local simp] facetOriginalIndices_decoded

theorem facetOriginalIndices_field : rawRoot.getObjValAs? (Array Nat) "facet_original_indices" = .ok facetOriginalIndices := by
  rw [getObjValAs_of_lookup rawRoot "facet_original_indices" rawFacetOriginalIndices lookup_facet_original_indices]
  exact facetOriginalIndices_decoded

attribute [local simp] facetOriginalIndices_field

theorem normalRank_decoded :
    (SourceJson.Decode.read rawNormalRank : Except String (Nat)) = .ok normalRank := by
  unfold rawNormalRank normalRank
  simp

attribute [local simp] normalRank_decoded

theorem normalRank_field : rawRoot.getObjValAs? (Nat) "normal_rank" = .ok normalRank := by
  rw [getObjValAs_of_lookup rawRoot "normal_rank" rawNormalRank lookup_normal_rank]
  exact normalRank_decoded

attribute [local simp] normalRank_field

theorem facetVertices_decoded :
    (SourceJson.Decode.read rawFacetVertices : Except String (Array (Array Nat))) = .ok facetVertices := by
  unfold rawFacetVertices facetVertices
  simp

attribute [local simp] facetVertices_decoded

theorem facetVertices_field : rawRoot.getObjValAs? (Array (Array Nat)) "facet_vertices" = .ok facetVertices := by
  rw [getObjValAs_of_lookup rawRoot "facet_vertices" rawFacetVertices lookup_facet_vertices]
  exact facetVertices_decoded

attribute [local simp] facetVertices_field

theorem positiveNormalBalance_decoded : rationalArray rawPositiveNormalBalance = .ok positiveNormalBalance := by
  unfold rawPositiveNormalBalance positiveNormalBalance
  simp

attribute [local simp] positiveNormalBalance_decoded

theorem positiveNormalBalance_field : rationalArrayField rawRoot "positive_normal_balance" = .ok positiveNormalBalance := by
  rw [rationalArrayField_of_lookup rawRoot "positive_normal_balance" rawPositiveNormalBalance lookup_positive_normal_balance]
  exact positiveNormalBalance_decoded

attribute [local simp] positiveNormalBalance_field

theorem allOriginalMinima_decoded : rationalArray rawAllOriginalMinima = .ok allOriginalMinima := by
  unfold rawAllOriginalMinima allOriginalMinima
  simp

attribute [local simp] allOriginalMinima_decoded

theorem allOriginalMinima_field : rationalArrayField rawRoot "all_original_constraint_minima" = .ok allOriginalMinima := by
  rw [rationalArrayField_of_lookup rawRoot "all_original_constraint_minima" rawAllOriginalMinima lookup_all_original_constraint_minima]
  exact allOriginalMinima_decoded

attribute [local simp] allOriginalMinima_field

theorem vertex00_decoded : rationalArray rawVertex00 = .ok vertex00 := by
  unfold rawVertex00 vertex00
  simp

attribute [local simp] vertex00_decoded

theorem vertex01_decoded : rationalArray rawVertex01 = .ok vertex01 := by
  unfold rawVertex01 vertex01
  simp

attribute [local simp] vertex01_decoded

theorem vertex02_decoded : rationalArray rawVertex02 = .ok vertex02 := by
  unfold rawVertex02 vertex02
  simp

attribute [local simp] vertex02_decoded

theorem vertex03_decoded : rationalArray rawVertex03 = .ok vertex03 := by
  unfold rawVertex03 vertex03
  simp

attribute [local simp] vertex03_decoded

theorem vertex04_decoded : rationalArray rawVertex04 = .ok vertex04 := by
  unfold rawVertex04 vertex04
  simp

attribute [local simp] vertex04_decoded

theorem vertex05_decoded : rationalArray rawVertex05 = .ok vertex05 := by
  unfold rawVertex05 vertex05
  simp

attribute [local simp] vertex05_decoded

theorem vertex06_decoded : rationalArray rawVertex06 = .ok vertex06 := by
  unfold rawVertex06 vertex06
  simp

attribute [local simp] vertex06_decoded

theorem vertex07_decoded : rationalArray rawVertex07 = .ok vertex07 := by
  unfold rawVertex07 vertex07
  simp

attribute [local simp] vertex07_decoded

theorem vertex08_decoded : rationalArray rawVertex08 = .ok vertex08 := by
  unfold rawVertex08 vertex08
  simp

attribute [local simp] vertex08_decoded

theorem vertex09_decoded : rationalArray rawVertex09 = .ok vertex09 := by
  unfold rawVertex09 vertex09
  simp

attribute [local simp] vertex09_decoded

theorem vertex10_decoded : rationalArray rawVertex10 = .ok vertex10 := by
  unfold rawVertex10 vertex10
  simp

attribute [local simp] vertex10_decoded

theorem vertex11_decoded : rationalArray rawVertex11 = .ok vertex11 := by
  unfold rawVertex11 vertex11
  simp

attribute [local simp] vertex11_decoded

theorem vertex12_decoded : rationalArray rawVertex12 = .ok vertex12 := by
  unfold rawVertex12 vertex12
  simp

attribute [local simp] vertex12_decoded

theorem vertex13_decoded : rationalArray rawVertex13 = .ok vertex13 := by
  unfold rawVertex13 vertex13
  simp

attribute [local simp] vertex13_decoded

theorem vertex14_decoded : rationalArray rawVertex14 = .ok vertex14 := by
  unfold rawVertex14 vertex14
  simp

attribute [local simp] vertex14_decoded

theorem vertex15_decoded : rationalArray rawVertex15 = .ok vertex15 := by
  unfold rawVertex15 vertex15
  simp

attribute [local simp] vertex15_decoded

theorem vertices_mapped : rawVerticesItems.toArray.mapM rationalArray = .ok vertices := by
  unfold rawVerticesItems vertices
  simp

attribute [local simp] vertices_mapped

theorem simplex00_lookup_simplex_id :
    rawSimplex00.getObjVal? "simplex_id" = .ok (.number (String.ofList ['0'])) := by
  rfl

attribute [local simp] simplex00_lookup_simplex_id

theorem simplex00_lookup_vertex_ids :
    rawSimplex00.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3']), .number (String.ofList ['1']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex00_lookup_vertex_ids

theorem simplex00_lookup_physical_volume :
    rawSimplex00.getObjVal? "physical_volume" = .ok (.str (String.ofList ['3', '8', '7', '7', '3', '5', '6', '8', '0', '8', '5', '7', '7', '9', '4', '6', '8', '9', '1', '0', '1', '7', '4', '0', '8', '3', '2', '1', '9', '1', '1', '/', '1', '6', '8', '3', '1', '0', '3', '2', '2', '9', '1', '6', '5', '0', '3', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex00_lookup_physical_volume

theorem simplex00_lookup_mean_gap :
    rawSimplex00.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex00_lookup_mean_gap

theorem simplex00_lookup_factor_maxima :
    rawSimplex00.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex00_lookup_factor_maxima

theorem simplex00_lookup_gap_weighted_means :
    rawSimplex00.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['6', '9', '7', '3', '2', '9', '5', '8', '7', '/', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '2', '5', '7', '8', '1', '3', '1', '/', '8', '5', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '7', '9', '8', '4', '6', '1', '9', '3', '4', '9', '/', '7', '1', '4', '7', '9', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '1', '5', '7', '4', '8', '8', '3', '2', '1', '/', '2', '6', '4', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '7', '0', '5', '4', '6', '0', '8', '2', '9', '1', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '9', '4', '1', '1', '0', '7', '8', '0', '3', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '4', '6', '6', '9', '8', '8', '8', '1', '/', '5', '2', '9', '4', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '8', '0', '1', '7', '0', '9', '2', '1', '/', '7', '9', '4', '2', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '0', '2', '6', '7', '0', '5', '9', '9', '1', '/', '2', '6', '4', '7', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '4', '3', '3', '5', '9', '2', '3', '9', '/', '2', '3', '0', '5', '8', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex00_lookup_gap_weighted_means

theorem simplex00_lookup_max_bound :
    rawSimplex00.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '2', '4', '8', '6', '3', '7', '6', '6', '6', '6', '7', '2', '0', '8', '5', '5', '4', '5', '8', '2', '6', '2', '4', '2', '4', '7', '9', '5', '8', '2', '3', '3', '5', '7', '4', '3', '2', '0', '6', '5', '6', '8', '7', '5', '5', '2', '0', '0', '0', '0', '/', '2', '9', '0', '5', '0', '3', '7', '6', '4', '9', '1', '0', '1', '5', '8', '8', '6', '8', '5', '5', '9', '3', '5', '3', '5', '2', '3', '6', '0', '4', '9', '9', '2', '5', '0', '0', '1', '7', '9', '5', '4', '1', '6', '2', '6', '4', '9', '1', '2', '1', '3', '4', '6', '5', '7', '1', '1', '5', '2', '0', '8', '6', '9', '8', '0', '3', '4', '1'])) := by
  rfl

attribute [local simp] simplex00_lookup_max_bound

theorem simplex00_lookup_jensen_bound :
    rawSimplex00.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '7', '0', '8', '5', '6', '5', '3', '6', '5', '0', '1', '2', '6', '8', '5', '4', '6', '8', '9', '8', '0', '1', '8', '8', '8', '4', '5', '5', '8', '7', '5', '5', '8', '3', '2', '3', '4', '1', '2', '6', '0', '6', '5', '7', '0', '4', '8', '8', '4', '1', '1', '7', '6', '8', '7', '8', '0', '1', '7', '6', '9', '4', '8', '8', '3', '2', '7', '6', '3', '9', '0', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '5', '6', '3', '6', '2', '2', '2', '2', '7', '8', '5', '9', '8', '5', '7', '1', '8', '2', '7', '1', '6', '7', '0', '7', '5', '7', '6', '2', '0', '8', '6', '2', '8', '1', '1', '7', '8', '0', '3', '0', '3', '1', '1', '9', '3', '8', '0', '8', '2', '5', '0', '2', '9', '6', '2', '3', '8', '1', '9', '7', '5', '6', '9', '7', '9', '2', '3', '8', '1', '3', '8', '7', '3', '1', '3', '0', '9', '5', '2', '5', '2', '6', '8', '8', '0', '3', '9', '5', '3', '0', '2', '8', '0', '9', '0', '4', '3', '6', '7', '4', '1', '4', '3'])) := by
  rfl

attribute [local simp] simplex00_lookup_jensen_bound

theorem simplex00_lookup_max_floor_Q96 :
    rawSimplex00.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['3', '4', '0', '5', '3', '6', '9', '5', '6', '5', '7', '6'])) := by
  rfl

attribute [local simp] simplex00_lookup_max_floor_Q96

theorem simplex00_lookup_jensen_floor_Q96 :
    rawSimplex00.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['8', '6', '5', '7', '2', '3', '7', '7', '9', '0', '1', '4'])) := by
  rfl

attribute [local simp] simplex00_lookup_jensen_floor_Q96

theorem simplex00_decoded : decodeSimplex rawSimplex00 = .ok simplex00 := by
  unfold decodeSimplex simplex00
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex00_decoded

theorem simplex01_lookup_simplex_id :
    rawSimplex01.getObjVal? "simplex_id" = .ok (.number (String.ofList ['1'])) := by
  rfl

attribute [local simp] simplex01_lookup_simplex_id

theorem simplex01_lookup_vertex_ids :
    rawSimplex01.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['3']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_vertex_ids

theorem simplex01_lookup_physical_volume :
    rawSimplex01.getObjVal? "physical_volume" = .ok (.str (String.ofList ['8', '7', '3', '1', '5', '2', '8', '0', '3', '7', '5', '6', '3', '1', '0', '4', '7', '4', '1', '6', '9', '3', '6', '0', '8', '5', '4', '2', '7', '5', '0', '7', '6', '3', '/', '7', '4', '8', '0', '4', '5', '8', '7', '9', '6', '2', '8', '9', '0', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_physical_volume

theorem simplex01_lookup_mean_gap :
    rawSimplex01.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_mean_gap

theorem simplex01_lookup_factor_maxima :
    rawSimplex01.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '2', '3', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_factor_maxima

theorem simplex01_lookup_gap_weighted_means :
    rawSimplex01.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '9', '7', '9', '8', '3', '0', '9', '1', '/', '2', '4', '0', '1', '8', '7', '5', '0', '0', '0']), .str (String.ofList ['4', '9', '8', '6', '4', '8', '1', '1', '/', '6', '0', '0', '4', '6', '8', '7', '5', '0']), .str (String.ofList ['2', '9', '7', '3', '2', '3', '0', '6', '5', '7', '1', '7', '/', '1', '7', '8', '6', '9', '9', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '6', '2', '6', '4', '9', '8', '5', '7', '1', '/', '1', '9', '8', '5', '5', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '9', '2', '7', '2', '0', '3', '4', '4', '0', '3', '/', '1', '9', '8', '5', '5', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '7', '9', '4', '3', '0', '9', '0', '8', '1', '/', '1', '1', '9', '1', '3', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '9', '3', '3', '3', '7', '2', '1', '9', '9', '/', '1', '1', '9', '1', '3', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '0', '0', '1', '4', '5', '1', '8', '7', '9', '/', '5', '9', '5', '6', '6', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '8', '0', '0', '1', '9', '6', '5', '3', '1', '/', '5', '9', '5', '6', '6', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '3', '5', '6', '9', '2', '8', '1', '9', '/', '5', '7', '6', '4', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex01_lookup_gap_weighted_means

theorem simplex01_lookup_max_bound :
    rawSimplex01.getObjVal? "max_bound" = .ok (.str (String.ofList ['4', '1', '3', '5', '0', '6', '1', '7', '9', '1', '9', '9', '8', '2', '9', '9', '1', '4', '0', '8', '3', '9', '9', '7', '9', '2', '0', '1', '4', '1', '5', '6', '0', '9', '3', '8', '9', '4', '2', '3', '9', '1', '3', '8', '6', '1', '1', '2', '0', '0', '0', '0', '/', '1', '8', '9', '8', '7', '1', '7', '4', '1', '7', '7', '1', '3', '4', '5', '6', '6', '5', '7', '2', '5', '0', '6', '7', '6', '6', '2', '4', '8', '6', '9', '2', '3', '2', '0', '2', '7', '3', '1', '7', '2', '6', '5', '5', '3', '2', '6', '2', '2', '3', '1', '0', '2', '3', '3', '4', '0', '8', '6', '3', '3', '1', '3', '5', '9', '7'])) := by
  rfl

attribute [local simp] simplex01_lookup_max_bound

theorem simplex01_lookup_jensen_bound :
    rawSimplex01.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '7', '6', '5', '9', '0', '5', '4', '1', '8', '8', '4', '2', '4', '3', '0', '8', '5', '5', '1', '1', '6', '2', '0', '8', '1', '9', '4', '3', '7', '8', '7', '7', '8', '6', '5', '9', '0', '9', '5', '8', '4', '7', '6', '0', '8', '6', '9', '6', '9', '8', '0', '5', '8', '7', '0', '0', '5', '8', '1', '4', '2', '0', '7', '2', '4', '2', '6', '0', '6', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '4', '9', '0', '4', '4', '8', '4', '9', '9', '6', '1', '9', '3', '2', '3', '8', '7', '9', '8', '2', '0', '3', '1', '2', '0', '0', '2', '4', '2', '5', '9', '3', '7', '5', '9', '9', '6', '3', '2', '6', '5', '4', '7', '7', '9', '3', '0', '5', '9', '4', '7', '9', '9', '7', '2', '9', '0', '7', '2', '5', '1', '2', '5', '6', '4', '6', '8', '8', '9', '5', '7', '9', '7', '4', '8', '7', '8', '4', '7', '6', '8', '9', '7', '0', '2', '1', '8', '0', '2', '0', '7', '9', '6', '2', '9', '9', '5', '7'])) := by
  rfl

attribute [local simp] simplex01_lookup_jensen_bound

theorem simplex01_lookup_max_floor_Q96 :
    rawSimplex01.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '7', '2', '5', '4', '4', '5', '5', '2', '7', '6', '3', '1', '4', '7', '3'])) := by
  rfl

attribute [local simp] simplex01_lookup_max_floor_Q96

theorem simplex01_lookup_jensen_floor_Q96 :
    rawSimplex01.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '4', '6', '8', '1', '0', '6', '3', '1', '8', '8', '7', '3', '9', '0', '0'])) := by
  rfl

attribute [local simp] simplex01_lookup_jensen_floor_Q96

theorem simplex01_decoded : decodeSimplex rawSimplex01 = .ok simplex01 := by
  unfold decodeSimplex simplex01
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex01_decoded

theorem simplex02_lookup_simplex_id :
    rawSimplex02.getObjVal? "simplex_id" = .ok (.number (String.ofList ['2'])) := by
  rfl

attribute [local simp] simplex02_lookup_simplex_id

theorem simplex02_lookup_vertex_ids :
    rawSimplex02.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['6']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_vertex_ids

theorem simplex02_lookup_physical_volume :
    rawSimplex02.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '6', '7', '6', '5', '8', '7', '4', '9', '9', '6', '2', '1', '7', '1', '8', '6', '9', '6', '7', '1', '7', '5', '3', '1', '1', '8', '7', '2', '4', '3', '/', '8', '6', '8', '6', '9', '8', '4', '4', '0', '8', '5', '9', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex02_lookup_physical_volume

theorem simplex02_lookup_mean_gap :
    rawSimplex02.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex02_lookup_mean_gap

theorem simplex02_lookup_factor_maxima :
    rawSimplex02.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_factor_maxima

theorem simplex02_lookup_gap_weighted_means :
    rawSimplex02.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '5', '6', '4', '1', '2', '7', '/', '4', '2', '8', '9', '0', '6', '2', '5']), .str (String.ofList ['5', '7', '4', '4', '7', '7', '9', '/', '6', '8', '6', '2', '5', '0', '0', '0']), .str (String.ofList ['1', '3', '7', '0', '8', '0', '4', '3', '7', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '5', '4', '6', '5', '0', '1', '9', '/', '1', '0', '6', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '1', '0', '6', '7', '7', '8', '9', '3', '/', '3', '2', '0', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '7', '7', '8', '7', '6', '8', '1', '/', '5', '4', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '3', '8', '4', '2', '3', '8', '7', '/', '1', '0', '9', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '2', '4', '6', '2', '0', '3', '1', '/', '2', '7', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '0', '3', '8', '3', '6', '0', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '5', '5', '0', '8', '1', '4', '1', '/', '8', '2', '3', '5', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex02_lookup_gap_weighted_means

theorem simplex02_lookup_max_bound :
    rawSimplex02.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '8', '4', '9', '8', '8', '4', '4', '6', '6', '9', '6', '5', '0', '0', '3', '7', '8', '6', '3', '8', '6', '1', '0', '9', '6', '8', '0', '8', '4', '4', '6', '5', '7', '1', '9', '2', '3', '3', '7', '4', '0', '8', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7'])) := by
  rfl

attribute [local simp] simplex02_lookup_max_bound

theorem simplex02_lookup_jensen_bound :
    rawSimplex02.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '4', '2', '9', '7', '2', '3', '4', '2', '1', '8', '0', '3', '7', '0', '6', '1', '4', '7', '8', '9', '2', '7', '5', '4', '7', '7', '2', '0', '2', '6', '0', '9', '5', '7', '2', '4', '2', '3', '0', '3', '1', '5', '1', '0', '8', '4', '0', '9', '7', '1', '7', '9', '6', '8', '7', '5', '0', '0', '0', '0', '0', '0', '/', '1', '5', '3', '3', '2', '8', '2', '9', '8', '9', '5', '1', '1', '3', '9', '3', '6', '9', '9', '9', '6', '7', '2', '3', '2', '5', '5', '4', '9', '4', '5', '0', '1', '2', '7', '3', '4', '1', '8', '0', '8', '6', '6', '9', '9', '3', '4', '6', '1', '5', '7', '1', '3', '6', '6', '5', '3', '2', '7', '8', '3', '4', '2', '1', '5', '9', '9', '8', '9', '2', '5', '0', '8', '9', '8', '3', '5', '4', '7', '9'])) := by
  rfl

attribute [local simp] simplex02_lookup_jensen_bound

theorem simplex02_lookup_max_floor_Q96 :
    rawSimplex02.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '5', '2', '9', '4', '6', '4', '5', '0', '7', '4'])) := by
  rfl

attribute [local simp] simplex02_lookup_max_floor_Q96

theorem simplex02_lookup_jensen_floor_Q96 :
    rawSimplex02.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '8', '7', '7', '0', '0', '7', '9', '5', '4', '8'])) := by
  rfl

attribute [local simp] simplex02_lookup_jensen_floor_Q96

theorem simplex02_decoded : decodeSimplex rawSimplex02 = .ok simplex02 := by
  unfold decodeSimplex simplex02
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex02_decoded

theorem simplex03_lookup_simplex_id :
    rawSimplex03.getObjVal? "simplex_id" = .ok (.number (String.ofList ['3'])) := by
  rfl

attribute [local simp] simplex03_lookup_simplex_id

theorem simplex03_lookup_vertex_ids :
    rawSimplex03.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['7']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_vertex_ids

theorem simplex03_lookup_physical_volume :
    rawSimplex03.getObjVal? "physical_volume" = .ok (.str (String.ofList ['6', '7', '0', '6', '1', '3', '5', '3', '3', '5', '7', '5', '3', '7', '9', '1', '8', '9', '8', '5', '5', '5', '9', '1', '9', '0', '9', '8', '6', '1', '3', '/', '3', '4', '7', '4', '7', '9', '3', '7', '6', '3', '4', '3', '7', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_physical_volume

theorem simplex03_lookup_mean_gap :
    rawSimplex03.getObjVal? "mean_gap" = .ok (.str (String.ofList ['2', '3', '4', '3', '1', '/', '6', '8', '6', '2', '5', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex03_lookup_mean_gap

theorem simplex03_lookup_factor_maxima :
    rawSimplex03.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '9', '6', '8', '6', '3', '/', '5', '6', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_factor_maxima

theorem simplex03_lookup_gap_weighted_means :
    rawSimplex03.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '1', '9', '3', '4', '5', '8', '8', '9', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '6', '0', '8', '5', '3', '8', '6', '6', '9', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '9', '8', '6', '3', '4', '3', '9', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0']), .str (String.ofList ['1', '2', '7', '7', '0', '1', '4', '1', '9', '/', '1', '2', '8', '1', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '1', '0', '4', '2', '5', '8', '7', '/', '4', '2', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '4', '4', '5', '1', '4', '1', '3', '3', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '8', '4', '4', '8', '3', '9', '1', '1', '/', '3', '8', '4', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '1', '5', '4', '3', '/', '2', '4', '0', '1', '8', '7', '5', '0']), .str (String.ofList ['5', '7', '0', '7', '3', '9', '7', '3', '/', '1', '9', '2', '1', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '1', '7', '4', '2', '3', '/', '1', '8', '0', '1', '4', '0', '6', '2', '5', '0'])]) := by
  rfl

attribute [local simp] simplex03_lookup_gap_weighted_means

theorem simplex03_lookup_max_bound :
    rawSimplex03.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '9', '8', '4', '9', '2', '4', '9', '0', '9', '4', '4', '5', '2', '0', '8', '3', '9', '8', '9', '8', '4', '1', '3', '7', '0', '2', '5', '0', '9', '3', '2', '9', '7', '4', '6', '5', '6', '6', '8', '4', '0', '3', '2', '0', '0', '0', '0', '/', '5', '5', '1', '2', '4', '4', '0', '9', '0', '8', '3', '4', '2', '7', '0', '7', '1', '6', '9', '6', '7', '8', '5', '5', '9', '3', '7', '7', '4', '6', '0', '7', '0', '7', '5', '4', '0', '8', '0', '0', '5', '0', '7', '7', '3', '2', '2', '1', '0', '5', '3', '7', '6', '2', '1', '6', '4', '1', '4', '6', '8', '3', '1', '4', '7'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_bound

theorem simplex03_lookup_jensen_bound :
    rawSimplex03.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '5', '8', '0', '4', '0', '4', '0', '6', '3', '7', '1', '9', '8', '7', '0', '9', '8', '4', '7', '7', '4', '2', '1', '5', '8', '0', '6', '5', '9', '0', '7', '4', '3', '2', '2', '9', '4', '6', '4', '0', '8', '2', '2', '4', '7', '1', '5', '0', '0', '6', '9', '3', '2', '1', '9', '9', '2', '1', '8', '7', '5', '0', '/', '1', '6', '9', '4', '5', '0', '9', '4', '2', '1', '6', '0', '7', '7', '9', '3', '4', '3', '3', '9', '0', '7', '4', '5', '6', '6', '7', '9', '2', '9', '5', '3', '2', '1', '0', '3', '6', '0', '2', '0', '3', '0', '2', '7', '7', '0', '9', '3', '1', '2', '7', '7', '4', '5', '9', '9', '8', '5', '9', '2', '4', '5', '6', '8', '4', '5', '1', '3', '7', '1', '5', '2', '8', '7', '7', '6', '6', '6', '3', '3'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_bound

theorem simplex03_lookup_max_floor_Q96 :
    rawSimplex03.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '8', '5', '2', '8', '5', '5', '1', '3', '1', '1', '2'])) := by
  rfl

attribute [local simp] simplex03_lookup_max_floor_Q96

theorem simplex03_lookup_jensen_floor_Q96 :
    rawSimplex03.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['7', '3', '8', '9', '3', '0', '7', '3', '9', '4', '9', '2'])) := by
  rfl

attribute [local simp] simplex03_lookup_jensen_floor_Q96

theorem simplex03_decoded : decodeSimplex rawSimplex03 = .ok simplex03 := by
  unfold decodeSimplex simplex03
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex03_decoded

theorem simplex04_lookup_simplex_id :
    rawSimplex04.getObjVal? "simplex_id" = .ok (.number (String.ofList ['4'])) := by
  rfl

attribute [local simp] simplex04_lookup_simplex_id

theorem simplex04_lookup_vertex_ids :
    rawSimplex04.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['9']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_vertex_ids

theorem simplex04_lookup_physical_volume :
    rawSimplex04.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '3', '9', '5', '0', '8', '6', '6', '3', '0', '0', '3', '0', '1', '6', '3', '1', '6', '6', '0', '8', '5', '0', '1', '1', '2', '8', '1', '9', '3', '7', '2', '8', '9', '0', '7', '/', '4', '4', '3', '4', '4', '9', '8', '7', '0', '7', '6', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_physical_volume

theorem simplex04_lookup_mean_gap :
    rawSimplex04.getObjVal? "mean_gap" = .ok (.str (String.ofList ['1', '1', '9', '9', '6', '4', '8', '9', '/', '1', '8', '3', '9', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex04_lookup_mean_gap

theorem simplex04_lookup_factor_maxima :
    rawSimplex04.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '0', '7', '8', '1', '3', '7', '/', '2', '4', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_factor_maxima

theorem simplex04_lookup_gap_weighted_means :
    rawSimplex04.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['1', '2', '7', '5', '2', '1', '7', '0', '6', '7', '0', '1', '9', '0', '9', '2', '3', '3', '9', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '8', '8', '8', '2', '7', '0', '7', '2', '9', '8', '9', '7', '1', '5', '7', '3', '7', '/', '1', '5', '4', '4', '4', '3', '3', '9', '9', '2', '1', '0', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '8', '5', '8', '3', '4', '4', '4', '7', '0', '2', '2', '0', '9', '0', '1', '6', '6', '7', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '0', '9', '0', '7', '1', '8', '2', '3', '1', '2', '3', '5', '6', '2', '4', '0', '7', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '9', '8', '8', '1', '6', '0', '7', '3', '6', '6', '4', '8', '1', '4', '0', '1', '/', '5', '1', '4', '8', '1', '1', '3', '3', '0', '7', '0', '1', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '0', '3', '0', '8', '1', '0', '7', '8', '2', '3', '2', '0', '2', '4', '9', '8', '7', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['9', '5', '4', '8', '3', '0', '9', '0', '1', '0', '7', '3', '3', '5', '7', '6', '0', '1', '/', '3', '0', '8', '8', '8', '6', '7', '9', '8', '4', '2', '0', '9', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '2', '6', '7', '6', '4', '5', '3', '1', '2', '3', '5', '0', '5', '9', '7', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '2', '7', '9', '3', '8', '9', '8', '0', '5', '2', '9', '7', '3', '9', '0', '5', '7', '/', '7', '7', '2', '2', '1', '6', '9', '9', '6', '0', '5', '2', '2', '5', '0', '0', '0', '0', '0']), .str (String.ofList ['6', '6', '0', '4', '9', '6', '4', '1', '4', '0', '6', '9', '7', '4', '9', '6', '2', '9', '/', '2', '3', '1', '6', '6', '5', '0', '9', '8', '8', '1', '5', '6', '7', '5', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex04_lookup_gap_weighted_means

theorem simplex04_lookup_max_bound :
    rawSimplex04.getObjVal? "max_bound" = .ok (.str (String.ofList ['7', '9', '3', '9', '7', '0', '5', '4', '7', '4', '3', '4', '9', '5', '5', '0', '9', '3', '3', '3', '5', '2', '0', '5', '3', '6', '3', '4', '9', '2', '6', '7', '4', '3', '5', '3', '2', '5', '5', '3', '6', '6', '6', '5', '0', '7', '5', '7', '1', '2', '0', '0', '0', '0', '0', '/', '4', '1', '2', '4', '2', '1', '3', '4', '8', '3', '8', '5', '6', '5', '6', '1', '0', '9', '9', '7', '7', '9', '9', '5', '8', '7', '2', '9', '3', '8', '0', '1', '9', '5', '8', '3', '9', '2', '5', '7', '8', '2', '1', '4', '5', '3', '1', '8', '8', '7', '8', '0', '7', '6', '8', '7', '4', '4', '1', '1', '8', '6', '3', '2', '4', '2', '0', '2', '9'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_bound

theorem simplex04_lookup_jensen_bound :
    rawSimplex04.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['2', '5', '4', '3', '9', '4', '4', '6', '1', '4', '6', '7', '1', '2', '8', '3', '5', '8', '1', '1', '1', '9', '1', '6', '8', '5', '2', '3', '1', '0', '6', '2', '4', '6', '2', '5', '7', '4', '5', '7', '7', '3', '2', '2', '8', '3', '4', '8', '5', '2', '6', '2', '0', '1', '4', '6', '3', '9', '6', '1', '3', '5', '8', '1', '4', '3', '3', '0', '9', '9', '1', '6', '7', '8', '7', '7', '4', '0', '1', '8', '6', '3', '7', '9', '6', '3', '1', '9', '5', '4', '3', '2', '5', '0', '4', '4', '0', '7', '8', '1', '7', '6', '3', '5', '4', '0', '3', '9', '8', '8', '0', '9', '0', '6', '3', '6', '7', '5', '8', '6', '1', '8', '1', '8', '2', '1', '4', '1', '5', '5', '1', '5', '7', '8', '5', '1', '8', '2', '1', '6', '3', '7', '9', '6', '6', '3', '7', '4', '5', '3', '1', '2', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '5', '0', '6', '3', '2', '6', '2', '2', '2', '5', '9', '3', '6', '6', '2', '0', '2', '0', '6', '2', '9', '9', '2', '6', '3', '1', '7', '7', '3', '2', '4', '0', '6', '6', '4', '9', '8', '9', '4', '6', '1', '2', '1', '7', '2', '1', '4', '8', '9', '1', '7', '8', '8', '9', '9', '9', '0', '1', '5', '4', '2', '3', '1', '5', '9', '1', '1', '1', '4', '2', '7', '3', '9', '4', '9', '4', '3', '8', '6', '0', '5', '2', '7', '6', '7', '0', '9', '4', '8', '7', '7', '5', '3', '6', '8', '2', '9', '1', '2', '7', '1', '4', '2', '2', '4', '0', '8', '9', '1', '0', '0', '8', '0', '2', '1', '8', '3', '7', '1', '6', '7', '8', '2', '1', '1', '2', '7', '0', '7', '3', '2', '5', '6', '6', '5', '9', '4', '1', '5', '2', '3', '3', '2', '5', '5', '5', '4', '5', '7', '8', '6', '1', '7', '1', '1', '3', '9', '3', '4', '4', '0', '5', '5', '6', '2', '4', '6', '4', '2', '2', '4', '6', '6', '9', '3'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_bound

theorem simplex04_lookup_max_floor_Q96 :
    rawSimplex04.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '5', '2', '5', '2', '5', '6', '3', '3', '8', '2', '0', '7', '1', '4', '8'])) := by
  rfl

attribute [local simp] simplex04_lookup_max_floor_Q96

theorem simplex04_lookup_jensen_floor_Q96 :
    rawSimplex04.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['3', '9', '8', '0', '6', '7', '5', '8', '6', '3', '9', '9', '1', '6', '2', '2'])) := by
  rfl

attribute [local simp] simplex04_lookup_jensen_floor_Q96

theorem simplex04_decoded : decodeSimplex rawSimplex04 = .ok simplex04 := by
  unfold decodeSimplex simplex04
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex04_decoded

theorem simplex05_lookup_simplex_id :
    rawSimplex05.getObjVal? "simplex_id" = .ok (.number (String.ofList ['5'])) := by
  rfl

attribute [local simp] simplex05_lookup_simplex_id

theorem simplex05_lookup_vertex_ids :
    rawSimplex05.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '3']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_vertex_ids

theorem simplex05_lookup_physical_volume :
    rawSimplex05.getObjVal? "physical_volume" = .ok (.str (String.ofList ['1', '0', '7', '2', '9', '1', '2', '9', '6', '4', '9', '4', '4', '1', '1', '9', '2', '5', '2', '3', '7', '2', '3', '0', '4', '3', '0', '8', '0', '3', '2', '5', '3', '/', '6', '1', '0', '6', '5', '2', '2', '8', '1', '0', '5', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_physical_volume

theorem simplex05_lookup_mean_gap :
    rawSimplex05.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex05_lookup_mean_gap

theorem simplex05_lookup_factor_maxima :
    rawSimplex05.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '0', '6', '1', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_factor_maxima

theorem simplex05_lookup_gap_weighted_means :
    rawSimplex05.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['2', '7', '9', '3', '3', '6', '6', '3', '7', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '1', '3', '0', '9', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '2', '1', '9', '4', '2', '2', '1', '0', '8', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '1', '3', '8', '2', '4', '5', '0', '1', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '3', '0', '5', '3', '8', '3', '1', '6', '9', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '5', '2', '0', '8', '2', '4', '0', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '6', '0', '7', '8', '2', '9', '2', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '4', '4', '1', '2', '9', '4', '3', '8', '1', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex05_lookup_gap_weighted_means

theorem simplex05_lookup_max_bound :
    rawSimplex05.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '6', '8', '7', '0', '2', '4', '1', '6', '3', '4', '0', '9', '5', '6', '7', '2', '1', '4', '1', '8', '1', '1', '3', '4', '5', '9', '1', '9', '5', '7', '2', '6', '3', '0', '8', '9', '4', '8', '5', '7', '4', '2', '0', '8', '0', '0', '0', '0', '0', '/', '5', '6', '4', '7', '3', '8', '7', '9', '8', '9', '6', '3', '7', '9', '2', '5', '7', '4', '2', '3', '9', '6', '0', '9', '2', '4', '2', '8', '2', '7', '3', '1', '2', '6', '7', '9', '1', '3', '0', '7', '8', '2', '4', '8', '6', '3', '3', '7', '7', '7', '3', '5', '6', '9', '4', '0', '9', '3', '4', '1', '4', '3', '9', '5', '7', '6', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_bound

theorem simplex05_lookup_jensen_bound :
    rawSimplex05.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['1', '0', '7', '1', '0', '3', '1', '6', '5', '9', '6', '1', '1', '3', '4', '8', '3', '3', '4', '8', '0', '5', '8', '6', '2', '8', '7', '3', '0', '5', '7', '6', '9', '2', '1', '3', '3', '9', '9', '7', '7', '0', '2', '7', '9', '8', '9', '6', '7', '1', '6', '8', '6', '7', '0', '6', '6', '8', '7', '0', '7', '5', '9', '4', '2', '4', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '3', '8', '3', '9', '3', '0', '7', '2', '6', '5', '9', '9', '4', '2', '2', '5', '6', '4', '5', '8', '0', '4', '0', '9', '3', '2', '1', '7', '9', '8', '7', '4', '1', '3', '2', '0', '8', '3', '3', '5', '6', '5', '9', '5', '3', '9', '8', '0', '0', '6', '9', '0', '1', '7', '7', '4', '2', '9', '0', '8', '8', '6', '3', '4', '7', '3', '1', '6', '4', '1', '9', '2', '6', '8', '1', '9', '0', '1', '5', '9', '2', '6', '9', '1', '6', '5', '5', '3', '8', '1', '0', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_bound

theorem simplex05_lookup_max_floor_Q96 :
    rawSimplex05.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '6', '6', '7', '5', '4', '7', '6', '9', '2', '7'])) := by
  rfl

attribute [local simp] simplex05_lookup_max_floor_Q96

theorem simplex05_lookup_jensen_floor_Q96 :
    rawSimplex05.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '1', '3', '1', '5', '1', '1', '4', '0', '8', '3', '8'])) := by
  rfl

attribute [local simp] simplex05_lookup_jensen_floor_Q96

theorem simplex05_decoded : decodeSimplex rawSimplex05 = .ok simplex05 := by
  unfold decodeSimplex simplex05
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex05_decoded

theorem simplex06_lookup_simplex_id :
    rawSimplex06.getObjVal? "simplex_id" = .ok (.number (String.ofList ['6'])) := by
  rfl

attribute [local simp] simplex06_lookup_simplex_id

theorem simplex06_lookup_vertex_ids :
    rawSimplex06.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '4']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_vertex_ids

theorem simplex06_lookup_physical_volume :
    rawSimplex06.getObjVal? "physical_volume" = .ok (.str (String.ofList ['4', '2', '9', '1', '5', '1', '4', '4', '8', '8', '8', '1', '9', '4', '1', '8', '7', '3', '8', '0', '6', '4', '3', '0', '5', '0', '6', '8', '2', '0', '5', '2', '3', '/', '2', '4', '4', '2', '6', '0', '9', '1', '2', '4', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_physical_volume

theorem simplex06_lookup_mean_gap :
    rawSimplex06.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex06_lookup_mean_gap

theorem simplex06_lookup_factor_maxima :
    rawSimplex06.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['5', '1', '5', '5', '8', '1', '/', '1', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_factor_maxima

theorem simplex06_lookup_gap_weighted_means :
    rawSimplex06.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['3', '4', '9', '1', '7', '1', '0', '0', '7', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '5', '5', '3', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '1', '0', '9', '7', '1', '0', '8', '4', '3', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '4', '0', '1', '9', '7', '3', '0', '9', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '0', '3', '4', '7', '0', '3', '2', '6', '3', '/', '3', '3', '7', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '6', '0', '4', '1', '2', '7', '1', '7', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '2', '3', '0', '3', '8', '9', '3', '5', '3', '/', '4', '2', '2', '1', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['3', '6', '0', '3', '2', '3', '8', '0', '6', '3', '/', '1', '2', '6', '6', '3', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex06_lookup_gap_weighted_means

theorem simplex06_lookup_max_bound :
    rawSimplex06.getObjVal? "max_bound" = .ok (.str (String.ofList ['5', '2', '7', '1', '7', '8', '1', '7', '6', '1', '4', '3', '8', '7', '7', '3', '9', '8', '2', '6', '6', '0', '1', '9', '4', '9', '3', '0', '4', '8', '8', '2', '7', '7', '2', '1', '5', '8', '7', '0', '9', '7', '6', '0', '0', '0', '0', '0', '/', '1', '7', '6', '4', '8', '0', '4', '5', '6', '3', '3', '3', '2', '9', '9', '6', '1', '3', '5', '2', '3', '0', '8', '4', '0', '9', '3', '6', '1', '9', '2', '2', '3', '1', '7', '3', '9', '4', '2', '3', '8', '1', '0', '7', '9', '7', '8', '2', '7', '4', '3', '1', '7', '9', '9', '2', '8', '8', '2', '2', '9', '9', '4', '4', '7', '3'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_bound

theorem simplex06_lookup_jensen_bound :
    rawSimplex06.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['8', '3', '6', '7', '1', '6', '7', '0', '0', '8', '5', '1', '9', '9', '6', '0', '9', '7', '6', '3', '7', '2', '4', '7', '0', '1', '5', '8', '8', '7', '7', '3', '9', '2', '3', '7', '1', '0', '1', '7', '4', '5', '4', '1', '7', '5', '7', '9', '1', '5', '8', '7', '4', '4', '8', '8', '9', '7', '6', '5', '6', '3', '2', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '1', '0', '7', '9', '2', '8', '6', '9', '5', '0', '9', '4', '6', '2', '4', '3', '3', '9', '0', '1', '0', '5', '7', '5', '1', '0', '5', '9', '6', '9', '8', '7', '1', '4', '2', '1', '6', '1', '2', '1', '4', '4', '6', '5', '3', '0', '1', '1', '3', '4', '9', '8', '5', '2', '2', '6', '0', '7', '8', '5', '0', '2', '0', '9', '0', '7', '9', '3', '1', '3', '9', '7', '5', '3', '0', '6', '8', '8', '0', '3', '5', '4', '9', '6', '5', '8', '7', '6', '8', '3', '6', '9'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_bound

theorem simplex06_lookup_max_floor_Q96 :
    rawSimplex06.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['2', '3', '6', '6', '6', '8', '4', '6', '2', '2', '2', '6'])) := by
  rfl

attribute [local simp] simplex06_lookup_max_floor_Q96

theorem simplex06_lookup_jensen_floor_Q96 :
    rawSimplex06.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['6', '1', '4', '2', '1', '5', '9', '5', '7', '0', '7', '5'])) := by
  rfl

attribute [local simp] simplex06_lookup_jensen_floor_Q96

theorem simplex06_decoded : decodeSimplex rawSimplex06 = .ok simplex06 := by
  unfold decodeSimplex simplex06
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex06_decoded

theorem simplex07_lookup_simplex_id :
    rawSimplex07.getObjVal? "simplex_id" = .ok (.number (String.ofList ['7'])) := by
  rfl

attribute [local simp] simplex07_lookup_simplex_id

theorem simplex07_lookup_vertex_ids :
    rawSimplex07.getObjVal? "vertex_ids" = .ok (.arr [.number (String.ofList ['1', '5']), .number (String.ofList ['1', '2']), .number (String.ofList ['1', '1']), .number (String.ofList ['1', '0']), .number (String.ofList ['8']), .number (String.ofList ['5']), .number (String.ofList ['4']), .number (String.ofList ['2']), .number (String.ofList ['0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_vertex_ids

theorem simplex07_lookup_physical_volume :
    rawSimplex07.getObjVal? "physical_volume" = .ok (.str (String.ofList ['2', '4', '0', '1', '4', '5', '4', '6', '3', '7', '6', '1', '6', '3', '8', '8', '5', '2', '8', '9', '8', '5', '6', '3', '6', '5', '6', '9', '8', '4', '7', '0', '8', '3', '1', '0', '7', '/', '1', '7', '4', '9', '9', '2', '8', '9', '2', '4', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_physical_volume

theorem simplex07_lookup_mean_gap :
    rawSimplex07.getObjVal? "mean_gap" = .ok (.str (String.ofList ['9', '3', '7', '2', '1', '/', '3', '0', '1', '5', '0', '0', '0', '0', '0'])) := by
  rfl

attribute [local simp] simplex07_lookup_mean_gap

theorem simplex07_lookup_factor_maxima :
    rawSimplex07.getObjVal? "factor_maxima" = .ok (.arr [.str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '4', '8', '4', '3', '3', '1', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '3', '2', '8', '0', '7', '3', '/', '1', '0', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '9', '8', '4', '3', '0', '7', '/', '2', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '6', '4', '2', '1', '8', '8', '7', '/', '2', '6', '8', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '1', '8', '5', '9', '/', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '1', '8', '3', '/', '3', '7', '5', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '4', '7', '/', '3', '6', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '1', '7', '1', '8', '2', '3', '/', '3', '6', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_factor_maxima

theorem simplex07_lookup_gap_weighted_means :
    rawSimplex07.getObjVal? "gap_weighted_means" = .ok (.arr [.str (String.ofList ['6', '9', '8', '3', '4', '2', '4', '3', '6', '7', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '0', '3', '0', '6', '5', '9', '7', '5', '1', '/', '8', '4', '4', '2', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '4', '3', '8', '8', '4', '2', '5', '2', '9', '/', '5', '0', '6', '5', '2', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['2', '3', '1', '6', '3', '4', '1', '5', '3', '/', '2', '3', '4', '5', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '3', '6', '4', '6', '8', '7', '6', '9', '/', '1', '4', '0', '7', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '8', '4', '1', '7', '2', '0', '1', '0', '7', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['1', '7', '5', '3', '8', '0', '9', '8', '0', '9', '/', '5', '6', '2', '8', '0', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['8', '5', '4', '9', '2', '7', '3', '3', '/', '2', '8', '1', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['4', '9', '2', '1', '5', '4', '8', '9', '7', '/', '1', '6', '8', '8', '4', '0', '0', '0', '0', '0', '0']), .str (String.ofList ['7', '2', '0', '6', '4', '8', '0', '3', '4', '7', '/', '2', '5', '3', '2', '6', '0', '0', '0', '0', '0', '0', '0'])]) := by
  rfl

attribute [local simp] simplex07_lookup_gap_weighted_means

theorem simplex07_lookup_max_bound :
    rawSimplex07.getObjVal? "max_bound" = .ok (.str (String.ofList ['1', '8', '4', '3', '7', '4', '6', '6', '5', '2', '9', '1', '4', '0', '3', '7', '1', '4', '0', '0', '7', '0', '9', '1', '4', '8', '2', '5', '9', '3', '3', '9', '3', '4', '3', '9', '4', '3', '3', '6', '4', '3', '6', '2', '2', '4', '0', '0', '0', '0', '0', '/', '7', '9', '0', '2', '0', '4', '8', '6', '7', '8', '6', '2', '4', '7', '7', '9', '5', '3', '1', '4', '1', '1', '5', '0', '9', '2', '7', '0', '7', '2', '5', '2', '0', '3', '8', '5', '5', '8', '0', '5', '7', '6', '9', '5', '6', '1', '5', '6', '2', '6', '4', '8', '6', '6', '5', '6', '9', '7', '1', '0', '8', '4', '6', '9'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_bound

theorem simplex07_lookup_jensen_bound :
    rawSimplex07.getObjVal? "jensen_bound" = .ok (.str (String.ofList ['5', '1', '9', '8', '4', '7', '2', '5', '2', '4', '9', '6', '9', '1', '8', '2', '9', '0', '5', '6', '5', '5', '1', '5', '1', '8', '8', '9', '1', '8', '6', '5', '0', '4', '0', '6', '0', '7', '4', '6', '9', '1', '8', '1', '7', '7', '8', '4', '0', '8', '8', '3', '2', '9', '6', '7', '6', '7', '7', '8', '9', '5', '1', '6', '8', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '/', '8', '6', '0', '9', '0', '9', '1', '8', '1', '0', '4', '5', '8', '3', '6', '0', '8', '0', '6', '1', '4', '2', '2', '5', '7', '5', '6', '0', '9', '0', '7', '5', '5', '4', '8', '9', '6', '6', '3', '1', '3', '2', '3', '7', '9', '7', '6', '0', '0', '0', '1', '1', '4', '2', '5', '8', '0', '7', '8', '6', '7', '8', '0', '3', '9', '7', '3', '8', '0', '4', '2', '8', '9', '0', '5', '5', '0', '7', '5', '7', '4', '1', '9', '5', '2', '4', '2', '8', '9'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_bound

theorem simplex07_lookup_max_floor_Q96 :
    rawSimplex07.getObjVal? "max_floor_Q96" = .ok (.str (String.ofList ['1', '8', '4', '8', '5', '9', '2', '2', '4', '9', '8', '4', '7', '1', '1', '7'])) := by
  rfl

attribute [local simp] simplex07_lookup_max_floor_Q96

theorem simplex07_lookup_jensen_floor_Q96 :
    rawSimplex07.getObjVal? "jensen_floor_Q96" = .ok (.str (String.ofList ['4', '7', '8', '4', '0', '7', '5', '1', '9', '7', '5', '0', '0', '6', '3', '1'])) := by
  rfl

attribute [local simp] simplex07_lookup_jensen_floor_Q96

theorem simplex07_decoded : decodeSimplex rawSimplex07 = .ok simplex07 := by
  unfold decodeSimplex simplex07
  simp [rationalField, rationalArrayField]

attribute [local simp] simplex07_decoded

theorem simplices_mapped : rawSimplicesItems.toArray.mapM decodeSimplex = .ok simplices := by
  unfold rawSimplicesItems simplices
  simp

attribute [local simp] simplices_mapped

theorem physicalVolume_field : rationalField rawRoot "physical_volume" = .ok physicalVolume := by
  unfold rationalField physicalVolume
  simp [rawPhysicalVolume]

attribute [local simp] physicalVolume_field

theorem integralGap_field : rationalField rawRoot "integral_gap" = .ok integralGap := by
  unfold rationalField integralGap
  simp [rawIntegralGap]

attribute [local simp] integralGap_field

theorem rawRoot_decoded : decodeCell rawRoot = .ok cell00Payload := by
  unfold decodeCell cell00Payload
  simp [rawActive8, rawVertices, rawVertexValues, rawFaceLedger, rawSimplices]

attribute [local simp] rawRoot_decoded

end ImbalancedChen.P2Saving16Cell00FieldDecode
