import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryCore
import ImbalancedChen.P1HistoricalFifthTypedArchiveShape
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlock000
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks001010
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks011020
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks021030
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks031040
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks041050
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks051060
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks061070
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks071080
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks081090
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks091100
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks101110
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks111120
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks121130
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks131140
import ImbalancedChen.P1HistoricalFifthTypedBaseGeometryBlocks141142

/-! Existing pure all-row lower-key theorem, extracted unchanged.
Independent interface using the accepted table shape and per-block bounds. -/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTypedArchiveShape

theorem rows_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList, LowerKeyBounds row := by
  intro row hrow
  rw [rows_toList_order] at hrow
  obtain ⟨block, hblock, hrow⟩ := List.mem_flatMap.mp hrow
  rw [block_order] at hblock
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock
  · subst block
    exact block000_lower_key_bounds row hrow
  · subst block
    exact block001_lower_key_bounds row hrow
  · subst block
    exact block002_lower_key_bounds row hrow
  · subst block
    exact block003_lower_key_bounds row hrow
  · subst block
    exact block004_lower_key_bounds row hrow
  · subst block
    exact block005_lower_key_bounds row hrow
  · subst block
    exact block006_lower_key_bounds row hrow
  · subst block
    exact block007_lower_key_bounds row hrow
  · subst block
    exact block008_lower_key_bounds row hrow
  · subst block
    exact block009_lower_key_bounds row hrow
  · subst block
    exact block010_lower_key_bounds row hrow
  · subst block
    exact block011_lower_key_bounds row hrow
  · subst block
    exact block012_lower_key_bounds row hrow
  · subst block
    exact block013_lower_key_bounds row hrow
  · subst block
    exact block014_lower_key_bounds row hrow
  · subst block
    exact block015_lower_key_bounds row hrow
  · subst block
    exact block016_lower_key_bounds row hrow
  · subst block
    exact block017_lower_key_bounds row hrow
  · subst block
    exact block018_lower_key_bounds row hrow
  · subst block
    exact block019_lower_key_bounds row hrow
  · subst block
    exact block020_lower_key_bounds row hrow
  · subst block
    exact block021_lower_key_bounds row hrow
  · subst block
    exact block022_lower_key_bounds row hrow
  · subst block
    exact block023_lower_key_bounds row hrow
  · subst block
    exact block024_lower_key_bounds row hrow
  · subst block
    exact block025_lower_key_bounds row hrow
  · subst block
    exact block026_lower_key_bounds row hrow
  · subst block
    exact block027_lower_key_bounds row hrow
  · subst block
    exact block028_lower_key_bounds row hrow
  · subst block
    exact block029_lower_key_bounds row hrow
  · subst block
    exact block030_lower_key_bounds row hrow
  · subst block
    exact block031_lower_key_bounds row hrow
  · subst block
    exact block032_lower_key_bounds row hrow
  · subst block
    exact block033_lower_key_bounds row hrow
  · subst block
    exact block034_lower_key_bounds row hrow
  · subst block
    exact block035_lower_key_bounds row hrow
  · subst block
    exact block036_lower_key_bounds row hrow
  · subst block
    exact block037_lower_key_bounds row hrow
  · subst block
    exact block038_lower_key_bounds row hrow
  · subst block
    exact block039_lower_key_bounds row hrow
  · subst block
    exact block040_lower_key_bounds row hrow
  · subst block
    exact block041_lower_key_bounds row hrow
  · subst block
    exact block042_lower_key_bounds row hrow
  · subst block
    exact block043_lower_key_bounds row hrow
  · subst block
    exact block044_lower_key_bounds row hrow
  · subst block
    exact block045_lower_key_bounds row hrow
  · subst block
    exact block046_lower_key_bounds row hrow
  · subst block
    exact block047_lower_key_bounds row hrow
  · subst block
    exact block048_lower_key_bounds row hrow
  · subst block
    exact block049_lower_key_bounds row hrow
  · subst block
    exact block050_lower_key_bounds row hrow
  · subst block
    exact block051_lower_key_bounds row hrow
  · subst block
    exact block052_lower_key_bounds row hrow
  · subst block
    exact block053_lower_key_bounds row hrow
  · subst block
    exact block054_lower_key_bounds row hrow
  · subst block
    exact block055_lower_key_bounds row hrow
  · subst block
    exact block056_lower_key_bounds row hrow
  · subst block
    exact block057_lower_key_bounds row hrow
  · subst block
    exact block058_lower_key_bounds row hrow
  · subst block
    exact block059_lower_key_bounds row hrow
  · subst block
    exact block060_lower_key_bounds row hrow
  · subst block
    exact block061_lower_key_bounds row hrow
  · subst block
    exact block062_lower_key_bounds row hrow
  · subst block
    exact block063_lower_key_bounds row hrow
  · subst block
    exact block064_lower_key_bounds row hrow
  · subst block
    exact block065_lower_key_bounds row hrow
  · subst block
    exact block066_lower_key_bounds row hrow
  · subst block
    exact block067_lower_key_bounds row hrow
  · subst block
    exact block068_lower_key_bounds row hrow
  · subst block
    exact block069_lower_key_bounds row hrow
  · subst block
    exact block070_lower_key_bounds row hrow
  · subst block
    exact block071_lower_key_bounds row hrow
  · subst block
    exact block072_lower_key_bounds row hrow
  · subst block
    exact block073_lower_key_bounds row hrow
  · subst block
    exact block074_lower_key_bounds row hrow
  · subst block
    exact block075_lower_key_bounds row hrow
  · subst block
    exact block076_lower_key_bounds row hrow
  · subst block
    exact block077_lower_key_bounds row hrow
  · subst block
    exact block078_lower_key_bounds row hrow
  · subst block
    exact block079_lower_key_bounds row hrow
  · subst block
    exact block080_lower_key_bounds row hrow
  · subst block
    exact block081_lower_key_bounds row hrow
  · subst block
    exact block082_lower_key_bounds row hrow
  · subst block
    exact block083_lower_key_bounds row hrow
  · subst block
    exact block084_lower_key_bounds row hrow
  · subst block
    exact block085_lower_key_bounds row hrow
  · subst block
    exact block086_lower_key_bounds row hrow
  · subst block
    exact block087_lower_key_bounds row hrow
  · subst block
    exact block088_lower_key_bounds row hrow
  · subst block
    exact block089_lower_key_bounds row hrow
  · subst block
    exact block090_lower_key_bounds row hrow
  · subst block
    exact block091_lower_key_bounds row hrow
  · subst block
    exact block092_lower_key_bounds row hrow
  · subst block
    exact block093_lower_key_bounds row hrow
  · subst block
    exact block094_lower_key_bounds row hrow
  · subst block
    exact block095_lower_key_bounds row hrow
  · subst block
    exact block096_lower_key_bounds row hrow
  · subst block
    exact block097_lower_key_bounds row hrow
  · subst block
    exact block098_lower_key_bounds row hrow
  · subst block
    exact block099_lower_key_bounds row hrow
  · subst block
    exact block100_lower_key_bounds row hrow
  · subst block
    exact block101_lower_key_bounds row hrow
  · subst block
    exact block102_lower_key_bounds row hrow
  · subst block
    exact block103_lower_key_bounds row hrow
  · subst block
    exact block104_lower_key_bounds row hrow
  · subst block
    exact block105_lower_key_bounds row hrow
  · subst block
    exact block106_lower_key_bounds row hrow
  · subst block
    exact block107_lower_key_bounds row hrow
  · subst block
    exact block108_lower_key_bounds row hrow
  · subst block
    exact block109_lower_key_bounds row hrow
  · subst block
    exact block110_lower_key_bounds row hrow
  · subst block
    exact block111_lower_key_bounds row hrow
  · subst block
    exact block112_lower_key_bounds row hrow
  · subst block
    exact block113_lower_key_bounds row hrow
  · subst block
    exact block114_lower_key_bounds row hrow
  · subst block
    exact block115_lower_key_bounds row hrow
  · subst block
    exact block116_lower_key_bounds row hrow
  · subst block
    exact block117_lower_key_bounds row hrow
  · subst block
    exact block118_lower_key_bounds row hrow
  · subst block
    exact block119_lower_key_bounds row hrow
  · subst block
    exact block120_lower_key_bounds row hrow
  · subst block
    exact block121_lower_key_bounds row hrow
  · subst block
    exact block122_lower_key_bounds row hrow
  · subst block
    exact block123_lower_key_bounds row hrow
  · subst block
    exact block124_lower_key_bounds row hrow
  · subst block
    exact block125_lower_key_bounds row hrow
  · subst block
    exact block126_lower_key_bounds row hrow
  · subst block
    exact block127_lower_key_bounds row hrow
  · subst block
    exact block128_lower_key_bounds row hrow
  · subst block
    exact block129_lower_key_bounds row hrow
  · subst block
    exact block130_lower_key_bounds row hrow
  · subst block
    exact block131_lower_key_bounds row hrow
  · subst block
    exact block132_lower_key_bounds row hrow
  · subst block
    exact block133_lower_key_bounds row hrow
  · subst block
    exact block134_lower_key_bounds row hrow
  · subst block
    exact block135_lower_key_bounds row hrow
  · subst block
    exact block136_lower_key_bounds row hrow
  · subst block
    exact block137_lower_key_bounds row hrow
  · subst block
    exact block138_lower_key_bounds row hrow
  · subst block
    exact block139_lower_key_bounds row hrow
  · subst block
    exact block140_lower_key_bounds row hrow
  · subst block
    exact block141_lower_key_bounds row hrow
  · subst block
    exact block142_lower_key_bounds row hrow

end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
