import ImbalancedChen.P1HistoricalFifthTypedArchiveShape
import ImbalancedChen.P5OriginalParentFourGateBlock000
import ImbalancedChen.P5OriginalParentFourGateBlocks001010
import ImbalancedChen.P5OriginalParentFourGateBlocks011020
import ImbalancedChen.P5OriginalParentFourGateBlocks021030
import ImbalancedChen.P5OriginalParentFourGateBlocks031040
import ImbalancedChen.P5OriginalParentFourGateBlocks041050
import ImbalancedChen.P5OriginalParentFourGateBlocks051060
import ImbalancedChen.P5OriginalParentFourGateBlocks061070
import ImbalancedChen.P5OriginalParentFourGateBlocks071080
import ImbalancedChen.P5OriginalParentFourGateBlocks081090
import ImbalancedChen.P5OriginalParentFourGateBlocks091100
import ImbalancedChen.P5OriginalParentFourGateBlocks101110
import ImbalancedChen.P5OriginalParentFourGateBlocks111120
import ImbalancedChen.P5OriginalParentFourGateBlocks121130
import ImbalancedChen.P5OriginalParentFourGateBlocks131140
import ImbalancedChen.P5OriginalParentFourGateBlocks141142

/-! All original table rows, with original source order.
Each finite parent-gate certificate is supplied by its own original block.
No physical owner-bank, key injectivity or NPY authenticity is inferred. -/
set_option autoImplicit false
namespace ImbalancedChen.P5OriginalFullTableChildSourceFacts
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTypedArchiveShape
open P5OldFifthExact64ChildTiling P5OriginalGenericWireFloorReceiver

theorem all_original_rows_child_source_facts :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList,
      ∀ c : ChildIndex, SourceChildFacts row c := by
  intro row hrow c
  rw [rows_toList_order] at hrow
  obtain ⟨block, hblock, hrow⟩ := List.mem_flatMap.mp hrow
  rw [block_order] at hblock
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock
  · subst block
    exact P5OriginalParentFourGateBlock000.block000_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block001_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block002_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block003_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block004_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block005_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block006_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block007_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block008_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block009_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks001010.block010_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block011_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block012_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block013_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block014_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block015_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block016_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block017_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block018_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block019_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks011020.block020_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block021_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block022_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block023_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block024_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block025_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block026_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block027_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block028_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block029_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks021030.block030_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block031_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block032_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block033_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block034_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block035_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block036_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block037_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block038_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block039_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks031040.block040_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block041_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block042_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block043_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block044_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block045_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block046_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block047_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block048_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block049_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks041050.block050_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block051_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block052_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block053_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block054_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block055_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block056_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block057_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block058_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block059_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks051060.block060_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block061_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block062_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block063_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block064_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block065_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block066_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block067_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block068_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block069_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks061070.block070_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block071_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block072_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block073_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block074_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block075_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block076_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block077_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block078_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block079_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks071080.block080_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block081_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block082_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block083_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block084_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block085_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block086_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block087_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block088_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block089_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks081090.block090_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block091_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block092_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block093_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block094_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block095_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block096_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block097_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block098_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block099_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks091100.block100_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block101_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block102_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block103_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block104_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block105_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block106_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block107_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block108_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block109_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks101110.block110_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block111_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block112_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block113_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block114_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block115_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block116_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block117_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block118_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block119_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks111120.block120_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block121_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block122_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block123_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block124_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block125_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block126_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block127_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block128_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block129_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks121130.block130_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block131_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block132_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block133_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block134_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block135_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block136_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block137_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block138_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block139_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks131140.block140_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks141142.block141_all_child_source_facts row hrow c
  · subst block
    exact P5OriginalParentFourGateBlocks141142.block142_all_child_source_facts row hrow c

end ImbalancedChen.P5OriginalFullTableChildSourceFacts
