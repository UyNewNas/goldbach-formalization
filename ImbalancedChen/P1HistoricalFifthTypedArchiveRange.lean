import ImbalancedChen.Data.P1HistoricalFifthSavedTableData
import ImbalancedChen.P1HistoricalFifthTypedArchiveShape
import ImbalancedChen.P1HistoricalFifthNpyFrame
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlock000
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks001010
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks011020
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks021030
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks031040
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks041050
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks051060
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks061070
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks071080
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks081090
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks091100
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks101110
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks111120
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks121130
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks131140
import ImbalancedChen.P1HistoricalFifthTypedArchiveRangeBlocks141142
import Mathlib.Tactic

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / NOT ROOT ACCEPTED.
-- All143 original closed obligations are supplied by the imported block owners.
-- Core and block000 have source-bound normal/kernel/full-owned receipts.
-- Remaining block owners and this full aggregation await their own acceptance.
-- The resulting frame roundtrip below concerns the TYPED ENCODED frame;
-- it is not an authenticity or decode claim about archived cells.npy.
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveRange
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload
open P1HistoricalFifthTypedArchiveShape

-- Row membership follows the actual143-block ordered hub, with no parsed
-- byte premise, omitted block, deduplication, sorting or row-key assumption.
theorem rows_typed_valid :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList, TypedValid row := by
  intro row hrow
  rw [rows_toList_order] at hrow
  obtain ⟨block, hblock, hrow⟩ := List.mem_flatMap.mp hrow
  rw [block_order] at hblock
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hblock
  rcases hblock with hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock | hblock
  · subst block
    exact block000_typed_valid row hrow
  · subst block
    exact block001_typed_valid row hrow
  · subst block
    exact block002_typed_valid row hrow
  · subst block
    exact block003_typed_valid row hrow
  · subst block
    exact block004_typed_valid row hrow
  · subst block
    exact block005_typed_valid row hrow
  · subst block
    exact block006_typed_valid row hrow
  · subst block
    exact block007_typed_valid row hrow
  · subst block
    exact block008_typed_valid row hrow
  · subst block
    exact block009_typed_valid row hrow
  · subst block
    exact block010_typed_valid row hrow
  · subst block
    exact block011_typed_valid row hrow
  · subst block
    exact block012_typed_valid row hrow
  · subst block
    exact block013_typed_valid row hrow
  · subst block
    exact block014_typed_valid row hrow
  · subst block
    exact block015_typed_valid row hrow
  · subst block
    exact block016_typed_valid row hrow
  · subst block
    exact block017_typed_valid row hrow
  · subst block
    exact block018_typed_valid row hrow
  · subst block
    exact block019_typed_valid row hrow
  · subst block
    exact block020_typed_valid row hrow
  · subst block
    exact block021_typed_valid row hrow
  · subst block
    exact block022_typed_valid row hrow
  · subst block
    exact block023_typed_valid row hrow
  · subst block
    exact block024_typed_valid row hrow
  · subst block
    exact block025_typed_valid row hrow
  · subst block
    exact block026_typed_valid row hrow
  · subst block
    exact block027_typed_valid row hrow
  · subst block
    exact block028_typed_valid row hrow
  · subst block
    exact block029_typed_valid row hrow
  · subst block
    exact block030_typed_valid row hrow
  · subst block
    exact block031_typed_valid row hrow
  · subst block
    exact block032_typed_valid row hrow
  · subst block
    exact block033_typed_valid row hrow
  · subst block
    exact block034_typed_valid row hrow
  · subst block
    exact block035_typed_valid row hrow
  · subst block
    exact block036_typed_valid row hrow
  · subst block
    exact block037_typed_valid row hrow
  · subst block
    exact block038_typed_valid row hrow
  · subst block
    exact block039_typed_valid row hrow
  · subst block
    exact block040_typed_valid row hrow
  · subst block
    exact block041_typed_valid row hrow
  · subst block
    exact block042_typed_valid row hrow
  · subst block
    exact block043_typed_valid row hrow
  · subst block
    exact block044_typed_valid row hrow
  · subst block
    exact block045_typed_valid row hrow
  · subst block
    exact block046_typed_valid row hrow
  · subst block
    exact block047_typed_valid row hrow
  · subst block
    exact block048_typed_valid row hrow
  · subst block
    exact block049_typed_valid row hrow
  · subst block
    exact block050_typed_valid row hrow
  · subst block
    exact block051_typed_valid row hrow
  · subst block
    exact block052_typed_valid row hrow
  · subst block
    exact block053_typed_valid row hrow
  · subst block
    exact block054_typed_valid row hrow
  · subst block
    exact block055_typed_valid row hrow
  · subst block
    exact block056_typed_valid row hrow
  · subst block
    exact block057_typed_valid row hrow
  · subst block
    exact block058_typed_valid row hrow
  · subst block
    exact block059_typed_valid row hrow
  · subst block
    exact block060_typed_valid row hrow
  · subst block
    exact block061_typed_valid row hrow
  · subst block
    exact block062_typed_valid row hrow
  · subst block
    exact block063_typed_valid row hrow
  · subst block
    exact block064_typed_valid row hrow
  · subst block
    exact block065_typed_valid row hrow
  · subst block
    exact block066_typed_valid row hrow
  · subst block
    exact block067_typed_valid row hrow
  · subst block
    exact block068_typed_valid row hrow
  · subst block
    exact block069_typed_valid row hrow
  · subst block
    exact block070_typed_valid row hrow
  · subst block
    exact block071_typed_valid row hrow
  · subst block
    exact block072_typed_valid row hrow
  · subst block
    exact block073_typed_valid row hrow
  · subst block
    exact block074_typed_valid row hrow
  · subst block
    exact block075_typed_valid row hrow
  · subst block
    exact block076_typed_valid row hrow
  · subst block
    exact block077_typed_valid row hrow
  · subst block
    exact block078_typed_valid row hrow
  · subst block
    exact block079_typed_valid row hrow
  · subst block
    exact block080_typed_valid row hrow
  · subst block
    exact block081_typed_valid row hrow
  · subst block
    exact block082_typed_valid row hrow
  · subst block
    exact block083_typed_valid row hrow
  · subst block
    exact block084_typed_valid row hrow
  · subst block
    exact block085_typed_valid row hrow
  · subst block
    exact block086_typed_valid row hrow
  · subst block
    exact block087_typed_valid row hrow
  · subst block
    exact block088_typed_valid row hrow
  · subst block
    exact block089_typed_valid row hrow
  · subst block
    exact block090_typed_valid row hrow
  · subst block
    exact block091_typed_valid row hrow
  · subst block
    exact block092_typed_valid row hrow
  · subst block
    exact block093_typed_valid row hrow
  · subst block
    exact block094_typed_valid row hrow
  · subst block
    exact block095_typed_valid row hrow
  · subst block
    exact block096_typed_valid row hrow
  · subst block
    exact block097_typed_valid row hrow
  · subst block
    exact block098_typed_valid row hrow
  · subst block
    exact block099_typed_valid row hrow
  · subst block
    exact block100_typed_valid row hrow
  · subst block
    exact block101_typed_valid row hrow
  · subst block
    exact block102_typed_valid row hrow
  · subst block
    exact block103_typed_valid row hrow
  · subst block
    exact block104_typed_valid row hrow
  · subst block
    exact block105_typed_valid row hrow
  · subst block
    exact block106_typed_valid row hrow
  · subst block
    exact block107_typed_valid row hrow
  · subst block
    exact block108_typed_valid row hrow
  · subst block
    exact block109_typed_valid row hrow
  · subst block
    exact block110_typed_valid row hrow
  · subst block
    exact block111_typed_valid row hrow
  · subst block
    exact block112_typed_valid row hrow
  · subst block
    exact block113_typed_valid row hrow
  · subst block
    exact block114_typed_valid row hrow
  · subst block
    exact block115_typed_valid row hrow
  · subst block
    exact block116_typed_valid row hrow
  · subst block
    exact block117_typed_valid row hrow
  · subst block
    exact block118_typed_valid row hrow
  · subst block
    exact block119_typed_valid row hrow
  · subst block
    exact block120_typed_valid row hrow
  · subst block
    exact block121_typed_valid row hrow
  · subst block
    exact block122_typed_valid row hrow
  · subst block
    exact block123_typed_valid row hrow
  · subst block
    exact block124_typed_valid row hrow
  · subst block
    exact block125_typed_valid row hrow
  · subst block
    exact block126_typed_valid row hrow
  · subst block
    exact block127_typed_valid row hrow
  · subst block
    exact block128_typed_valid row hrow
  · subst block
    exact block129_typed_valid row hrow
  · subst block
    exact block130_typed_valid row hrow
  · subst block
    exact block131_typed_valid row hrow
  · subst block
    exact block132_typed_valid row hrow
  · subst block
    exact block133_typed_valid row hrow
  · subst block
    exact block134_typed_valid row hrow
  · subst block
    exact block135_typed_valid row hrow
  · subst block
    exact block136_typed_valid row hrow
  · subst block
    exact block137_typed_valid row hrow
  · subst block
    exact block138_typed_valid row hrow
  · subst block
    exact block139_typed_valid row hrow
  · subst block
    exact block140_typed_valid row hrow
  · subst block
    exact block141_typed_valid row hrow
  · subst block
    exact block142_typed_valid row hrow

theorem rows_grid_eq400 :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList, row.grid = 400 :=
  fun row hrow => (rows_typed_valid row hrow).1

theorem rows_mask_nonnegative :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList, 0 ≤ row.mask :=
  fun row hrow => (rows_typed_valid row hrow).2.1

-- This is solely the primitive signed schema validity used by the row
-- decoder. It says nothing about row geometry, gateCheck or saved caps.
theorem rows_grid_mask_valid :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList,
      0 < row.grid ∧ 0 ≤ row.mask := by
  intro row hrow
  refine ⟨?_, rows_mask_nonnegative row hrow⟩
  rw [rows_grid_eq400 row hrow]
  norm_num

theorem rows_signed64_range :
    ∀ row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList, ∀ column : Fin 10,
      -(half64 : ℤ) ≤ wireColumns row column ∧ wireColumns row column < (half64 : ℤ) :=
  fun row hrow => (rows_typed_valid row hrow).2.2

-- Concrete instantiation of the already written generic signed64 payload
-- roundtrip. The input bytes here are encoded FROM the typed table itself.
theorem typed_encoded_payload_roundtrip :
    decodeRows (encodeRows Data.P1HistoricalFifthSavedTableData.rows.toList) =
      some Data.P1HistoricalFifthSavedTableData.rows.toList :=
  decodeRows_encodeRows Data.P1HistoricalFifthSavedTableData.rows.toList rows_signed64_range

-- The actual shape proof supplies292633 and the new literal proofs supply
-- signed range. There is no independent archived-byte object in this term.
theorem typed_encoded_frame_roundtrip :
    P1HistoricalFifthNpyFrame.decodeFrame
        (P1HistoricalFifthNpyFrame.encodeFrame Data.P1HistoricalFifthSavedTableData.rows.toList) =
      some Data.P1HistoricalFifthSavedTableData.rows.toList := by
  apply P1HistoricalFifthNpyFrame.decodeFrame_encodeFrame
  · simpa only [P1HistoricalFifthNpyFrame.rowCount] using rows_toList_length
  · exact rows_signed64_range

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveRange
