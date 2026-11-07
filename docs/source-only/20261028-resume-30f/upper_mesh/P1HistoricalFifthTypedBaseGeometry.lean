import ImbalancedChen.P1HistoricalFifthIndexedOwnerArchive
import ImbalancedChen.P1HistoricalFifthCommonPolicyInputs
import ImbalancedChen.P1HistoricalFifthTypedArchiveRange
import Mathlib

/-!
SOURCE_ONLY / UNCOMPILED_ZERO_CREDIT.
The full independent143-block typed table has the original positive
lower-key range. These143 closed finite decisions are source proposals;
none was run. They complement, rather than repeat, the frozen grid/mask
range proof. No archived-NPY authenticity or owner-gate licence follows.
-/
namespace ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTypedArchiveShape
open P1HistoricalFifthTypedArchiveRange P1HistoricalFifthIndexedOwnerArchive
open P1HistoricalFifthCommonPolicyInputs

/-- The original generator uses all five keys in8..77; only1..77 is needed
here. Opaque fields and masks never enter this lower-key check. -/
def LowerKeyBounds (row : FifthWireRow) : Prop :=
  ∀ k : Fin 5, 1 ≤ row.lo k ∧ row.lo k ≤ 77

instance lowerKeyBoundsDecidable (row : FifthWireRow) : Decidable (LowerKeyBounds row) := by
  unfold LowerKeyBounds
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block000_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock000.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block001_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock001.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block002_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock002.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block003_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock003.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block004_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock004.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block005_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock005.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block006_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock006.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block007_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock007.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block008_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock008.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block009_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock009.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block010_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock010.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block011_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock011.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block012_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock012.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block013_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock013.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block014_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock014.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block015_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock015.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block016_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock016.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block017_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock017.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block018_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock018.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block019_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock019.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block020_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock020.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block021_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock021.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block022_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock022.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block023_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock023.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block024_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock024.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block025_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock025.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block026_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock026.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block027_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock027.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block028_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock028.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block029_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock029.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block030_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock030.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block031_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock031.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block032_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock032.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block033_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock033.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block034_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock034.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block035_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock035.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block036_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock036.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block037_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock037.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block038_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock038.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block039_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock039.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block040_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock040.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block041_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock041.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block042_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock042.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block043_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock043.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block044_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock044.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block045_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock045.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block046_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock046.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block047_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock047.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block048_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock048.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block049_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock049.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block050_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock050.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block051_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock051.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block052_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock052.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block053_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock053.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block054_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock054.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block055_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock055.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block056_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock056.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block057_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock057.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block058_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock058.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block059_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock059.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block060_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock060.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block061_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock061.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block062_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock062.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block063_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock063.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block064_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock064.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block065_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock065.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block066_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock066.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block067_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock067.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block068_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock068.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block069_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock069.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block070_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock070.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block071_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock071.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block072_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock072.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block073_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock073.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block074_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock074.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block075_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock075.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block076_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock076.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block077_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock077.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block078_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock078.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block079_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock079.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block080_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock080.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block081_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock081.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block082_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock082.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block083_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock083.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block084_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock084.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block085_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock085.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block086_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock086.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block087_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock087.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block088_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock088.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block089_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock089.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block090_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock090.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block091_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock091.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block092_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock092.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block093_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock093.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block094_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock094.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block095_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock095.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block096_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock096.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block097_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock097.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block098_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock098.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block099_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock099.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block100_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock100.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block101_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock101.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block102_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock102.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block103_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock103.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block104_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock104.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block105_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock105.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block106_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock106.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block107_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock107.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block108_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock108.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block109_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock109.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block110_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock110.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block111_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock111.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block112_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock112.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block113_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock113.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block114_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock114.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block115_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock115.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block116_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock116.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block117_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock117.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block118_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock118.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block119_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock119.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block120_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock120.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block121_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock121.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block122_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock122.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block123_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock123.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block124_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock124.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block125_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock125.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block126_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock126.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block127_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock127.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block128_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock128.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block129_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock129.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block130_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock130.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block131_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock131.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block132_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock132.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block133_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock133.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block134_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock134.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block135_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock135.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block136_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock136.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block137_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock137.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block138_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock138.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block139_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock139.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block140_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock140.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block141_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock141.rows.toList, LowerKeyBounds row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block142_lower_key_bounds :
    ∀ row ∈ Data.P1HistoricalFifthSavedDataBlock142.rows.toList, LowerKeyBounds row := by
  decide

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


theorem rows_baseGeometry (row : FifthWireRow)
    (hr : row ∈ Data.P1HistoricalFifthSavedTableData.rows.toList) : baseGeometry row :=
  ⟨rows_grid_eq400 row hr, rows_mask_nonnegative row hr,
    fun k => (rows_lower_key_bounds row hr k).1, (rows_lower_key_bounds row hr 0).2⟩

theorem archiveRow_baseGeometry (i : ArchiveIndex) : baseGeometry (archiveRow i) :=
  rows_baseGeometry _ (archiveRow_source_member i)

theorem archiveRow_grid (i : ArchiveIndex) : (archiveRow i).grid = 400 :=
  (archiveRow_baseGeometry i).1

theorem archiveRow_mask_nonnegative (i : ArchiveIndex) : 0 ≤ (archiveRow i).mask :=
  (archiveRow_baseGeometry i).2.1

noncomputable section
open scoped Classical BigOperators

theorem licensedIndices_eq_univ : licensedIndices = Finset.univ := by
  ext i
  simp [licensedIndices, archiveRow_baseGeometry i]

/-- The geometric rejection set is empty on this actual typed table.
Strict selected/firstStop/full/complement gate rejection is not this set. -/
theorem residualIndices_eq_empty : residualIndices = ∅ := by
  rw [residualIndices, licensedIndices_eq_univ]
  exact Finset.sdiff_self _

theorem all_archive_indices_licensed (i : ArchiveIndex) : i ∈ licensedIndices := by
  rw [licensedIndices_eq_univ]
  exact Finset.mem_univ _

theorem globalOwners_eq_full_index_bank (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    globalOwners e q chi omega =
      Finset.univ.biUnion (fun i : ArchiveIndex => licensedOwners i e q chi omega) := by
  rw [globalOwners, licensedIndices_eq_univ]

theorem common_rows5_eq_full_index_bank
    (rows4 : Finset P2OriginalFourthCapProducerInterface.ProducerRow)
    (licensed4 : P2OriginalFourthCapProducerInterface.ProducerRow → Prop)
    (e : ℚ) (q : ℕ) (chi omega : ℝ) :
    (sourceData rows4 licensed4 e q chi omega).rows5 =
      Finset.univ.biUnion (fun i : ArchiveIndex =>
        (licensedOwners i e q chi omega).image (sourceOwnerRow i q)) := by
  simp only [sourceData, licensedRows, licensedIndices_eq_univ]

end
end ImbalancedChen.P1HistoricalFifthTypedBaseGeometry
