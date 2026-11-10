import ImbalancedChen.Data.P1HistoricalFifthSavedTableData
import ImbalancedChen.P1HistoricalFifthTypedArchiveShape
import ImbalancedChen.P1HistoricalFifthNpyFrame
import Mathlib.Tactic

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / NOT ROOT ACCEPTED.
-- These143 bounded closed proof terms concern the actual typed literals.
-- No Lean/compiler/evaluation was run when authoring this source. Whether
-- each per-block decide proof fits its stated resource bound is unverified.
-- The resulting frame roundtrip below concerns the TYPED ENCODED frame;
-- it is not an authenticity or decode claim about archived cells.npy.
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveRange
noncomputable section
open P1OriginalPrefixRowDecodeSoundness P1HistoricalFifthTableParser
open P1HistoricalFifthSigned64Arithmetic P1HistoricalFifthSigned64Payload
open P1HistoricalFifthTypedArchiveShape

-- The source grid is exactly400; valid mask means the original conservative
-- decoder's nonnegative signed mask condition, without a geometric flag.
def TypedValid (row : FifthWireRow) : Prop :=
  row.grid = 400 ∧ 0 ≤ row.mask ∧ ∀ column : Fin 10,
    -(half64 : ℤ) ≤ wireColumns row column ∧ wireColumns row column < (half64 : ℤ)

-- Fin10 and signed integer comparisons have constructive decidability.
-- No classical choice or externally evaluated Boolean is a proof premise.
instance typedValidDecidable (row : FifthWireRow) : Decidable (TypedValid row) := by
  unfold TypedValid
  infer_instance

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block000_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block001_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock001.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block002_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock002.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block003_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock003.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block004_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock004.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block005_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock005.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block006_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock006.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block007_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock007.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block008_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock008.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block009_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock009.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block010_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock010.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block011_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock011.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block012_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock012.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block013_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock013.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block014_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock014.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block015_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock015.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block016_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock016.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block017_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock017.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block018_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock018.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block019_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock019.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block020_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock020.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block021_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock021.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block022_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock022.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block023_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock023.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block024_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock024.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block025_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock025.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block026_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock026.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block027_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock027.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block028_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock028.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block029_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock029.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block030_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock030.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block031_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock031.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block032_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock032.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block033_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock033.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block034_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock034.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block035_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock035.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block036_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock036.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block037_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock037.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block038_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock038.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block039_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock039.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block040_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock040.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block041_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock041.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block042_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock042.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block043_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock043.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block044_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock044.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block045_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock045.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block046_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock046.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block047_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock047.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block048_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock048.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block049_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock049.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block050_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock050.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block051_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock051.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block052_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock052.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block053_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock053.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block054_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock054.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block055_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock055.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block056_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock056.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block057_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock057.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block058_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock058.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block059_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock059.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block060_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock060.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block061_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock061.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block062_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock062.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block063_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock063.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block064_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock064.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block065_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock065.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block066_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock066.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block067_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock067.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block068_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock068.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block069_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock069.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block070_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock070.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block071_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock071.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block072_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock072.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block073_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock073.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block074_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock074.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block075_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock075.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block076_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock076.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block077_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock077.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block078_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock078.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block079_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock079.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block080_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock080.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block081_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock081.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block082_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock082.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block083_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock083.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block084_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock084.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block085_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock085.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block086_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock086.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block087_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock087.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block088_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock088.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block089_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock089.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block090_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock090.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block091_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock091.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block092_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock092.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block093_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock093.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block094_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock094.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block095_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock095.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block096_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock096.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block097_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock097.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block098_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock098.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block099_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock099.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block100_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock100.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block101_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock101.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block102_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock102.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block103_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock103.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block104_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock104.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block105_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock105.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block106_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock106.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block107_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock107.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block108_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock108.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block109_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock109.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block110_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock110.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block111_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock111.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block112_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock112.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block113_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock113.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block114_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock114.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block115_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock115.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block116_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock116.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block117_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock117.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block118_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock118.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block119_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock119.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block120_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock120.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block121_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock121.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block122_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock122.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block123_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock123.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block124_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock124.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block125_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock125.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block126_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock126.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block127_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock127.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block128_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock128.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block129_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock129.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block130_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock130.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block131_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock131.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block132_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock132.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block133_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock133.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block134_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock134.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block135_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock135.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block136_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock136.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block137_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock137.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block138_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock138.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block139_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock139.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block140_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock140.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block141_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock141.rows.toList, TypedValid row := by
  decide

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
theorem block142_typed_valid :
    ∀ row ∈ ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock142.rows.toList, TypedValid row := by
  decide

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
