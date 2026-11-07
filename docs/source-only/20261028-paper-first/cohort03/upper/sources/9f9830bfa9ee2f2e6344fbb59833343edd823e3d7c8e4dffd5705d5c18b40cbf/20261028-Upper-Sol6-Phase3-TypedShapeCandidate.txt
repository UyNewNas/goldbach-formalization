import ImbalancedChen.Data.P1HistoricalFifthSavedTableData
import ImbalancedChen.P1HistoricalFifthNpyFrame
import Mathlib.Tactic

-- SOURCE ONLY / UNCOMPILED_ZERO_CREDIT / NOT ROOT ACCEPTED.
-- This is a concrete shape/order proof for the143 archived typed blocks.
-- It does not parse cells.npy, check gates, infer saved dynamic parents,
-- or assert that a source SHA is a kernel proof of byte-to-row equality.
namespace ImbalancedChen.P1HistoricalFifthTypedArchiveShape
noncomputable section
open P1OriginalPrefixRowDecodeSoundness
open P1HistoricalFifthTableParser P1HistoricalFifthSigned64Payload
open Data.P1HistoricalFifthSavedTableData

set_option maxRecDepth 16384

-- Each proof reduces only one authentic literal array's size.
theorem block000_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000.rows.size = 2048 := rfl
theorem block001_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock001.rows.size = 2048 := rfl
theorem block002_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock002.rows.size = 2048 := rfl
theorem block003_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock003.rows.size = 2048 := rfl
theorem block004_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock004.rows.size = 2048 := rfl
theorem block005_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock005.rows.size = 2048 := rfl
theorem block006_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock006.rows.size = 2048 := rfl
theorem block007_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock007.rows.size = 2048 := rfl
theorem block008_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock008.rows.size = 2048 := rfl
theorem block009_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock009.rows.size = 2048 := rfl
theorem block010_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock010.rows.size = 2048 := rfl
theorem block011_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock011.rows.size = 2048 := rfl
theorem block012_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock012.rows.size = 2048 := rfl
theorem block013_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock013.rows.size = 2048 := rfl
theorem block014_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock014.rows.size = 2048 := rfl
theorem block015_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock015.rows.size = 2048 := rfl
theorem block016_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock016.rows.size = 2048 := rfl
theorem block017_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock017.rows.size = 2048 := rfl
theorem block018_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock018.rows.size = 2048 := rfl
theorem block019_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock019.rows.size = 2048 := rfl
theorem block020_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock020.rows.size = 2048 := rfl
theorem block021_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock021.rows.size = 2048 := rfl
theorem block022_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock022.rows.size = 2048 := rfl
theorem block023_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock023.rows.size = 2048 := rfl
theorem block024_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock024.rows.size = 2048 := rfl
theorem block025_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock025.rows.size = 2048 := rfl
theorem block026_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock026.rows.size = 2048 := rfl
theorem block027_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock027.rows.size = 2048 := rfl
theorem block028_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock028.rows.size = 2048 := rfl
theorem block029_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock029.rows.size = 2048 := rfl
theorem block030_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock030.rows.size = 2048 := rfl
theorem block031_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock031.rows.size = 2048 := rfl
theorem block032_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock032.rows.size = 2048 := rfl
theorem block033_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock033.rows.size = 2048 := rfl
theorem block034_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock034.rows.size = 2048 := rfl
theorem block035_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock035.rows.size = 2048 := rfl
theorem block036_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock036.rows.size = 2048 := rfl
theorem block037_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock037.rows.size = 2048 := rfl
theorem block038_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock038.rows.size = 2048 := rfl
theorem block039_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock039.rows.size = 2048 := rfl
theorem block040_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock040.rows.size = 2048 := rfl
theorem block041_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock041.rows.size = 2048 := rfl
theorem block042_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock042.rows.size = 2048 := rfl
theorem block043_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock043.rows.size = 2048 := rfl
theorem block044_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock044.rows.size = 2048 := rfl
theorem block045_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock045.rows.size = 2048 := rfl
theorem block046_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock046.rows.size = 2048 := rfl
theorem block047_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock047.rows.size = 2048 := rfl
theorem block048_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock048.rows.size = 2048 := rfl
theorem block049_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock049.rows.size = 2048 := rfl
theorem block050_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock050.rows.size = 2048 := rfl
theorem block051_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock051.rows.size = 2048 := rfl
theorem block052_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock052.rows.size = 2048 := rfl
theorem block053_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock053.rows.size = 2048 := rfl
theorem block054_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock054.rows.size = 2048 := rfl
theorem block055_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock055.rows.size = 2048 := rfl
theorem block056_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock056.rows.size = 2048 := rfl
theorem block057_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock057.rows.size = 2048 := rfl
theorem block058_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock058.rows.size = 2048 := rfl
theorem block059_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock059.rows.size = 2048 := rfl
theorem block060_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock060.rows.size = 2048 := rfl
theorem block061_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock061.rows.size = 2048 := rfl
theorem block062_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock062.rows.size = 2048 := rfl
theorem block063_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock063.rows.size = 2048 := rfl
theorem block064_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock064.rows.size = 2048 := rfl
theorem block065_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock065.rows.size = 2048 := rfl
theorem block066_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock066.rows.size = 2048 := rfl
theorem block067_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock067.rows.size = 2048 := rfl
theorem block068_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock068.rows.size = 2048 := rfl
theorem block069_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock069.rows.size = 2048 := rfl
theorem block070_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock070.rows.size = 2048 := rfl
theorem block071_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock071.rows.size = 2048 := rfl
theorem block072_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock072.rows.size = 2048 := rfl
theorem block073_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock073.rows.size = 2048 := rfl
theorem block074_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock074.rows.size = 2048 := rfl
theorem block075_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock075.rows.size = 2048 := rfl
theorem block076_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock076.rows.size = 2048 := rfl
theorem block077_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock077.rows.size = 2048 := rfl
theorem block078_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock078.rows.size = 2048 := rfl
theorem block079_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock079.rows.size = 2048 := rfl
theorem block080_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock080.rows.size = 2048 := rfl
theorem block081_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock081.rows.size = 2048 := rfl
theorem block082_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock082.rows.size = 2048 := rfl
theorem block083_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock083.rows.size = 2048 := rfl
theorem block084_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock084.rows.size = 2048 := rfl
theorem block085_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock085.rows.size = 2048 := rfl
theorem block086_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock086.rows.size = 2048 := rfl
theorem block087_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock087.rows.size = 2048 := rfl
theorem block088_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock088.rows.size = 2048 := rfl
theorem block089_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock089.rows.size = 2048 := rfl
theorem block090_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock090.rows.size = 2048 := rfl
theorem block091_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock091.rows.size = 2048 := rfl
theorem block092_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock092.rows.size = 2048 := rfl
theorem block093_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock093.rows.size = 2048 := rfl
theorem block094_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock094.rows.size = 2048 := rfl
theorem block095_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock095.rows.size = 2048 := rfl
theorem block096_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock096.rows.size = 2048 := rfl
theorem block097_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock097.rows.size = 2048 := rfl
theorem block098_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock098.rows.size = 2048 := rfl
theorem block099_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock099.rows.size = 2048 := rfl
theorem block100_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock100.rows.size = 2048 := rfl
theorem block101_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock101.rows.size = 2048 := rfl
theorem block102_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock102.rows.size = 2048 := rfl
theorem block103_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock103.rows.size = 2048 := rfl
theorem block104_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock104.rows.size = 2048 := rfl
theorem block105_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock105.rows.size = 2048 := rfl
theorem block106_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock106.rows.size = 2048 := rfl
theorem block107_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock107.rows.size = 2048 := rfl
theorem block108_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock108.rows.size = 2048 := rfl
theorem block109_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock109.rows.size = 2048 := rfl
theorem block110_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock110.rows.size = 2048 := rfl
theorem block111_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock111.rows.size = 2048 := rfl
theorem block112_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock112.rows.size = 2048 := rfl
theorem block113_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock113.rows.size = 2048 := rfl
theorem block114_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock114.rows.size = 2048 := rfl
theorem block115_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock115.rows.size = 2048 := rfl
theorem block116_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock116.rows.size = 2048 := rfl
theorem block117_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock117.rows.size = 2048 := rfl
theorem block118_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock118.rows.size = 2048 := rfl
theorem block119_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock119.rows.size = 2048 := rfl
theorem block120_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock120.rows.size = 2048 := rfl
theorem block121_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock121.rows.size = 2048 := rfl
theorem block122_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock122.rows.size = 2048 := rfl
theorem block123_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock123.rows.size = 2048 := rfl
theorem block124_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock124.rows.size = 2048 := rfl
theorem block125_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock125.rows.size = 2048 := rfl
theorem block126_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock126.rows.size = 2048 := rfl
theorem block127_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock127.rows.size = 2048 := rfl
theorem block128_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock128.rows.size = 2048 := rfl
theorem block129_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock129.rows.size = 2048 := rfl
theorem block130_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock130.rows.size = 2048 := rfl
theorem block131_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock131.rows.size = 2048 := rfl
theorem block132_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock132.rows.size = 2048 := rfl
theorem block133_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock133.rows.size = 2048 := rfl
theorem block134_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock134.rows.size = 2048 := rfl
theorem block135_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock135.rows.size = 2048 := rfl
theorem block136_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock136.rows.size = 2048 := rfl
theorem block137_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock137.rows.size = 2048 := rfl
theorem block138_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock138.rows.size = 2048 := rfl
theorem block139_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock139.rows.size = 2048 := rfl
theorem block140_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock140.rows.size = 2048 := rfl
theorem block141_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock141.rows.size = 2048 := rfl
theorem block142_size : ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock142.rows.size = 1817 := rfl

theorem blocks_size : blocks.size = 143 := rfl

-- The explicit order is the hub's actual ordered array, not a Finset image.
theorem block_order : blocks.toList = [
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock001.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock002.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock003.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock004.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock005.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock006.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock007.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock008.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock009.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock010.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock011.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock012.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock013.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock014.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock015.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock016.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock017.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock018.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock019.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock020.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock021.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock022.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock023.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock024.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock025.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock026.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock027.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock028.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock029.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock030.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock031.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock032.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock033.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock034.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock035.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock036.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock037.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock038.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock039.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock040.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock041.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock042.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock043.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock044.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock045.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock046.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock047.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock048.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock049.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock050.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock051.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock052.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock053.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock054.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock055.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock056.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock057.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock058.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock059.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock060.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock061.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock062.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock063.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock064.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock065.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock066.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock067.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock068.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock069.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock070.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock071.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock072.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock073.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock074.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock075.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock076.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock077.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock078.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock079.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock080.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock081.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock082.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock083.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock084.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock085.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock086.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock087.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock088.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock089.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock090.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock091.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock092.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock093.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock094.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock095.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock096.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock097.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock098.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock099.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock100.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock101.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock102.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock103.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock104.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock105.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock106.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock107.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock108.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock109.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock110.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock111.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock112.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock113.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock114.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock115.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock116.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock117.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock118.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock119.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock120.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock121.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock122.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock123.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock124.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock125.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock126.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock127.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock128.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock129.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock130.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock131.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock132.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock133.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock134.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock135.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock136.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock137.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock138.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock139.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock140.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock141.rows,
  ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock142.rows] := rfl

theorem block_sizes : (blocks.toList.map (fun a => a.size)) =
    List.replicate 142 2048 ++ [1817] := by
  change [ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock000.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock001.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock002.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock003.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock004.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock005.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock006.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock007.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock008.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock009.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock010.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock011.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock012.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock013.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock014.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock015.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock016.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock017.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock018.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock019.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock020.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock021.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock022.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock023.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock024.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock025.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock026.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock027.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock028.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock029.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock030.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock031.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock032.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock033.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock034.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock035.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock036.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock037.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock038.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock039.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock040.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock041.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock042.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock043.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock044.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock045.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock046.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock047.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock048.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock049.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock050.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock051.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock052.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock053.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock054.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock055.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock056.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock057.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock058.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock059.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock060.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock061.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock062.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock063.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock064.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock065.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock066.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock067.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock068.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock069.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock070.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock071.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock072.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock073.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock074.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock075.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock076.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock077.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock078.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock079.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock080.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock081.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock082.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock083.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock084.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock085.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock086.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock087.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock088.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock089.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock090.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock091.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock092.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock093.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock094.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock095.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock096.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock097.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock098.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock099.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock100.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock101.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock102.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock103.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock104.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock105.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock106.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock107.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock108.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock109.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock110.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock111.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock112.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock113.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock114.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock115.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock116.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock117.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock118.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock119.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock120.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock121.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock122.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock123.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock124.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock125.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock126.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock127.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock128.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock129.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock130.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock131.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock132.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock133.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock134.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock135.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock136.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock137.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock138.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock139.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock140.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock141.rows.size,
    ImbalancedChen.Data.P1HistoricalFifthSavedDataBlock142.rows.size] = _
  rw [block000_size,
    block001_size,
    block002_size,
    block003_size,
    block004_size,
    block005_size,
    block006_size,
    block007_size,
    block008_size,
    block009_size,
    block010_size,
    block011_size,
    block012_size,
    block013_size,
    block014_size,
    block015_size,
    block016_size,
    block017_size,
    block018_size,
    block019_size,
    block020_size,
    block021_size,
    block022_size,
    block023_size,
    block024_size,
    block025_size,
    block026_size,
    block027_size,
    block028_size,
    block029_size,
    block030_size,
    block031_size,
    block032_size,
    block033_size,
    block034_size,
    block035_size,
    block036_size,
    block037_size,
    block038_size,
    block039_size,
    block040_size,
    block041_size,
    block042_size,
    block043_size,
    block044_size,
    block045_size,
    block046_size,
    block047_size,
    block048_size,
    block049_size,
    block050_size,
    block051_size,
    block052_size,
    block053_size,
    block054_size,
    block055_size,
    block056_size,
    block057_size,
    block058_size,
    block059_size,
    block060_size,
    block061_size,
    block062_size,
    block063_size,
    block064_size,
    block065_size,
    block066_size,
    block067_size,
    block068_size,
    block069_size,
    block070_size,
    block071_size,
    block072_size,
    block073_size,
    block074_size,
    block075_size,
    block076_size,
    block077_size,
    block078_size,
    block079_size,
    block080_size,
    block081_size,
    block082_size,
    block083_size,
    block084_size,
    block085_size,
    block086_size,
    block087_size,
    block088_size,
    block089_size,
    block090_size,
    block091_size,
    block092_size,
    block093_size,
    block094_size,
    block095_size,
    block096_size,
    block097_size,
    block098_size,
    block099_size,
    block100_size,
    block101_size,
    block102_size,
    block103_size,
    block104_size,
    block105_size,
    block106_size,
    block107_size,
    block108_size,
    block109_size,
    block110_size,
    block111_size,
    block112_size,
    block113_size,
    block114_size,
    block115_size,
    block116_size,
    block117_size,
    block118_size,
    block119_size,
    block120_size,
    block121_size,
    block122_size,
    block123_size,
    block124_size,
    block125_size,
    block126_size,
    block127_size,
    block128_size,
    block129_size,
    block130_size,
    block131_size,
    block132_size,
    block133_size,
    block134_size,
    block135_size,
    block136_size,
    block137_size,
    block138_size,
    block139_size,
    block140_size,
    block141_size,
    block142_size]
  rfl

-- This private list induction accounts for ordered concatenation lengths;
-- the concrete sizes enter only through the preceding literal proofs.
private theorem flatMap_array_length {α : Type*} (bs : List (Array α)) :
    (bs.flatMap Array.toList).length = (bs.map (fun a => a.size)).sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.flatMap_cons, List.length_append,
      Array.length_toList, List.map_cons, List.sum_cons, ih]

theorem rows_toList_order : rows.toList = blocks.toList.flatMap Array.toList := by
  unfold Data.P1HistoricalFifthSavedTableData.rows
  rw [← Array.foldl_toList (fun (acc : Array FifthWireRow) block => acc ++ block)]
  simpa only [Array.toList_empty, List.nil_append] using
    (Array.foldl_toList_eq_flatMap (l := blocks.toList)
      (acc := (#[] : Array FifthWireRow))
      (F := fun acc block => acc ++ block) (G := Array.toList)
      (fun acc block => Array.toList_append))

theorem rows_toList_length : rows.toList.length = 292633 := by
  rw [rows_toList_order, flatMap_array_length, block_sizes]
  norm_num [List.replicate]

theorem rows_size : rows.size = 292633 := by
  simpa only [Array.length_toList] using rows_toList_length

def prefixRows (k : ℕ) : List FifthWireRow :=
  (blocks.toList.take k).flatMap Array.toList

def suffixRows (k : ℕ) : List FifthWireRow :=
  (blocks.toList.drop k).flatMap Array.toList

def rowBoundary (k : ℕ) : ℕ := if k ≤ 142 then 2048 * k else 292633

theorem rows_split_at_block (k : ℕ) :
    rows.toList = prefixRows k ++ suffixRows k := by
  rw [rows_toList_order]
  unfold prefixRows suffixRows
  rw [← List.flatMap_append, List.take_append_drop]

theorem prefixRows_length (k : ℕ) (hk : k ≤ 143) :
    (prefixRows k).length = rowBoundary k := by
  unfold prefixRows
  rw [flatMap_array_length, List.map_take, block_sizes]
  by_cases h : k ≤ 142
  · rw [List.take_append_of_le_length (by simpa using h)]
    simp [rowBoundary, h, List.take_replicate, Nat.min_eq_left h,
      List.sum_replicate, nsmul_eq_mul, Nat.mul_comm]
  · have heq : k = 143 := by omega
    subst k
    norm_num [rowBoundary, List.replicate]

theorem block_start (b : Fin 143) :
    (prefixRows b.val).length = 2048 * b.val := by
  rw [prefixRows_length b.val (by omega), rowBoundary, if_pos (by omega)]

theorem last_block_boundaries :
    (prefixRows 142).length = 290816 ∧ (prefixRows 143).length = 292633 := by
  constructor
  · rw [prefixRows_length 142 (by omega)]
    norm_num [rowBoundary]
  · rw [prefixRows_length 143 (by omega)]
    norm_num [rowBoundary]

theorem last_block_size :
    Data.P1HistoricalFifthSavedDataBlock142.rows.size = 292633 - 290816 := by
  rw [block142_size]
  norm_num

-- Frame facts below concern the encoding of these actual typed rows.
-- They deliberately do not identify that encoding with archived raw bytes.
theorem typed_frame_header :
    P1HistoricalFifthNpyFrame.headerCheck
      (P1HistoricalFifthNpyFrame.encodeFrame rows.toList) = true := by
  rw [P1HistoricalFifthNpyFrame.headerCheck_iff,
    P1HistoricalFifthNpyFrame.encodeFrame]
  exact List.take_left' rfl

theorem typed_payload_length : (encodeRows rows.toList).length = 23410640 := by
  rw [encodeRows_length, rows_toList_length]
  norm_num

theorem typed_frame_length :
    (P1HistoricalFifthNpyFrame.encodeFrame rows.toList).length = 23410768 := by
  rw [P1HistoricalFifthNpyFrame.encodeFrame, List.length_append,
    P1HistoricalFifthNpyFrame.authenticHeader_length, typed_payload_length]

theorem typed_frame_block_split (k : ℕ) :
    P1HistoricalFifthNpyFrame.encodeFrame rows.toList =
      P1HistoricalFifthNpyFrame.authenticHeader ++ encodeRows (prefixRows k) ++
        encodeRows (suffixRows k) := by
  rw [rows_split_at_block k]
  simp only [P1HistoricalFifthNpyFrame.encodeFrame, encodeRows, encodeChunks,
    List.flatMap_append, List.append_assoc]

theorem typed_frame_block_offset (k : ℕ) (hk : k ≤ 143) :
    (P1HistoricalFifthNpyFrame.authenticHeader ++ encodeRows (prefixRows k)).length =
      128 + 80 * rowBoundary k := by
  rw [List.length_append, P1HistoricalFifthNpyFrame.authenticHeader_length,
    encodeRows_length, prefixRows_length k hk]

theorem typed_frame_final_block_offset :
    (P1HistoricalFifthNpyFrame.authenticHeader ++ encodeRows (prefixRows 142)).length =
      23265408 := by
  rw [typed_frame_block_offset 142 (by omega)]
  norm_num [rowBoundary]

theorem columns_exact : columns.toList =
    ["n", "l1", "l2", "l3", "l4", "l5", "mask", "vertex_gap_sum", "A", "B"] := rfl

-- Pairing literal archived field names with the actual signed64 row ABI
-- retains the three opaque statistics in their original columns.
def namedRow (r : FifthWireRow) : List (String × ℤ) :=
  columns.toList.zip (List.ofFn (wireColumns r))

theorem namedRow_exact (r : FifthWireRow) : namedRow r =
    [("n", r.grid), ("l1", r.lo 0), ("l2", r.lo 1), ("l3", r.lo 2),
     ("l4", r.lo 3), ("l5", r.lo 4), ("mask", r.mask),
     ("vertex_gap_sum", r.vertexGapSum), ("A", r.ratioA), ("B", r.ratioB)] := rfl

end
end ImbalancedChen.P1HistoricalFifthTypedArchiveShape
