import ImbalancedChen.Certificates.PairedV2Batch4To64Data
import ImbalancedChen.Certificates.PairedV2Geometry

/-! Byte-identical proof blocks split from the batch to bound compiler memory. -/

namespace ImbalancedChen.Certificates.PairedV2.Batch4To64

open MeasureTheory Set
open scoped BigOperators Interval

set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

theorem lower_sum : (∑ i : Fin 60, (certificates i).lower) = lowerBound := by
  norm_num [certificates, lowerBound, Fin.sum_univ_succ, certificate0004, certificate0005, certificate0006, certificate0007, certificate0008, certificate0009, certificate0010, certificate0011, certificate0012, certificate0013, certificate0014, certificate0015, certificate0016, certificate0017, certificate0018, certificate0019, certificate0020, certificate0021, certificate0022, certificate0023, certificate0024, certificate0025, certificate0026, certificate0027, certificate0028, certificate0029, certificate0030, certificate0031, certificate0032, certificate0033, certificate0034, certificate0035, certificate0036, certificate0037, certificate0038, certificate0039, certificate0040, certificate0041, certificate0042, certificate0043, certificate0044, certificate0045, certificate0046, certificate0047, certificate0048, certificate0049, certificate0050, certificate0051, certificate0052, certificate0053, certificate0054, certificate0055, certificate0056, certificate0057, certificate0058, certificate0059, certificate0060, certificate0061, certificate0062, certificate0063]

end ImbalancedChen.Certificates.PairedV2.Batch4To64
